module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Torus
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerDecomp
public import CFSG.RankThree.PartOne.TCX.Ree.A1Layer
public import CFSG.RankThree.PartOne.TCX.Ree.B2Layer
public import CFSG.RankThree.PartOne.TCX.Ree.Frame

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Malle.LocalAction

section Transport

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

omit [IsAlgClosed L] in
theorem rootDiagUnit_eq_mul_ZGrp_gen {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (u : WeylGroup ReeTag.F4.tag)
    {J : Set (Fin ReeTag.F4.tag.rank)}
    (hu : (fun α => u • α) '' S = parabolicRoots ReeTag.F4.tag J)
    (hsplit : ∀ c : Fin ReeTag.F4.tag.rank → Lˣ,
      ∃ z ∈ ZGrp (L := L) (parabolicRoots ReeTag.F4.tag J),
        ∃ q ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag J),
          rootDiagUnit ReeTag.F4.tag c = z * q)
    (c : Fin ReeTag.F4.tag.rank → Lˣ) :
    ∃ z ∈ ZGrp (L := L) S, ∃ q ∈ rootSpan ReeTag.F4.tag L S,
      rootDiagUnit ReeTag.F4.tag c = z * q := by
  obtain ⟨z', hz', q', hq', h'⟩ := hsplit
    (fun i => rootChar c (u⁻¹ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)))
  rw [← CFSG.Quasithin.B45Tor.canonicalRep_conj_rootDiagUnit_F4] at h'
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L u with hn
  have hzS : n⁻¹ * z' * n ∈ ZGrp (L := L) S := by
    apply conj_inv_mem_ZGrp u
    rwa [hu]
  have hqS : n⁻¹ * q' * n ∈ rootSpan ReeTag.F4.tag L S := by
    apply conj_inv_mem_rootSpan hS u
    rw [hu]
    exact hq'
  refine ⟨_, hzS, _, hqS, ?_⟩
  calc rootDiagUnit ReeTag.F4.tag c = n⁻¹ * (n * rootDiagUnit ReeTag.F4.tag c * n⁻¹) * n := by
        group
    _ = n⁻¹ * (z' * q') * n := by rw [h']
    _ = _ := by group

omit [IsAlgClosed L] in
theorem ZGrp_inf_rootSpan_eq_bot_gen {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (u : WeylGroup ReeTag.F4.tag)
    {J : Set (Fin ReeTag.F4.tag.rank)}
    (hu : (fun α => u • α) '' S = parabolicRoots ReeTag.F4.tag J)
    (hinf : ZGrp (L := L) (parabolicRoots ReeTag.F4.tag J) ⊓
      rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag J) = ⊥) :
    ZGrp (L := L) S ⊓ rootSpan ReeTag.F4.tag L S = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hz, hq⟩
  have h1 := conj_mem_ZGrp u hz
  have h2 : canonicalRep (coxeterSystem ReeTag.F4.tag) L u * x *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ ∈
      rootSpan ReeTag.F4.tag L ((fun α => u • α) '' S) := by
    rw [← map_conj_rootSpan (L := L) u hS]
    exact ⟨x, hq, rfl⟩
  rw [hu] at h1 h2
  have h3 : canonicalRep (coxeterSystem ReeTag.F4.tag) L u * x *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ ∈
      ZGrp (L := L) (parabolicRoots ReeTag.F4.tag J) ⊓
        rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag J) :=
    Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot] at h3
  rw [Subgroup.mem_bot]
  have := congrArg (fun y => (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ * y *
    canonicalRep (coxeterSystem ReeTag.F4.tag) L u) h3
  simpa [mul_assoc] using this

end Transport

section Decomp

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem exists_decomp_gen {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (w : WeylGroup ReeTag.F4.tag) {g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L)
    (hFg₀ : Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
    {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (hbp : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1)
    {u : WeylGroup ReeTag.F4.tag} {J : Set (Fin ReeTag.F4.tag.rank)}
    (hΦ : (fun α => u • α) '' rootCharKernel b = parabolicRoots ReeTag.F4.tag J)
    (hsplit : ∀ c : Fin ReeTag.F4.tag.rank → Lˣ,
      ∃ z ∈ ZGrp (L := L) (parabolicRoots ReeTag.F4.tag J),
        ∃ q ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag J),
          rootDiagUnit ReeTag.F4.tag c = z * q)
    (hinfJ : ZGrp (L := L) (parabolicRoots ReeTag.F4.tag J) ⊓
      rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag J) = ⊥)
    (x : ReeTag.F4.reeGamma K a) (hx : reeConj g₀ x = rootDiagUnit ReeTag.F4.tag b) :
    ∃ A Sg : Subgroup (ReeTag.F4.reeGamma K a),
      (∀ γ, γ ∈ A ↔ reeConj g₀ γ ∈ ZGrp (L := L) (rootCharKernel b)) ∧
      (∀ γ, γ ∈ Sg ↔ reeConj g₀ γ ∈ rootSpan ReeTag.F4.tag L (rootCharKernel b)) ∧
      (∀ α ∈ A, ∀ s ∈ Sg, α * s = s * α) ∧ A ⊓ Sg = ⊥ ∧
      A ⊔ Sg = Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧ x ∈ A := by
  classical
  have hp2 : p ≠ 2 := by omega
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  set S := rootCharKernel b with hSdef
  set κ := reeConj (K := K) (a := a) g₀ with hκ
  have hκinj : Function.Injective κ := reeConj_injective g₀
  have hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hSn : ∀ α ∈ S, -α ∈ S := fun α hα =>
    ⟨(isRoot_neg_iff).2 hα.1, by rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2]; simp⟩
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b).1 hb
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot hp hp2 hbp hw hβ
  have hst₁ : ∀ γ ∈ S, w • ReeTag.F4.dualRoot γ ∈ S := fun γ hγ => (hst γ (hS γ hγ)).2 hγ
  have hst₂ : ∀ α ∈ S, ReeTag.F4.dualRoot (w⁻¹ • α) ∈ S := by
    intro α hα
    have hr : IsRoot ReeTag.F4.tag (w⁻¹ • α) := IsRoot.smul (hS α hα) w⁻¹
    have hβ : IsRoot ReeTag.F4.tag (ReeTag.F4.dualRoot (w⁻¹ • α)) := ReeTag.isRoot_dualRoot hr
    refine (hst _ hβ).1 ?_
    rw [ReeTag.dualRoot_dualRoot hr, smul_inv_smul]
    exact hα
  have hsplitS := rootDiagUnit_eq_mul_ZGrp_gen (L := L) hS u hΦ hsplit
  have hinf := ZGrp_inf_rootSpan_eq_bot_gen (L := L) hS u hΦ hinfJ
  have hordW : ¬ p ∣ Nat.card (WeylGroup ReeTag.F4.tag) := not_dvd_card_weylGroup_F4 hp hp3
  set A : Subgroup (ReeTag.F4.reeGamma K a) := (ZGrp (L := L) S).comap κ with hA
  set Sg : Subgroup (ReeTag.F4.reeGamma K a) :=
    (rootSpan ReeTag.F4.tag L S).comap κ with hSg
  have hcommH : ∀ z ∈ ZGrp (L := L) S, rootDiagUnit ReeTag.F4.tag b * z =
      z * rootDiagUnit ReeTag.F4.tag b := by
    intro z hz
    obtain ⟨c, -, rfl⟩ := mem_ZGrp.1 hz
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hxA : x ∈ A := by
    show κ x ∈ ZGrp (L := L) S
    rw [hx]
    exact mem_ZGrp.2 ⟨b, fun α hα => hα.2, rfl⟩
  refine ⟨A, Sg, fun γ => Iff.rfl, fun γ => Iff.rfl, ?_, ?_, ?_, hxA⟩
  · intro α hα s hs
    apply hκinj
    rw [map_mul, map_mul]
    exact ZGrp_commute_rootSpan hS hα hs
  · rw [eq_bot_iff]
    intro γ hγ
    have : κ γ ∈ ZGrp (L := L) S ⊓ rootSpan ReeTag.F4.tag L S := hγ
    rw [hinf, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    apply hκinj
    rw [this, map_one]
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · intro γ hγ
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply hκinj
        rw [map_mul, map_mul, hx]
        exact (hcommH _ hγ).symm
      · intro γ hγ
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply hκinj
        rw [map_mul, map_mul, hx]
        exact Subgroup.mem_centralizer_singleton_iff.1
          (rootSpan_rootCharKernel_le_centralizer b hγ)
    · intro γ hγ
      rw [Subgroup.mem_centralizer_singleton_iff] at hγ
      have hcomm : κ γ * rootDiagUnit ReeTag.F4.tag b = rootDiagUnit ReeTag.F4.tag b * κ γ := by
        rw [← hx, ← map_mul, ← map_mul, hγ]
      have hadj : κ γ ∈ adjointGroup ReeTag.F4.tag L :=
        (reeConj_mem_twistedFixed D hg₀ hFg₀ γ).1
      obtain ⟨t, ht, q, hq, htq⟩ := mem_torus_mul_rootSpan_of_commute hp hordW hbp hb1
        hS hSn (fun _ h => h) hadj hcomm
      obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      obtain ⟨z, hz, q₀, hq₀, hzq⟩ := hsplitS c
      have hq₁ : q₀ * q ∈ rootSpan ReeTag.F4.tag L S := mul_mem hq₀ hq
      have hprod : z * (q₀ * q) = κ γ := by
        rw [← htq, hzq]
        exact (mul_assoc z q₀ q).symm
      have hfix : z * (q₀ * q) ∈ twistedFixed D.F n := by
        rw [hprod]
        exact reeConj_mem_twistedFixed D hg₀ hFg₀ γ
      obtain ⟨hzf, hqf⟩ := fixed_of_mul_mem D.isFrob hS w hst₁ hst₂ hinf hz hq₁ hfix
      obtain ⟨α, hα⟩ := exists_reeConj_eq D hg₀ hFg₀ hzf
      obtain ⟨s, hs⟩ := exists_reeConj_eq D hg₀ hFg₀ hqf
      have hαA : α ∈ A := by
        show κ α ∈ ZGrp (L := L) S
        rw [hα]; exact hz
      have hsS : s ∈ Sg := by
        show κ s ∈ rootSpan ReeTag.F4.tag L S
        rw [hs]; exact hq₁
      have hγ' : γ = α * s := by
        apply hκinj
        rw [map_mul, hα, hs]
        exact hprod.symm
      rw [hγ']
      exact Subgroup.mul_mem_sup hαA hsS

theorem smul_dualRoot_mem_parabolic_gen {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (w u : WeylGroup ReeTag.F4.tag)
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S))
    {J : Set (Fin ReeTag.F4.tag.rank)}
    (hu : (fun α => u • α) '' S = parabolicRoots ReeTag.F4.tag J)
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : γ ∈ parabolicRoots ReeTag.F4.tag J) :
    (u * w * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
      parabolicRoots ReeTag.F4.tag J := by
  rw [← hu] at hγ ⊢
  obtain ⟨β, hβ, rfl⟩ := hγ
  have hβr := hS β hβ
  refine ⟨w • ReeTag.F4.dualRoot β, (hst β hβr).2 hβ, ?_⟩
  show u • (w • ReeTag.F4.dualRoot β) = _
  rw [ReeTag.dualRoot_smul u hβr, mul_smul, mul_smul, inv_smul_smul]

theorem rootSpan_inf_twistedFixed_equiv_a1 (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α)
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S))
    {u : WeylGroup ReeTag.F4.tag} {i j : Fin ReeTag.F4.tag.rank} (hA : A1Pair i j)
    (hΦ : (fun α => u • α) '' S = parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    Nonempty (SL2 K ≃* ↥(rootSpan ReeTag.F4.tag L S ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))) := by
  have hn := canonicalRep_mem_adjointGroup (coxeterSystem ReeTag.F4.tag) L w
  have hperm := CFSG.RankThree.PartOne.TCX.Ree.permAct_conjTwist D.isFrob (permAct_canonicalRep w) u
  have hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)),
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank)) :=
    fun γ hγ => smul_dualRoot_mem_parabolic_gen hS w u hst hΦ hγ
  obtain ⟨⟨e⟩, -⟩ := CFSG.RankThree.PartOne.TCX.Ree.a1_level D hA hK
    (CFSG.RankThree.PartOne.TCX.Ree.conjTwist_mem hn u) hperm hstab
  rw [← hΦ] at e
  exact CFSG.RankThree.PartOne.TCX.Ree.transport_iso u hS _ e

theorem rootSpan_inf_twistedFixed_equiv_b2 (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α)
    (hst : ∀ β, IsRoot ReeTag.F4.tag β → (w • ReeTag.F4.dualRoot β ∈ S ↔ β ∈ S))
    {u : WeylGroup ReeTag.F4.tag}
    (hΦ : (fun α => u • α) '' S = parabolicRoots ReeTag.F4.tag f4B2Support) :
    Nonempty (suzukiGroup a K ≃* ↥(rootSpan ReeTag.F4.tag L S ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))) := by
  have hperm := CFSG.RankThree.PartOne.TCX.Ree.permAct_conjTwist D.isFrob (permAct_canonicalRep w) u
  have hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      (u * w * (ReeTag.F4.weylPerm u)⁻¹) • ReeTag.F4.dualRoot γ ∈
        parabolicRoots ReeTag.F4.tag f4B2Support :=
    fun γ hγ => smul_dualRoot_mem_parabolic_gen hS w u hst hΦ hγ
  obtain ⟨⟨e⟩, -⟩ := CFSG.RankThree.PartOne.TCX.Ree.b2_level D hK hperm hstab
  rw [← hΦ] at e
  exact CFSG.RankThree.PartOne.TCX.Ree.transport_iso u hS _ e

theorem sg_equiv_of {g₀ : ModGL ReeTag.F4.tag L} (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L)
    (w : WeylGroup ReeTag.F4.tag)
    (hFg₀ : Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
    {S : Set (Fin ReeTag.F4.tag.rank → ℤ)} {Sg : Subgroup (ReeTag.F4.reeGamma K a)}
    (hSgm : ∀ γ, γ ∈ Sg ↔ reeConj g₀ γ ∈ rootSpan ReeTag.F4.tag L S) {G₀ : Type} [Group G₀]
    (e : G₀ ≃* ↥(rootSpan ReeTag.F4.tag L S ⊓
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))) :
    Nonempty (Sg ≃* G₀) := by
  have hκinj : Function.Injective (reeConj (K := K) (a := a) g₀) := reeConj_injective g₀
  have hSgeq : Sg = (rootSpan ReeTag.F4.tag L S).comap (reeConj (K := K) (a := a) g₀) :=
    Subgroup.ext hSgm
  have hmap : Sg.map (reeConj (K := K) (a := a) g₀) =
      rootSpan ReeTag.F4.tag L S ⊓
        twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
    rw [hSgeq, Subgroup.map_comap_eq, range_reeConj D hg₀ hFg₀, inf_comm]
  have e1 : Sg ≃* Sg.map (reeConj (K := K) (a := a) g₀) :=
    Sg.equivMapOfInjective (reeConj g₀) hκinj
  exact ⟨((e1.trans (MulEquiv.subgroupCongr hmap)).trans e.symm)⟩

theorem exists_layer_decomp (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (w : WeylGroup ReeTag.F4.tag) {g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L)
    (hFg₀ : Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
    {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (hbp : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1) (hne : rootCharKernel b ≠ ∅)
    (x : ReeTag.F4.reeGamma K a) (hx : reeConj g₀ x = rootDiagUnit ReeTag.F4.tag b) :
    ∃ A Sg : Subgroup (ReeTag.F4.reeGamma K a),
      (∀ γ, γ ∈ A ↔ reeConj g₀ γ ∈ ZGrp (L := L) (rootCharKernel b)) ∧
      (∀ α ∈ A, ∀ s ∈ Sg, α * s = s * α) ∧ A ⊓ Sg = ⊥ ∧
      A ⊔ Sg = Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧ x ∈ A ∧
      (Nonempty (Sg ≃* suzukiGroup a K) ∨ Nonempty (Sg ≃* SL2 K)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hw := (rootDiagUnit_mem_twistedFixed_canonicalRep_iff D.isFrob w b).1 hb
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a) hp hp3 hbp hb1 hw
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have hst : ∀ β, IsRoot ReeTag.F4.tag β →
      (w • ReeTag.F4.dualRoot β ∈ rootCharKernel b ↔ β ∈ rootCharKernel b) := fun β hβ =>
    mem_kernel_iff_smul_dualRoot hp hp2 hbp hw hβ
  have hJne : J ≠ ∅ := by
    rintro rfl
    apply hne
    have h1 : parabolicRoots ReeTag.F4.tag
        (((∅ : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) = ∅ := by
      ext γ
      simp only [parabolicRoots, Finset.coe_empty, Set.mem_empty_iff_false, not_false_eq_true,
        forall_const, Set.mem_ofPred_eq, iff_false]
      rintro ⟨hγ, hz⟩
      exact IsRoot.ne_zero hγ (funext hz)
    rw [h1] at hΦ
    exact Set.image_eq_empty.1 hΦ
  have hA1 : ∀ {i j : Fin ReeTag.F4.tag.rank}, A1Pair i j →
      (J = ({i, j} : Finset (Fin ReeTag.F4.tag.rank))) →
      ∃ A Sg : Subgroup (ReeTag.F4.reeGamma K a),
        (∀ γ, γ ∈ A ↔ reeConj g₀ γ ∈ ZGrp (L := L) (rootCharKernel b)) ∧
        (∀ α ∈ A, ∀ s ∈ Sg, α * s = s * α) ∧ A ⊓ Sg = ⊥ ∧
        A ⊔ Sg = Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧ x ∈ A ∧
        (Nonempty (Sg ≃* suzukiGroup a K) ∨ Nonempty (Sg ≃* SL2 K)) := by
    intro i j hA hJij
    subst hJij
    obtain ⟨A, Sg, hAm, hSgm, hc, hi, hs, hxA⟩ := exists_decomp_gen D hp hp3 w hg₀ hFg₀ hb hbp hb1
      hΦ (a1_split hA) (a1_inf hA) x hx
    obtain ⟨e⟩ := rootSpan_inf_twistedFixed_equiv_a1 D hK w hS hst hA hΦ
    obtain ⟨e'⟩ := sg_equiv_of D hg₀ w hFg₀ hSgm e
    exact ⟨A, Sg, hAm, hc, hi, hs, hxA, Or.inr ⟨e'⟩⟩
  rcases hJ with rfl | h02 | h03 | h13 | h12
  · exact absurd rfl hJne
  · have hJ' : J = ({⟨0, by decide⟩, ⟨2, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h02 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    exact hA1 a1Pair_zero_two hJ'
  · have hJ' : J = ({⟨0, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h03 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    exact hA1 a1Pair_zero_three hJ'
  · have hJ' : J = ({⟨1, by decide⟩, ⟨3, by decide⟩} : Finset (Fin ReeTag.F4.tag.rank)) := by
      ext k
      rw [h13 k, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    exact hA1 a1Pair_one_three hJ'
  · have hJs : (J : Set (Fin ReeTag.F4.tag.rank)) = f4B2Support := by
      ext k
      constructor
      · intro hk
        have hk' := (h12 k).1 hk
        refine (mem_f4B2Support k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · intro hk
        have hk' := (mem_f4B2Support k).1 hk
        refine (h12 k).2 ?_
        rcases hk' with h | h
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
    rw [hJs] at hΦ
    have hsplit : ∀ c : Fin ReeTag.F4.tag.rank → Lˣ,
        ∃ z ∈ ZGrp (L := L) (parabolicRoots ReeTag.F4.tag f4B2Support),
          ∃ q ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support),
            rootDiagUnit ReeTag.F4.tag c = z * q := by
      intro c
      obtain ⟨z, hz, q, hq, h⟩ := rootDiagUnit_eq_mul_ZGrp_b2 (L := L) c
      exact ⟨z, hz, q, by rw [← B2Q_eq_rootSpan]; exact hq, h⟩
    have hinfJ : ZGrp (L := L) (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
        rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag f4B2Support) = ⊥ := by
      rw [← B2Q_eq_rootSpan]
      exact ZGrp_inf_subsystemGroup_b2
    obtain ⟨A, Sg, hAm, hSgm, hc, hi, hs, hxA⟩ := exists_decomp_gen D hp hp3 w hg₀ hFg₀ hb hbp hb1
      hΦ hsplit hinfJ x hx
    obtain ⟨e⟩ := rootSpan_inf_twistedFixed_equiv_b2 D hK w hS hst hΦ
    obtain ⟨e'⟩ := sg_equiv_of D hg₀ w hFg₀ hSgm e
    exact ⟨A, Sg, hAm, hc, hi, hs, hxA, Or.inl ⟨e'⟩⟩

end Decomp

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
