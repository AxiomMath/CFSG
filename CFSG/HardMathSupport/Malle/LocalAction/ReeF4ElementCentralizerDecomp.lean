module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerSuzuki
public import CFSG.RankThree.PartOne.KLR.Master

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

@[expose] def reeConj (g₀ : ModGL ReeTag.F4.tag L) :
    ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag L :=
  (MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a)

omit [IsAlgClosure K L] in
theorem reeConj_apply (g₀ : ModGL ReeTag.F4.tag L) (γ : ReeTag.F4.reeGamma K a) :
    reeConj g₀ γ = g₀⁻¹ * thetaGamma L a γ * g₀ := by
  simp [reeConj]

omit [IsAlgClosure K L] in
theorem reeConj_injective (g₀ : ModGL ReeTag.F4.tag L) :
    Function.Injective (reeConj (K := K) (a := a) g₀) := by
  intro d₁ d₂ h
  rw [reeConj_apply, reeConj_apply] at h
  have h1 := mul_left_cancel (mul_right_cancel h)
  exact thetaGamma_injective L h1

omit [IsAlgClosure K L] in
theorem reeConj_mem_twistedFixed {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    (γ : ReeTag.F4.reeGamma K a) : reeConj g₀ γ ∈ twistedFixed D.F n := by
  rw [reeConj_apply]
  exact conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L γ) (D.fext_theta γ)

theorem exists_reeConj_eq {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    {u : ModGL ReeTag.F4.tag L} (hu : u ∈ twistedFixed D.F n) :
    ∃ γ : ReeTag.F4.reeGamma K a, reeConj g₀ γ = u := by
  obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀ hFg₀ hu
  obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hadj hfix
  refine ⟨γ, ?_⟩
  rw [reeConj_apply, hγ]
  group

theorem range_reeConj {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n) :
    (reeConj (K := K) (a := a) g₀).range = twistedFixed D.F n := by
  ext u
  constructor
  · rintro ⟨γ, rfl⟩
    exact reeConj_mem_twistedFixed D hg₀ hFg₀ γ
  · intro hu
    exact exists_reeConj_eq D hg₀ hFg₀ hu

end Conj

section Decomp

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem exists_decomp_of_kernel (hK : Nat.card K = 2 ^ (2 * a + 1))
    (w : WeylGroup ReeTag.F4.tag) {g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L)
    (hFg₀ : Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
    {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (hbp : ∀ i, b i ^ 5 = 1) (hb1 : b ≠ 1)
    (hlong : (rootCharKernel b ∩ ReeTag.F4.longRoots).ncard = 4)
    (hshort : (rootCharKernel b ∩ ReeTag.F4.shortRoots).ncard = 4)
    (x : ReeTag.F4.reeGamma K a) (hx : reeConj g₀ x = rootDiagUnit ReeTag.F4.tag b) :
    ∃ A Sg : Subgroup (ReeTag.F4.reeGamma K a),
      (∀ γ, γ ∈ A ↔ reeConj g₀ γ ∈ ZGrp (L := L) (rootCharKernel b)) ∧
      (∀ γ, γ ∈ Sg ↔ reeConj g₀ γ ∈ rootSpan ReeTag.F4.tag L (rootCharKernel b)) ∧
      (∀ α ∈ A, ∀ s ∈ Sg, α * s = s * α) ∧ A ⊓ Sg = ⊥ ∧
      A ⊔ Sg = Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)) ∧ x ∈ A ∧
      Nonempty (Sg ≃* suzukiGroup a K) := by
  classical
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
    mem_kernel_iff_smul_dualRoot Nat.prime_five (by norm_num) hbp hw hβ
  have hst₁ : ∀ γ ∈ S, w • ReeTag.F4.dualRoot γ ∈ S := fun γ hγ => (hst γ (hS γ hγ)).2 hγ
  have hst₂ : ∀ α ∈ S, ReeTag.F4.dualRoot (w⁻¹ • α) ∈ S := by
    intro α hα
    have hr : IsRoot ReeTag.F4.tag (w⁻¹ • α) := IsRoot.smul (hS α hα) w⁻¹
    have hβ : IsRoot ReeTag.F4.tag (ReeTag.F4.dualRoot (w⁻¹ • α)) := ReeTag.isRoot_dualRoot hr
    refine (hst _ hβ).1 ?_
    rw [ReeTag.dualRoot_dualRoot hr, smul_inv_smul]
    exact hα
  obtain ⟨u, hΦ⟩ := exists_b2_conj hbp hb1 hw hlong hshort
  have hsplit := rootDiagUnit_eq_mul_ZGrp (L := L) hS u hΦ
  have hinf := ZGrp_inf_rootSpan_eq_bot (L := L) hS u hΦ
  have hordW : ¬ 5 ∣ Nat.card (WeylGroup ReeTag.F4.tag) :=
    not_dvd_card_weylGroup_F4 Nat.prime_five (by norm_num)
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
  refine ⟨A, Sg, fun γ => Iff.rfl, fun γ => Iff.rfl, ?_, ?_, ?_, hxA, ?_⟩
  · intro α hα s hs
    apply hκinj
    rw [map_mul, map_mul]
    exact ZGrp_commute_rootSpan hS hα hs
  · rw [eq_bot_iff]
    intro γ hγ
    have h1 := hinf
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
      have hadj : κ γ ∈ adjointGroup ReeTag.F4.tag L := (reeConj_mem_twistedFixed D hg₀ hFg₀ γ).1
      obtain ⟨t, ht, q, hq, htq⟩ := mem_torus_mul_rootSpan_of_commute Nat.prime_five hordW hbp hb1
        hS hSn (fun _ h => h) hadj hcomm
      obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      obtain ⟨z, hz, q₀, hq₀, hzq⟩ := hsplit c
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
  · obtain ⟨e⟩ := rootSpan_inf_twistedFixed_mulEquiv_suzuki D hK w hb hbp hb1 hlong hshort
    have hmap : Sg.map κ = rootSpan ReeTag.F4.tag L S ⊓ twistedFixed D.F n := by
      rw [hSg, Subgroup.map_comap_eq, range_reeConj D hg₀ hFg₀, inf_comm]
    have e1 : Sg ≃* Sg.map κ := Sg.equivMapOfInjective κ hκinj
    exact ⟨(e1.trans (MulEquiv.subgroupCongr hmap)).trans e⟩

end Decomp
end CFSG.HardMathSupport.Malle.LocalAction
