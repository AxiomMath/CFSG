module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerTorus
public import CFSG.Quasithin.Background.SmithB45TorF4W
public import CFSG.RankThree.PartOne.KLR.B2Twist

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4

section Dyn

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

omit [CharP L 2] [IsAlgClosed L] in
theorem rootSpan_le_centralizer_of_charKer {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    {c : Fin ReeTag.F4.tag.rank → Lˣ} (hc : ∀ α ∈ S, rootChar c α = 1)
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) :
    rootSpan ReeTag.F4.tag L S ≤ Subgroup.centralizer ({rootDiagUnit ReeTag.F4.tag c} : Set (ModGL ReeTag.F4.tag L)) := by
  refine iSup₂_le fun α hα => ?_
  show rootSubgroup ReeTag.F4.tag L α ≤ _
  intro g hg
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := rootDiagUnit_conj_pinnedX c (hS α hα) t
  rw [hc α hα, Units.val_one, one_mul] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

omit [CharP L 2] [IsAlgClosed L] in
theorem ZGrp_commute_rootSpan {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) {z q : ModGL ReeTag.F4.tag L}
    (hz : z ∈ ZGrp S) (hq : q ∈ rootSpan ReeTag.F4.tag L S) : z * q = q * z := by
  obtain ⟨c, hc, rfl⟩ := mem_ZGrp.1 hz
  have := Subgroup.mem_centralizer_singleton_iff.1
    (rootSpan_le_centralizer_of_charKer hc hS hq)
  exact this.symm

omit [IsAlgClosed L] in
theorem twistMap_mem_rootSpan (hF : IsReeFrob a F) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (w : WeylGroup ReeTag.F4.tag)
    (hst : ∀ γ ∈ S, w • ReeTag.F4.dualRoot γ ∈ S) {q : ModGL ReeTag.F4.tag L}
    (hq : q ∈ rootSpan ReeTag.F4.tag L S) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) q ∈ rootSpan ReeTag.F4.tag L S := by
  have hqa : q ∈ adjointGroup ReeTag.F4.tag L := rootSpan_le_adjointGroup L S hq
  have h1 := hF.mem_rootSpan hS (g := ⟨q, hqa⟩) hq
  have hS' : ∀ γ ∈ ReeTag.F4.dualRoot '' S, IsRoot ReeTag.F4.tag γ := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ReeTag.isRoot_dualRoot (hS γ hγ)
  have h2 := map_conj_rootSpan (L := L) w hS'
  have h3 : canonicalRep (coxeterSystem ReeTag.F4.tag) L w * Fext F q *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ ∈
      rootSpan ReeTag.F4.tag L ((fun γ => w • γ) '' (ReeTag.F4.dualRoot '' S)) := by
    rw [← h2]
    refine ⟨Fext F q, ?_, rfl⟩
    rw [Fext_of_mem F hqa]
    exact h1
  refine rootSpan_mono ?_ h3
  rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
  exact hst γ hγ

theorem twistMap_mem_ZGrp (hF : IsReeFrob a F) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (w : WeylGroup ReeTag.F4.tag)
    (hst : ∀ α ∈ S, ReeTag.F4.dualRoot (w⁻¹ • α) ∈ S) {z : ModGL ReeTag.F4.tag L}
    (hz : z ∈ ZGrp S) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) z ∈ ZGrp S := by
  obtain ⟨c, hc, rfl⟩ := mem_ZGrp.1 hz
  unfold twistMap
  rw [hF.fext_rootDiagUnit c, CFSG.Quasithin.B45Tor.canonicalRep_conj_rootDiagUnit_F4]
  refine mem_ZGrp.2 ⟨_, fun α hα => ?_, rfl⟩
  have hiff := (rootDiagUnit_eq_conj_canonicalRep_iff
    (fun i => rootChar (reeTuple a c) (w⁻¹ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)))
    (reeTuple a c) w).1
    ((CFSG.Quasithin.B45Tor.canonicalRep_conj_rootDiagUnit_F4 w (reeTuple a c)).symm) (w⁻¹ • α)
  rw [smul_inv_smul] at hiff
  rw [hiff, rootChar_reeTuple]
  obtain ⟨k, hk⟩ := reePsi_root a (IsRoot.smul (hS α hα) w⁻¹)
  rw [hk, rootChar_zsmul, hc _ (hst α hα), one_zpow]

omit [CharP L 2] in
theorem ZGrp_le_adjointGroup (S : Set (Fin ReeTag.F4.tag.rank → ℤ)) :
    ZGrp (L := L) S ≤ adjointGroup ReeTag.F4.tag L := by
  rintro _ hz
  obtain ⟨c, -, rfl⟩ := mem_ZGrp.1 hz
  exact torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup c)

theorem fixed_of_mul_mem (hF : IsReeFrob a F) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (w : WeylGroup ReeTag.F4.tag)
    (hst₁ : ∀ γ ∈ S, w • ReeTag.F4.dualRoot γ ∈ S)
    (hst₂ : ∀ α ∈ S, ReeTag.F4.dualRoot (w⁻¹ • α) ∈ S)
    (hinf : ZGrp (L := L) S ⊓ rootSpan ReeTag.F4.tag L S = ⊥)
    {z q : ModGL ReeTag.F4.tag L} (hz : z ∈ ZGrp S) (hq : q ∈ rootSpan ReeTag.F4.tag L S)
    (hfix : z * q ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    z ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      q ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hza := ZGrp_le_adjointGroup S hz
  have hqa := rootSpan_le_adjointGroup L S hq
  have h1 : twistMap F n z * twistMap F n q = z * q := by
    rw [← twistMap_mul n hza hqa]
    exact hfix.2
  have hz' := twistMap_mem_ZGrp hF hS w hst₂ hz
  have hq' := twistMap_mem_rootSpan hF hS w hst₁ hq
  have h2 : z⁻¹ * twistMap F n z = q * (twistMap F n q)⁻¹ := by
    have : twistMap F n z = z * q * (twistMap F n q)⁻¹ := by
      rw [← h1]; group
    rw [this]; group
  have hmem : z⁻¹ * twistMap F n z ∈ ZGrp (L := L) S ⊓ rootSpan ReeTag.F4.tag L S :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hz) hz', h2 ▸ mul_mem hq (inv_mem hq')⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  have hzz : twistMap F n z = z := by
    have := congrArg (fun x => z * x) hmem
    simpa using this
  have hqq : twistMap F n q = q := by
    rw [hzz] at h1
    exact mul_left_cancel h1
  exact ⟨⟨hza, hzz⟩, ⟨hqa, hqq⟩⟩

end Dyn

section Transport

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

omit [IsAlgClosed L] in
theorem canonicalRep_inv_eq (u : WeylGroup ReeTag.F4.tag) :
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L u⁻¹ :=
  (map_inv (CFSG.Quasithin.B45Tor.nuF4 L) u).symm

omit [CharP L 2] [IsAlgClosed L] in
theorem conj_mem_ZGrp (u : WeylGroup ReeTag.F4.tag) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    {z : ModGL ReeTag.F4.tag L} (hz : z ∈ ZGrp S) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L u * z *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ ∈ ZGrp ((fun α => u • α) '' S) := by
  obtain ⟨c, hc, rfl⟩ := mem_ZGrp.1 hz
  rw [CFSG.Quasithin.B45Tor.canonicalRep_conj_rootDiagUnit_F4]
  refine mem_ZGrp.2 ⟨_, fun γ hγ => ?_, rfl⟩
  obtain ⟨α, hα, rfl⟩ := hγ
  have hiff := (rootDiagUnit_eq_conj_canonicalRep_iff
    (fun i => rootChar c (u⁻¹ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))) c u).1
    ((CFSG.Quasithin.B45Tor.canonicalRep_conj_rootDiagUnit_F4 u c).symm) α
  rw [hiff, hc α hα]

theorem image_inv_smul_image {S : Set (Fin ReeTag.F4.tag.rank → ℤ)} (u : WeylGroup ReeTag.F4.tag) :
    (fun α => u⁻¹ • α) '' ((fun α => u • α) '' S) = S := by
  rw [Set.image_image]
  simp

omit [IsAlgClosed L] in
theorem conj_inv_mem_ZGrp {S : Set (Fin ReeTag.F4.tag.rank → ℤ)} (u : WeylGroup ReeTag.F4.tag)
    {z : ModGL ReeTag.F4.tag L} (hz : z ∈ ZGrp ((fun α => u • α) '' S)) :
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ * z *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L u ∈ ZGrp S := by
  have h := conj_mem_ZGrp u⁻¹ hz
  rw [image_inv_smul_image, ← canonicalRep_inv_eq, inv_inv] at h
  exact h

omit [IsAlgClosed L] in
theorem conj_inv_mem_rootSpan {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (u : WeylGroup ReeTag.F4.tag)
    {q : ModGL ReeTag.F4.tag L} (hq : q ∈ rootSpan ReeTag.F4.tag L ((fun α => u • α) '' S)) :
    (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ * q *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L u ∈ rootSpan ReeTag.F4.tag L S := by
  have hS' : ∀ γ ∈ (fun α => u • α) '' S, IsRoot ReeTag.F4.tag γ := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul (hS α hα) u
  have h : (rootSpan ReeTag.F4.tag L ((fun α => u • α) '' S)).map
      (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u⁻¹)).toMonoidHom =
        rootSpan ReeTag.F4.tag L S := by
    rw [map_conj_rootSpan (L := L) u⁻¹ hS', image_inv_smul_image]
  have hmem : canonicalRep (coxeterSystem ReeTag.F4.tag) L u⁻¹ * q *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L u⁻¹)⁻¹ ∈
      (rootSpan ReeTag.F4.tag L ((fun α => u • α) '' S)).map
        (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u⁻¹)).toMonoidHom :=
    ⟨q, hq, rfl⟩
  rw [h, ← canonicalRep_inv_eq u, inv_inv] at hmem
  exact hmem

theorem rootDiagUnit_eq_mul_ZGrp {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (u : WeylGroup ReeTag.F4.tag)
    (hu : (fun α => u • α) '' S = parabolicRoots ReeTag.F4.tag f4B2Support)
    (c : Fin ReeTag.F4.tag.rank → Lˣ) :
    ∃ z ∈ ZGrp (L := L) S, ∃ q ∈ rootSpan ReeTag.F4.tag L S,
      rootDiagUnit ReeTag.F4.tag c = z * q := by
  obtain ⟨z', hz', q', hq', h'⟩ := rootDiagUnit_eq_mul_ZGrp_b2 (L := L)
    (fun i => rootChar c (u⁻¹ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ)))
  rw [← CFSG.Quasithin.B45Tor.canonicalRep_conj_rootDiagUnit_F4] at h'
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L u with hn
  have hzS : n⁻¹ * z' * n ∈ ZGrp (L := L) S := by
    apply conj_inv_mem_ZGrp u
    rwa [hu]
  have hqS : n⁻¹ * q' * n ∈ rootSpan ReeTag.F4.tag L S := by
    apply conj_inv_mem_rootSpan hS u
    rw [hu, ← B2Q_eq_rootSpan]
    exact hq'
  refine ⟨_, hzS, _, hqS, ?_⟩
  calc rootDiagUnit ReeTag.F4.tag c = n⁻¹ * (n * rootDiagUnit ReeTag.F4.tag c * n⁻¹) * n := by
        group
    _ = n⁻¹ * (z' * q') * n := by rw [h']
    _ = _ := by group

theorem ZGrp_inf_rootSpan_eq_bot {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot ReeTag.F4.tag α) (u : WeylGroup ReeTag.F4.tag)
    (hu : (fun α => u • α) '' S = parabolicRoots ReeTag.F4.tag f4B2Support) :
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
      ZGrp (L := L) (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
        subsystemGroup ReeTag.F4.tag L f4B2Support :=
    Subgroup.mem_inf.2 ⟨h1, by rw [← B2Q_eq_rootSpan] at h2; exact h2⟩
  rw [ZGrp_inf_subsystemGroup_b2, Subgroup.mem_bot] at h3
  rw [Subgroup.mem_bot]
  have := congrArg (fun y => (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)⁻¹ * y *
    canonicalRep (coxeterSystem ReeTag.F4.tag) L u) h3
  simpa [mul_assoc] using this

omit [CharP L 2] [IsAlgClosed L] [Field L] in
theorem balanced_b2_counts : ∀ J : Finset (Fin ReeTag.F4.tag.rank), BalancedSupport J →
    kernelCount J 4 = 4 → kernelCount J 2 = 4 → ∀ i, i ∈ J ↔ i.val = 1 ∨ i.val = 2 := by
  decide +kernel

theorem exists_b2_conj {a : ℕ} {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hbp : ∀ i, b i ^ 5 = 1) (hb1 : b ≠ 1) {w : WeylGroup ReeTag.F4.tag}
    (hw : ∀ v, rootChar b (w • v) = rootChar (reeTuple a b) v)
    (hlong : (rootCharKernel b ∩ ReeTag.F4.longRoots).ncard = 4)
    (hshort : (rootCharKernel b ∩ ReeTag.F4.shortRoots).ncard = 4) :
    ∃ u : WeylGroup ReeTag.F4.tag, (fun α => u • α) '' rootCharKernel b =
      parabolicRoots ReeTag.F4.tag f4B2Support := by
  obtain ⟨u, J, hJ, hΦ⟩ := exists_balanced_conj (a := a) (L := L) Nat.prime_five (by norm_num)
    hbp hb1 hw
  have hS : ∀ α ∈ rootCharKernel b, IsRoot ReeTag.F4.tag α := fun α hα => hα.1
  have himg : ∀ T : Set (Fin ReeTag.F4.tag.rank → ℤ), (T = ReeTag.F4.longRoots ∨
      T = ReeTag.F4.shortRoots) →
      (parabolicRoots ReeTag.F4.tag (J : Set (Fin ReeTag.F4.tag.rank)) ∩ T).ncard =
        (rootCharKernel b ∩ T).ncard := by
    intro T hT
    rw [← hΦ]
    have himg : (fun α => u • α) '' rootCharKernel b ∩ T =
        (fun α => u • α) '' (rootCharKernel b ∩ T) := by
      ext β
      constructor
      · rintro ⟨⟨α, hα, rfl⟩, hβ⟩
        refine ⟨α, ⟨hα, ?_⟩, rfl⟩
        rcases hT with rfl | rfl
        · exact ⟨hS α hα, by rw [← lengthParam_smul u α]; exact hβ.2⟩
        · exact ⟨hS α hα, by rw [← lengthParam_smul u α]; exact hβ.2⟩
      · rintro ⟨α, ⟨hα, hαT⟩, rfl⟩
        refine ⟨⟨α, hα, rfl⟩, ?_⟩
        rcases hT with rfl | rfl
        · exact smul_mem_longRoots u hαT
        · exact smul_mem_shortRoots u hαT
    rw [himg]
    exact Set.ncard_image_of_injective _ (MulAction.injective u)
  have h1 := himg _ (Or.inl rfl)
  have h2 := himg _ (Or.inr rfl)
  rw [ncard_parabolic_inter_long, hlong] at h1
  rw [ncard_parabolic_inter_short, hshort] at h2
  have hJs := balanced_b2_counts J hJ h1 h2
  refine ⟨u, ?_⟩
  rw [hΦ]
  congr 1
  ext k
  rw [Finset.mem_coe, hJs k]
  refine Iff.trans ?_ (mem_f4B2Support k).symm
  constructor
  · rintro (h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  · rintro (h | h)
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)

end Transport
end CFSG.HardMathSupport.Malle.LocalAction
