module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralLift

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin.SmithC27
open scoped commutatorElement

section Quasisimple

variable {P Q : Type*} [Group P] [Group Q]

theorem isQuasisimple_of_central_quotient (π : P →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center P) (hP : CFSG.IsQuasisimple P) :
    CFSG.IsQuasisimple Q ∧ Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have : Group.IsPerfect P := hP.1
  have e := quotCenterEquivOfSurjective π hπ hker
  refine ⟨⟨Group.IsPerfect.ofSurjective hπ, (MulEquiv.isSimpleGroup_congr e).mp hP.2.1, ?_⟩,
    ⟨e⟩⟩
  obtain ⟨a, b, hab⟩ := hP.2.2
  exact ⟨e a, e b, fun h => hab (by simpa using congrArg e.symm h)⟩

end Quasisimple

variable {Γ : Type} [Group Γ]

theorem exists_mul_of_mem_sup {C R : Subgroup Γ} (hCn : C ≤ Subgroup.normalizer (R : Set Γ))
    {x : Γ} (hx : x ∈ C ⊔ R) : ∃ c ∈ C, ∃ r ∈ R, c * r = x := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right C R hCn
  have hx' : x ∈ (↑(C ⊔ R) : Set Γ) := hx
  rw [h] at hx'
  exact hx'

theorem mem_center_of_mem_inf_of_quasisimple [Finite Γ] {C R : Subgroup Γ}
    (hq : CFSG.IsQuasisimple ↥C) (hR2 : IsPGroup 2 R)
    (hCn : C ≤ Subgroup.normalizer (R : Set Γ)) {c : ↥C} (hc : (c : Γ) ∈ R) :
    c ∈ Subgroup.center ↥C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥C := (R ⊓ C).subgroupOf C with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    have e : ((g * n * g⁻¹ : ↥C) : Γ) = (g : Γ) * n * (g : Γ)⁻¹ := by simp
    rw [e]
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hCn g.2) n).mp hn.1, ?_⟩
    rw [← e]; exact (g * n * g⁻¹ : ↥C).2⟩
  set q := QuotientGroup.mk' (Subgroup.center ↥C) with hqdef
  have hsimple := hq.2.1
  have hNm : (N.map q).Normal := Subgroup.Normal.map hNn q (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hNm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map q) with hbot | htop
  · have hle : N ≤ q.ker := Subgroup.map_eq_bot_iff _ |>.mp hbot
    rw [hqdef, QuotientGroup.ker_mk'] at hle
    exact hle (show c ∈ N from ⟨hc, c.2⟩)
  · exfalso
    have hN2 : IsPGroup 2 N := by
      refine (hR2.to_le (inf_le_left : R ⊓ C ≤ R)).of_equiv ?_
      exact (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ⊓ C ≤ C)).symm.trans (MulEquiv.refl _)
    have hS2 : IsPGroup 2 (↥C ⧸ Subgroup.center ↥C) := by
      refine hN2.of_surjective (q.comp N.subtype) ?_
      intro y
      have : y ∈ N.map q := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨x, hx, hxy⟩ := this
      exact ⟨⟨x, hx⟩, hxy⟩
    have hnil : Group.IsNilpotent (↥C ⧸ Subgroup.center ↥C) := hS2.isNilpotent
    have hsolv : Group.IsSolvable (↥C ⧸ Subgroup.center ↥C) := by
      have := hnil; exact IsNilpotent.to_isSolvable
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := ↥C ⧸ Subgroup.center ↥C)).mpr hsolv
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (hcomm a b)

theorem commutator_mem_of_mem_normalizer {R : Subgroup Γ} {g r : Γ}
    (hg : g ∈ Subgroup.normalizer (R : Set Γ)) (hr : r ∈ R) : ⁅r, g⁆ ∈ R ∧ ⁅g, r⁆ ∈ R := by
  have h1 : g * r⁻¹ * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg r⁻¹).mp (inv_mem hr)
  have h2 : g * r * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg r).mp hr
  refine ⟨?_, ?_⟩
  · have : ⁅r, g⁆ = r * (g * r⁻¹ * g⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]; exact mul_mem hr h1
  · have : ⁅g, r⁆ = (g * r * g⁻¹) * r⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]; exact mul_mem h2 (inv_mem hr)

theorem leviModR_of_leviStructure [Finite Γ] {L R : Subgroup Γ} (hR2 : IsPGroup 2 R)
    (h : LeviStructure L R) : LeviModR L R := by
  obtain ⟨n, C, D, hRD, hDY, hDs, hC, hcomm, hY⟩ := h
  have hRY : R ≤ L ⊓ Subgroup.normalizer (R : Set Γ) := hRD.trans hDY
  have hCn : ∀ i, C i ≤ Subgroup.normalizer (R : Set Γ) := fun i => (hC i).1.trans inf_le_right
  refine ⟨n, fun i => C i ⊔ R, D, hRD, hDY, hDs, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hCY, hq, hcl, hDn⟩ := hC i
    have hVn : C i ⊔ R ≤ Subgroup.normalizer (R : Set Γ) :=
      sup_le (hCn i) Subgroup.le_normalizer
    have : (R.subgroupOf (C i ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hVn
    refine ⟨le_sup_right, sup_le hCY hRY, ?_, hDn⟩
    set φ := QuotientGroup.mk' (R.subgroupOf (C i ⊔ R)) with hφ
    set ψ : ↥(C i) →* (↥(C i ⊔ R) ⧸ R.subgroupOf (C i ⊔ R)) :=
      φ.comp (Subgroup.inclusion le_sup_left) with hψ
    have hψs : Function.Surjective ψ := by
      intro y
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ y
      obtain ⟨c, hc, r, hr, hcr⟩ := exists_mul_of_mem_sup (hCn i) v.2
      refine ⟨⟨c, hc⟩, ?_⟩
      have hv : v = Subgroup.inclusion le_sup_left ⟨c, hc⟩ *
          (⟨r, Subgroup.mem_sup_right hr⟩ : ↥(C i ⊔ R)) := Subtype.ext hcr.symm
      rw [hψ, MonoidHom.comp_apply, hv, map_mul]
      have : φ (⟨r, Subgroup.mem_sup_right hr⟩ : ↥(C i ⊔ R)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hr)
      rw [this, mul_one]
    have hψk : ψ.ker ≤ Subgroup.center ↥(C i) := by
      intro c hc
      have h1 : φ (Subgroup.inclusion le_sup_left c) = 1 := hc
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_subgroupOf] at h2
      exact mem_center_of_mem_inf_of_quasisimple hq hR2 (hCn i) h2
    obtain ⟨hQq, ⟨e⟩⟩ := isQuasisimple_of_central_quotient ψ hψs hψk hq
    exact ⟨_, inferInstance, φ, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _, hQq,
      isClassicalTwoOrG2_of_mulEquiv e hcl⟩
  · intro i j hij
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨c, hc, r, hr, rfl⟩ := exists_mul_of_mem_sup (hCn i) ha
    obtain ⟨d, hd, s, hs, rfl⟩ := exists_mul_of_mem_sup (hCn j) hb
    have hcN := hCn i hc
    have hdN := hCn j hd
    have hdsN : d * s ∈ Subgroup.normalizer (R : Set Γ) :=
      mul_mem hdN (Subgroup.le_normalizer hs)
    have hcd : ⁅c, d⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (hcomm i j hij hc) d hd).symm
    have e1 : ⁅c * r, d * s⁆ = c * ⁅r, d * s⁆ * c⁻¹ * ⁅c, d * s⁆ := by
      simp only [commutatorElement_def]; group
    have e2 : ⁅c, d * s⁆ = ⁅c, d⁆ * (d * ⁅c, s⁆ * d⁻¹) := by
      simp only [commutatorElement_def]; group
    have h1 : ⁅r, d * s⁆ ∈ R := (commutator_mem_of_mem_normalizer hdsN hr).1
    have h2 : ⁅c, s⁆ ∈ R := (commutator_mem_of_mem_normalizer hcN hs).2
    have h3 : c * ⁅r, d * s⁆ * c⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hcN _).mp h1
    have h4 : d * ⁅c, s⁆ * d⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hdN _).mp h2
    rw [e1, e2, hcd, one_mul]
    exact mul_mem h3 h4
  · apply le_antisymm
    · rw [hY]
      refine sup_le le_sup_left (iSup_le fun i => ?_)
      exact (le_sup_left : C i ≤ C i ⊔ R).trans ((le_iSup (fun i => C i ⊔ R) i).trans le_sup_right)
    · exact sup_le hDY (iSup_le fun i => sup_le (hC i).1 hRY)

theorem lieInputStatement_of_simple (hS : LieInputSimple) : LieInputStatement := by
  refine ⟨fun Γ _ _ L R hc hR => ?_, fun Γ _ _ L R hc hR hne => ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR2 : IsPGroup 2 R := by
      rw [hR]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hlev := leviStructure_of_simple hS hc hR
    exact ⟨hlev, leviModR_of_leviStructure hR2 hlev⟩
  · exact centralizerInRadical_of_simple hS hc hR hne

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
