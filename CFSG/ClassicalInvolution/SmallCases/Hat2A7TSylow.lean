module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TGold
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Assembly

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Sylow

variable {F : Type} [Group F] [Finite F]

omit [Finite F] in
theorem isPGroup_cliqueGrp' (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F) {K : Subgroup F}
    (hK : IsMember K) : IsPGroup 2 (cliqueGrp K) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := cliqueGrp_sq hZ IH hK x.2
  simpa [pow_two] using this

variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)

include hZ IH in
theorem exists_sylow_le_normalizer_of_key {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (KL : ∀ a ∈ cliqueGrp K, a ≠ 1 → ∀ g : F,
      g * a * g⁻¹ ∈ Subgroup.normalizer (cliqueGrp K : Set F) →
        g ∈ Subgroup.normalizer (cliqueGrp K : Set F)) :
    ∃ T : Sylow 2 F, cliqueGrp K ≤ (T : Subgroup F) ∧
      (T : Subgroup F) ≤ Subgroup.normalizer (cliqueGrp K : Set F) := by
  have hKm : IsMember K := ⟨z, hK⟩
  set A : Subgroup F := cliqueGrp K with hA
  set H : Subgroup F := Subgroup.normalizer (A : Set F) with hH
  have hA2 : IsPGroup 2 A := isPGroup_cliqueGrp' hZ IH hKm
  have hz : z ∈ A := Subgroup.subset_closure (mem_cliqueInv_self hK)
  have hz1 : z ≠ 1 := by
    intro h
    have := hK.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  set R : Subgroup F := (P₀ : Subgroup ↥H).map H.subtype with hR
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := P₀.isPGroup'.map H.subtype
  have hAR : A ≤ R := by
    have hAn : (A.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
    have hA'2 : IsPGroup 2 ↥(A.subgroupOf H) := hA2.comap_subtype
    have h1 := hA'2.le_sylow_of_normal P₀
    intro x hx
    exact ⟨⟨x, Subgroup.le_normalizer hx⟩, h1 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨T, hRT⟩ := hR2.exists_le_sylow
  have hTH : (T : Subgroup F) ⊓ H ≤ R := by
    have hQ2 : IsPGroup 2 ↥(((T : Subgroup F) ⊓ H).subgroupOf H) :=
      (T.isPGroup'.to_inf_left (K := H)).comap_subtype
    have hPQ : (P₀ : Subgroup ↥H) ≤ ((T : Subgroup F) ⊓ H).subgroupOf H := fun p hp =>
      Subgroup.mem_subgroupOf.mpr ⟨hRT ⟨p, hp, rfl⟩, p.2⟩
    have hQeq := P₀.is_maximal' hQ2 hPQ
    intro x hx
    have h1 : (⟨x, hx.2⟩ : ↥H) ∈ ((T : Subgroup F) ⊓ H).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [hQeq] at h1
    exact ⟨_, h1, rfl⟩
  have hex : ∃ a₀ ∈ A, a₀ ≠ 1 ∧ ∀ r ∈ R, a₀ * r = r * a₀ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have _inst : Group.IsNilpotent ↥R := hR2.isNilpotent
    have hAn : (A.subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAR).mpr hRH
    have hne : A.subgroupOf R ≠ ⊥ := by
      rw [Ne, Subgroup.eq_bot_iff_forall]
      intro h
      have := h ⟨z, hAR hz⟩ (Subgroup.mem_subgroupOf.mpr hz)
      exact hz1 (congrArg Subtype.val this)
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    refine ⟨((y : ↥R) : F), Subgroup.mem_subgroupOf.mp y.2.1, ?_, fun r hr => ?_⟩
    · intro h
      apply hy1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    · have := Subgroup.mem_center_iff.mp y.2.2 ⟨r, hr⟩
      exact (congrArg Subtype.val this).symm
  have hnorm : ∀ x ∈ (T : Subgroup F), x ∈ Subgroup.normalizer (R : Set F) → x ∈ R := by
    intro x hxT hxR
    obtain ⟨a₀, ha₀A, ha₀1, -⟩ := hex
    have hb : x * a₀ * x⁻¹ ∈ H :=
      hRH ((Subgroup.mem_normalizer_iff.mp hxR a₀).mp (hAR ha₀A))
    exact hTH ⟨hxT, KL a₀ ha₀A ha₀1 x hb⟩
  have hTR : (T : Subgroup F) ≤ R := by
    by_contra hnle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have _inst : Group.IsNilpotent ↥(T : Subgroup F) := T.isPGroup'.isNilpotent
    have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥(T : Subgroup F))
    have hR'top : R.subgroupOf (T : Subgroup F) < ⊤ := lt_top_iff_ne_top.mpr fun h =>
      hnle fun x hx => by
        have : (⟨x, hx⟩ : ↥(T : Subgroup F)) ∈ R.subgroupOf (T : Subgroup F) :=
          h ▸ Subgroup.mem_top _
        exact this
    obtain ⟨y, hy, hyR'⟩ := IsConcreteLE.exists_of_lt (hNC _ hR'top)
    apply hyR'
    have hyN : (y : F) ∈ Subgroup.normalizer (R : Set F) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      have hyT : (y : F) ∈ (T : Subgroup F) := y.2
      constructor
      · intro ht
        have h1 : (⟨t, hRT ht⟩ : ↥(T : Subgroup F)) ∈ R.subgroupOf (T : Subgroup F) := ht
        exact (Subgroup.mem_normalizer_iff.mp hy _).mp h1
      · intro ht
        have htT : t ∈ (T : Subgroup F) := by
          have := (T : Subgroup F).mul_mem ((T : Subgroup F).mul_mem ((T : Subgroup F).inv_mem hyT)
            (hRT ht)) hyT
          simpa [mul_assoc] using this
        have h1 : y * (⟨t, htT⟩ : ↥(T : Subgroup F)) * y⁻¹ ∈ R.subgroupOf (T : Subgroup F) := ht
        exact (Subgroup.mem_normalizer_iff.mp hy ⟨t, htT⟩).mpr h1
    exact hnorm y y.2 hyN
  exact ⟨T, hAR.trans hRT, hTR.trans hRH⟩

end Sylow

section Final

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem false_of_key (hnab : ∃ a b : F, a * b ≠ b * a)
    (GS : GoldschmidtStronglyClosedExponent) (IH : ClassicalCommuteBelow F)
    {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (KL : ∀ a ∈ cliqueGrp K, a ≠ 1 → ∀ g : F,
      g * a * g⁻¹ ∈ Subgroup.normalizer (cliqueGrp K : Set F) →
        g ∈ Subgroup.normalizer (cliqueGrp K : Set F)) : False := by
  have hZ : CenterTrivial F := fun x hx => center_trivial_of_simple hnab x hx
  obtain ⟨T, hAT, hTH⟩ := exists_sylow_le_normalizer_of_key hZ IH hK KL
  refine false_of_cliqueGrp_strongly_closed hnab GS hZ IH hK T hAT ?_
  intro a ha g hg
  by_cases ha1 : a = 1
  · subst ha1
    simp
  · have hgH : g ∈ Subgroup.normalizer (cliqueGrp K : Set F) := KL a ha ha1 g (hTH hg)
    exact (Subgroup.mem_normalizer_iff.mp hgH a).mp ha

end Final

end CFSG.ClassicalInvolution.Hat2A7T
