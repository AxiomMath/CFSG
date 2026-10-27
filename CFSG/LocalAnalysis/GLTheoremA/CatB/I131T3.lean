module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T2
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I131

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Wimg (L T : Subgroup G) : Subgroup (PSimple 3 L) :=
  (T.subgroupOf L).map (piS 3 L)

theorem isPGroup_two_Wimg (L T : Subgroup G) (hT2 : IsPGroup 2 T) :
    IsPGroup 2 ↥(Wimg L T) := by
  rintro ⟨w, hw⟩
  unfold Wimg at hw
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw
  obtain ⟨k, hk⟩ := hT2 ⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩
  have hx2 : x ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow, hx2, map_one]

theorem Wimg_ne_bot (L T : Subgroup G) (hT2 : IsPGroup 2 T) (hTL : T ≤ L)
    (hT : ¬ T ≤ GLAPPrimeCoreOf 3 L) : Wimg L T ≠ ⊥ := by
  intro hW
  apply hT
  intro t ht
  let x : ↥L := ⟨t, hTL ht⟩
  have hxW : piS 3 L x ∈ Wimg L T :=
    Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  rw [hW, Subgroup.mem_bot, piS_apply, QuotientGroup.eq_one_iff] at hxW
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  obtain ⟨m, hm⟩ := CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three L
    ⟨QuotientGroup.mk x, hxW⟩
  have hx2 : x ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hz2 : (QuotientGroup.mk x : PQuot 3 L) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hx2]
    rfl
  have hz3 : (QuotientGroup.mk x : PQuot 3 L) ^ 3 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hz1 : (QuotientGroup.mk x : PQuot 3 L) = 1 := by
    have hg : (QuotientGroup.mk x : PQuot 3 L) ^ (2 ^ k).gcd (3 ^ m) = 1 :=
      pow_gcd_eq_one.2 ⟨hz2, hz3⟩
    rw [(Nat.Coprime.pow k m (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, pow_one] at hg
    exact hg
  rw [QuotientGroup.eq_one_iff] at hz1
  rw [glaPPrimeCoreOf_eq_map]
  exact Subgroup.mem_map.2 ⟨x, hz1, rfl⟩

theorem Wimg_normalized (L T : Subgroup G) (a : ↥(Subgroup.normalizer (L : Set G)))
    (ha : ∀ t ∈ T, (a : G) * t * (a : G)⁻¹ ∈ T) (w : PSimple 3 L) (hw : w ∈ Wimg L T) :
    indS 3 L a w ∈ Wimg L T := by
  unfold Wimg at hw ⊢
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw
  rw [indS_piS]
  refine Subgroup.mem_map.2 ⟨indL L a x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
  rw [indL_apply]
  exact ha _ (Subgroup.mem_subgroupOf.1 hx)

theorem card_le_nine_mul_card_centMod
    (L A T : Subgroup G) (hperf : commutator (PQuot 3 L) = ⊤)
    (φ : PSimple 3 L ≃* ↥CFSG.Quasithin.trialityGroup8) (hS : Nat.card (PSimple 3 L) = 211341312)
    (hZ : Subgroup.center (PSimple 3 L) = ⊥)
    (hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PSimple 3 L)) = 3)
    (hTL : T ≤ L) (hT2 : IsPGroup 2 T) (hT : ¬ T ≤ GLAPPrimeCoreOf 3 L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    Nat.card A ≤ 3 ^ 2 * Nat.card ↥(A ⊓ centModSubgroup 3 L) := by
  let ρA : ↥A →* MulAut (PSimple 3 L) := (indS 3 L).comp (Subgroup.inclusion hAN)
  have hρ : ∀ a : ↥A, ρA a = indS 3 L (Subgroup.inclusion hAN a) := fun a => rfl
  have hcomm : ∀ a b : ↥A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  have h3 : ∀ a : ↥A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hA.2 a a.2)
  have hYc : ∀ y ∈ ρA.range, ∀ z ∈ ρA.range, y * z = z * y := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a b]
  have hY3 : ∀ y ∈ ρA.range, y ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, h3 a, map_one]
  have hYW : ∀ y ∈ ρA.range, ∀ w ∈ Wimg L T, y w ∈ Wimg L T := by
    rintro _ ⟨a, rfl⟩ w hw
    rw [hρ]
    exact Wimg_normalized L T _ (fun t ht => (Subgroup.mem_normalizer_iff.1 (hAT a.2) t).1 ht) w hw
  have hW2 : IsPGroup 2 ↥(Wimg L T) := isPGroup_two_Wimg L T hT2
  have hWne : Wimg L T ≠ ⊥ := Wimg_ne_bot L T hT2 hTL hT
  have hcardY : Nat.card ρA.range ≤ 9 :=
    card_le_nine_of_normalizes φ hS hZ hO ρA.range hYc hY3 (Wimg L T) hW2 hWne hYW
  have hK : Nat.card ρA.ker ≤ Nat.card ↥(A ⊓ centModSubgroup 3 L) := by
    refine Nat.card_le_card_of_injective (fun x : ρA.ker =>
      (⟨(x : ↥A).1, Subgroup.mem_inf.2 ⟨(x : ↥A).2, ?_⟩⟩ : ↥(A ⊓ centModSubgroup 3 L))) ?_
    · have hx : ρA (x : ↥A) = 1 := (MonoidHom.mem_ker).1 x.2
      rw [hρ] at hx
      exact centMod_of_indS_eq_one 3 hperf ⟨(x : ↥A).1, hAN (x : ↥A).2⟩ hx
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(A ⊓ centModSubgroup 3 L) => (z : G)) hxy
  have hsplit : Nat.card ↥A = Nat.card ρA.range * Nat.card ρA.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρA.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρA).toEquiv]
  calc Nat.card A = Nat.card ρA.range * Nat.card ρA.ker := hsplit
    _ ≤ 9 * Nat.card ↥(A ⊓ centModSubgroup 3 L) := Nat.mul_le_mul hcardY hK
    _ = 3 ^ 2 * Nat.card ↥(A ⊓ centModSubgroup 3 L) := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.I131

end
