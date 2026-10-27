module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseNoA4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelCore
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent barM)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Proving
open scoped Pointwise

theorem eq_one_of_central_two_element {H : Type*} [Group H] [Finite H]
    (hH : CFSG.pCore 2 H = ⊥) {K : Subgroup H} (hK : IsSubnormal K ⊤) {z : H} (hzK : z ∈ K)
    (hz : ∀ k ∈ K, z * k = k * z) {n : ℕ} (hn : z ^ (2 ^ n) = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.zpowers z with hZdef
  have hZK : Z ≤ K := (Subgroup.zpowers_le).2 hzK
  have hZc : ∀ k ∈ K, ∀ w ∈ Z, k * w * k⁻¹ = w := by
    intro k hk w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : Commute k z := (hz k hk).symm
    exact (hc.zpow_right m).mul_inv_cancel
  have hZn : (Z.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZK]
    intro k hk
    refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · rwa [hZc k hk w hw]
    · have h1 := hZc k⁻¹ (K.inv_mem hk) _ hw
      rw [inv_inv] at h1
      have h2 : w = k⁻¹ * (k * w * k⁻¹) * k := by group
      rw [h2, h1]
      exact hw
  have hZsub : IsSubnormal Z ⊤ := IsSubnormal.step hZK hZn hK
  have hZ2 : IsPGroup 2 Z := fun w => ⟨n, by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp w.2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]⟩
  have hle := CFSG.Quasithin.F6.le_pCoreOf_of_isSubnormal hZsub hZ2
  rw [CFSG.Quasithin.Fan86.Model.pCoreOf_top_eq,
    hH] at hle
  have := hle (Subgroup.mem_zpowers z)
  simpa using this

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

omit [Finite G] in
theorem barHom_comm_iff {a b : ↥X} :
    barHom X a * barHom X b = barHom X b * barHom X a ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 X := by
  constructor
  · intro h
    have h1 : barHom X (a * b * a⁻¹ * b⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      exact (commutatorElement_eq_one_iff_mul_comm.mpr h :)
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp h1
    exact mem_pCoreOf_iff.mpr ⟨_, h2, by simp⟩
  · intro hab
    obtain ⟨y, hy, hyab⟩ := mem_pCoreOf_iff.mp hab
    have : y = a * b * a⁻¹ * b⁻¹ := Subtype.ext (by simpa using hyab)
    rw [this] at hy
    have h1 : barHom X (a * b * a⁻¹ * b⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hy
    simp only [map_mul, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem hlie_of_centralizerInRadical (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hcent : CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralizerInRadical
      (barM X L) (barM X (S ⊓ L))) :
    ∀ g ∈ L, g ^ 3 = 1 → (∀ r ∈ S ⊓ L, g * r * g⁻¹ * r⁻¹ ∈ pCoreOf 2 X) →
      ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ pCoreOf 2 X := by
  classical
  have hLX : L ≤ X := hL.le
  have hSX : S ≤ X := hA.twoRadical.1
  intro g hgL hg3 hgR l hl
  have hgX : g ∈ X := hLX hgL
  set g' : ↥X := ⟨g, hgX⟩ with hg'
  have hcentralizes : ∀ r ∈ barM X (S ⊓ L), barHom X g' * r = r * barHom X g' := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hr
    exact barHom_comm_iff.mpr (hgR _ hx)
  have hmem := hcent (barHom X g') (barHom_mem_barM hgL) hcentralizes
  set Rb := barM X (S ⊓ L) with hRb
  set Lb := barM X L with hLb
  have hRL : Rb ≤ Lb := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hr
    exact barHom_mem_barM hx.2
  have hZc : ∀ z ∈ CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.centerIn Lb,
      z ∈ Lb ∧ ∀ k ∈ Lb, z * k = k * z := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c.2, fun k hk => by
      have := Subgroup.mem_center_iff.mp hc ⟨k, hk⟩
      exact congrArg Subtype.val this.symm⟩
  have hmul : ((CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.centerIn Lb :
      Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) *
        (Rb : Set (↥X ⧸ CFSG.pCore 2 ↥X)) = (Rb : Set (↥X ⧸ CFSG.pCore 2 ↥X)) *
        ((CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.centerIn Lb :
          Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    ext w
    constructor
    · rintro ⟨z, hz, r, hr, rfl⟩
      exact ⟨r, hr, z, hz, ((hZc z hz).2 r (hRL hr)).symm⟩
    · rintro ⟨r, hr, z, hz, rfl⟩
      exact ⟨z, hz, r, hr, ((hZc z hz).2 r (hRL hr))⟩
  have hsup := A4.coe_sup_eq_mul_of_mul_comm hmul
  have hmem' : barHom X g' ∈ ((Rb ⊔ CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.centerIn Lb :
      Subgroup _) : Set _) := hmem
  rw [hsup] at hmem'
  obtain ⟨r, hr, z, hz, hrz⟩ := hmem'
  have hrzc : Commute r z := ((hZc z hz).2 r (hRL hr)).symm
  have hg3' : (barHom X g') ^ 3 = 1 := by
    rw [← map_pow]
    have : g' ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  rw [← hrz, hrzc.mul_pow] at hg3'
  have hr2 : IsPGroup 2 Rb := isPGroup_barM (hA.twoRadical.isPGroup.to_le inf_le_left)
  obtain ⟨a, ha⟩ := hr2 ⟨r, hr⟩
  have ha' : r ^ (2 ^ a) = 1 := congrArg Subtype.val ha
  have hr3 : r ^ 3 = (z ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hg3'
  have hzL : z ∈ Lb := (hZc z hz).1
  have hr3c : ∀ k ∈ Lb, r ^ 3 * k = k * r ^ 3 := by
    intro k hk
    rw [hr3]
    have hzk := (hZc z hz).2 k hk
    have : Commute (z ^ 3) k := (Commute.pow_left (show Commute z k from hzk) 3)
    exact (this.inv_left).eq
  have hr3L : r ^ 3 ∈ Lb := Lb.pow_mem (hRL hr) 3
  have hr3two : (r ^ 3) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ha', one_pow]
  have hK : IsSubnormal Lb ⊤ := hL.component.2.1
  have hH : CFSG.pCore 2 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ :=
    CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' 2
  have h3 : r ^ 3 = 1 := eq_one_of_central_two_element hH hK hr3L hr3c hr3two
  have hr1 : r = 1 := eq_one_of_pow_three_of_pow_two h3 ha'
  simp only [hr1, one_mul] at hrz
  have hcz := (hZc z hz).2
  have hcomm : barHom X g' * barHom X ⟨l, hLX hl⟩ = barHom X ⟨l, hLX hl⟩ * barHom X g' := by
    rw [← hrz]
    exact hcz _ (barHom_mem_barM hl)
  exact barHom_comm_iff.mp hcomm

end CFSG.HardMathSupport.Cooperstein.StructureLie
