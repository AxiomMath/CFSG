module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

variable {X : Type} [Group X]

theorem exists_isSylowOf_le [Finite X] {L R : Subgroup X} (hR : IsPGroup 2 R) (hRL : R ≤ L) :
    ∃ P : Subgroup X, IsSylowOf 2 P L ∧ R ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' : IsPGroup 2 (R.subgroupOf L) := hR.comap_subtype
  obtain ⟨Q', hQ'⟩ := hR'.exists_le_sylow
  refine ⟨(Q' : Subgroup L).map L.subtype, ⟨Q', rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hRL hx⟩, hQ' hx, rfl⟩

theorem exists_rightConjugate_le_of_isSylowOf [Finite X] {P L R : Subgroup X}
    (hP : IsSylowOf 2 P L) (hR : IsPGroup 2 R) (hRL : R ≤ L) :
    ∃ c ∈ L, rightConjugate R c ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := hP.exists_sylow_eq_subgroupOf
  have hR' : IsPGroup 2 (R.subgroupOf L) := hR.comap_subtype
  obtain ⟨Q', hQ'⟩ := hR'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq L Q' P'
  refine ⟨((c⁻¹ : L) : X), (c⁻¹).2, fun x hx => ?_⟩
  rw [mem_rightConjugate_iff] at hx
  have hx' : (c : X)⁻¹ * x * c ∈ R := by simpa using hx
  have hrL : (c : X)⁻¹ * x * c ∈ L := hRL hx'
  have hxL : x ∈ L := by
    have heq : x = (c : X) * ((c : X)⁻¹ * x * c) * (c : X)⁻¹ := by group
    rw [heq]
    exact L.mul_mem (L.mul_mem c.2 hrL) (L.inv_mem c.2)
  have hmemQ : (⟨(c : X)⁻¹ * x * c, hrL⟩ : L) ∈ (Q' : Subgroup L) := hQ' hx'
  have hmemP' : (⟨x, hxL⟩ : L) ∈ (P' : Subgroup L) := by
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    convert hmemQ using 1
    apply Subtype.ext
    simp [MulAut.smul_def, mul_assoc]
  rw [hP'] at hmemP'
  exact hmemP'

theorem exists_rightConjugate_eq_of_isSylowOf [Finite X] {P P' L : Subgroup X}
    (hP : IsSylowOf 2 P L) (hP' : IsSylowOf 2 P' L) : ∃ c ∈ L, rightConjugate P' c = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hle⟩ := exists_rightConjugate_le_of_isSylowOf hP hP'.isPGroup hP'.le
  refine ⟨c, hc, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [rightConjugate_card, hP.card_eq, hP'.card_eq]

theorem card_le_of_isSylowOf [Finite X] {P L R : Subgroup X} (hP : IsSylowOf 2 P L)
    (hR : IsPGroup 2 R) (hRL : R ≤ L) : Nat.card R ≤ Nat.card P := by
  obtain ⟨c, -, hle⟩ := exists_rightConjugate_le_of_isSylowOf hP hR hRL
  rw [← rightConjugate_card R c]
  exact Subgroup.card_le_of_le hle

theorem rightConjugate_normalizer (A : Subgroup X) (g : X) :
    rightConjugate (Subgroup.normalizer (A : Set X)) g =
      Subgroup.normalizer (rightConjugate A g : Set X) := by
  refine le_antisymm (Subgroup.le_normalizer_map _) fun x hx => ?_
  rw [mem_rightConjugate_iff, Subgroup.mem_normalizer_iff]
  rw [Subgroup.mem_normalizer_iff] at hx
  intro a
  have h := hx (g⁻¹ * a * g)
  rw [mem_rightConjugate_iff, mem_rightConjugate_iff] at h
  have h1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  have h2 : g * (x * (g⁻¹ * a * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * a * (g * x * g⁻¹)⁻¹ := by group
  rw [h1, h2] at h
  exact h

theorem rightConjugate_centralizer (A : Subgroup X) (g : X) :
    rightConjugate (Subgroup.centralizer (A : Set X)) g =
      Subgroup.centralizer (rightConjugate A g : Set X) := by
  ext x
  rw [mem_rightConjugate_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx b hb
    rw [SetLike.mem_coe, mem_rightConjugate_iff] at hb
    have h := hx _ hb
    calc b * x = g⁻¹ * ((g * b * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * b * g⁻¹)) * g := by rw [h]
      _ = x * b := by group
  · intro hx a ha
    have hb : g⁻¹ * a * g ∈ (rightConjugate A g : Set X) := conj_mem_rightConjugate ha g
    have h := hx _ hb
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * a := by group

theorem normalizer_le_normalizer_centralizer (A : Subgroup X) :
    Subgroup.normalizer (A : Set X) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set X) : Set X) := by
  intro y hy
  rw [← rightConjugate_eq_self_iff, rightConjugate_centralizer,
    (rightConjugate_eq_self_iff A y).mpr hy]

theorem isMulCommutative_of_le {A B : Subgroup X} (hAB : A ≤ B) (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hB ⊢
  exact hAB.trans (hB.trans (Subgroup.centralizer_le hAB))

theorem isMulCommutative_rightConjugate {A : Subgroup X} (hA : IsMulCommutative A) (g : X) :
    IsMulCommutative (rightConjugate A g) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hA ⊢
  rw [← rightConjugate_centralizer]
  exact rightConjugate_le_rightConjugate hA g

@[expose] def omegaOne (P : Subgroup X) : Subgroup X :=
  Subgroup.closure {x | x ∈ P ∧ x ^ 2 = 1}

@[expose] def QuotientRankTwo (N M : Subgroup X) : Prop :=
  ∃ u ∈ N, ∃ v ∈ N, u ∉ M ∧ v ∉ M ∧ u * v ∉ M ∧ u ^ 2 ∈ M ∧ v ^ 2 ∈ M ∧
    u * v * u⁻¹ * v⁻¹ ∈ M

theorem omegaOne_le (P : Subgroup X) : omegaOne P ≤ P :=
  (Subgroup.closure_le P).mpr fun _ hx => hx.1

theorem omegaOne_mono {P P' : Subgroup X} (h : P ≤ P') : omegaOne P ≤ omegaOne P' :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem mem_omegaOne {P : Subgroup X} {x : X} (hx : x ∈ P) (hx2 : x ^ 2 = 1) :
    x ∈ omegaOne P :=
  Subgroup.subset_closure ⟨hx, hx2⟩

theorem le_omegaOne {P : Subgroup X} (h : ∀ x ∈ P, x ^ 2 = 1) : P ≤ omegaOne P :=
  fun x hx => mem_omegaOne hx (h x hx)

theorem rightConjugate_omegaOne (P : Subgroup X) (g : X) :
    rightConjugate (omegaOne P) g = omegaOne (rightConjugate P g) := by
  unfold rightConjugate omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hy2⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ hy, by rw [← map_pow, hy2, map_one]⟩
  · rintro ⟨⟨y, hy, rfl⟩, hy2⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    rw [← map_pow] at hy2
    exact (MulEquiv.map_eq_one_iff _).mp hy2

theorem mem_omegaOne_iff {P : Subgroup X} (hP : IsMulCommutative P) {x : X} :
    x ∈ omegaOne P ↔ x ∈ P ∧ x ^ 2 = 1 := by
  refine ⟨fun hx => ?_, fun hx => mem_omegaOne hx.1 hx.2⟩
  rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hP
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨P.one_mem, one_pow 2⟩
  | mul y z _ _ hy hz =>
    refine ⟨P.mul_mem hy.1 hz.1, ?_⟩
    have hyz : y * z = z * y := (Subgroup.mem_centralizer_iff.mp (hP hz.1) y hy.1)
    rw [pow_two, show y * z * (y * z) = (y * y) * (z * z) by
      rw [mul_assoc, ← mul_assoc z, ← hyz, mul_assoc, mul_assoc], ← pow_two, ← pow_two, hy.2,
      hz.2, one_mul]
  | inv y _ hy => exact ⟨P.inv_mem hy.1, by rw [inv_pow, hy.2, inv_one]⟩

end CFSG.ComponentClassification.AschbacherTheorem3
