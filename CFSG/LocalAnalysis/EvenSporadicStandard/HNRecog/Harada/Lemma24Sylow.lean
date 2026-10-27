module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Orbit
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

theorem eq_of_le_of_sylow_data {G : Type} [Group G] [Finite G] {a : G} {τ : G → Prop}
    (hτ : ∀ (g x : G), τ x → τ (g * x * g⁻¹))
    {P E : Subgroup G} (hP2 : IsPGroup 2 P) (hPcard : Nat.card P = 64) (hEP : E ≤ P)
    (hEab : IsMulCommutative E) (hEcard : Nat.card E = 16)
    (hEuniq : ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B = 16 → B = E)
    (hT : Set.ncard {x : G | x ∈ E ∧ τ x} = 10)
    (hmove : ∀ x ∈ E, τ x → ∃ p ∈ P, p * x * p⁻¹ ≠ x)
    (h32 : ∀ x ∈ E, τ x → ∀ R : Subgroup G,
      R ≤ centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G) → IsPGroup 2 R → Nat.card R ≤ 32)
    {Q : Subgroup G} (hQa : Q ≤ centralizer ({a} : Set G)) (hQ2 : IsPGroup 2 Q) (hPQ : P ≤ Q) :
    Q = P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  let N : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ Q
  have hN_le_normalizer : N ≤ Subgroup.normalizer (P : Set G) := inf_le_left
  have hN_le_Q : N ≤ Q := inf_le_right
  have hP_sub_ne_top : P.subgroupOf Q ≠ ⊤ := by
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hne (le_antisymm htop hPQ)
  have hP_sub_lt_top : P.subgroupOf Q < ⊤ := lt_top_iff_ne_top.mpr hP_sub_ne_top
  have hnc : NormalizerCondition ↥Q := by
    haveI : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    exact Group.normalizerCondition_of_isNilpotent
  have hlt : P.subgroupOf Q < Subgroup.normalizer (P.subgroupOf Q) := hnc _ hP_sub_lt_top
  have hN_lt : P < N := by
    have hle : (P.subgroupOf Q).map Q.subtype ≤
        (Subgroup.normalizer (P.subgroupOf Q)).map Q.subtype := Subgroup.map_mono hlt.le
    have hne' : (P.subgroupOf Q).map Q.subtype ≠
        (Subgroup.normalizer (P.subgroupOf Q)).map Q.subtype :=
      fun h => hlt.ne (Subgroup.map_injective Q.subtype_injective h)
    have hlt' := lt_of_le_of_ne hle hne'
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPQ,
        ← Subgroup.subgroupOf_normalizer_eq hPQ, Subgroup.subgroupOf_map_subtype] at hlt'
    exact hlt'
  have hPN : P ≤ N := hN_lt.le
  have hNnormP : N ≤ Subgroup.normalizer (P : Set G) := inf_le_left
  have hPcard_dvd : Nat.card P ∣ Nat.card N := Subgroup.card_dvd_of_le hPN
  have hPlt : Nat.card P < Nat.card N := Subgroup.card_lt_of_lt hN_lt
  have hNge : 128 ≤ Nat.card N := by
    rw [hPcard] at hPcard_dvd hPlt
    obtain ⟨k, hk⟩ := hPcard_dvd
    omega
  have hN2 : IsPGroup 2 ↥N := hQ2.to_le hN_le_Q
  have hNnormE : N ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro n hn e he
    have hn_normP : n ∈ Subgroup.normalizer (P : Set G) := hNnormP hn
    have hconjP : P.map (MulAut.conj n).toMonoidHom = P :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hn_normP
    have hB_le : E.map (MulAut.conj n).toMonoidHom ≤ P := by
      rw [← hconjP]
      exact Subgroup.map_mono hEP
    haveI : IsMulCommutative E := hEab
    have hB_ab : IsMulCommutative (E.map (MulAut.conj n).toMonoidHom) := inferInstance
    have hB_card : Nat.card (E.map (MulAut.conj n).toMonoidHom) = 16 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hEcard]
    have hB_eq : E.map (MulAut.conj n).toMonoidHom = E := hEuniq _ hB_le hB_ab hB_card
    have hmem : (MulAut.conj n).toMonoidHom e ∈ E.map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom he
    rw [hB_eq] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hNnormE' : ∀ n ∈ N, ∀ e ∈ E, n * e * n⁻¹ ∈ E :=
    (Subgroup.le_normalizer_iff.mp hNnormE)
  let X' : Type := {x : G // x ∈ E ∧ τ x}
  have hXcard : Nat.card X' = 10 := by
    change ({x : G | x ∈ E ∧ τ x} : Set G).ncard = 10
    exact hT
  have hXmod : Nat.card X' % 4 = 2 := by rw [hXcard]
  letI : MulAction ↥N X' :=
    { smul := fun n x =>
        ⟨n.1 * x.1 * n.1⁻¹, hNnormE' n.1 n.2 x.1 x.2.1, hτ n.1 x.1 x.2.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : ↥N).1 * x.1 * (1 : ↥N).1⁻¹ = x.1
        simp
      mul_smul := fun n m x => by
        apply Subtype.ext
        show (n * m).1 * x.1 * ((n * m).1)⁻¹ = n.1 * (m.1 * x.1 * m.1⁻¹) * n.1⁻¹
        rw [Subgroup.coe_mul]
        group }
  have hmoveX : ∀ x : X', ∃ n : ↥N, n • x ≠ x := by
    rintro ⟨x, hxE, hxτ⟩
    obtain ⟨p, hpP, hpx⟩ := hmove x hxE hxτ
    refine ⟨⟨p, hPN hpP⟩, ?_⟩
    intro h
    exact hpx (congrArg Subtype.val h)
  obtain ⟨x₀, hx₀orbit⟩ := exists_orbit_card_two hN2 hXmod hmoveX
  let H : Subgroup ↥N := MulAction.stabilizer ↥N x₀
  have hidx : H.index = 2 := by
    change (MulAction.stabilizer ↥N x₀).index = 2
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    exact hx₀orbit
  have hcard_mul : Nat.card H * 2 = Nat.card ↥N := by
    have h := Subgroup.card_mul_index H
    rwa [hidx] at h
  have hHge : 64 ≤ Nat.card H := by omega
  let R : Subgroup G := H.map N.subtype
  have hR2 : IsPGroup 2 R := by
    change IsPGroup 2 (H.map N.subtype)
    exact IsPGroup.map (hN2.to_subgroup H) N.subtype
  have hRcard : Nat.card R = Nat.card H := by
    change Nat.card (H.map N.subtype) = Nat.card H
    exact Subgroup.card_subtype N H
  have hRle : R ≤ centralizer ({x₀.1} : Set G) ⊓ centralizer ({a} : Set G) := by
    refine le_inf ?_ ?_
    · intro r hr
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hnfix : n • x₀ = x₀ := (MulAction.mem_stabilizer_iff).mp hn
      have hxval : n.1 * x₀.1 * n.1⁻¹ = x₀.1 := congrArg Subtype.val hnfix
      change n.1 * x₀.1 = x₀.1 * n.1
      calc n.1 * x₀.1 = (n.1 * x₀.1 * n.1⁻¹) * n.1 := by group
        _ = x₀.1 * n.1 := by rw [hxval]
    · intro r hr
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hr
      exact hQa (hN_le_Q n.2)
  have hle32 : Nat.card R ≤ 32 := h32 x₀.1 x₀.2.1 x₀.2.2 R hRle hR2
  have hge64 : 64 ≤ Nat.card R := by rw [hRcard]; exact hHge
  omega

theorem card_le_of_sylow_data {G : Type} [Group G] [Finite G] {a : G} {τ : G → Prop}
    (hτ : ∀ (g x : G), τ x → τ (g * x * g⁻¹))
    {P E : Subgroup G} (hPa : P ≤ centralizer ({a} : Set G)) (hP2 : IsPGroup 2 P)
    (hPcard : Nat.card P = 64) (hEP : E ≤ P)
    (hEab : IsMulCommutative E) (hEcard : Nat.card E = 16)
    (hEuniq : ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B = 16 → B = E)
    (hT : Set.ncard {x : G | x ∈ E ∧ τ x} = 10)
    (hmove : ∀ x ∈ E, τ x → ∃ p ∈ P, p * x * p⁻¹ ≠ x)
    (h32 : ∀ x ∈ E, τ x → ∀ R : Subgroup G,
      R ≤ centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G) → IsPGroup 2 R → Nat.card R ≤ 32) :
    ∀ R : Subgroup G, R ≤ centralizer ({a} : Set G) → IsPGroup 2 R → Nat.card R ≤ 64 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro R hRa hR2
  let Y : Subgroup G := centralizer ({a} : Set G)
  have hPY : P ≤ Y := hPa
  have hP'2 : IsPGroup 2 (P.subgroupOf Y) :=
    hP2.comap_of_injective Y.subtype Y.subtype_injective
  obtain ⟨S₀, hP'S₀⟩ := IsPGroup.exists_le_sylow hP'2
  have hQ2' : IsPGroup 2 ((S₀ : Subgroup ↥Y).map Y.subtype) :=
    IsPGroup.map S₀.isPGroup' Y.subtype
  have hQa' : ((S₀ : Subgroup ↥Y).map Y.subtype) ≤ centralizer ({a} : Set G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hPQ' : P ≤ (S₀ : Subgroup ↥Y).map Y.subtype := by
    calc P = (P.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hPY).symm
      _ ≤ (S₀ : Subgroup ↥Y).map Y.subtype := Subgroup.map_mono hP'S₀
  have hQ_eq_P : (S₀ : Subgroup ↥Y).map Y.subtype = P :=
    eq_of_le_of_sylow_data hτ hP2 hPcard hEP hEab hEcard hEuniq hT hmove h32 hQa' hQ2' hPQ'
  have hS₀coe : (S₀ : Subgroup ↥Y) = P.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [hQ_eq_P, Subgroup.map_subgroupOf_eq_of_le hPY]
  have hP'card : Nat.card (P.subgroupOf Y) = 64 := by
    rw [← Subgroup.card_subtype Y (P.subgroupOf Y), Subgroup.map_subgroupOf_eq_of_le hPY, hPcard]
  have hS₀card : Nat.card S₀ = 64 := by
    rw [show Nat.card S₀ = Nat.card (S₀ : Subgroup ↥Y) from rfl, hS₀coe, hP'card]
  let R' : Subgroup ↥Y := R.subgroupOf Y
  have hR'2 : IsPGroup 2 R' := hR2.comap_of_injective Y.subtype Y.subtype_injective
  obtain ⟨S', hR'S'⟩ := IsPGroup.exists_le_sylow hR'2
  have hRcard : Nat.card R = Nat.card R' := by
    rw [← Subgroup.card_subtype Y R', Subgroup.map_subgroupOf_eq_of_le hRa]
  have hS'card : Nat.card S' = Nat.card S₀ := by
    rw [Sylow.card_eq_multiplicity S', Sylow.card_eq_multiplicity S₀]
  calc Nat.card R = Nat.card R' := hRcard
    _ ≤ Nat.card S' := Subgroup.card_le_of_le hR'S'
    _ = Nat.card S₀ := hS'card
    _ = 64 := hS₀card

end CFSG.EvenSporadicStandard.HNRecog.Harada
