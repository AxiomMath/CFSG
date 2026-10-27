module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTE16
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

section Rank

variable {R : Type} [Group R] [Finite R]

omit [Finite R] in
theorem card_le_two_of_isCyclic [IsCyclic R] (E : Subgroup R) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
  have hE : Nat.card E = orderOf g := by
    rw [← Nat.card_zpowers]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv fun x => hg x)).symm
  rw [hE]
  apply orderOf_le_of_pow_eq_one (by norm_num)
  rw [sq]
  exact Subtype.ext (hsq g g.2)

theorem card_le_four_of_index_le_two {C : Subgroup R} [IsCyclic C] (hi : C.index ≤ 2)
    (E : Subgroup R) (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have h1 : Nat.card ↥(C ⊓ E) ≤ 2 := by
    have h := card_le_two_of_isCyclic ((C ⊓ E).subgroupOf C)
      (fun x hx => Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.mp hx).2))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  have hC0 : C.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have h2 : (C ⊓ E).relIndex E ≤ 2 := by
    rw [Subgroup.inf_relIndex_right]
    calc C.relIndex E ≤ C.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top hC0
      _ = C.index := Subgroup.relIndex_top_right C
      _ ≤ 2 := hi
  have h3 := Subgroup.card_mul_index ((C ⊓ E).subgroupOf E)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : C ⊓ E ≤ E)).toEquiv] at h3
  calc Nat.card E = Nat.card ↥(C ⊓ E) * (C ⊓ E).relIndex E := h3.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2

theorem index_zpowers_eq_two {g : R} (h : Nat.card R = 2 * orderOf g) :
    (zpowers g).index = 2 := by
  have h1 := Subgroup.card_mul_index (zpowers g)
  rw [Nat.card_zpowers, h] at h1
  have h0 : 0 < orderOf g := orderOf_pos g
  have : orderOf g * (zpowers g).index = orderOf g * 2 := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left h0 this

theorem card_le_four_of_narrow (hR : IsCyclic R ∨ IsQuat R ∨ IsDihedral R) (E : Subgroup R)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  rcases hR with hR | ⟨n, hn, ⟨e⟩⟩ | ⟨m, k, -, hk, ⟨e⟩⟩
  · have := card_le_two_of_isCyclic E hsq
    omega
  · have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    set g : R := e.symm (QuaternionGroup.a 1) with hg
    have hord : orderOf g = 2 * 2 ^ (n - 2) := by
      rw [hg, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
    have hcard : Nat.card R = 2 * orderOf g := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, hord]
      ring
    exact card_le_four_of_index_le_two (C := zpowers g) (index_zpowers_eq_two hcard).le E hsq
  · have : NeZero k := ⟨by omega⟩
    set g : R := e.symm (DihedralGroup.r 1) with hg
    have hord : orderOf g = k := by
      rw [hg, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hcard : Nat.card R = 2 * orderOf g := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hord]
    exact card_le_four_of_index_le_two (C := zpowers g) (index_zpowers_eq_two hcard).le E hsq

end Rank

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem eq_bot_of_elem_le_centralizer (hL31 : Lemma31Narrow)
    (h : Cfg55E G z k S T Tstar p H P g X Y) (hd : Data5A2 z k S T Tstar p H P t q I Q₁)
    {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hQJ : barIn H Q₁ ≤ centralizer (J : Set (HBar H))) {A : Subgroup (HBar H)}
    (hAJ : A ≤ centralizer (J : Set (HBar H)))
    (hAQ : A ≤ centralizer (barIn H Q₁ : Set (HBar H))) (hsq : ∀ x ∈ A, x * x = 1)
    (hinf : A ⊓ barIn H Q₁ = ⊥) : A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := barIn H Q₁ with hQ
  have hQH : Q₁ ≤ H := hd.Q₁_le.trans hd.i.good.le_H
  have hQ4 : Nat.card Q = 4 := by
    have := hd.Q₁_four.1
    rw [hQ, L52Two.card_barIn (IsElementaryAbelian.isPGroup 2 ↥Q₁) hQH, hd.Q₁_four.2]
  have hQsq : ∀ x ∈ Q, x * x = 1 := by
    have := hd.Q₁_four.1
    rintro _ ⟨y, hy, rfl⟩
    have hy2 : (y : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (y : G) hy
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hy2, Subgroup.coe_one])
    rw [this, map_one]
  have hcomm : ∀ a ∈ A, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hAQ ha)) b hb).symm
  set W := A ⊔ Q with hW
  have hWsq : ∀ x ∈ W, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup' hcomm hx
    calc a * b * (a * b) = a * a * (b * b) := by
          rw [show a * b * (a * b) = a * (b * a) * b by group, ← hcomm a ha b hb]
          group
      _ = 1 := by rw [hsq a ha, hQsq b hb, one_mul]
  have hW2 : IsPGroup 2 ↥W := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq, Subgroup.coe_one]; exact hWsq _ x.2)⟩
  have hWJ : W ≤ centralizer (J : Set (HBar H)) := sup_le hAJ hQJ
  have hW1 : W ≠ ⊥ := by
    intro hbot
    have hle : Q ≤ ⊥ := hbot ▸ le_sup_right
    rw [le_bot_iff] at hle
    rw [hle, card_bot] at hQ4
    omega
  have hodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥H)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨Jt, R, ρ, -, -, -, hconcl, hρ, hWρ⟩ := sec31_core_hom hL31 h.ctx (H_ne_top h)
    (QuotientGroup.mk' (pPrimeCore 2 ↥H)) (QuotientGroup.mk'_surjective _) hodd hJ hW2 hWJ hW1
  set E : Subgroup ↥R := W.comap ρ with hE
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => hρ (by rw [map_mul, map_one]; exact hWsq _ hx)
  have hE4 := card_le_four_of_narrow hconcl.1 E hEsq
  have hcardE : Nat.card E = Nat.card W := by
    rw [← Subgroup.card_map_of_injective hρ, Subgroup.map_comap_eq_self hWρ]
  have hcardW : Nat.card W = Nat.card A * 4 := by
    rw [hW, L52Two.card_sup_eq_mul_of_commute hcomm hinf, hQ4]
  have hA1 : Nat.card A ≤ 1 := by omega
  exact Subgroup.eq_bot_of_card_le A hA1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
