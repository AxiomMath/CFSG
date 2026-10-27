module

public import CFSG.Walter.TwoRank
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GH74.KGH

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

theorem pRank_hbar_le {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    pRank 2 (HBar H) ≤ pRank 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Open.pRank 2 (⊤ : Subgroup (HBar H)) = Open.pRank 2 (⊤ : Subgroup ↥H) :=
    SectionRank.pRank_quotient_eq (G := ↥H) (pPrimeCore 2 ↥H)
      (fun hd => by
        have := odd_card_pPrimeCore H
        exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hd))
  rw [SectionRank.pRank_eq_open_pRank_top, h1, ← SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.GH74.GLS.Bg.pRank_subgroup_le (p := 2) (by norm_num) H

section Join

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem exists_elemAbelian_join {K K' : Subgroup Y} (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hinf : K ⊓ K' = ⊥) {E E' : Subgroup Y} (hE : E ≤ K) (hE' : E' ≤ K')
    (hEa : Open.IsElemAbelian 2 E) (hEa' : Open.IsElemAbelian 2 E') {a b : ℕ}
    (ha : Nat.card ↥E = 2 ^ a) (hb : Nat.card ↥E' = 2 ^ b) :
    ∃ F : Subgroup Y, F ≤ K ⊔ K' ∧ Open.IsElemAbelian 2 F ∧ Nat.card ↥F = 2 ^ (a + b) := by
  have := hEa.1
  have := hEa'.1
  have hc : ∀ (x : ↥E) (y : ↥E'), Commute (E.subtype x) (E'.subtype y) :=
    fun x y => hcomm x (hE x.2) y (hE' y.2)
  let f : ↥E × ↥E' →* Y := E.subtype.noncommCoprod E'.subtype hc
  have hf : ∀ (x : ↥E) (y : ↥E'), f (x, y) = (x : Y) * y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    rw [hf] at h
    have hx : (x : Y) ∈ K ⊓ K' := by
      refine ⟨hE x.2, ?_⟩
      have : (x : Y) = (y : Y)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact K'.inv_mem (hE' y.2)
    rw [hinf, Subgroup.mem_bot] at hx
    have hy : (y : Y) = 1 := by rw [hx, one_mul] at h; exact h
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  refine ⟨f.range, ?_, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hf]
    exact (K ⊔ K').mul_mem (Subgroup.mem_sup_left (hE x.2)) (Subgroup.mem_sup_right (hE' y.2))
  · rintro ⟨_, ⟨⟨x₁, y₁⟩, rfl⟩⟩ ⟨_, ⟨⟨x₂, y₂⟩, rfl⟩⟩
    apply Subtype.ext
    change f (x₁, y₁) * f (x₂, y₂) = f (x₂, y₂) * f (x₁, y₁)
    rw [← map_mul, ← map_mul]
    have h1 : x₁ * x₂ = x₂ * x₁ := mul_comm' x₁ x₂
    have h2 : y₁ * y₂ = y₂ * y₁ := mul_comm' y₁ y₂
    simp only [Prod.mk_mul_mk, h1, h2]
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [← map_pow]
    have hx2 : x ^ 2 = 1 := Subtype.ext (hEa.2 x x.2)
    have hy2 : y ^ 2 = 1 := Subtype.ext (hEa'.2 y y.2)
    have h2 : ((x, y) : ↥E × ↥E') ^ 2 = 1 := Prod.ext (by simpa using hx2) (by simpa using hy2)
    rw [h2, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, ha, hb, pow_add]

theorem rank_add_le {K K' : Subgroup Y} (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hinf : K ⊓ K' = ⊥) {E E' : Subgroup Y} (hE : E ≤ K) (hE' : E' ≤ K')
    (hEa : Open.IsElemAbelian 2 E) (hEa' : Open.IsElemAbelian 2 E') {a b : ℕ}
    (ha : Nat.card ↥E = 2 ^ a) (hb : Nat.card ↥E' = 2 ^ b) :
    a + b ≤ Open.pRank 2 (⊤ : Subgroup Y) := by
  obtain ⟨F, -, hF, hcard⟩ := exists_elemAbelian_join hcomm hinf hE hE' hEa hEa' ha hb
  exact SectionRank.le_pRank (by norm_num) le_top hF hcard

end Join

section Simple

theorem exists_elemAbelian_of_simple {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hs : IsSimpleGroup ↥K) (hnab : ∃ a b : ↥K, a * b ≠ b * a) :
    2 ≤ Open.pRank 2 (⊤ : Subgroup ↥K) ∧
      ∃ E : Subgroup Y, E ≤ K ∧ Open.IsElemAbelian 2 E ∧ Nat.card ↥E = 2 ^ Open.pRank 2 (⊤ : Subgroup ↥K) := by
  have hev : Even (Nat.card ↥K) := CFSG.GH74.even_card_of_nonabelian_simple hnab
  have h2 : 2 ≤ Open.pRank 2 (⊤ : Subgroup ↥K) := CFSG.Walter.two_le_twoRank ↥K hnab hev
  obtain ⟨E₀, -, hE₀, hcard⟩ := SectionRank.exists_pRank (G := ↥K) (p := 2) (by norm_num) ⊤
  refine ⟨h2, E₀.map K.subtype, Subgroup.map_subtype_le _, SectionRank.isElemAbelian_map hE₀ _, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, hcard]

end Simple


end CFSG.GH74.GLS.Stage2.Local.P34
