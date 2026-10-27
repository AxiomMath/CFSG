module

public import CFSG.GH74.GLS.LU.Local.CStruct
public import CFSG.GH74.GLS.LU.Local.A3
public import CFSG.GH74.GLS.LU.Local.SL2Pure

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
open scoped Pointwise MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local

variable {G : Type} [Group G] [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

omit [Finite G] in
theorem involution_mem_zpowers₁ (hc : LUComps G q z K₁ K₂) (hq : Odd q) {a : G} (ha : a ∈ K₁)
    (ha2 : a * a = 1) : a ∈ zpowers z := by
  obtain ⟨F, hF, hFin, hFq, ⟨e0⟩⟩ := hc.sl₁
  obtain ⟨e⟩ := exists_mulEquiv_SL2 hc.sl₁ F hFq
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact hq
  have hh2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    refine Ring.two_ne_zero ?_
    intro h2
    have h := (FiniteField.even_card_iff_char_two (F := F)).mp h2
    rw [← Nat.card_eq_fintype_card] at h
    have := Nat.odd_iff.mp hodd
    omega
  set a₀ : SL(2, F) := e.symm ⟨a, ha⟩ with ha₀
  have h1 : a₀ * a₀ = 1 := by
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.apply_symm_apply, ha₀]
    simpa using ha2
  have h2 : a₀ ∈ Subgroup.center SL(2, F) := sl2_involution_central hh2 h1
  have h3 : (⟨a, ha⟩ : ↥K₁) ∈ center ↥K₁ := by
    have := (mem_center_equiv_iff e (a := a₀)).mpr h2
    simpa [ha₀] using this
  have h4 : a ∈ (center ↥K₁).map K₁.subtype := ⟨⟨a, ha⟩, h3, rfl⟩
  rw [hc.cen₁] at h4
  exact h4


omit [Finite G] in
theorem involution_mem_zpowers₂ (hc : LUComps G q z K₁ K₂) (hq : Odd q) {a : G} (ha : a ∈ K₂)
    (ha2 : a * a = 1) : a ∈ zpowers z := by
  obtain ⟨F, hF, hFin, hFq, ⟨e0⟩⟩ := hc.sl₂
  obtain ⟨e⟩ := exists_mulEquiv_SL2 hc.sl₂ F hFq
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact hq
  have hh2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    refine Ring.two_ne_zero ?_
    intro h2
    have h := (FiniteField.even_card_iff_char_two (F := F)).mp h2
    rw [← Nat.card_eq_fintype_card] at h
    have := Nat.odd_iff.mp hodd
    omega
  set a₀ : SL(2, F) := e.symm ⟨a, ha⟩ with ha₀
  have h1 : a₀ * a₀ = 1 := by
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.apply_symm_apply, ha₀]
    simpa using ha2
  have h2 : a₀ ∈ Subgroup.center SL(2, F) := sl2_involution_central hh2 h1
  have h3 : (⟨a, ha⟩ : ↥K₂) ∈ center ↥K₂ := by
    have := (mem_center_equiv_iff e (a := a₀)).mpr h2
    simpa [ha₀] using this
  have h4 : a ∈ (center ↥K₂).map K₂.subtype := ⟨⟨a, ha⟩, h3, rfl⟩
  rw [hc.cen₂] at h4
  exact h4

theorem cs₂ (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : ∀ k ∈ K₂, s * k = k * s) : s ∈ K₁ := by
  have ht2 : t * t = 1 := hs.t_sq
  have htS : t ∈ (S : Subgroup G) := hs.t_mem
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set s' : G := t * s * t⁻¹ with hs'
  have hs'S : s' ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem htS hsS)
    ((S : Subgroup G).inv_mem htS)
  have e1 : ∀ k : G, t * (t * k * t⁻¹) * t⁻¹ = k := by
    intro k
    calc t * (t * k * t⁻¹) * t⁻¹ = (t * t) * k * (t * t)⁻¹ := by group
      _ = k := by rw [ht2]; group
  have hs'K : ∀ k ∈ K₁, s' * k = k * s' := by
    intro k hk
    have hk2 : t * k * t⁻¹ ∈ K₂ := LUComps.mem_of_map hs.t_swap hk
    have h1 := hsK _ hk2
    calc s' * k = t * s * t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) := by rw [e1 k]
      _ = t * (s * (t * k * t⁻¹)) * t⁻¹ := by group
      _ = t * ((t * k * t⁻¹) * s) * t⁻¹ := by rw [h1]
      _ = (t * (t * k * t⁻¹) * t⁻¹) * (t * s * t⁻¹) := by group
      _ = k * s' := by rw [e1 k]
  have h2 := cs₁ hc hs hs'S hs'K
  have h3 := LUComps.mem_of_map hs.t_swap₂ h2
  have e2 : t * s' * t⁻¹ = s := by
    rw [hs']
    calc t * (t * s * t⁻¹) * t⁻¹ = (t * t) * s * (t * t)⁻¹ := by group
      _ = s := by rw [ht2]; group
  rwa [e2] at h3

theorem exists_conj_into_S (hs : LUSyl G z S K₁ K₂ t u) {w : G}
    (hwC : w ∈ Cz z) (hw2 : ∃ n : ℕ, orderOf w = 2 ^ n) :
    ∃ c ∈ Cz z, c⁻¹ * w * c ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_conj_mem_sylow_of_le S hs.S_le_Cz hwC hw2

omit [Finite G] in
theorem mem_of_map_inv {H H' : Subgroup G} {c : G} (e : H.map (MulAut.conj c).toMonoidHom = H')
    {a : G} (ha : a ∈ H') : c⁻¹ * a * c ∈ H := by
  rw [← e] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  have : c⁻¹ * (MulAut.conj c).toMonoidHom x * c = x := by
    show c⁻¹ * (c * x * c⁻¹) * c = x
    group
  rw [this]; exact hx

theorem comp_conj_mem (hc : LUComps G q z K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) {c : G}
    (hcC : c ∈ Cz z) : K.map (MulAut.conj c).toMonoidHom = K₁ ∨ K.map (MulAut.conj c).toMonoidHom = K₂ := by
  rcases hc.perm hcC with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hK with rfl | rfl
    · exact Or.inl e1
    · exact Or.inr e2
  · rcases hK with rfl | rfl
    · exact Or.inr e1
    · exact Or.inl e2

theorem inv_cent_mem_zpowers (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u)
    (hq : Odd q) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) {w : G} (hwC : w ∈ Cz z)
    (hw2 : w * w = 1) (hwK : ∀ k ∈ K, w * k = k * w) : w ∈ zpowers z := by
  have hord : ∃ n : ℕ, orderOf w = 2 ^ n := by
    have : w ^ 2 = 1 := by rw [pow_two]; exact hw2
    have h1 : orderOf w ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one this
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨m, hm⟩
  obtain ⟨c, hcC, hcs⟩ := exists_conj_into_S hs hwC hord
  have hs2 : (c⁻¹ * w * c) * (c⁻¹ * w * c) = 1 := by
    calc (c⁻¹ * w * c) * (c⁻¹ * w * c) = c⁻¹ * (w * w) * c := by group
      _ = 1 := by rw [hw2]; group
  have hcz := Cz_conj_z hcC
  have hfin : ∀ s' : G, s' ∈ zpowers z → c * s' * c⁻¹ ∈ zpowers z := by
    intro s' hs'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hs'
    refine mem_zpowers_iff.mpr ⟨i, ?_⟩
    calc z ^ i = (c * z * c⁻¹) ^ i := by rw [hcz]
      _ = c * z ^ i * c⁻¹ := conj_zpow
  have hw : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
  have hcinv : c⁻¹ ∈ Cz z := (Cz z).inv_mem hcC
  have hK' := comp_conj_mem hc hK hcinv
  have hsK : ∀ k ∈ K.map (MulAut.conj c⁻¹).toMonoidHom, (c⁻¹ * w * c) * k = k * (c⁻¹ * w * c) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := hk
    have := hwK x hx
    show c⁻¹ * w * c * (c⁻¹ * x * c⁻¹⁻¹) = (c⁻¹ * x * c⁻¹⁻¹) * (c⁻¹ * w * c)
    calc c⁻¹ * w * c * (c⁻¹ * x * c⁻¹⁻¹) = c⁻¹ * (w * x) * c := by group
      _ = c⁻¹ * (x * w) * c := by rw [this]
      _ = c⁻¹ * x * c⁻¹⁻¹ * (c⁻¹ * w * c) := by group
  rcases hK' with e | e
  · rw [e] at hsK
    have h1 := cs₁ hc hs hcs hsK
    have h2 := involution_mem_zpowers₂ hc hq h1 hs2
    rw [hw]; exact hfin _ h2
  · rw [e] at hsK
    have h1 := cs₂ hc hs hcs hsK
    have h2 := involution_mem_zpowers₁ hc hq h1 hs2
    rw [hw]; exact hfin _ h2

omit [Finite G] in
theorem cenAb₂ (hs : LUSyl G z S K₁ K₂ t u) : LUCenAb (S : Subgroup G) K₂ := by
  have h := hs.cen_ab.map_conj t
  have hS : (S : Subgroup G).map (MulAut.conj t).toMonoidHom = (S : Subgroup G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs.t_mem)
  rw [hS, hs.t_swap] at h
  exact h

theorem cenAb_C (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {w : G} (hwC : w ∈ Cz z)
    (hw2 : ∃ n : ℕ, orderOf w = 2 ^ n) (hwn : w ∈ normalizer (K : Set G))
    (hnc : ∃ k ∈ K, w * k ≠ k * w) :
    ∀ a ∈ K, ∀ b ∈ K, a * w = w * a → b * w = w * b → a * b = b * a := by
  obtain ⟨c, hcC, hcs⟩ := exists_conj_into_S hs hwC hw2
  have hwSc : w ∈ (S : Subgroup G).map (MulAut.conj c).toMonoidHom := by
    refine ⟨c⁻¹ * w * c, hcs, ?_⟩
    show c * (c⁻¹ * w * c) * c⁻¹ = w
    group
  have hcinv : c⁻¹ ∈ Cz z := (Cz z).inv_mem hcC
  have hK' := comp_conj_mem hc hK hcinv
  have hKK : (K.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = K := by
    rw [Subgroup.map_map]
    have : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      show c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹ = x
      group
    rw [this, Subgroup.map_id]
  have hL : LUCenAb ((S : Subgroup G).map (MulAut.conj c).toMonoidHom) K := by
    rcases hK' with e | e
    · have h := hs.cen_ab.map_conj c
      rw [← e, hKK] at h
      exact h
    · have h := (cenAb₂ hs).map_conj c
      rw [← e, hKK] at h
      exact h
  exact hL w hwSc hwn hnc

omit [Finite G] in
theorem commutator_mul_of_commute {x x' y y' : G} (h1 : x * y' = y' * x) (h2 : x' * y = y * x')
    (h3 : x * y = y * x) (h4 : x' * y' = y' * x') :
    (x * y) * (x' * y') * (x * y)⁻¹ * (x' * y')⁻¹ = (x * x' * x⁻¹ * x'⁻¹) * (y * y' * y⁻¹ * y'⁻¹) := by
  have hxy : Commute x y := h3
  have hxy' : Commute x y' := h1
  have hx'y : Commute x' y := h2
  have hx'y' : Commute x' y' := h4
  have c1 : (y * y' * y⁻¹) * x⁻¹ = x⁻¹ * (y * y' * y⁻¹) :=
    (((hxy.symm.mul_left hxy'.symm).mul_left hxy.symm.inv_left).inv_right).eq
  have c2 : (y * y' * y⁻¹ * y'⁻¹) * x'⁻¹ = x'⁻¹ * (y * y' * y⁻¹ * y'⁻¹) :=
    ((((hx'y.symm.mul_left hx'y'.symm).mul_left hx'y.symm.inv_left).mul_left
      hx'y'.symm.inv_left).inv_right).eq
  calc (x * y) * (x' * y') * (x * y)⁻¹ * (x' * y')⁻¹
      = x * (y * x') * y' * y⁻¹ * x⁻¹ * y'⁻¹ * x'⁻¹ := by group
    _ = x * (x' * y) * y' * y⁻¹ * x⁻¹ * y'⁻¹ * x'⁻¹ := by rw [hx'y.symm.eq]
    _ = x * x' * ((y * y' * y⁻¹) * x⁻¹) * y'⁻¹ * x'⁻¹ := by group
    _ = x * x' * (x⁻¹ * (y * y' * y⁻¹)) * y'⁻¹ * x'⁻¹ := by rw [c1]
    _ = x * x' * x⁻¹ * ((y * y' * y⁻¹ * y'⁻¹) * x'⁻¹) := by group
    _ = x * x' * x⁻¹ * (x'⁻¹ * (y * y' * y⁻¹ * y'⁻¹)) := by rw [c2]
    _ = (x * x' * x⁻¹ * x'⁻¹) * (y * y' * y⁻¹ * y'⁻¹) := by group

omit [Finite G] in
theorem commutator_mul_central_both {x x' ζ ζ' : G} (hx : ζ * x = x * ζ) (hx' : ζ * x' = x' * ζ)
    (hy : ζ' * x = x * ζ') (hy' : ζ' * x' = x' * ζ') (hζ : ζ * ζ' = ζ' * ζ) :
    (x * ζ) * (x' * ζ') * (x * ζ)⁻¹ * (x' * ζ')⁻¹ = x * x' * x⁻¹ * x'⁻¹ := by
  have a1 : Commute ζ x := hx
  have a2 : Commute ζ x' := hx'
  have a3 : Commute ζ' x := hy
  have a4 : Commute ζ' x' := hy'
  have a5 : Commute ζ ζ' := hζ
  have e5 : ζ * ζ' * ζ⁻¹ = ζ' := by rw [a5.eq]; group
  calc (x * ζ) * (x' * ζ') * (x * ζ)⁻¹ * (x' * ζ')⁻¹
      = x * (ζ * x') * ζ' * ζ⁻¹ * x⁻¹ * ζ'⁻¹ * x'⁻¹ := by group
    _ = x * (x' * ζ) * ζ' * ζ⁻¹ * x⁻¹ * ζ'⁻¹ * x'⁻¹ := by rw [hx']
    _ = x * x' * (ζ * ζ' * ζ⁻¹) * x⁻¹ * ζ'⁻¹ * x'⁻¹ := by group
    _ = x * x' * ζ' * x⁻¹ * ζ'⁻¹ * x'⁻¹ := by rw [e5]
    _ = x * x' * (ζ' * x⁻¹) * ζ'⁻¹ * x'⁻¹ := by group
    _ = x * x' * (x⁻¹ * ζ') * ζ'⁻¹ * x'⁻¹ := by rw [a3.inv_right.eq]
    _ = x * x' * x⁻¹ * x'⁻¹ := by group

theorem perfect_commuting_eq_bot (hc : LUComps G q z K₁ K₂) {w : G}
    (hw₁ : ∀ k ∈ K₁, w * k * w⁻¹ ∈ K₁) (hw₂ : ∀ k ∈ K₂, w * k * w⁻¹ ∈ K₂)
    (hab₁ : ∀ a ∈ K₁, ∀ b ∈ K₁, a * w = w * a → b * w = w * b → a * b = b * a)
    (hab₂ : ∀ a ∈ K₂, ∀ b ∈ K₂, a * w = w * a → b * w = w * b → a * b = b * a)
    {Λ : Subgroup G} (hΛK : Λ ≤ K₁ ⊔ K₂) (hΛw : ∀ l ∈ Λ, l * w = w * l) (hΛ : ⁅Λ, Λ⁆ = Λ) :
    Λ = ⊥ := by
  classical
  set A₁ : Subgroup G := K₁ ⊓ centralizer ({w} : Set G) with hA₁
  set A₂ : Subgroup G := K₂ ⊓ centralizer ({w} : Set G) with hA₂
  have hA₁ab : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb =>
    hab₁ a ha.1 b hb.1 (mem_centralizer_singleton_iff.mp ha.2) (mem_centralizer_singleton_iff.mp hb.2)
  have hA₂ab : ∀ a ∈ A₂, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    hab₂ a ha.1 b hb.1 (mem_centralizer_singleton_iff.mp ha.2) (mem_centralizer_singleton_iff.mp hb.2)
  have hcross : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb => hc.comm a ha.1 b hb.1
  have hAab : ∀ x ∈ A₁ ⊔ A₂, ∀ y ∈ A₁ ⊔ A₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcross hx
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute hcross hy
    have e1 := hA₁ab a ha a' ha'
    have e2 := hA₂ab b hb b' hb'
    have e3 := hcross a ha b' hb'
    have e4 := hcross a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← e4]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [e1, e2]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [e3]
      _ = a' * b' * (a * b) := by group
  have hcomm_in : ∀ l ∈ Λ, ∀ l' ∈ Λ, ⁅l, l'⁆ ∈ A₁ ⊔ A₂ := by
    intro l hl l' hl'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc.comm (hΛK hl)
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_commute hc.comm (hΛK hl')
    have hw := hΛw _ hl
    have hw' := hΛw _ hl'
    have key : ∀ (a b : G), a ∈ K₁ → b ∈ K₂ → (a * b) * w = w * (a * b) →
        ∃ ζ : G, ζ ∈ K₁ ∧ ζ ∈ K₂ ∧ w * a * w⁻¹ = a * ζ ∧ w * b * w⁻¹ = b * ζ⁻¹ := by
      intro a b ha hb hab
      set ζ : G := a⁻¹ * (w * a * w⁻¹) with hζ
      have hζ1 : ζ ∈ K₁ := K₁.mul_mem (K₁.inv_mem ha) (hw₁ a ha)
      have hwab : (w * a * w⁻¹) * (w * b * w⁻¹) = a * b := by
        calc (w * a * w⁻¹) * (w * b * w⁻¹) = w * (a * b) * w⁻¹ := by group
          _ = ((a * b) * w) * w⁻¹ := by rw [hab]
          _ = a * b := by group
      have hwb : w * b * w⁻¹ = ζ⁻¹ * b := by
        have : w * b * w⁻¹ = (w * a * w⁻¹)⁻¹ * (a * b) := by
          rw [← hwab]; group
        rw [this, hζ]; group
      have hζ2 : ζ ∈ K₂ := by
        have h1 : ζ⁻¹ = (w * b * w⁻¹) * b⁻¹ := by rw [hwb]; group
        have h2 : ζ⁻¹ ∈ K₂ := by rw [h1]; exact K₂.mul_mem (hw₂ b hb) (K₂.inv_mem hb)
        simpa using K₂.inv_mem h2
      refine ⟨ζ, hζ1, hζ2, by rw [hζ]; group, ?_⟩
      rw [hwb]
      exact hc.comm ζ⁻¹ (K₁.inv_mem hζ1) b hb
    obtain ⟨ζ, hζ1, hζ2, hwa, hwb⟩ := key a b ha hb hw
    obtain ⟨ζ', hζ1', hζ2', hwa', hwb'⟩ := key a' b' ha' hb' hw'
    have hcm : ∀ x ∈ K₁, ∀ y ∈ K₂, y * x = x * y := fun x hx y hy => (hc.comm x hx y hy).symm
    have hsplit : ⁅a * b, a' * b'⁆ = (a * a' * a⁻¹ * a'⁻¹) * (b * b' * b⁻¹ * b'⁻¹) := by
      rw [commutatorElement_def]
      exact commutator_mul_of_commute (hc.comm a ha b' hb') (hc.comm a' ha' b hb)
        (hc.comm a ha b hb) (hc.comm a' ha' b' hb')
    have hc₁K : a * a' * a⁻¹ * a'⁻¹ ∈ K₁ :=
      K₁.mul_mem (K₁.mul_mem (K₁.mul_mem ha ha') (K₁.inv_mem ha)) (K₁.inv_mem ha')
    have hc₂K : b * b' * b⁻¹ * b'⁻¹ ∈ K₂ :=
      K₂.mul_mem (K₂.mul_mem (K₂.mul_mem hb hb') (K₂.inv_mem hb)) (K₂.inv_mem hb')
    have hc₁w : w * (a * a' * a⁻¹ * a'⁻¹) * w⁻¹ = a * a' * a⁻¹ * a'⁻¹ := by
      have e : w * (a * a' * a⁻¹ * a'⁻¹) * w⁻¹ =
          (w * a * w⁻¹) * (w * a' * w⁻¹) * (w * a * w⁻¹)⁻¹ * (w * a' * w⁻¹)⁻¹ := by group
      rw [e, hwa, hwa']
      exact commutator_mul_central_both (hcm a ha ζ hζ2) (hcm a' ha' ζ hζ2) (hcm a ha ζ' hζ2')
        (hcm a' ha' ζ' hζ2') (hc.comm ζ hζ1 ζ' hζ2')
    have hc₂w : w * (b * b' * b⁻¹ * b'⁻¹) * w⁻¹ = b * b' * b⁻¹ * b'⁻¹ := by
      have e : w * (b * b' * b⁻¹ * b'⁻¹) * w⁻¹ =
          (w * b * w⁻¹) * (w * b' * w⁻¹) * (w * b * w⁻¹)⁻¹ * (w * b' * w⁻¹)⁻¹ := by group
      rw [e, hwb, hwb']
      exact commutator_mul_central_both (hc.comm ζ⁻¹ (K₁.inv_mem hζ1) b hb)
        (hc.comm ζ⁻¹ (K₁.inv_mem hζ1) b' hb') (hc.comm ζ'⁻¹ (K₁.inv_mem hζ1') b hb)
        (hc.comm ζ'⁻¹ (K₁.inv_mem hζ1') b' hb')
        (hc.comm ζ⁻¹ (K₁.inv_mem hζ1) ζ'⁻¹ (K₂.inv_mem hζ2'))
    have hc₁A : a * a' * a⁻¹ * a'⁻¹ ∈ A₁ := by
      refine ⟨hc₁K, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (a * a' * a⁻¹ * a'⁻¹) * w = (w * (a * a' * a⁻¹ * a'⁻¹) * w⁻¹) * w := by rw [hc₁w]
        _ = w * (a * a' * a⁻¹ * a'⁻¹) := by group
    have hc₂A : b * b' * b⁻¹ * b'⁻¹ ∈ A₂ := by
      refine ⟨hc₂K, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (b * b' * b⁻¹ * b'⁻¹) * w = (w * (b * b' * b⁻¹ * b'⁻¹) * w⁻¹) * w := by rw [hc₂w]
        _ = w * (b * b' * b⁻¹ * b'⁻¹) := by group
    rw [hsplit]
    exact (A₁ ⊔ A₂).mul_mem (Subgroup.mem_sup_left hc₁A) (Subgroup.mem_sup_right hc₂A)
  have hΛle : Λ ≤ A₁ ⊔ A₂ := by
    calc Λ = ⁅Λ, Λ⁆ := hΛ.symm
      _ ≤ A₁ ⊔ A₂ := Subgroup.commutator_le.mpr hcomm_in
  have hΛcomm : ⁅Λ, Λ⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := hAab x (hΛle hx) y (hΛle hy)
    calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [this]
      _ = 1 := by group
  calc Λ = ⁅Λ, Λ⁆ := hΛ.symm
    _ = ⊥ := hΛcomm

end CFSG.GH74.GLS.LU.Local
