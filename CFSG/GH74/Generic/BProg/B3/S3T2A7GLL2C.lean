module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLL2A

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}

theorem comm_conj (hL : CFSG.IsComponent L) {a b : Y} (hab : a⁻¹ * b ∉ normalizer (L : Set Y))
    {x y : Y} (hx : x ∈ L) (hy : y ∈ L) :
    (a * x * a⁻¹) * (b * y * b⁻¹) = (b * y * b⁻¹) * (a * x * a⁻¹) := by
  set s := a⁻¹ * b with hsdef
  set L' : Subgroup Y := L.map (MulAut.conj s).toMonoidHom with hL'
  have hL'c : CFSG.IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv _ hL
  have hne : L ≠ L' := fun h => hab (mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcomm : ⁅L, L'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hL hL'c).resolve_left hne
  have hy' : s * y * s⁻¹ ∈ L' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have h1 : x * (s * y * s⁻¹) = (s * y * s⁻¹) * x := by
    have := Subgroup.commutator_mem_commutator hx hy'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  calc (a * x * a⁻¹) * (b * y * b⁻¹) = a * (x * (s * y * s⁻¹)) * a⁻¹ := by
        rw [hsdef]; group
    _ = a * ((s * y * s⁻¹) * x) * a⁻¹ := by rw [h1]
    _ = (b * y * b⁻¹) * (a * x * a⁻¹) := by rw [hsdef]; group

omit [Finite Y] in
theorem mem_normalizer_of_act {x c : Y} (hc : c ∈ L) (h : ∀ y ∈ L, x * y * x⁻¹ = c * y * c⁻¹) :
    x ∈ normalizer (L : Set Y) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy]
    exact mul_mem (mul_mem hc hy) (inv_mem hc)
  · intro hy
    have h1 := h _ (mul_mem (mul_mem (inv_mem hc) hy) hc)
    have h2 : y = c⁻¹ * (x * y * x⁻¹) * c := by
      have h3 : x * (c⁻¹ * (x * y * x⁻¹) * c) * x⁻¹ = x * y * x⁻¹ := by
        rw [h1]; group
      exact (mul_left_cancel (mul_right_cancel h3)).symm
    rw [h2]
    exact mul_mem (mul_mem (inv_mem hc) hy) hc

omit [Finite Y] in
theorem eq_one_or_eq_of_mem_zpowers {s x : Y} (hs : s * s = 1) (hx : x ∈ zpowers s) :
    x = 1 ∨ x = s := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hs2 : s ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hs
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hs2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hs2, one_zpow, one_mul]

theorem two_le_pRank_sup (hs : Setting125 Y L B X₀ z) {D : Subgroup Y} (hDB : D ≤ B) {s t : Y}
    (hsD : s ∈ D) (htD : t ∈ D) (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t) :
    zpowers s ⊔ zpowers t ≤ D ∧ 2 ≤ pRank 2 ↥(zpowers s ⊔ zpowers t) := by
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  have hs2 : s * s = 1 := hBsq s (hDB hsD)
  have ht2 : t * t = 1 := hBsq t (hDB htD)
  have hle : zpowers s ⊔ zpowers t ≤ D := sup_le (zpowers_le.mpr hsD) (zpowers_le.mpr htD)
  refine ⟨hle, ?_⟩
  have hel : CFSG.IsElementaryAbelian 2 ↥(zpowers s ⊔ zpowers t) :=
    Th2Sig6.isElementaryAbelian_of_le hs.B_el (hle.trans hDB)
  have hos : Nat.card ↥(zpowers s) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  have hot : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have h1 := Obs.card_mul_le_of_trivial_inter (le_sup_left : zpowers s ≤ zpowers s ⊔ zpowers t)
    le_sup_right fun x hxs hxt => by
      rcases eq_one_or_eq_of_mem_zpowers hs2 hxs with h | h
      · exact h
      · rcases eq_one_or_eq_of_mem_zpowers ht2 hxt with h' | h'
        · exact h'
        · exact absurd (h.symm.trans h') hst
  rw [hos, hot, C3.Layer1.Back.card_eq_two_pow_pRank hel] at h1
  by_contra hlt
  push Not at hlt
  have : 2 ^ pRank 2 ↥(zpowers s ⊔ zpowers t) ≤ 2 ^ 1 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem false_of_orbit_four (hs : Setting125 Y L B X₀ z) (hsig : Sig125 L X₀) {D : Subgroup Y}
    (hDB : D ≤ B) (hDz : D ⊓ zpowers z = ⊥) (hDsup : D ⊔ zpowers z = B) {s t : Y} (hsD : s ∈ D)
    (htD : t ∈ D) (hsN : s ∉ normalizer (L : Set Y)) (htN : t ∉ normalizer (L : Set Y))
    (hstN : s * t ∉ normalizer (L : Set Y)) : False := by
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  have hs2 : s * s = 1 := hBsq s (hDB hsD)
  have ht2 : t * t = 1 := hBsq t (hDB htD)
  have hst : s * t = t * s := hBc s (hDB hsD) t (hDB htD)
  have h1N : (1 : Y) ∈ normalizer (L : Set Y) := one_mem _
  have hs1 : s ≠ 1 := fun h => hsN (h ▸ h1N)
  have ht1 : t ≠ 1 := fun h => htN (h ▸ h1N)
  have hsne : s ≠ t := fun h => hstN (by rw [h, ht2]; exact h1N)
  obtain ⟨hED, hE2⟩ := two_le_pRank_sup hs hDB hsD htD hs1 ht1 hsne
  have hNW := centralizer_le_normalizer_W hs hDB hDz hDsup hED hE2
  have hC : ∀ {a b : Y}, a⁻¹ * b ∉ normalizer (L : Set Y) → ∀ x ∈ L, ∀ y ∈ L,
      Commute (a * x * a⁻¹) (b * y * b⁻¹) := fun hab x hx y hy => comm_conj hs.comp hab hx hy
  have hC1 : ∀ {b : Y}, b ∉ normalizer (L : Set Y) → ∀ x ∈ L, ∀ y ∈ L,
      Commute x (b * y * b⁻¹) := fun hb x hx y hy => by
    simpa using hC (a := 1) (by simpa using hb) x hx y hy
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hNst : s⁻¹ * t ∉ normalizer (L : Set Y) := by rwa [hsi]
  have hNsst : s⁻¹ * (s * t) ∉ normalizer (L : Set Y) := by rwa [← mul_assoc, inv_mul_cancel,
    one_mul]
  have hNtst : t⁻¹ * (s * t) ∉ normalizer (L : Set Y) := by
    rwa [hst, ← mul_assoc, inv_mul_cancel, one_mul]
  refine false_of_sig_of_inner hs hsig fun c hc => ?_
  set b₀ := s * c * s⁻¹ with hb₀
  set d₀ := t * c * t⁻¹ with hd₀
  set e₀ := (s * t) * c * (s * t)⁻¹ with he₀
  have hab := hC1 hsN c hc c hc
  have had := hC1 htN c hc c hc
  have hae := hC1 hstN c hc c hc
  have hbd := hC hNst c hc c hc
  have hbe := hC hNsst c hc c hc
  have hde := hC hNtst c hc c hc
  have hact : ∀ y ∈ L, c * b₀ * d₀ * e₀ * y * (c * b₀ * d₀ * e₀)⁻¹ = c * y * c⁻¹ := by
    intro y hy
    have h1 : Commute y (b₀ * d₀ * e₀) :=
      ((hC1 hsN y hy c hc).mul_right (hC1 htN y hy c hc)).mul_right (hC1 hstN y hy c hc)
    calc c * b₀ * d₀ * e₀ * y * (c * b₀ * d₀ * e₀)⁻¹ =
          c * ((b₀ * d₀ * e₀) * y * (b₀ * d₀ * e₀)⁻¹) * c⁻¹ := by group
      _ = c * (y * (b₀ * d₀ * e₀) * (b₀ * d₀ * e₀)⁻¹) * c⁻¹ := by rw [h1.eq]
      _ = c * y * c⁻¹ := by group
  have hxs : s * (c * b₀ * d₀ * e₀) * s⁻¹ = c * b₀ * d₀ * e₀ := by
    have h1 : s * b₀ * s⁻¹ = c := by
      rw [hb₀]
      calc s * (s * c * s⁻¹) * s⁻¹ = (s * s) * c * (s * s)⁻¹ := by group
        _ = c := by rw [hs2]; group
    have h2 : s * d₀ * s⁻¹ = e₀ := by rw [hd₀, he₀]; group
    have h3 : s * e₀ * s⁻¹ = d₀ := by
      rw [he₀, hd₀]
      calc s * ((s * t) * c * (s * t)⁻¹) * s⁻¹ = (s * s) * t * c * ((s * s) * t)⁻¹ := by group
        _ = t * c * t⁻¹ := by rw [hs2]; group
    calc s * (c * b₀ * d₀ * e₀) * s⁻¹ =
          (s * c * s⁻¹) * (s * b₀ * s⁻¹) * ((s * d₀ * s⁻¹) * (s * e₀ * s⁻¹)) := by group
      _ = b₀ * c * (e₀ * d₀) := by rw [h1, h2, h3]
      _ = c * b₀ * (d₀ * e₀) := by rw [hab.eq, hde.eq]
      _ = c * b₀ * d₀ * e₀ := by group
  have hxt : t * (c * b₀ * d₀ * e₀) * t⁻¹ = c * b₀ * d₀ * e₀ := by
    have h1 : t * b₀ * t⁻¹ = e₀ := by rw [hb₀, he₀, hst]; group
    have h2 : t * d₀ * t⁻¹ = c := by
      rw [hd₀]
      calc t * (t * c * t⁻¹) * t⁻¹ = (t * t) * c * (t * t)⁻¹ := by group
        _ = c := by rw [ht2]; group
    have h3 : t * e₀ * t⁻¹ = b₀ := by
      rw [he₀, hb₀]
      have hts : t * s * t = s := by rw [← hst, mul_assoc, ht2, mul_one]
      calc t * ((s * t) * c * (s * t)⁻¹) * t⁻¹ = (t * s * t) * c * (t * s * t)⁻¹ := by group
        _ = s * c * s⁻¹ := by rw [hts]
    have hc4 : Commute (d₀ * e₀) (c * b₀) :=
      (had.symm.mul_right hbd.symm).mul_left (hae.symm.mul_right hbe.symm)
    calc t * (c * b₀ * d₀ * e₀) * t⁻¹ =
          (t * c * t⁻¹) * (t * b₀ * t⁻¹) * ((t * d₀ * t⁻¹) * (t * e₀ * t⁻¹)) := by group
      _ = (d₀ * e₀) * (c * b₀) := by rw [h1, h2, h3]
      _ = (c * b₀) * (d₀ * e₀) := hc4.eq
      _ = c * b₀ * d₀ * e₀ := by group
  have hcomm : ∀ g : Y, g * (c * b₀ * d₀ * e₀) * g⁻¹ = c * b₀ * d₀ * e₀ →
      g ∈ centralizer ({c * b₀ * d₀ * e₀} : Set Y) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (by
      calc g * (c * b₀ * d₀ * e₀) = (g * (c * b₀ * d₀ * e₀) * g⁻¹) * g := by group
        _ = c * b₀ * d₀ * e₀ * g := by rw [hg])
  have hle : zpowers s ⊔ zpowers t ≤ centralizer ({c * b₀ * d₀ * e₀} : Set Y) :=
    sup_le (zpowers_le.mpr (hcomm s hxs)) (zpowers_le.mpr (hcomm t hxt))
  have hxE : c * b₀ * d₀ * e₀ ∈ centralizer ((zpowers s ⊔ zpowers t : Subgroup Y) : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (hle hg)
  exact ⟨c * b₀ * d₀ * e₀, hNW hxE, mem_normalizer_of_act hc hact, hact⟩

end CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR
