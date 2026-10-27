module

public import CFSG.LargeExtraspecial.AS35IHyp

public section

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup

variable {X : Type} [Group X]

theorem mem_map_conj {H : Subgroup X} {g y : X} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by simp [mul_assoc]⟩

theorem card_sup_mul_card_inf {A B : Subgroup X}
    (hB : B ≤ normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set Nr := normalizer (A : Set X)
  have hAN : A ≤ Nr := le_normalizer
  have : (A.subgroupOf Nr).Normal := normal_in_normalizer
  have hc : ∀ Y : Subgroup X, Y ≤ Nr → Nat.card (Y.subgroupOf Nr) = Nat.card Y := fun Y hY =>
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
  have h1 := relIndex_mul_card (H := A.subgroupOf Nr) (K := B.subgroupOf Nr ⊔ A.subgroupOf Nr)
  have h2 := relIndex_mul_card (H := A.subgroupOf Nr) (K := B.subgroupOf Nr)
  rw [relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf Nr ≤ _)] at h1
  rw [inf_comm] at h2
  have hsup : B.subgroupOf Nr ⊔ A.subgroupOf Nr = (A ⊔ B).subgroupOf Nr := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf Nr ⊓ A.subgroupOf Nr = (A ⊓ B).subgroupOf Nr := by
    ext
    simp [mem_subgroupOf, and_comm]
  rw [hsup] at h1
  rw [hinf] at h2
  rw [hc _ (sup_le hAN hB)] at h1
  rw [hc A hAN] at h1
  rw [hc _ hB] at h2
  rw [hc _ (inf_le_left.trans hAN)] at h2
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A.subgroupOf Nr).relIndex (B.subgroupOf Nr) * Nat.card A) *
          Nat.card ↥(A ⊓ B) := by rw [h1]
    _ = Nat.card A * ((A.subgroupOf Nr).relIndex (B.subgroupOf Nr) * Nat.card ↥(A ⊓ B)) := by
          ring
    _ = Nat.card A * Nat.card B := by rw [h2]

structure AbsTI (X : Type) [Group X] (Q M : Subgroup X) : Prop where
  sq : ∀ x ∈ Q, x * x = 1
  comm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  QM : Q ≤ M
  norm : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q
  cent : ∀ x ∈ Q, x ≠ 1 → centralizer ({x} : Set X) ≤ M
  ti : ∀ g : X, ∀ x ∈ Q, x ≠ 1 → g * x * g⁻¹ ∈ Q → g ∈ M
  gen : ∀ g : X, g ∉ M → Q ⊔ Q.map (MulAut.conj g).toMonoidHom = ⊤
  o2 : ∀ Y : Subgroup X, Y.Normal → IsPGroup 2 Y → Y = ⊥

namespace AbsTI

variable {Q M : Subgroup X} (h : AbsTI X Q M)
include h

theorem eq_one_of_conj_mem_Q {g : X} (hg : g ∉ M) {q : X} (hq : q ∈ Q)
    (hgq : g * q * g⁻¹ ∈ Q) : q = 1 := by
  by_contra hq1
  exact hg (h.ti g q hq hq1 hgq)

theorem conj_mem_of_comm {g c y : X} (hc : c ∈ Q) (hc1 : c ≠ 1)
    (hy : y * (g * c * g⁻¹) = g * c * g⁻¹ * y) : g⁻¹ * y * g ∈ M := by
  apply h.cent c hc hc1
  rw [mem_centralizer_singleton_iff]
  calc g⁻¹ * y * g * c = g⁻¹ * (y * (g * c * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * c * g⁻¹ * y) * g := by rw [hy]
    _ = c * (g⁻¹ * y * g) := by group

omit h in
theorem comm_commutator_of_sq {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hc : a * b * a⁻¹ * b⁻¹ * (a * b * a⁻¹ * b⁻¹) = 1) :
    b * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hcinv : (a * b * a⁻¹ * b⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹ := inv_eq_of_mul_eq_one_right hc
  have h1 : b * (a * b * a⁻¹ * b⁻¹) * b⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by
    calc b * (a * b * a⁻¹ * b⁻¹) * b⁻¹ = b * a * b * a⁻¹ * (b⁻¹ * b⁻¹) := by group
      _ = b * a * b * a⁻¹ := by rw [hbinv, hb, mul_one]
      _ = b * a * b⁻¹ * a⁻¹ := by rw [hbinv]
      _ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
  rw [hcinv] at h1
  calc b * (a * b * a⁻¹ * b⁻¹) = b * (a * b * a⁻¹ * b⁻¹) * b⁻¹ * b := by group
    _ = a * b * a⁻¹ * b⁻¹ * b := by rw [h1]

theorem eq_one_of_conj_mem {g : X} (hg : g ∉ M) {x : X} (hx : x ∈ Q) (hgx : g * x * g⁻¹ ∈ M) :
    x = 1 := by
  set Qg := Q.map (MulAut.conj g).toMonoidHom with hQg
  have mQg : ∀ y, y ∈ Qg ↔ g⁻¹ * y * g ∈ Q := fun y => mem_map_conj
  have sqQg : ∀ y ∈ Qg, y * y = 1 := by
    intro y hy
    have := h.sq _ ((mQg y).1 hy)
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have commQg : ∀ y ∈ Qg, ∀ y' ∈ Qg, y * y' = y' * y := by
    intro y hy y' hy'
    have := h.comm _ ((mQg y).1 hy) _ ((mQg y').1 hy')
    calc y * y' = g * ((g⁻¹ * y * g) * (g⁻¹ * y' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y' * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = y' * y := by group
  have ti : ∀ y ∈ Q, y ∈ Qg → y = 1 := by
    intro y hy hyg
    have h1 := h.eq_one_of_conj_mem_Q hg ((mQg y).1 hyg)
      (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group])
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  set L : Subgroup X := Q ⊓ M.map (MulAut.conj g).toMonoidHom with hL
  set L₁ : Subgroup X := Qg ⊓ M with hL₁
  have mL : ∀ l, l ∈ L ↔ l ∈ Q ∧ g⁻¹ * l * g ∈ M := fun l => by rw [hL, mem_inf, mem_map_conj]
  have mL₁ : ∀ l, l ∈ L₁ ↔ l ∈ Qg ∧ l ∈ M := fun l => by rw [hL₁, mem_inf]
  have normg : ∀ m, g⁻¹ * m * g ∈ M → ∀ y ∈ Qg, m * y * m⁻¹ ∈ Qg := by
    intro m hm y hy
    rw [mQg]
    have := h.norm _ hm _ ((mQg y).1 hy)
    rwa [show g⁻¹ * m * g * (g⁻¹ * y * g) * (g⁻¹ * m * g)⁻¹ = g⁻¹ * (m * y * m⁻¹) * g by
      group] at this
  have commLL : ∀ l ∈ L, ∀ l₁ ∈ L₁, l * l₁ = l₁ * l := by
    intro l hl l₁ hl₁
    obtain ⟨hlQ, hlM⟩ := (mL l).1 hl
    obtain ⟨hl₁Q, hl₁M⟩ := (mL₁ l₁).1 hl₁
    have hc1 : l * l₁ * l⁻¹ * l₁⁻¹ ∈ Q := by
      rw [show l * l₁ * l⁻¹ * l₁⁻¹ = l * (l₁ * l⁻¹ * l₁⁻¹) by group]
      exact Q.mul_mem hlQ (h.norm l₁ hl₁M _ (Q.inv_mem hlQ))
    have hc2 : l * l₁ * l⁻¹ * l₁⁻¹ ∈ Qg := Qg.mul_mem (normg l hlM l₁ hl₁Q) (Qg.inv_mem hl₁Q)
    have h1 := ti _ hc1 hc2
    calc l * l₁ = l * l₁ * l⁻¹ * l₁⁻¹ * (l₁ * l) := by group
      _ = l₁ * l := by rw [h1, one_mul]
  set W := L ⊔ L₁ with hW
  have mW : ∀ w, w ∈ W ↔ ∃ l ∈ L, ∃ l₁ ∈ L₁, w = l * l₁ := fun w => mem_sup_of_commute commLL
  have pW : IsPGroup 2 W := by
    intro w
    obtain ⟨l, hl, l₁, hl₁, hw⟩ := (mW w).1 w.2
    refine ⟨1, Subtype.ext ?_⟩
    have hl2 := h.sq l ((mL l).1 hl).1
    have hl₁2 := sqQg l₁ ((mL₁ l₁).1 hl₁).1
    have hc := commLL l hl l₁ hl₁
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, hw, pow_two]
    calc l * l₁ * (l * l₁) = l * (l₁ * l) * l₁ := by group
      _ = l * (l * l₁) * l₁ := by rw [hc]
      _ = (l * l) * (l₁ * l₁) := by group
      _ = 1 := by rw [hl2, hl₁2, one_mul]
  have normQ : ∀ x' ∈ Q, ∀ w ∈ W, x' * w * x'⁻¹ ∈ W := by
    intro x' hx' w hw
    obtain ⟨l, hl, l₁, hl₁, rfl⟩ := (mW w).1 hw
    obtain ⟨hlQ, -⟩ := (mL l).1 hl
    obtain ⟨hl₁Q, hl₁M⟩ := (mL₁ l₁).1 hl₁
    have hcQ : x' * l₁ * x'⁻¹ * l₁⁻¹ ∈ Q := by
      rw [show x' * l₁ * x'⁻¹ * l₁⁻¹ = x' * (l₁ * x'⁻¹ * l₁⁻¹) by group]
      exact Q.mul_mem hx' (h.norm l₁ hl₁M _ (Q.inv_mem hx'))
    have hcL : x' * l₁ * x'⁻¹ * l₁⁻¹ ∈ L := by
      refine (mL _).2 ⟨hcQ, ?_⟩
      by_cases hl₁1 : l₁ = 1
      · rw [hl₁1]
        simp
      · have hq1 : g⁻¹ * l₁ * g ∈ Q := (mQg l₁).1 hl₁Q
        have hq1ne : g⁻¹ * l₁ * g ≠ 1 := fun h1 => hl₁1 (by
          calc l₁ = g * (g⁻¹ * l₁ * g) * g⁻¹ := by group
            _ = 1 := by rw [h1]; group)
        apply h.conj_mem_of_comm hq1 hq1ne
        rw [show g * (g⁻¹ * l₁ * g) * g⁻¹ = l₁ by group]
        exact (comm_commutator_of_sq (h.sq x' hx') (sqQg l₁ hl₁Q) (h.sq _ hcQ)).symm
    have hxl : x' * l = l * x' := h.comm x' hx' l hlQ
    rw [mW]
    refine ⟨l * (x' * l₁ * x'⁻¹ * l₁⁻¹), L.mul_mem hl hcL, l₁, hl₁, ?_⟩
    calc x' * (l * l₁) * x'⁻¹ = (x' * l) * l₁ * x'⁻¹ := by group
      _ = (l * x') * l₁ * x'⁻¹ := by rw [hxl]
      _ = l * (x' * l₁ * x'⁻¹ * l₁⁻¹) * l₁ := by group
  have normQg : ∀ y ∈ Qg, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro y hy w hw
    obtain ⟨l, hl, l₁, hl₁, rfl⟩ := (mW w).1 hw
    obtain ⟨hlQ, hlM⟩ := (mL l).1 hl
    obtain ⟨hl₁Q, -⟩ := (mL₁ l₁).1 hl₁
    have hcQg : y * l * y⁻¹ * l⁻¹ ∈ Qg := by
      rw [show y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) by group]
      exact Qg.mul_mem hy (normg l hlM _ (Qg.inv_mem hy))
    have hcM : y * l * y⁻¹ * l⁻¹ ∈ M := by
      by_cases hl1 : l = 1
      · rw [hl1]
        simp
      · apply h.cent l hlQ hl1
        rw [mem_centralizer_singleton_iff]
        exact (comm_commutator_of_sq (sqQg y hy) (h.sq l hlQ) (sqQg _ hcQg)).symm
    have hc : y * l * y⁻¹ * l⁻¹ ∈ L₁ := (mL₁ _).2 ⟨hcQg, hcM⟩
    have hyl₁ : y * l₁ = l₁ * y := commQg y hy l₁ hl₁Q
    have hcl : l * (y * l * y⁻¹ * l⁻¹) = y * l * y⁻¹ * l⁻¹ * l := commLL l hl _ hc
    rw [mW]
    refine ⟨l, hl, (y * l * y⁻¹ * l⁻¹) * l₁, L₁.mul_mem hc hl₁, ?_⟩
    calc y * (l * l₁) * y⁻¹ = (y * l * y⁻¹ * l⁻¹) * l * (y * l₁ * y⁻¹) := by group
      _ = (y * l * y⁻¹ * l⁻¹) * l * l₁ := by rw [hyl₁]; group
      _ = l * ((y * l * y⁻¹ * l⁻¹) * l₁) := by rw [← hcl]; group
  have hNQ : Q ≤ normalizer (W : Set X) := by
    intro x' hx'
    rw [mem_normalizer_iff]
    intro w
    refine ⟨normQ x' hx' w, fun hw => ?_⟩
    have := normQ x'⁻¹ (Q.inv_mem hx') _ hw
    simpa [mul_assoc] using this
  have hNQg : Qg ≤ normalizer (W : Set X) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro w
    refine ⟨normQg y hy w, fun hw => ?_⟩
    have := normQg y⁻¹ (Qg.inv_mem hy) _ hw
    simpa [mul_assoc] using this
  have hWn : W.Normal := by
    have htop : normalizer (W : Set X) = ⊤ := by
      rw [eq_top_iff, ← h.gen g hg]
      exact sup_le hNQ hNQg
    exact normalizer_eq_top_iff.1 htop
  have hW1 := h.o2 W hWn pW
  have hmem : g * x * g⁻¹ ∈ W :=
    mem_sup_right ((mL₁ _).2 ⟨(mQg _).2 (by simpa [mul_assoc] using hx), hgx⟩)
  rw [hW1, mem_bot] at hmem
  calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = 1 := by rw [hmem]; group

theorem mem_of_comm_conj {x k q : X} (hx : x ∈ Q) (hx1 : x ≠ 1) (hq : q ∈ Q) (hq1 : q ≠ 1)
    (hc : x * (k * q * k⁻¹) = k * q * k⁻¹ * x) : k * q * k⁻¹ ∈ Q := by
  have hyM : k * q * k⁻¹ ∈ M := h.cent x hx hx1 (mem_centralizer_singleton_iff.2 hc.symm)
  by_cases hk : k ∈ M
  · exact h.norm k hk q hq
  · exact absurd (h.eq_one_of_conj_mem hk hq hyM) hq1

end AbsTI

end CFSG.LargeExtraspecial.Asc22
