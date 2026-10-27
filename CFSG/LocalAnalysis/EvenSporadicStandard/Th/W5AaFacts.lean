module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalIn2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG

public section

namespace CFSG.EvenSporadicStandard.ThStd

variable {G : Type} [Group G] {L S A B Aa : Subgroup G} {z b : G}

@[expose] def psi (r x : G) : G := r * x * r⁻¹ * x⁻¹

theorem psi_mul_left (r r' x : G) : psi (r * r') x = r * psi r' x * r⁻¹ * psi r x := by
  simp only [psi]
  group

theorem psi_conj (n r x : G) : psi (n * r * n⁻¹) (n * x * n⁻¹) = n * psi r x * n⁻¹ := by
  simp only [psi]
  group

theorem psi_eq_one_of_mem {A : Subgroup G} {r a : G} (hr : ∀ a ∈ A, r * a = a * r) (ha : a ∈ A) :
    psi r a = 1 := by
  simp only [psi]
  rw [hr a ha]
  group

theorem ThLocalIn2.A_le (W2 : ThLocalIn2 B A Aa b) : A ≤ Aa := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (W2.A_eq_sq y).1 hy
  exact Aa.pow_mem hx 2

theorem ThLocalIn2.sq_mem_A (W2 : ThLocalIn2 B A Aa b) {x : G} (hx : x ∈ Aa) : x ^ 2 ∈ A :=
  (W2.A_eq_sq _).2 ⟨x, hx, rfl⟩

theorem ThLocalIn2.mem_A_of_sq_eq_one (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {y : G} (hy : y ∈ Aa) (hy2 : y ^ 2 = 1) : y ∈ A := by
  have : Finite Aa := Nat.finite_of_card_ne_zero (by rw [W2.Aa_card]; positivity)
  let sq : Aa →* Aa := MonoidHom.mk' (fun x => x ^ 2) (fun x y => by
    apply Subtype.ext
    have hc : Commute (x : G) (y : G) := W2.Aa_comm _ x.2 _ y.2
    simpa using hc.mul_pow 2)
  have hAcard : Nat.card (A.subgroupOf Aa) = 16 := by
    rw [← W.A_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe W2.A_le).toEquiv
  have hrange : sq.range = A.subgroupOf Aa := by
    ext x
    simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, rfl⟩
      exact W2.sq_mem_A w.2
    · intro hxA
      obtain ⟨w, hw, hwx⟩ := (W2.A_eq_sq _).1 hxA
      exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩
  have hker : A.subgroupOf Aa ≤ sq.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact W.A_sq _ hx
  have hcardker : Nat.card sq.ker = 16 := by
    have h1 := Subgroup.card_mul_index sq.ker
    rw [Subgroup.index_ker, hrange, hAcard, Nat.card_congr (Equiv.refl Aa), W2.Aa_card] at h1
    omega
  have heq : A.subgroupOf Aa = sq.ker :=
    Subgroup.eq_of_le_of_card_ge hker (by omega)
  have hmem : (⟨y, hy⟩ : Aa) ∈ sq.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hy2
  rw [← heq] at hmem
  exact hmem

theorem ThLocalIn2.mem_Aa_or_mul_b (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {y : G} (hy : y ∈ B) : y ∈ Aa ∨ y * b ∈ Aa := by
  by_contra hcon
  replace hcon := not_or.1 hcon
  have hcard : Nat.card (Aa.subgroupOf B) = 2 ^ 8 := by
    rw [← W2.Aa_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe W2.Aa_le).toEquiv
  have hindex : (Aa.subgroupOf B).index = 2 := by
    have h1 := Subgroup.card_mul_index (Aa.subgroupOf B)
    rw [hcard, W.B_card] at h1
    omega
  have hm := Subgroup.mul_mem_iff_of_index_two hindex (a := (⟨y, hy⟩ : B))
    (b := (⟨b, W2.b_mem⟩ : B))
  have hmem : (⟨y, hy⟩ * ⟨b, W2.b_mem⟩ : B) ∈ Aa.subgroupOf B := by
    rw [hm]
    exact iff_of_false hcon.1 W2.b_not_mem
  exact hcon.2 hmem

theorem ThLocalIn2.exists_sq_ne_one (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) :
    ∃ x ∈ Aa, x ^ 2 ≠ 1 := by
  by_contra h
  have h' : ∀ x ∈ Aa, x ^ 2 = 1 := fun x hx => by
    by_contra hne
    exact h ⟨x, hx, hne⟩
  have hbot : A = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (W2.A_eq_sq y).1 hy
    simp [h' x hx]
  have hc := W.A_card
  rw [hbot, Subgroup.card_bot] at hc
  omega

theorem ThLocalIn2.psi_mem_A (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {r : G}
    (hr : ∀ a ∈ A, r * a = a * r) (hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa) {x : G} (hx : x ∈ Aa) :
    psi r x ∈ A := by
  have h1 : r * x * r⁻¹ ∈ Aa := hrAa x hx
  have hpsi : psi r x ∈ Aa := Aa.mul_mem h1 (Aa.inv_mem hx)
  refine W2.mem_A_of_sq_eq_one W hpsi ?_
  have hc : Commute (r * x * r⁻¹) x⁻¹ := W2.Aa_comm _ h1 _ (Aa.inv_mem hx)
  have hcomm := hr _ (W2.sq_mem_A hx)
  calc psi r x ^ 2 = (r * x * r⁻¹) ^ 2 * (x⁻¹) ^ 2 := hc.mul_pow 2
    _ = r * x ^ 2 * r⁻¹ * (x ^ 2)⁻¹ := by rw [conj_pow, inv_pow]
    _ = 1 := by rw [hcomm]; group

theorem ThLocalIn2.psi_mul (W2 : ThLocalIn2 B A Aa b) {r : G}
    (hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa) {x y : G} (hx : x ∈ Aa) (hy : y ∈ Aa) :
    psi r (x * y) = psi r x * psi r y := by
  have hp : psi r y ∈ Aa := Aa.mul_mem (hrAa y hy) (Aa.inv_mem hy)
  have hc : x⁻¹ * psi r y = psi r y * x⁻¹ := W2.Aa_comm _ (Aa.inv_mem hx) _ hp
  calc psi r (x * y) = (r * x * r⁻¹) * (psi r y * x⁻¹) := by unfold psi; group
    _ = (r * x * r⁻¹) * (x⁻¹ * psi r y) := by rw [hc]
    _ = psi r x * psi r y := by unfold psi; group

theorem ThLocalIn2.psi_eq_of_sq_eq (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {r : G}
    (hr : ∀ a ∈ A, r * a = a * r) (hrAa : ∀ x ∈ Aa, r * x * r⁻¹ ∈ Aa) {x x' : G}
    (hx : x ∈ Aa) (hx' : x' ∈ Aa) (h : x ^ 2 = x' ^ 2) : psi r x = psi r x' := by
  have hxx : x * x'⁻¹ ∈ Aa := Aa.mul_mem hx (Aa.inv_mem hx')
  have hsq : (x * x'⁻¹) ^ 2 = 1 := by
    have hc : Commute x x'⁻¹ := W2.Aa_comm _ hx _ (Aa.inv_mem hx')
    rw [hc.mul_pow, h, inv_pow, mul_inv_cancel]
  have hxxA : x * x'⁻¹ ∈ A := W2.mem_A_of_sq_eq_one W hxx hsq
  have h1 : psi r (x * x'⁻¹ * x') = psi r (x * x'⁻¹) * psi r x' := W2.psi_mul hrAa hxx hx'
  rwa [psi_eq_one_of_mem hr hxxA, one_mul, inv_mul_cancel_right] at h1

theorem ThLocalIn2.psi_of_mem_B (W2 : ThLocalIn2 B A Aa b) {y : G} (hy : y ∈ B)
    (hyb : y ∈ Aa ∨ y * b ∈ Aa) : (∀ x ∈ Aa, psi y x = 1) ∨ (∀ x ∈ Aa, psi y x = x ^ 2) := by
  rcases hyb with h | h
  · left
    intro x hx
    unfold psi
    rw [W2.Aa_comm y h x hx]
    group
  · right
    intro x hx
    have hy_eq : y = (y * b) * b := by rw [mul_assoc, ← pow_two, W2.b_sq, mul_one]
    have hcomm : y * b * x⁻¹ = x⁻¹ * (y * b) := W2.Aa_comm _ h _ (Aa.inv_mem hx)
    have h4 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact W2.Aa_exp x hx
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact W2.b_sq)
    have hbx : b * x * b = x⁻¹ := by
      have := W2.b_inv x hx
      rwa [hbinv] at this
    generalize hy' : y * b = y' at hy_eq hcomm
    subst hy_eq
    calc psi (y' * b) x = y' * (b * x * b) * y'⁻¹ * x⁻¹ := by
          unfold psi; rw [mul_inv_rev, hbinv]; group
      _ = y' * x⁻¹ * y'⁻¹ * x⁻¹ := by rw [hbx]
      _ = x⁻¹ * x⁻¹ := by rw [hcomm]; group
      _ = (x ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
      _ = x ^ 2 := inv_eq_of_mul_eq_one_right h4

end CFSG.EvenSporadicStandard.ThStd
