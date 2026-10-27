module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataSylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Lift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_two_pairs {m : ℕ} {σ : Perm (Fin m)} (h2 : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk2 : 2 ≤ k) :
    ∃ a b c d : Fin m, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c := by
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun p : Perm (Fin m) => p x) h2
    simpa using this
  have hpos : 0 < σ.support.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
  have haσ : σ a ≠ a := Equiv.Perm.mem_support.1 ha
  have hex : ∃ c ∈ σ.support, c ≠ a ∧ c ≠ σ a := by
    by_contra hcon
    push Not at hcon
    have hsub : σ.support ⊆ {a, σ a} := fun x hx => by
      by_cases hxa : x = a
      · simp [hxa]
      · simp [hcon x hx hxa]
    have := Finset.card_le_card hsub
    have h22 : ({a, σ a} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨c, hc, hca, hcb⟩ := hex
  have hcσ : σ c ≠ c := Equiv.Perm.mem_support.1 hc
  refine ⟨a, σ a, c, σ c, haσ.symm, hca.symm, ?_, hcb.symm, ?_, hcσ.symm, rfl, hinv a, rfl,
    hinv c⟩
  · intro h
    apply hcb
    rw [h, hinv c]
  · intro h
    exact hca (σ.injective h).symm

theorem swap_mem_centralizer_involution {m : ℕ} {σ : Perm (Fin m)} (h2 : σ * σ = 1)
    (a : Fin m) : swap a (σ a) ∈ centralizer ({σ} : Set (Perm (Fin m))) := by
  rw [mem_centralizer_singleton_iff]
  have hinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
  have h3 : σ (σ a) = a := by
    have := congrArg (fun p : Perm (Fin m) => p a) h2
    simpa using this
  have h4 := Equiv.swap_apply_apply σ a (σ a)
  rw [hinv, h3, swap_comm] at h4
  calc swap a (σ a) * σ = (σ * swap a (σ a) * σ) * σ := by rw [← h4]
    _ = σ * swap a (σ a) * (σ * σ) := by group
    _ = σ * swap a (σ a) := by rw [h2, mul_one]

theorem card_inf_alternating_mul_two {α : Type*} [Fintype α] [DecidableEq α]
    {D : Subgroup (Perm α)} {g : Perm α} (hg : g ∈ D) (hs : sign g = -1) :
    Nat.card ↥(D ⊓ alternatingGroup α) * 2 = Nat.card D := by
  let φ : D →* ℤˣ := sign.comp D.subtype
  have hker : φ.ker = (alternatingGroup α).subgroupOf D := by
    ext x
    simp [φ, Perm.mem_alternatingGroup, Subgroup.mem_subgroupOf]
  have hsurj : Function.Surjective φ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, by simp [φ]⟩
    · exact ⟨⟨g, hg⟩, by simp [φ, hs]⟩
  have hrange : Nat.card φ.range = 2 := by
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have h1 := Subgroup.card_mul_index ((alternatingGroup α).subgroupOf D)
  rw [← hker, Subgroup.index_ker, hrange] at h1
  rw [← h1]
  congr 1
  rw [hker, ← Subgroup.inf_subgroupOf_left (alternatingGroup α) D]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem card_centralizer_involution {m : ℕ} {σ : Perm (Fin m)} (h2 : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk1 : 1 ≤ k) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin m)))) =
      (m - 2 * k).factorial * (2 ^ k * k.factorial) := by
  have hcyc := cycleType_eq_replicate_of_involution h2 hk
  rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.sum_cycleType, hk, hcyc, Multiset.prod_replicate,
    Fintype.card_fin]
  have : (Multiset.replicate k 2).toFinset = {2} := by
    ext x
    simp only [Multiset.mem_toFinset, Multiset.mem_replicate, Finset.mem_singleton]
    exact ⟨fun hx => hx.2, fun hx => ⟨by omega, hx⟩⟩
  rw [this, Finset.prod_singleton, Multiset.count_replicate_self]
  ring

theorem card_centralizer_inf_alternating {m : ℕ} {σ : Perm (Fin m)} (h2 : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk1 : 1 ≤ k) :
    Nat.card ↥(centralizer ({σ} : Set (Perm (Fin m))) ⊓ alternatingGroup (Fin m)) * 2 =
      (m - 2 * k).factorial * (2 ^ k * k.factorial) := by
  have hpos : 0 < σ.support.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
  have haσ : σ a ≠ a := Equiv.Perm.mem_support.1 ha
  rw [card_inf_alternating_mul_two (swap_mem_centralizer_involution h2 a)
    (Perm.sign_swap haσ.symm), card_centralizer_involution h2 hk hk1]

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.exists_not_fixed {C : CoverSetup n K} (hn : 8 ≤ n) {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk2 : 2 ≤ k) :
    ∃ y : K, C.ρ y * σ = σ * C.ρ y ∧ α y ≠ y := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ha, hb, hc, hd⟩ :=
    exists_two_pairs hσ hk hk2
  set δ : Perm (Fin n) := swap a b * swap c d with hδ
  obtain ⟨xδ, hxδ⟩ := C.exists_ρ_eq (σ := δ) (by
    rw [hδ, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide)
  have hsignε : sign (swap a c * swap b d) = 1 := by
    rw [Perm.sign_mul, Perm.sign_swap hac, Perm.sign_swap hbd]
    decide
  obtain ⟨y, hy⟩ := C.exists_ρ_eq hsignε
  have h' := h.conj_mul xδ⁻¹
  have hρinv : C.ρ xδ⁻¹ = δ := by
    rw [map_inv, hxδ, hδ, dbl_inv hab hac had hbc hbd hcd]
  rw [hρinv] at h'
  have hfix : ∀ z, (z = a ∨ z = b ∨ z = c ∨ z = d) → (δ * σ) z = z := fun z hz => by
    rw [hδ, dbl_mul_apply hab hac had hbc hbd hcd ha hb hc hd z]
    simp [hz]
  have hαy : (MulAut.conj xδ⁻¹ * α) y = y :=
    h'.apply_eq_of_dbl_fixed hac hab had hbc.symm hcd hbd (hfix a (Or.inl rfl))
      (hfix c (Or.inr (Or.inr (Or.inl rfl)))) (hfix b (Or.inr (Or.inl rfl)))
      (hfix d (Or.inr (Or.inr (Or.inr rfl)))) hy
  have hαy' : α y = xδ * y * xδ⁻¹ := by
    simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv] at hαy
    calc α y = xδ * (xδ⁻¹ * α y * xδ) * xδ⁻¹ := by group
      _ = xδ * y * xδ⁻¹ := by rw [hαy]
  have hπδ : (C.π xδ : Perm (Fin n)) = δ := hxδ
  have e1 : (C.π xδ : Perm (Fin n)) a = b := by
    rw [hπδ, hδ, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]
  have e2 : (C.π xδ : Perm (Fin n)) c = d := by
    rw [hπδ, hδ, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm]
  have e3 : (C.π xδ : Perm (Fin n)) b = a := by
    rw [hπδ, hδ, Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
  have e4 : (C.π xδ : Perm (Fin n)) d = c := by
    rw [hπδ, hδ, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm]
  refine ⟨y, ?_, ?_⟩
  · rw [hy]
    exact (comm_swap_pairs hab had hbc.symm hcd σ ha hc hb hd).symm
  · intro hy'
    rw [hαy'] at hy'
    have hc1 : ⁅xδ, y⁆ = 1 := by
      rw [commutatorElement_def]
      calc xδ * y * xδ⁻¹ * y⁻¹ = (xδ * y * xδ⁻¹) * y⁻¹ := rfl
        _ = y * y⁻¹ := by rw [hy']
        _ = 1 := mul_inv_cancel y
    exact commutator_ne_one_of_doubleCover hn C.hX C.surj C.ker hac hab had hbc.symm hcd hbd
      e1 e2 e3 e4 hy hc1

theorem CoverSetup.Induces.card_fixSub_of_not_fixed [Finite K] {C : CoverSetup n K}
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk1 : 1 ≤ k)
    (hex : ∃ y : K, C.ρ y * σ = σ * C.ρ y ∧ α y ≠ y) :
    Nat.card (fixSub α) = 2 ^ (k - 1) * k.factorial * (n - 2 * k).factorial := by
  classical
  set H : Subgroup K := (centralizer ({σ} : Set (Perm (Fin n)))).comap C.ρ with hHdef
  have hH : ∀ x ∈ H, C.ρ x * σ = σ * C.ρ x := fun x hx =>
    mem_centralizer_singleton_iff.1 hx
  have hle : fixSub α ≤ H := by
    intro x hx
    rw [hHdef, Subgroup.mem_comap, mem_centralizer_singleton_iff]
    have h1 := h.map_ρ x
    rw [mem_fixSub.1 hx] at h1
    calc C.ρ x * σ = (σ * C.ρ x * σ⁻¹) * σ := by rw [← h1]
      _ = σ * C.ρ x := by group
  have hle2 := h.index_fixSub_le_two H hH
  obtain ⟨y, hyρ, hy⟩ := hex
  have hyH : y ∈ H := by
    rw [hHdef, Subgroup.mem_comap, mem_centralizer_singleton_iff]
    exact hyρ
  have hne1 : ((fixSub α).subgroupOf H).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    have : (⟨y, hyH⟩ : H) ∈ (fixSub α).subgroupOf H := by rw [h1]; trivial
    exact hy this
  have hne0 : ((fixSub α).subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : ((fixSub α).subgroupOf H).index = 2 := by omega
  have hc1 : Nat.card H = Nat.card (fixSub α) * 2 := by
    have h1 := Subgroup.card_mul_index ((fixSub α).subgroupOf H)
    rw [hidx] at h1
    rw [← h1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hD : (centralizer ({σ} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)).comap C.ρ = H := by
    ext x
    rw [hHdef, Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, Perm.mem_alternatingGroup.2 (C.sign_ρ x)⟩⟩
  have hc2 : Nat.card H = 2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin n))) ⊓
      alternatingGroup (Fin n)) := by
    rw [← hD]
    exact C.card_comap inf_le_right
  have hc3 := card_centralizer_inf_alternating hσ hk hk1
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) ?_
  calc Nat.card (fixSub α) * 2 = Nat.card H := hc1.symm
    _ = 2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) := hc2
    _ = Nat.card ↥(centralizer ({σ} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) * 2 :=
        mul_comm _ _
    _ = (n - 2 * k).factorial * (2 ^ k * k.factorial) := hc3
    _ = 2 ^ (k - 1) * k.factorial * (n - 2 * k).factorial * 2 := by rw [hpow]; ring

theorem CoverSetup.Induces.card_fixSub [Finite K] {C : CoverSetup n K} (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hk2 : 2 ≤ k) :
    Nat.card (fixSub α) = 2 ^ (k - 1) * k.factorial * (n - 2 * k).factorial :=
  h.card_fixSub_of_not_fixed hσ hk (by omega) (h.exists_not_fixed hn hσ hk hk2)

end AhatData

end CFSG.OddStandard.Solomon75
