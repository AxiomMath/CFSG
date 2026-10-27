module

public import Certificates.Data.Kernel.PermCent.OuterRepOC
public import CFSG.Certificates.Kernel.PermCent.OuterRepSound

public section

namespace CFSG.Certificates.Kernel.PkCV.OutR

open Subgroup

variable {n : Nat} [Small n] {P A S : Subgroup (Equiv.Perm (Fin n))}

theorem passO_split {inP : CV n → Bool} {LA LS gs csO csI : List (CV n)} {τ v : CV n}
    (h : passO inP LA LS gs csO csI τ v = true) :
    (∀ ψ ∈ LA, outT csO τ ψ = true) ∧ (∀ ψ ∈ LA, innerT csI v ψ = true) ∧
      (∀ ψ ∈ LA, centT LS gs ψ = true) ∧ (∀ ψ ∈ LA, sqOT inP LS gs ψ = true) := by
  have h' := List.all_eq_true.1 h
  simp only [Bool.and_eq_true] at h'
  exact ⟨fun ψ hψ => (h' ψ hψ).1.1.1, fun ψ hψ => (h' ψ hψ).1.1.2, fun ψ hψ => (h' ψ hψ).1.2,
    fun ψ hψ => (h' ψ hψ).2⟩

theorem sylSqO_of_pass {LA LS gs : List (CV n)} {inP : CV n → Bool}
    (hLA : ∀ x ∈ A, ∃ y ∈ LA, ev y = x) (hgs : ∀ g ∈ gs, ev g ∈ S)
    (hLS' : ∀ x ∈ S, ∃ y ∈ LS, ev y = x) (hgen : S ≤ closure {σ | σ ∈ gs.map ev})
    (hinP : ∀ y, inP y = true → ev y ∈ P) (h : ∀ ψ ∈ LA, sqOT inP LS gs ψ = true) :
    ∀ ψ ∈ A, ψ ∉ P → (∀ q ∈ S, ψ * q * ψ⁻¹ ∈ S) → ∀ v ∈ S, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ P, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
      ∀ q ∈ S, q * v = v * q := by
  intro x hx hxP hnorm v hv hv2 hv1 _ hxv
  obtain ⟨ψ, hψ, rfl⟩ := hLA x hx
  subst hxv
  have hq : sqT LS gs ψ = true := by
    have h1 := h ψ hψ
    unfold sqOT at h1
    cases e : inP ψ
    · simpa [e] using h1
    · exact absurd (hinP ψ e) hxP
  have inS : ∀ z : CV n, ev z ∈ S → inC LS z = true := fun z hz => by
    obtain ⟨y, hy, e⟩ := hLS' _ hz
    rw [inC_iff, ← ev_injective e]
    exact hy
  have hc : (!decide (ψ * ψ = 1) && decide (ψ * ψ * (ψ * ψ) = 1) && inC LS (ψ * ψ) &&
      gs.all fun q => inC LS (ψ * q * ψ⁻¹)) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
      List.all_eq_true]
    rw [ev_sq] at hv hv1 hv2
    refine ⟨⟨⟨fun e => hv1 (by rw [e, ev_one]), ?_⟩, inS _ hv⟩, fun q hq => inS _ ?_⟩
    · rw [pow_two, ← ev_mul, ev_eq_one_iff] at hv2
      exact hv2
    · rw [ev_mul, ev_mul, ev_inv]
      exact hnorm _ (hgs q hq)
  simp only [sqT, hc, Bool.not_true, Bool.false_or, fixC_iff] at hq
  have hcl : closure {σ | σ ∈ gs.map ev} ≤ centralizer {ev ψ ^ 2} := by
    rw [closure_le]
    intro σ hσ
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hσ
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ev_sq, ev_comm_iff]
    exact (hq g hg).symm
  intro q hq'
  have := hcl (hgen hq')
  rwa [mem_centralizer_singleton_iff] at this

theorem conj4K_of_check {LS refs ks : List (CV n)} (hLS' : ∀ x ∈ S, ∃ y ∈ LS, ev y = x)
    (hLS : ∀ y ∈ LS, ev y ∈ S) (hrefs : ∀ c ∈ refs, ev c ∈ P) (hks : ∀ k ∈ ks, ev k ∈ P)
    (h : conj4KC LS refs ks = true) :
    ∀ a ∈ S, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ P, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ P, k⁻¹ * a * k ∈ S ∧ ∀ y ∈ S, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y := by
  intro x hx h4 h2 hfix
  obtain ⟨a, ha, rfl⟩ := hLS' x hx
  have h1 := List.all_eq_true.1 h a ha
  have h4' : powOneC a 4 = true := by
    rw [powOneC_eq, decide_eq_true_eq]
    exact (ev_pow_eq_one_iff a 4).1 h4
  have h2' : powOneC a 2 = false := by
    rw [powOneC_eq, decide_eq_false_iff_not]
    exact fun e => h2 ((ev_pow_eq_one_iff a 2).2 e)
  rw [h4', h2'] at h1
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    List.any_eq_true] at h1
  rcases h1 with ⟨c, hc, hc'⟩ | ⟨k, hk, hk'⟩
  · exfalso
    simp only [Bool.and_eq_true, powOneC_eq, eq22C_eq, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hc'
    obtain ⟨⟨hc3, hca⟩, hna⟩ := hc'
    refine hna ((ev_comm_iff c a).1 (hfix (ev c) (hrefs c hc) ((ev_pow_eq_one_iff c 3).2 hc3) ?_))
    rw [ev_sq, ev_comm_iff]
    exact hca
  · rw [Bool.and_eq_true, inC_iff, fixC_iff] at hk'
    obtain ⟨hkS, hkc⟩ := hk'
    have hx : (ev k)⁻¹ * ev a * ev k = ev (k⁻¹ * a * k) := by rw [ev_mul, ev_mul, ev_inv]
    refine ⟨ev k, hks k hk, by rw [hx]; exact hLS _ hkS, fun y hy => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hLS' y hy
    rw [hx, ev_comm_iff]
    exact (hkc z hz).symm

end CFSG.Certificates.Kernel.PkCV.OutR

end
