module

public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.RankThree.PartOne.KS.PKitLines
public import Certificates.Certificate12625

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic

theorem no_E9_of_element_order_nine {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 2448)
    (h : H) (ho : orderOf h = 9) (E : Subgroup H) (hE : ∀ x ∈ E, x ^ 3 = 1)
    (hE9 : 9 ≤ Nat.card E) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card H).factorization 3 = 2 := by
    rw [hcard, show (2448 : ℕ) = 3 ^ 2 * 272 by norm_num]
    exact CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)
  have hSc : Nat.card (zpowers h) = 3 ^ (Nat.card H).factorization 3 := by
    rw [Nat.card_zpowers, ho, hfac]; norm_num
  let S : Sylow 3 H := Sylow.ofCard (zpowers h) hSc
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE g g.2)⟩
  obtain ⟨Q, hQ⟩ := hE3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S Q
  have hQc : Nat.card (Q : Subgroup H) = 9 := by
    rw [Sylow.card_eq_multiplicity, hfac]; norm_num
  have hEQ : E = Q := Subgroup.eq_of_le_of_card_ge hQ (by rw [hQc]; exact hE9)
  have hmem : (MulAut.conj g) h ∈ (Q : Subgroup H) := by
    have h1 : (MulAut.conj g) h ∈ (g • S : Sylow 3 H) := by
      have := Set.smul_mem_smul_set (a := MulAut.conj g)
        (show h ∈ (S : Set H) from Subgroup.mem_zpowers h)
      rw [← Sylow.coe_smul] at this
      exact this
    rw [hg] at h1
    exact h1
  rw [← hEQ] at hmem
  have h3 := hE _ hmem
  rw [← map_pow] at h3
  have h3' : h ^ 3 = 1 := (MulAut.conj g).injective (by rw [h3, map_one])
  have := orderOf_dvd_of_pow_eq_one h3'
  rw [ho] at this
  omega

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem j3_outer_centralizer_no_elementary_abelian_nine {t : Equiv.Perm (Fin 6156)}
    (ht : t ∈ j3R) (ht2 : orderOf t = 2) (htP : t ∉ j3P) {E : Subgroup (Equiv.Perm (Fin 6156))}
    (hEP : E ≤ j3P) (hEt : E ≤ centralizer ({t} : Set (Equiv.Perm (Fin 6156))))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : 9 ≤ Nat.card E) : False := by
  obtain ⟨-, -, -, hrows, hcover, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, htr⟩ := hcover t ht ht2
  obtain ⟨-, -, hout, hC, hcard, -⟩ := hrows r hr
  have hro : r.outer = true := by
    by_contra hro
    apply htP
    have hin : tp 6156 r.rep ∈ j3P := by
      by_contra hn
      exact hro (hout.2 hn)
    rw [htr]
    exact j3P.mul_mem (j3P.mul_mem hg hin) (j3P.inv_mem hg)
  have key : r.rep = j3CentTbl 21 ∧
      r.centGens = [j3CentTbl 22, j3CentTbl 23, j3CentTbl 24] ∧ r.centOrder = 2448 := by
    have hr' := hr
    simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h0 | h1
    · rw [h0] at hro
      simp at hro
    · rw [h1]
      refine ⟨?_, ?_, ?_⟩ <;> simp
  obtain ⟨hrep, hgens, hord⟩ := key
  have hperm : ∀ k < 31, Th.Rep 6156 (j3CentTbl k) (tp 6156 (j3CentTbl k)) :=
    (ctuc_j3_involution_centralizer_data).1
  have hn : (6156 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Equiv.Perm (Fin 6156), t₀ = tp 6156 r.rep := ⟨_, rfl⟩
  rw [← ht₀] at htr hC hcard
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (Equiv.Perm (Fin 6156)),
      H = j3P ⊓ centralizer ({t₀} : Set (Equiv.Perm (Fin 6156))) := ⟨_, rfl⟩
  have hHcard : Nat.card H = 2448 := by rw [hH, hcard, hord]
  have hgen : ∀ k, k = 22 ∨ k = 23 ∨ k = 24 → tp 6156 (j3CentTbl k) ∈ H := by
    intro k hk
    rw [hH, ← hC, j3C, hgens]
    refine Subgroup.subset_closure ⟨j3CentTbl k, ?_, rfl⟩
    rcases hk with rfl | rfl | rfl <;> simp
  have hg22 := hgen 22 (Or.inl rfl)
  have hg24 := hgen 24 (Or.inr (Or.inr rfl))
  obtain ⟨h, hh⟩ : ∃ h : Equiv.Perm (Fin 6156),
      h = tp 6156 (j3CentTbl 22) * tp 6156 (j3CentTbl 24) := ⟨_, rfl⟩
  have hhH : h ∈ H := by rw [hh]; exact H.mul_mem hg22 hg24
  have hRep : Th.Rep 6156 (Certificates.j3OuterH ()) h := by
    rw [hh]; exact Th.Rep.compT (hperm 22 (by norm_num)) (hperm 24 (by norm_num))
  obtain ⟨c9, c3⟩ := Certificates.certificate12625
  have h9 : h ^ 9 = 1 := (tblEq_idT_iff hn (hRep.powT hn 9)).1 c9
  have h3 : h ^ 3 ≠ 1 := fun h31 => by
    have := (tblEq_idT_iff hn (hRep.powT hn 3)).2 h31
    rw [c3] at this
    exact Bool.false_ne_true this
  have hord9 : orderOf h = 9 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show orderOf h ∣ 3 ^ 2 from orderOf_dvd_of_pow_eq_one (by simpa using h9))
    interval_cases k
    · exfalso; apply h3
      have : h = 1 := orderOf_eq_one_iff.1 (by simpa using hk')
      rw [this]; simp
    · exfalso; apply h3
      have h' := pow_orderOf_eq_one h
      rw [hk'] at h'; simpa using h'
    · simpa using hk'
  have hgP : g ∈ j3P := hg
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Subgroup (Equiv.Perm (Fin 6156)),
      E₀ = E.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hE₀mem : ∀ y, y ∈ E₀ ↔ ∃ x ∈ E, y = g⁻¹ * x * g := by
    intro y
    rw [hE₀, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
  have hE₀H : E₀ ≤ H := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hE₀mem y).1 hy
    rw [hH]
    refine ⟨?_, ?_⟩
    · exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hgP) (hEP hx)) hgP
    · show g⁻¹ * x * g ∈ centralizer ({t₀} : Set (Equiv.Perm (Fin 6156)))
      rw [mem_centralizer_singleton_iff]
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hEt hx)
      have : t₀ = g⁻¹ * t * g := by rw [htr]; group
      rw [this]
      calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
        _ = g⁻¹ * (t * x) * g := by rw [hxt]
        _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group
  have hE₀3 : ∀ x ∈ E₀, x ^ 3 = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hE₀mem y).1 hy
    have := hE3 x hx
    have hc := conj_pow (a := g⁻¹) (b := x) (i := 3)
    rw [inv_inv] at hc
    rw [hc, this]; group
  have hE₀9 : 9 ≤ Nat.card E₀ := by
    rw [hE₀, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]; exact hE9
  refine no_E9_of_element_order_nine (H := ↥H) hHcard ⟨h, hhH⟩ ?_ (E₀.subgroupOf H) ?_ ?_
  · rw [← Subgroup.orderOf_coe]; exact hord9
  · intro x hx
    have := hE₀3 x (Subgroup.mem_subgroupOf.1 hx)
    exact Subtype.ext (by simpa using this)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀H).toEquiv]; exact hE₀9

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
