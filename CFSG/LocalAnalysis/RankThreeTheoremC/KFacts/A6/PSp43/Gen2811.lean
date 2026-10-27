module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.ThreeC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.Open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

@[expose] def genOK (d : ℕ × List (Fin 45) × List (Fin 45)) : Bool :=
  decide (d.1 < Eelems.length) &&
    tmul (conjTab d.2.1 (Eelems.getD d.1 [])) (conjTab d.2.2 (Eelems.getD d.1 [])) == wtab x0W

theorem gen_ok : genW.all genOK = true := by decide +kernel

theorem gen_cover : (List.range Eelems.length).all (fun i => (Eelems.getD i [] == tid) ||
    (Eelems.getD i [] == tau0Tab) || !(tmul (Eelems.getD i []) (Eelems.getD i []) == tid) ||
    (genW.map (·.1)).contains i) = true := by
  decide +kernel

theorem exists_gen_two {a : Equiv.Perm (Fin 45)} (ha : a ∈ E) (ha1 : a ≠ 1)
    (ha0 : a ≠ tauPerm 0) (ha2 : a * a = 1) :
    ∃ h₁ ∈ P, ∃ h₂ ∈ P, wperm x0W = (h₁ * a * h₁⁻¹) * (h₂ * a * h₂⁻¹) := by
  obtain ⟨i, hi, hr⟩ := (mem_gen_words E_enumOK a).1 ha
  have h1 := List.all_eq_true.1 gen_cover i (List.mem_range.2 hi)
  have hne1 : (Eelems.getD i [] == tid) = false := by
    rw [beq_eq_false_iff_ne]
    rintro h
    exact ha1 (rep_unique (h ▸ hr) rep_one)
  have hne0 : (Eelems.getD i [] == tau0Tab) = false := by
    rw [beq_eq_false_iff_ne]
    rintro h
    have hr' : Rep a tau0Tab := h ▸ hr
    exact ha0 (rep_unique hr' (rep_tauPerm 0))
  have hsq : (tmul (Eelems.getD i []) (Eelems.getD i []) == tid) = true := by
    rw [beq_iff_eq]
    exact rep_eq_tab (rep_mul hr hr) (ha2 ▸ rep_one)
  rw [hne1, hne0, hsq] at h1
  simp only [Bool.false_or, Bool.not_true, List.contains_iff_mem, List.mem_map] at h1
  obtain ⟨d, hd, rfl⟩ := h1
  have hok := List.all_eq_true.1 gen_ok d hd
  simp only [genOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  refine ⟨wperm d.2.1, wperm_mem _, wperm d.2.2, wperm_mem _, ?_⟩
  exact rep_unique (rep_wperm x0W) (hok.2 ▸ rep_mul (rep_conj _ hr) (rep_conj _ hr))

theorem conj_mem_map_conj {A : Subgroup (Equiv.Perm (Fin 45))} {a : Equiv.Perm (Fin 45)}
    (ha : a ∈ A) (k : Equiv.Perm (Fin 45)) :
    k * a * k⁻¹ ∈ A.map (MulAut.conj k).toMonoidHom :=
  ⟨a, ha, rfl⟩

theorem pCoreOf_conj_tau {g : Equiv.Perm (Fin 45)} (hg : g ∈ P) :
    pCoreOf 2 (P ⊓ centralizer ({g * tauPerm 0 * g⁻¹} : Set (Equiv.Perm (Fin 45)))) =
      E.map (MulAut.conj g).toMonoidHom := by
  rw [P_inf_centralizer_conj hg, pCoreOf_map_of_injective' (MulAut.conj g).injective, pCoreOf_H0]

theorem gen_two_of_model {z x : Equiv.Perm (Fin 45)} (hzP : z ∈ P) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hzc : Nat.card ↥(P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45)))) = 576)
    (hxP : x ∈ P) (hx3 : x ^ 3 = 1)
    (hxc : Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 45)))) = 108)
    {A : Subgroup (Equiv.Perm (Fin 45))} (hA : IsElemAbelian 2 A)
    (hAle : A ≤ pCoreOf 2 (P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45)))))
    (hAz : ¬ A ≤ zpowers z) :
    ∃ g₁ ∈ P, ∃ g₂ ∈ P,
      x ∈ A.map (MulAut.conj g₁).toMonoidHom ⊔ A.map (MulAut.conj g₂).toMonoidHom := by
  obtain ⟨g, hgP, rfl⟩ := exists_conj_tau_zero hzP hz2 hz1 hzc
  obtain ⟨h, hhP, rfl⟩ := exists_conj_x0 hxP hx3 hxc
  rw [pCoreOf_conj_tau hgP] at hAle
  obtain ⟨a, haA, haz⟩ := Set.not_subset.1 hAz
  obtain ⟨a₀, ha₀E, rfl⟩ := hAle haA
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at haA haz
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    exact haz (by simp)
  have ha₀0 : a₀ ≠ tauPerm 0 := by
    rintro rfl
    exact haz (mem_zpowers _)
  have ha₀2 : a₀ * a₀ = 1 := by
    have h2 := hA.2 _ haA
    have : g * (a₀ * a₀) * g⁻¹ = 1 := by
      rw [← h2, pow_two]; group
    simpa using this
  obtain ⟨h₁, hh₁, h₂, hh₂, he⟩ := exists_gen_two ha₀E ha₀1 ha₀0 ha₀2
  refine ⟨h * h₁ * g⁻¹, mul_mem (mul_mem hhP hh₁) (inv_mem hgP),
    h * h₂ * g⁻¹, mul_mem (mul_mem hhP hh₂) (inv_mem hgP), ?_⟩
  have e : h * wperm x0W * h⁻¹ = (h * h₁ * g⁻¹) * (g * a₀ * g⁻¹) * (h * h₁ * g⁻¹)⁻¹ *
      ((h * h₂ * g⁻¹) * (g * a₀ * g⁻¹) * (h * h₂ * g⁻¹)⁻¹) := by
    rw [he]; group
  rw [e]
  exact mul_mem (mem_sup_left (conj_mem_map_conj haA _)) (mem_sup_right (conj_mem_map_conj haA _))

theorem gen_four_of_model {z x : Equiv.Perm (Fin 45)} (hzP : z ∈ P) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hzc : Nat.card ↥(P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45)))) = 576)
    (hxP : x ∈ P) (hx3 : x ^ 3 = 1)
    (hxc : Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 45)))) = 108)
    {A : Subgroup (Equiv.Perm (Fin 45))} (hA1 : A ≠ ⊥) (hA : IsElemAbelian 2 A)
    (hAle : A ≤ pCoreOf 2 (P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45))))) :
    ∃ g : Fin 4 → Equiv.Perm (Fin 45), (∀ i, g i ∈ P) ∧
      x ∈ ⨆ i, A.map (MulAut.conj (g i)).toMonoidHom := by
  by_cases hAz : A ≤ zpowers z
  ·
    have hzA : z ∈ A := by
      obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
      have ha := hAz haA
      have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
      rw [mem_zpowers_iff] at ha
      obtain ⟨k, hk⟩ := ha
      have : (a : Equiv.Perm (Fin 45)) = z ^ (k % 2) := by
        rw [← hk, ← zpow_mod_orderOf, hzo]
        norm_cast
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · have ha' : a = 1 := by rw [this, h0, zpow_zero]
        exact absurd (Subtype.ext ha') ha1
      · rw [this, h1, zpow_one] at haA
        exact haA
    obtain ⟨g, hgP, rfl⟩ := exists_conj_tau_zero hzP hz2 hz1 hzc
    obtain ⟨h, hhP, rfl⟩ := exists_conj_x0 hxP hx3 hxc
    have htau : ∀ j : Fin 45, ∃ c ∈ P, tauPerm j = c * tauPerm 0 * c⁻¹ := by
      intro j
      obtain ⟨c, hcP, hc0⟩ := exists_mem_P_apply_zero j
      exact ⟨c, hcP, by rw [conj_tauPerm hcP, hc0]⟩
    obtain ⟨c₁, hc₁, e₁⟩ := htau 13
    obtain ⟨c₂, hc₂, e₂⟩ := htau 12
    obtain ⟨c₃, hc₃, e₃⟩ := htau 4
    obtain ⟨c₄, hc₄, e₄⟩ := htau 3
    set k : Fin 4 → Equiv.Perm (Fin 45) := ![h * c₁ * g⁻¹, h * c₂ * g⁻¹, h * c₃ * g⁻¹,
      h * c₄ * g⁻¹] with hk
    have hk0 : k 0 = h * c₁ * g⁻¹ := rfl
    have hk1 : k 1 = h * c₂ * g⁻¹ := rfl
    have hk2 : k 2 = h * c₃ * g⁻¹ := rfl
    have hk3 : k 3 = h * c₄ * g⁻¹ := rfl
    refine ⟨k, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hk0 ▸ mul_mem (mul_mem hhP hc₁) (inv_mem hgP)
      · exact hk1 ▸ mul_mem (mul_mem hhP hc₂) (inv_mem hgP)
      · exact hk2 ▸ mul_mem (mul_mem hhP hc₃) (inv_mem hgP)
      · exact hk3 ▸ mul_mem (mul_mem hhP hc₄) (inv_mem hgP)
    · have hx0 : wperm x0W = tauPerm 13 * tauPerm 12 * tauPerm 4 * tauPerm 3 := by
        simp [x0W, wperm, mul_assoc]
      have hmem : ∀ i : Fin 4, k i * (g * tauPerm 0 * g⁻¹) * (k i)⁻¹ ∈
          ⨆ i, A.map (MulAut.conj (k i)).toMonoidHom := fun i =>
        mem_iSup_of_mem i (conj_mem_map_conj hzA (k i))
      have e : h * wperm x0W * h⁻¹ =
          k 0 * (g * tauPerm 0 * g⁻¹) * (k 0)⁻¹ * (k 1 * (g * tauPerm 0 * g⁻¹) * (k 1)⁻¹) *
          (k 2 * (g * tauPerm 0 * g⁻¹) * (k 2)⁻¹) * (k 3 * (g * tauPerm 0 * g⁻¹) * (k 3)⁻¹) := by
        rw [hk0, hk1, hk2, hk3, hx0, e₁, e₂, e₃, e₄]
        group
      rw [e]
      exact mul_mem (mul_mem (mul_mem (hmem 0) (hmem 1)) (hmem 2)) (hmem 3)
  · obtain ⟨g₁, hg₁, g₂, hg₂, hx⟩ :=
      gen_two_of_model hzP hz2 hz1 hzc hxP hx3 hxc hA hAle hAz
    refine ⟨![g₁, g₂, g₂, g₂], ?_, ?_⟩
    · intro i
      fin_cases i <;> simpa
    · have hle : A.map (MulAut.conj g₁).toMonoidHom ⊔ A.map (MulAut.conj g₂).toMonoidHom ≤
          ⨆ i, A.map (MulAut.conj (![g₁, g₂, g₂, g₂] i)).toMonoidHom :=
        sup_le (le_iSup_of_le (0 : Fin 4) le_rfl) (le_iSup_of_le (1 : Fin 4) le_rfl)
      exact hle hx

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
