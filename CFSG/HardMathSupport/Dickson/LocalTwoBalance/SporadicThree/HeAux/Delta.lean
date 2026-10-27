module

public import CFSG.RankThree.PartOne.KS.HeKit
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.Sporadic.HeldB.OuterCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux

open CFSG.Open CFSG.Sporadic.HeldB CFSG.HardMathSupport.Timmesfeld.Proving


theorem he_delta_trivial
    (hA : ∀ x ∈ heP, orderOf x = 3 →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) = ⊥)
    (hC : ∀ d ∈ heP, orderOf d = 3 →
      (∀ x ∈ heP, x * d = d * x → x * heAutU = heAutU * x) →
        d ∈ Subgroup.map heOuterD.subtype (Subgroup.center ↥heOuterD))
    (E : Subgroup (Equiv.Perm (Fin 8330))) (hEP : E ≤ heP) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) (H' : Subgroup (Equiv.Perm (Fin 8330))) (hPH : heP ≤ H')
    (hHR : H' ≤ heAutGroup) (y : Equiv.Perm (Fin 8330))
    (hy : ∀ d ∈ E, d ≠ 1 →
      y ∈ GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))))) :
    y = 1 := by
  classical
  have hAM := CFSG.RankThree.PartOne.heAutModel
  have h3 : ∀ d ∈ E, d ≠ 1 → orderOf d = 3 := fun d hd hd1 =>
    orderOf_eq_prime (hE.2 d hd) hd1
  obtain ⟨d₀, hd₀E, hd₀1⟩ : ∃ d ∈ E, d ≠ 1 := by
    by_contra hall
    push_neg at hall
    have : Nat.card E = 1 := Subgroup.card_eq_one.2 ((Subgroup.eq_bot_iff_forall _).2 hall)
    rw [hEc] at this
    norm_num at this
  have hy₀ := hy d₀ hd₀E hd₀1
  have hyH : y ∈ H' := (Subgroup.mem_inf.1 (GLAPPrimeCoreOf_le _ hy₀)).1
  have hyR : y ∈ heAutGroup := hHR hyH
  have hcore : ∀ d ∈ E, d ≠ 1 →
      ∀ n ∈ GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330)))),
        n ∈ heP → n = 1 := by
    intro d hd hd1 n hn hnP
    have hle : GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330)))) ⊓
        heP ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) := by
      refine le_GLAPPrimeCoreOf_of_normal ?_ ?_ ?_
      · intro x hx
        exact ⟨(Subgroup.mem_inf.1 (GLAPPrimeCoreOf_le _ hx.1)).2, hx.2⟩
      · intro g hg x hx
        have hgH : g ∈ H' ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) :=
          ⟨hPH hg.2, hg.1⟩
        exact ⟨GLAPPrimeCoreOf_conj_mem g hgH x hx.1,
          heP.mul_mem (heP.mul_mem hg.2 hx.2) (heP.inv_mem hg.2)⟩
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          (coprime_card_GLAPPrimeCoreOf Nat.prime_three _)
    have h1 := hle ⟨hn, hnP⟩
    rw [hA d (hEP hd) (h3 d hd hd1)] at h1
    exact Subgroup.mem_bot.1 h1
  have hcomm : ∀ d ∈ E, d ≠ 1 → ∀ g ∈ heP, g * d = d * g → g * y = y * g := by
    intro d hd hd1 g hgP hgd
    have hyO := hy d hd hd1
    have hgH : g ∈ H' ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) :=
      ⟨hPH hgP, Subgroup.mem_centralizer_singleton_iff.2 hgd⟩
    have hc1 := GLAPPrimeCoreOf_conj_mem g hgH y hyO
    have hc2 : g * y * g⁻¹ * y⁻¹ ∈
        GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330)))) :=
      Subgroup.mul_mem _ hc1 (Subgroup.inv_mem _ hyO)
    have hc3 : g * y * g⁻¹ * y⁻¹ ∈ heP := by
      have h1 : g * (y * g⁻¹ * y⁻¹) ∈ heP :=
        heP.mul_mem hgP (hAM.conj_mem y hyR g⁻¹ (heP.inv_mem hgP))
      have h2 : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
      rw [h2]
      exact h1
    have h1 := hcore d hd hd1 _ hc2 hc3
    have h2 : g * y * g⁻¹ = y := mul_inv_eq_one.1 h1
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h2]
  by_cases hyP : y ∈ heP
  · exact hcore d₀ hd₀E hd₀1 y hy₀ hyP
  exfalso
  have hy2P : y ^ 2 ∈ heP := by
    have hi : (heP.subgroupOf heAutGroup).index = 2 := heP_relIndex_heAutGroup
    have hsq := Subgroup.sq_mem_of_index_two hi (⟨y, hyR⟩ : ↥heAutGroup)
    rw [Subgroup.mem_subgroupOf] at hsq
    simpa using hsq
  have hy2 : y ^ 2 = 1 := hcore d₀ hd₀E hd₀1 _ (Subgroup.pow_mem _ hy₀ 2) hy2P
  have hy1 : y ≠ 1 := fun h => hyP (h ▸ heP.one_mem)
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  obtain ⟨-, hcl, -⟩ := ctbh_outer_involution_class_exhaustion
  have hymem : y ∈ {x : Equiv.Perm (Fin 8330) | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2} :=
    ⟨hyR, hyP, hyo⟩
  rw [hcl] at hymem
  obtain ⟨g, hgP, hyg⟩ := hymem
  have hZ : ∀ d ∈ E, d ≠ 1 →
      g⁻¹ * d * g ∈ Subgroup.map heOuterD.subtype (Subgroup.center ↥heOuterD) := by
    intro d hd hd1
    have hdP : d ∈ heP := hEP hd
    have hd' : g⁻¹ * d * g ∈ heP := heP.mul_mem (heP.mul_mem (heP.inv_mem hgP) hdP) hgP
    have hd'o : orderOf (g⁻¹ * d * g) = 3 := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective d
      simpa [MulAut.conj_apply, h3 d hd hd1] using this
    refine hC _ hd' hd'o fun x hxP hx => ?_
    have hgx : g * x * g⁻¹ ∈ heP := heP.mul_mem (heP.mul_mem hgP hxP) (heP.inv_mem hgP)
    have h1 : g * x * g⁻¹ * d = d * (g * x * g⁻¹) :=
      calc g * x * g⁻¹ * d = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by rw [hx]
        _ = d * (g * x * g⁻¹) := by group
    have h2 := hcomm d hd hd1 _ hgx h1
    calc x * heAutU = g⁻¹ * ((g * x * g⁻¹) * (g * heAutU * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hyg]
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h2]
      _ = heAutU * x := by rw [hyg]; group
  have hsub : E.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.map heOuterD.subtype (Subgroup.center ↥heOuterD) := by
    rintro _ ⟨d, hd, rfl⟩
    by_cases hd1 : d = 1
    · subst hd1
      rw [map_one]
      exact Subgroup.one_mem _
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hZ d hd hd1
  have hcle := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEc,
    Subgroup.card_map_of_injective heOuterD.subtype_injective, card_center_heOuterD] at hcle
  norm_num at hcle

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux
