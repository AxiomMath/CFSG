module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHS5

public section

namespace CFSG.EvenSporadicStandard.TwoHS.SignWr

open Equiv Equiv.Perm Subgroup SignS9

variable {M : Type*} [Group M] {τ : M} {D S : Subgroup M}
  {eD : D ≃* DihedralGroup 4} {eS : S ≃* Perm (Fin 5)}

theorem conclusion_of_retraction (h : LocalPair τ D S eD eS)
    {P : Type*} [Fintype P] [DecidableEq P] (hP : Fintype.card P = 5)
    (ρ : centralizer ({τ} : Set M) →* Perm P) (ι : Perm P →* M)
    (hι : ∀ u, ι u ∈ centralizer ({τ} : Set M)) (hρι : ∀ u, ρ ⟨ι u, hι u⟩ = u)
    (hcomm : ∀ (u : Perm P) (g : centralizer ({τ} : Set M)), ρ g = 1 → ι u * g = g * ι u)
    (χ : M →* ℤˣ) (hχι : ∀ u, χ (ι u) = sign u) (hχτ : χ τ = 1)
    (hker : ∀ g : centralizer ({τ} : Set M), ρ g = 1 → orderOf (g : M) = 4 → χ g = -1) :
    (∀ d ∈ D, orderOf d = 4 → χ d = -1) ∧ (∀ s : S, sign (eS s) = -1 → χ s = -1) := by
  have hDC := left_le_centralizer h
  have hSC := right_le_centralizer h
  have : Finite (centralizer ({τ} : Set M)) :=
    Nat.finite_of_card_ne_zero (by rw [card_centralizer h]; norm_num)
  have hρ : Function.Surjective ρ := fun u => ⟨⟨ι u, hι u⟩, hρι u⟩
  have hcardP : Nat.card (Perm P) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hP]
    rfl
  have hD1 : ∀ d (hd : d ∈ D), ρ ⟨d, hDC hd⟩ = 1 := by
    let ρD : D →* Perm P := ρ.comp (Subgroup.inclusion hDC)
    have hnorm : ρD.range.Normal := by
      refine ⟨?_⟩
      rintro _ ⟨d₁, rfl⟩ u
      obtain ⟨g, rfl⟩ := hρ u
      have hmem := conj_mem_left h (mem_centralizer_singleton_iff.1 g.2) d₁.2
      refine ⟨⟨(g : M) * d₁ * (g : M)⁻¹, hmem⟩, ?_⟩
      have hinc : Subgroup.inclusion hDC ⟨(g : M) * d₁ * (g : M)⁻¹, hmem⟩ =
          g * Subgroup.inclusion hDC d₁ * g⁻¹ := rfl
      change ρ _ = _
      rw [hinc, map_mul, map_mul, map_inv]
      rfl
    have hcard : Nat.card ρD.range ∣ 8 := by
      rw [← card_of_equiv_dihedral eD]
      exact Subgroup.card_dvd_of_surjective ρD.rangeRestrict_surjective
    have hbot := eq_bot_of_normal_card_dvd_eight hP ρD.range hcard
    intro d hd
    have : ρD ⟨d, hd⟩ ∈ ρD.range := ⟨_, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have hker_le : ∀ g : centralizer ({τ} : Set M), ρ g = 1 → (g : M) ∈ D := by
    have hle : D.subgroupOf (centralizer {τ}) ≤ ρ.ker := fun g hg => hD1 g hg
    have hcardker : Nat.card ρ.ker = 8 := by
      have h1 := ρ.ker.card_mul_index
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ, Subgroup.card_top, hcardP,
        card_centralizer h] at h1
      omega
    have hcardD : Nat.card (D.subgroupOf (centralizer {τ})) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, card_of_equiv_dihedral eD]
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardker, hcardD])
    intro g hg
    have hg' : g ∈ ρ.ker := hg
    rw [← heq] at hg'
    exact hg'
  have hS : ∀ s (hs : s ∈ S), χ s = sign (ρ ⟨s, hSC hs⟩) := by
    intro s hs
    set u := ρ ⟨s, hSC hs⟩ with hu
    have hker1 : (⟨s, hSC hs⟩ * ⟨ι u, hι u⟩⁻¹ : centralizer ({τ} : Set M)) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρι, ← hu, mul_inv_cancel]
    have hsU : s * (ι u)⁻¹ ∈ D := hker_le _ hker1
    have hcomm' : ∀ d ∈ D, s * (ι u)⁻¹ * d = d * (s * (ι u)⁻¹) := by
      intro d hd
      have h1 : Commute s d := (h.comm d hd s hs).symm
      have h2 : Commute (ι u) d := hcomm u ⟨d, hDC hd⟩ (hD1 d hd)
      exact h1.mul_left h2.inv_left
    have hsU1 : χ (s * (ι u)⁻¹) = 1 := by
      rcases eq_one_or_eq_tau h hsU hcomm' with h1 | h1
      · rw [h1, map_one]
      · rw [h1, hχτ]
    calc χ s = χ (s * (ι u)⁻¹) * χ (ι u) := by rw [← map_mul, inv_mul_cancel_right]
      _ = sign u := by rw [hsU1, one_mul, hχι]
  refine ⟨fun d hd h4 => hker ⟨d, hDC hd⟩ (hD1 d hd) h4, ?_⟩
  let ρS : S →* Perm P := ρ.comp (Subgroup.inclusion hSC)
  have hinj : Function.Injective ρS := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have hD : (t : M) ∈ D := hker_le ⟨t, hSC t.2⟩ ht
    exact Subtype.ext (h.inf _ hD t.2)
  have hbij : Function.Bijective ρS :=
    hinj.bijective_of_nat_card_le (by rw [hcardP, card_of_equiv_perm_five eS])
  have : Nontrivial P := Fintype.one_lt_card_iff_nontrivial.1 (by rw [hP]; norm_num)
  let ψ : Perm (Fin 5) →* ℤˣ := (χ.comp S.subtype).comp eS.symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro ε
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · obtain ⟨u, hu⟩ := sign_surjective P (-1)
      obtain ⟨s₀, rfl⟩ := hbij.2 u
      refine ⟨eS s₀, ?_⟩
      change χ ((eS.symm (eS s₀) : S) : M) = -1
      rw [MulEquiv.symm_apply_apply, hS s₀ s₀.2]
      exact hu
  intro s hs
  have h2 := congrArg (fun f : Perm (Fin 5) →* ℤˣ => f (eS s)) (eq_sign_of_surjective_hom hψ)
  change χ ((eS.symm (eS s) : S) : M) = sign (eS s) at h2
  rwa [MulEquiv.symm_apply_apply, hs] at h2

theorem conclusion_of_map {X Y : Type*} [Group X] [Group Y] (D S : Subgroup X)
    (eS : S ≃* Perm (Fin 5)) (φ : X ≃* Y) (χ : Y →* ℤˣ)
    (hc : (∀ d ∈ D.map φ.toMonoidHom, orderOf d = 4 → χ d = -1) ∧
      (∀ s : S.map φ.toMonoidHom,
        sign (((S.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eS) s) = -1 →
          χ s = -1)) :
    (∀ d ∈ D, orderOf d = 4 → χ (φ d) = -1) ∧ (∀ s : S, sign (eS s) = -1 → χ (φ s) = -1) := by
  refine ⟨fun d hd h4 => hc.1 (φ d) ⟨d, hd, rfl⟩ (by rw [MulEquiv.orderOf_eq, h4]), ?_⟩
  intro s hs
  have hs' : ((S.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eS)
      ⟨φ s, s, s.2, rfl⟩ = eS s := by
    rw [MulEquiv.trans_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq]
    rfl
  exact hc.2 ⟨φ s, s, s.2, rfl⟩ (by rw [hs', hs])

end CFSG.EvenSporadicStandard.TwoHS.SignWr
