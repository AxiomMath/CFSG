module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHS5

public section

namespace CFSG.EvenSporadicStandard.TwoHS.SignInsp

open Equiv Equiv.Perm Subgroup SignS9

variable {M : Type*} [Group M] {τ : M} {D S : Subgroup M}
  {eD : D ≃* DihedralGroup 4} {eS : S ≃* Perm (Fin 5)}
  {P : Type*} [Fintype P] [DecidableEq P]

theorem retraction_ker (h : LocalPair τ D S eD eS) (hP : Fintype.card P = 5)
    (ρ : centralizer ({τ} : Set M) →* Perm P) (ι : Perm P →* M)
    (hι : ∀ u, ι u ∈ centralizer ({τ} : Set M)) (hρι : ∀ u, ρ ⟨ι u, hι u⟩ = u)
    (g : centralizer ({τ} : Set M)) : ρ g = 1 ↔ (g : M) ∈ D := by
  have hDC := left_le_centralizer h
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
  have hle : D.subgroupOf (centralizer {τ}) ≤ ρ.ker := fun g hg => hD1 g hg
  have hcardker : Nat.card ρ.ker = 8 := by
    have h1 := ρ.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hρ, Subgroup.card_top, hcardP,
      card_centralizer h] at h1
    omega
  have hcardD : Nat.card (D.subgroupOf (centralizer {τ})) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, card_of_equiv_dihedral eD]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardker, hcardD])
  refine ⟨fun hg => ?_, fun hg => hD1 g hg⟩
  have hg' : g ∈ ρ.ker := hg
  rw [← heq] at hg'
  exact hg'

theorem retraction_decomp (h : LocalPair τ D S eD eS) (hP : Fintype.card P = 5)
    (ρ : centralizer ({τ} : Set M) →* Perm P) (ι : Perm P →* M)
    (hι : ∀ u, ι u ∈ centralizer ({τ} : Set M)) (hρι : ∀ u, ρ ⟨ι u, hι u⟩ = u)
    (hcomm : ∀ (u : Perm P) (g : centralizer ({τ} : Set M)), ρ g = 1 → ι u * g = g * ι u)
    {s : M} (hs : s ∈ S) :
    s * (ι (ρ ⟨s, right_le_centralizer h hs⟩))⁻¹ = 1 ∨
      s * (ι (ρ ⟨s, right_le_centralizer h hs⟩))⁻¹ = τ := by
  have hDC := left_le_centralizer h
  have hSC := right_le_centralizer h
  set u := ρ ⟨s, hSC hs⟩ with hu
  have hker1 : (⟨s, hSC hs⟩ * ⟨ι u, hι u⟩⁻¹ : centralizer ({τ} : Set M)) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρι, ← hu, mul_inv_cancel]
  have hsU : s * (ι u)⁻¹ ∈ D := (retraction_ker h hP ρ ι hι hρι _).1 hker1
  have hcomm' : ∀ d ∈ D, s * (ι u)⁻¹ * d = d * (s * (ι u)⁻¹) := by
    intro d hd
    have h1 : Commute s d := (h.comm d hd s hs).symm
    have h2 : Commute (ι u) d :=
      hcomm u ⟨d, hDC hd⟩ ((retraction_ker h hP ρ ι hι hρι _).2 hd)
    exact h1.mul_left h2.inv_left
  exact eq_one_or_eq_tau h hsU hcomm'

theorem retraction_ne_one (h : LocalPair τ D S eD eS) (hP : Fintype.card P = 5)
    (ρ : centralizer ({τ} : Set M) →* Perm P) (ι : Perm P →* M)
    (hι : ∀ u, ι u ∈ centralizer ({τ} : Set M)) (hρι : ∀ u, ρ ⟨ι u, hι u⟩ = u)
    {s : M} (hs : s ∈ S) (hs1 : s ≠ 1) : ρ ⟨s, right_le_centralizer h hs⟩ ≠ 1 := fun h1 =>
  hs1 (h.inf s ((retraction_ker h hP ρ ι hι hρι _).1 h1) hs)

theorem retraction_mul_decomp (h : LocalPair τ D S eD eS) (hP : Fintype.card P = 5)
    (ρ : centralizer ({τ} : Set M) →* Perm P) (ι : Perm P →* M)
    (hι : ∀ u, ι u ∈ centralizer ({τ} : Set M)) (hρι : ∀ u, ρ ⟨ι u, hι u⟩ = u)
    (hcomm : ∀ (u : Perm P) (g : centralizer ({τ} : Set M)), ρ g = 1 → ι u * g = g * ι u)
    {d s : M} (hd : d ∈ D) (hdτ : d ≠ τ) (hd1 : d ≠ 1) (hs : s ∈ S) :
    ∃ d' ∈ D, d' ≠ 1 ∧ d * s = d' * ι (ρ ⟨s, right_le_centralizer h hs⟩) := by
  obtain ⟨hτD, -⟩ := h.tau_mem
  rcases retraction_decomp h hP ρ ι hι hρι hcomm hs with h1 | h1
  · exact ⟨d, hd, hd1, congrArg (d * ·) (mul_inv_eq_one.1 h1)⟩
  · refine ⟨d * τ, D.mul_mem hd hτD, ?_, ?_⟩
    · intro hdτ1
      apply hdτ
      rw [mul_eq_one_iff_eq_inv.1 hdτ1]
      exact inv_eq_of_mul_eq_one_right h.tau_sq
    · have hs' : s = τ * ι (ρ ⟨s, right_le_centralizer h hs⟩) := mul_inv_eq_iff_eq_mul.1 h1
      rw [mul_assoc]
      exact congrArg (d * ·) hs'

theorem inspect_of_map {X Y : Type*} [Group X] [Group Y] {τ : X} (D S : Subgroup X)
    (φ : X ≃* Y) (χ : Y →* ℤˣ) {τ' : Y} (hτ : φ τ = τ')
    (hc : ∀ d ∈ D.map φ.toMonoidHom, d ≠ 1 → d ≠ τ' → d * d = 1 → χ d = 1 →
      ∀ s ∈ S.map φ.toMonoidHom, s ≠ 1 → s * s = 1 → χ s = 1 →
        ¬ ∃ g : Y, d * s = g * τ' * g⁻¹) :
    ∀ d ∈ D, d ≠ 1 → d ≠ τ → d * d = 1 → χ (φ d) = 1 →
      ∀ s ∈ S, s ≠ 1 → s * s = 1 → χ (φ s) = 1 →
        ¬ ∃ g : X, d * s = g * τ * g⁻¹ := by
  rintro d hd hd1 hdτ hdd hχd s hs hs1 hss hχs ⟨g, hg⟩
  refine hc (φ d) ⟨d, hd, rfl⟩ ((map_ne_one_iff φ φ.injective).2 hd1)
    (hτ ▸ φ.injective.ne hdτ) (by rw [← map_mul, hdd, map_one]) hχd (φ s) ⟨s, hs, rfl⟩
    ((map_ne_one_iff φ φ.injective).2 hs1) (by rw [← map_mul, hss, map_one]) hχs
    ⟨φ g, ?_⟩
  rw [← hτ, ← map_mul, hg, map_mul, map_mul, map_inv]

end CFSG.EvenSporadicStandard.TwoHS.SignInsp
