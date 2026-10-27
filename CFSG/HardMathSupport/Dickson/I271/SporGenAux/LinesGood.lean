module

public import CFSG.RankThree.PartOne.KS.Lines
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.AutModelPlane

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.RankThree.PartOne

theorem good_of_lines {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} (hPR : P ≤ R) {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    {Good : ℕ → Prop}
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, g * xs i * g⁻¹ = xs j) ∧
      Good (Nat.card (R ⊓ centralizer ({xs i} : Set M) : Subgroup M))) :
    ∀ y ∈ P, orderOf y = p → Good (Nat.card (R ⊓ centralizer ({y} : Set M) : Subgroup M)) := by
  intro y hyP hord
  obtain ⟨g, hgP, j, hcent⟩ := exists_conj_line hp hSyl hlines hyP hord
  obtain ⟨i, ⟨r, hrR, hr⟩, hgood⟩ := hrep j
  have h1 := card_inf_centralizer_conj R (hPR hgP) (g⁻¹ * y * g)
  rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h1
  have h2 := card_inf_centralizer_conj R hrR (xs i)
  rw [hr] at h2
  rw [h1, hcent, h2]
  exact hgood


theorem rankOK_of_lines {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} (hPR : P ≤ R) {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, g * xs i * g⁻¹ = xs j) ∧
      RankOK p (R ⊓ centralizer ({xs i} : Set M) : Subgroup M)) :
    ∀ y ∈ P, orderOf y = p → RankOK p (R ⊓ centralizer ({y} : Set M) : Subgroup M) := by
  intro y hyP hord
  obtain ⟨g, hgP, j, hcent⟩ := exists_conj_line hp hSyl hlines hyP hord
  obtain ⟨i, ⟨r, hrR, hr⟩, hgood⟩ := hrep j
  have h1 : R ⊓ centralizer ({y} : Set M) =
      (R ⊓ centralizer ({xs j} : Set M)).map (MulAut.conj g).toMonoidHom := by
    have := inf_centralizer_conj_eq R (hPR hgP) (g⁻¹ * y * g)
    rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group, hcent] at this
    exact this
  have h2 : RankOK p (R ⊓ centralizer ({xs j} : Set M) : Subgroup M) := by
    have := rankOK_inf_centralizer_conj R hrR hgood
    rwa [hr] at this
  rw [h1]
  exact rankOK_map_conj h2 g

end CFSG.HardMathSupport.Dickson.I271
