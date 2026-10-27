module

public import CFSG.GH74.Generic.S3.LinEvenInv
public import CFSG.GH74.Generic.S3.V1InnerUni
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.B1.PilotS3Models

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3L3KGroup

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped MatrixGroups commutatorElement

theorem exists_invDataB4 {Kt : Type} [Group Kt] [Finite Kt] (h3 : QShape3 Kt) {u : Kt}
    (hu : orderOf u = 2) :
    ∃ S : Subgroup Kt, S ≤ centralizer ({u} : Set Kt) ∧ u ∈ S ∧ CFSG.IsQuasisimple ↥S ∧
      (∀ a ∈ centralizer ({u} : Set Kt), ∀ b ∈ centralizer ({u} : Set Kt), ⁅a, b⁆ ∈ S) ∧
      (∀ σ : MulAut Kt, σ * σ = 1 → (∀ s ∈ S, σ s = s) → σ = 1 ∨ σ = MulAut.conj u) := by
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  have hu1 : u ≠ 1 := fun h => by simp [h] at hu
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := h3
  have h5 : 5 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have := Nat.odd_iff.mp hodd
    omega
  rcases hmod with hm | hm
  · obtain ⟨S, hS⟩ := S3.exists_invDataB4_lin hp hp2 h5 (stated_of_lieModel_PSL hm) hu2 hu1
    exact ⟨S, hS.le_centralizer, hS.mem, hS.quasisimple, hS.commutator_mem, hS.aut_fixing⟩
  · obtain ⟨S, hS⟩ := ((S3.libData_uni hp hp2 h5) Kt (stated_of_lieModel_PSU hm)).1 u hu2 hu1
    exact ⟨S, hS.le_centralizer, hS.mem, hS.quasisimple, hS.commutator_mem, hS.aut_fixing⟩

theorem exists_sl2_component {Kt : Type} [Group Kt] [Finite Kt] (h3 : QShape3 Kt)
    (hZ : ∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1) {u : Kt} (hu : orderOf u = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup Kt),
      Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧ Nonempty (↥S ≃* SL(2, F)) ∧ u ∈ S ∧
      S ≤ centralizer ({u} : Set Kt) ∧
      (∀ a ∈ centralizer ({u} : Set Kt), ∀ b ∈ centralizer ({u} : Set Kt), ⁅a, b⁆ ∈ S) ∧
      IsPCompIn 2 (centralizer ({u} : Set Kt)) S ∧
      (∀ σ : MulAut Kt, σ * σ = 1 → (∀ s ∈ S, σ s = s) → σ = 1 ∨ σ = MulAut.conj u) := by
  obtain ⟨S, hSc, huS, hSq, hScomm, hB4⟩ := exists_invDataB4 h3 hu
  obtain ⟨F, _, _, P, _, ⟨e⟩, hP⟩ := exists_equiv_grpS3_of_qShape3 h3
  have hZ' : ∀ z ∈ (⊤ : Subgroup Kt), (∀ g ∈ (⊤ : Subgroup Kt), g * z = z * g) → z = 1 :=
    fun z _ hz => hZ z (fun g => hz g trivial)
  have hY : Split3Like F (⊤ : Subgroup Kt) :=
    Split3Like.of_equiv (Subgroup.topEquiv.trans e) hP hZ'
  obtain ⟨J, -, hJ⟩ := hY.split u trivial hu
  have hSJ : S ≤ J := by
    refine hJ.le_of_perfect' (le_inf hSc (le_top)) ?_
    exact Subgroup.isPerfect_iff.1 hSq.1
  have hJS : J ≤ S := by
    have h1 : ⁅J, J⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact hScomm a (hJ.le_H ha).1 b (hJ.le_H hb).1
    rw [hJ.perfect] at h1
    exact h1
  have hSeq : S = J := le_antisymm hSJ hJS
  subst hSeq
  have h5 : 5 ≤ Nat.card F := by
    have h4 := hP.big
    obtain ⟨k, hk⟩ := hP.odd
    omega
  exact ⟨F, inferInstance, inferInstance, S, hP.odd, h5, hJ.equiv, huS, hSc, hScomm,
    by simpa using hJ.isPCompIn, hB4⟩

end S3L3KGroup

end CFSG.GH74.Generic.BProg.B3
