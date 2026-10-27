module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JDr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JA5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

variable {G : Type} [Group G] {t : G} {L S : Subgroup G}

theorem sec12D_elemAb (hbd : Sec10BData t L S) {P : Subgroup ↥(secM t S L ⊓ L)}
    (hP : IsElemAbelian 2 P) :
    Nat.card P ≤ 16 ∧ (Nat.card P = 16 → P = (secB S L).subgroupOf (secM t S L ⊓ L)) := by
  classical
  obtain ⟨ρ, φ, _, hker, hinj, hmem, hact⟩ := sec12D_struct hbd
  have hleAM : secA t S L ≤ secM t S L := by
    rw [secM]
    exact Subgroup.le_normalizer
  have hBD : secB S L ≤ secM t S L ⊓ L := le_inf (le_sup_left.trans hleAM) hbd.1
  have hKcard : Nat.card ((secB S L).subgroupOf (secM t S L ⊓ L)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBD).toEquiv, hbd.2.1]
    norm_num
  haveI : Finite ((secB S L).subgroupOf (secM t S L ⊓ L)) :=
    Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  have hQea : IsElemAbelian 2 (P.map ρ) := hP.map ρ
  have hcardP : Nat.card ↥(P ⊓ ρ.ker) * Nat.card (P.map ρ) = Nat.card P :=
    sec12J_card_inf_ker_mul ρ P
  by_cases hQ : P.map ρ = ⊥
  · have hPle : P ≤ (secB S L).subgroupOf (secM t S L ⊓ L) := by
      intro y hy
      have hymap : ρ y ∈ P.map ρ := Subgroup.mem_map_of_mem ρ hy
      rw [hQ, Subgroup.mem_bot] at hymap
      rw [← hker, MonoidHom.mem_ker]
      exact hymap
    have hle16 : Nat.card P ≤ 16 := by
      have h := Subgroup.card_le_of_le hPle
      rwa [hKcard] at h
    exact ⟨hle16, fun h16 => Subgroup.eq_of_le_of_card_ge hPle (by omega)⟩
  · have hmemB : ∀ y : ↥(P ⊓ ρ.ker), (y.1 : G) ∈ secB S L := by
      intro y
      have h1 : y.1 ∈ (secB S L).subgroupOf (secM t S L ⊓ L) := by
        rw [← hker]
        exact y.2.2
      exact Subgroup.mem_subgroupOf.mp h1
    let vOf : ↥(P ⊓ ρ.ker) → (Fin 5 → ZMod 2) := fun y =>
      Classical.choose ((hmem (y.1 : G)).mp (hmemB y))
    have hspec : ∀ y : ↥(P ⊓ ρ.ker), IsEvenVec (vOf y) ∧ φ (vOf y) = (y.1 : G) :=
      fun y => Classical.choose_spec ((hmem (y.1 : G)).mp (hmemB y))
    have hfixOf : ∀ y : ↥(P ⊓ ρ.ker), ∀ σ ∈ P.map ρ,
        permVec (σ : Equiv.Perm (Fin 5)) (vOf y) = vOf y := by
      intro y σ hσ
      obtain ⟨y', hy'P, hy'σ⟩ := Subgroup.mem_map.mp hσ
      have hcommG : (y' : G) * (y.1 : G) = (y.1 : G) * (y' : G) :=
        congrArg (fun z : ↥(secM t S L ⊓ L) => (z : G)) (hP.comm hy'P y.2.1)
      have hfixy' : (y' : G) * φ (vOf y) * (y' : G)⁻¹ = φ (vOf y) := by
        rw [(hspec y).2, hcommG]
        group
      have hφeq : φ (permVec (ρ y' : Equiv.Perm (Fin 5)) (vOf y)) = φ (vOf y) := by
        rw [← hact y' (vOf y) (hspec y).1, hfixy']
      have hvec : permVec (ρ y' : Equiv.Perm (Fin 5)) (vOf y) = vOf y :=
        hinj _ _ (isEvenVec_permVec (ρ y' : Equiv.Perm (Fin 5)) (hspec y).1)
          (hspec y).1 hφeq
      have hσeq : (ρ y' : Equiv.Perm (Fin 5)) = (σ : Equiv.Perm (Fin 5)) :=
        congrArg (fun z : ↥(alternatingGroup (Fin 5)) => (z : Equiv.Perm (Fin 5))) hy'σ
      simpa only [hσeq] using hvec
    have hcardF : Nat.card ↥(P ⊓ ρ.ker) ≤ Nat.card {v : Fin 5 → ZMod 2 //
        IsEvenVec v ∧ ∀ σ ∈ P.map ρ, permVec (σ : Equiv.Perm (Fin 5)) v = v} :=
      Nat.card_le_card_of_injective
        (fun y : ↥(P ⊓ ρ.ker) =>
          (⟨vOf y, (hspec y).1, hfixOf y⟩ : {v : Fin 5 → ZMod 2 //
            IsEvenVec v ∧ ∀ σ ∈ P.map ρ, permVec (σ : Equiv.Perm (Fin 5)) v = v}))
        (by
          intro y y' hyy'
          have hv : vOf y = vOf y' := congrArg Subtype.val hyy'
          have hφ : φ (vOf y) = φ (vOf y') := by rw [hv]
          have hG : (y.1 : G) = (y'.1 : G) := by
            rw [← (hspec y).2, ← (hspec y').2, hφ]
          exact Subtype.ext (Subtype.ext hG))
    have hle8 : Nat.card P ≤ 8 := by
      rw [← hcardP]
      calc Nat.card ↥(P ⊓ ρ.ker) * Nat.card (P.map ρ)
          ≤ Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧
              ∀ σ ∈ P.map ρ, permVec (σ : Equiv.Perm (Fin 5)) v = v} *
              Nat.card (P.map ρ) := Nat.mul_le_mul hcardF le_rfl
        _ = Nat.card (P.map ρ) * Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧
              ∀ σ ∈ P.map ρ, permVec (σ : Equiv.Perm (Fin 5)) v = v} := Nat.mul_comm _ _
        _ ≤ 8 := sec12A5_fix_le (P.map ρ) hQea hQ
    exact ⟨by omega, fun h16 => by exfalso; omega⟩

end CFSG.OddStandard.SmallF3.Omega
