module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011CoreG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011K1

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec1011_autIn_CMt (t : G) (S L : Subgroup G) :
    autIn (secCMt t S L) (secA t S L) =
      secMstar t S L ⊓ MulAction.stabilizer (MulAut ↥(secA t S L)) (sec1011_tA t S L) := by
  ext α
  rw [Subgroup.mem_inf]
  unfold secCMt secMstar
  have hS : ({t} : Set G) ⊆ (secA t S L : Set G) := by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact sec1011_t_mem_A t S L
  rw [sec1011_mem_autIn_inf_centralizer (H := secM t S L) (Y := secA t S L) hS,
    MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨hα, hfix⟩
    exact ⟨hα, hfix (sec1011_tA t S L) (by simp [sec1011_tA])⟩
  · rintro ⟨hα, hfix⟩
    refine ⟨hα, fun y hy => ?_⟩
    have hyt : y = sec1011_tA t S L := Subtype.ext (Set.mem_singleton_iff.mp hy)
    rw [hyt]
    exact hfix

theorem sec1011_autIn_CMB (t : G) (S L : Subgroup G) :
    autIn (secCMB t S L) (secA t S L) =
      sec1011_KB (sec1011_BA t S L) (secMstar t S L) := by
  ext α
  unfold secCMB secMstar
  rw [sec1011_mem_autIn_inf_centralizer (H := secM t S L) (Y := secA t S L)
    (sec1011_B_le_A t S L)]
  constructor
  · rintro ⟨hα, hfix⟩
    exact ⟨hα, fun b hb => hfix b hb⟩
  · rintro ⟨hα, hfix⟩
    exact ⟨hα, fun y hy => hfix y hy⟩

theorem sec1011_conjClassIn_M (t : G) (S L : Subgroup G) :
    conjClassIn (secM t S L) t =
      Subtype.val '' sec1011_orb (secMstar t S L) (sec1011_tA t S L) := by
  ext y
  have h : y ∈ conjClassIn (secM t S L) ((sec1011_tA t S L : ↥(secA t S L)) : G) ↔
      ∃ α ∈ autIn (secM t S L) (secA t S L), y = (((α (sec1011_tA t S L)) : ↥(secA t S L)) : G) :=
    sec1011_mem_conjClassIn_iff (le_refl _)
  show y ∈ conjClassIn (secM t S L) ((sec1011_tA t S L : ↥(secA t S L)) : G) ↔ _
  rw [h]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α (sec1011_tA t S L), ⟨α, hα, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨α, hα, rfl⟩

theorem sec1011_iso_of_107b {t : G} {S L : Subgroup G}
    (h107b : Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5))) :
    Nonempty (↥(secMstar t S L ⊓ MulAction.stabilizer (MulAut ↥(secA t S L))
        (sec1011_tA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(secMstar t S L ⊓ MulAction.stabilizer (MulAut ↥(secA t S L))
        (sec1011_tA t S L)) ≃* Equiv.Perm (Fin 5)) := by
  rw [← sec1011_autIn_CMt]
  exact h107b

end CFSG.OddStandard.SmallF3.Omega
