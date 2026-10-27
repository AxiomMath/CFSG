module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Br0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Alt2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {φ : (Fin 5 → ZMod 2) → G}

theorem sec1011_conjClassIn_ML (hs : Sec1011Setup t L S z φ) :
    conjClassIn (secM t S L ⊓ L) (t * z) =
      {y | ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ y = t * φ v} := by
  obtain ⟨v0, hv0, hw0, hzφ⟩ := hs.hz
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hhL : h ∈ L := (Subgroup.mem_inf.mp hh).2
    have hhN : h ∈ L ⊓ normalizer (secB S L : Set G) := by
      rw [← hs.hML]
      exact hh
    obtain ⟨σ, -, hσ⟩ := hs.hperm.2.2.2.1 h hhN
    have hct : h * t * h⁻¹ = t := by
      rw [Subgroup.mem_centralizer_iff.mp hs.htC h hhL]
      group
    refine ⟨permVec σ v0, isEvenVec_permVec σ hv0, ?_, ?_⟩
    · rw [vecWeight_permVec]
      exact hw0
    · rw [← hσ v0 hv0, ← hzφ]
      calc h * (t * z) * h⁻¹ = (h * t * h⁻¹) * (h * z * h⁻¹) := by group
        _ = t * (h * z * h⁻¹) := by rw [hct]
  · rintro ⟨v, hv, hw, rfl⟩
    obtain ⟨σ, hσA, hσv⟩ := exists_alt_permVec_weight_four v0 v hw0 hw
    obtain ⟨h, hhN, hh⟩ := hs.hperm.2.2.2.2 σ hσA
    have hhM : h ∈ secM t S L ⊓ L := by
      rw [hs.hML]
      exact hhN
    have hhL : h ∈ L := (Subgroup.mem_inf.mp hhN).1
    have hct : h * t * h⁻¹ = t := by
      rw [Subgroup.mem_centralizer_iff.mp hs.htC h hhL]
      group
    refine ⟨h, hhM, ?_⟩
    rw [← hσv, ← hh v0 hv0, hzφ]
    calc t * (h * φ v0 * h⁻¹) = (h * t * h⁻¹) * (h * φ v0 * h⁻¹) := by rw [hct]
      _ = h * (t * φ v0) * h⁻¹ := by group

theorem sec1011_conjClassIn_M_six (hs : Sec1011Setup t L S z φ)
    (h6 : sec1011_orb (secMstar t S L) (sec1011_tA t S L) =
      {a | a = sec1011_tA t S L ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧
        a = sec1011_tA t S L * sec1011_phiA t S L φ v}) :
    conjClassIn (secM t S L) t = {t} ∪ conjClassIn (secM t S L ⊓ L) (t * z) := by
  rw [sec1011_conjClassIn_M, h6, sec1011_conjClassIn_ML hs]
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl | ⟨v, hv, hw, rfl⟩, rfl⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨v, hv, hw, ?_⟩
      show t * ((sec1011_phiA t S L φ v : ↥(secA t S L)) : G) = t * φ v
      rw [sec1011_phiA_coe hs hv]
  · rintro (hy | ⟨v, hv, hw, hy⟩)
    · exact ⟨sec1011_tA t S L, Or.inl rfl, hy.symm⟩
    · refine ⟨sec1011_tA t S L * sec1011_phiA t S L φ v, Or.inr ⟨v, hv, hw, rfl⟩, ?_⟩
      show t * ((sec1011_phiA t S L φ v : ↥(secA t S L)) : G) = y
      rw [sec1011_phiA_coe hs hv, hy]

theorem sec1011_isPermMod6_of {Alt : Subgroup (Equiv.Perm (Fin 6))}
    {φ6 : (Fin 6 → ZMod 2) → ↥(secA t S L)}
    (hom : ∀ v w, φ6 (v + w) = φ6 v * φ6 w)
    (hker : ∀ v, φ6 v = 1 ↔ v = 0 ∨ v = sec1011_one6)
    (hsurj : ∀ a, ∃ v, φ6 v = a)
    (hK : ∀ α ∈ secMstar t S L, ∃ σ ∈ Alt, ∀ v, α (φ6 v) = φ6 (permVec σ v))
    (hσ : ∀ σ ∈ Alt, ∃ α ∈ secMstar t S L, ∀ v, α (φ6 v) = φ6 (permVec σ v)) :
    IsPermMod6 (secA t S L) (secM t S L) Alt := by
  refine ⟨fun v => ((φ6 v : ↥(secA t S L)) : G), ?_⟩
  refine ⟨bot_le, ?_, le_refl _, ?_, fun v _ => (φ6 v).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    exact Subgroup.normal_bot
  · intro h _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  · intro v w _ _
    rw [Subgroup.mem_bot]
    show (((φ6 v : ↥(secA t S L)) : G) * ((φ6 w : ↥(secA t S L)) : G))⁻¹ *
      ((φ6 (v + w) : ↥(secA t S L)) : G) = 1
    rw [hom v w]
    simp
  · intro v _
    rw [Subgroup.mem_bot]
    show ((φ6 v : ↥(secA t S L)) : G) = 1 ↔ v ∈ ({0, fun _ => 1} : Set (Fin 6 → ZMod 2))
    rw [OneMemClass.coe_eq_one, hker v]
    exact Iff.rfl
  · intro x hx
    obtain ⟨v, hv⟩ := hsurj ⟨x, hx⟩
    refine ⟨v, trivial, ?_⟩
    rw [Subgroup.mem_bot]
    have h1 := congrArg Subtype.val hv
    simp only at h1
    simp [h1]
  · intro h hh
    have hhN : h ∈ normalizer (secA t S L : Set G) := hh
    obtain ⟨σ, hσA, hact⟩ := hK _ (sec1011_conjAut_mem hh hhN)
    refine ⟨σ, hσA, fun v _ => ?_⟩
    have h1 := congrArg Subtype.val (hact v)
    rw [sec1011_conjAut_apply] at h1
    rw [Subgroup.mem_bot]
    show (h * ((φ6 v : ↥(secA t S L)) : G) * h⁻¹)⁻¹ *
      ((φ6 (permVec σ v) : ↥(secA t S L)) : G) = 1
    rw [h1]
    group
  · intro σ hσA
    obtain ⟨α, hα, hact⟩ := hσ σ hσA
    obtain ⟨m, hmM, hmN, rfl⟩ := sec1011_exists_conjAut hα
    refine ⟨m, hmM, fun v _ => ?_⟩
    have h1 := congrArg Subtype.val (hact v)
    rw [sec1011_conjAut_apply] at h1
    rw [Subgroup.mem_bot]
    show (m * ((φ6 v : ↥(secA t S L)) : G) * m⁻¹)⁻¹ *
      ((φ6 (permVec σ v) : ↥(secA t S L)) : G) = 1
    rw [h1]
    group

theorem sec1011_alt2_of_setup [Finite G] (hs : Sec1011Setup t L S z φ)
    (h6 : sec1011_orb (secMstar t S L) (sec1011_tA t S L) =
      {a | a = sec1011_tA t S L ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧
        a = sec1011_tA t S L * sec1011_phiA t S L φ v})
    (h107b : Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5)))
    (hP2 : conjClassIn ⊤ t ∩ (secA t S L : Set G) ⊆ conjClassIn (secM t S L) t) :
    Sec1011Alt2 t S L z := by
  have hcore := sec1011_core_of_setup hs
  have hA2 : Sec1011A2 (sec1011_BA t S L) (sec1011_tA t S L) (secMstar t S L)
      (sec1011_phiA t S L φ) := ⟨hcore, h6, sec1011_iso_of_107b h107b⟩
  obtain ⟨Alt, hAlt, ⟨e⟩, φ6, hom, hker, hsurj, hK, hσ⟩ := sec1011_alt2_perm hA2
  refine ⟨?_, ?_, sec1011_conjClassIn_M_six hs h6, ?_, ?_⟩
  · rcases hAlt with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e.trans Subgroup.topEquiv⟩
  · apply Set.Subset.antisymm hP2
    rintro y ⟨m, hm, rfl⟩
    refine ⟨⟨m, Subgroup.mem_top m, rfl⟩, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (show m ∈ normalizer (secA t S L : Set G) from hm) t).mp
      (sec1011_t_mem_A t S L)
  · rw [sec1011_conjClassIn_M, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact sec1011_core_ncard_six hcore h6
  · rcases hAlt with rfl | rfl
    · exact Or.inl (sec1011_isPermMod6_of hom hker hsurj hK hσ)
    · exact Or.inr (sec1011_isPermMod6_of hom hker hsurj hK hσ)

end CFSG.OddStandard.SmallF3.Omega
