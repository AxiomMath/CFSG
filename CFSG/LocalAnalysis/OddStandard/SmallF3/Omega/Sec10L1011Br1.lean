module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Br0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011K2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {φ : (Fin 5 → ZMod 2) → G}

theorem sec1011_alt1_of_setup [Finite G] (hs : Sec1011Setup t L S z φ)
    (hB : sec1011_orb (secMstar t S L) (sec1011_tA t S L) =
      {a | ∃ b ∈ sec1011_BA t S L, a = sec1011_tA t S L * b})
    (h107b : Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5))) :
    Sec1011Alt1 t S L := by
  have hcore := sec1011_core_of_setup hs
  have hA1 : Sec1011A1 (sec1011_BA t S L) (sec1011_tA t S L) (secMstar t S L)
      (sec1011_phiA t S L φ) := ⟨hcore, hB, sec1011_iso_of_107b h107b⟩
  obtain ⟨hK, hKB, hel, hreg⟩ := sec1011_alt1_core hA1
  have hTB : secTB t S L = conjClassIn (secM t S L) t := by
    rw [sec1011_conjClassIn_M, hB]
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨sec1011_tA t S L * ⟨b, sec1011_B_le_A t S L hb⟩,
        ⟨⟨b, sec1011_B_le_A t S L hb⟩, hb, rfl⟩, rfl⟩
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨(b : G), hb, rfl⟩
  refine ⟨?_, hTB, ?_, ?_, ?_, ?_⟩
  ·
    apply Set.Subset.antisymm
    · rintro x ⟨⟨g, -, rfl⟩, hxA⟩
      have h1 : g⁻¹⁻¹ * t * g⁻¹ ∈ secA t S L := by
        rw [inv_inv]
        exact hxA
      have h2 := hs.htB g⁻¹ h1
      rwa [inv_inv] at h2
    · intro x hx
      refine ⟨?_, ?_⟩
      · rw [hTB] at hx
        obtain ⟨m, hm, rfl⟩ := hx
        exact ⟨m, Subgroup.mem_top m, rfl⟩
      · obtain ⟨b, hb, rfl⟩ := hx
        exact (secA t S L).mul_mem (sec1011_t_mem_A t S L) (sec1011_B_le_A t S L hb)
  · rw [sec1011_autIn_CMB, sec1011_autIn_CMt]
    exact hK
  · rw [sec1011_autIn_CMB]
    exact hKB
  · rw [sec1011_autIn_CMB]
    exact hel
  · intro x y hx hy
    rw [sec1011_autIn_CMB]
    obtain ⟨bx, hbx, hxeq⟩ := hx
    obtain ⟨by', hby, hyeq⟩ := hy
    refine hreg x y ⟨⟨bx, sec1011_B_le_A t S L hbx⟩, hbx, Subtype.ext hxeq⟩
      ⟨⟨by', sec1011_B_le_A t S L hby⟩, hby, Subtype.ext hyeq⟩

end CFSG.OddStandard.SmallF3.Omega
