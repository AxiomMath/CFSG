module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2c2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Br2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {φ : (Fin 5 → ZMod 2) → G}

theorem sec1011_p2_of_setup [Finite G] (hB5 : Asc82FactB5) (hOut5 : Asc82FactOut5)
    (hpsp : IsPSp43 L) (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (h102 : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G))))
    (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hB16 : Nat.card (secB S L) = 2 ^ 4) (hs : Sec1011Setup t L S z φ)
    (h6 : sec1011_orb (secMstar t S L) (sec1011_tA t S L) =
      {a | a = sec1011_tA t S L ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧
        a = sec1011_tA t S L * sec1011_phiA t S L φ v})
    (h107b : Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5))) :
    conjClassIn ⊤ t ∩ (secA t S L : Set G) ⊆ conjClassIn (secM t S L) t := by
  rintro y ⟨⟨g, -, rfl⟩, hyA⟩
  have hyB : g * t * g⁻¹ ∈ secTB t S L := by
    have h := hs.htB g⁻¹ (by simpa using hyA)
    simpa using h
  obtain ⟨b, hb, hbeq⟩ := hyB
  obtain ⟨v, hv, rfl⟩ := (hs.hperm.2.2.1 b).1 hb
  rw [sec1011_conjClassIn_M_six hs h6]
  rcases even_weight_cases_five v hv with h0 | h2 | h4
  · left
    rw [Set.mem_singleton_iff, hbeq, h0, sec1011_phi_zero hs, mul_one]
  · exfalso
    obtain ⟨σ, hσ, hσv⟩ := sec1011_alt_weight_two v sec1011_w0 h2 sec1011_w0_weight
    obtain ⟨k, hk, hkact⟩ := hs.hperm.2.2.2.2 σ hσ
    have hkL : k ∈ L := (Subgroup.mem_inf.mp hk).1
    have hkt : k * t * k⁻¹ = t := by
      rw [Subgroup.mem_centralizer_iff.mp hs.htC k hkL]
      group
    have hk0 := hkact v hv
    rw [hσv] at hk0
    have hy0 : k * (g * t * g⁻¹) * k⁻¹ = t * φ sec1011_w0 := by
      rw [hbeq, ← hk0]
      calc k * (t * φ v) * k⁻¹ = (k * t * k⁻¹) * (k * φ v * k⁻¹) := by group
        _ = t * (k * φ v * k⁻¹) := by rw [hkt]
    have hh : (k * g)⁻¹ * (t * φ sec1011_w0) * ((k * g)⁻¹)⁻¹ = t := by
      rw [← hy0]
      group
    exact sec1011_p2_conj_false hB5 hOut5 hpsp hLC h102 hN hB16 hs h6 h107b hh
  · right
    rw [sec1011_conjClassIn_ML hs]
    exact ⟨v, hv, h4, hbeq⟩

end CFSG.OddStandard.SmallF3.Omega
