module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123Hom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123Sign
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123Alt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Yc

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec123_Cmt_act (F : Sec12Frame t L S) (hS : IsSylow2Of S (centralizer ({t} : Set G)))
    (htS : t ∈ S) {X : Subgroup G} (hXA : X ⊓ secA t S L = ⊥)
    (hXsup : X ⊔ secA t S L = (secM t S L ⊓ L) ⊔ S)
    (hX60 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    (hlast : ∀ g ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G),
      ∃ σ : Equiv.Perm (Fin 5), ∀ v, IsEvenVec v → g * φ v * g⁻¹ = φ (permVec σ v))
    {m : G} (hm : m ∈ secCMt t S L) :
    ∃ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEvenVec v → m * φ v * m⁻¹ = φ (permVec σ v) := by
  have hSc : S ≤ centralizer ({t} : Set G) := hS.1
  have hXYc : X ≤ (secM t S L ⊓ L) ⊔ S := by rw [← hXsup]; exact le_sup_left
  have hYcC : (secM t S L ⊓ L) ⊔ S ≤ secCMt t S L :=
    le_inf (sec122_Yc_le_M F) (sec122_Yc_le_cent F hSc)
  have hSC : S ≤ secCMt t S L := le_inf F.hSM hSc
  have hAC : secA t S L ≤ secCMt t S L := (sec122_A_le_Yc htS).trans hYcC
  have hφB : ∀ v, IsEvenVec v → φ v ∈ secB S L := fun v hv =>
    (hperm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
  have hmemNB : ∀ g ∈ secCMt t S L,
      g ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G) := fun g hg =>
    ⟨F.hCt hg.2, sec122_M_le_normalizer_B F hg.1⟩
  have hactC : ∀ x ∈ secCMt t S L, ∃ σ : Equiv.Perm (Fin 5),
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) :=
    fun x hx => hlast x (hmemNB x hx)
  obtain ⟨Θ, hΘ⟩ := sec123_exists_hom hperm.2.1 hactC
  have hker : ∀ x : ↥(secCMt t S L), (x : G) ∈ X → Θ x = 1 → x = 1 := by
    intro x hxX hΘx
    have hcent : ∀ b ∈ secB S L, (x : G) * b = b * (x : G) := by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := (hperm.2.2.1 b).mp hb
      have h := hΘ x v hv
      rw [hΘx, permVec_one] at h
      calc (x : G) * φ v = ((x : G) * φ v * (x : G)⁻¹) * (x : G) := by group
        _ = φ v * (x : G) := by rw [h]
    exact Subtype.ext (by simpa using sec122_ker F hS htS hXYc hXA hxX hcent)
  have hsurj : ∀ σ ∈ alternatingGroup (Fin 5),
      ∃ x : ↥(secCMt t S L), (x : G) ∈ X ∧ Θ x = σ := by
    intro σ hσ
    obtain ⟨y, hy, hyσ⟩ := hperm.2.2.2.2 σ hσ
    obtain ⟨x, hxX, hxσ⟩ := sec122_surj F hXsup hy hyσ hφB
    exact ⟨⟨x, hYcC (hXYc hxX)⟩, hxX,
      sec123_perm_unique hperm.2.1 (hΘ ⟨x, hYcC (hXYc hxX)⟩) hxσ⟩
  have himage : ∀ x : ↥(secCMt t S L), (x : G) ∈ X → Θ x ∈ alternatingGroup (Fin 5) :=
    sec123_image_alt (H := secCMt t S L) (X := X) (hXYc.trans hYcC) Θ hker hsurj hX60
  have hS_act : ∀ s : ↥(secCMt t S L), (s : G) ∈ S → Θ s ∈ alternatingGroup (Fin 5) := by
    intro s hsS
    have hsXA : (s : G) ∈ X ⊔ secA t S L := by
      have hSXA : S ≤ X ⊔ secA t S L := by rw [hXsup]; exact le_sup_right
      exact hSXA hsS
    have hXM : X ≤ secM t S L := hXYc.trans (sec122_Yc_le_M F)
    have hs' : (s : G) ∈ (X : Set G) * (secA t S L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right X (secA t S L) hXM]
      exact hsXA
    obtain ⟨x, hxX, a, haA, hxa⟩ := Set.mem_mul.mp hs'
    have hxC : x ∈ secCMt t S L := hYcC (hXYc hxX)
    have haC : a ∈ secCMt t S L := hAC haA
    have ha_act : ∀ v, IsEvenVec v →
        a * φ v * a⁻¹ = φ (permVec (1 : Equiv.Perm (Fin 5)) v) := by
      intro v hv
      rw [permVec_one]
      have hcomm := sec12E_A_comm F haA (Subgroup.mem_sup_left (T := zpowers t) (hφB v hv))
      calc a * φ v * a⁻¹ = (φ v * a) * a⁻¹ := by rw [hcomm]
        _ = φ v := by group
    have hΘa : Θ ⟨a, haC⟩ = 1 :=
      sec123_perm_unique hperm.2.1 (hΘ ⟨a, haC⟩) ha_act
    have hs_eq : (s : ↥(secCMt t S L)) = ⟨x, hxC⟩ * ⟨a, haC⟩ := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using hxa.symm
    rw [hs_eq, map_mul, hΘa, mul_one]
    exact himage ⟨x, hxC⟩ hxX
  have hCcent : secCMt t S L ≤ centralizer ({t} : Set G) := inf_le_right
  have hodd : ¬ 2 ∣ S.relIndex (secCMt t S L) := by
    intro hdvd
    have hrel := Subgroup.relIndex_mul_relIndex S (secCMt t S L) (centralizer ({t} : Set G))
      hSC hCcent
    have hdvd' : 2 ∣ S.relIndex (secCMt t S L) *
        (secCMt t S L).relIndex (centralizer ({t} : Set G)) := hdvd.mul_right _
    rw [hrel] at hdvd'
    exact hS.2.2 hdvd'
  exact ⟨Θ ⟨m, hm⟩, sec123_range_alt hSC hodd Θ hS_act ⟨m, hm⟩, hΘ ⟨m, hm⟩⟩

end CFSG.OddStandard.SmallF3.Omega
