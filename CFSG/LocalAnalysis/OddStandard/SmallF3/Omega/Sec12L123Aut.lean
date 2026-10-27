module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123Act

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec123_ker_cent (F : Sec12Frame t L S) (hS : IsSylow2Of S (centralizer ({t} : Set G)))
    (htS : t ∈ S) {X : Subgroup G} (hXYc : X ≤ (secM t S L ⊓ L) ⊔ S)
    (hXA : X ⊓ secA t S L = ⊥) : X ⊓ centralizer (secA t S L : Set G) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
  have hcent : ∀ b ∈ secB S L, x * b = b * x := by
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.mp hxC) b (Subgroup.mem_sup_left hb)).symm
  exact Subgroup.mem_bot.mpr (sec122_ker F hS htS hXYc hXA hxX hcent)

theorem sec123_autIn_eq (F : Sec12Frame t L S) (hS : IsSylow2Of S (centralizer ({t} : Set G)))
    (htS : t ∈ S) {X : Subgroup G} (hXA : X ⊓ secA t S L = ⊥)
    (hXsup : X ⊔ secA t S L = (secM t S L ⊓ L) ⊔ S)
    (hX60 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    (hlast : ∀ g ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G),
      ∃ σ : Equiv.Perm (Fin 5), ∀ v, IsEvenVec v → g * φ v * g⁻¹ = φ (permVec σ v)) :
    autIn X (secA t S L) = autIn (secCMt t S L) (secA t S L) := by
  have hSc : S ≤ centralizer ({t} : Set G) := hS.1
  have hXYc : X ≤ (secM t S L ⊓ L) ⊔ S := le_sup_left.trans hXsup.le
  have hYcC : (secM t S L ⊓ L) ⊔ S ≤ secCMt t S L :=
    le_inf (sec122_Yc_le_M F) (sec122_Yc_le_cent F hSc)
  have hXC : X ≤ secCMt t S L := hXYc.trans hYcC
  have hXM : X ≤ secM t S L := hXC.trans inf_le_left
  refine le_antisymm ?_ ?_
  · intro ρ hρ
    rw [autIn] at hρ ⊢
    rcases Subgroup.mem_map.mp hρ with ⟨n, hn, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨n, Subgroup.mem_subgroupOf.mpr (hXC (Subgroup.mem_subgroupOf.mp hn)), rfl⟩
  · intro ρ hρ
    rw [autIn] at hρ ⊢
    rcases Subgroup.mem_map.mp hρ with ⟨n, hn, hρn⟩
    have hnC : (n : G) ∈ secCMt t S L := Subgroup.mem_subgroupOf.mp hn
    have hncent : (n : G) ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hnC).2
    obtain ⟨σ, hσalt, hσ⟩ :=
      sec123_Cmt_act F hS htS hXA hXsup hX60 hperm hlast hnC
    have hφB : ∀ v, IsEvenVec v → φ v ∈ secB S L := by
      intro v hv
      exact (hperm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
    obtain ⟨y, hy, hyσ⟩ := hperm.2.2.2.2 σ hσalt
    obtain ⟨x, hxX, hxσ⟩ := sec122_surj F hXsup hy hyσ hφB
    have hxB : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = (n : G) * φ v * (n : G)⁻¹ := by
      intro v hv
      exact (hxσ v hv).trans (hσ v hv).symm
    let z : G := (n : G)⁻¹ * x
    have hzB : ∀ b ∈ secB S L, z * b = b * z := by
      intro b hb
      obtain ⟨v, hv, hvb⟩ := (hperm.2.2.1 b).mp hb
      have hxb : x * b * x⁻¹ = (n : G) * b * (n : G)⁻¹ := by
        rw [← hvb]; exact hxB v hv
      have hzconj : z * b * z⁻¹ = b := by
        have h1 : z * b * z⁻¹ = (n : G)⁻¹ * (x * b * x⁻¹) * (n : G) := by
          dsimp only [z]; group
        rw [h1, hxb]; group
      calc z * b = (z * b * z⁻¹) * z := by group
        _ = b * z := by rw [hzconj]
    have hzt : z * t = t * z := by
      have hnct : Commute (n : G) t :=
        ((Subgroup.mem_centralizer_iff.mp hncent) t (Set.mem_singleton t)).symm
      have hxct : Commute x t :=
        ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hXC hxX)).2) t
          (Set.mem_singleton t)).symm
      have hzct : Commute z t := by
        dsimp only [z]
        exact hnct.inv_left.mul_left hxct
      exact hzct.eq
    have hzcent : z ∈ centralizer (secA t S L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rcases (sec12E_mem_A F).mp ha with haB | ⟨b, hb, rfl⟩
      · exact (hzB a haB).symm
      · calc (t * b) * z = t * (b * z) := by group
          _ = t * (z * b) := by rw [← hzB b hb]
          _ = (t * z) * b := by group
          _ = (z * t) * b := by rw [← hzt]
          _ = z * (t * b) := by group
    have hconj : ∀ a ∈ secA t S L, x * a * x⁻¹ = (n : G) * a * (n : G)⁻¹ := by
      intro a ha
      have haz : a * z = z * a := (Subgroup.mem_centralizer_iff.mp hzcent) a ha
      calc x * a * x⁻¹ = (n : G) * (z * a) * x⁻¹ := by dsimp only [z]; group
        _ = (n : G) * (a * z) * x⁻¹ := by rw [← haz]
        _ = (n : G) * a * (n : G)⁻¹ := by dsimp only [z]; group
    have hxnorm : x ∈ normalizer (secA t S L : Set G) := by
      simpa only [secM] using hXM hxX
    refine Subgroup.mem_map.mpr ⟨⟨x, hxnorm⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hxX
    · refine Eq.trans ?_ hρn
      refine MulEquiv.ext fun a => Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hconj a a.2

end CFSG.OddStandard.SmallF3.Omega
