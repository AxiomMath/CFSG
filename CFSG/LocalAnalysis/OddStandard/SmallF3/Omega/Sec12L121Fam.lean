module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Lift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

theorem sec121_exists_family (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5))) :
    ∃ u : Fin 5 → G, (∀ i, u i ∈ E) ∧ (∀ i, sec12f t (u i) = φ (wvec i)) ∧
      ∀ y ∈ secM t S L ⊓ L, ∀ σ : Equiv.Perm (Fin 5),
        (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v)) →
          ∀ i, (u (σ i))⁻¹ * (y * u i * y⁻¹) ∈ secB S L := by
  have h0B : φ (wvec 0) ∈ secB S L :=
    (hperm.2.2.1 (φ (wvec 0))).2 ⟨wvec 0, wvec_even 0, rfl⟩
  obtain ⟨u₀, hu₀E, hu₀f⟩ := sec120_f_surj_E F hE h0B
  choose σ hσmem hσ0 using fun i : Fin 5 => exists_alt_apply 0 i
  choose g hgmem hgact using fun i : Fin 5 => hperm.2.2.2.2 (σ i) (hσmem i)
  have hg0 : ∀ i, g i * φ (wvec 0) * (g i)⁻¹ = φ (wvec i) := by
    intro i
    rw [hgact i (wvec 0) (wvec_even 0), permVec_wvec, hσ0 i]
  have hgt : ∀ i, g i * t = t * g i := fun i =>
    (Subgroup.mem_centralizer_iff.mp F.htC) (g i) (hgmem i).2
  let u : Fin 5 → G := fun i => g i * u₀ * (g i)⁻¹
  have huE : ∀ i, u i ∈ E := by
    intro i
    change g i * u₀ * (g i)⁻¹ ∈ E
    exact (Subgroup.mem_normalizer_iff.mp
      (sec12E_sylow_normal F hE (hgmem i).1) u₀).1 hu₀E
  have huf : ∀ i, sec12f t (u i) = φ (wvec i) := by
    intro i
    change sec12f t (g i * u₀ * (g i)⁻¹) = φ (wvec i)
    rw [sec12E_f_conj (hgt i), hu₀f, hg0 i]
  refine ⟨u, huE, huf, ?_⟩
  intro y hy σ' hσ' i
  have hyt : y * t = t * y := (Subgroup.mem_centralizer_iff.mp F.htC) y hy.2
  let j : Fin 5 := σ' i
  let s : G := (g j)⁻¹ * y * g i
  have hsY : s ∈ secM t S L ⊓ L := by
    change (g j)⁻¹ * y * g i ∈ secM t S L ⊓ L
    exact (secM t S L ⊓ L).mul_mem
      ((secM t S L ⊓ L).mul_mem ((secM t S L ⊓ L).inv_mem (hgmem j)) hy) (hgmem i)
  have hfix_s : s * φ (wvec 0) * s⁻¹ = φ (wvec 0) := by
    have h2 : y * φ (wvec i) * y⁻¹ = φ (wvec j) := by
      have hh := hσ' (wvec i) (wvec_even i)
      rw [permVec_wvec] at hh
      exact hh
    have h3 : (g j)⁻¹ * φ (wvec j) * g j = φ (wvec 0) := by
      have hh := hg0 j
      rw [← hh]
      group
    change ((g j)⁻¹ * y * g i) * φ (wvec 0) * ((g j)⁻¹ * y * g i)⁻¹ = φ (wvec 0)
    calc ((g j)⁻¹ * y * g i) * φ (wvec 0) * ((g j)⁻¹ * y * g i)⁻¹
        = (g j)⁻¹ * (y * (g i * φ (wvec 0) * (g i)⁻¹) * y⁻¹) * g j := by group
      _ = (g j)⁻¹ * (y * φ (wvec i) * y⁻¹) * g j := by rw [hg0 i]
      _ = (g j)⁻¹ * φ (wvec j) * g j := by rw [h2]
      _ = φ (wvec 0) := h3
  have hcR : u₀⁻¹ * (s * u₀ * s⁻¹) ∈ secB S L :=
    sec121_fixed_lift F hE hperm (i := 0) hu₀E hu₀f hsY hfix_s
  let c : G := u₀⁻¹ * (s * u₀ * s⁻¹)
  have hcB : c ∈ secB S L := hcR
  have hsc : s * u₀ * s⁻¹ = u₀ * c := by
    change s * u₀ * s⁻¹ = u₀ * (u₀⁻¹ * (s * u₀ * s⁻¹))
    group
  have hyg : y * g i = g j * s := by
    change y * g i = g j * ((g j)⁻¹ * y * g i)
    group
  have hfinal : y * (g i * u₀ * (g i)⁻¹) * y⁻¹
      = (g j * u₀ * (g j)⁻¹) * (g j * c * (g j)⁻¹) := by
    calc y * (g i * u₀ * (g i)⁻¹) * y⁻¹
        = (y * g i) * u₀ * (y * g i)⁻¹ := by group
      _ = (g j * s) * u₀ * (g j * s)⁻¹ := by rw [hyg]
      _ = g j * (s * u₀ * s⁻¹) * (g j)⁻¹ := by group
      _ = g j * (u₀ * c) * (g j)⁻¹ := by rw [hsc]
      _ = (g j * u₀ * (g j)⁻¹) * (g j * c * (g j)⁻¹) := by group
  have hconj : (u (σ' i))⁻¹ * (y * u i * y⁻¹) = g j * c * (g j)⁻¹ := by
    show (g j * u₀ * (g j)⁻¹)⁻¹ * (y * (g i * u₀ * (g i)⁻¹) * y⁻¹)
      = g j * c * (g j)⁻¹
    rw [hfinal]
    group
  rw [hconj]
  exact F.normB (g j) (hgmem j).1 c hcB

end CFSG.OddStandard.SmallF3.Omega
