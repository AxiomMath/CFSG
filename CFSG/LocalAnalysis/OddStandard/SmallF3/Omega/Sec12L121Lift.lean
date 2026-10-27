module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

private lemma sec121_tB_mul (F : Sec12Frame t L S) {b b' : G} (hb : b ∈ secB S L) :
    (t * b) * (t * b') = b * b' := by
  calc (t * b) * (t * b')
      = (b * t) * (t * b') := by rw [sec12E_t_comm_B F hb]
    _ = b * (t * t) * b' := by group
    _ = b * b' := by rw [sec12E_t_sq F]; group

private lemma sec121_tB_prod (F : Sec12Frame t L S) {b₀ b₁ b₂ : G}
    (h₀ : b₀ ∈ secB S L) (h₁ : b₁ ∈ secB S L) (h₂ : b₂ ∈ secB S L) :
    (t * b₀) * (t * b₁) * (t * b₂) = t * (b₀ * b₁ * b₂) := by
  have h₀c : Commute t b₀ := sec12E_t_comm_B F h₀
  have h₁c : Commute t b₁ := sec12E_t_comm_B F h₁
  have h₂c : Commute t b₂ := sec12E_t_comm_B F h₂
  have ht : Commute t (b₀ * b₁ * b₂) := (h₀c.mul_right h₁c).mul_right h₂c
  calc (t * b₀) * (t * b₁) * (t * b₂)
      = (b₀ * b₁) * (t * b₂) := by rw [sec121_tB_mul F h₀]
    _ = (b₀ * b₁) * (b₂ * t) := by rw [sec12E_t_comm_B F h₂]
    _ = b₀ * b₁ * b₂ * t := by group
    _ = t * (b₀ * b₁ * b₂) := by rw [ht.eq]

private lemma sec121_pow_three_mem_B (F : Sec12Frame t L S) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {ρ : Equiv.Perm (Fin 5)} {y₀ : G} (hy₀ : y₀ ∈ secM t S L ⊓ L)
    (hy₀act : ∀ v, IsEvenVec v → y₀ * φ v * y₀⁻¹ = φ (permVec ρ v)) (hρc : ρ ^ 3 = 1) :
    y₀ ^ 3 ∈ secB S L := by
  have himg := hperm.2.2.1
  have hfix : ∀ v, IsEvenVec v → y₀ ^ 3 * φ v * (y₀ ^ 3)⁻¹ = φ v := by
    intro v hv
    have hv₁ : IsEvenVec (permVec ρ v) := isEvenVec_permVec ρ hv
    have hv₂ : IsEvenVec (permVec ρ (permVec ρ v)) := isEvenVec_permVec ρ hv₁
    calc y₀ ^ 3 * φ v * (y₀ ^ 3)⁻¹
        = y₀ * (y₀ * (y₀ * φ v * y₀⁻¹) * y₀⁻¹) * y₀⁻¹ := by
          rw [← inv_pow y₀ 3, pow_three' y₀, pow_three' (y₀⁻¹)]
          group
      _ = y₀ * (y₀ * φ (permVec ρ v) * y₀⁻¹) * y₀⁻¹ := by rw [hy₀act v hv]
      _ = y₀ * φ (permVec ρ (permVec ρ v)) * y₀⁻¹ := by rw [hy₀act (permVec ρ v) hv₁]
      _ = φ (permVec ρ (permVec ρ (permVec ρ v))) := hy₀act _ hv₂
      _ = φ v := by rw [permVec_cube hρc]
  have hC : y₀ ^ 3 ∈ centralizer (secB S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨v, hv, rfl⟩ := (himg b).1 hb
    have h := hfix v hv
    calc φ v * y₀ ^ 3 = (y₀ ^ 3 * φ v * (y₀ ^ 3)⁻¹) * y₀ ^ 3 := by rw [h]
      _ = y₀ ^ 3 * φ v := by group
  have hmem : y₀ ^ 3 ∈ centralizer (secB S L : Set G) ⊓ L :=
    ⟨hC, ((secM t S L ⊓ L).pow_mem hy₀ 3).2⟩
  rwa [F.bdata.2.2.1] at hmem

theorem sec121_cube_lift (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) {u y : G}
    (hu : u ∈ E) (hy : y ∈ secM t S L ⊓ L) (hy3 : y ^ 3 ∈ secB S L)
    (hf : sec12f t (y * u * y⁻¹) = sec12f t u) : u⁻¹ * (y * u * y⁻¹) ∈ secB S L := by
  have hyM : y ∈ secM t S L := hy.1
  have hyt : y * t * y⁻¹ = t := by
    rw [show y * t = t * y from (Subgroup.mem_centralizer_iff.mp F.htC) y hy.2]
    group
  have huy : y * u * y⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (sec12E_sylow_normal F hE hyM) u).1 hu
  have hdA : u⁻¹ * (y * u * y⁻¹) ∈ secA t S L :=
    sec120_inv_mul_mem_A F hE hu huy hf.symm
  rcases (sec12E_mem_A F).mp hdA with hdB | ⟨b₀, hb₀, hd_eq⟩
  · exact hdB
  · exfalso
    let b₁ : G := y * b₀ * y⁻¹
    let b₂ : G := y * b₁ * y⁻¹
    have hb₁ : b₁ ∈ secB S L := by
      change y * b₀ * y⁻¹ ∈ secB S L
      exact F.normB y hyM b₀ hb₀
    have hb₂ : b₂ ∈ secB S L := by
      change y * b₁ * y⁻¹ ∈ secB S L
      exact F.normB y hyM b₁ hb₁
    have hconj1 : y * (t * b₀) * y⁻¹ = t * b₁ := by
      change y * (t * b₀) * y⁻¹ = t * (y * b₀ * y⁻¹)
      calc y * (t * b₀) * y⁻¹ = (y * t * y⁻¹) * (y * b₀ * y⁻¹) := by group
        _ = t * (y * b₀ * y⁻¹) := by rw [hyt]
    have hconj2 : y * (t * b₁) * y⁻¹ = t * b₂ := by
      change y * (t * b₁) * y⁻¹ = t * (y * b₁ * y⁻¹)
      calc y * (t * b₁) * y⁻¹ = (y * t * y⁻¹) * (y * b₁ * y⁻¹) := by group
        _ = t * (y * b₁ * y⁻¹) := by rw [hyt]
    have htele : (u⁻¹ * (y * u * y⁻¹)) * (y * (u⁻¹ * (y * u * y⁻¹)) * y⁻¹) *
        (y * (y * (u⁻¹ * (y * u * y⁻¹)) * y⁻¹) * y⁻¹)
        = u⁻¹ * (y ^ 3 * u * (y ^ 3)⁻¹) := by
      rw [← inv_pow y 3, pow_three' y, pow_three' (y⁻¹)]
      group
    have hy3u : y ^ 3 * u * (y ^ 3)⁻¹ = u := by
      have huC : u ∈ centralizer (secB S L : Set G) := (Subgroup.mem_inf.mp (hE.1 hu)).2
      have hcomm : y ^ 3 * u = u * y ^ 3 :=
        (Subgroup.mem_centralizer_iff.mp huC) (y ^ 3) hy3
      rw [hcomm]
      group
    have htele1 : (t * b₀) * (t * b₁) * (t * b₂) = 1 := by
      have h := htele
      rw [hd_eq, hconj1, hconj2] at h
      rw [hy3u, inv_mul_cancel] at h
      exact h
    have ht1 : t * (b₀ * b₁ * b₂) = 1 := by
      rw [← sec121_tB_prod F hb₀ hb₁ hb₂]
      exact htele1
    have htB : t ∈ secB S L := by
      rw [eq_inv_of_mul_eq_one_left ht1]
      exact (secB S L).inv_mem ((secB S L).mul_mem ((secB S L).mul_mem hb₀ hb₁) hb₂)
    exact sec120_t_not_mem_L F (F.bdata.1 htB)

theorem sec121_stab_decomp (F : Sec12Frame t L S) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {i : Fin 5} {y : G} (hy : y ∈ secM t S L ⊓ L) (hfix : y * φ (wvec i) * y⁻¹ = φ (wvec i)) :
    ∃ y₁ ∈ secM t S L ⊓ L, ∃ y₂ ∈ secM t S L ⊓ L, ∃ b ∈ secB S L,
      y = b * y₁ * y₂ ∧ y₁ ^ 3 ∈ secB S L ∧ y₂ ^ 3 ∈ secB S L ∧
        y₁ * φ (wvec i) * y₁⁻¹ = φ (wvec i) ∧ y₂ * φ (wvec i) * y₂⁻¹ = φ (wvec i) := by
  have hinj := hperm.2.1
  have himg := hperm.2.2.1
  have hactH := hperm.2.2.2.1
  have hactAlt := hperm.2.2.2.2
  obtain ⟨σ, hσ, hσact⟩ := hactH y hy
  have hσi : σ i = i := by
    have h1 : φ (wvec (σ i)) = φ (wvec i) := by
      have hh := hσact (wvec i) (wvec_even i)
      rw [permVec_wvec] at hh
      rw [hfix] at hh
      exact hh.symm
    exact wvec_injective (hinj (wvec (σ i)) (wvec i) (wvec_even (σ i)) (wvec_even i) h1)
  obtain ⟨ρ₁, hρ₁, ρ₂, hρ₂, hρ₁i, hρ₂i, hρ₁c, hρ₂c, hσ_eq⟩ := alt_stab_decomp i hσ hσi
  obtain ⟨y₁, hy₁, hy₁act⟩ := hactAlt ρ₁ hρ₁
  obtain ⟨y₂, hy₂, hy₂act⟩ := hactAlt ρ₂ hρ₂
  have hfix₁ : y₁ * φ (wvec i) * y₁⁻¹ = φ (wvec i) := by
    rw [hy₁act (wvec i) (wvec_even i), permVec_wvec, hρ₁i]
  have hfix₂ : y₂ * φ (wvec i) * y₂⁻¹ = φ (wvec i) := by
    rw [hy₂act (wvec i) (wvec_even i), permVec_wvec, hρ₂i]
  let g : G := y₁ * y₂
  have hg : g ∈ secM t S L ⊓ L := (secM t S L ⊓ L).mul_mem hy₁ hy₂
  have hgact : ∀ v, IsEvenVec v → g * φ v * g⁻¹ = y * φ v * y⁻¹ := by
    intro v hv
    have hv₂ : IsEvenVec (permVec ρ₂ v) := isEvenVec_permVec ρ₂ hv
    calc g * φ v * g⁻¹
        = y₁ * (y₂ * φ v * y₂⁻¹) * y₁⁻¹ := by
          change (y₁ * y₂) * φ v * (y₁ * y₂)⁻¹ = y₁ * (y₂ * φ v * y₂⁻¹) * y₁⁻¹
          group
      _ = y₁ * φ (permVec ρ₂ v) * y₁⁻¹ := by rw [hy₂act v hv]
      _ = φ (permVec ρ₁ (permVec ρ₂ v)) := hy₁act (permVec ρ₂ v) hv₂
      _ = φ (permVec (ρ₁ * ρ₂) v) := by rw [permVec_mul]
      _ = φ (permVec σ v) := by rw [hσ_eq]
      _ = y * φ v * y⁻¹ := (hσact v hv).symm
  have hb'act : ∀ v, IsEvenVec v → (g⁻¹ * y) * φ v * (g⁻¹ * y)⁻¹ = φ v := by
    intro v hv
    have hgv := hgact v hv
    calc (g⁻¹ * y) * φ v * (g⁻¹ * y)⁻¹
        = g⁻¹ * (y * φ v * y⁻¹) * g := by group
      _ = g⁻¹ * (g * φ v * g⁻¹) * g := by rw [hgv]
      _ = φ v := by group
  have hb'C : g⁻¹ * y ∈ centralizer (secB S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨v, hv, rfl⟩ := (himg b).1 hb
    have h := hb'act v hv
    calc φ v * (g⁻¹ * y) = ((g⁻¹ * y) * φ v * (g⁻¹ * y)⁻¹) * (g⁻¹ * y) := by rw [h]
      _ = (g⁻¹ * y) * φ v := by group
  have hb'L : g⁻¹ * y ∈ L :=
    ((secM t S L ⊓ L).mul_mem ((secM t S L ⊓ L).inv_mem hg) hy).2
  have hb'B : g⁻¹ * y ∈ secB S L := by
    have hmem : g⁻¹ * y ∈ centralizer (secB S L : Set G) ⊓ L := ⟨hb'C, hb'L⟩
    rwa [F.bdata.2.2.1] at hmem
  let b : G := g * (g⁻¹ * y) * g⁻¹
  have hbB : b ∈ secB S L := by
    change g * (g⁻¹ * y) * g⁻¹ ∈ secB S L
    exact F.normB g hg.1 (g⁻¹ * y) hb'B
  have hb_eq : b * g = y := by
    change (g * (g⁻¹ * y) * g⁻¹) * g = y
    group
  have hy₁3 : y₁ ^ 3 ∈ secB S L := sec121_pow_three_mem_B F hperm hy₁ hy₁act hρ₁c
  have hy₂3 : y₂ ^ 3 ∈ secB S L := sec121_pow_three_mem_B F hperm hy₂ hy₂act hρ₂c
  refine ⟨y₁, hy₁, y₂, hy₂, b, hbB, ?_, hy₁3, hy₂3, hfix₁, hfix₂⟩
  rw [← hb_eq]
  change b * (y₁ * y₂) = b * y₁ * y₂
  group

theorem sec121_fixed_lift (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5)))
    {i : Fin 5} {u y : G} (hu : u ∈ E) (hfu : sec12f t u = φ (wvec i)) (hy : y ∈ secM t S L ⊓ L)
    (hfix : y * φ (wvec i) * y⁻¹ = φ (wvec i)) : u⁻¹ * (y * u * y⁻¹) ∈ secB S L := by
  obtain ⟨y₁, hy₁, y₂, hy₂, b, hb, hy_eq, hy₁3, hy₂3, hfix₁, hfix₂⟩ :=
    sec121_stab_decomp F hperm hy hfix
  have hlift : ∀ {y₀ : G} (hy₀ : y₀ ∈ secM t S L ⊓ L) (hy₀3 : y₀ ^ 3 ∈ secB S L)
      (hfix₀ : y₀ * φ (wvec i) * y₀⁻¹ = φ (wvec i)),
      u⁻¹ * (y₀ * u * y₀⁻¹) ∈ secB S L := by
    intro y₀ hy₀ hy₀3 hfix₀
    have hy₀t : y₀ * t = t * y₀ := (Subgroup.mem_centralizer_iff.mp F.htC) y₀ hy₀.2
    have hf₀ : sec12f t (y₀ * u * y₀⁻¹) = sec12f t u := by
      rw [sec12E_f_conj hy₀t, hfu, hfix₀]
    have hy₀u : y₀ * u * y₀⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (sec12E_sylow_normal F hE hy₀.1) u).1 hu
    exact sec121_cube_lift F hE hu hy₀ hy₀3 hf₀
  have hc1 : u⁻¹ * (y₁ * u * y₁⁻¹) ∈ secB S L := hlift hy₁ hy₁3 hfix₁
  have hc2 : u⁻¹ * (y₂ * u * y₂⁻¹) ∈ secB S L := hlift hy₂ hy₂3 hfix₂
  let c1 : G := u⁻¹ * (y₁ * u * y₁⁻¹)
  let c2 : G := u⁻¹ * (y₂ * u * y₂⁻¹)
  have hc1B : c1 ∈ secB S L := hc1
  have hc2B : c2 ∈ secB S L := hc2
  have hy1u : y₁ * u * y₁⁻¹ = u * c1 := by
    change y₁ * u * y₁⁻¹ = u * (u⁻¹ * (y₁ * u * y₁⁻¹))
    group
  have hy2u : y₂ * u * y₂⁻¹ = u * c2 := by
    change y₂ * u * y₂⁻¹ = u * (u⁻¹ * (y₂ * u * y₂⁻¹))
    group
  let c2' : G := y₁ * c2 * y₁⁻¹
  have hc2'B : c2' ∈ secB S L := by
    change y₁ * c2 * y₁⁻¹ ∈ secB S L
    exact F.normB y₁ hy₁.1 c2 hc2B
  have hbu : b * u = u * b :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hE.1 hu)).2) b hb
  have hfin : y * u * y⁻¹ = u * (c1 * c2') := by
    rw [hy_eq]
    calc (b * y₁ * y₂) * u * (b * y₁ * y₂)⁻¹
        = b * (y₁ * (y₂ * u * y₂⁻¹) * y₁⁻¹) * b⁻¹ := by group
      _ = b * (y₁ * (u * c2) * y₁⁻¹) * b⁻¹ := by rw [hy2u]
      _ = b * ((y₁ * u * y₁⁻¹) * (y₁ * c2 * y₁⁻¹)) * b⁻¹ := by group
      _ = b * ((u * c1) * c2') * b⁻¹ := by rw [hy1u]
      _ = u * (c1 * c2') := by
            have hbc1 : b * c1 * b⁻¹ = c1 := by
              rw [show b * c1 = c1 * b from sec12E_B_comm F hb hc1B]; group
            have hbc2' : b * c2' * b⁻¹ = c2' := by
              rw [show b * c2' = c2' * b from sec12E_B_comm F hb hc2'B]; group
            have hbu' : b * u * b⁻¹ = u := by rw [hbu]; group
            calc b * ((u * c1) * c2') * b⁻¹
                = (b * u * b⁻¹) * (b * c1 * b⁻¹) * (b * c2' * b⁻¹) := by group
              _ = u * (c1 * c2') := by rw [hbu', hbc1, hbc2']; group
  rw [hfin]
  have : u⁻¹ * (u * (c1 * c2')) = c1 * c2' := by group
  rw [this]
  exact (secB S L).mul_mem hc1B hc2'B

end CFSG.OddStandard.SmallF3.Omega
