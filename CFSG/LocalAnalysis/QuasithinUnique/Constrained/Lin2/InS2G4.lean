module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem x_sq_mem_R1 : x₀ * x₀ ∈ AppE.R1 S L := by
  have hB := O.base
  have h1 : x₀ * x₀ ∈ S := CFSG.QuasithinUnique.mul_self_mem_of_relIndex_two hB.h2 hB.hx₀ hB.hx₀S
  rw [← hB.S_inf_S₁]
  exact ⟨h1, (s2S₁ M₀ S L).mul_mem O.x_mem_S₁ O.x_mem_S₁⟩

theorem conjR_L₂x_R1 {s : G} (hs : s ∈ AppE.R1 S L) :
    conjR (conjR L t) s = conjR L t ∧ conjR (conjR (conjR L t) x₀) s = conjR (conjR L t) x₀ := by
  have hB := O.base
  have h1 : conjR (conjR L t) s = conjR L t :=
    conjR_eq_self_iff.2 (hB.dbl.R1_le_normalizer_L₂ hs)
  refine ⟨h1, ?_⟩
  have hxs : x₀ * s * x₀⁻¹ ∈ AppE.R1 S L := (O.conj_mem_R1_iff (AppE.R1_le_S hs)).2 hs
  have e : x₀ * s = (x₀ * s * x₀⁻¹) * x₀ := by group
  rw [conjR_conjR, e, ← conjR_conjR,
    conjR_eq_self_iff.2 (hB.dbl.R1_le_normalizer_L₂ hxs)]

theorem S₁_le_normalizer_K :
    s2S₁ M₀ S L ≤ Subgroup.normalizer ((conjR L t ⊔ conjR (conjR L t) x₀ : Subgroup G) : Set G) := by
  have hB := O.base
  intro g hg
  rw [← conjR_eq_self_iff]
  have hS₀ : ∀ s ∈ AppE.R1 S L,
      conjR (conjR L t ⊔ conjR (conjR L t) x₀) s = conjR L t ⊔ conjR (conjR L t) x₀ := by
    intro s hs
    rw [conjR_sup, (O.conjR_L₂x_R1 hs).1, (O.conjR_L₂x_R1 hs).2]
  have hx : conjR (conjR L t ⊔ conjR (conjR L t) x₀) x₀ =
      conjR L t ⊔ conjR (conjR L t) x₀ := by
    have h2 : conjR (conjR (conjR L t) x₀) x₀ = conjR L t := by
      rw [conjR_conjR]
      exact conjR_eq_self_iff.2 (hB.dbl.R1_le_normalizer_L₂ O.x_sq_mem_R1)
    rw [conjR_sup, h2, sup_comm]
  obtain ⟨hgM, -⟩ := mem_s2S₁.1 hg
  rcases CFSG.QuasithinUnique.mem_or_inv_mul_mem_of_relIndex_two hB.h2 hB.hx₀ hB.hx₀S hgM with h | h
  · have hgS₀ : g ∈ AppE.R1 S L := by
      rw [← hB.S_inf_S₁]
      exact ⟨h, hg⟩
    exact hS₀ g hgS₀
  · have hs : x₀⁻¹ * g ∈ AppE.R1 S L := by
      rw [← hB.S_inf_S₁]
      exact ⟨h, (s2S₁ M₀ S L).mul_mem ((s2S₁ M₀ S L).inv_mem O.x_mem_S₁) hg⟩
    have e : g = x₀ * (x₀⁻¹ * g) := by group
    rw [e, ← conjR_conjR, hx, hS₀ _ hs]

theorem K_le_centralizer_R₁ :
    (conjR L t ⊔ conjR (conjR L t) x₀ : Subgroup G) ≤
      Subgroup.centralizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) := by
  have hB := O.base
  refine sup_le (fun l hl => ?_) (fun l hl => ?_)
  · refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
    exact hB.comm_elem r hr.2 l hl
  · refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
    obtain ⟨l₀, hl₀, rfl⟩ := mem_conjR_iff'.1 hl
    have hrx : x₀ * r * x₀⁻¹ ∈ thompsonJ S ⊓ L := by
      have : r ∈ conjR (thompsonJ S ⊓ L) x₀ := by rw [O.conjR_R₁]; exact hr
      exact mem_conjR.1 this
    have h1 := hB.comm_elem _ hrx.2 l₀ hl₀
    calc r * (x₀⁻¹ * l₀ * x₀) = x₀⁻¹ * ((x₀ * r * x₀⁻¹) * l₀) * x₀ := by group
      _ = x₀⁻¹ * (l₀ * (x₀ * r * x₀⁻¹)) * x₀ := by rw [h1]
      _ = x₀⁻¹ * l₀ * x₀ * r := by group

theorem D₁_le_centralizer_K :
    D₁ ≤ Subgroup.centralizer ((conjR L t ⊔ conjR (conjR L t) x₀ : Subgroup G) : Set G) := by
  have hB := O.base
  have hD₁L : D₁ ≤ L := O.hT₁.le_borel.trans inf_le_left
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  have h : (conjR L t ⊔ conjR (conjR L t) x₀ : Subgroup G) ≤ Subgroup.centralizer ({d} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun l hl => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hB.comm_elem d (hD₁L hd) l hl).symm
    · obtain ⟨l₀, hl₀, rfl⟩ := mem_conjR_iff'.1 hl
      have hdx : x₀ * d * x₀⁻¹ ∈ D₁ := by
        have : d ∈ conjR D₁ x₀ := by rw [hB.conjR_D₁_eq_self O.hT₁ O.hT₂ O.hD O.hC O.hDx]; exact hd
        exact mem_conjR.1 this
      have h1 := hB.comm_elem _ (hD₁L hdx) l₀ hl₀
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc x₀⁻¹ * l₀ * x₀ * d = x₀⁻¹ * (l₀ * (x₀ * d * x₀⁻¹)) * x₀ := by group
        _ = x₀⁻¹ * ((x₀ * d * x₀⁻¹) * l₀) * x₀ := by rw [h1]
        _ = d * (x₀⁻¹ * l₀ * x₀) := by group
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h hk))

theorem D₁_inf_K : D₁ ⊓ (conjR L t ⊔ conjR (conjR L t) x₀) = ⊥ := by
  have hB := O.base
  have h4 : 4 ≤ 2 ^ n := two_pow_ge_four hB.hn
  rw [eq_bot_iff]
  rintro d ⟨hd, hdK⟩
  rw [Subgroup.mem_bot]
  by_contra hd1
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_one_lt_card (X := blockU L) (one_lt_card_blockU hB.hlin hB.hn)
  have huR : u ∈ thompsonJ S ⊓ L := ⟨hB.U₁_le_R hu, blockU_le L hu⟩
  have hcomm : d * u = u * d := by
    have := Subgroup.mem_centralizer_iff.1 (O.K_le_centralizer_R₁ hdK) u huR
    exact this.symm
  have hz := torus_comm_mem_Z O.hT₁ hB.pCore_L hd hd1 huR hcomm
  rw [hB.blockZ_eq_bot O.hC, Subgroup.mem_bot] at hz
  exact hu1 hz

end S2Ok

end CFSG.QuasithinUnique.Lin2
