module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2C6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Borel4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

theorem S2Base.exists_good_normalizing (B : S2Base T M H S L D n t M₀ x₀ q W) (h246 : Lemma246Double) :
    ∃ (y : G) (D₁ D₂ : Subgroup G), S2Base T M H S L D n t M₀ y q W ∧
      BlockTorus L (thompsonJ S ⊓ L) D₁ n ∧
      BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n ∧ D = D₁ ⊔ D₂ ∧ conjR D y = D := by
  obtain ⟨D₁, D₂, hT₁, hT₂, hD⟩ := B.exists_torus
  obtain ⟨y, B', By, hH⟩ := B.exists_stageC h246
  exact ⟨y, D₁, D₂, By, hT₁, hT₂, hD, By.hall_conj_eq hH hT₁ hT₂ hD⟩

omit [Finite G] in
theorem exists_unique_of_inf_bot {X Y : Subgroup G} (hXY : X ⊓ Y = ⊥) {a a' b b' : G} (ha : a ∈ X)
    (ha' : a' ∈ X) (hb : b ∈ Y) (hb' : b' ∈ Y) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ X ⊓ Y :=
    ⟨X.mul_mem (X.inv_mem ha') ha, by rw [h1]; exact Y.mul_mem hb' (Y.inv_mem hb)⟩
  rw [hXY, Subgroup.mem_bot] at h2
  have e1 : a = a' := by
    have := congrArg (fun z => a' * z) h2
    simpa using this
  subst e1
  refine ⟨rfl, ?_⟩
  exact mul_left_cancel h

theorem two_pow_ge_four {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem R_decomp : ∀ r ∈ thompsonJ S, ∃ r₁ ∈ thompsonJ S ⊓ L, ∃ r₂ ∈ thompsonJ S ⊓ conjR L t,
    ∃ c ∈ baumD S L, r = r₁ * r₂ * c := by
  intro r hr
  have hr' := hr
  rw [B.R_eq_sup] at hr'
  have hNC : thompsonJ S ⊓ Subgroup.centralizer (conjJoin S L : Set G) ≤
      Subgroup.normalizer (((thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t) : Subgroup G) : Set G) := by
    refine le_normalizer_of_commute fun a ha b hb => ?_
    have haL₀ : a ∈ conjJoin S L :=
      (sup_le (inf_le_right.trans B.L_le_L₀) (inf_le_right.trans B.L₂_le_L₀)) ha
    exact Subgroup.mem_centralizer_iff.1 hb.2 a haL₀
  obtain ⟨p, hp, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer hNC).1 hr'
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := (mem_sup_iff_of_le_normalizer B.R₂_le_normalizer_R₁).1 hp
  refine ⟨r₁, hr₁, r₂, hr₂, c, ?_, rfl⟩
  rw [← B.C_eq_baumD]; exact hc

theorem D_decomp {D₁ D₂ : Subgroup G} (h₁ : D₁ ≤ L) (h₂ : D₂ ≤ conjR L t) (hD : D = D₁ ⊔ D₂) :
    ∀ d ∈ D, ∃ d₁ ∈ D₁, ∃ d₂ ∈ D₂, d = d₁ * d₂ := by
  intro d hd
  rw [hD] at hd
  have hN : D₂ ≤ Subgroup.normalizer (D₁ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => B.comm_elem a (h₁ ha) b (h₂ hb)
  exact (mem_sup_iff_of_le_normalizer hN).1 hd

theorem centralizer_L₀_of_mem {u : G} (hL : ∀ a ∈ L, a * u = u * a) (hu : u ∈ L) :
    u ∈ Subgroup.centralizer (conjJoin S L : Set G) := by
  rw [B.hjoin]
  exact C56.mem_centralizer_sup hL (fun b hb => (B.comm_elem u hu b hb).symm)

theorem blockZ_le_C : blockZ L ≤ baumD S L := by
  intro u hu
  have huU : u ∈ blockU L := hu.1
  have huR : u ∈ baum S := B.su.U₁_le_B huU
  refine ⟨huR, ?_⟩
  exact B.centralizer_L₀_of_mem (fun a ha => Subgroup.mem_centralizer_iff.1 hu.2 a ha)
    (blockU_le L huU)

theorem blockZ_le_C₂ : blockZ (conjR L t) ≤ baumD S L := by
  intro u hu
  have huU : u ∈ blockU (conjR L t) := hu.1
  have huR : u ∈ baum S := by
    have : u ∈ conjR (blockU L) t := by rw [← DoubleA3.blockU_conjR]; exact huU
    exact B.su.U₂_le_B this
  refine ⟨huR, ?_⟩
  rw [B.hjoin]
  exact C56.mem_centralizer_sup (fun a ha => B.comm_elem a ha u (blockU_le _ huU))
    (fun b hb => Subgroup.mem_centralizer_iff.1 hu.2 b hb)

end S2Base

omit [Finite G] in
theorem exists_ne_one_of_one_lt_card {X : Subgroup G} (h : 1 < Nat.card X) : ∃ x ∈ X, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcon x hx)
  rw [this, Subgroup.card_bot] at h
  omega

omit [Finite G] in
theorem torus_comm_mem_Z {Lb Rb Dt : Subgroup G} {n : ℕ} (hT : BlockTorus Lb Rb Dt n)
    (hpc : pCoreOf 2 Lb = blockU Lb) {d r : G} (hd : d ∈ Dt) (hd1 : d ≠ 1) (hr : r ∈ Rb)
    (hcomm : d * r = r * d) : r ∈ blockZ Lb := by
  have h1 : d * r * d⁻¹ * r⁻¹ = 1 := by rw [hcomm]; group
  have hp : r ∈ pCoreOf 2 Lb := hT.fpf_R d hd hd1 r hr (by rw [h1]; exact Subgroup.one_mem _)
  exact hT.fpf_U d hd hd1 r (hpc ▸ hp) (by rw [h1]; exact Subgroup.one_mem _)

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem C_eq_RCD {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂) :
    thompsonJ S ⊓ Subgroup.centralizer (D : Set G) = baumD S L := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have h4 : 4 ≤ 2 ^ n := two_pow_ge_four B.hn
  have hD₁D : D₁ ≤ D := hD ▸ le_sup_left
  have hD₂D : D₂ ≤ D := hD ▸ le_sup_right
  apply le_antisymm
  · rintro r ⟨hrR, hrD⟩
    obtain ⟨r₁, hr₁, r₂, hr₂, c, hc, rfl⟩ := B.R_decomp r hrR
    have hrD' : ∀ d ∈ D, d * (r₁ * r₂ * c) = (r₁ * r₂ * c) * d := fun d hd =>
      Subgroup.mem_centralizer_iff.1 hrD d hd
    obtain ⟨d₁, hd₁, hd₁1⟩ := exists_ne_one_of_one_lt_card (X := D₁) (by rw [hT₁.card]; omega)
    obtain ⟨d₂, hd₂, hd₂1⟩ := exists_ne_one_of_one_lt_card (X := D₂) (by rw [hT₂.card]; omega)
    have hcL₀ := Subgroup.mem_centralizer_iff.1 hc.2
    have h1 : d₁ * r₁ = r₁ * d₁ := by
      have hfull := hrD' d₁ (hD₁D hd₁)
      have hdr₂ : d₁ * r₂ = r₂ * d₁ := B.comm_elem d₁ (hD₁L hd₁) r₂ hr₂.2
      have hdc : d₁ * c = c * d₁ := hcL₀ d₁ (B.L_le_L₀ (hD₁L hd₁))
      calc d₁ * r₁ = (d₁ * (r₁ * r₂ * c)) * (r₂ * c)⁻¹ := by group
        _ = ((r₁ * r₂ * c) * d₁) * (r₂ * c)⁻¹ := by rw [hfull]
        _ = r₁ * r₂ * (c * d₁) * (r₂ * c)⁻¹ := by group
        _ = r₁ * r₂ * (d₁ * c) * (r₂ * c)⁻¹ := by rw [hdc]
        _ = r₁ * (r₂ * d₁) * c * (r₂ * c)⁻¹ := by group
        _ = r₁ * (d₁ * r₂) * c * (r₂ * c)⁻¹ := by rw [hdr₂]
        _ = r₁ * d₁ := by group
    have h2 : d₂ * r₂ = r₂ * d₂ := by
      have hfull := hrD' d₂ (hD₂D hd₂)
      have hdr₁ : d₂ * r₁ = r₁ * d₂ := (B.comm_elem r₁ hr₁.2 d₂ (hD₂L hd₂)).symm
      have hdc : d₂ * c = c * d₂ := hcL₀ d₂ (B.L₂_le_L₀ (hD₂L hd₂))
      calc d₂ * r₂ = r₁⁻¹ * (r₁ * d₂ * r₂ * c) * c⁻¹ := by group
        _ = r₁⁻¹ * (d₂ * r₁ * r₂ * c) * c⁻¹ := by rw [hdr₁]
        _ = r₁⁻¹ * (d₂ * (r₁ * r₂ * c)) * c⁻¹ := by group
        _ = r₁⁻¹ * ((r₁ * r₂ * c) * d₂) * c⁻¹ := by rw [hfull]
        _ = r₂ * (c * d₂) * c⁻¹ := by group
        _ = r₂ * (d₂ * c) * c⁻¹ := by rw [hdc]
        _ = r₂ * d₂ := by group
    have hz₁ : r₁ ∈ baumD S L := B.blockZ_le_C (torus_comm_mem_Z hT₁ B.pCore_L hd₁ hd₁1 hr₁ h1)
    have hz₂ : r₂ ∈ baumD S L := B.blockZ_le_C₂ (torus_comm_mem_Z hT₂ B.pCore_L₂ hd₂ hd₂1 hr₂ h2)
    exact (baumD S L).mul_mem ((baumD S L).mul_mem hz₁ hz₂) hc
  · intro r hr
    refine ⟨(AppE.baumD_le_baum S L).trans (B.baum_eq ▸ le_rfl) hr, ?_⟩
    show r ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.1 hr.2 d (B.D_le_L₀ hd))

theorem C_eq_bot {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hDx : conjR D x₀ = D) : baumD S L = ⊥ := by
  have h1 := B.su.D_inf_conj
  have h2 : conjR (baumD S L) x₀ = baumD S L := by
    rw [← B.C_eq_RCD hT₁ hT₂ hD, conjR_inf, B.conjR_R_x₀, ← conjR_centralizer, hDx]
  have h3 : conjSubgroup (baumD S L) x₀ = baumD S L := h2
  rwa [h3, inf_idem] at h1

end S2Base

end CFSG.QuasithinUnique.Lin2
