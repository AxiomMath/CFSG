module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4C
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4X1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6_conj_mem_sup_Ft (c : Ctx5 G L) {x : G}
    (hF : ∀ f ∈ c.s.fr.F, x * f * x⁻¹ = f)
    (ht : x * c.s.t * x⁻¹ ∈ c.s.fr.F ⊔ zpowers c.s.t) :
    ∀ y ∈ c.s.fr.F ⊔ zpowers c.s.t, x * y * x⁻¹ ∈ c.s.fr.F ⊔ zpowers c.s.t := by
  have hle : c.s.fr.F ⊔ zpowers c.s.t ≤
      (c.s.fr.F ⊔ zpowers c.s.t).comap (MulAut.conj x).toMonoidHom := by
    apply sup_le
    · intro f hf
      exact Subgroup.mem_comap.mpr
        (Subgroup.mem_sup_left (show x * f * x⁻¹ ∈ c.s.fr.F by rw [hF f hf]; exact hf))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_comap.mpr ht
  intro y hy
  exact Subgroup.mem_comap.mp (hle hy)

theorem y6b_T_le_normalizer_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : c.s.T ≤ normalizer (M3 c.s : Set G) := by
  rw [y5_T_eq_R_g hH hRT]
  refine sup_le ?_ ?_
  · intro r hr
    rw [Subgroup.mem_set_normalizer_iff]
    intro m
    constructor
    · exact fun hm => y54_R_norm_M3 c hH r hr m hm
    · intro hm
      have h := y54_R_norm_M3 c hH r⁻¹ (c.s.R.inv_mem hr) (r * m * r⁻¹) hm
      rwa [show r⁻¹ * (r * m * r⁻¹) * (r⁻¹)⁻¹ = m by group] at h
  · rw [Subgroup.zpowers_le, Subgroup.mem_set_normalizer_iff]
    intro m
    constructor
    · intro hm
      rw [hF.2.2.2.1 hRT m hm]
      exact hm
    · intro hm
      have hg2 : c.g * c.g = 1 := y6b_g_sq c hRT
      have hginv : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right hg2
      have h2 : c.g * (c.g * m * c.g⁻¹) * c.g⁻¹ = m := by
        calc c.g * (c.g * m * c.g⁻¹) * c.g⁻¹
            = (c.g * c.g) * m * (c.g⁻¹ * c.g⁻¹) := by group
          _ = m := by rw [hg2, hginv, hg2, one_mul, mul_one]
      have h3 := hF.2.2.2.1 hRT (c.g * m * c.g⁻¹) hm
      rw [h2] at h3
      rw [h3]
      exact hm

theorem y6b_E_le_normalizer_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : y6bE c ≤ normalizer (M3 c.s : Set G) :=
  (y6b_E_le_T c hH hRT).trans (y6b_T_le_normalizer_M3 c hH hF hRT)

theorem y6b_card_W (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : Nat.card ↥(y6bW c) = 256 := by
  have h := y6e_card_sup_mul_inf (H := y6bE c) (N := M3 c.s)
    (y6b_E_le_normalizer_M3 c hH hF hRT)
  rw [y6b_E_inf_M3 c hH hRT, y6b_card_E c hH hRT, y6e_card_M3 c hH] at h
  have hF8 : Nat.card ↥(c.s.fr.F) = 8 := by simpa using (y54_F_isE3 hH).2
  rw [hF8] at h
  rw [y6bW]
  omega

theorem y6b_mem_W (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T)
    {x : G} : x ∈ y6bW c ↔ ∃ e ∈ y6bE c, ∃ m ∈ M3 c.s, x = e * m := by
  show x ∈ (↑(y6bE c ⊔ M3 c.s) : Set G) ↔ ∃ e ∈ y6bE c, ∃ m ∈ M3 c.s, x = e * m
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (y6bE c) (M3 c.s)
    (y6b_E_le_normalizer_M3 c hH hF hRT), Set.mem_mul]
  constructor
  · rintro ⟨e, he, m, hm, h⟩
    exact ⟨e, he, m, hm, h.symm⟩
  · rintro ⟨e, he, m, hm, h⟩
    exact ⟨e, he, m, hm, h.symm⟩

theorem y6b_T3_decomp (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) : ∀ x ∈ y6bT3 c, ∃ τ ∈ c.s.T, ∃ m ∈ M3 c.s, x = τ * m := by
  intro x hx
  change x ∈ (↑(c.s.T ⊔ M3 c.s) : Set G) at hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (c.s.T) (M3 c.s)
    (y6b_T_le_normalizer_M3 c hH hF hRT), Set.mem_mul] at hx
  obtain ⟨τ, hτ, m, hm, h⟩ := hx
  exact ⟨τ, hτ, m, hm, h.symm⟩

theorem y6b_T3_cent_F_le_W (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ y6bT3 c, (∀ f ∈ c.s.fr.F, x * f = f * x) → x ∈ y6bW c := by
  intro x hx hxcent
  obtain ⟨τ, hτT, m, hmM3, rfl⟩ := y6b_T3_decomp c hH hF hRT x hx
  have hFM3 : c.s.fr.F ≤ M3 c.s := le_sup_right
  have hm_cent : ∀ f ∈ c.s.fr.F, m * f = f * m := by
    haveI : IsMulCommutative ↥(M3 c.s) := y6e_M3_comm c hF
    intro f hf
    exact congrArg Subtype.val (mul_comm' (⟨m, hmM3⟩ : ↥(M3 c.s))
      (⟨f, hFM3 hf⟩ : ↥(M3 c.s)))
  have hτf : ∀ f ∈ c.s.fr.F, τ * f = f * τ := by
    intro f hf
    have h2 : τ * f * m = f * τ * m := by
      calc τ * f * m = τ * (f * m) := by group
        _ = τ * (m * f) := by rw [hm_cent f hf]
        _ = (τ * m) * f := by group
        _ = f * (τ * m) := hxcent f hf
        _ = f * τ * m := by group
    exact mul_right_cancel h2
  have hτcent : τ ∈ centIn c.s.H c.s.fr.F :=
    Subgroup.mem_inf.mpr ⟨c.s.sylow_T.1 hτT, by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact (hτf f hf).symm⟩
  have hτE : τ ∈ y6bE c := y6b_cent_H_F_le_E c hH hRT hτcent
  exact (y6bW c).mul_mem (show τ ∈ y6bW c from Subgroup.mem_sup_left hτE)
    (show m ∈ y6bW c from Subgroup.mem_sup_right hmM3)

theorem y6b_swap (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T) :
    ∀ a ∈ y6bX c, (∀ f ∈ c.s.fr.F, a * f = f * a) → a ∉ y6bW c →
      ∃ f ∈ c.s.fr.F, a * c.s.t * a⁻¹ = f * (c.g * c.s.t) := by
  intro a ha hac haW
  obtain ⟨e, he16, hconj⟩ := y6b_X_conj_t c hH hF hRT a ha
  obtain ⟨f, hf, hef⟩ := (y6b_mem_E16 c hH hRT).mp he16
  rcases hef with he | he
  · exfalso
    have hFa : ∀ g' ∈ c.s.fr.F, a * g' * a⁻¹ = g' := by
      intro g' hg'
      rw [hac g' hg']
      group
    have hFa_inv : ∀ g' ∈ c.s.fr.F, a⁻¹ * g' * a = g' := by
      intro g' hg'
      calc a⁻¹ * g' * a = a⁻¹ * (g' * a) := by group
        _ = a⁻¹ * (a * g') := by rw [← hac g' hg']
        _ = g' := by group
    have hconjf : a * c.s.t * a⁻¹ = f * c.s.t := by rw [hconj, he]
    have ht : a * c.s.t * a⁻¹ ∈ c.s.fr.F ⊔ zpowers c.s.t := by
      rw [hconjf]
      exact Subgroup.mul_mem_sup hf (Subgroup.mem_zpowers c.s.t)
    have hta : a⁻¹ * c.s.t * a = f⁻¹ * c.s.t := by
      have hmid : a⁻¹ * (f * c.s.t) * a = c.s.t := by
        rw [← hconjf]
        group
      have h2 : f * (a⁻¹ * c.s.t * a) = c.s.t := by
        calc f * (a⁻¹ * c.s.t * a)
            = (a⁻¹ * f * a) * (a⁻¹ * c.s.t * a) := by rw [hFa_inv f hf]
          _ = a⁻¹ * (f * c.s.t) * a := by group
          _ = c.s.t := hmid
      calc a⁻¹ * c.s.t * a = f⁻¹ * (f * (a⁻¹ * c.s.t * a)) := by group
        _ = f⁻¹ * c.s.t := by rw [h2]
    have hta_mem : a⁻¹ * c.s.t * a ∈ c.s.fr.F ⊔ zpowers c.s.t := by
      rw [hta]
      exact Subgroup.mul_mem_sup (c.s.fr.F.inv_mem hf) (Subgroup.mem_zpowers c.s.t)
    have haP : a ∈ normalizer ((c.s.fr.F ⊔ zpowers c.s.t : Subgroup G) : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro y
      constructor
      · exact y6_conj_mem_sup_Ft c hFa ht y
      · intro hy
        have h2 := y6_conj_mem_sup_Ft c (x := a⁻¹)
          (fun g' hg' => by simpa using hFa_inv g' hg') (by simpa using hta_mem)
          (a * y * a⁻¹) hy
        rwa [show a⁻¹ * (a * y * a⁻¹) * (a⁻¹)⁻¹ = y by group] at h2
    have haY : a ∈ f4Y c.s := by
      refine Subgroup.mem_inf.mpr ⟨haP, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g' hg'
      exact (hac g' hg').symm
    obtain ⟨m, hmM3, x, hxX0, hax⟩ :=
      y54_Y_decomp (c := c) hH (y54_M3_cand c hH) a haY
    have hxE : x ∈ y6bE c := y6b_cent_H_F_le_E c hH hRT hxX0
    exact haW (by
      rw [hax]
      exact (y6bW c).mul_mem (show m ∈ y6bW c from Subgroup.mem_sup_right hmM3)
        (show x ∈ y6bW c from Subgroup.mem_sup_left hxE))
  · refine ⟨f, hf, ?_⟩
    rw [hconj, he, mul_assoc]

end CFSG.OddStandard.HigherRank.YamadaG23
