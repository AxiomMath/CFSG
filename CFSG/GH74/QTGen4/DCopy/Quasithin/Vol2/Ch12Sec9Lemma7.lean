module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem Hyp1223.ti_of_1222_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} (h : Hyp1223 G T L V)
    {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥ := by
  rcases h1222 G T h.simple h.nonabelian h.qtke h.sylow with hAlt | h3
  · exact absurd hAlt h.notAlt
  obtain ⟨-, -, hall⟩ := h3 L h.maximal h.faithful h.quasisimple
  exact (hall V h.irrPlus).2.1 m hm

@[expose] def Claim12_9_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₂ : Subgroup G, IsTSub T V V₂ 2 →
      Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)

theorem lemma12_9_7_of_claim_F4 (h1222 : Stmt12_2_2_F4) (hcl : Claim12_9_7_F4) : Lemma12_9_7_F4 := by
  intro G _ _ T L V n hcx i Vi hi1 hin hVi
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes_F4 h1222

  obtain ⟨V₂, hV₂⟩ := exists_tsub hyp.sylow.1 hsq hab hTV hcard 2 (by omega)
  have hV₂i : V₂ ≤ Vi := by
    rcases tinv_comparable_of_hyp1281One_F4 h1222 hcx.hyp hV₂.1 hVi.1 hV₂.2.2 hVi.2.2 with h | h
    · exact h
    · have h1 := Subgroup.card_le_of_le h
      rw [hVi.2.1, hV₂.2.1] at h1
      have hi : i = 2 := by
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
        omega
      exact (Subgroup.eq_of_le_of_card_ge h (by rw [hVi.2.1, hV₂.2.1, hi])).ge
  intro g hg
  obtain ⟨l, hl, hlg⟩ := exists_mem_conj_eq_of_le hcx.hyp hVi.1 hg
  have hc : l⁻¹ * g ∈ Subgroup.centralizer (Vi : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * (l⁻¹ * g) = l⁻¹ * (l * x * l⁻¹) * g := by group
      _ = l⁻¹ * (g * x * g⁻¹) * g := by rw [hlg x hx]
      _ = l⁻¹ * g * x := by group
  have hcM : l⁻¹ * g ∈ Subgroup.normalizer (L : Set G) :=
    hcl G T L V n hcx V₂ hV₂ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hV₂i) hc)
  have hgM : g ∈ Subgroup.normalizer (L : Set G) := by
    have h1 := mul_mem (Subgroup.le_normalizer hl) hcM
    rwa [mul_inv_cancel_left] at h1
  refine ⟨hgM, ?_⟩
  rcases hyp.ti_of_1222_F4 h1222 hgM with h | h
  · exact SteinbergBS.mem_normalizer_of_conjugate_eq h
  · exfalso
    have hViV : Vi ≤ V ⊓ CFSG.conjugate V g := le_inf hVi.1 fun x hx => by
      rw [SteinbergBS.mem_conjugate_iff]
      exact hVi.1 ((Subgroup.mem_normalizer_iff.1 hg x).1 hx)
    rw [h, le_bot_iff] at hViV
    have h1 := hVi.2.1
    rw [hViV, Subgroup.card_bot] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end CFSG.Quasithin.H13
