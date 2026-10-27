module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmgLocal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmhConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmi_card_S₀_le :
    Nat.card (swapS₂ P U T ⊓ centralizer ({t * w} : Set G) : Subgroup G) ≤ 8 * f * (2 ^ f) ^ 2 := by
  set S₀ := swapS₂ P U T ⊓ centralizer ({t * w} : Set G) with hS₀
  set Y := (U ⊔ T) ⊓ S₀ with hY
  have h1 := relIndex_mul_card (H := U ⊔ T) (K := S₀)
  have h2 : (U ⊔ T).relIndex S₀ ≤ 2 := by
    rw [← hW.relIndex_SU_S₂]
    exact relIndex_le_of_le_right inf_le_left (by rw [hW.relIndex_SU_S₂]; norm_num)
  have h3 := relIndex_mul_card (H := U₁) (K := Y)
  have hU₁ne : U₁.relIndex (U ⊔ T) ≠ 0 := by
    intro h0
    have h4 := relIndex_mul_card (H := U₁) (K := U ⊔ T)
    rw [h0, zero_mul] at h4
    exact Nat.card_pos.ne' h4.symm
  have h4 : U₁.relIndex Y ≤ 4 * f :=
    (relIndex_le_of_le_right (inf_le_left : Y ≤ U ⊔ T) hU₁ne).trans hW.relIndex_U₁_le
  have h5 : U₁ ⊓ Y ≤ U₁ ⊓ centralizer ({t * w} : Set G) := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp (mem_inf.mp hx).2).2).2⟩
  have h6 := Subgroup.card_le_of_le h5
  rw [hW.card_F] at h6
  have h7 : Nat.card Y ≤ 4 * f * (2 ^ f) ^ 2 := by
    rw [← h3]
    exact Nat.mul_le_mul h4 h6
  calc Nat.card S₀ = (U ⊔ T).relIndex S₀ * Nat.card Y := h1.symm
    _ ≤ 2 * (4 * f * (2 ^ f) ^ 2) := Nat.mul_le_mul h2 h7
    _ = 8 * f * (2 ^ f) ^ 2 := by ring

theorem gmi_eq_one_of_conj_eq {e : G} (heT : e ∈ normalizer (szT₁ L T : Set G))
    (heV : e ∈ normalizer (V : Set G))
    (heA : ∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b → b = 1)
    {x : G} (hx : x ∈ U₁ ⊓ centralizer ({t * w} : Set G)) (hex : e * x * e⁻¹ = x) : x = 1 := by
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨-, -, -, -, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W', hW'T₁, -, -, -, -, -, hW'iff⟩ :=
    h.exists_W_of_card_sylow hS2 hW.tw_mem hW.tw_sq hW.tw_not_mem
  have hWVN : W' ≤ normalizer (V : Set G) := fun y hy =>
    hL.muOne_T₁_le_normalizer hS (hW'T₁ hy)
  obtain ⟨y, hy, r, hr, rfl⟩ := ncyc_exists_mul_of_mem_sup hWVN (hW.F_le hW'iff hx)
  have hyT : y ∈ szT₁ L T := hW'T₁ hy
  have heyT : e * y * e⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp heT y).mp hyT
  have herV : e * r * e⁻¹ ∈ V := (mem_normalizer_iff.mp heV r).mp hr
  set b := y⁻¹ * (e * y * e⁻¹) with hb
  have hbT : b ∈ szT₁ L T := mul_mem (inv_mem hyT) heyT
  have hb' : b = r * (e * r * e⁻¹)⁻¹ := by
    have e1 : (e * y * e⁻¹) * (e * r * e⁻¹) = y * r := by
      rw [show (e * y * e⁻¹) * (e * r * e⁻¹) = e * (y * r) * e⁻¹ by group, hex]
    rw [hb]
    calc y⁻¹ * (e * y * e⁻¹) = y⁻¹ * ((e * y * e⁻¹) * (e * r * e⁻¹)) * (e * r * e⁻¹)⁻¹ := by
          group
      _ = r * (e * r * e⁻¹)⁻¹ := by rw [e1]; group
  have hbV : b ∈ V := by rw [hb']; exact mul_mem hr (inv_mem herV)
  have hbA : b ∈ szA₁ (szT₁ L T) :=
    mem_szA₁.mpr ⟨hbT, mem_centralizer_iff.mpr fun z hz => (hL.muOne_T₁_comm hS hz hbV)⟩
  have hb2 : b * b = 1 := by rw [← sq]; exact hA₁sq b hbA
  have herr : e * r * e⁻¹ = b⁻¹ * r := by
    rw [hb']
    group
  have hr2V : r ^ 2 ∈ V := pow_mem hr 2
  have hr4 : (r ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hS.conf.pow r hr
  have hr2A : r ^ 2 ∈ szA₁ (szT₁ L T) := hS.conf.omega _ hr2V hr4
  have hbr : b * r = r * b := hS.conf.comm b hbV r hr
  have her2 : e * r ^ 2 * e⁻¹ = r ^ 2 := by
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    calc e * r ^ 2 * e⁻¹ = (e * r * e⁻¹) * (e * r * e⁻¹) := by rw [sq]; group
      _ = (b * r) * (b * r) := by rw [herr, hbinv]
      _ = (b * b) * (r * r) := by
          rw [show (b * r) * (b * r) = b * (r * b) * r by group, ← hbr]; group
      _ = r ^ 2 := by rw [hb2, one_mul, sq]
  have hr21 : r ^ 2 = 1 := heA _ hr2A her2
  have hrA : r ∈ szA₁ (szT₁ L T) := hS.conf.omega r hr hr21
  have hxT : y * r ∈ szT₁ L T := mul_mem hyT (szA₁_le _ hrA)
  have hxt : y * r * t = t * (y * r) :=
    (mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ (y * r) hxT)
  exact heA _ (hW.gmg_mem_szA₁_of_commute_t hx hxt) hex

theorem gmi_exists_torus : ∃ e : G, e ∈ L ∧ e * (t * w) = (t * w) * e ∧ Odd (orderOf e) ∧
    e ∈ normalizer (U₁ : Set G) ∧ e ∈ normalizer (szT₁ L T : Set G) ∧
    e ∈ normalizer (V : Set G) ∧ (∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b → b = 1) ∧
    ∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G), e * x * e⁻¹ = x → x = 1 := by
  obtain ⟨c, hc, hvD⟩ := hW.gmh_exists_normalizes
  have hW' := hW.gmh_conj hc
  obtain ⟨e, heD, hev, hetr⟩ := hW'.gmh_exists_torus hvD
  have heL : e ∈ L := hW'.step.cartan.le heD
  have heodd : Odd (orderOf e) := by
    have hdvd : orderOf e ∣ Nat.card (D.map (MulAut.conj c⁻¹).toMonoidHom) := by
      have := orderOf_dvd_natCard (⟨e, heD⟩ : D.map (MulAut.conj c⁻¹).toMonoidHom)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hW'.step.cartan.odd hdvd
  have heU : e ∈ normalizer (U₁ : Set G) := hW'.level.D_le heD
  have heT : e ∈ normalizer (szT₁ L T : Set G) := hW'.step.cartan.le_normalizer heD
  have heV : e ∈ normalizer (V : Set G) := hW'.step.conf.D_le heD
  have heA : ∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b → b = 1 := by
    intro b hb heb
    have heb' : e⁻¹ * b * e = b := by
      calc e⁻¹ * b * e = e⁻¹ * (e * b * e⁻¹) * e := by rw [heb]
        _ = b := by group
    exact hW.step.start.gmh_eq_one_of_conj_eq hW.step.card_sylow hetr hb heb'
  exact ⟨e, heL, hev, heodd, heU, heT, heV, heA,
    fun x hx hex => hW.gmi_eq_one_of_conj_eq heT heV heA hx hex⟩

end U3C1OuterSwapHigh

end CFSG.SeitzReduction.RankOne
