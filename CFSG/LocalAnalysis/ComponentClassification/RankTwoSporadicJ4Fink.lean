module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkOut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkReduce
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTwoA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTwoB

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4Fink

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Sporadic.J4.QT2

section Conf

variable {W : Type*} [Group W] [Finite W]

structure LocalConf (a : W) (M P : Subgroup W) : Prop where
  le_centralizer : M ≤ centralizer ({a} : Set W)
  normalized : ∀ c ∈ centralizer ({a} : Set W), ∀ m ∈ M, c * m * c⁻¹ ∈ M
  abelian : ∀ Q : Subgroup W, Q ≤ M → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  sylow : IsSylowOf 2 P M
  sq_eq_one : ∀ x ∈ P, x * x = 1
  four_le : 4 ≤ Nat.card P

theorem localConf_of_mem {H₀ P : Subgroup W} (hPsyl : IsSylowOf 2 P H₀)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hPsq : ∀ x ∈ P, x * x = 1) (hP4 : 4 ≤ Nat.card P)
    {a : W} (ha : a ∈ P) (hN : centralizer ({a} : Set W) ≤ normalizer (H₀ : Set W)) :
    LocalConf a (H₀ ⊓ centralizer ({a} : Set W)) P where
  le_centralizer := inf_le_right
  normalized c hc m hm := by
    rw [mem_inf] at hm ⊢
    exact ⟨(mem_normalizer_iff.mp (hN hc) m).mp hm.1, mul_mem (mul_mem hc hm.2) (inv_mem hc)⟩
  abelian Q hQ hQp x hx y hy := by
    obtain ⟨h, -, hconj⟩ := exists_conj_le_of_isSylowOf hPsyl hQp (hQ.trans inf_le_left)
    have hc := hPc _ (hconj x hx) _ (hconj y hy)
    calc x * y = h * ((h⁻¹ * x * h) * (h⁻¹ * y * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * y * h) * (h⁻¹ * x * h)) * h⁻¹ := by rw [hc]
      _ = y * x := by group
  sylow := by
    refine hPsyl.of_le (le_inf hPsyl.le fun x hx => ?_) inf_le_left
    rw [mem_centralizer_singleton_iff]
    exact hPc x hx a ha
  sq_eq_one := hPsq
  four_le := hP4

theorem LocalConf.conj {a : W} {M P : Subgroup W} (h : LocalConf a M P) (g : W) :
    LocalConf (g * a * g⁻¹) (M.map (MulAut.conj g).toMonoidHom)
      (P.map (MulAut.conj g).toMonoidHom) where
  le_centralizer := by
    rintro _ ⟨m, hm, rfl⟩
    have hma := h.le_centralizer hm
    rw [mem_centralizer_singleton_iff] at hma ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * m * g⁻¹ * (g * a * g⁻¹) = g * (m * a) * g⁻¹ := by group
      _ = g * (a * m) * g⁻¹ := by rw [hma]
      _ = g * a * g⁻¹ * (g * m * g⁻¹) := by group
  normalized := by
    rintro c hc _ ⟨m, hm, rfl⟩
    have hc' : g⁻¹ * c * g ∈ centralizer ({a} : Set W) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      calc g⁻¹ * c * g * a = g⁻¹ * (c * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * c) * g := by rw [hc]
        _ = a * (g⁻¹ * c * g) := by group
    refine ⟨(g⁻¹ * c * g) * m * (g⁻¹ * c * g)⁻¹, h.normalized _ hc' m hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  abelian Q hQ hQp x hx y hy := by
    have hQ' : Q.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨m, hm, hmq⟩ := hQ hq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmq ⊢
      have e : g⁻¹ * q * g⁻¹⁻¹ = m := by rw [← hmq]; group
      rw [e]
      exact hm
    have hc := h.abelian _ hQ' (hQp.map _) _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hc
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = y * x := by group
  sylow := IsSylowOf.map h.sylow _
  sq_eq_one := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h.sq_eq_one x hx, map_one]
  four_le := by
    rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
    exact h.four_le

end Conf

theorem star_J :
    NoCentralizerNormalized J := by
  intro H₀ P hPsyl hPel hP4 hN
  have hM := j4Facts.mat
  have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h := congrArg Subtype.val (hPel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using h
  have hPsq : ∀ x ∈ P, x * x = 1 := fun x hx => by
    rw [← sq]
    exact hPel.2 x hx
  have hconf : ∀ a ∈ P, a ≠ 1 → LocalConf a (H₀ ⊓ centralizer ({a} : Set J)) P :=
    fun a ha ha1 => localConf_of_mem hPsyl hPc hPsq hP4 ha (hN a ha ha1)
  by_cases h2A : ∃ b ∈ P, b ≠ 1 ∧ IsConj (eta uJ 11 3) b
  ·
    obtain ⟨b, hb, hb1, hbc⟩ := h2A
    obtain ⟨g₀, -, hg₀⟩ := exists_conj_eta_three hM mem_zMasks_1131
    have hzc : IsConj (eta uJ 11 3) (eta uJ 11 1131) := isConj_iff.mpr ⟨g₀, hg₀⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp (hbc.symm.trans hzc)
    have hc := (hconf b hb hb1).conj g
    rw [hg] at hc
    exact false_of_twoA hc.le_centralizer hc.normalized hc.abelian hc.sylow.le
      hc.sylow.isPGroup hc.four_le
  ·
    simp only [not_exists, not_and] at h2A
    have hPne : P ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hP4
      omega
    obtain ⟨a, ha, ha1⟩ := IsConcreteLE.not_le_iff_exists.mp fun h => hPne (le_bot_iff.mp h)
    have ha1' : a ≠ 1 := fun h => ha1 (mem_bot.mpr h)
    have h1 : IsConj (eta uJ 11 1) a :=
      (inv_conj_root j4Facts (hPsq a ha) ha1').resolve_right (h2A a ha ha1')
    obtain ⟨g, hg⟩ := isConj_iff.mp h1.symm
    have hc := (hconf a ha ha1').conj g
    rw [hg] at hc
    refine false_of_twoB hc.le_centralizer hc.normalized hc.sylow hc.sq_eq_one hc.four_le ?_
    rintro _ ⟨p, hp, rfl⟩ k hk
    have hk1 : IsConj (eta uJ 11 3) ((MulAut.conj g).toMonoidHom p) := isConj_iff.mpr ⟨k, hk⟩
    have hk2 : IsConj ((MulAut.conj g).toMonoidHom p) p := by
      refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    by_cases hp1 : p = 1
    · subst hp1
      exact eta_ne_one hM (by norm_num) (by norm_num) (isConj_one_left.mp (hk1.trans hk2))
    · exact h2A p hp hp1 (hk1.trans hk2)

theorem sporadicCaseOdd_J4_of_noDoubleCover
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) (hM : J4.J4NoDoubleCover) :
    SporadicCaseOdd .J4 := by
  intro G _ _ A hH hodd ⟨e₀⟩
  obtain ⟨f₀⟩ := J4.isSporadic_J4_of_quot hM hH.standard.1.1 e₀
  let f : ↥A ≃* ↥J := f₀.trans (seedEquiv j4Facts.mat)
  have hZ : center ↥A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hfx : f x ∈ center ↥J := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := f.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hx) z]
    rw [center_J, mem_bot] at hfx
    rw [mem_bot]
    exact f.injective (hfx.trans (map_one f).symm)
  let e : ↥A ⧸ center ↥A ≃* ↥J := e₀.trans (seedEquiv j4Facts.mat)
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus autModel_J (fun E _ _ h => (h le_top).elim)
      hH.standard.1.1 e, hodd, by have := hH.rank; omega, hH.not_normal⟩
  exact false_of_noCentralizerNormalized h32 h33 hyp autModel_J hZ e star_J

end CFSG.ComponentClassification.RankTwoSporadic.J4Fink
