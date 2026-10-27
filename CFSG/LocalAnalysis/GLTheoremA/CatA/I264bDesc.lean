module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bGen
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open scoped Pointwise

section Mono

variable {Y : Type} [Group Y] [Finite Y]

private theorem openIsKGroup_subgroup_held (hY : CFSG.Open.IsKGroup Y) (H : Subgroup Y) :
    CFSG.Open.IsKGroup ↥H :=
  CFSG.KCore.KGroupNonab.subgroup CFSG.Assembly.inCatalog_isoInvariant hY H

private theorem mem_normalizer_inf_centralizer_held {K E' : Subgroup Y} (hK : K.Normal) {g : Y}
    (hg : ∀ e ∈ E', g * e = e * g) :
    g ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (E' : Set Y) : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ (g : Y), (∀ e ∈ E', g * e = e * g) → ∀ h ∈ K ⊓ Subgroup.centralizer (E' : Set Y),
      g * h * g⁻¹ ∈ K ⊓ Subgroup.centralizer (E' : Set Y) := by
    intro g hg h hh
    refine ⟨hK.conj_mem h hh.1 g, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have h1 : e * h = h * e := (Subgroup.mem_centralizer_iff.1 hh.2 e he)
    have h2 : g⁻¹ * e = e * g⁻¹ := by
      have := hg e he
      calc g⁻¹ * e = g⁻¹ * (e * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * e) * g⁻¹ := by rw [this]
        _ = e * g⁻¹ := by group
    calc e * (g * h * g⁻¹) = (e * g) * h * g⁻¹ := by group
      _ = (g * e) * h * g⁻¹ := by rw [hg e he]
      _ = g * (e * h) * g⁻¹ := by group
      _ = g * (h * e) * g⁻¹ := by rw [h1]
      _ = g * h * (e * g⁻¹) := by group
      _ = g * h * (g⁻¹ * e) := by rw [h2]
      _ = g * h * g⁻¹ * e := by group
  intro h
  refine ⟨fun hh => key g hg h hh, fun hgh => ?_⟩
  have hg' : ∀ e ∈ E', g⁻¹ * e = e * g⁻¹ := by
    intro e he
    have := hg e he
    calc g⁻¹ * e = g⁻¹ * (e * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * e) * g⁻¹ := by rw [this]
      _ = e * g⁻¹ := by group
  have h2 := key g⁻¹ hg' _ hgh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rw [e] at h2
  exact h2

theorem layer_ne_bot_of_le {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt Y p) (hY : CFSG.Open.IsKGroup Y)
    {K E E' : Subgroup Y} (hK : K.Normal) (hE : IsElemAbelian p E) (hE'E : E' ≤ E)
    (h : GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) :
    GLAPLayer p (K ⊓ Subgroup.centralizer (E' : Set Y)) ≠ ⊥ := by
  set X : Subgroup Y := K ⊓ Subgroup.centralizer (E' : Set Y) with hX
  have hP : IsPGroup p E := isPGroup_of_isElemAbelian hE
  have hPX : E ≤ Subgroup.normalizer (X : Set Y) := fun g hg =>
    mem_normalizer_inf_centralizer_held hK fun e he => isElemAbelian_commute hE hg (hE'E he)
  have hKg : CFSG.Open.IsKGroup ↥(X ⊔ E) := openIsKGroup_subgroup_held hY _
  have hbal := glaPLayer_inf_centralizer_le hp hLB hKg hP hPX
  have heq : X ⊓ Subgroup.centralizer (E : Set Y) = K ⊓ Subgroup.centralizer (E : Set Y) := by
    ext y
    simp only [hX, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hyK, -⟩, hyE⟩
      exact ⟨hyK, hyE⟩
    · rintro ⟨hyK, hyE⟩
      refine ⟨⟨hyK, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩, hyE⟩
      exact Subgroup.mem_centralizer_iff.1 hyE e (hE'E he)
  rw [heq] at hbal
  intro hbot
  exact h (le_bot_iff.1 (hbot ▸ hbal))

theorem exists_sub_card_pow_three {p : ℕ} (hp : p.Prime) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E) : ∃ E' : Subgroup Y, E' ≤ E ∧ Nat.card E' = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  have h3 : 3 ≤ a := by
    rw [ha] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  have hdvd : p ^ 3 ∣ Nat.card E := by
    rw [ha]
    exact pow_dvd_pow p h3
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨S.map E.subtype, Subgroup.map_subtype_le S, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hS]

theorem kConcl_of_ge {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt Y p) (hY : CFSG.Open.IsKGroup Y)
    {K B E : Subgroup Y} (hK : K.Normal) (hB : IsElemAbelian p B) (hEB : E ≤ B)
    (hcard : p ^ 3 ≤ Nat.card E) (h : GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) :
    KConcl p K B := by
  have hE : IsElemAbelian p E := isElemAbelian_mono hB hEB
  obtain ⟨E', hE'E, hE'c⟩ := exists_sub_card_pow_three hp hE hcard
  exact ⟨E', hE'E.trans hEB, isElemAbelian_mono hE hE'E, hE'c,
    layer_ne_bot_of_le hp hLB hY hK hE hE'E h⟩

theorem kConcl_of_card_cent {p : ℕ} (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (hc : p ^ 3 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y))) : KConcl p K B := by
  have hE0 : IsElemAbelian p (B ⊓ Subgroup.centralizer (K : Set Y)) :=
    isElemAbelian_mono h.elem inf_le_left
  obtain ⟨E, hEE0, hEc⟩ := exists_sub_card_pow_three hp hE0 hc
  have hEK : E ≤ Subgroup.centralizer (K : Set Y) := hEE0.trans inf_le_right
  have hKC : K ≤ Subgroup.centralizer (E : Set Y) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.2 fun e he =>
      (Subgroup.mem_centralizer_iff.1 (hEK he) k hk).symm
  refine ⟨E, hEE0.trans inf_le_left, isElemAbelian_mono h.elem (hEE0.trans inf_le_left), hEc, ?_⟩
  rw [inf_eq_left.2 hKC]
  have hq : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq h.core).trans QuotientGroup.quotientBot).symm h.qs
  obtain ⟨hcomp, -, -⟩ := glaPLayer_of_isQuasisimple (p := p) (Y := K) hq
  intro hbot
  have := glaPComponent_ne_bot hcomp
  exact this hbot

end Mono

section Desc

variable {Y : Type} [Group Y] [Finite Y]

private theorem mem_centralizer_sup_iff_held {D E : Subgroup Y} {y : Y} :
    y ∈ Subgroup.centralizer ((E ⊔ D : Subgroup Y) : Set Y) ↔
      y ∈ Subgroup.centralizer (E : Set Y) ∧ y ∈ Subgroup.centralizer (D : Set Y) := by
  have key : ∀ T : Subgroup Y, y ∈ Subgroup.centralizer (T : Set Y) ↔
      T ≤ Subgroup.centralizer ({y} : Set Y) := by
    intro T
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hy t ht
      exact Subgroup.mem_centralizer_singleton_iff.2 (hy t ht)
    · intro hT t ht
      exact Subgroup.mem_centralizer_singleton_iff.1 (hT ht)
  rw [key, key, key, sup_le_iff]

structure DescData {Y : Type} [Group Y] [Finite Y] (p : ℕ) (K B D J : Subgroup Y) : Prop where
  le : D ≤ B
  noncent : ¬ D ≤ Subgroup.centralizer (K : Set Y)
  jk : J ≤ K
  comp : GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set Y)) J
  norm : B ≤ Subgroup.normalizer (J : Set Y)
  hyp : I264bHyp p B J

theorem DescData.card_lt {p : ℕ} {K B D J : Subgroup Y} (h : DescData p K B D J) :
    Nat.card J < Nat.card K := by
  refine Subgroup.card_lt_of_lt (lt_of_le_of_ne h.jk ?_)
  intro hJK
  apply h.noncent
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have : k ∈ J := hJK ▸ hk
  have h1 : k ∈ Subgroup.centralizer (D : Set Y) := (h.comp.1 this).2
  exact (Subgroup.mem_centralizer_iff.1 h1 d hd).symm

theorem layer_ne_bot_of_desc {p : ℕ} (hp : p.Prime) {K B D J E : Subgroup Y} (hK : K.Normal)
    (hB : IsElemAbelian p B) (hDB : D ≤ B) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set Y)) J)
    (hEB : E ≤ B) (hE : GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) :
    GLAPLayer p (K ⊓ Subgroup.centralizer ((E ⊔ D : Subgroup Y) : Set Y)) ≠ ⊥ := by
  have hJK : J ≤ K ⊓ Subgroup.centralizer (D : Set Y) := hJ.1
  have hFB : E ⊔ D ≤ B := sup_le hEB hDB
  have hJEF : J ⊓ Subgroup.centralizer (E : Set Y) = J ⊓ Subgroup.centralizer ((E ⊔ D : Subgroup Y) : Set Y) := by
    ext y
    simp only [Subgroup.mem_inf, mem_centralizer_sup_iff_held]
    constructor
    · rintro ⟨hyJ, hyE⟩
      exact ⟨hyJ, hyE, (hJK hyJ).2⟩
    · rintro ⟨hyJ, hyE, -⟩
      exact ⟨hyJ, hyE⟩
  obtain ⟨J₂, hJ₂, hJ₂ne⟩ := ys03_exists_component_ne_bot hE
  set N₀ : Subgroup Y := K ⊓ Subgroup.centralizer (D : Set Y) with hN₀
  set F : Subgroup Y := E ⊔ D with hF
  have hFN : F ≤ Subgroup.normalizer (N₀ : Set Y) := fun g hg =>
    mem_normalizer_inf_centralizer_held hK fun e he =>
      isElemAbelian_commute hB (hFB hg) (hDB he)
  set P : Subgroup Y := N₀ ⊔ F with hP
  have hN₀P : N₀ ≤ P := le_sup_left
  have hN₀n : (N₀.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀P).2 (sup_le Subgroup.le_normalizer hFN)
  have hN₀sn : IsSubnormal N₀ P := IsSubnormal.step hN₀P hN₀n (IsSubnormal.refl P)
  have hJP : IsSubnormal J P := isSubnormal_trans' hJ.2.1 hN₀sn
  have h1 := CFSG.Open.IsSubnormal.inf hJP (Subgroup.centralizer (F : Set Y))
  have hKF : K ⊓ Subgroup.centralizer (F : Set Y) ≤ P ⊓ Subgroup.centralizer (F : Set Y) := by
    intro y hy
    refine ⟨hN₀P ⟨hy.1, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩, hy.2⟩
    exact Subgroup.mem_centralizer_iff.1 hy.2 d ((show D ≤ F from le_sup_right) hd)
  have hJF : J ⊓ Subgroup.centralizer (F : Set Y) ≤ K ⊓ Subgroup.centralizer (F : Set Y) :=
    inf_le_inf_right _ (hJK.trans inf_le_left)
  have hsn : IsSubnormal (J ⊓ Subgroup.centralizer (F : Set Y)) (K ⊓ Subgroup.centralizer (F : Set Y)) :=
    isSubnormal_of_le_of_le h1 hJF hKF
  rw [hJEF] at hJ₂
  have hJ₂' := glaPComponent_of_isSubnormal' hp hsn hJ₂
  intro hbot
  have hle : J₂ ≤ GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set Y)) := le_sSup hJ₂'
  rw [hbot] at hle
  exact hJ₂ne (le_bot_iff.1 hle)

end Desc

@[expose] def KDescOrDirect (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3 →
    KConcl p K B ∨ ∃ D J : Subgroup Y, DescData p K B D J

theorem kd264bK_of_descOrDirect {p : ℕ}
    (hLB : p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p)
    (h : KDescOrDirect p) : KD264bK p := by
  intro hp hp2
  have key : ∀ n : ℕ, ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
      Nat.card K ≤ n → KConcl p K B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y _ _ K B hKH hn
      by_cases hc : p ^ 3 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y))
      · exact kConcl_of_card_cent hp hKH hc
      · rcases h hp hp2 Y K B hKH (not_le.1 hc) with hdirect | ⟨D, J, hD⟩
        · exact hdirect
        · obtain ⟨Y', _, _, K', B', hKH', hKle, hconcl⟩ := exists_kLevel_of_hyp hp hD.hyp
          have hlt : Nat.card K' < n := lt_of_le_of_lt hKle (lt_of_lt_of_le hD.card_lt hn)
          have hGB : IsGB p B J := hconcl (ih _ hlt Y' K' B' hKH' le_rfl)
          obtain ⟨E, hEB, hEab, hEc, -, hEl⟩ := hGB
          have hlayer := layer_ne_bot_of_desc hp hKH.normal hKH.elem hD.le hD.comp hEB hEl
          refine kConcl_of_ge hp (hLB hp Y) hKH.kgroup hKH.normal hKH.elem
            (sup_le hEB hD.le) ?_ hlayer
          calc p ^ 3 = Nat.card E := hEc.symm
            _ ≤ Nat.card ↥(E ⊔ D) := Subgroup.card_le_of_le le_sup_left
  intro Y _ _ K B hKH
  exact key _ Y K B hKH le_rfl

end CFSG.LocalAnalysis.GLTheoremA
