module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDichotomy
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem JData.centralizer_le {A R T J : Subgroup G} {p y : G} (hJ : JData A R T p J y) :
    A ⊓ centralizer ({p} : Set G) ≤ centralizer (J : Set G) := by
  intro a ha
  obtain ⟨haA, hap⟩ := mem_inf.mp ha
  refine hJ.free a (mem_inf.mpr ⟨haA, hJ.le_normalizer ha⟩) p hJ.mem hJ.ne_one ?_
  rw [mem_centralizer_singleton_iff] at hap
  rw [hap, mul_inv_cancel_right]

structure AParts (A R T : Subgroup G) (p : G) (J : Subgroup G) : Prop where
  mem : p ∈ A
  ne_one : p ≠ 1
  aPart_mem : ∃ t ∈ T, t⁻¹ * p ∈ R
  aPart_le : ∀ t ∈ T, ∀ p' ∈ A, t⁻¹ * p' ∈ R → p' ∈ J
  centralizer_le : A ⊓ centralizer ({p} : Set G) ≤ centralizer (J : Set G)

omit [Finite G] in
theorem JData.toAParts {A R T J : Subgroup G} {p y : G} (hJ : JData A R T p J y) :
    AParts A R T p J :=
  ⟨hJ.le hJ.mem, hJ.ne_one, hJ.aPart_mem, hJ.aPart_le, hJ.centralizer_le⟩

theorem rightConjugate_perfectCore (H : Subgroup G) (x : G) :
    rightConjugate (CFSG.Quasithin.perfectCore H) x =
      CFSG.Quasithin.perfectCore (rightConjugate H x) :=
  CFSG.Quasithin.map_perfectCore _ H

omit [Finite G] in
theorem rightConjugate_centralizer_singleton (p h : G) :
    rightConjugate (centralizer ({p} : Set G)) h = centralizer ({h⁻¹ * p * h} : Set G) := by
  ext x
  rw [mem_rightConjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * (h⁻¹ * p * h) = h⁻¹ * ((h * x * h⁻¹) * p) * h := by group
      _ = h⁻¹ * (p * (h * x * h⁻¹)) * h := by rw [hx]
      _ = h⁻¹ * p * h * x := by group
  · intro hx
    calc h * x * h⁻¹ * p = h * (x * (h⁻¹ * p * h)) * h⁻¹ := by group
      _ = h * (h⁻¹ * p * h * x) * h⁻¹ := by rw [hx]
      _ = p * (h * x * h⁻¹) := by group

omit [Finite G] in
theorem mem_normalizer_inf {H K : Subgroup G} {x : G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hH hK ⊢
  intro y
  rw [mem_inf, mem_inf, hH y, hK y]

omit [Finite G] in
theorem mem_centralizer_of_noInvolutory {A X : Subgroup G} (hX : NoInvolutoryCentralizing A X)
    {k : ℕ} : ∀ {s : G}, s ∈ normalizer (A : Set G) → s ∈ centralizer (X : Set G) →
      s ^ 2 ^ k ∈ centralizer (A : Set G) → s ∈ centralizer (A : Set G) := by
  induction k with
  | zero =>
    intro s _ _ hk
    simpa using hk
  | succ k ih =>
    intro s hsN hsX hk
    have hs2 : s ^ 2 ∈ centralizer (A : Set G) := by
      refine ih (pow_mem hsN 2) (pow_mem hsX 2) ?_
      rw [← pow_mul, ← pow_succ']
      exact hk
    have hmap : A.map (MulAut.conj s).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp hsN
    let σ : MulAut ↥A := ((MulAut.conj s).subgroupMap A).trans (MulEquiv.subgroupCongr hmap)
    have hσ : ∀ x : ↥A, ((σ x : ↥A) : G) = s * x * s⁻¹ := fun x => rfl
    have hσσ : σ * σ = 1 := by
      ext x
      rw [MulAut.mul_apply, hσ, hσ, MulAut.one_apply]
      have h := mem_centralizer_iff.mp hs2 x x.2
      calc s * (s * ↑x * s⁻¹) * s⁻¹ = s ^ 2 * ↑x * (s ^ 2)⁻¹ := by rw [pow_two]; group
        _ = ↑x := by rw [← h, mul_inv_cancel_right]
    have hfix : ∀ x : ↥A, (x : G) ∈ X → σ x = x := by
      intro x hx
      apply Subtype.ext
      rw [hσ]
      have h := mem_centralizer_iff.mp hsX x hx
      rw [← h, mul_inv_cancel_right]
    have h1 := hX σ hσσ hfix
    rw [mem_centralizer_iff]
    intro a ha
    have h2 := congrArg (fun τ : MulAut ↥A => ((τ ⟨a, ha⟩ : ↥A) : G)) h1
    simp only [hσ, MulAut.one_apply] at h2
    calc a * s = s * a * s⁻¹ * s := by rw [h2]
      _ = s * a := by group

theorem isSylowOf_of_noInvolutory {A R X : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hX : NoInvolutoryCentralizing A X)
    {H : Subgroup G} (hRH : R ≤ H) (hHX : H ≤ centralizer (X : Set G))
    (hHR : H ≤ normalizer (R : Set G)) : IsSylowOf 2 R H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hRS⟩ := exists_isSylowOf_le hRH hR.isPGroup
  have hNA : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have h := Lemma36.normalizer_le hA hR 1
    rwa [rightConjugate_one, rightConjugate_one] at h
  have hSK : S ≤ centralizer (A : Set G) := by
    intro s hs
    obtain ⟨k, hk⟩ := (hS.isPGroup ⟨s, hs⟩)
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact mem_centralizer_of_noInvolutory hX (hNA (hHR (hS.le hs))) (hHX (hS.le hs))
      (by rw [hk']; exact one_mem _)
  have hSR := hR.eq_of_le hRS hSK hS.isPGroup
  rw [← hSR]
  exact hS

omit [Finite G] in
theorem conj_eq_rightConjugate (L : Subgroup G) (c : G) :
    Lemma34.conj L c = rightConjugate L c⁻¹ := by
  rw [rightConjugate, inv_inv]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

variable (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include h32 h4 h34

theorem inf_centralizer_eq {p : G} {J : Subgroup G} (hJ : AParts A R T p J) :
    A ⊓ centralizer (T : Set G) = A ⊓ centralizer ({p} : Set G) := by
  obtain ⟨t, ht, hρ⟩ := hJ.aPart_mem
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haT⟩ := mem_inf.mp ha
    refine mem_inf.mpr ⟨haA, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : Commute a t := (mem_centralizer_iff.mp haT t ht).symm
    have h2 : Commute a (t⁻¹ * p) := hc.commute_of_mem haA hρ
    have h3 := h1.mul_right h2
    rw [mul_inv_cancel_left] at h3
    exact h3.eq
  · intro a ha
    have haJ := hJ.centralizer_le ha
    refine mem_inf.mpr ⟨(mem_inf.mp ha).1, ?_⟩
    rw [mem_centralizer_iff]
    intro t' ht'
    obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart h32 h4 h34 ht'
    have hp'J := hJ.aPart_le t' ht' p' hp'A hρ'
    have h1 : Commute p' a := mem_centralizer_iff.mp haJ p' hp'J
    have h2 : Commute (t'⁻¹ * p')⁻¹ a := ((hc.commute_of_mem (mem_inf.mp ha).1 hρ').symm).inv_left
    have h3 := h1.mul_left h2
    rw [show p' * (t'⁻¹ * p')⁻¹ = t' by group] at h3
    exact h3.eq

theorem perfectCore_le (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) :
    CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) ≤
      CFSG.Quasithin.perfectCore (rightConjugate A g ⊓ centralizer (R : Set G)) := by
  obtain ⟨t, ht, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  have hle : A ⊓ centralizer (T : Set G) ≤ A ⊓ centralizer ({t} : Set G) :=
    inf_le_inf_left _ (centralizer_le (by simpa using ht))
  have h0 : CFSG.Quasithin.perfectCore (A ⊓ centralizer ({t} : Set G)) ≤
      admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) :=
    le_admResidual_of_perfect
      ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans le_sup_right)
      (CFSG.Quasithin.perfectCore_perfect _)
  have h2 := ((CFSG.Quasithin.perfectCore_mono hle).trans h0).trans
    (Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT ht ht1 hOut).1
  refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf h2 ?_)
    (CFSG.Quasithin.perfectCore_perfect _)
  refine (CFSG.Quasithin.perfectCore_le _).trans (inf_le_left.trans ?_)
  intro a ha
  rw [mem_centralizer_iff]
  intro r hr
  exact (hc.commute_of_mem ha hr).eq.symm

theorem perfectCore_eq (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) :
    CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) =
      CFSG.Quasithin.perfectCore (rightConjugate A g ⊓ centralizer (R : Set G)) := by
  refine le_antisymm (hc.perfectCore_le h32 h4 h34 hOut) ?_
  have h := hc.swap.perfectCore_le h32 h4 h34 hOut
  have h' := (rightConjugate_le_rightConjugate_iff (x := g)).mpr h
  rwa [rightConjugate_perfectCore, rightConjugate_perfectCore, rightConjugate_inf,
    rightConjugate_inf, centralizer_rightConjugate R, centralizer_rightConjugate T,
    rightConjugate_inv_rightConjugate, rightConjugate_inv_rightConjugate,
    rightConjugate_inv_rightConjugate] at h'

omit h4 h34 in
theorem orderOf_aPart_swap {p₂ : G} {J₂ : Subgroup G}
    (hJ₂ : AParts A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₂ J₂) :
    orderOf p₂ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, hρ⟩ := hJ₂.aPart_mem
  have hsw := hc.swap
  have hcomm : Commute t (t⁻¹ * p₂) := hsw.commute_T_R ht hρ
  have h2 : p₂ ^ 2 = 1 := by
    have hp : p₂ = t * (t⁻¹ * p₂) := by group
    rw [hp, hcomm.mul_pow, (hsw.elemT h32).2 t ht, (hsw.elemR h32).2 _ hρ, one_mul]
  exact orderOf_eq_prime h2 hJ₂.ne_one

theorem not_le_normalizer {D : ClassicalModel A}
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) {p p₂ : G}
    {J₂ : Subgroup G} (hJ : AParts A R T p (D.alpha p))
    (hJ₂ : AParts A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₂ J₂) {W Y : Subgroup G}
    (hW : LeviChoice D p W Y) (hrig : LeviRigid A p Y) (hTY : T ≤ centralizer (Y : Set G)) :
    ¬ centralizer (Y : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw, hAw⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hYA : Y ≤ A := hW.Y_le.trans inf_le_left
  have hpRA : g⁻¹ * p₂ * g ∈ rightConjugate A g := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hJ₂.mem
  have hpR2 : orderOf (g⁻¹ * p₂ * g) = 2 := by
    rw [show g⁻¹ * p₂ * g = g⁻¹ * p₂ * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq]
    exact hc.orderOf_aPart_swap h32 hJ₂
  have hYT : Y ≤ centralizer (T : Set G) := le_centralizer_iff.mp hTY
  have hNT : normalizer (T : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
    have h := Lemma36.normalizer_le hc.hyp hc.sylowR w
    rwa [← hw, hAw] at h
  have hYN : Y ≤ normalizer (rightConjugate A g : Set G) :=
    hYT.trans ((centralizer_le_normalizer _).trans hNT)
  have hRp : rightConjugate A g ⊓ centralizer (R : Set G) =
      rightConjugate A g ⊓ centralizer ({g⁻¹ * p₂ * g} : Set G) := by
    have h : rightConjugate (A ⊓ centralizer (rightConjugate R g⁻¹ : Set G)) g =
        rightConjugate (A ⊓ centralizer ({p₂} : Set G)) g := by
      rw [hc.swap.inf_centralizer_eq h32 h4 h34 hJ₂]
    rwa [rightConjugate_inf, rightConjugate_inf, centralizer_rightConjugate,
      rightConjugate_inv_rightConjugate, rightConjugate_centralizer_singleton] at h
  have heq : CFSG.Quasithin.perfectCore (A ⊓ centralizer ({p} : Set G)) =
      CFSG.Quasithin.perfectCore
        (rightConjugate A g ⊓ centralizer ({g⁻¹ * p₂ * g} : Set G)) := by
    rw [← hc.inf_centralizer_eq h32 h4 h34 hJ, hc.perfectCore_eq h32 h4 h34 hOut, hRp]
  have hNN := hrig g _ hpRA hpR2 hYN heq
  have hRY : R ≤ centralizer (Y : Set G) := hc.sylowR.le.trans (centralizer_le hYA)
  have hAgT : rightConjugate A g ≤ centralizer (T : Set G) := by
    rw [le_centralizer_iff, centralizer_rightConjugate]
    exact hc.sylowT.le
  have hQle : (R ⊔ T) ⊓ rightConjugate A g ≤ rightConjugate A g ⊓ centralizer (Y : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (sup_le hRY hTY))
  have hQN : rightConjugate A g ⊓ centralizer (Y : Set G) ≤
      normalizer (((R ⊔ T) ⊓ rightConjugate A g : Subgroup G) : Set G) := by
    intro c hc'
    obtain ⟨hcA, hcY⟩ := mem_inf.mp hc'
    have hcT := hAgT hcA
    have hcR : c ∈ normalizer (R : Set G) := hle (mem_inf.mpr ⟨hcY, hcT⟩)
    exact mem_normalizer_inf (mem_normalizer_sup hcR (centralizer_le_normalizer _ hcT))
      (Subgroup.le_normalizer hcA)
  have hQbot := hNN _ hQle (hc.isPGroup_sup.to_le inf_le_left) hQN
  have hRTA : R ≤ T ⊔ rightConjugate A g := by
    have h := (rightConjugate_le_rightConjugate_iff (x := g)).mpr (hc.swap.le_sup h32 h4 h34)
    rwa [rightConjugate_sup, rightConjugate_inv_rightConjugate,
      rightConjugate_inv_rightConjugate] at h
  obtain ⟨r, hr, hr1⟩ := R.bot_or_exists_ne_one.resolve_left hc.R_ne_bot
  have hTA : T ≤ normalizer (rightConjugate A g : Set G) :=
    le_centralizer_iff.mp hAgT |>.trans (centralizer_le_normalizer _)
  have hr' : r ∈ ((T ⊔ rightConjugate A g : Subgroup G) : Set G) := hRTA hr
  rw [coe_mul_of_left_le_normalizer_right T _ hTA] at hr'
  obtain ⟨t, ht, a, ha, hra⟩ := hr'
  have hra' : t * a = r := hra
  have haQ : a ∈ (R ⊔ T) ⊓ rightConjugate A g := by
    refine mem_inf.mpr ⟨?_, ha⟩
    have : a = t⁻¹ * r := by rw [← hra']; group
    rw [this]
    exact mul_mem (mem_sup_right (inv_mem ht)) (mem_sup_left hr)
  rw [hQbot, mem_bot] at haQ
  rw [haQ, mul_one] at hra'
  rw [← hra'] at hr hr1
  have : t ∈ R ⊓ T := mem_inf.mpr ⟨hr, ht⟩
  rw [hc.inf_eq_bot, mem_bot] at this
  exact hr1 this

theorem levi75_of_not_le
    {D : ClassicalModel A}
    (hch : Choice74 D R T g) {p : G} (hJ : AParts A R T p (D.alpha p)) {W Y : Subgroup G}
    (hW : LeviChoice D p W Y)
    (hnn : T ≤ centralizer (Y : Set G) →
      ¬ centralizer (Y : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G)) :
    Levi75 D T Y W (layerCentralizer A Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYA : Y ≤ A := hW.Y_le.trans inf_le_left
  have hYα : Y ≤ centralizer (D.alpha p : Set G) := hW.Y_le.trans inf_le_right
  have hLA := layerCentralizer_le A Y
  have hTY : T ≤ centralizer (Y : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart h32 h4 h34 ht
    have hp' := hJ.aPart_le t ht p' hp'A hρ'
    have h1 : Commute p' z := mem_centralizer_iff.mp (hYα hz) p' hp'
    have h2 : Commute (t⁻¹ * p')⁻¹ z := ((hc.commute_of_mem (hYA hz) hρ').symm).inv_left
    have h3 := h1.mul_left h2
    rw [show p' * (t⁻¹ * p')⁻¹ = t by group] at h3
    exact h3.eq.symm
  have hTRL : T ≤ R ⊔ layerCentralizer A Y := by
    intro t ht
    obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart h32 h4 h34 ht
    have hp' := hJ.aPart_le t ht p' hp'A hρ'
    rw [show t = p' * (t⁻¹ * p')⁻¹ by group]
    exact mul_mem (mem_sup_right (hW.alpha_le hp')) (mem_sup_left (inv_mem hρ'))
  have hTL : T ⊓ layerCentralizer A Y = ⊥ := by
    rw [eq_bot_iff, ← hch.inf_eq_bot]
    exact inf_le_inf_left T (hLA.trans inf_le_left)
  have hRY : R ≤ centralizer (Y : Set G) := hc.sylowR.le.trans (centralizer_le hYA)
  have hRL' : R ≤ centralizer (layerCentralizer A Y : Set G) :=
    hc.sylowR.le.trans (centralizer_le (hLA.trans inf_le_left))
  have hRL : IsSylowOf 2 R (centralizer (Y : Set G) ⊓
      centralizer (layerCentralizer A Y : Set G) ⊓ normalizer (R : Set G)) := by
    refine isSylowOf_of_noInvolutory hc.hyp hc.sylowR hW.noInv
      (le_inf (le_inf hRY hRL') (Subgroup.le_normalizer)) ?_ inf_le_right
    intro x hx
    obtain ⟨⟨hxY, hxL⟩, -⟩ := mem_inf.mp hx
    exact mem_centralizer_sup hxY hxL
  have hL2 : ∀ n : ℕ, 2 ^ n = Nat.card R →
      Nonempty (↥(layerCentralizer A Y) ≃* SL(2, GaloisField 2 n)) →
        ∀ c : G, ¬ Lemma34.conj R c ≤ layerCentralizer A Y := by
    intro _ _ _ c hle
    rw [conj_eq_rightConjugate] at hle
    exact hch.not_le c⁻¹ (hle.trans (hLA.trans inf_le_left))
  obtain ⟨hstd, hnn'⟩ := lemma38_of_le h4 h32 h34 hc.hyp hc.sylowR hYA hW.quasisimple hLA
    (normalizer_inf_le_normalizer_layerCentralizer A Y) hRL hTRL hTL hc.card_eq
    (hnn hTY) hL2
  exact ⟨hW.W_le, hYA, hTY, hLA, hW.W_type, hW.levi, hW.quasisimple, hW.oddCenter, hstd, hnn',
    rfl, hW.diag, hW.noInv, hW.outerFree, hW.sym⟩

theorem levi75_of
    {D : ClassicalModel A}
    (hch : Choice74 D R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    {p p₂ : G} {J₂ : Subgroup G} (hJ : AParts A R T p (D.alpha p))
    (hJ₂ : AParts A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₂ J₂) {W Y : Subgroup G}
    (hW : LeviChoice D p W Y) (hrig : LeviRigid A p Y) :
    Levi75 D T Y W (layerCentralizer A Y) :=
  hc.levi75_of_not_le h32 h4 h34 hch hJ hW
    (hc.not_le_normalizer h32 h4 h34 hOut hJ hJ₂ hW hrig)

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
