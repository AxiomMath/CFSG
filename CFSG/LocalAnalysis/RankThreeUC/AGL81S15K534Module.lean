module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Gen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Dim
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.SecModel
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.MS24
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement IsMulCommutative

section Small

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem zmod_two_add_self (x : W) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

theorem eq_of_sq_sub_one_eq_zero {φ : Module.End (ZMod 2) W} (h3 : φ * φ * φ = 1) {x : W}
    (h : (φ - 1) ((φ - 1) x) = 0) : φ x = x := by
  have h0 : φ (φ x) - φ x - (φ x - x) = 0 := by
    simpa only [LinearMap.sub_apply, Module.End.one_apply, map_sub] using h
  have e : φ (φ x) - φ x - (φ x - x) = φ (φ x) + x - (φ x + φ x) := by abel
  rw [e, zmod_two_add_self, sub_zero] at h0
  have h1 : φ (φ x) = x := by
    have h2 : φ (φ x) = -x := eq_neg_of_add_eq_zero_left h0
    rw [h2]
    exact neg_eq_of_add_eq_zero_right (zmod_two_add_self x)
  have h4 : (φ * φ * φ) x = x := by rw [h3]; rfl
  have h5 : φ (φ (φ x)) = x := by simpa [Module.End.mul_apply] using h4
  rw [h1] at h5
  exact h5

theorem exists_isMinSec_bot {G : Type*} [Group G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (H : Subgroup G) {U : Submodule (ZMod 2) W} (hU : U ≠ ⊥) (hUinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H U) :
    ∃ X : Submodule (ZMod 2) W, X ≤ U ∧ IsMinSec ρ H ⊥ X := by
  classical
  let S : Set (Submodule (ZMod 2) W) := {X | X ≤ U ∧ X ≠ ⊥ ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H X}
  have hex : ∃ n, ∃ X ∈ S, Module.finrank (ZMod 2) X = n := ⟨_, U, ⟨le_rfl, hU, hUinv⟩, rfl⟩
  obtain ⟨X, hXS, hXn⟩ := Nat.find_spec hex
  have hmin : ∀ Y ∈ S, Nat.find hex ≤ Module.finrank (ZMod 2) Y := fun Y hY =>
    Nat.find_min' hex ⟨Y, hY, rfl⟩
  have h₀ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H ⊥ := fun _ _ u hu => by
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  refine ⟨X, hXS.1, h₀, hXS.2.2, bot_lt_iff_ne_bot.2 hXS.2.1, fun Z hZ _ hZX => ?_⟩
  by_cases hZ0 : Z = ⊥
  · exact Or.inl hZ0
  · right
    have hZS : Z ∈ S := ⟨hZX.trans hXS.1, hZ0, hZ⟩
    have h1 := hmin Z hZS
    exact Submodule.eq_of_le_of_finrank_le hZX (by rw [hXn]; exact h1)

end Small

section Data

theorem isQuasisimple_of_open_native {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hc, hs⟩ := h
  have hperf : Group.IsPerfect Q := ⟨hc⟩
  refine ⟨hperf, hs, ?_⟩
  by_contra hne
  push Not at hne
  have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := hne
  have hbot : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact (hcomm b a)
  have htop : commutator (Q ⧸ Subgroup.center Q) = ⊤ := by
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center Q))) hc
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    rw [_root_.commutator_def]
    exact h2
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hs.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  have hx' : x ∈ commutator (Q ⧸ Subgroup.center Q) := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [hbot, Subgroup.mem_bot] at hx'
  exact hx hx'

theorem data_of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (hq : CFSG.Open.IsQuasisimple L) (hZ : Nat.card (Subgroup.center L) = 3)
    (e6 : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6)) :
    CFSG.Open.IsQuasisimple K ∧ Nat.card (Subgroup.center K) = 3 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hc, hs⟩ := hq
  have hc' : (Subgroup.center K).map e.toMonoidHom = Subgroup.center L := Subgroup.map_center_eq e
  let f : (K ⧸ Subgroup.center K) ≃* (L ⧸ Subgroup.center L) :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center L) e hc'
  have hperfL : Group.IsPerfect L := ⟨hc⟩
  have hperfK : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨⟨hperfK.commutator_eq_top, f.isSimpleGroup⟩, ?_, ⟨f.trans e6⟩⟩
  have h1 : Nat.card ((Subgroup.center K).map e.toMonoidHom) = Nat.card (Subgroup.center K) :=
    Subgroup.card_map_of_injective e.injective
  rw [← h1, hc']
  exact hZ

end Data

section Triv

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem secTrivial_of_commutator {ρ : Representation (ZMod 2) G W} {L B : Subgroup G}
    (hLB : ⁅L, B⁆ = L) {X U : Submodule (ZMod 2) W}
    (hX : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) X) (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U)
    (hBtriv : ∀ b ∈ B, ∀ y ∈ U, ρ b y - y ∈ X) :
    ∀ l ∈ L, ∀ y ∈ U, ρ l y - y ∈ X := by
  have hcancel : ∀ (a : G) (y : W), ρ a⁻¹ (ρ a y) = y := fun a y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  let S₀ : Subgroup G :=
    { carrier := {k | k ∈ L ⊔ B ∧ ∀ y ∈ U, ρ k y - y ∈ X}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨(L ⊔ B).mul_mem ha.1 hb.1, fun y hy => ?_⟩
        have e : ρ (a * b) y - y = ρ a (ρ b y - y) + (ρ a y - y) := by
          simp only [map_mul, Module.End.mul_apply, map_sub]
          abel
        rw [e]
        exact X.add_mem (hX a ha.1 _ (hb.2 y hy)) (ha.2 y hy)
      one_mem' := ⟨(L ⊔ B).one_mem, fun y _ => by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨(L ⊔ B).inv_mem ha.1, fun y hy => ?_⟩
        have e : ρ a⁻¹ y - y = -(ρ a⁻¹ (ρ a y - y)) := by
          rw [map_sub, hcancel]
          abel
        rw [e]
        exact X.neg_mem (hX a⁻¹ ((L ⊔ B).inv_mem ha.1) _ (ha.2 y hy)) }
  have hconj : ∀ h ∈ L ⊔ B, ∀ k ∈ S₀, h * k * h⁻¹ ∈ S₀ := by
    intro h hh k hk
    refine ⟨(L ⊔ B).mul_mem ((L ⊔ B).mul_mem hh hk.1) ((L ⊔ B).inv_mem hh), fun y hy => ?_⟩
    have e : ρ (h * k * h⁻¹) y - y = ρ h (ρ k (ρ h⁻¹ y) - ρ h⁻¹ y) := by
      have e1 : ρ h (ρ h⁻¹ y) = y := by
        have := hcancel h⁻¹ y
        rwa [inv_inv] at this
      simp only [map_mul, Module.End.mul_apply, map_sub]
      rw [e1]
    rw [e]
    exact hX h hh _ (hk.2 _ (hU h⁻¹ ((L ⊔ B).inv_mem hh) y hy))
  have hcomm : ⁅L, B⁆ ≤ S₀ := by
    rw [Subgroup.commutator_le]
    intro l hl b hb
    have hbS : b ∈ S₀ := ⟨Subgroup.mem_sup_right hb, hBtriv b hb⟩
    have h1 : l * b * l⁻¹ ∈ S₀ := hconj l (Subgroup.mem_sup_left hl) b hbS
    have h2 : (l * b * l⁻¹) * b⁻¹ ∈ S₀ := S₀.mul_mem h1 (S₀.inv_mem hbS)
    have e : ⁅l, b⁆ = (l * b * l⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact h2
  rw [hLB] at hcomm
  intro l hl y hy
  exact (hcomm hl).2 y hy

end Triv

section Setup

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_q3a6_section [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ (B : Subgroup G) (X : Submodule (ZMod 2) W) (z : ↥L),
      z ∈ Subgroup.center ↥L ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧ (∀ b ∈ B, b ^ 2 = 1) ∧
      (∀ a ∈ B, ∀ c ∈ B, a * c = c * a) ∧ ⁅L, B⁆ = L ∧
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤) ∧
      (∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ u ∈ commOn ρ L ⊤, ρ b u = u) ∧
      2 ^ secCod ρ B ⊥ (commOn ρ L ⊤) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        Nat.card B ∧
      commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ ∧
      X ≤ commOn ρ L ⊤ ∧ IsMinSec ρ (L ⊔ B) ⊥ X ∧ (∀ x ∈ X, ρ (z : G) x = x → x = 0) := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hqn : CFSG.IsQuasisimple ↥L := isQuasisimple_of_open_native hq
  obtain ⟨z0, hz0, hz01⟩ := exists_mem_center_ne_one hZ
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hbot : commutator ↥L = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _ b _
      exact hcon b a
    rw [hq.1] at hbot
    have : z0 ∈ (⊥ : Subgroup ↥L) := by rw [← hbot]; exact Subgroup.mem_top z0
    exact hz01 (Subgroup.mem_bot.1 this)
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hLnab
    apply hab
    have h1 : ∀ k : ↥L, k = 1 := fun k => by
      apply Subtype.ext
      apply hρ
      ext v
      rw [Subgroup.coe_one, map_one, Module.End.one_apply]
      exact (h k.2).2 v Submodule.mem_top
    rw [h1 a, h1 b]
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbest, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hb
  set U := commOn ρ L ⊤ with hU
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩)
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc => hAc a (hBA ha) c (hBA hc)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hLB : ⁅L, B⁆ = L := by
    refine commutator_eq_of_ne_bot hqn hBN fun hbot => ?_
    obtain ⟨b, hb, hbc⟩ := Set.not_subset.mp hBU
    obtain ⟨k, hk, u, -, hne⟩ := hmove b hb hbc
    apply hne
    have h1 : ⁅k, b⁆ ∈ ⁅L, B⁆ := Subgroup.commutator_mem_commutator hk hb
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    rw [← Module.End.mul_apply, ← map_mul, ← h1, map_mul, Module.End.mul_apply]
  have hUU : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ := commOn_commOn_eq hA2 hAN hLA
  have hcen := ms24_comm ρ hBN hLB hUU hquad
  have hbudU := two_pow_secCod_le hbest hcen
  set g : G := (z0 : G) with hg
  have hgL : g ∈ L := z0.2
  have hg1 : g ≠ 1 := fun h => hz01 (Subtype.ext h)
  have hg3 : g * g * g = 1 := by
    have h3 : z0 ^ 3 = 1 := pow_three_eq_one_of_mem_center hZ hz0
    have := congrArg Subtype.val h3
    simpa [pow_succ, mul_assoc] using this
  have hρg3 : ρ g * ρ g * ρ g = 1 := by
    rw [← map_mul, ← map_mul, hg3, map_one]
  have hUg : ∀ y ∈ U, ρ g y ∈ U := fun y hy => hUinv g (Subgroup.mem_sup_left hgL) y hy
  have hmemU : ∀ w : W, ρ g w - w ∈ U := fun w =>
    Submodule.subset_span ⟨g, hgL, w, Submodule.mem_top, rfl⟩
  have hzU : ∃ u ∈ U, ρ g u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hg1
    apply hρ
    ext w
    have h0 : (ρ g - 1) ((ρ g - 1) w) = 0 := by
      simp only [LinearMap.sub_apply, Module.End.one_apply]
      rw [hcon _ (hmemU w), sub_self]
    rw [map_one, Module.End.one_apply]
    exact eq_of_sq_sub_one_eq_zero hρg3 h0
  set U1 : Submodule (ZMod 2) W := U.map (ρ g - 1) with hU1
  have hU1ne : U1 ≠ ⊥ := by
    obtain ⟨u, hu, hne⟩ := hzU
    intro h
    have : (ρ g - 1) u ∈ U1 := Submodule.mem_map_of_mem hu
    rw [h, Submodule.mem_bot] at this
    apply hne
    simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using this
  have hU1U : U1 ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact U.sub_mem (hUg u hu) hu
  have hLBN : L ⊔ B ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hU1inv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U1 := by
    intro h hh v hv
    obtain ⟨u, hu, rfl⟩ := hv
    have e : ρ h (ρ g u - u) = ρ (h * g * h⁻¹) (ρ h u) - ρ h u := by
      simp only [map_mul, Module.End.mul_apply, map_sub]
      rw [rep_inv_apply_apply ρ h]
    obtain ⟨w, hw, hwe⟩ := exists_center_of_conj (hLBN hh) hz0
    have hUh : ρ h u ∈ U := hUinv h hh u hu
    change ρ h (ρ g u - u) ∈ U1
    rw [e, ← hwe]
    rcases mem_center_cases hZ hz0 hz01 hw with h1 | h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      exact ⟨ρ h u, hUh, rfl⟩
    · rw [h1]
      refine ⟨ρ g (ρ h u) + ρ h u, U.add_mem (hUg _ hUh) hUh, ?_⟩
      have e2 : ((z0 ^ 2 : ↥L) : G) = g * g := by rw [pow_two]; rfl
      rw [e2]
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, map_mul,
        Module.End.mul_apply]
      abel
  have hU1fix : ∀ v ∈ U1, ρ g v = v → v = 0 := by
    rintro _ ⟨u, hu, rfl⟩ hfix
    have h0 : (ρ g - 1) ((ρ g - 1) u) = 0 := by
      simp only [LinearMap.sub_apply, Module.End.one_apply] at hfix ⊢
      rw [hfix, sub_self]
    have := eq_of_sq_sub_one_eq_zero hρg3 h0
    simp only [LinearMap.sub_apply, Module.End.one_apply, this, sub_self]
  obtain ⟨X, hXU1, hXmin⟩ := exists_isMinSec_bot ρ (L ⊔ B) hU1ne hU1inv
  have hXU : X ≤ U := hXU1.trans hU1U
  have hXne : X ≠ ⊥ := ne_of_gt hXmin.2.2.1
  exact ⟨B, X, z0, hz0, hBN, hB2, hBc, hLB, hUinv, hcen, hbudU, hUU, hXU, hXmin,
    fun x hx => hU1fix x (hXU1 hx)⟩

end Setup

section Count

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem q3a6_finrank_of_section [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e6 : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6))
    {B : Subgroup G} {X : Submodule (ZMod 2) W} {z0 : ↥L}
    (hz0 : z0 ∈ Subgroup.center ↥L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a) (hLB : ⁅L, B⁆ = L)
    (hUinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤))
    (hcen : ∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ u ∈ commOn ρ L ⊤, ρ b u = u)
    (hbudU : 2 ^ secCod ρ B ⊥ (commOn ρ L ⊤) *
      Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card B)
    (hUU : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤)
    (hXU : X ≤ commOn ρ L ⊤) (hXmin : IsMinSec ρ (L ⊔ B) ⊥ X)
    (hXfix : ∀ x ∈ X, ρ (z0 : G) x = x → x = 0) :
    Module.finrank (ZMod 2) ↥(commOn ρ L ⊤) = 6 := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  set U := commOn ρ L ⊤ with hU
  set g : G := (z0 : G) with hg
  have hXne : X ≠ ⊥ := ne_of_gt hXmin.2.2.1
  set H := L ⊔ B with hH
  have hLH : L ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  set Q := SecQ ⊥ X with hQ
  set σ := secRep ρ H hXmin.1 hXmin.2.1 with hσ
  set σu := σ.asGroupHom with hσu
  have hσu_apply : ∀ h : ↥H, ((σu h : (Module.End (ZMod 2) Q)ˣ) : Module.End (ZMod 2) Q) = σ h :=
    fun h => Representation.asGroupHom_apply σ h
  obtain ⟨hQnt, hirrQ⟩ := secRep_irreducible hXmin
  have : Finite Q := Module.finite_of_finite (ZMod 2)
  set σL : ↥L →* (Module.End (ZMod 2) Q)ˣ := σu.comp (Subgroup.inclusion hLH) with hσL
  set σB : ↥B →* (Module.End (ZMod 2) Q)ˣ := σu.comp (Subgroup.inclusion hBH) with hσB
  have hσLz : σL z0 ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hx0⟩ : ∃ x ∈ X, x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hXne (eq_bot_iff.2 fun x hx => (Submodule.mem_bot _).2 (hcon x hx))
    have h2 := congrArg (fun u : (Module.End (ZMod 2) Q)ˣ =>
      (u : Module.End (ZMod 2) Q) (Submodule.Quotient.mk ⟨x, hx⟩)) h1
    simp only [hσL, MonoidHom.comp_apply, Units.val_one, Module.End.one_apply] at h2
    rw [hσu_apply, hσ, secRep_mk, Submodule.Quotient.eq] at h2
    have h3 : ρ g x - x = 0 := by
      have h4 := h2
      rw [Submodule.mem_comap, Submodule.mem_bot] at h4
      exact h4
    exact hx0 (hXfix x hx (sub_eq_zero.1 h3))
  have hσLinj : Function.Injective σL := injective_of_center_ne_one hq hZ σL ⟨z0, hz0, hσLz⟩
  set Y := σL.range with hY
  set A' := σB.range with hA'
  set eY : ↥Y ≃* ↥L := (MonoidHom.ofInjective hσLinj).symm with heY
  obtain ⟨hqY, hZY, ⟨e6Y⟩⟩ := data_of_mulEquiv eY hq hZ e6
  have hconjB : ∀ (b : ↥B) (k : ↥L), σB b * σL k * (σB b)⁻¹ =
      σL ⟨(b : G) * k * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBN b.2) k).mp k.2⟩ := by
    intro b k
    simp only [hσL, hσB, MonoidHom.comp_apply, ← map_inv, ← map_mul]
    rfl
  have hA'N : A' ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) Q)ˣ) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, (hconjB b k).symm⟩
    · rintro ⟨k, hk⟩
      have hb' : (b : G)⁻¹ ∈ B := B.inv_mem b.2
      have h1 := hconjB ⟨(b : G)⁻¹, hb'⟩ k
      have h2 : σB ⟨(b : G)⁻¹, hb'⟩ = (σB b)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h2, inv_inv, hk] at h1
      refine ⟨⟨(b : G)⁻¹ * (k : G) * ((b : G)⁻¹)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBN hb') k).mp k.2⟩, ?_⟩
      rw [← h1]
      group
  have hHle : ∀ h : ↥H, σu h ∈ Y ⊔ A' := by
    intro h
    have hmem : (h : G) ∈ ((L ⊔ B : Subgroup G) : Set G) := h.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hBN] at hmem
    obtain ⟨l, hl, b, hb, hlb⟩ := hmem
    have e : h = Subgroup.inclusion hLH ⟨l, hl⟩ * Subgroup.inclusion hBH ⟨b, hb⟩ :=
      Subtype.ext hlb.symm
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨l, hl⟩, rfl⟩)
      (Subgroup.mem_sup_right ⟨⟨b, hb⟩, rfl⟩)
  have hirr : ∀ N : Submodule (ZMod 2) Q,
      (∀ d ∈ Y ⊔ A', ∀ v ∈ N, (d : Module.End (ZMod 2) Q) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    refine hirrQ N fun h q hq => ?_
    have h1 := hN _ (hHle h) q hq
    rwa [hσu_apply] at h1
  have hA1 : A' ≠ ⊥ := by
    intro hbot
    apply hσLz
    have hBtriv : ∀ b : ↥B, σB b = 1 := fun b => by
      have h1 : σB b ∈ A' := ⟨b, rfl⟩
      rw [hbot] at h1
      exact Subgroup.mem_bot.mp h1
    have hle' : ⁅L, B⁆ ≤ (σL.ker).map L.subtype := by
      rw [Subgroup.commutator_le]
      intro l hl b hb
      have hmem : ⁅l, b⁆ ∈ L := by
        rw [commutatorElement_def]
        have h1 : b * l⁻¹ * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hBN hb) l⁻¹).mp
          (L.inv_mem hl)
        have e : l * b * l⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) := by group
        rw [e]
        exact L.mul_mem hl h1
      refine ⟨⟨⁅l, b⁆, hmem⟩, ?_, rfl⟩
      show σL ⟨⁅l, b⁆, hmem⟩ = 1
      have e : Subgroup.inclusion hLH ⟨⁅l, b⁆, hmem⟩ =
          ⁅Subgroup.inclusion hLH ⟨l, hl⟩, Subgroup.inclusion hBH ⟨b, hb⟩⁆ := Subtype.ext rfl
      have hb1 : σu (Subgroup.inclusion hBH ⟨b, hb⟩) = 1 := hBtriv ⟨b, hb⟩
      rw [hσL, MonoidHom.comp_apply, e]
      simp only [commutatorElement_def, map_mul, map_inv, hb1]
      group
    rw [hLB] at hle'
    obtain ⟨k', hk', hkk'⟩ := hle' z0.2
    have e : k' = z0 := Subtype.ext hkk'
    rw [← e]
    exact hk'
  have hAc' : ∀ a ∈ A', ∀ c ∈ A', a * c = c * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ a.2 _ c.2)
  have hA2' : ∀ a ∈ A', a ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have h1 : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hB2 _ a.2)
    rw [h1, map_one]
  have hkerB : ∀ b : ↥B, σB b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro b
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h2 := hconjB b ⟨k, hk⟩
      rw [h1, one_mul, inv_one, mul_one] at h2
      have h3 : k = (b : G) * k * (b : G)⁻¹ := congrArg Subtype.val (hσLinj h2)
      calc k * (b : G) = (b : G) * k * (b : G)⁻¹ * (b : G) := by rw [← h3]
        _ = (b : G) * k := by group
    · intro h1
      apply Units.ext
      refine LinearMap.ext fun q => ?_
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [Units.val_one, Module.End.one_apply, hσB, MonoidHom.comp_apply, hσu_apply, hσ,
          secRep_mk]
        congr 1
        apply Subtype.ext
        exact hcen b b.2 (fun k hk => (Subgroup.mem_centralizer_iff.mp h1 k hk).symm) z
          (hXU z.2)
  have hcardA : Nat.card A' * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = Nat.card B := by
    have h1 := Subgroup.index_mul_card σB.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card σB.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.card_congr
        { toFun := fun b => ⟨b.1.1, b.1.2, (hkerB b.1).mp b.2⟩
          invFun := fun c => ⟨⟨c.1, c.2.1⟩, (hkerB _).mpr c.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [← h2]
    exact h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAfin : Finite ↥A' := Finite.of_surjective _ σB.rangeRestrict_surjective
  have hAp : IsPGroup 2 ↥A' := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2' a a.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hfixeq : fixSub σ (B.subgroupOf H) = CFSG.LocalAnalysis.CommutingFactor.fixedSub A' := by
    ext q
    rw [mem_fixSub, CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub]
    constructor
    · rintro h _ ⟨b, rfl⟩
      rw [hσB, MonoidHom.comp_apply, hσu_apply]
      exact h _ (Subgroup.mem_subgroupOf.mpr b.2)
    · intro h b hb
      have h1 := h (σB ⟨b, Subgroup.mem_subgroupOf.mp hb⟩) ⟨_, rfl⟩
      rw [hσB, MonoidHom.comp_apply, hσu_apply] at h1
      exact h1
  have hsc0 := secCod_eq hXmin.1 hXmin.2.1 (bot_le : (⊥ : Submodule (ZMod 2) W) ≤ X) hBH
  rw [← hσ, hfixeq] at hsc0
  have hsc : secCod ρ B ⊥ X = finrank (ZMod 2) Q -
      finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub A') := hsc0
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hsU : secCod ρ B ⊥ U ≤ m := by
    have h1 : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [← hm, hcardA]
      exact hbudU
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hcpos)
  have hsX : secCod ρ B ⊥ X ≤ secCod ρ B ⊥ U :=
    secCod_mono_sub (le_refl _) hXmin.2.2.1.le hXU (isInvariant_mono le_sup_right hXmin.1)
      (isInvariant_mono le_sup_right hXmin.2.1)
  have := hQnt
  obtain ⟨r', m', hr'card, -, -, hmr, hdimle⟩ :=
    q3a6_short_gen hirr hA'N hqY hZY e6Y hA1 hAc' hA2'
  have hrm : r' = m := Nat.pow_right_injective le_rfl (hr'card.symm.trans hm)
  rw [hrm] at hmr
  have hdimle' : finrank (ZMod 2) Q ≤ m' * secCod ρ B ⊥ X := by
    rw [hsc]
    exact hdimle
  have hdim6 : 6 ≤ finrank (ZMod 2) Q := six_le_finrank_of_dvd_27 σL hσLinj (dvd_27_card hZ e6)
  have hdimQ : finrank (ZMod 2) Q = 6 := by
    have h1 : finrank (ZMod 2) Q ≤ m' * m :=
      hdimle'.trans (Nat.mul_le_mul_left _ (hsX.trans hsU))
    omega
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h0 | h0
    · rw [h0, zero_mul] at hdimle'
      omega
    · exact h0
  have hsXm : secCod ρ B ⊥ X = m := by
    have h2 : secCod ρ B ⊥ X ≤ m := hsX.trans hsU
    by_contra hne
    have h3 : secCod ρ B ⊥ X < m := lt_of_le_of_ne h2 hne
    have h4 : m' * secCod ρ B ⊥ X < m' * m := Nat.mul_lt_mul_of_pos_left h3 hm'pos
    omega
  have hsc00 : secCod ρ B X U = 0 := by
    have := secCod_add_le (ρ := ρ) (B := B) (bot_le : (⊥ : Submodule (ZMod 2) W) ≤ X) hXU
      (isInvariant_mono le_sup_right hXmin.2.1)
    omega
  have hBtriv : ∀ b ∈ B, ∀ y ∈ U, ρ b y - y ∈ X := by
    intro b hb y hy
    have hle : finrank (ZMod 2) ↥(relFix ρ B X U) ≤ finrank (ZMod 2) ↥U :=
      Submodule.finrank_mono relFix_le
    have h1 : finrank (ZMod 2) ↥U ≤ finrank (ZMod 2) ↥(relFix ρ B X U) := by
      unfold secCod at hsc00
      omega
    have h2 : relFix ρ B X U = U := Submodule.eq_of_le_of_finrank_le relFix_le h1
    have : y ∈ relFix ρ B X U := by rw [h2]; exact hy
    exact this.2 b hb
  have hLtriv := secTrivial_of_commutator hLB hXmin.2.1 hUinv hBtriv
  have hcommLU : commOn ρ L U ≤ X := by
    rw [commOn, Submodule.span_le]
    rintro _ ⟨k, hk, u, hu, rfl⟩
    exact hLtriv k hk u hu
  have hUX : U ≤ X := by
    have h1 : commOn ρ L U = U := hUU
    rw [← h1]
    exact hcommLU
  have hUXeq : U = X := le_antisymm hUX hXU
  have h1 := finrank_secQ (Z₀ := (⊥ : Submodule (ZMod 2) W)) (Z₁ := X) bot_le
  rw [finrank_bot] at h1
  have h2 : finrank (ZMod 2) (SecQ (⊥ : Submodule (ZMod 2) W) X) = 6 := hdimQ
  rw [hUXeq]
  omega

end Count

section Main

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem q3a6_finrank_commOn [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e6 : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6))
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) :
    Module.finrank (ZMod 2) ↥(commOn ρ L ⊤) = 6 := by
  obtain ⟨B, X, z0, hz0, hBN, hB2, hBc, hLB, hUinv, hcen, hbudU, hUU, hXU, hXmin, hXfix⟩ :=
    exists_q3a6_section ρ hρ hq hZ hA2 hAN hLA hb
  exact q3a6_finrank_of_section ρ hρ hq hZ e6 hz0 hBN hB2 hBc hLB hUinv hcen hbudU hUU hXU hXmin
    hXfix

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof
