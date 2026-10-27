module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeLayer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThree

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.Balance

section Layers

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

@[expose] def IsPLayer (p : ℕ) (E : Subgroup (MulAut K)) (T : Subgroup K) : Prop :=
  ∃ e ∈ E, e ≠ 1 ∧ T ≤ fixSub e ∧ (∀ f ∈ fixSub e, ∀ t ∈ T, f * t * f⁻¹ ∈ T) ∧
    CFSG.IsQuasisimple T ∧ ¬ Nat.Coprime p (Nat.card T)

theorem localDeltaIn_eq_bot_of_layers_faithful (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H E : Subgroup (MulAut K)} (hH : innerAut K ≤ H) (hE : ∃ x ∈ E, x ≠ 1)
    (hfaith : ∀ g : MulAut K, Nat.Coprime p (orderOf g) → (∀ d ∈ E, g * d = d * g) →
      (∀ T, IsPLayer p E T → ∀ t ∈ T, g t = t) → g = 1) :
    localDeltaIn p H E = ⊥ := by
  obtain ⟨x, hxE, hx1⟩ := hE
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  refine hfaith g (coprime_orderOf_of_mem_localDeltaIn hp hg hxE hx1)
    (fun d hd => commute_of_mem_localDeltaIn hg hd) ?_
  rintro T ⟨e, he, he1, hTF, hTn, hTq, hTp⟩ t ht
  have hTC : T.map (MulAut.conj : K →* MulAut K) ≤
      H ⊓ Subgroup.centralizer ({e} : Set (MulAut K)) := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hH ⟨s, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (conj_commute_of_mem_fixSub (hTF hs)).symm
  exact mem_fixSub.1 (le_fixSub_of_component hp hinj hg he he1 hTC
    (isComponent_conj_of_fieldCore hH hTF hTn hTq hinj) hTp ht)

end Layers

theorem localDeltaIn_eq_bot_of_core_bot {M : Type*} [Group M] {p : ℕ} {H D : Subgroup M} {d : M}
    (hd : d ∈ D) (hd1 : d ≠ 1)
    (h : GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set M)) = ⊥) :
    localDeltaIn p H D = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  have := le_core_of_mem_localDeltaIn hg hd hd1
  rwa [h] at this

section Core

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem noNormalPPrime_of_core_eq_bot {L : Subgroup K} (h : GLAPPrimeCoreOf p L = ⊥) :
    NoNormalPPrime p L := by
  intro N hNL hNn hcop
  have := le_gLAPPrimeCoreOf_of_normal' (p := p) hNL hNn hcop
  rw [h] at this
  exact le_bot_iff.1 this

theorem map_mem_centralizerOf {e h : MulAut K} (hhe : h * e = e * h) {x : K}
    (hx : x ∈ centralizerOf e) : h x ∈ centralizerOf e := by
  rw [mem_centralizerOf] at hx ⊢
  rw [← mul_conj_mul_inv]
  have hc : Commute (MulAut.conj x) e := hx
  have hh : Commute h e := hhe
  exact ((hh.mul_left hc).mul_left hh.inv_left).eq

theorem localDeltaIn_eq_bot_of_closure_centralizers (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {H D : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H)
    (hgen : Subgroup.closure {x : K | ∃ d ∈ D, d ≠ 1 ∧ x ∈ centralizerOf d} = ⊤)
    (hcore : ∀ d ∈ D, d ≠ 1 → NoNormalPPrime p (centralizerOf d)) :
    localDeltaIn p H D = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot, ← fixSub_eq_top_iff, eq_top_iff, ← hgen]
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  obtain ⟨d, hd, hd1, hxd⟩ := hx
  exact le_fixSub_of_noNormalPPrime hp hinj (le_core_of_mem_localDeltaIn hg hd hd1)
    (L := centralizerOf d) (fun y _ => hH ⟨y, rfl⟩) (fun _ hy => mem_centralizerOf.1 hy)
    (fun _ _ hhe _ hy => map_mem_centralizerOf hhe hy) (hcore d hd hd1) hxd

end Core

@[expose] def PlaneBalanceIn (p : ℕ) (K : Type*) [Group K] (A : Subgroup (MulAut K)) : Prop :=
  ∀ D : Subgroup (MulAut K), D ≤ A → IsElemAbelian p D → Nat.card D = p ^ 2 →
    ∀ H : Subgroup (MulAut K), innerAut K ≤ H → localDeltaIn p H D = ⊥

@[expose] def OuterGood (p : ℕ) {K : Type*} [Group K] (x : MulAut K) : Prop :=
  FieldCoreAt p x ∨ CoreFreeAt p x

theorem isLocallyBalancedAbs_two_of_kinds {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (Idg : Subgroup (MulAut K)) (hdg : PlaneBalanceIn p K Idg)
    (hout : ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 2 → ¬ D ≤ Idg →
      ∃ x ∈ D, x ∉ Idg ∧ OuterGood p x) :
    IsLocallyBalancedAbs p 2 K := by
  intro D hD hcard H hH _
  by_cases hDin : D ≤ Idg
  · exact hdg D hDin hD hcard H hH
  · obtain ⟨x, hxD, hxI, hx⟩ := hout D hD hcard hDin
    have hx1 : x ≠ 1 := fun h => hxI (by rw [h]; exact one_mem _)
    rcases hx with hfc | hcf
    · exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hxD hx1 hfc
    · exact localDeltaIn_eq_bot_of_coreFree hp hinj hH hxD hx1 hcf

theorem innerPlaneBalance_three_of_innerOneBalanceThree {K : Type*} [Group K]
    (h : InnerOneBalanceThree K) : InnerPlaneBalance 3 K := by
  intro E hEin hE hEc H hH
  have hne : ∃ d ∈ E, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hall
    rw [this, Subgroup.card_bot] at hEc
    norm_num at hEc
  obtain ⟨d, hdE, hd1⟩ := hne
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree h hE hdE (hEin hdE) hd1 hH

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
