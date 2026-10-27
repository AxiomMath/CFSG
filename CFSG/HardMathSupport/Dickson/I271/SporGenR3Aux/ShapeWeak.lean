module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.Yardstones.Md0ec50421ce4

@[expose] def ShapeRkAt' (p : ℕ) (Good Rk : ∀ (T : Type) [Group T], Prop) {Q : Type} [Group Q]
    (k : Q) : Prop :=
  (∀ J : Subgroup Q, ¬ GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J) ∨
    ∃ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J ∧
      (∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I → I = J) ∧
      Good (PSimple p J) ∧ Rk (PQuot p J)

@[expose] def CentShapeRk' (p : ℕ) (Good Rk : ∀ (T : Type) [Group T], Prop) (Q : Type) [Group Q] :
    Prop :=
  ∀ k : Q, k ≠ 1 → k ^ p = 1 → ShapeRkAt' p Good Rk k

section Weaken

variable {Q : Type} [Group Q] [Finite Q]

theorem ShapeRkAt.toWeak {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q}
    (h : ShapeRkAt p Good Rk k) : ShapeRkAt' p Good Rk k :=
  Or.imp_left (fun hc _ hJ => no_glaPComponent_of_pConstrainedShape hp hc hJ) h

theorem CentShapeRk.toWeak {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (h : CentShapeRk p Good Rk Q) : CentShapeRk' p Good Rk Q :=
  fun k hk1 hkp => (h k hk1 hkp).toWeak hp

end Weaken

section Transport

variable {Q Q' : Type} [Group Q] [Finite Q] [Group Q']

theorem ShapeRkAt'.of_equiv {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') [Finite Q']
    (e : Q ≃* Q') {k : Q} (h : ShapeRkAt' p Good Rk k) : ShapeRkAt' p Good Rk (e k) := by
  have hmap : (Subgroup.centralizer ({k} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({e k} : Set Q') := map_centralizer_singleton e k
  have hmap' : (Subgroup.centralizer ({e k} : Set Q')).map e.symm.toMonoidHom =
      Subgroup.centralizer ({k} : Set Q) := by
    rw [map_centralizer_singleton e.symm (e k), MulEquiv.symm_apply_apply]
  rcases h with hno | ⟨J, hJ, hu, hG, hR⟩
  · left
    intro J' hJ'
    have h1 := glaPComponent_map_equiv hp e.symm hJ'
    rw [hmap'] at h1
    exact hno _ h1
  · right
    refine ⟨J.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rw [← hmap]
      exact glaPComponent_map_equiv hp e hJ
    · intro I' hI'
      have h1 := glaPComponent_map_equiv hp e.symm hI'
      rw [hmap'] at h1
      have h2 := hu _ h1
      rw [← h2, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [this, Subgroup.map_id]
    · exact hGood _ _ (pSimpleEquiv p (e.subgroupMap J)) hG
    · exact hRk _ _ (pQuotEquiv p (e.subgroupMap J)) hR

theorem CentShapeRk'.of_equiv {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') [Finite Q']
    (e : Q ≃* Q') (h : CentShapeRk' p Good Rk Q) : CentShapeRk' p Good Rk Q' := by
  intro k' hk1 hkp
  set k : Q := e.symm k' with hk
  have hk1' : k ≠ 1 := fun h1 => hk1 (by simpa [hk] using congrArg e h1)
  have hkp' : k ^ p = 1 := by
    apply e.injective
    simpa [hk] using hkp
  have hek : e k = k' := by simp [hk]
  have := ShapeRkAt'.of_equiv hp hGood hRk e (h k hk1' hkp')
  rwa [hek] at this

end Transport

section Core

variable {X : Type} [Group X] [Finite X]

theorem comp_dichotomy_rk' {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    {K : Subgroup X} {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (h : (∀ J : Subgroup ↥K,
        ¬ GLAPComponent p (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) J) ∨
      ∃ J : Subgroup ↥K, GLAPComponent p (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) J ∧
        (∀ I : Subgroup ↥K, GLAPComponent p
          (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) I → I = J) ∧
        Good (PSimple p J) ∧ Rk (PQuot p J)) :
    (∀ J : Subgroup X, ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) ∨
      ∃ J₀ : Subgroup X, J₀ ≤ K ∧
        (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → J = J₀) ∧
        Good (PSimple p (J₀.subgroupOf K)) ∧ Rk (PQuot p (J₀.subgroupOf K)) := by
  rcases h with hno | ⟨I, hI, hu, hG, hR⟩
  · refine Or.inl fun J hJ => hno (J.subgroupOf K) ?_
    have h1 := glaPComponent_subgroupOf hp
      (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
    rwa [subgroupOf_inf_centralizer_eq hk hc] at h1
  · refine Or.inr ⟨I.map K.subtype, Subgroup.map_subtype_le I, ?_, ?_⟩
    · intro J hJ
      have hJK : J ≤ K := hJ.1.trans inf_le_left
      have h1 := glaPComponent_subgroupOf hp
        (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
      rw [subgroupOf_inf_centralizer_eq hk hc] at h1
      rw [← Subgroup.map_subgroupOf_eq_of_le hJK, hu _ h1]
    · have h1 : (I.map K.subtype).subgroupOf K = I :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective I
      rw [h1]
      exact ⟨hG, hR⟩

end Core

section Templates

theorem strong_of_centShapeRk' {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : CentShapeRk' p Good Rk (NativeSporadic.Carrier name)) {X : Type} [Group X] [Finite X]
    {K B : Subgroup X} (hC : CompHyp p K B) (hN : I271Norm p K B) (hS : I271SporType K name)
    (hZ : Subgroup.center ↥K = ⊥) : IsStronglyBalancedIn p B K := by
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_of_pair hOut hBr hC.prime hC.odd hP _ hq.2
      (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eK : ↥K ≃* NativeSporadic.Carrier name :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (e.trans (hBr name).some.symm)
  haveI : Finite (NativeSporadic.Carrier name) := Finite.of_equiv ↥K eK.toEquiv
  have hshape : CentShapeRk' p Good Rk ↥K := CentShapeRk'.of_equiv hC.prime hGood hRk eK.symm hD
  refine strong_of_dichotomy_rk hGood hRk hOut hC hN ⟨e⟩ hloc hIH ?_
  intro a k hk haB hc haC
  obtain ⟨hkZ, hkp⟩ := lift_data_of_inner (hC.elem.2 a haB) haC hk hc
  have hk1 : (⟨k, hk⟩ : ↥K) ≠ 1 := fun h => hkZ (h ▸ Subgroup.one_mem _)
  have hkp1 : (⟨k, hk⟩ : ↥K) ^ p = 1 := by
    rw [hZ] at hkp
    exact Subgroup.mem_bot.1 hkp
  exact comp_dichotomy_rk' hC.prime hk hc (hshape _ hk1 hkp1)

theorem sporStrong_of_centShapeRk' {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hm : ¬ p ∣ sporadicMultiplierOrder name)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : CentShapeRk' p Good Rk (NativeSporadic.Carrier name)) : SporStrong name p := by
  intro X _ _ K B hC hN hS
  exact strong_of_centShapeRk' hGood hRk hOut hBr hP hIH hD hC hN hS
    (center_eq_bot_of_mult hSpM hC hS hm)

theorem sporStrong_of_goodSporShape'
    {name : TauCeti.SporadicName} {p : ℕ} {names : List TauCeti.SporadicName}
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hm : ¬ p ∣ sporadicMultiplierOrder name)
    (hChev : ChevStrong p) (hSp : ∀ S ∈ names, SporStrong S p)
    (hD : CentShapeRk' p (GoodSpor p names) (RkSpor p names) (NativeSporadic.Carrier name)) :
    SporStrong name p :=
  sporStrong_of_centShapeRk' (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
    (fun _ _ _ _ e h => RkSpor.of_equiv e h) hOut hSpM hBr hP hm
    (fun _ _ _ _ _ h hG hR => strong_goodSpor hChev hSp h hG hR) hD

end Templates

end CFSG.HardMathSupport.Dickson.I271
