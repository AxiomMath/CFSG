module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped commutatorElement

section Central

variable {X : Type} [Group X]

def centralInvolutions (Q : Subgroup X) : Set X :=
  {x | x ∈ Q ∧ x ∈ Subgroup.centralizer (Q : Set X) ∧ x ^ 2 = 1}

def omegaOneCentralIn (Q : Subgroup X) : Subgroup X :=
  Subgroup.closure (centralInvolutions Q)

theorem omegaOneCentralIn_le (Q : Subgroup X) : omegaOneCentralIn Q ≤ Q :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem omegaOneCentralIn_le_centralizer (Q : Subgroup X) :
    omegaOneCentralIn Q ≤ Subgroup.centralizer (omegaOneCentralIn Q : Set X) := by
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_iff.1 hx.2.1 h (omegaOneCentralIn_le Q hh)

theorem omegaOneCentralIn_sq (Q : Subgroup X) : ∀ x ∈ omegaOneCentralIn Q, x ^ 2 = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2.2
  | one => simp
  | mul a b ha hb iha ihb =>
    have hc : Commute a b :=
      (Subgroup.mem_centralizer_iff.1 (omegaOneCentralIn_le_centralizer Q ha) b hb).symm
    rw [hc.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem omegaOneCentralIn_isElemAbelian (Q : Subgroup X) : IsElemAbelian 2 (omegaOneCentralIn Q) :=
  ⟨isMulCommutative_iff.2 fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 (omegaOneCentralIn_le_centralizer Q a.2) b.1 b.2).symm,
    fun x hx => omegaOneCentralIn_sq Q x hx⟩

theorem conj_mem_centralInvolutions (Q : Subgroup X) [Q.Normal] (g : X) {x : X}
    (hx : x ∈ centralInvolutions Q) : g * x * g⁻¹ ∈ centralInvolutions Q := by
  obtain ⟨hxQ, hxC, hx2⟩ := hx
  refine ⟨Subgroup.Normal.conj_mem inferInstance x hxQ g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h' : g⁻¹ * h * g ∈ Q := by
      simpa using Subgroup.Normal.conj_mem inferInstance h hh g⁻¹
    have hc := Subgroup.mem_centralizer_iff.1 hxC _ h'
    calc h * (g * x * g⁻¹) = g * (g⁻¹ * h * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * h := by group
  · rw [conj_pow, hx2]
    simp

theorem omegaOneCentralIn_normal (Q : Subgroup X) [Q.Normal] : (omegaOneCentralIn Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold omegaOneCentralIn at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (conj_mem_centralInvolutions Q g hx)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

instance pCoreOf_two_top_normal : (pCoreOf 2 (⊤ : Subgroup X)).Normal :=
  ⟨fun x hx g => by
    have hn : (⊤ : Subgroup X) ≤ Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) : Set X) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤
    have := (Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_top g)) x).mp hx
    simpa using this⟩

end Central

section Route

variable {X : Type} [Group X] {T : Subgroup X}

theorem omegaOneCenterOf_le_omegaOneCentralIn (hC : CharTwo (⊤ : Subgroup X))
    (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T) :
    omegaOneCenterOf T ≤ omegaOneCentralIn (pCoreOf 2 (⊤ : Subgroup X)) := by
  unfold omegaOneCenterOf omegaOneOf
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  obtain ⟨hxZ, hx2⟩ := hx
  have hxZ' : x ∈ T ⊓ Subgroup.centralizer (T : Set X) := hxZ
  have hxC : x ∈ Subgroup.centralizer ((pCoreOf 2 (⊤ : Subgroup X)) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_iff.1 hxZ'.2 h (hQT hh)
  have hxQ : x ∈ pCoreOf 2 (⊤ : Subgroup X) := hC ⟨Subgroup.mem_top x, hxC⟩
  exact Subgroup.subset_closure ⟨hxQ, hxC, hx2⟩

theorem gnV_le_omegaOneCentralIn (hC : CharTwo (⊤ : Subgroup X))
    (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T) :
    gnV T ≤ omegaOneCentralIn (pCoreOf 2 (⊤ : Subgroup X)) := by
  have := omegaOneCentralIn_normal (pCoreOf 2 (⊤ : Subgroup X))
  unfold gnV
  exact Subgroup.normalClosure_le_normal fun x hx =>
    omegaOneCenterOf_le_omegaOneCentralIn hC hQT hx

theorem gnV_le_of_le (hC : CharTwo (⊤ : Subgroup X)) (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T) :
    gnV T ≤ T :=
  (gnV_le_omegaOneCentralIn hC hQT).trans ((omegaOneCentralIn_le _).trans hQT)

theorem isElemAbelian_gnV_of_le (hC : CharTwo (⊤ : Subgroup X))
    (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T) : IsElemAbelian 2 (gnV T) :=
  ⟨isMulCommutative_iff.2 fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.1
        (omegaOneCentralIn_le_centralizer (pCoreOf 2 (⊤ : Subgroup X))
          (gnV_le_omegaOneCentralIn hC hQT a.2)) b.1 (gnV_le_omegaOneCentralIn hC hQT b.2)).symm,
    fun x hx => (omegaOneCentralIn_isElemAbelian (pCoreOf 2 (⊤ : Subgroup X))).2 x
      (gnV_le_omegaOneCentralIn hC hQT hx)⟩

end Route

section Offender

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}
  (hV : IsElemAbelian 2 (gnV T)) [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem isBestOffender_gnRep_of_le (hVT : gnV T ≤ T) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) :
    IsBestOffender (gnRep hV) (A.map (QuotientGroup.mk' (gnC T))) := by
  intro B hB
  have hTN : T ≤ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) :=
    fun g _ => mem_normalizer_gnV T g
  have hBA : B.map (gnIota hV) ≤ autI hV A := by
    rw [← map_mk_map_gnIota hV A]
    exact Subgroup.map_mono hB
  have h := (offender_core hV hVT hTN hA hBA).1
  rw [← map_mk_map_gnIota hV A, card_map_gnIota hV, card_map_gnIota hV] at h
  rw [card_fixSub_gnRep hV, card_fixSub_gnRep hV]
  exact h

include hV in
theorem exists_offender_of_le (hVT : gnV T ≤ T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ A : Subgroup X, IsMaxElemAbelian T A ∧
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ∧
      ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L := by
  have hinj : Function.Injective (gnRep hV) := gnRep_injective hV
  have hC : CFSG.IsComponent L := (isComponent_iff_open L).2 hL
  have hQ : CFSG.IsQuasisimple L := hC.1
  have hLbot : L ≠ ⊥ := by
    intro h
    have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    subst h
    have : Nontrivial (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T))) :=
      hs.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne
      (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T)))
    induction x using QuotientGroup.induction_on with
    | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))
  have hnorm : ∀ A : Subgroup X, IsMaxElemAbelian T A →
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := fun A hA =>
    (le_bestOffenderSub (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep_of_le hV hVT hA)).trans
      (bestOffenderSub_le_normalizer_component (gnRep hV) hinj hC)
  have key : ∃ A : Subgroup X, IsMaxElemAbelian T A ∧
      ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L := by
    by_contra hno
    push Not at hno
    have hcen : ∀ A : Subgroup X, IsMaxElemAbelian T A →
        A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
      intro A hA
      by_cases hb : ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = ⊥
      · intro a ha l hl
        have : ⁅l, a⁆ ∈ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ :=
          Subgroup.commutator_mem_commutator hl ha
        rw [hb, Subgroup.mem_bot] at this
        exact commutatorElement_eq_one_iff_mul_comm.1 this
      · exact absurd (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commutator_eq_of_ne_bot hQ
          (hnorm A hA) hb) (hno A hA)
    have hJle : gnImg T (thompsonJ T) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
      unfold gnImg thompsonJ
      rw [Subgroup.map_iSup]
      refine iSup_le fun A => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hA => hcen A hA
    apply hLbot
    rw [← hJ, eq_bot_iff, Subgroup.commutator_le]
    intro l hl j hj
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 (hJle hj) l hl)
  obtain ⟨A, hAmax, hLA⟩ := key
  exact ⟨A, hAmax, hnorm A hAmax, hLA⟩

end Offender

theorem exists_rep_offender_of_le (X : Type) [Group X] [Finite X] (T : Subgroup X)
    (hC : CharTwo (⊤ : Subgroup X)) (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (ρ : Representation (ZMod 2) (X ⧸ gnC T) W), Function.Injective ρ ∧
      ∃ A : Subgroup (X ⧸ gnC T), CFSG.IsElementaryAbelian 2 A ∧
        CFSG.RankThree.FFModules.IsBestOffender ρ A ∧
        A ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) ∧ ⁅L, A⁆ = L := by
  have hVT : gnV T ≤ T := gnV_le_of_le hC hQT
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hC hQT
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  obtain ⟨A, hAmax, hnorm, hLA⟩ := exists_offender_of_le hV hVT L hL hJ
  exact ⟨Additive (IntMod (gnV T) hV), inferInstance, inferInstance, inferInstance, gnRep hV,
    gnRep_injective hV, A.map (QuotientGroup.mk' (gnC T)), isElementaryAbelian_map_mk hAmax,
    isBestOffender_gnRep_of_le hV hVT hAmax, hnorm, hLA⟩

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
