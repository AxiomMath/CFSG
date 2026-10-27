module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerStruct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerCenter

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem actW_eq_one_of_disp_mem_fix {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I) {x : ↥(L ⊔ A)}
    (hx : ∀ w ∈ I, (x : V ≃ₗ[ZMod 2] V) w - w ∈ fixGL L) : actW L A I hAn hI x = 1 := by
  apply LinearEquiv.ext
  intro w
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [actW_mk]
  show (Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI x u) :
    ↥I ⧸ fixIn L I) = Submodule.Quotient.mk u
  rw [Submodule.Quotient.eq]
  intro l hl
  have e : ((resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI x u - u : ↥I) : V) =
      (x : V ≃ₗ[ZMod 2] V) u - u := by
    rw [Submodule.coe_sub, resSub_apply]
    rfl
  show l ((resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI x u - u : ↥I) : V) = _
  rw [e]
  exact hx u u.2 l hl

theorem even_SL2_component_layer
    [Finite V] {H T M E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (V ≃ₗ[ZMod 2] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N →
      N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[ZMod 2] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    {Lstar : Subgroup (V ≃ₗ[ZMod 2] V)} (hLstar : IsComponentIn Lstar H)
    (α : (↥Lstar ⧸ Subgroup.center ↥Lstar) ≃* SL(2, F))
    {r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (hLc : IsCompListIn H r Lc) :
    EvenSL2LayerOutput H T r F Lc := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hnl : NonsolvableLayer H T M :=
    nonsolvable_layer quadBestOffendersNormalize hns hO2 hT hTn hTM hMH hmax hEH hEne hEel hEoff
  have hpar := hnl.parabolic
  have hiso : ∀ X : Subgroup (V ≃ₗ[ZMod 2] V), IsComponentIn X H →
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* SL(2, F)) := fun X hX =>
    component_iso_ambient hnl hLstar hX α
  let αi : ∀ i : Fin r, (↥(Lc i) ⧸ Subgroup.center ↥(Lc i)) ≃* SL(2, F) := fun i =>
    (hiso (Lc i) (hLc.isComp i)).some
  have hcen : ∀ i, Subgroup.center ↥(Lc i) = ⊥ := fun i =>
    center_component_eq_bot hnl hF (hLc.isComp i) (αi i)
  have hrad : CFSG.solvableRadical ↥H = ⊥ := rad_eq_bot hnl hF hLstar α
  have hcent := centralizer_oddGen_eq_bot hnl hT hrad
  have hK := hLc.oddGen_eq hnl
  obtain ⟨i₀, -⟩ := hLc.complete Lstar hLstar
  have hoffd : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), IsMinOffender H A → ∀ i : Fin r, ⁅Lc i, A⁆ ≠ ⊥ →
      ComponentOffenderOutput (Lc i) A n (αi i) (commGL (Lc i) ⊤) ∧
        ∀ C : Subgroup (V ≃ₗ[ZMod 2] V), IsComponentIn C H → C ≠ Lc i →
          (∀ c ∈ C, ∀ w ∈ commGL (Lc i) ⊤, c w = w) ∧ ∀ c ∈ C, ∀ a ∈ A, c * a = a * c :=
    fun A hA i hmove => minimal_even_SL2_component_offender (hLc.isComp i) hn hF (αi i) hA.1
      hA.2.2.1 hA.2.1 hA.2.2.2.1 hA.2.2.2.2 hmove
  have hmoving : ∀ i, ∃ A, IsMinOffender H A ∧ ⁅Lc i, A⁆ = Lc i := fun i => by
    obtain ⟨A, hA, hLA, -⟩ := (hpar.comps (Lc i) (hLc.isComp i)).2.2
    exact ⟨A, hA, hLA⟩
  have hper : ∀ i : Fin r,
      IsIrrQuot (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i) (commGL (Lc i) ⊤) ∧
      (∀ x ∈ Lc i, (∀ v ∈ commGL (Lc i) ⊤, x v - v ∈ fixGL (Lc i)) → x = 1) ∧
      (∀ j, j ≠ i → ∀ x ∈ Lc j, ∀ v ∈ commGL (Lc i) ⊤, x v = v) := by
    intro i
    obtain ⟨A, hA, hLA, -⟩ := (hpar.comps (Lc i) (hLc.isComp i)).2.2
    have hmove : ⁅Lc i, A⁆ ≠ ⊥ := by rw [hLA]; exact hLc.ne_bot i
    obtain ⟨hd1, hd2⟩ := hoffd A hA i hmove
    refine ⟨hd1.irr, ?_, fun j hji x hx v hv =>
      (hd2 (Lc j) (hLc.isComp j) (fun h => hji (hLc.injective h))).1 x hx v hv⟩
    intro x hx hxfix
    have hker : (⟨x, hx⟩ : ↥(Lc i)) ∈ (actOn (Lc i) A (commGL (Lc i) ⊤) hd1.A_norm
        (isInvariant_sup_subgroup hd1.inv_L hd1.inv_A) (Lc i) le_sup_left).ker := by
      rw [MonoidHom.mem_ker]
      exact actW_eq_one_of_disp_mem_fix hd1.A_norm _ (x := ⟨x, Subgroup.mem_sup_left hx⟩)
        (fun w hw => hxfix w hw)
    rw [hd1.kernel_L, hcen i, Subgroup.mem_bot] at hker
    exact congrArg Subtype.val hker
  have hoffA : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), IsMinOffender H A →
      (∀ i, A ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V))) ∧
      ∃ i, ⁅Lc i, A⁆ ≠ ⊥ ∧ (∀ j, ⁅Lc j, A⁆ ≠ ⊥ → j = i) ∧ ⁅Lc i, A⁆ = Lc i ∧
        commGL (Lc i) ⊤ ⊔ fixGL A = ⊤ ∧ commGL (Lc i ⊔ A) ⊤ = commGL (Lc i) ⊤ ∧
        (∀ a ∈ A, (∀ v ∈ commGL (Lc i) ⊤, a v - v ∈ fixGL (Lc i)) → a = 1) ∧
        commGL (Lc i) ⊤ ⊓ fixGL (Lc i) ≤ fixGL (Lc i ⊔ A) ∧
        weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A = Nat.card V ∧
        ∀ j, j ≠ i → ∀ x ∈ Lc j, ∀ a ∈ A, x * a = a * x := by
    intro A hA
    refine ⟨fun i => (le_offenderJ hA).trans (hpar.comps (Lc i) (hLc.isComp i)).2.1, ?_⟩
    obtain ⟨i, hi⟩ : ∃ i, ⁅Lc i, A⁆ ≠ ⊥ := by
      by_contra hnone
      push Not at hnone
      have h1 : oddGen H ≤ Subgroup.centralizer (A : Set (V ≃ₗ[ZMod 2] V)) := by
        rw [hK]
        exact iSup_le fun i => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hnone i)
      have h2 : A ≤ Subgroup.centralizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 h1
      have h3 : A ≤ H ⊓ Subgroup.centralizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) :=
        le_inf hA.1 h2
      rw [hcent] at h3
      exact hA.2.1 (le_bot_iff.1 h3)
    obtain ⟨hd1, hd2⟩ := hoffd A hA i hi
    have hothers : ∀ j, j ≠ i → ∀ x ∈ Lc j, ∀ a ∈ A, x * a = a * x := fun j hji x hx a ha =>
      (hd2 (Lc j) (hLc.isComp j) (fun h => hji (hLc.injective h))).2 x hx a ha
    refine ⟨i, hi, ?_, hd1.L_perf, hd1.V_split, hd1.I_LA, ?_, hd1.Z_fixed, hd1.weight_eq, hothers⟩
    · intro j hj
      by_contra hji
      refine hj ?_
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
      refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      exact (hothers j hji x hx a ha).symm
    · intro a ha haf
      have h1 : actOn (Lc i) A (commGL (Lc i) ⊤) hd1.A_norm
          (isInvariant_sup_subgroup hd1.inv_L hd1.inv_A) A le_sup_right ⟨a, ha⟩ = 1 :=
        actW_eq_one_of_disp_mem_fix hd1.A_norm _ (x := ⟨a, Subgroup.mem_sup_right ha⟩)
          (fun w hw => haf w hw)
      have h2 := hd1.A_faithful_W (h1.trans (map_one _).symm)
      exact congrArg Subtype.val h2
  refine ⟨hpar.nonempty, hpar.J_normal, hpar.H_eq, hnl.H_eq_KT, hpar.K_le_J, i₀.pos,
    hLc.card_pow_two hnl hT i₀, hLc.trans hnl,
    hcen, fun i => nonempty_equiv_of_center_eq_bot (hcen i) (αi i), hK,
    fun i j hij => hLc.commutator_eq_bot hij, ?_, hrad, hcent, fun i => (hper i).1,
    fun i => (hper i).2.1, fun i j hji => (hper i).2.2 j hji, hmoving, hoffA, ?_⟩
  · intro i
    rw [eq_bot_iff]
    rintro x ⟨hxi, hxj⟩
    have hle : (⨆ j, ⨆ (_ : j ≠ i), Lc j) ≤
        centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc i) ⊤) :=
      iSup₂_le fun j hji y hy => mem_centSub.2 fun v hv => (hper i).2.2 j hji y hy v hv
    have hfix := mem_centSub.1 (hle hxj)
    rw [Subgroup.mem_bot]
    refine (hper i).2.1 x hxi fun v hv => ?_
    rw [show x v - v = 0 from sub_eq_zero.2 (hfix v hv)]
    exact Submodule.zero_mem _
  · intro E' hE'H hE'ne hE'el
    refine weight_le_of_offenders (fun A hA => ?_) hE'H hE'ne hE'el
    obtain ⟨-, i, -, -, -, -, -, -, -, hw, -⟩ := hoffA A hA
    exact hw

end CFSG.QuasithinUnique.Setup.Lift
