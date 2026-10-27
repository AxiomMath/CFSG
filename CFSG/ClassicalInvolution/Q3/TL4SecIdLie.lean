module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdExact
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Uniform

section Transfer

variable {X : Type} [Group X] [Finite X] {Δ : Set (Subgroup X)}

theorem dAdj_liftFam_iff (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (hl : HasLifts Δ)
    (hex : ExactSylow Δ) {M M' J J' : Subgroup X} (hM : M ∈ liftFam Δ) (hJ : J ∈ Δ)
    (hJM : J ≤ M) (hM' : M' ∈ liftFam Δ) (hJ' : J' ∈ Δ) (hJM' : J' ≤ M') :
    dAdj (liftFam Δ) M M' ↔ dAdj Δ J J' :=
  or_congr (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hM hJ hJM hM' hJ' hJM')
    (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl hM' hJ' hJM' hM hJ hJM)

theorem dstarAdj_liftFam_iff (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) {M M' J J' : Subgroup X} (hM : M ∈ liftFam Δ)
    (hJ : J ∈ Δ) (hJM : J ≤ M) (hM' : M' ∈ liftFam Δ) (hJ' : J' ∈ Δ) (hJM' : J' ≤ M') :
    dstarAdj (liftFam Δ) M M' ↔ dstarAdj Δ J J' :=
  ⟨fun h => ⟨hJ', (or_congr (hex.mem_omegaStarNbr_liftFam_iff hΩ h2 hl hM hJ hJM hM' hJ' hJM')
      (hex.mem_omegaStarNbr_liftFam_iff hΩ h2 hl hM' hJ' hJM' hM hJ hJM)).mp h.2⟩,
    fun h => ⟨hM', (or_congr (hex.mem_omegaStarNbr_liftFam_iff hΩ h2 hl hM hJ hJM hM' hJ' hJM')
      (hex.mem_omegaStarNbr_liftFam_iff hΩ h2 hl hM' hJ' hJM' hM hJ hJM)).mpr h.2⟩⟩

theorem dConnected_of_liftFam (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) (hc : DConnected (liftFam Δ)) : DConnected Δ := by
  intro K hK J hJ
  obtain ⟨L, u, h⟩ := hl K hK
  obtain ⟨L', u', h'⟩ := hl J hJ
  have hM := satU_mem_liftFam hK h
  have hM' := satU_mem_liftFam hJ h'
  have key : ∀ N, Relation.ReflTransGen
      (fun A B : Subgroup X => B ∈ liftFam Δ ∧ dAdj (liftFam Δ) A B)
      (satU (.sl2 3 1) L u) N → N ∈ liftFam Δ ∧ ∀ J'' ∈ Δ, J'' ≤ N →
        Relation.ReflTransGen (fun A B : Subgroup X => B ∈ Δ ∧ dAdj Δ A B) K J'' := by
    intro N hN
    induction hN with
    | refl =>
      refine ⟨hM, fun J'' hJ'' hJ''M => ?_⟩
      rw [hex.core_unique hΩ h2 hM hK hJ'' h.le_sat hJ''M]
    | tail _ hbc ih =>
      obtain ⟨hb, ihJ⟩ := ih
      refine ⟨hbc.1, fun J'' hJ'' hJ''c => ?_⟩
      obtain ⟨Jb, hJb, hJbb⟩ := exists_core_of_mem_liftFam hb
      exact (ihJ Jb hJb hJbb).tail
        ⟨hJ'', (dAdj_liftFam_iff hΩ h2 hl hex hb hJb hJbb hbc.1 hJ'' hJ''c).mp hbc.2⟩
  exact (key _ (hc _ hM _ hM')).2 J hJ h'.le_sat

theorem dstarConnected_of_liftFam (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    (hl : HasLifts Δ) (hex : ExactSylow Δ) (hc : T3.DStarConnected (liftFam Δ)) :
    T3.DStarConnected Δ := by
  intro K hK J hJ
  obtain ⟨L, u, h⟩ := hl K hK
  obtain ⟨L', u', h'⟩ := hl J hJ
  have hM := satU_mem_liftFam hK h
  have hM' := satU_mem_liftFam hJ h'
  have key : ∀ N, Relation.ReflTransGen (dstarAdj (liftFam Δ)) (satU (.sl2 3 1) L u) N →
      N ∈ liftFam Δ ∧ ∀ J'' ∈ Δ, J'' ≤ N → Relation.ReflTransGen (dstarAdj Δ) K J'' := by
    intro N hN
    induction hN with
    | refl =>
      refine ⟨hM, fun J'' hJ'' hJ''M => ?_⟩
      rw [hex.core_unique hΩ h2 hM hK hJ'' h.le_sat hJ''M]
    | tail _ hbc ih =>
      obtain ⟨hb, ihJ⟩ := ih
      refine ⟨hbc.1, fun J'' hJ'' hJ''c => ?_⟩
      obtain ⟨Jb, hJb, hJbb⟩ := exists_core_of_mem_liftFam hb
      exact (ihJ Jb hJb hJbb).tail
        ((dstarAdj_liftFam_iff hΩ h2 hl hex hb hJb hJbb hbc.1 hJ'' hJ''c).mp hbc)
  exact (key _ (hc _ hM _ hM')).2 J hJ h'.le_sat

theorem exists_lift_clique (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (hl : HasLifts Δ)
    (hex : ExactSylow Δ) {k : ℕ} (B : Fin k → Subgroup X) (hB : ∀ i, B i ∈ Δ)
    (hinj : Function.Injective B) (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Δ (B i)) :
    ∃ M : Fin k → Subgroup X, (∀ i, M i ∈ liftFam Δ) ∧ (∀ i, B i ≤ M i) ∧
      Function.Injective M ∧ ∀ i j, i ≠ j → M j ∈ omegaNbr (liftFam Δ) (M i) := by
  choose L u h using fun i => hl (B i) (hB i)
  refine ⟨fun i => satU (.sl2 3 1) (L i) (u i), fun i => satU_mem_liftFam (hB i) (h i),
    fun i => (h i).le_sat, ?_, ?_⟩
  · intro i j hij
    apply hinj
    refine hex.core_unique hΩ h2 (satU_mem_liftFam (hB i) (h i)) (hB i) (hB j) (h i).le_sat ?_
    rw [show satU (.sl2 3 1) (L i) (u i) = satU (.sl2 3 1) (L j) (u j) from hij]
    exact (h j).le_sat
  · intro i j hij
    exact (hex.mem_omegaNbr_liftFam_iff hΩ h2 hl (satU_mem_liftFam (hB i) (h i)) (hB i)
      (h i).le_sat (satU_mem_liftFam (hB j) (h j)) (hB j) (h j).le_sat).mpr (hadj i j hij)

end Transfer

section Cit3


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem SecIdLie3.hasLifts (hl : SecIdLie3 R t) (hd : TightDatum R S t) :
    HasLifts (CoreAssembly.conjClass (tightCore R)) := by
  obtain ⟨L, hKL, hL, -⟩ := hl
  exact hasLifts_conjClass hd.isUniqueInvolution_core hKL hL

theorem SecIdLie3.isPGroup_members (hl : SecIdLie3 R t) (hO : TightOddFree Y) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J := by
  rintro _ ⟨g, rfl⟩
  exact (hl.isPGroup_core hO).map (MulAut.conj g).toMonoidHom


theorem SecIdLie3.oddCoreIn_centralizer_eq_bot (hl : SecIdLie3 R t) (hO : TightOddFree Y)
    {a : Y} (ha : orderOf a = 2) :
    Balance.oddCoreIn (Subgroup.centralizer ({a} : Set Y)) = ⊥ := by
  obtain ⟨L, -, -, -, hLie⟩ := hl
  have h := lieSystemOddCentralizer3_proved Y _ hLie a ha
  have hO' : classicalInvolutionOddCore Y = ⊥ := hO
  rw [hO'] at h
  exact le_bot_iff.mp h

theorem SecIdLie3.exactSylow (hl : SecIdLie3 R t) (hO : TightOddFree Y) :
    ExactSylow (CoreAssembly.conjClass (tightCore R)) :=
  ExactSylow.of_oddCoreIn_eq_bot fun _ _ _ _ h => hl.oddCoreIn_centralizer_eq_bot hO
    (orderOf_eq_prime (by rw [pow_two]; exact h.inv.sq) h.inv.ne_one)

theorem SecIdLie3.liftFam_hyp (hl : SecIdLie3 R t) (hd : TightDatum R S t)
    (hc : TightCls Y R S t) :
    HypOmegaModU (.sl2 3 1) (liftFam (CoreAssembly.conjClass (tightCore R))) ∧
      omegaGen (liftFam (CoreAssembly.conjClass (tightCore R))) = ⊤ ∧
      ∀ M ∈ liftFam (CoreAssembly.conjClass (tightCore R)),
        AEmpty (liftFam (CoreAssembly.conjClass (tightCore R))) M := by
  have hΩ := hd.hypOmegaGen
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    have h1 : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hc.2.1
    rw [eq_top_iff, ← h1]
    exact iSup_le fun g => le_iSup₂_of_le (conjSub g (tightCore R)) ⟨g, rfl⟩ le_rfl
  refine ⟨hypOmegaModU_liftFam hΩ.conjInvariant,
    (inClass3_liftFam hΩ.conjInvariant ⟨_, CoreAssembly.mem_conjClass_self _⟩
      (hl.hasLifts hd) hgen).generated,
    (hl.exactSylow hc.2.2).aEmpty_liftFam hΩ (hl.isPGroup_members hc.2.2) (hl.hasLifts hd)
      hd.aEmpty⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
