module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphNeighbour

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open scoped MatrixGroups

variable {N ε : ℕ} {K : Type} [Field K]

theorem exists_eq_conj_of_mulAut_spBlock [CharP K 2] (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m)
    (k : Fin (m + 1)) (δ : MulAut (spBlock K ({k} : Finset (Fin (m + 1)))ᶜ)) :
    ∃ s : spBlock K ({k} : Finset (Fin (m + 1)))ᶜ, δ = MulAut.conj s := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨s, σ, hβ⟩ := exists_eq_conj_mul_fieldSp hm (MulAut.congr (blockComplEquiv K k) δ)
  rw [q2RingEquiv_eq_one hK σ, map_one, mul_one] at hβ
  refine ⟨(blockComplEquiv K k).symm s, (MulAut.congr (blockComplEquiv K k)).injective ?_⟩
  rw [hβ]
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_mulEquiv_eq_of_intertwine [CharP K 2] (hK : Nat.card K = 2) (hε : ε ≤ 1)
    {R : Finset (Fin N)} (haut : ∀ δ : MulAut (spBlock K Rᶜ), ∃ s, δ = MulAut.conj s)
    (hperf : Group.IsPerfect (spBlock K Rᶜ)) {M : Type*} [Group M] [Finite M]
    (ψ : q2Block ε K R ≃* M) {θ : MulAut M} (hψθ : ∀ x, θ (ψ x) = ψ (q2GraphBlock ε hK R x))
    (ι : spBlock K Rᶜ →* M) (hι : Function.Injective ι)
    (hιr : ι.range = perfectCore (fixedSubgroup θ)) :
    ∃ ψ' : q2Block ε K R ≃* M, ∀ (y : StatedSp N K) (hy : y ∈ spBlock K Rᶜ),
      ψ' ⟨q2Embed ε hK y, (q2Embed_mem_q2Block_iff hK).2 hy⟩ = ι ⟨y, hy⟩ := by
  have hfix : fixedSubgroup θ = (q2SpBlock ε K hK R).map ψ.toMonoidHom := by
    rw [← fixedSubgroup_q2GraphBlock hK hε R]
    ext z
    obtain ⟨x, rfl⟩ := ψ.surjective z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    change θ (ψ x) = ψ x ↔ q2GraphBlock ε hK R x = x
    rw [hψθ]
    exact ψ.injective.eq_iff
  have hSperf : ⁅q2SpBlock ε K hK R, q2SpBlock ε K hK R⁆ = q2SpBlock ε K hK R := by
    have hP' : Group.IsPerfect (q2SpBlock ε K hK R) :=
      Group.IsPerfect.ofSurjective (f := (q2SpBlockEquiv hK R).toMonoidHom)
        (MulEquiv.surjective _)
    exact Subgroup.isPerfect_iff.mp hP'
  have hcore : perfectCore (fixedSubgroup θ) = (q2SpBlock ε K hK R).map ψ.toMonoidHom := by
    rw [hfix]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect (by
      rw [← map_commutator, hSperf])
  set κ : spBlock K Rᶜ →* M :=
    (ψ.toMonoidHom.comp (q2SpBlock ε K hK R).subtype).comp (q2SpBlockEquiv hK R).toMonoidHom
    with hκ
  have hκinj : Function.Injective κ :=
    ψ.injective.comp (Subtype.val_injective.comp (q2SpBlockEquiv hK R).injective)
  have hκr : κ.range = ι.range := by
    rw [hιr, hcore, hκ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, range_subtype]
  set δ : MulAut (spBlock K Rᶜ) := ((MonoidHom.ofInjective hκinj).trans
    (MulEquiv.subgroupCongr hκr)).trans (MonoidHom.ofInjective hι).symm with hδdef
  have hδ : ∀ y, ι (δ y) = κ y := by
    intro y
    have h := (MonoidHom.ofInjective hι).apply_symm_apply
      (MulEquiv.subgroupCongr hκr (MonoidHom.ofInjective hκinj y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, hs⟩ := haut δ
  set b : q2Block ε K R := ⟨q2Embed ε hK s, (q2Embed_mem_q2Block_iff hK).2 s.2⟩ with hb
  refine ⟨(MulAut.conj b⁻¹).trans ψ, fun y hy => ?_⟩
  have hy' : (⟨y, hy⟩ : spBlock K Rᶜ) = s * (s⁻¹ * ⟨y, hy⟩ * s) * s⁻¹ := by group
  have h1 := hδ (s⁻¹ * ⟨y, hy⟩ * s)
  rw [hs, MulAut.conj_apply, ← hy'] at h1
  rw [h1]
  change ψ (b⁻¹ * ⟨q2Embed ε hK y, _⟩ * b⁻¹⁻¹) = ψ ((q2SpBlockEquiv hK R (s⁻¹ * ⟨y, hy⟩ * s) :
    q2SpBlock ε K hK R) : q2Block ε K R)
  congr 1
  apply Subtype.ext
  rw [coe_q2SpBlockEquiv]
  simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, hb, map_mul, map_inv]

section Exists


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_nsLinParam [CharP K 2] (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hε : ε ≤ 1) {m : ℕ} (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {κ : Sp2mKind}
    (hκ : (κ = .linearEven ∧ ε = 0) ∨ (κ = .linearOdd ∧ ε = 1)) (h : NsKindSp e t k κ) :
    Nonempty (NsLinParam hK ε e k) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set X : Subgroup G := modelToG e (nsTorusSp K k) with hXdef
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (UnitaryPilot.mem_normalizer_modelToG_of_mem_centralizer e htC _)
  set θ := (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ with hθ
  have hκ' : κ = .linearEven ∨ κ = .linearOdd := by
    rcases hκ with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨r, F, _, _, hF, hr, ε₀, hα2, hαo, hαfix⟩ :=
    exists_mulEquiv_neighbourCore_linear_two hset hK hm e htC ht k rfl rfl hκ' h hN
  have hr' : r = 2 * m + ε := by
    rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · cases h1
    · cases h1
    · omega
  subst hr'
  have hcard : ((planeCoordsQ2 ε ({k} : Finset (Fin (m + 1))))ᶜ).card = 2 * m + ε := by
    rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨χK⟩ : Nonempty (q2Block ε K ({k} : Finset (Fin (m + 1))) ≃*
      LinearFlag.projectiveSL (2 * m + ε) K) := by
    have := nonempty_q2Block_mulEquiv (ε := ε) hK ({k} : Finset (Fin (m + 1)))
    rwa [hcard] at this
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  have hKF : Fintype.card K = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF]
  set χ : q2Block ε K ({k} : Finset (Fin (m + 1))) ≃* LinearFlag.projectiveSL (2 * m + ε) F :=
    χK.trans (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr
      (FiniteField.ringEquivOfCardEq hKF)) with hχ
  set ψ₀ : q2Block ε K ({k} : Finset (Fin (m + 1))) ≃* centralizerPerfectCore X :=
    χ.trans ε₀.symm with hψ₀
  set α : MulAut (q2Block ε K ({k} : Finset (Fin (m + 1)))) := MulAut.congr ψ₀.symm θ with hα
  have hαcongr : MulAut.congr χ α = MulAut.congr ε₀ θ := by
    ext z
    simp [hα, hψ₀, MulAut.congr_apply]
  have hαα : α * α = 1 := (MulAut.congr χ).injective (by
    rw [map_mul, hαcongr, hα2, map_one])
  have hαo' : α ∉ (MulAut.conj : q2Block ε K ({k} : Finset (Fin (m + 1))) →* MulAut _).range :=
    fun h' => hαo (by rw [← hαcongr]; exact (FixedFourGroup.congr_mem_inner_iff χ α).2 h')
  have hαfix' : LieModel (fixedSubgroup α) .PSp m 2 1 := by
    rw [← hαcongr] at hαfix
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv χ α).symm hαfix
  obtain ⟨β, hβ⟩ := exists_eq_mul_q2GraphBlock_mul_inv hK hε hm k (by rw [hF]) χ hαα hαo' hαfix'
  set ψ₁ : q2Block ε K ({k} : Finset (Fin (m + 1))) ≃* centralizerPerfectCore X :=
    β.trans ψ₀ with hψ₁
  have hψ₁θ : ∀ x, θ (ψ₁ x) = ψ₁ (q2GraphBlock ε hK {k} x) := by
    intro x
    have h1 : ∀ y, θ (ψ₀ y) = ψ₀ (α y) := by
      intro y
      simp [hα, MulAut.congr_apply]
    change θ (ψ₀ (β x)) = ψ₀ (β (q2GraphBlock ε hK {k} x))
    rw [h1, hβ]
    simp
  have hD : modelToG e (complSp K k) ≤ centralizerPerfectCore X :=
    modelToG_complSp_le_centralizerPerfectCore_nsTorusSp hK hm e k
  have hmemD : ∀ y : spBlock K ({k} : Finset (Fin (m + 1)))ᶜ,
      ((e.symm (y : StatedSp (m + 1) K) : L) : G) ∈ centralizerPerfectCore X := fun y =>
    hD (UnitaryPilot.symm_mem_modelToG e (by
      rw [← spBlock_compl_singleton]
      exact y.2))
  set ι : spBlock K ({k} : Finset (Fin (m + 1)))ᶜ →* centralizerPerfectCore X :=
    ((L.subtype.comp (e.symm.toMonoidHom.comp
      (spBlock K ({k} : Finset (Fin (m + 1)))ᶜ).subtype))).codRestrict _ hmemD with hιdef
  have hιapp : ∀ y, ((ι y : centralizerPerfectCore X) : G) =
      ((e.symm (y : StatedSp (m + 1) K) : L) : G) := fun _ => rfl
  have hιinj : Function.Injective ι := by
    intro y z hyz
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    have := congrArg (fun w : centralizerPerfectCore X => (w : G)) hyz
    simpa only [hιapp] using this
  have hιr : ι.range = perfectCore (fixedSubgroup θ) := by
    apply Subgroup.map_injective (centralizerPerfectCore X).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore]
    change _ = perfectCore ((MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _)).map
      (centralizerPerfectCore X).subtype)
    rw [map_eqLocus_normalizerMonoidHom_eq hN,
      perfectCore_centralizerPerfectCore_nsTorusSp_inf_centralizer hset hK hm e htC ht k]
    ext g
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      rw [coe_subtype, hιapp]
      exact UnitaryPilot.symm_mem_modelToG e (by
        rw [← spBlock_compl_singleton]
        exact y.2)
    · intro hg
      obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
      have hx' : x ∈ spBlock K ({k} : Finset (Fin (m + 1)))ᶜ := by
        rwa [spBlock_compl_singleton]
      exact ⟨ι ⟨x, hx'⟩, ⟨⟨x, hx'⟩, rfl⟩, rfl⟩
  have haut := exists_eq_conj_of_mulAut_spBlock hK hm k
  have hperf : Group.IsPerfect (spBlock K ({k} : Finset (Fin (m + 1)))ᶜ) := by
    have := isPerfect_statedSp_of_charTwo (k := K) hm
    exact Group.IsPerfect.ofSurjective (f := (blockComplEquiv K k).symm.toMonoidHom)
      (MulEquiv.surjective _)
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_eq_of_intertwine hK hε haut hperf ψ₁ hψ₁θ ι hιinj hιr
  refine ⟨⟨(centralizerPerfectCore X).subtype.comp ψ'.toMonoidHom,
    Subtype.val_injective.comp ψ'.injective, ?_, fun y hy => ?_⟩⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ'.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  · change ((ψ' ⟨q2Embed ε hK y, _⟩ : centralizerPerfectCore X) : G) = _
    rw [hψ' y hy, hιapp]

end Exists

end CFSG.SeitzReduction.SymplecticPilot
