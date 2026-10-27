module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneSp
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyClosed
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.OuterSpData

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP
  CFSG.Adapters.RankTwoModelTransports
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.KCSpComm
open CFSG.Open (IsElemAbelian)

noncomputable def statedProjSpCongr {r : ℕ} {k k' : Type} [Field k] [Field k'] (φ : k ≃+* k') :
    StatedProj (StatedSp r k) ≃* StatedProj (StatedSp r k') :=
  statedProjCongr (ι := Fin r ⊕ Fin r) (glCongr φ)
    (CFSG.Blueprint.EvenSource.glCongr_statedSp φ r) (glCongr_statedScalars φ)

theorem rankLE2_of_injective {M X : Type*} [Group M] [Group X] {p : ℕ} (ψ : M →* X)
    (hψ : Function.Injective ψ) (h : RankLE2 p X) : RankLE2 p M := by
  intro F hF
  have := h (F.map ψ) (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF ψ)
  rwa [Subgroup.card_map_of_injective hψ] at this

theorem closure_comm_of_planeGen_conj {K : Type*} [Group K] {E₀ : Subgroup K}
    (h : PlaneGen (E₀.map (MulAut.conj : K →* MulAut K))) :
    Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  rw [eq_top_iff, ← h, planeClosure]
  refine Subgroup.closure_mono ?_
  rintro k ⟨_, ⟨x, hx, rfl⟩, hx1, hk⟩
  refine ⟨x, hx, ?_, ?_⟩
  · rintro rfl
    exact hx1 (map_one _)
  · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hk
    exact hk.symm

theorem fixPlaneGen_projectiveSp_two_three
    {K : Type} [Field K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hℓ3 : ℓ ≠ 3) (hexc : ¬ (ℓ = 2 ∧ f = 3))
    (hrk : RankLE2 3 (StatedProj (StatedSp 2 K))) :
    FixPlaneGen (StatedProj (StatedSp 2 K)) 3 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  refine fixPlaneGen_projectiveSp_of_inner (le_refl 2) hℓ hf hK Nat.prime_three (by norm_num) ?_
  intro σ0 hσ0 E₁ hE₁ hc₁
  have hpf : 3 ∣ f ∧ Nat.card (descentField σ0) = ℓ ^ (f / 3) :=
    CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK hσ0
  have hf' : 0 < f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf.1) (by norm_num)
  let q0 : TauCeti.PrimePower := ⟨ℓ, f / 3, hℓ, hf'⟩
  have hq0card : q0.card = ℓ ^ (f / 3) := by simp [TauCeti.PrimePower.card_def, q0]
  have hq0ne2 : q0.card ≠ 2 := by
    intro h
    rw [hq0card, Nat.Prime.pow_eq_iff Nat.prime_two] at h
    obtain ⟨h1, h2⟩ := h
    apply hexc
    refine ⟨h1, ?_⟩
    obtain ⟨c, hc⟩ := hpf.1
    omega
  have hq0ne3 : q0.card ≠ 3 := by
    intro h
    rw [hq0card, Nat.Prime.pow_eq_iff Nat.prime_three] at h
    exact hℓ3 h.1
  have hv : (TauCeti.LieTypeIndex.B 2 q0).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨le_rfl, fun h => hq0ne2 h.2⟩, fun h => hq0ne3 h.2⟩
  let d0 : TauCeti.ValidLieTypeIndex := ⟨.B 2 q0, hv⟩
  have hF0 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d0) = ℓ ^ (f / 3) :=
    CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q0 hv
  have hF0fin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d0) :=
    Nat.finite_of_card_ne_zero (by rw [hF0]; exact pow_ne_zero _ hℓ.ne_zero)
  have hkfin : Finite (descentField σ0) := inferInstance
  let φ : descentField σ0 ≃+* ↥(TauCeti.ValidLieTypeIndex.fixedField d0) := by
    haveI := Fintype.ofFinite (descentField σ0)
    haveI := Fintype.ofFinite ↥(TauCeti.ValidLieTypeIndex.fixedField d0)
    exact FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hpf.2, hF0])
  let ε : Cat d0 ≃* StatedProj (StatedSp 2 (descentField σ0)) :=
    (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q0 hv).trans (statedProjSpCongr φ.symm)
  have hrk0 : RankLE2 3 (Cat d0) :=
    rankLE2_of_injective ((subfieldInj (r := 2) σ0).comp ε.toMonoidHom)
      ((subfieldInj_injective σ0).comp ε.injective) hrk
  have hinj0 : Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 (descentField σ0)) →*
        MulAut (StatedProj (StatedSp 2 (descentField σ0)))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center (StatedProj (StatedSp 2 (descentField σ0))) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ => φ z) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [center_statedProj_statedSp_eq_bot (le_refl 2), Subgroup.mem_bot] at hgc
    exact hgc
  have hinj : Function.Injective (MulAut.conj : Cat d0 →* MulAut (Cat d0)) :=
    conj_injective_of_mulEquiv ε hinj0
  set E₀ : Subgroup (Cat d0) := E₁.map ε.symm.toMonoidHom with hE₀
  have hE₀a : IsElemAbelian 3 E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₁ _
  have hE₀c : Nat.card E₀ = 3 ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective ε.symm.injective, hc₁]
  have hEa : IsElemAbelian 3 (E₀.map (MulAut.conj : Cat d0 →* MulAut (Cat d0))) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀a _
  have hEc : Nat.card (E₀.map (MulAut.conj : Cat d0 →* MulAut (Cat d0))) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hE₀c]
  have hEinner : InnerPlane d0 3 (E₀.map (MulAut.conj : Cat d0 →* MulAut (Cat d0))) := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hpd : 3 ≠ d0.1.characteristic := by
    have : d0.1.characteristic = ℓ := by simp [d0, q0]
    rw [this]
    exact hℓ3.symm
  have hexc0 : ¬ IsD2SeitzException 3 d0.1 := by
    simp [IsD2SeitzException, d0]
  have hPG : PlaneGen (E₀.map (MulAut.conj : Cat d0 →* MulAut (Cat d0))) :=
    seitzInnerLowClassical_of_heisCore unitaryHeisCore d0 3 Nat.prime_three (by norm_num) hpd
      hexc0 _ hEa hEc ⟨hEinner, hrk0, by simp [IsClassicalIndex, d0]⟩
  have hcl := closure_comm_of_planeGen_conj hPG
  rw [eq_top_iff]
  intro g _
  have hg : ε.symm g ∈ Subgroup.closure {k : Cat d0 | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k} := by
    rw [hcl]; trivial
  have h1 := Subgroup.mem_map_of_mem ε.toMonoidHom hg
  rw [MonoidHom.map_closure] at h1
  have h2 : (ε.toMonoidHom '' {k : Cat d0 | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k}) ⊆
      {k | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} := by
    rintro _ ⟨k, ⟨x, ⟨y, hy, rfl⟩, hx1, hk⟩, rfl⟩
    refine ⟨y, hy, ?_, ?_⟩
    · rintro rfl
      exact hx1 (map_one _)
    · have := congrArg ε.toMonoidHom hk
      simpa using this
  simpa using Subgroup.closure_mono h2 h1

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
