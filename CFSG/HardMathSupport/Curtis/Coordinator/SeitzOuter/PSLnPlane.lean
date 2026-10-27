module

public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyClosed
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def centSet {X : Type*} [Group X] (A : Subgroup X) : Set X :=
  {x | ∃ b ∈ A, b ≠ 1 ∧ x * b = b * x}

@[expose] def PlaneCentGen (X : Type*) [Group X] (p : ℕ) : Prop :=
  ∀ A : Subgroup X, IsElemAbelian p A → Nat.card A = p ^ 2 → Subgroup.closure (centSet A) = ⊤

theorem closure_cent_map {X P : Type*} [Group X] [Group P] (e : X ≃* P) {A : Subgroup X}
    (h : Subgroup.closure (centSet A) = ⊤) : Subgroup.closure (centSet (A.map e.toMonoidHom)) = ⊤ := by
  have h1 : Subgroup.map e.toMonoidHom (Subgroup.closure (centSet A)) = ⊤ := by
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]
  rw [MonoidHom.map_closure] at h1
  refine top_le_iff.mp (h1 ▸ Subgroup.closure_mono ?_)
  rintro _ ⟨x, ⟨b, hb, hb1, hxb⟩, rfl⟩
  refine ⟨e b, Subgroup.mem_map_of_mem _ hb, fun h => hb1 (e.injective (by simpa using h)), ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hxb]

theorem PlaneCentGen.of_mulEquiv {X P : Type*} [Group X] [Group P] (e : X ≃* P) {p : ℕ}
    (h : PlaneCentGen X p) : PlaneCentGen P p := by
  intro A hA hAc
  have hA' : A = (A.map e.symm.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map]
    ext x
    simp
  have hel : IsElemAbelian p (A.map e.symm.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hA _
  have hc : Nat.card (A.map e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hAc]
  rw [hA']
  exact closure_cent_map e (h _ hel hc)

noncomputable def catEquivProjectiveSL {m : ℕ} {k : Type} [Field k] [Finite k] {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (he : 0 < e) (hkc : Nat.card k = ℓ ^ e)
    (hv : (TauCeti.LieTypeIndex.A m ⟨ℓ, e, hℓ, he⟩).Valid) :
    Cat ⟨.A m ⟨ℓ, e, hℓ, he⟩, hv⟩ ≃* projectiveSL (m + 1) k := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := Fintype.ofFinite k
  haveI := Fintype.ofFinite (GaloisField ℓ e)
  have hcard : Fintype.card (GaloisField ℓ e) = Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card ℓ e he.ne', hkc]
  exact ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m ⟨ℓ, e, hℓ, he⟩ hv).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)).trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcard))

theorem planeCentGen_projectiveSL
    {m : ℕ} (hm : 2 ≤ m)
    {k : Type} [Field k] [Finite k] {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 0 < e)
    (hkc : Nat.card k = ℓ ^ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hdup : ¬ (ℓ ^ e = 2 ∧ (m = 2 ∨ m = 3)))
    (hexc : ¬ (p = 3 ∧ ℓ = 2 ∧ e = 2 ∧ m = 2))
    (hrk : RankLE2 p (projectiveSL (m + 1) k)) : PlaneCentGen (projectiveSL (m + 1) k) p := by
  have hv : (TauCeti.LieTypeIndex.A m ⟨ℓ, e, hℓ, he⟩).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    simp only [TauCeti.PrimePower.card_def]
    rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩)
    · omega
    · exact hdup ⟨h, Or.inl (by omega)⟩
    · exact hdup ⟨h, Or.inr (by omega)⟩
  set d₀ : TauCeti.ValidLieTypeIndex := ⟨.A m ⟨ℓ, e, hℓ, he⟩, hv⟩ with hd₀
  let e₁ := catEquivProjectiveSL hℓ he hkc hv
  refine PlaneCentGen.of_mulEquiv e₁ ?_
  intro A hA hAc
  have hn3 : 3 ≤ m + 1 := by omega
  have hinj : Function.Injective (MulAut.conj : Cat d₀ →* MulAut (Cat d₀)) := by
    intro x y hxy
    have hz : ∀ z, y⁻¹ * x * z = z * (y⁻¹ * x) := by
      intro z
      have h1 := congrArg (fun φ : MulAut (Cat d₀) => φ (x⁻¹ * y * z * y⁻¹ * x)) hxy
      simp only [MulAut.conj_apply] at h1
      have h2 : x * (x⁻¹ * y * z * y⁻¹ * x) * x⁻¹ = y * (x⁻¹ * y * z * y⁻¹ * x) * y⁻¹ := h1
      have h3 : y * (x⁻¹ * y * z * y⁻¹ * x) * y⁻¹ = y * x⁻¹ * y * z * y⁻¹ * x * y⁻¹ := by group
      have h4 : x * (x⁻¹ * y * z * y⁻¹ * x) * x⁻¹ = y * z * y⁻¹ := by group
      rw [h3, h4] at h2
      calc y⁻¹ * x * z = y⁻¹ * x * (y⁻¹ * (y * z * y⁻¹) * y) := by group
        _ = y⁻¹ * x * (y⁻¹ * (y * x⁻¹ * y * z * y⁻¹ * x * y⁻¹) * y) := by rw [h2]
        _ = z * (y⁻¹ * x) := by group
    have hc : e₁ (y⁻¹ * x) ∈ Subgroup.center (projectiveSL (m + 1) k) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hz (e₁.symm g)
      have h5 := congrArg e₁ this
      simpa using h5.symm
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn3, Subgroup.mem_bot] at hc
    have : y⁻¹ * x = 1 := e₁.injective (by rw [hc, map_one])
    exact (inv_mul_eq_one.mp this).symm
  have hel : IsElemAbelian p (A.map (MulAut.conj : Cat d₀ →* MulAut (Cat d₀))) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hA _
  have hEc : Nat.card (A.map (MulAut.conj : Cat d₀ →* MulAut (Cat d₀))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hAc]
  have hrank : RankLE2 p (Cat d₀) := by
    intro F hF
    have h1 := hrk (F.map e₁.toMonoidHom)
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _)
    rwa [Subgroup.card_map_of_injective e₁.injective] at h1
  have hpd : p ≠ d₀.1.characteristic := by simpa [hd₀] using hpℓ
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d₀.1 := by
    rintro (⟨hp3, ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ |
        ⟨q, hq1, hq2, hd | hd⟩ | hd⟩ | ⟨h5, hd | hd⟩)
    · have := (TauCeti.LieTypeIndex.A.inj hd).1
      omega
    · obtain ⟨hm2, hq⟩ := TauCeti.LieTypeIndex.A.inj hd
      have h1 : ℓ = 2 := by
        have := congrArg TauCeti.PrimePower.p hq
        simpa [hq1] using this
      have h2 : e = 2 := by
        have := congrArg TauCeti.PrimePower.exponent hq
        simpa [hq2] using this
      exact hexc ⟨hp3, h1, h2, by omega⟩
    all_goals cases hd
  have hgen : PlaneGen (A.map (MulAut.conj : Cat d₀ →* MulAut (Cat d₀))) :=
    seitzInnerLowClassical_of_heisCore unitaryHeisCore d₀ p hp hp2 hpd hex _ hel hEc
      ⟨Subgroup.map_le_range _ _, hrank, by unfold IsClassicalIndex; trivial⟩
  refine eq_top_iff.mpr ?_
  rw [← hgen]
  refine Subgroup.closure_mono ?_
  rintro x ⟨ε, ⟨b, hb, rfl⟩, hε1, hεx⟩
  refine ⟨b, hb, fun h => hε1 (by rw [h, map_one]), ?_⟩
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hεx
  exact hεx.symm

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
