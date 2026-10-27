module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.D4Three.StableSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ6
public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenLevi

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Diag

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)} {d : ℤ}

@[expose] def suppSet (hd : 1 ≤ d) (P : degLayerRoots τ J d → Prop) :
    Set (Lyr (isLayer_degSeries (K := K) (J := J) hd)) :=
  coordMap hd '' {c | ∀ i, ¬ P i → c i = 0}

theorem card_suppSet (hd : 1 ≤ d) (P : degLayerRoots τ J d → Prop) :
    Nat.card (suppSet (K := K) hd P) = Nat.card K ^ Nat.card {i // P i} := by
  classical
  have hinj := (coordMap_bijective (τ := τ) (K := K) (J := J) hd).1
  unfold suppSet
  rw [Nat.card_image_of_injective hinj]
  have e : {c : degLayerRoots τ J d → K | ∀ i, ¬ P i → c i = 0} ≃ ({i // P i} → K) :=
    { toFun := fun c i => c.1 i.1
      invFun := fun f => ⟨fun i => if h : P i then f ⟨i, h⟩ else 0, fun i hi => by simp [hi]⟩
      left_inv := fun c => by
        apply Subtype.ext
        funext i
        by_cases h : P i
        · simp [h]
        · simp [h, c.2 i h]
      right_inv := fun f => by
        funext i
        simp [i.2] }
  rw [Nat.card_congr e, Nat.card_fun]

theorem eq_zero_of_neg_eq_self' (hK2 : ringChar K ≠ 2) {x : K} (h : -x = x) : x = 0 := by
  have h2 : (2 : K) * x = 0 := by linear_combination (-1 : K) * h
  exact (mul_eq_zero.1 h2).resolve_left (Ring.two_ne_zero hK2)

theorem inf_fixSp_diag (hd : 1 ≤ d) (hK2 : ringChar K ≠ 2)
    {T T' : Lyr (isLayer_degSeries (K := K) (J := J) hd) →ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd)}
    (f f' : degLayerRoots τ J d → K) (P P' : degLayerRoots τ J d → Prop)
    (hT : ∀ c, T (coordMap hd c) = coordMap hd (fun i => f i * c i))
    (hT' : ∀ c, T' (coordMap hd c) = coordMap hd (fun i => f' i * c i))
    (hf : ∀ i, (P i ∧ f i = 1) ∨ (¬ P i ∧ f i = -1))
    (hf' : ∀ i, (P' i ∧ f' i = 1) ∨ (¬ P' i ∧ f' i = -1)) :
    ((fixSp T ⊓ fixSp T' : Submodule (ZMod 3) (Lyr (isLayer_degSeries (K := K) (J := J) hd))) :
      Set (Lyr (isLayer_degSeries (K := K) (J := J) hd))) =
      suppSet (K := K) (J := J) hd (fun i => P i ∧ P' i) := by
  have hbij := coordMap_bijective (τ := τ) (K := K) (J := J) hd
  have hinj := hbij.1
  ext z
  obtain ⟨c, rfl⟩ := hbij.2 z
  simp only [SetLike.mem_coe, Submodule.mem_inf, mem_fixSp, hT, hT', suppSet, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := fun i => congrFun (hinj h1) i
    have h2' := fun i => congrFun (hinj h2) i
    refine ⟨c, fun i hi => ?_, rfl⟩
    by_cases hP : P i
    · have hP' : ¬ P' i := fun h => hi ⟨hP, h⟩
      rcases hf' i with ⟨h, _⟩ | ⟨_, hfi⟩
      · exact absurd h hP'
      · have := h2' i
        rw [hfi] at this
        exact eq_zero_of_neg_eq_self' hK2 (by simpa using this)
    · rcases hf i with ⟨h, _⟩ | ⟨_, hfi⟩
      · exact absurd h hP
      · have := h1' i
        rw [hfi] at this
        exact eq_zero_of_neg_eq_self' hK2 (by simpa using this)
  · rintro ⟨c', hc', hcc'⟩
    have := hinj hcc'
    subst this
    have key : ∀ (f : degLayerRoots τ J d → K) (P : degLayerRoots τ J d → Prop),
        (∀ i, (P i ∧ f i = 1) ∨ (¬ P i ∧ f i = -1)) → (∀ i, ¬ P i → c' i = 0) →
        coordMap hd (fun i => f i * c' i) = coordMap hd c' := by
      intro f P hf hz
      congr 1
      funext i
      rcases hf i with ⟨_, hfi⟩ | ⟨hP, _⟩
      · rw [hfi, one_mul]
      · rw [hz i hP]; simp
    exact ⟨key f P hf (fun i hi => hc' i (fun h => hi h.1)),
      key f' P' hf' (fun i hi => hc' i (fun h => hi h.2))⟩

theorem card_inf_fixSp_diag (hd : 1 ≤ d) (hK2 : ringChar K ≠ 2)
    {T T' : Lyr (isLayer_degSeries (K := K) (J := J) hd) →ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd)}
    (f f' : degLayerRoots τ J d → K) (P P' : degLayerRoots τ J d → Prop)
    (hT : ∀ c, T (coordMap hd c) = coordMap hd (fun i => f i * c i))
    (hT' : ∀ c, T' (coordMap hd c) = coordMap hd (fun i => f' i * c i))
    (hf : ∀ i, (P i ∧ f i = 1) ∨ (¬ P i ∧ f i = -1))
    (hf' : ∀ i, (P' i ∧ f' i = 1) ∨ (¬ P' i ∧ f' i = -1)) :
    Nat.card (fixSp T ⊓ fixSp T' : Submodule (ZMod 3)
        (Lyr (isLayer_degSeries (K := K) (J := J) hd))) =
      Nat.card K ^ Nat.card {i // P i ∧ P' i} := by
  have h := inf_fixSp_diag hd hK2 f f' P P' hT hT' hf hf'
  rw [← card_suppSet (K := K) (J := J) hd (fun i => P i ∧ P' i), ← h]
  exact Nat.card_congr (Equiv.refl _)

theorem card_fixSp_diag (hd : 1 ≤ d) (hK2 : ringChar K ≠ 2)
    {T : Lyr (isLayer_degSeries (K := K) (J := J) hd) →ₗ[ZMod 3]
      Lyr (isLayer_degSeries (K := K) (J := J) hd)}
    (f : degLayerRoots τ J d → K) (P : degLayerRoots τ J d → Prop)
    (hT : ∀ c, T (coordMap hd c) = coordMap hd (fun i => f i * c i))
    (hf : ∀ i, (P i ∧ f i = 1) ∨ (¬ P i ∧ f i = -1)) :
    Nat.card (fixSp T) = Nat.card K ^ Nat.card {i // P i} := by
  have h := card_inf_fixSp_diag hd hK2 f f P P hT hT hf hf
  rw [inf_idem] at h
  simpa using h

theorem exists_card_pow (hd : 1 ≤ d) (u : Kˣ → Fin τ.rank → Kˣ)
    (hu : ∀ μ : Kˣ, ∀ i : degLayerRoots τ J d, ((rootChar (u μ) i.1 : Kˣ) : K) = μ)
    (F : Submodule (ZMod 3) (Lyr (isLayer_degSeries (K := K) (J := J) hd)))
    (hF : ∀ μ : Kˣ, ∀ z ∈ F, conjL (u μ) hd z ∈ F) :
    ∃ k : ℕ, Nat.card F = Nat.card K ^ k := by
  classical
  have hbij := coordMap_bijective (τ := τ) (K := K) (J := J) hd
  let F' : Submodule K (degLayerRoots τ J d → K) :=
    { carrier := {c | coordMap hd c ∈ F}
      add_mem' := fun {a b} ha hb => by
        show coordMap hd (a + b) ∈ F
        rw [map_add]
        exact F.add_mem ha hb
      zero_mem' := by
        show coordMap hd 0 ∈ F
        rw [map_zero]
        exact F.zero_mem
      smul_mem' := fun μ c hc => by
        show coordMap hd (μ • c) ∈ F
        by_cases hμ : μ = 0
        · rw [hμ, zero_smul, map_zero]
          exact F.zero_mem
        · have h := hF (Units.mk0 μ hμ) _ hc
          rw [conjL_coordMap] at h
          have e : (μ • c : degLayerRoots τ J d → K) =
              fun i => ((rootChar (u (Units.mk0 μ hμ)) i.1 : Kˣ) : K) * c i := by
            funext i
            rw [hu, Pi.smul_apply, smul_eq_mul]
            rfl
          rw [e]
          exact h }
  refine ⟨Module.finrank K F', ?_⟩
  rw [← Module.natCard_eq_pow_finrank (K := K) (V := F')]
  refine (Nat.card_congr (Equiv.ofBijective (fun x : F' => (⟨coordMap hd x.1, x.2⟩ : F))
    ⟨fun x y h => Subtype.ext (hbij.1 (congrArg Subtype.val h)), fun z => ?_⟩)).symm
  obtain ⟨c, hc⟩ := hbij.2 z.1
  exact ⟨⟨c, show coordMap hd c ∈ F by rw [hc]; exact z.2⟩, Subtype.ext hc⟩

end Diag

end CFSG.LocalAnalysis.GLTheoremA
