module

public import CFSG.LieType.SeitzGeneration.RootPairOrthTailCenter
public import CFSG.LieType.SeitzGeneration.RootPairOrthGen

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical2 (orthDerived)

namespace RootPairOrth

section Inst

variable {K : Type} [Field K] {m : ℕ} {T : Type} [DecidableEq T] {d : ℕ}

@[expose] def starIdx : Fin m ⊕ Fin m ⊕ T → Fin m ⊕ Fin m ⊕ T
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr t) => .inr (.inr t)

@[expose] def hypEmb : Fin m ⊕ Fin m → Fin m ⊕ Fin m ⊕ T
  | .inl i => .inl i
  | .inr i => .inr (.inl i)

omit [DecidableEq T] in
theorem starIdx_starIdx (x : Fin m ⊕ Fin m ⊕ T) : starIdx (starIdx x) = x := by
  rcases x with i | i | t <;> simp [starIdx]

omit [DecidableEq T] in
theorem hypEmb_injective : Function.Injective (hypEmb (m := m) (T := T)) := by
  intro x y h
  rcases x with i | i <;> rcases y with j | j <;> simp [hypEmb] at h ⊢ <;> exact h

omit [DecidableEq T] in
theorem starIdx_hypEmb (x : Fin m ⊕ Fin m) : starIdx (hypEmb (T := T) x) = hypEmb x.swap := by
  rcases x with i | i <;> simp [starIdx, hypEmb]

theorem single_comp_equiv (e : (Fin m ⊕ Fin m ⊕ T) ≃ Fin d) (z : Fin m ⊕ Fin m ⊕ T) :
    (fun i => (Pi.single (e z) 1 : Fin d → K) (e i)) = Pi.single z 1 := by
  funext i
  simp [Pi.single_apply, e.injective.eq_iff, eq_comm]

@[expose] noncomputable def tailCoord [Fintype T] (e : (Fin m ⊕ Fin m ⊕ T) ≃ Fin d)
    (Q' : QuadraticForm K (Fin m ⊕ Fin m ⊕ T → K))
    (hQ : ∀ x : Fin m ⊕ Fin m, Q' (Pi.single (hypEmb x) 1) = 0)
    (hP : ∀ (v : Fin m ⊕ Fin m ⊕ T → K) (x : Fin m ⊕ Fin m),
      polar Q' v (Pi.single (hypEmb x) 1) = v (hypEmb x.swap)) (hm : 3 ≤ m) :
    HypCoord (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexQuadraticForm e Q')
    where
  hyp := Finset.univ.image fun x => e (hypEmb x)
  star a := e (starIdx (e.symm a))
  star_mem a ha := by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨x.swap, Finset.mem_univ _, ?_⟩
    simp [starIdx_hypEmb]
  star_star a _ := by simp [starIdx_starIdx]
  star_ne a ha h := by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    have h1 := e.injective h
    simp only [Equiv.symm_apply_apply, starIdx_hypEmb] at h1
    exact (by rcases x with i | i <;> simp [hypEmb] at h1 : False)
  Q_single a ha := by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexQuadraticForm_apply,
      single_comp_equiv]
    exact hQ x
  polar_single a ha w := by
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    rw [polar_comm]
    change polar Q' (fun i => w (e i)) (fun i => (Pi.single (e (hypEmb x)) 1 : Fin d → K) (e i)) =
      w (e (starIdx (e.symm (e (hypEmb x)))))
    rw [single_comp_equiv, hP, Equiv.symm_apply_apply, starIdx_hypEmb]
  card_hyp := by
    have hinj : Function.Injective fun x : Fin m ⊕ Fin m => e (hypEmb (T := T) x) :=
      e.injective.comp hypEmb_injective
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin]
    omega

theorem mem_tailCoord_hyp [Fintype T] (e : (Fin m ⊕ Fin m ⊕ T) ≃ Fin d)
    (Q' : QuadraticForm K (Fin m ⊕ Fin m ⊕ T → K))
    (hQ : ∀ x : Fin m ⊕ Fin m, Q' (Pi.single (hypEmb x) 1) = 0)
    (hP : ∀ (v : Fin m ⊕ Fin m ⊕ T → K) (x : Fin m ⊕ Fin m),
      polar Q' v (Pi.single (hypEmb x) 1) = v (hypEmb x.swap)) (hm : 3 ≤ m) {a : Fin d} :
    a ∈ (tailCoord e Q' hQ hP hm).hyp ↔ ∃ x, e (hypEmb x) = a := by
  simp [tailCoord]

end Inst

section Pair

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem orthPair_of_hypCoord (S : HypCoord Q)
    (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q)
    (hnd : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0) (hTT : TailPairs S k) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdeg : Module.finrank k K = p)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k)
    (hsetup : ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldSetup k Q₀ Q σ p)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hne : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≠
      subfieldFixedGroup k Q₀ Q) :
    Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
      ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
        Set (matrixProjectiveDerived Q))) = ⊤ := by
  have hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k := fun a =>
    Q_isRat_mem hext (isRat_single k a)
  have hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k := fun a b =>
    polar_isRat_mem hext (isRat_single k a) (isRat_single k b)
  refine orthPair_of_basic (IsBasicT S)
    (fun x y h => ⟨(h.isRat k hQk).1, (h.isRat k hQk).2, h.isTS⟩) ?_ ?_ hext hder hp hp2 hdeg hK
    hk3 hsetup gp hgp hne
  · intro σ hσk g μ hμ hdet hgμ hP
    exact S.rational_of_pairs_T h2 hQk hPk hTT hnd (σ := σ.toRingHom) (fun x => (hσk x).symm) hμ
      hgμ hdet hP
  · intro H hH hrat x y hxy hne' hline
    exact S.elementaryGroup_le_of_basic_line_T H hnd hH hrat hxy hne' hline

end Pair

end RootPairOrth

end CFSG.LieType.SeitzGeneration
