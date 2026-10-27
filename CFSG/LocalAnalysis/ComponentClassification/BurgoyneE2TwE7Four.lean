module

public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LieType.Chevalley.RationalToralSignDiagramE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Frame

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ComponentClassification.CatLeafProof


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem e7Word2_1_four : applyWordIdx e7Certificate e7Word2_1 4 = 4 := by
  decide +kernel

theorem thetaMap_e7Word2_1_four :
    thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 (Pi.single (e7Node 4) 1) =
      Pi.single (e7Node 4) 1 := by
  obtain ⟨hl4, hr4⟩ := root_fin e7Certificate_check (e7Node 4)
  obtain ⟨-, he⟩ := applyWordIdx_spec e7Certificate_check e7Word2_1 hl4
  change ToralSign.wordElt .E7 e7Word2_1 • (Pi.single (e7Node 4) 1 : Fin (Tag.rank .E7) → ℤ) = _
  rw [← hr4, ← he]
  change e7Certificate.root (applyWordIdx e7Certificate e7Word2_1 4) = _
  rw [e7Word2_1_four]
  rfl

section Four

variable (D : OrthogonalSemilinearFixedRootDatum .E7 p k)

theorem thetaOrbit_four
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ)) :
    thetaOrbit D.θ (Pi.single (e7Node 4) 1) = {Pi.single (e7Node 4) 1} := by
  have h1 : D.θ (toReal (Pi.single (e7Node 4) 1 : Fin (Tag.rank .E7) → ℤ)) =
      toReal (Pi.single (e7Node 4) 1 : Fin (Tag.rank .E7) → ℤ) := by
    rw [hθ, thetaMap_e7Word2_1_four]
  have hpow : ∀ m : ℕ, (D.θ ^ m) (toReal (Pi.single (e7Node 4) 1 : Fin (Tag.rank .E7) → ℤ)) =
      toReal (Pi.single (e7Node 4) 1 : Fin (Tag.rank .E7) → ℤ) := by
    intro m
    induction m with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ m ih => rw [pow_succ, Module.End.mul_apply, h1, ih]
  ext β
  simp only [thetaOrbit, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm⟩
    rw [hpow] at hm
    exact (toReal_injective hm).symm
  · rintro rfl
    exact ⟨0, by rw [pow_zero, Module.End.one_apply]⟩

theorem orbitMap_four
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (hΔ : Pi.single (e7Node 4) 1 ∈ D.simpleRootsJ) :
    ({Pi.single (e7Node 4) 1} : Set (Fin (Tag.rank .E7) → ℤ)) ∈ D.orbits ∧
      orbitCard ({Pi.single (e7Node 4) 1} : Set (Fin (Tag.rank .E7) → ℤ)) = 1 ∧
      ∀ A, D.orbitMap {Pi.single (e7Node 4) 1} A = rootSL2 .E7 k (Pi.single (e7Node 4) 1)
        (Matrix.SpecialLinearGroup.map (D.orbitField {Pi.single (e7Node 4) 1}).subtype A) := by
  have hO : ({Pi.single (e7Node 4) 1} : Set (Fin (Tag.rank .E7) → ℤ)) ∈ D.orbits :=
    ⟨_, hΔ, (thetaOrbit_four D hθ).symm⟩
  have hcard : orbitCard ({Pi.single (e7Node 4) 1} : Set (Fin (Tag.rank .E7) → ℤ)) = 1 :=
    Set.ncard_singleton _
  have hroot : orbitRoot ({Pi.single (e7Node 4) 1} : Set (Fin (Tag.rank .E7) → ℤ)) =
      Pi.single (e7Node 4) 1 := D.orbitRoot_mem hO
  refine ⟨hO, hcard, fun A => ?_⟩
  rw [D.orbitMap_eq_prod, hcard, List.range_one, List.map_singleton, List.prod_singleton,
    D.orbitFactor_apply, D.orbitVec_zero, hroot, mul_zero, iterateFrobenius_zero]
  congr 1

theorem exists_involution_orbitGroup
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (hΔ : Pi.single (e7Node 4) 1 ∈ D.simpleRootsJ) :
    ∃ w ∈ D.orbitGroup, w ≠ 1 ∧ w * w = 1 := by
  obtain ⟨hO, -, hmap⟩ := orbitMap_four D hθ hΔ
  refine ⟨D.orbitMap _ (-1), D.orbitMap_mem_orbitGroup hO _, ?_, ?_⟩
  · have hneg : Matrix.SpecialLinearGroup.map (D.orbitField {Pi.single (e7Node 4) 1}).subtype
        (-1 : SL2 (D.orbitField {Pi.single (e7Node 4) 1})) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hmap, hneg]
    intro h1
    have hk2' : ringChar k ≠ 2 := by
      rw [ringChar.eq k p]
      exact D.odd
    obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ :=
      exceptional_Lang_root_rank_one_data .E7 k (Pi.single (e7Node 4) 1)
    have h2 := (hinj hk2').1 (h1.trans (map_one _).symm)
    have h3 := congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h2
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h3
    have hk2 : ringChar k ≠ 2 := by
      rw [ringChar.eq k p]
      exact D.odd
    exact Ring.neg_one_ne_one_of_char_ne_two hk2 h3
  · rw [← D.orbitMap_mul hO, neg_one_mul, neg_neg]
    exact D.orbitMap_one _

end Four

theorem e7Word2_1_mem_omegaWords {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    (hm : r.mask = 2 ∨ r.mask = 3) : e7Word2_1 ∈ r.omegaWords := by
  simp only [e7SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simp at hm
  · simp at hm
  · exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)
  · exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)

theorem e7Word2_1_ne_nil : e7Word2_1 ≠ [] := by
  unfold e7Word2_1
  exact List.cons_ne_nil _ _

theorem three_le_q (D : OrthogonalSemilinearFixedRootDatum .E7 p k) : 3 ≤ D.q := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h D.odd
    · have := hp.two_le
      obtain ⟨m, hm⟩ := h
      omega
  calc 3 ≤ p := h3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ D.e := Nat.pow_le_pow_right hp.pos D.one_le_e

theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {g : G} (hg : g ^ 2 = 1)
    (hodd : Odd (orderOf g)) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
