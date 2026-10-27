module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.ComponentClassification.CatLeafProof (weylWordElt)
open CFSG.RankThree.Chevalley (wordRep)
open CFSG.StandardType.TableBExc.E6Three (mapsRootLines_rootDiagUnit)
open CFSG.LieType.Chevalley.RootWalk (hVecSum hStep hVecSum_single prod_weylElt_hVecSum)

set_option linter.unusedSectionVars false

section Orbits

variable {ι : Type*} [Fintype ι]

private theorem e6InF_exists_reps (σ : ι → ι) (h3 : ∀ x, σ (σ (σ x)) = x)
    (h1 : ∀ x, σ x ≠ x) :
    ∃ R : Finset ι, 3 * R.card = Fintype.card ι ∧
      (∀ x, ∃ r ∈ R, x = r ∨ x = σ r ∨ x = σ (σ r)) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ≠ σ r ∧ r' ≠ σ (σ r) := by
  classical
  obtain ⟨rep, hrep, hrepσ⟩ : ∃ rep : ι → ι, (∀ x, rep x = x ∨ rep x = σ x ∨ rep x = σ (σ x)) ∧
      ∀ x, rep (σ x) = rep x := by
    set e := Fintype.equivFin ι
    refine ⟨fun x => e.symm (min (e x) (min (e (σ x)) (e (σ (σ x))))), fun x => ?_, fun x => ?_⟩
    · dsimp only
      rcases min_choice (e x) (min (e (σ x)) (e (σ (σ x)))) with h | h <;> rw [h]
      · exact Or.inl (e.symm_apply_apply x)
      · rcases min_choice (e (σ x)) (e (σ (σ x))) with h' | h' <;> rw [h']
        · exact Or.inr (Or.inl (e.symm_apply_apply _))
        · exact Or.inr (Or.inr (e.symm_apply_apply _))
    · dsimp only
      rw [h3, min_comm (e (σ (σ x))) (e x), min_left_comm]
  have hrr : ∀ x, rep (rep x) = rep x := by
    intro x
    rcases hrep x with h | h | h <;> rw [h]
    · exact h
    · rw [hrepσ, h]
    · rw [hrepσ, hrepσ, h]
  have hσσ : ∀ x, σ (σ x) ≠ x := fun x h => h1 x (by
    have h' := congrArg σ h
    rwa [h3, eq_comm] at h')
  have hfib : ∀ r, rep r = r → Finset.univ.filter (fun x => rep x = r) = {r, σ r, σ (σ r)} := by
    intro r hr
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      rcases hrep x with h | h | h
      · exact Or.inl (h.symm.trans hx)
      · refine Or.inr (Or.inr ?_)
        rw [← hx, h, h3]
      · refine Or.inr (Or.inl ?_)
        rw [← hx, h, h3]
    · rintro (rfl | rfl | rfl)
      · exact hr
      · rw [hrepσ, hr]
      · rw [hrepσ, hrepσ, hr]
  refine ⟨Finset.univ.filter (fun x => rep x = x), ?_, fun x => ?_, fun r hr r' hr' => ?_⟩
  · have hcard : Fintype.card ι = ∑ r ∈ Finset.univ.filter (fun x => rep x = x),
        (Finset.univ.filter (fun x => rep x = r)).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise (fun x _ => by simp [hrr])
    have h3c : ∀ r ∈ Finset.univ.filter (fun x => rep x = x),
        (Finset.univ.filter (fun x => rep x = r)).card = 3 := by
      intro r hr
      rw [hfib r (Finset.mem_filter.1 hr).2, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using (h1 (σ r)).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(h1 r).symm, (hσσ r).symm⟩
    rw [hcard, Finset.sum_congr rfl h3c, Finset.sum_const, smul_eq_mul, mul_comm]
  · refine ⟨rep x, by simp [hrr], ?_⟩
    rcases hrep x with h | h | h
    · exact Or.inl h.symm
    · refine Or.inr (Or.inr ?_)
      rw [h, h3]
    · refine Or.inr (Or.inl ?_)
      rw [h, h3]
  · have hr0 : rep r = r := (Finset.mem_filter.1 hr).2
    have hr0' : rep r' = r' := (Finset.mem_filter.1 hr').2
    refine ⟨fun h => h1 r ?_, fun h => hσσ r ?_⟩
    · rw [← h, ← hr0', h, hrepσ, hr0]
    · rw [← h, ← hr0', h, hrepσ, hrepσ, hr0]

end Orbits

section Fixed

variable {K : Type*} [Field K] {κ ι : Type*} [Fintype κ] [Fintype ι]

private theorem e6InF_finrank_fix (h3K : (3 : K) ≠ 0) (S : Module.End K (κ ⊕ ι →₀ K))
    (hS3 : S ^ 3 = 1) (σ : ι → ι) (hσ3 : ∀ x, σ (σ (σ x)) = x) (hσ1 : ∀ x, σ x ≠ x)
    (c : ι → K)
    (hSr : ∀ i, S (Finsupp.single (Sum.inr i) 1) = c i • Finsupp.single (Sum.inr (σ i)) 1)
    (hSh : ∀ j i, S (Finsupp.single (Sum.inl j) 1) (Sum.inr i) = 0)
    (hPh : ∀ j, Finsupp.single (Sum.inl j) 1 + S (Finsupp.single (Sum.inl j) 1) +
      S (S (Finsupp.single (Sum.inl j) 1)) = 0) :
    3 * Module.finrank K (LinearMap.ker (S - 1)) = Fintype.card ι := by
  classical
  obtain ⟨R, hRc, hR1, hR2⟩ := e6InF_exists_reps σ hσ3 hσ1
  set F := LinearMap.ker (S - 1) with hF
  have hmem : ∀ x, x ∈ F ↔ S x = x := fun x => by
    rw [hF, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hS3' : ∀ z, S (S (S z)) = z := fun z => by
    have h := LinearMap.congr_fun hS3 z
    rwa [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply] at h
  have hσinj : Function.Injective σ := fun a b h => by
    rw [← hσ3 a, ← hσ3 b, h]
  have hsingle : ∀ (b : κ ⊕ ι) (a : K), Finsupp.single b a = a • Finsupp.single b 1 :=
    fun b a => by rw [Finsupp.smul_single_one]
  have hcoef : ∀ (x : κ ⊕ ι →₀ K) (i : ι), S x (Sum.inr (σ i)) = c i * x (Sum.inr i) := by
    intro x i
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg, mul_add]
    | single b a =>
      rw [hsingle b a, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
        smul_eq_mul]
      rcases b with j | i'
      · rw [hSh, Finsupp.single_apply, if_neg Sum.inl_ne_inr]
        ring
      · rw [hSr, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Finsupp.single_apply]
        by_cases hi : i' = i
        · subst hi
          simp only [if_true]
          ring
        · rw [if_neg (fun h => hi (hσinj (Sum.inr_injective h))),
            if_neg (fun h => hi (Sum.inr_injective h))]
          ring
  have hPinl : ∀ (x : κ ⊕ ι →₀ K) (k : κ), (x + S x + S (S x)) (Sum.inl k) = 0 := by
    intro x k
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      have e : f + g + S (f + g) + S (S (f + g)) = (f + S f + S (S f)) + (g + S g + S (S g)) := by
        simp only [map_add]
        abel
      rw [e, Finsupp.add_apply, hf, hg, add_zero]
    | single b a =>
      have e : Finsupp.single b a + S (Finsupp.single b a) + S (S (Finsupp.single b a)) =
          a • (Finsupp.single b 1 + S (Finsupp.single b 1) + S (S (Finsupp.single b 1))) := by
        rw [hsingle b a]
        simp only [map_smul, smul_add]
      rw [e, Finsupp.smul_apply]
      rcases b with j | i
      · rw [hPh, Finsupp.zero_apply, smul_zero]
      · rw [hSr, map_smul, hSr]
        simp [Finsupp.single_apply]
  have hFinl : ∀ x ∈ F, ∀ k, x (Sum.inl k) = 0 := by
    intro x hx k
    have hSx := (hmem x).1 hx
    have h := hPinl x k
    rw [hSx, hSx, Finsupp.add_apply, Finsupp.add_apply] at h
    have h' : (3 : K) * x (Sum.inl k) = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_left h3K
  have hFinr : ∀ x ∈ F, ∀ i, x (Sum.inr (σ i)) = c i * x (Sum.inr i) := by
    intro x hx i
    rw [← hcoef x i, (hmem x).1 hx]
  let Ψ : F →ₗ[K] (R → K) :=
    { toFun := fun x r => (x : κ ⊕ ι →₀ K) (Sum.inr (r : ι))
      map_add' := fun x y => by
        funext r
        simp
      map_smul' := fun a x => by
        funext r
        simp }
  have hΨ : Function.Injective Ψ := by
    have key : Function.Injective Ψ ↔ ∀ x, Ψ x = 0 → x = 0 := injective_iff_map_eq_zero Ψ
    refine key.2 fun x hx => ?_
    have h0 : ∀ r ∈ R, (x : κ ⊕ ι →₀ K) (Sum.inr r) = 0 := fun r hr => congrFun hx ⟨r, hr⟩
    have hx0 : (x : κ ⊕ ι →₀ K) = 0 := by
      refine Finsupp.ext fun b => ?_
      rw [Finsupp.zero_apply]
      rcases b with k | i
      · exact hFinl x x.2 k
      · obtain ⟨r, hr, hi⟩ := hR1 i
        rcases hi with h | h | h <;> rw [h]
        · exact h0 r hr
        · rw [hFinr x x.2, h0 r hr, mul_zero]
        · rw [hFinr x x.2, hFinr x x.2, h0 r hr, mul_zero, mul_zero]
    exact Subtype.ext hx0
  let y : R → F := fun r => ⟨Finsupp.single (Sum.inr (r : ι)) 1 +
      S (Finsupp.single (Sum.inr (r : ι)) 1) + S (S (Finsupp.single (Sum.inr (r : ι)) 1)), by
    rw [hmem, map_add, map_add, hS3']
    abel⟩
  have hΨy : ∀ r, Ψ (y r) = Pi.single r 1 := by
    intro r
    funext r'
    have hne := hR2 r r.2 r' r'.2
    change (Finsupp.single (Sum.inr (r : ι)) 1 + S (Finsupp.single (Sum.inr (r : ι)) 1) +
      S (S (Finsupp.single (Sum.inr (r : ι)) 1)) : κ ⊕ ι →₀ K) (Sum.inr (r' : ι)) =
        (Pi.single r (1 : K) : R → K) r'
    rw [hSr, map_smul, hSr]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
      Sum.inr.injEq, Pi.single_apply]
    rw [if_neg (Ne.symm hne.1), if_neg (Ne.symm hne.2)]
    by_cases hrr : r' = r
    · subst hrr
      simp
    · rw [if_neg (fun h => hrr (Subtype.ext h.symm)), if_neg hrr]
      ring
  have hle : Module.finrank K F ≤ R.card := by
    have h := LinearMap.finrank_le_finrank_of_injective hΨ
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  have hge : R.card ≤ Module.finrank K F := by
    have hli : LinearIndependent K y := by
      refine LinearIndependent.of_comp Ψ ?_
      have e : (Ψ ∘ y) = ⇑(Pi.basisFun K R) := funext fun r => by
        rw [Function.comp_apply, hΨy, Pi.basisFun_apply]
      rw [e]
      exact (Pi.basisFun K R).linearIndependent
    have h := hli.fintype_card_le_finrank
    rwa [Fintype.card_coe] at h
  rw [← hRc, le_antisymm hle hge]

end Fixed

private theorem e6InF_sum_eq_zero {v : WeylGroup Tag.E6} (hv3 : v ^ 3 = 1)
    (hv : ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 → ¬ FixesForm v l) (β : Fin Tag.E6.rank → ℤ) :
    β + v • β + v • v • β = 0 := by
  let N : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := fun β => β + v • β + v • v • β
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [smul_add]
        abel }
  have hN : ∀ γ, N γ = γ + v • γ + v • v • γ := fun _ => rfl
  have hNv : ∀ γ, N (v • γ) = N γ := by
    intro γ
    have h3v : v • v • v • γ = γ := by
      rw [smul_smul, smul_smul, ← pow_three', hv3, one_smul]
    rw [hN, hN, h3v]
    abel
  have hlin : ∀ (k : Fin Tag.E6.rank) (γ : Fin Tag.E6.rank → ℤ),
      ∑ i, N (Pi.single i 1) k * γ i = N γ k := by
    intro k γ
    conv_rhs => rw [← Finset.univ_sum_single γ]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Pi.single i (γ i) : Fin Tag.E6.rank → ℤ) = γ i • Pi.single i 1 := by
      ext j
      rcases eq_or_ne j i with rfl | h <;> simp [*]
    rw [e, map_zsmul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hk : ∀ k, N β k = 0 := by
    intro k
    by_contra hne
    refine hv (fun i => N (Pi.single i 1) k) (fun h0 => hne ?_) (fun γ => ?_)
    · rw [← hlin k β]
      exact Finset.sum_eq_zero fun i _ => by rw [show N (Pi.single i 1) k = 0 from congrFun h0 i,
        zero_mul]
    · rw [hlin, hlin, hNv]
  funext k
  exact hk k

private def e6InF_eps (k : Fin Tag.E6.rank) : ℤ :=
  if k.val = 1 ∨ k.val = 2 ∨ k.val = 4 then -1 else 1

private theorem e6InF_eps_mul_self : e6InF_eps * e6InF_eps = 1 := by
  funext k
  revert k
  decide +kernel

private theorem e6InF_cartan_eps : ∀ i j : Fin Tag.E6.rank,
    ((Tag.E6.cartan j i).natAbs : ℤ) = e6InF_eps i * e6InF_eps j * Tag.E6.cartan i j := by
  decide +kernel

private theorem e6InF_hStep (i : Fin Tag.E6.rank) (c : Fin Tag.E6.rank → ℤ) :
    hStep Tag.E6 i c = e6InF_eps * reflect Tag.E6 i (e6InF_eps * c) := by
  have hε : ∀ k, e6InF_eps k * e6InF_eps k = 1 := fun k => congrFun e6InF_eps_mul_self k
  funext k
  simp only [hStep, reflect, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  by_cases hki : k = i
  · subst hki
    simp only [if_true, mul_one]
    have hs : ∑ j, ((Tag.E6.cartan j k).natAbs : ℤ) * c j =
        e6InF_eps k * ∑ j, Tag.E6.cartan k j * (e6InF_eps j * c j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e6InF_cartan_eps k j]
      ring
    rw [hs]
    linear_combination (-c k) * hε k
  · simp only [hki, if_false, mul_zero, sub_zero]
    rw [← mul_assoc, hε k, one_mul]

private theorem e6InF_foldr_hStep (μ : List (Fin Tag.E6.rank)) (c : Fin Tag.E6.rank → ℤ) :
    μ.foldr (hStep Tag.E6) c =
      e6InF_eps * ((coxeterSystem Tag.E6).wordProd μ • (e6InF_eps * c)) := by
  induction μ with
  | nil => rw [List.foldr_nil, CoxeterSystem.wordProd_nil, one_smul, ← mul_assoc,
      e6InF_eps_mul_self, one_mul]
  | cons i μ ih =>
    rw [List.foldr_cons, ih, e6InF_hStep, ← mul_assoc, e6InF_eps_mul_self, one_mul,
      CoxeterSystem.wordProd_cons, mul_smul]
    rfl

private theorem e6InF_hVecSum_add {K : Type*} [Field K] (a b : Fin Tag.E6.rank → ℤ) :
    hVecSum K (a + b) = hVecSum K a + hVecSum K b := by
  simp only [hVecSum, Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

private theorem e6InF_hVecSum_zero {K : Type*} [Field K] :
    hVecSum K (0 : Fin Tag.E6.rank → ℤ) = 0 := by
  simp [hVecSum]

section Fix24


theorem e6MonoEllipticFix24_holds : E6MonoEllipticFix24 := by
  intro K _ _ hK3 hK s hs3 v hBm hv
  classical
  have hK4 : 4 ≤ Nat.card K := e6Cen_four_le_card hK
  have h3K : (3 : K) ≠ 0 := by
    intro h0
    have hd : ringChar K ∣ 3 := (ringChar.spec K 3).mp (by exact_mod_cast h0)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact CharP.ringChar_ne_one h1
    · exact hK3 h3
  have hv3 : v ^ 3 = 1 := by
    have h := hBm.pow 3
    rw [← map_pow, hs3, map_one] at h
    exact (BmMono.unique hK4 bmMono_one h).symm
  have hN := e6InF_sum_eq_zero hv3 hv
  obtain ⟨μ, hμ⟩ := (coxeterSystem Tag.E6).wordProd_surjective v
  rw [← hμ] at hBm
  obtain ⟨b, hb⟩ := hBm.exists_eq_word
  have hs : (s : ModGL Tag.E6 K) =
      (weylWordElt .E6 K μ : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b :=
    e6Cen_coe_eq_of_conj_eq hK4 hb
  set S : Module.End K (RootModule Tag.E6 K) :=
    ((s : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) with hSdef
  have hS3 : S ^ 3 = 1 := by
    rw [hSdef, ← Units.val_pow_eq_pow_val, ← SubgroupClass.coe_pow, hs3]
    rfl
  have hSh : ∀ c : Fin Tag.E6.rank → ℤ,
      S (hVecSum K c) = hVecSum K (μ.foldr (hStep Tag.E6) c) := by
    intro c
    have hd : rootDiag b (hVecSum K c) = hVecSum K c := by
      simp only [hVecSum, map_sum, map_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [hVec, rootDiag_single_inl]
    rw [hSdef, hs, coe_weylWordElt, Units.val_mul, Module.End.mul_apply]
    change ((wordRep Tag.E6 K μ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
      (rootDiag b (hVecSum K c)) = _
    rw [hd]
    exact prod_weylElt_hVecSum K μ c
  have hPh : ∀ j, Finsupp.single (Sum.inl j) 1 + S (Finsupp.single (Sum.inl j) 1) +
      S (S (Finsupp.single (Sum.inl j) 1)) = (0 : RootModule Tag.E6 K) := by
    intro j
    rw [show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K j from rfl,
      ← hVecSum_single, hSh, hSh, ← e6InF_hVecSum_add, ← e6InF_hVecSum_add,
      e6InF_foldr_hStep, e6InF_foldr_hStep, hμ]
    convert e6InF_hVecSum_zero (K := K) using 2
    set β : Fin Tag.E6.rank → ℤ := e6InF_eps * Pi.single j 1
    have hβ : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = e6InF_eps * β := by
      rw [← mul_assoc, e6InF_eps_mul_self, one_mul]
    rw [← mul_assoc e6InF_eps e6InF_eps, e6InF_eps_mul_self, one_mul, hβ, ← mul_add, ← mul_add,
      hN, mul_zero]
  have hShr : ∀ (j : Fin Tag.E6.rank) (i : {β : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 β}),
      S (Finsupp.single (Sum.inl j) 1) (Sum.inr i) = 0 := by
    intro j i
    rw [show (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 K) = hVec Tag.E6 K j from rfl,
      ← hVecSum_single, hSh]
    simp [hVecSum, hVec, Finsupp.single_apply]
  have hMR : MapsRootLines (s : ModGL Tag.E6 K) v := by
    have h := (bm_mapsRootLines_weylWordElt (K := K) μ).mul
      (mapsRootLines_rootDiagUnit (τ := Tag.E6) (K := K) b)
    rwa [mul_one, ← hs, hμ] at h
  choose c hc using fun β : {β : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 β} => hMR β.1 β.2
  let σ : {β : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 β} →
      {β : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 β} := fun β => ⟨v • β.1, IsRoot.smul β.2 v⟩
  have hσ3 : ∀ β, σ (σ (σ β)) = β := fun β => Subtype.ext (by
    change v • v • v • β.1 = β.1
    rw [smul_smul, smul_smul, ← pow_three', hv3, one_smul])
  have hσ1 : ∀ β, σ β ≠ β := by
    intro β h
    have h1 : v • β.1 = β.1 := congrArg Subtype.val h
    have h2 := hN β.1
    rw [h1, h1] at h2
    refine β.2.ne_zero (funext fun k => ?_)
    have h3 := congrFun h2 k
    simp only [Pi.add_apply, Pi.zero_apply] at h3 ⊢
    omega
  have hSr : ∀ β, S (Finsupp.single (Sum.inr β) 1) =
      ((c β : Kˣ) : K) • Finsupp.single (Sum.inr (σ β)) 1 := by
    intro β
    have h := hc β
    rw [rootVec_eq_single_of_isRoot β.2, rootVec_eq_single_of_isRoot (IsRoot.smul β.2 v)] at h
    exact h
  have h72 := e6InF_finrank_fix h3K S hS3 σ hσ3 hσ1 (fun β => ((c β : Kˣ) : K)) hSr hShr hPh
  rw [card_isRoot] at h72
  have h72' : 3 * Module.finrank K (LinearMap.ker (S - 1)) = 3 * 24 := h72
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h72'

end Fix24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
