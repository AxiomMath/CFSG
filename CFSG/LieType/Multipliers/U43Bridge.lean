module

public import CFSG.LieType.Multipliers.U43Data
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import Certificates.Certificate10012
public import CFSG.LieType.Multipliers.CoverBounds
public meta import CFSG.LieType.Multipliers.U43Data
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public meta import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U43Action
public meta import CFSG.LieType.Multipliers.U43Action
public meta import CFSG.Open.Defs

public section

namespace CFSG.LieType.Multipliers.U43

open Matrix CFSG.Assembly.LowTwoRank CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.CosetTable

@[expose] def mv4 (A : Matrix (Fin 4) (Fin 4) F9) (v : V) : V :=
  fun i => A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 + A i 3 * v 3

theorem mulVec_eq_mv4 (A : Matrix (Fin 4) (Fin 4) F9) (v : V) : A *ᵥ v = mv4 A v := by
  funext i
  simp [mulVec, dotProduct, Fin.sum_univ_four, mv4]

theorem matA_unitary : (matA.map (· ^ 3))ᵀ * matA = 1 := by decide +kernel
theorem matB_unitary : (matB.map (· ^ 3))ᵀ * matB = 1 := by decide +kernel
theorem det_matA : matA.det = 1 := by decide +kernel
theorem det_matB : matB.det = 1 := by decide +kernel

noncomputable def suA : StatedSU 4 3 F9 :=
  ⟨GeneralLinearGroup.mk'' matA (by rw [det_matA]; exact isUnit_one),
    Subgroup.subset_closure ⟨det_matA, matA_unitary⟩⟩

noncomputable def suB : StatedSU 4 3 F9 :=
  ⟨GeneralLinearGroup.mk'' matB (by rw [det_matB]; exact isUnit_one),
    Subgroup.subset_closure ⟨det_matB, matB_unitary⟩⟩

noncomputable def xElt : X₀ := QuotientGroup.mk suA

noncomputable def yElt : X₀ := QuotientGroup.mk suB

theorem tabA_spec : ∀ i : Fin 820, tabA[(i : ℕ)]! = ptIndex (mv4 matA (decode i)) := by
  decide +kernel

theorem tabB_spec : ∀ i : Fin 820, tabB[(i : ℕ)]! = ptIndex (mv4 matB (decode i)) := by
  decide +kernel

theorem rep_tabA : CFSG.Monster.B.Co2.Rep 820 tabA (psi xElt) := fun i => by
  rw [tabA_spec, xElt, psi_mk_apply, ← mulVec_eq_mv4]
  rfl

theorem rep_tabB : CFSG.Monster.B.Co2.Rep 820 tabB (psi yElt) := fun i => by
  rw [tabB_spec, yElt, psi_mk_apply, ← mulVec_eq_mv4]
  rfl

noncomputable def chainQ : RawSchreierDatum 820 :=
  RawSchreierDatum.ofArrays 820 (by norm_num) chainS 2 (by decide) chainBase (by decide) chainW

theorem chain_check :
    rawChainOK 820 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW 4 = true :=
  Certificates.certificate10012.1

theorem chain_orbits :
    (rawOrbitSizes 820 chainS (chainBase.map Fin.val).toArray).prod = 3265920 :=
  Certificates.certificate10012.2.1

private theorem eq_of_rep {n : ℕ} {t : Array ℕ} {g g' : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n t g) (h' : CFSG.Monster.B.Co2.Rep n t g') : g = g' :=
  Equiv.ext fun i => Fin.ext (by rw [← h i, ← h' i])

theorem card_chainQ :
    Nat.card chainQ.originalSubgroup = 3265920 := by
  rw [chainQ, card_originalSubgroup_of_chainOK
    (chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv) (by norm_num) chain_check,
    chain_orbits]

theorem chainQ_eq :
    chainQ.originalSubgroup = Subgroup.closure {psi xElt, psi yElt} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [chainQ, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have h0 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 0 (by decide))).1
  have h1 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 1 (by decide))).1
  have e0 : permOfArr 820 chainS[0]! = psi xElt := eq_of_rep h0 rep_tabA
  have e1 : permOfArr 820 chainS[1]! = psi yElt := eq_of_rep h1 rep_tabB
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem card_X₀ : Nat.card X₀ = 3265920 := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F9) (p := 3) (f := 1)
    (n := 4) Nat.prime_three le_rfl (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num)
    (by norm_num)
  rw [pow_one] at h
  rw [X₀, h]
  decide

theorem card_closure_psi :
    Nat.card (Subgroup.closure {psi xElt, psi yElt}) = 3265920 := by
  rw [← chainQ_eq, card_chainQ]

theorem closure_xy :
    Subgroup.closure ({xElt, yElt} : Set X₀) = ⊤ := by
  have : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  apply Subgroup.eq_top_of_le_card
  have hmap : (Subgroup.closure ({xElt, yElt} : Set X₀)).map psi =
      Subgroup.closure {psi xElt, psi yElt} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  rw [card_X₀, ← card_closure_psi, ← hmap]
  exact Nat.card_le_card_of_surjective _ (psi.subgroupMap_surjective _)

theorem psi_injective : Function.Injective psi := by
  have : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  have hle : Nat.card X₀ ≤ Nat.card psi.range := by
    rw [card_X₀, ← card_closure_psi]
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨xElt, rfl⟩
    · exact ⟨yElt, rfl⟩
  have hb := psi.rangeRestrict_surjective.bijective_of_nat_card_le hle
  exact fun g h hgh => hb.1 (Subtype.ext hgh)

noncomputable instance : MulAction X₀ (Fin 820) := MulAction.compHom _ psi

instance : FaithfulSMul X₀ (Fin 820) :=
  ⟨fun h => psi_injective (Equiv.ext h)⟩

private theorem permOfArr_eq_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 820)}
    (h : CFSG.Monster.B.Co2.Rep 820 t g) : permOfArr 820 t = g := by
  have hc : (∀ i < 820, t[i]! < 820) ∧ ∀ i < 820, ∀ j < 820, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

private theorem isInvA_invCand_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 820)}
    (h : CFSG.Monster.B.Co2.Rep 820 t g) : isInvA 820 t (invCand 820 t) = true := by
  have key : ∀ k ≤ 820, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate 820 0)).size = 820 ∧ ∀ i < k, ((List.range k).foldl
      (fun r i => r.set! t[i]! i) (Array.replicate 820 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have htk : t[k]! < 820 := h.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [h.apply (by omega : i < 820), h.apply (by omega : k < 820)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  have hc : invCand 820 t =
      (List.range 820).foldl (fun r i => r.set! t[i]! i) (Array.replicate 820 0) := by
    unfold invCand
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
      Std.Legacy.Range.size]
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
    rfl
  rw [isInvA, CFSG.Monster.B.Co2.allLt_iff, hc]
  intro i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨h.lt hi, (key 820 le_rfl).2 i hi⟩

theorem isInvA_tabA : isInvA 820 tabA (invCand 820 tabA) = true :=
  isInvA_invCand_of_rep rep_tabA

theorem isInvA_tabB : isInvA 820 tabB (invCand 820 tabB) = true :=
  isInvA_invCand_of_rep rep_tabB

theorem checkWords_perm :
    ∀ v ∈ checkWords, wordProd (img2 (permOfArr 820 tabA) (permOfArr 820 tabB)) v = 1 :=
  Certificates.certificate10012.2.2.1

theorem checkWords_eval :
    ∀ v ∈ checkWords, wordProd (img2 xElt yElt) v = 1 := by
  intro v hv
  apply psi_injective
  have himg : img2 (permOfArr 820 tabA) (permOfArr 820 tabB) = fun i => psi (img2 xElt yElt i) := by
    funext i
    simp only [img2]
    split_ifs
    · exact permOfArr_eq_of_rep rep_tabA
    · exact permOfArr_eq_of_rep rep_tabB
  rw [map_one, map_wordProd, ← himg]
  exact checkWords_perm v hv

theorem card_le :
    Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 3265920 :=
  Certificates.certificate10012.2.2.2

private theorem mem_checkWords_of_rels {v : List (Fin 2 × Bool)} (hv : v ∈ rels) :
    v.map (fun l => (l.1.val, l.2)) ∈ checkWords := by
  rw [checkWords, List.map_append, List.map_append]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hv))

theorem isPresentation_X₀ :
    IsPresentation (fun i : Fin 2 => img2 xElt yElt i.val) (wordSet rels) :=
  IsPresentation.of_wordProd_of_card closure_xy
    (fun v hv => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      exact checkWords_eval _ (mem_checkWords_of_rels hu))
    card_le (by rw [card_X₀])

theorem commWord_eval (i : Fin 2) :
    FreeGroup.lift (fun j : Fin 2 => img2 xElt yElt j.val)
      (FreeGroup.mk (commWords (coverPairs i))) = img2 xElt yElt i.val := by
  refine lift_mk_eq_of_wordProd _ (checkWords_eval _ ?_)
  rw [checkWords, List.map_append]
  refine List.mem_append_right _ ?_
  fin_cases i <;> simp

private theorem psi_yElt_apply (i : Fin 820) : (psi yElt i : ℕ) = tabB[(i : ℕ)]! :=
  (rep_tabB i).symm

theorem orderOf_yElt : orderOf yElt = 6 := by
  have h6 : yElt ^ 6 = 1 := by
    have := checkWords_eval _
      (mem_checkWords_of_rels (v := List.replicate 6 ((1 : Fin 2), true))
        (List.mem_cons_of_mem _ List.mem_cons_self))
    simpa [wordProd, img2, pow_succ, mul_assoc] using this
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h6 fun p hp hdvd => ?_
  have hp' : p = 2 ∨ p = 3 := by
    have := (Nat.le_of_dvd (by norm_num) hdvd)
    interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hdvd; decide) |
      (exfalso; norm_num at hp)
  intro h
  have hpsi : psi yElt ^ (6 / p) = 1 := by rw [← map_pow, h, map_one]
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 820) => (σ 0 : ℕ)) hpsi
  rcases hp' with rfl | rfl
  · simp only [show 6 / 2 = 3 from rfl, pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply] at h0
    rw [psi_yElt_apply, psi_yElt_apply, psi_yElt_apply] at h0
    revert h0; decide +kernel
  · simp only [show 6 / 3 = 2 from rfl, pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply] at h0
    rw [psi_yElt_apply, psi_yElt_apply] at h0
    revert h0; decide +kernel

theorem kernelT_eval : ∀ p ∈ kernelT,
    FreeGroup.lift (fun j : Fin 2 => img2 xElt yElt j.val) (FreeGroup.mk p.1) = 1 := by
  intro p hp
  rw [lift_mk_eq_wordProd]
  refine checkWords_eval _ ?_
  rw [checkWords, List.map_append, List.map_append]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (List.mem_map_of_mem hp)))

end CFSG.LieType.Multipliers.U43
