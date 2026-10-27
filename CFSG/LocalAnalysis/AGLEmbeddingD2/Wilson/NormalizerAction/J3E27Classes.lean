module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3E27
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverF0
public import Certificates.Certificate12623
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.CosetTable
  CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.Asc83Table

@[expose] noncomputable def fixN (σ : Equiv.Perm (Fin 6156)) : ℕ := Nat.card {p : Fin 6156 // σ p = p}

theorem fixN_conj (g σ : Equiv.Perm (Fin 6156)) : fixN (g * σ * g⁻¹) = fixN σ := by
  unfold fixN
  refine Nat.card_congr (Equiv.subtypeEquiv g.symm fun a => ?_)
  simp only [Equiv.Perm.mul_apply]
  constructor
  · intro h
    have := congrArg g.symm h
    simpa using this
  · intro h
    simp [h]

theorem fixN_inv (σ : Equiv.Perm (Fin 6156)) : fixN σ⁻¹ = fixN σ := by
  unfold fixN
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact eq_comm

theorem card_fin_subtype_eq_countP' (N : ℕ) (q : ℕ → Bool) :
    Nat.card {x : Fin N // q x = true} = (List.range N).countP q := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if q i = true then 1 else 0) N]
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.countP_append]
    simp [List.countP_cons]

theorem card_fixed_eq_j3fix {g : Array ℕ} {G : Equiv.Perm (Fin 6156)} (hg : Rep 6156 g G) :
    fixN G = Certificates.j3fix g := by
  rw [Certificates.j3fix, fixN, ← card_fin_subtype_eq_countP' 6156]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [beq_iff_eq, hg x]
  exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

section Main


set_option linter.unusedSectionVars false

@[expose] noncomputable def Lp (i : ℕ) : Equiv.Perm (Fin 6156) := permOfArr 6156 j3tLines[i]!

theorem rep_Lp {i : ℕ} (hi : i < 13) : Rep 6156 j3tLines[i]! (Lp i) :=
  rep_of_validA (linesOK3_line j3t_lines_check.1 hi).1

theorem Lp_pow3 {i : ℕ} (hi : i < 13) : Lp i ^ 3 = 1 :=
  (linesOK3_line j3t_lines_check.1 hi).2

@[expose] noncomputable def Eel (m : ℕ) : Equiv.Perm (Fin 6156) :=
  Lp 2 ^ (m / 9) * Lp 4 ^ (m / 3 % 3) * Lp 0 ^ (m % 3)

theorem rep_Eel (m : ℕ) : Rep 6156 (Certificates.j3e27Elt m) (Eel m) :=
  rep_compA (rep_compA (rep_powArr (rep_Lp (by norm_num)) _) (rep_powArr (rep_Lp (by norm_num)) _))
    (rep_powArr (rep_Lp (by norm_num)) _)

theorem Lp_comm_24 : Lp 2 * Lp 4 = Lp 4 * Lp 2 :=
  (eqA_iff (rep_compA (rep_Lp (by norm_num)) (rep_Lp (by norm_num)))
    (rep_compA (rep_Lp (by norm_num)) (rep_Lp (by norm_num)))).1
    Certificates.certificate12623.1

theorem Lp_comm_20 : Lp 2 * Lp 0 = Lp 0 * Lp 2 :=
  (eqA_iff (rep_compA (rep_Lp (by norm_num)) (rep_Lp (by norm_num)))
    (rep_compA (rep_Lp (by norm_num)) (rep_Lp (by norm_num)))).1
    Certificates.certificate12623.2.1

theorem Lp_comm_40 : Lp 4 * Lp 0 = Lp 0 * Lp 4 :=
  (eqA_iff (rep_compA (rep_Lp (by norm_num)) (rep_Lp (by norm_num)))
    (rep_compA (rep_Lp (by norm_num)) (rep_Lp (by norm_num)))).1
    Certificates.certificate12623.2.2.1

theorem fixN_Eel {m : ℕ} (hm : m < 27) (h0 : m ≠ 0) :
    fixN (Eel m) = if m % 3 = 0 then 0 else 36 := by
  have h := Certificates.certificate12623.2.2.2.1
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rw [card_fixed_eq_j3fix (rep_Eel m)]
  exact (h m hm).resolve_left h0

theorem Eel_ne {m m' : ℕ} (hm : m < 27) (hm' : m' < m) : Eel m ≠ Eel m' := by
  have h := Certificates.certificate12623.2.2.2.2.1
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  have h1 := h m hm m' hm'
  intro heq
  have := (eqA_iff (rep_Eel m) (rep_Eel m')).2 heq
  rw [this] at h1
  exact absurd h1 (by decide)

theorem fixN_XA : fixN j3tXA = 36 := by
  have h := Certificates.certificate12623.2.2.2.2.2.1
  simp only [decide_eq_true_eq] at h
  change fixN (permOfArr 6156 j3tReps[0]!) = 36
  rw [card_fixed_eq_j3fix (rep_of_validA (j3tReps_spec (c := 0) (by norm_num)).1)]
  exact h

theorem fixN_XB : fixN j3tXB = 0 := by
  have h := Certificates.certificate12623.2.2.2.2.2.2.1
  simp only [decide_eq_true_eq] at h
  change fixN (permOfArr 6156 j3tReps[1]!) = 0
  rw [card_fixed_eq_j3fix (rep_of_validA (j3tReps_spec (c := 1) (by norm_num)).1)]
  exact h

theorem Lp_mem {i : ℕ} (hi : i = 2 ∨ i = 4 ∨ i = 0) : Lp i ∈ j3P := by
  have h := Certificates.certificate12623.2.2.2.2.2.2.2
  have hi13 : i < 13 := by omega
  rcases hi with rfl | rfl | rfl
  · exact mem_j3P_of_sift (rep_Lp hi13) h.1
  · exact mem_j3P_of_sift (rep_Lp hi13) h.2.1
  · exact mem_j3P_of_sift (rep_Lp hi13) h.2.2

theorem Eel_inj {m m' : ℕ} (hm : m < 27) (hm' : m' < 27) (h : Eel m = Eel m') : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h.symm (Eel_ne hm' hlt)
  · exact heq
  · exact absurd h (Eel_ne hm hgt)

theorem Lp_comm {a b : ℕ} (ha : a = 2 ∨ a = 4 ∨ a = 0) (hb : b = 2 ∨ b = 4 ∨ b = 0) :
    Commute (Lp a) (Lp b) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact Commute.refl _
  · exact Lp_comm_24
  · exact Lp_comm_20
  · exact Lp_comm_24.symm
  · exact Commute.refl _
  · exact Lp_comm_40
  · exact Lp_comm_20.symm
  · exact Lp_comm_40.symm
  · exact Commute.refl _

@[expose] def idx3 : Fin 3 → ℕ := ![2, 4, 0]

@[expose] def idx2 : Fin 2 → ℕ := ![2, 4]

theorem idx3_mem (i : Fin 3) : idx3 i = 2 ∨ idx3 i = 4 ∨ idx3 i = 0 := by
  fin_cases i <;> simp [idx3]

theorem idx2_mem (i : Fin 2) : idx2 i = 2 ∨ idx2 i = 4 ∨ idx2 i = 0 := by
  fin_cases i <;> simp [idx2]

@[expose] noncomputable def xe : Fin 3 → Equiv.Perm (Fin 6156) := fun i => Lp (idx3 i)

@[expose] noncomputable def xe2 : Fin 2 → Equiv.Perm (Fin 6156) := fun i => Lp (idx2 i)

theorem xe_pow (i : Fin 3) : xe i ^ 3 = 1 :=
  Lp_pow3 (by rcases idx3_mem i with h | h | h <;> omega)

theorem xe_comm (i j : Fin 3) : Commute (xe i) (xe j) := Lp_comm (idx3_mem i) (idx3_mem j)

theorem xe2_pow (i : Fin 2) : xe2 i ^ 3 = 1 :=
  Lp_pow3 (by rcases idx2_mem i with h | h | h <;> omega)

theorem xe2_comm (i j : Fin 2) : Commute (xe2 i) (xe2 j) := Lp_comm (idx2_mem i) (idx2_mem j)

theorem basisProd_xe (a : Fin 3 → ZMod 3) :
    basisProd xe a = Eel (9 * (a 0).val + 3 * (a 1).val + (a 2).val) := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have e1 : (9 * (a 0).val + 3 * (a 1).val + (a 2).val) / 9 = (a 0).val := by omega
  have e2 : (9 * (a 0).val + 3 * (a 1).val + (a 2).val) / 3 % 3 = (a 1).val := by omega
  have e3 : (9 * (a 0).val + 3 * (a 1).val + (a 2).val) % 3 = (a 2).val := by omega
  rw [Eel, e1, e2, e3]
  simp [basisProd, List.ofFn_succ, xe, idx3, mul_assoc]

theorem basisProd_xe2 (a : Fin 2 → ZMod 3) :
    basisProd xe2 a = Eel (9 * (a 0).val + 3 * (a 1).val) := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have e1 : (9 * (a 0).val + 3 * (a 1).val) / 9 = (a 0).val := by omega
  have e2 : (9 * (a 0).val + 3 * (a 1).val) / 3 % 3 = (a 1).val := by omega
  have e3 : (9 * (a 0).val + 3 * (a 1).val) % 3 = 0 := by omega
  rw [Eel, e1, e2, e3]
  simp [basisProd, List.ofFn_succ, xe2, idx2]

theorem xe_inj : Function.Injective (basisProd xe) := by
  intro a b h
  rw [basisProd_xe, basisProd_xe] at h
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have g0 := ZMod.val_lt (b 0)
  have g1 := ZMod.val_lt (b 1)
  have g2 := ZMod.val_lt (b 2)
  have := Eel_inj (by omega) (by omega) h
  funext i
  fin_cases i
  · exact ZMod.val_injective 3 (by simp only [Fin.zero_eta]; omega)
  · exact ZMod.val_injective 3 (by simp only [Fin.mk_one]; omega)
  · exact ZMod.val_injective 3 (by simp only [Fin.reduceFinMk]; omega)

theorem xe2_inj : Function.Injective (basisProd xe2) := by
  intro a b h
  rw [basisProd_xe2, basisProd_xe2] at h
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have g0 := ZMod.val_lt (b 0)
  have g1 := ZMod.val_lt (b 1)
  have := Eel_inj (by omega) (by omega) h
  funext i
  fin_cases i
  · exact ZMod.val_injective 3 (by simp only [Fin.zero_eta]; omega)
  · exact ZMod.val_injective 3 (by simp only [Fin.mk_one]; omega)

theorem Eel_zero : Eel 0 = 1 := by simp [Eel]

theorem j3P_e27_split :
    ∃ B₀ B₁ : Subgroup (Equiv.Perm (Fin 6156)), B₀ ≤ j3P ∧ IsElementaryAbelian 3 B₀ ∧
      Nat.card B₀ = 27 ∧ B₁ ≤ B₀ ∧ Nat.card B₁ = 9 ∧
      (∀ y ∈ B₁, y ≠ 1 → fixN y = 0) ∧ (∀ y ∈ B₀, y ∉ B₁ → fixN y = 36) := by
  refine ⟨Subgroup.closure (Set.range xe), Subgroup.closure (Set.range xe2), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Lp_mem (idx3_mem i)
  · exact isElementaryAbelian_closure xe_pow xe_comm
  · rw [card_closure_basis xe_pow xe_comm xe_inj]; norm_num
  · apply Subgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rw [card_closure_basis xe2_pow xe2_comm xe2_inj]; norm_num
  · intro y hy hy1
    obtain ⟨a, ha⟩ := basisHom_surjective xe2_pow xe2_comm ⟨y, hy⟩
    have hya : y = basisProd xe2 (Multiplicative.toAdd a) := by
      rw [← coe_basisHom xe2_pow xe2_comm, ha]
    have h0 := ZMod.val_lt (Multiplicative.toAdd a 0)
    have h1 := ZMod.val_lt (Multiplicative.toAdd a 1)
    rw [hya, basisProd_xe2] at hy1 ⊢
    have hm : 9 * (Multiplicative.toAdd a 0).val + 3 * (Multiplicative.toAdd a 1).val ≠ 0 := by
      intro h0'
      rw [h0', Eel_zero] at hy1
      exact hy1 rfl
    rw [fixN_Eel (by omega) hm]
    simp only [if_pos (by omega : (9 * (Multiplicative.toAdd a 0).val +
      3 * (Multiplicative.toAdd a 1).val) % 3 = 0)]
  · intro y hy hyB
    obtain ⟨a, rfl⟩ := exists_basisProd xe_pow xe_comm hy
    rw [basisProd_xe] at hyB ⊢
    have h0 := ZMod.val_lt (a 0)
    have h1 := ZMod.val_lt (a 1)
    have h2 := ZMod.val_lt (a 2)
    have hm3 : (9 * (a 0).val + 3 * (a 1).val + (a 2).val) % 3 ≠ 0 := by
      intro hm3
      apply hyB
      have : Eel (9 * (a 0).val + 3 * (a 1).val + (a 2).val) =
          basisProd xe2 ![a 0, a 1] := by
        rw [basisProd_xe2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        congr 1
        omega
      rw [this]
      exact basisProd_mem_closure xe2_pow xe2_comm _
    have hm : 9 * (a 0).val + 3 * (a 1).val + (a 2).val ≠ 0 := fun h => hm3 (by rw [h])
    rw [fixN_Eel (by omega) hm, if_neg hm3]

theorem card_cent_j3P_of_fix {y : Equiv.Perm (Fin 6156)} (hy : y ∈ j3P) (hy3 : orderOf y = 3) :
    (fixN y = 36 → Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 1080) ∧
    (fixN y = 0 → Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 243) := by
  obtain ⟨k0, hk0, c, hc, e', he', hyeq⟩ := j3t_fusion hy hy3
  have hfix : ∀ c' : Equiv.Perm (Fin 6156), c' ^ 3 = 1 → fixN (c' ^ e') = fixN c' := by
    intro c' hc3
    rcases he' with rfl | rfl
    · rw [pow_one]
    · have : c' ^ 2 = c'⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hc3
      rw [this, fixN_inv]
  rcases hc with rfl | rfl
  · have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
    have hf : fixN y = 36 := by rw [hyeq, fixN_conj, hfix _ hA3, fixN_XA]
    have hcard : Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 1080 := by
      rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hA3 he',
        ← j3t_caseA.1, j3t_caseA.2]
    exact ⟨fun _ => hcard, fun h0 => by omega⟩
  · have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
    have hf : fixN y = 0 := by rw [hyeq, fixN_conj, hfix _ hB3, fixN_XB]
    have hcard : Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 243 := by
      rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hB3 he',
        ← j3t_caseB.1, j3t_caseB.2]
    exact ⟨fun h36 => by omega, fun _ => hcard⟩

theorem j3_e27_class_split {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.J3) {B : Subgroup Q}
    (hB : IsElementaryAbelian 3 B) (h27 : Nat.card B = 27) :
    ∃ B₁ : Subgroup Q, B₁ ≤ B ∧ Nat.card B₁ = 9 ∧
      (∀ x ∈ B₁, x ≠ 1 → Nat.card (centralizer ({x} : Set Q)) = 243) ∧
      (∀ x ∈ B, x ∉ B₁ → Nat.card (centralizer ({x} : Set Q)) = 1080) := by
  obtain ⟨B₀, B₁p, hB₀j, hB₀e, hB₀c, hB₁B₀, hB₁c, hf0, hf36⟩ := j3P_e27_split
  set ψ : Q ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
  set A : Subgroup ↥j3P := B.map ψ.toMonoidHom with hA
  set A' : Subgroup ↥j3P := B₀.subgroupOf j3P with hA'
  have hAe : IsElementaryAbelian 3 A := IsElementaryAbelian.map_hom ψ.toMonoidHom hB
  have hA27 : Nat.card A = 27 := by
    rw [hA, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, h27]
  have hA'e : IsElementaryAbelian 3 A' := by
    have hB₀' := isElementaryAbelian_iff.1 hB₀e
    rw [isElementaryAbelian_iff]
    refine ⟨fun a ha b hb => Subtype.ext (hB₀'.1 a.1 ha b.1 hb), fun a ha => ?_⟩
    exact Subtype.ext (hB₀'.2 a.1 ha)
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀j).toEquiv, hB₀c]
  obtain ⟨g, hg⟩ := j3_e27_conj (L := ↥j3P) Item228CensusProof.j3CarrierEquiv.symm hAe hA'e hA27
    hA'27
  set φ : Q →* ↥j3P := (MulAut.conj g).toMonoidHom.comp ψ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g).injective.comp ψ.injective
  have hφsurj : Function.Surjective φ := (MulAut.conj g).surjective.comp ψ.surjective
  set T : Subgroup ↥j3P := B₁p.subgroupOf j3P with hT
  have hTA' : T ≤ A' := fun x hx => hB₁B₀ hx
  have hφB : B.map φ = A' := by
    rw [← hg, hA, Subgroup.map_map]
  refine ⟨B ⊓ T.comap φ, inf_le_left, ?_, ?_, ?_⟩
  · have h1 : (B ⊓ T.comap φ).map φ = T := by
      rw [Subgroup.map_inf_eq _ _ φ hφinj, hφB, Subgroup.map_comap_eq_self_of_surjective hφsurj,
        inf_eq_right.2 hTA']
    rw [← Subgroup.card_map_of_injective hφinj, h1, hT,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hB₁B₀.trans hB₀j)).toEquiv, hB₁c]
  · intro x hx hx1
    have hxB := hx.1
    have hxT : φ x ∈ T := hx.2
    have hx3 : x ^ 3 = 1 := (isElementaryAbelian_iff.1 hB).2 x hxB
    have hy3 : orderOf ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) = 3 := by
      have h3 : ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) ^ 3 = 1 := by
        have := congrArg (fun z : ↥j3P => (z : Equiv.Perm (Fin 6156)))
          (show ψ x ^ 3 = 1 from (map_pow ψ x 3).symm.trans ((congrArg ψ hx3).trans (map_one _)))
        simpa using this
      have h1 : ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) ≠ 1 := by
        intro h
        apply hx1
        exact (map_eq_one_iff _ ψ.injective).1 (Subtype.ext h)
      exact orderOf_eq_prime h3 h1
    have hy1 : ((φ x : ↥j3P) : Equiv.Perm (Fin 6156)) ≠ 1 := by
      intro h
      apply hx1
      have : φ x = 1 := Subtype.ext h
      exact hφinj (this.trans (map_one φ).symm)
    have hyB : ((φ x : ↥j3P) : Equiv.Perm (Fin 6156)) ∈ B₁p := hxT
    have hf := hf0 _ hyB hy1
    have hconj : ((φ x : ↥j3P) : Equiv.Perm (Fin 6156)) =
        (g : Equiv.Perm (Fin 6156)) * ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) *
          (g : Equiv.Perm (Fin 6156))⁻¹ := rfl
    rw [hconj, fixN_conj] at hf
    rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ x]
    exact (card_cent_j3P_of_fix (ψ x).2 hy3).2 hf
  · intro x hxB hxn
    have hxT : φ x ∉ T := fun h => hxn ⟨hxB, h⟩
    have hx3 : x ^ 3 = 1 := (isElementaryAbelian_iff.1 hB).2 x hxB
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxn ⟨hxB, Subgroup.one_mem _⟩
    have hy3 : orderOf ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) = 3 := by
      have h3 : ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) ^ 3 = 1 := by
        have := congrArg (fun z : ↥j3P => (z : Equiv.Perm (Fin 6156)))
          (show ψ x ^ 3 = 1 from (map_pow ψ x 3).symm.trans ((congrArg ψ hx3).trans (map_one _)))
        simpa using this
      have h1 : ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) ≠ 1 := by
        intro h
        apply hx1
        exact (map_eq_one_iff _ ψ.injective).1 (Subtype.ext h)
      exact orderOf_eq_prime h3 h1
    have hyA' : φ x ∈ A' := hφB ▸ Subgroup.mem_map_of_mem φ hxB
    have hyB₀ : ((φ x : ↥j3P) : Equiv.Perm (Fin 6156)) ∈ B₀ := hyA'
    have hyB₁ : ((φ x : ↥j3P) : Equiv.Perm (Fin 6156)) ∉ B₁p := hxT
    have hf := hf36 _ hyB₀ hyB₁
    have hconj : ((φ x : ↥j3P) : Equiv.Perm (Fin 6156)) =
        (g : Equiv.Perm (Fin 6156)) * ((ψ x : ↥j3P) : Equiv.Perm (Fin 6156)) *
          (g : Equiv.Perm (Fin 6156))⁻¹ := rfl
    rw [hconj, fixN_conj] at hf
    rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ x]
    exact (card_cent_j3P_of_fix (ψ x).2 hy3).1 hf

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
