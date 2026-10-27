module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Module
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Transport
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.SylowFromGens
import CFSG.HardMathSupport.Timmesfeld.LieRank.O7SylowPack

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank.O7

open Matrix CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.HardMathSupport.Timmesfeld.SporadicRank

theorem card_sup_le {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (H : Set G)) : Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  classical
  let f : H × K → G := fun x => (x.1 : G) * x.2
  let T : Subgroup G :=
    { carrier := Set.range f
      mul_mem' := by
        rintro _ _ ⟨⟨a, q⟩, rfl⟩ ⟨⟨a', q'⟩, rfl⟩
        have hq : (q : G) * a' * (q : G)⁻¹ ∈ H := by
          have := (Subgroup.mem_normalizer_iff.mp (hK q.2) (a' : G)).1 a'.2
          simpa using this
        refine ⟨⟨a * ⟨_, hq⟩, q * q'⟩, ?_⟩
        simp [f, mul_assoc]
      one_mem' := ⟨⟨1, 1⟩, by simp [f]⟩
      inv_mem' := by
        rintro _ ⟨⟨a, q⟩, rfl⟩
        have hq : (q : G)⁻¹ * (a : G)⁻¹ * (q : G) ∈ H := by
          have := (Subgroup.mem_normalizer_iff.mp (hK (inv_mem q.2)) ((a : G)⁻¹)).1 (inv_mem a.2)
          simpa using this
        refine ⟨⟨⟨_, hq⟩, q⁻¹⟩, ?_⟩
        simp [f, mul_assoc] }
  have hHT : H ≤ T := fun a ha => ⟨⟨⟨a, ha⟩, 1⟩, by simp [f]⟩
  have hKT : K ≤ T := fun q hq => ⟨⟨1, ⟨q, hq⟩⟩, by simp [f]⟩
  calc Nat.card ↥(H ⊔ K) ≤ Nat.card T := Subgroup.card_le_of_le (sup_le hHT hKT)
    _ ≤ Nat.card (H × K) := by
        refine Nat.card_le_card_of_surjective (fun x : H × K => (⟨f x, x, rfl⟩ : T)) ?_
        rintro ⟨_, x, rfl⟩
        exact ⟨x, rfl⟩
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

@[expose] def eQ0L : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 0, 2, 0,
   0, 0, 1, 0, 1, 0, 0,
   0, 0, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 1, 0, 0,
   0, 0, 0, 0, 0, 1, 0,
   0, 0, 0, 0, 0, 0, 1]

@[expose] def eQ1L : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0,
   0, 1, 2, 0, 0, 0, 0,
   0, 0, 1, 0, 0, 0, 0,
   0, 0, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 1, 0, 0,
   0, 0, 0, 0, 1, 1, 0,
   0, 0, 0, 0, 0, 0, 1]

@[expose] def eQ2L : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 2, 0, 1,
   0, 0, 1, 0, 0, 0, 0,
   0, 0, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 1, 0, 0,
   0, 0, 0, 0, 0, 1, 0,
   0, 0, 0, 0, 1, 0, 1]

@[expose] def eQ3L : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 0, 0, 0,
   0, 0, 1, 0, 0, 2, 1,
   0, 0, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 1, 0, 0,
   0, 0, 0, 0, 0, 1, 0,
   0, 0, 0, 0, 0, 1, 1]

theorem eQ0L_eq : toMatL 3 7 eQ0L = eQ0 := by decide +kernel
theorem eQ1L_eq : toMatL 3 7 eQ1L = eQ1 := by decide +kernel
theorem eQ2L_eq : toMatL 3 7 eQ2L = eQ2 := by decide +kernel
theorem eQ3L_eq : toMatL 3 7 eQ3L = eQ3 := by decide +kernel

@[expose] def QgensL : List (List ℕ) :=
  [eQ0L, eQ1L, eQ2L, eQ3L, mmulL 3 7 eQ0L eQ0L, mmulL 3 7 eQ1L eQ1L, mmulL 3 7 eQ2L eQ2L,
    mmulL 3 7 eQ3L eQ3L]

@[expose] def Qlst : List (List ℕ) := wordsL 3 7 [eQ0L, eQ1L, eQ2L, eQ3L]

theorem Qlst_length : Qlst.length = 81 := by decide +kernel

theorem Qlst_one : midL 3 7 ∈ Qlst := by decide +kernel

theorem Qlst_closed : ∀ A ∈ Qlst, ∀ γ ∈ QgensL, mmulL 3 7 A γ ∈ Qlst := by
  have pinQ : (O7Pack.words7 ([eQ0L, eQ1L, eQ2L, eQ3L].map (CFSG.KC.WordsS.pk3 49)) ==
      O7Pack.QP) = true := by decide +kernel
  have pinG : ([CFSG.KC.WordsS.pk3 49 eQ0L, CFSG.KC.WordsS.pk3 49 eQ1L,
      CFSG.KC.WordsS.pk3 49 eQ2L, CFSG.KC.WordsS.pk3 49 eQ3L,
      O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ0L) (CFSG.KC.WordsS.pk3 49 eQ0L),
      O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ1L) (CFSG.KC.WordsS.pk3 49 eQ1L),
      O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ2L) (CFSG.KC.WordsS.pk3 49 eQ2L),
      O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ3L) (CFSG.KC.WordsS.pk3 49 eQ3L)] ==
      O7Pack.GP) = true := by decide +kernel
  have l0 : eQ0L.length ≤ 49 := by decide +kernel
  have l1 : eQ1L.length ≤ 49 := by decide +kernel
  have l2 : eQ2L.length ≤ 49 := by decide +kernel
  have l3 : eQ3L.length ≤ 49 := by decide +kernel
  have hA : ∀ A ∈ [eQ0L, eQ1L, eQ2L, eQ3L], A.length ≤ 49 := by
    intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    exacts [l0, l1, l2, l3]
  have r0 := O7Pack.rel_pk3 l0
  have r1 := O7Pack.rel_pk3 l1
  have r2 := O7Pack.rel_pk3 l2
  have r3 := O7Pack.rel_pk3 l3
  have hG : List.Forall₂ (CFSG.KS.WordsS.Rel3 7 49) QgensL
      [CFSG.KC.WordsS.pk3 49 eQ0L, CFSG.KC.WordsS.pk3 49 eQ1L,
        CFSG.KC.WordsS.pk3 49 eQ2L, CFSG.KC.WordsS.pk3 49 eQ3L,
        O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ0L) (CFSG.KC.WordsS.pk3 49 eQ0L),
        O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ1L) (CFSG.KC.WordsS.pk3 49 eQ1L),
        O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ2L) (CFSG.KC.WordsS.pk3 49 eQ2L),
        O7Pack.mul7 (CFSG.KC.WordsS.pk3 49 eQ3L) (CFSG.KC.WordsS.pk3 49 eQ3L)] := by
    rw [QgensL]
    exact .cons r0 (.cons r1 (.cons r2 (.cons r3 (.cons (O7Pack.rel_sq r0)
      (.cons (O7Pack.rel_sq r1) (.cons (O7Pack.rel_sq r2) (.cons (O7Pack.rel_sq r3) .nil)))))))
  rw [beq_iff_eq.1 pinG] at hG
  rw [Qlst]
  exact O7Pack.closed_of_check hA hG (beq_iff_eq.1 pinQ) O7Pack.check_close

@[expose] def Qsub : Subgroup Om7 := Subgroup.closure (Set.range qE)

theorem qE_val (j : Fin 4) : (((qE j : Om7) : GL (Fin 7) K) : M7) =
    toMatL 3 7 ([eQ0L, eQ1L, eQ2L, eQ3L].get ⟨j, by simp⟩) := by
  fin_cases j
  · exact eQ0L_eq.symm
  · exact eQ1L_eq.symm
  · exact eQ2L_eq.symm
  · exact eQ3L_eq.symm

theorem qE_inv_val (j : Fin 4) : ((((qE j)⁻¹ : Om7) : GL (Fin 7) K) : M7) =
    toMatL 3 7 (mmulL 3 7 ([eQ0L, eQ1L, eQ2L, eQ3L].get ⟨j, by simp⟩)
      ([eQ0L, eQ1L, eQ2L, eQ3L].get ⟨j, by simp⟩)) := by
  rw [toMatL_mmulL, ← qE_val]
  fin_cases j <;> rfl

theorem mem_Qlst {x : Om7} (hx : x ∈ Qsub) :
    ∃ A ∈ Qlst, ((x : GL (Fin 7) K) : M7) = toMatL 3 7 A := by
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨midL 3 7, Qlst_one, by simp [toMatL_midL]⟩
  | mul_right x hx y hy ih =>
    obtain ⟨A, hA, hxA⟩ := ih
    obtain ⟨j, rfl⟩ := hy
    have hγ : [eQ0L, eQ1L, eQ2L, eQ3L].get ⟨j, by simp⟩ ∈ QgensL := by
      fin_cases j <;> simp [QgensL]
    refine ⟨_, Qlst_closed A hA _ hγ, ?_⟩
    rw [toMatL_mmulL, ← hxA, ← qE_val]
    rfl
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨A, hA, hxA⟩ := ih
    obtain ⟨j, rfl⟩ := hy
    have hγ : mmulL 3 7 ([eQ0L, eQ1L, eQ2L, eQ3L].get ⟨j, by simp⟩)
        ([eQ0L, eQ1L, eQ2L, eQ3L].get ⟨j, by simp⟩) ∈ QgensL := by
      fin_cases j <;> simp [QgensL]
    refine ⟨_, Qlst_closed A hA _ hγ, ?_⟩
    rw [toMatL_mmulL, ← hxA, ← qE_inv_val]
    rfl

theorem card_Qsub_le : Nat.card Qsub ≤ 81 := by
  classical
  let F : Finset M7 := (Qlst.map (toMatL 3 7)).toFinset
  have hF : F.card ≤ 81 := by
    refine (List.toFinset_card_le _).trans ?_
    simp [Qlst_length]
  refine le_trans ?_ hF
  have hmem : ∀ x : Qsub, (((x : Om7) : GL (Fin 7) K) : M7) ∈ F := fun x => by
    obtain ⟨A, hA, h⟩ := mem_Qlst x.2
    rw [h]
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨A, hA, rfl⟩)
  calc Nat.card Qsub ≤ Nat.card F := by
        refine Nat.card_le_card_of_injective (fun x => ⟨_, hmem x⟩) ?_
        intro x y hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext (Units.ext this))
    _ = F.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe F)

@[expose] def Psub : Subgroup Om7 := modSpec.span ⊔ Qsub

theorem span_le_Psub : modSpec.span ≤ Psub := le_sup_left

theorem Qsub_le_normalizer : Qsub ≤ Subgroup.normalizer (modSpec.span : Set Om7) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, rfl⟩
  have := modSpec.g_mem_normalizer ⟨j.1, by show (j : ℕ) < 7; have := j.2; omega⟩
  convert this using 1
  fin_cases j <;> rfl

theorem Psub_le_normalizer : Psub ≤ Subgroup.normalizer (modSpec.span : Set Om7) :=
  sup_le Subgroup.le_normalizer Qsub_le_normalizer

theorem card_Psub_le : Nat.card Psub ≤ 3 ^ 9 := by
  have h1 := card_sup_le modSpec.span Qsub Qsub_le_normalizer
  have h2 : Nat.card modSpec.span = 3 ^ 5 := modSpec.card_span Nat.prime_three
  have h3 := card_Qsub_le
  calc Nat.card Psub ≤ Nat.card modSpec.span * Nat.card Qsub := h1
    _ ≤ 3 ^ 5 * 81 := by rw [h2]; exact Nat.mul_le_mul_left _ h3
    _ = 3 ^ 9 := by norm_num

@[expose] def gensL : List (List ℕ) :=
  [[1, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
   [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
   [1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1],
   [1, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1]]

theorem gensL_eq : ∀ j : Fin 4,
    toMatL 3 5 (gensL.get ⟨j, by simp [gensL]⟩) = actMat ⟨j, by omega⟩ := by
  decide +kernel

theorem O7_hcodes : (wordsL 3 5 gensL).Pairwise fun A B => codeL 3 A ≠ codeL 3 B := by
  decide +kernel

theorem O7_hs : 3 ^ 9 ≤ (wordsL 3 5 gensL).length * 3 ^ 5 := by decide +kernel

theorem O7_hv : 3 ^ 9 ∣ Nat.card Om7 ∧ ¬ 3 ^ (9 + 1) ∣ Nat.card Om7 := by
  rw [card_Om7]; norm_num

theorem sylowCover_O7 : SylowModuleCover Om7 3 5 (wordsL 3 5 gensL) := by
  have hgen : ∀ A ∈ gensL, ∃ q ∈ Psub, ActsBy modSpec q (toMatL 3 modSpec.n A) := by
    intro A hA
    obtain ⟨j, hj⟩ := List.mem_iff_get.1 hA
    have hj4 : (j : ℕ) < 4 := by have := j.2; simpa [gensL] using this
    have hg : modSpec.g ⟨j, by show (j : ℕ) < 7; omega⟩ = qE ⟨j, hj4⟩ := by
      have : ∀ i : Fin 4, modSpec.g ⟨i, by show (i : ℕ) < 7; have := i.2; omega⟩ = qE i := by
        intro i; fin_cases i <;> rfl
      exact this ⟨j, hj4⟩
    refine ⟨modSpec.g ⟨j, by show (j : ℕ) < 7; omega⟩, ?_, ?_⟩
    · rw [hg]
      exact (le_sup_right : Qsub ≤ Psub) (Subgroup.subset_closure ⟨_, rfl⟩ : qE ⟨j, hj4⟩ ∈ Qsub)
    · have h1 := actsBy_g modSpec ⟨j, by show (j : ℕ) < 7; omega⟩
      have h2 := gensL_eq ⟨j, hj4⟩
      rw [← hj]
      have h3 : toMatL 3 modSpec.n (gensL.get j) =
          modSpec.M ⟨j, by show (j : ℕ) < 7; omega⟩ := h2
      rw [h3]
      exact h1
  exact sylowCover_of_gens Nat.prime_three modSpec noAlt_O7 noFun_O7 Psub span_le_Psub
    Psub_le_normalizer gensL hgen O7_hcodes O7_hs card_Psub_le O7_hv

end CFSG.HardMathSupport.Timmesfeld.LieRank.O7
