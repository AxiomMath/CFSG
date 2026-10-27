module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Certificates.Certificate27100
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.TMemRu

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

theorem wordA_size (n : ℕ) (S Sinv : Array (Array ℕ)) :
    ∀ w : List ℤ, (wordA n S Sinv w).size = n
  | [] => by simp [wordA, idA]
  | _ :: _ => by simp [wordA, compA]

theorem tabRep_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g)
    (hs : t.size = n) : TabRep t g := ⟨hs, h⟩

theorem rep_getD_two {n : ℕ} {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin n)} (h₀ : Rep n t₀ g₀)
    (h₁ : Rep n t₁ g₁) : ∀ h < 2, Rep n #[t₀, t₁][h]! ([g₀, g₁].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem rep_getD_two_inv {n : ℕ} {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin n)}
    (h₀ : Rep n t₀ g₀⁻¹) (h₁ : Rep n t₁ g₁⁻¹) :
    ∀ h < 2, Rep n #[t₀, t₁][h]! ([g₀, g₁].getD h 1)⁻¹ := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem rep_getD_four {n : ℕ} {t₀ t₁ t₂ t₃ : Array ℕ} {g₀ g₁ g₂ g₃ : Equiv.Perm (Fin n)}
    (h₀ : Rep n t₀ g₀) (h₁ : Rep n t₁ g₁) (h₂ : Rep n t₂ g₂) (h₃ : Rep n t₃ g₃) :
    ∀ h < 4, Rep n #[t₀, t₁, t₂, t₃][h]! ([g₀, g₁, g₂, g₃].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂
  · simpa using h₃

theorem rep_getD_four_inv {n : ℕ} {t₀ t₁ t₂ t₃ : Array ℕ}
    {g₀ g₁ g₂ g₃ : Equiv.Perm (Fin n)} (h₀ : Rep n t₀ g₀⁻¹) (h₁ : Rep n t₁ g₁⁻¹)
    (h₂ : Rep n t₂ g₂⁻¹) (h₃ : Rep n t₃ g₃⁻¹) :
    ∀ h < 4, Rep n #[t₀, t₁, t₂, t₃][h]! ([g₀, g₁, g₂, g₃].getD h 1)⁻¹ := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂
  · simpa using h₃

theorem ruP_le {H : Subgroup (Equiv.Perm (Fin 4060))} (h0 : ruA0 ∈ H) (h1 : ruA1 ∈ H) :
    ruP ≤ H := by
  rw [ruP, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact h0
  · exact h1

theorem tmRuCheck_parts :
    tmBasicCheck = true ∧ tmABCheck = true ∧ tmZLCheck = true ∧ tmGenCheck = true ∧
      tmSylowCheck = true := by
  have h := Certificates.certificate27100
  simp only [tmRuCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hb, hab⟩, hzl⟩, hg⟩, hs⟩ := h
  exact ⟨hb, hab, hzl, hg, hs⟩


theorem tm_basic :
    isInvA 4060 ruA0A (ruInv ruA0A) = true ∧ isInvA 4060 ruA1A (ruInv ruA1A) = true ∧
    lettersOK 2 tmWordA = true ∧ lettersOK 2 tmWordB = true ∧ lettersOK 2 tmWordL = true ∧
    lettersOK 2 tmWordZ = true ∧ lettersOK 4 tmWordG0 = true ∧ lettersOK 4 tmWordG1 = true ∧
    (∀ i < 4, lettersOK 2 (tmWordsS.getD i []) = true) ∧
    (∀ j < 7, lettersOK 2 (tmWordsC.getD j []) = true) ∧
    eqA 4060 (compA 4060 ruA0A ruA0A) (idA 4060) = true ∧ eqA 4060 ruA0A (idA 4060) = false ∧
    ∀ i < 4060, ruA0A[i]! ≠ i := by
  obtain ⟨hb, -⟩ := tmRuCheck_parts
  simp only [tmBasicCheck, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hb
  obtain ⟨h0, h1, hlA, hlB, hlL, hlZ, hlG0, hlG1, hlS, hlC, hsq, hne, hfpf⟩ := hb
  refine ⟨h0, h1, hlA, hlB, hlL, hlZ, hlG0, hlG1, ?_, ?_, hsq, hne, ?_⟩
  · intro i hi
    exact List.all_eq_true.1 hlS i (List.mem_range.2 hi)
  · intro j hj
    exact List.all_eq_true.1 hlC j (List.mem_range.2 hj)
  · intro i hi
    have := allLt_spec hfpf hi
    simpa using this

theorem tm_ab :
    isInvA 4060 tmTA (ruInv tmTA) = true ∧ isInvA 4060 tmTB (ruInv tmTB) = true ∧
    eqA 4060 (compA 4060 tmTA ruA0A) (compA 4060 ruA0A tmTA) = true ∧
    eqA 4060 (compA 4060 tmTB ruA0A) (compA 4060 ruA0A tmTB) = true ∧
    eqA 4060 (powA 4060 tmTA 5) (idA 4060) = true ∧ eqA 4060 tmTA (idA 4060) = false ∧
    eqA 4060 (powA 4060 tmTB 7) (idA 4060) = true ∧ eqA 4060 tmTB (idA 4060) = false ∧
    eqA 4060 (powA 4060 (compA 4060 tmTA tmTB) 13) (idA 4060) = true ∧
    eqA 4060 (compA 4060 tmTA tmTB) (idA 4060) = false := by
  obtain ⟨-, hab, -⟩ := tmRuCheck_parts
  simpa only [tmABCheck, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using hab

theorem tm_zl :
    eqA 4060 (compA 4060 tmTZ tmTZ) (idA 4060) = true ∧ eqA 4060 tmTZ (idA 4060) = false ∧
    tmZFix < 4060 ∧ tmTZ[tmZFix]! = tmZFix ∧
    isInvA 4060 tmTL (ruInv tmTL) = true ∧ isInvA 4060 tmTAl (ruInv tmTAl) = true ∧
    isInvA 4060 tmTBl (ruInv tmTBl) = true ∧
    eqA 4060 (compA 4060 (compA 4060 tmTL ruA0A) (ruInv tmTL)) (compA 4060 ruA0A tmTZ) = true := by
  obtain ⟨-, -, hzl, -⟩ := tmRuCheck_parts
  simpa only [tmZLCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq,
    and_assoc] using hzl

theorem tm_gen :
    eqA 4060 (wordA 4060 tmGen4 tmGen4i tmWordG0) ruA0A = true ∧
    eqA 4060 (wordA 4060 tmGen4 tmGen4i tmWordG1) ruA1A = true := by
  obtain ⟨-, -, -, hg, -⟩ := tmRuCheck_parts
  simpa only [tmGenCheck, Bool.and_eq_true] using hg

theorem tm_sylow :
    (∀ i < 4, isInvA 4060 (tmSGen i) (ruInv (tmSGen i)) = true) ∧
    (∀ j < 7, isInvA 4060 (tmCGen j) (ruInv (tmCGen j)) = true) ∧
    (∀ g ∈ tmSTabs, comp 4060 g tmTZ = comp 4060 tmTZ g) ∧
    enumOK 4060 tmSTabs tmSEnum = true ∧ tmSEnum.tabs.size = 64 ∧
    tmCentralCover tmSEnum = true := by
  obtain ⟨-, -, -, -, hs⟩ := tmRuCheck_parts
  simp only [tmSylowCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at hs
  obtain ⟨hI, hIc, hcomm, henum, hsz, hcover⟩ := hs
  refine ⟨fun i hi => List.all_eq_true.1 hI i (List.mem_range.2 hi),
    fun j hj => List.all_eq_true.1 hIc j (List.mem_range.2 hj), fun g hg => ?_, henum, hsz,
    hcover⟩
  have := (Array.all_eq_true'.1 hcomm) g hg
  simpa using this

def tmA : Equiv.Perm (Fin 4060) := evalSigned [ruA0, ruA1] tmWordA

def tmB : Equiv.Perm (Fin 4060) := evalSigned [ruA0, ruA1] tmWordB

def tmZ : Equiv.Perm (Fin 4060) := evalSigned [tmA, tmB] tmWordZ

def tmL : Equiv.Perm (Fin 4060) := evalSigned [ruA0, ruA1] tmWordL

theorem tmA0_mem : ruA0 ∈ ruP := Subgroup.subset_closure (Set.mem_insert _ _)

theorem tmA1_mem : ruA1 ∈ ruP := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mem_gens_ru : ∀ g ∈ [ruA0, ruA1], g ∈ ruP := by
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact tmA0_mem
  · exact tmA1_mem

theorem tmA_mem : tmA ∈ ruP := evalSigned_mem mem_gens_ru _

theorem tmB_mem : tmB ∈ ruP := evalSigned_mem mem_gens_ru _

theorem tmL_mem : tmL ∈ ruP := evalSigned_mem mem_gens_ru _

theorem mem_gens_AB : ∀ g ∈ [tmA, tmB], g ∈ Subgroup.closure {tmA, tmB} := by
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mem_gens_four : ∀ g ∈ [tmA, tmB, tmL * tmA * tmL⁻¹, tmL * tmB * tmL⁻¹],
    g ∈ Subgroup.closure {tmA, tmB, tmL * tmA * tmL⁻¹, tmL * tmB * tmL⁻¹} := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem tmZ_mem : tmZ ∈ Subgroup.closure {tmA, tmB} := evalSigned_mem mem_gens_AB _

section Reps


theorem rep_tmGenA0 : Rep 4060 ruA0A ruA0 := (rep_permOfArr tm_basic.1).1

theorem rep_tmGenA0i : Rep 4060 (ruInv ruA0A) ruA0⁻¹ := rep_inv_of_isInvA rep_tmGenA0 tm_basic.1

theorem rep_tmGenA1 : Rep 4060 ruA1A ruA1 := (rep_permOfArr tm_basic.2.1).1

theorem rep_tmGenA1i : Rep 4060 (ruInv ruA1A) ruA1⁻¹ := rep_inv_of_isInvA rep_tmGenA1 tm_basic.2.1

theorem rep_gen2 : ∀ h < 2, Rep 4060 tmGen2[h]! ([ruA0, ruA1].getD h 1) :=
  rep_getD_two rep_tmGenA0 rep_tmGenA1

theorem rep_gen2i : ∀ h < 2, Rep 4060 tmGen2i[h]! ([ruA0, ruA1].getD h 1)⁻¹ :=
  rep_getD_two_inv rep_tmGenA0i rep_tmGenA1i

theorem rep_tmTA : Rep 4060 tmTA tmA := by
  unfold tmTA tmA
  exact rep_wordA_evalSigned rep_gen2 rep_gen2i tmWordA tm_basic.2.2.1

theorem rep_tmTAi : Rep 4060 (ruInv tmTA) tmA⁻¹ := rep_inv_of_isInvA rep_tmTA tm_ab.1

theorem rep_tmTB : Rep 4060 tmTB tmB := by
  unfold tmTB tmB
  exact rep_wordA_evalSigned rep_gen2 rep_gen2i tmWordB tm_basic.2.2.2.1

theorem rep_tmTBi : Rep 4060 (ruInv tmTB) tmB⁻¹ := rep_inv_of_isInvA rep_tmTB tm_ab.2.1

theorem rep_genAB : ∀ h < 2, Rep 4060 tmGenAB[h]! ([tmA, tmB].getD h 1) :=
  rep_getD_two rep_tmTA rep_tmTB

theorem rep_genABi : ∀ h < 2, Rep 4060 tmGenABi[h]! ([tmA, tmB].getD h 1)⁻¹ :=
  rep_getD_two_inv rep_tmTAi rep_tmTBi

theorem rep_tmTZ : Rep 4060 tmTZ tmZ := by
  unfold tmTZ tmZ
  exact rep_wordA_evalSigned rep_genAB rep_genABi tmWordZ tm_basic.2.2.2.2.2.1

theorem rep_tmTL : Rep 4060 tmTL tmL := by
  unfold tmTL tmL
  exact rep_wordA_evalSigned rep_gen2 rep_gen2i tmWordL tm_basic.2.2.2.2.1

theorem rep_tmTLi : Rep 4060 (ruInv tmTL) tmL⁻¹ := rep_inv_of_isInvA rep_tmTL tm_zl.2.2.2.2.1

theorem rep_tmTAl : Rep 4060 tmTAl (tmL * tmA * tmL⁻¹) := by
  unfold tmTAl
  exact rep_compA (rep_compA rep_tmTL rep_tmTA) rep_tmTLi

theorem rep_tmTAli : Rep 4060 (ruInv tmTAl) (tmL * tmA * tmL⁻¹)⁻¹ :=
  rep_inv_of_isInvA rep_tmTAl tm_zl.2.2.2.2.2.1

theorem rep_tmTBl : Rep 4060 tmTBl (tmL * tmB * tmL⁻¹) := by
  unfold tmTBl
  exact rep_compA (rep_compA rep_tmTL rep_tmTB) rep_tmTLi

theorem rep_tmTBli : Rep 4060 (ruInv tmTBl) (tmL * tmB * tmL⁻¹)⁻¹ :=
  rep_inv_of_isInvA rep_tmTBl tm_zl.2.2.2.2.2.2.1

theorem rep_gen4 : ∀ h < 4, Rep 4060 tmGen4[h]!
    ([tmA, tmB, tmL * tmA * tmL⁻¹, tmL * tmB * tmL⁻¹].getD h 1) :=
  rep_getD_four rep_tmTA rep_tmTB rep_tmTAl rep_tmTBl

theorem rep_gen4i : ∀ h < 4, Rep 4060 tmGen4i[h]!
    ([tmA, tmB, tmL * tmA * tmL⁻¹, tmL * tmB * tmL⁻¹].getD h 1)⁻¹ :=
  rep_getD_four_inv rep_tmTAi rep_tmTBi rep_tmTAli rep_tmTBli

end Reps


section Facts


theorem tmA_comm : tmA * ruA0 = ruA0 * tmA :=
  eq_of_eqA (rep_compA rep_tmTA rep_tmGenA0) (rep_compA rep_tmGenA0 rep_tmTA) tm_ab.2.2.1

theorem tmB_comm : tmB * ruA0 = ruA0 * tmB :=
  eq_of_eqA (rep_compA rep_tmTB rep_tmGenA0) (rep_compA rep_tmGenA0 rep_tmTB) tm_ab.2.2.2.1

theorem orderOf_tmA : orderOf tmA = 5 := by
  obtain ⟨-, -, -, -, hA5, hAne, -⟩ := tm_ab
  have h5 : tmA ^ 5 = 1 := eq_of_eqA (rep_powA rep_tmTA 5) rep_idA hA5
  have hne : tmA ≠ 1 := fun h => by
    have := (eqA_iff rep_tmTA rep_idA).2 h
    rw [hAne] at this
    exact Bool.false_ne_true this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h5 hne

theorem orderOf_tmB : orderOf tmB = 7 := by
  obtain ⟨-, -, -, -, -, -, hB7, hBne, -⟩ := tm_ab
  have h7 : tmB ^ 7 = 1 := eq_of_eqA (rep_powA rep_tmTB 7) rep_idA hB7
  have hne : tmB ≠ 1 := fun h => by
    have := (eqA_iff rep_tmTB rep_idA).2 h
    rw [hBne] at this
    exact Bool.false_ne_true this
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime h7 hne

theorem orderOf_tmAB : orderOf (tmA * tmB) = 13 := by
  obtain ⟨-, -, -, -, -, -, -, -, hAB13, hABne⟩ := tm_ab
  have hAB := rep_compA rep_tmTA rep_tmTB
  have h13 : (tmA * tmB) ^ 13 = 1 := eq_of_eqA (rep_powA hAB 13) rep_idA hAB13
  have hne : tmA * tmB ≠ 1 := fun h => by
    have := (eqA_iff hAB rep_idA).2 h
    rw [hABne] at this
    exact Bool.false_ne_true this
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_eq_prime h13 hne

theorem orderOf_tmA0 : orderOf ruA0 = 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsq, hne, -⟩ := tm_basic
  have h2 : ruA0 ^ 2 = 1 := by
    rw [pow_two]
    exact eq_of_eqA (rep_compA rep_tmGenA0 rep_tmGenA0) rep_idA hsq
  have hne' : ruA0 ≠ 1 := fun h => by
    have := (eqA_iff rep_tmGenA0 rep_idA).2 h
    rw [hne] at this
    exact Bool.false_ne_true this
  exact orderOf_eq_prime h2 hne'

theorem ruA0_fixedPointFree : ∀ p : Fin 4060, ruA0 p ≠ p := by
  intro p hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfpf⟩ := tm_basic
  have h1 := hfpf p.1 p.2
  have h2 := rep_tmGenA0 p
  rw [hp] at h2
  exact h1 h2

theorem tmZ_sq : tmZ * tmZ = 1 :=
  eq_of_eqA (rep_compA rep_tmTZ rep_tmTZ) rep_idA tm_zl.1

theorem tmZ_ne : tmZ ≠ 1 := fun h => by
  have := (eqA_iff rep_tmTZ rep_idA).2 h
  rw [tm_zl.2.1] at this
  exact Bool.false_ne_true this

theorem tmZ_fixed : ∃ p : Fin 4060, tmZ p = p := by
  obtain ⟨-, -, hlt, hfix, -⟩ := tm_zl
  refine ⟨⟨tmZFix, hlt⟩, Fin.ext ?_⟩
  have := rep_tmTZ ⟨tmZFix, hlt⟩
  rw [hfix] at this
  exact this.symm

theorem tmL_conj : tmL * ruA0 * tmL⁻¹ = ruA0 * tmZ :=
  eq_of_eqA (rep_compA (rep_compA rep_tmTL rep_tmGenA0) rep_tmTLi)
    (rep_compA rep_tmGenA0 rep_tmTZ) tm_zl.2.2.2.2.2.2.2

theorem ruP_le_closure_four :
    ruP ≤ Subgroup.closure {tmA, tmB, tmL * tmA * tmL⁻¹, tmL * tmB * tmL⁻¹} := by
  obtain ⟨-, -, -, -, -, -, hlG0, hlG1, -⟩ := tm_basic
  obtain ⟨hg0, hg1⟩ := tm_gen
  have e0 := eq_of_eqA (rep_wordA_evalSigned rep_gen4 rep_gen4i tmWordG0 hlG0) rep_tmGenA0 hg0
  have e1 := eq_of_eqA (rep_wordA_evalSigned rep_gen4 rep_gen4i tmWordG1 hlG1) rep_tmGenA1 hg1
  refine ruP_le ?_ ?_
  · rw [← e0]
    exact evalSigned_mem mem_gens_four _
  · rw [← e1]
    exact evalSigned_mem mem_gens_four _

end Facts


def tmSg (i : ℕ) : Equiv.Perm (Fin 4060) := evalSigned [tmA, tmB] (tmWordsS.getD i [])

def tmCg (j : ℕ) : Equiv.Perm (Fin 4060) := evalSigned [tmA, tmB] (tmWordsC.getD j [])

section Sylow


theorem rep_tmSGen {i : ℕ} (hi : i < 4) : Rep 4060 (tmSGen i) (tmSg i) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlS, -⟩ := tm_basic
  unfold tmSGen tmSg
  exact rep_wordA_evalSigned rep_genAB rep_genABi _ (hlS i hi)

theorem rep_tmCGen {j : ℕ} (hj : j < 7) : Rep 4060 (tmCGen j) (tmCg j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hlC, -⟩ := tm_basic
  unfold tmCGen tmCg
  exact rep_wordA_evalSigned rep_genAB rep_genABi _ (hlC j hj)

theorem tmRu_S : ∃ S : Subgroup (Equiv.Perm (Fin 4060)), S ≤ Subgroup.closure {tmA, tmB} ∧
    Nat.card S = 64 ∧ (∀ x ∈ S, x * tmZ = tmZ * x) ∧
    ∀ x ∈ S, x * x = 1 → x ≠ 1 → (∀ s ∈ S, x * s = s * x) →
      ∃ c ∈ Subgroup.closure {tmA, tmB}, c * tmZ * c⁻¹ = x := by
  obtain ⟨-, hIC, hcomm, henum, hsz, hcover⟩ := tm_sylow
  have hZT : TabRep tmTZ tmZ :=
    tabRep_of_rep rep_tmTZ (by unfold tmTZ; exact wordA_size _ _ _ _)
  have hsgRep : ∀ i : Fin 4, TabRep (tmSGen i) (tmSg i) := fun i =>
    tabRep_of_rep (rep_tmSGen i.2) (by unfold tmSGen; exact wordA_size _ _ _ _)
  have hSget : ∀ i : Fin 4, tmSTabs[(i : ℕ)]! = tmSGen i := by
    intro i
    fin_cases i <;> simp [tmSTabs]
  have hE : Enumerates (Subgroup.closure (Set.range fun i : Fin 4 => tmSg i))
      tmSEnum.tabs.toList := by
    refine enumerates_closure (gens := tmSTabs) ?_ ?_ henum
    · rintro a ⟨i, rfl⟩
      refine ⟨i, by simp [tmSTabs], ?_⟩
      rw [hSget i]
      exact hsgRep i
    · intro j hj
      have hj4 : j < 4 := by simpa [tmSTabs] using hj
      refine ⟨tmSg j, ⟨⟨j, hj4⟩, rfl⟩, ?_⟩
      rw [show tmSTabs[j]! = tmSTabs[((⟨j, hj4⟩ : Fin 4) : ℕ)]! from rfl, hSget]
      exact hsgRep ⟨j, hj4⟩
  have hSD : Subgroup.closure (Set.range fun i : Fin 4 => tmSg i) ≤
      Subgroup.closure {tmA, tmB} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact evalSigned_mem mem_gens_AB _
  have hcard : Nat.card (Subgroup.closure (Set.range fun i : Fin 4 => tmSg i)) = 64 := by
    rw [hE.card, Array.length_toList]
    exact hsz
  have hSζ : ∀ x ∈ Subgroup.closure (Set.range fun i : Fin 4 => tmSg i),
      x * tmZ = tmZ * x := by
    have hle : Subgroup.closure (Set.range fun i : Fin 4 => tmSg i) ≤
        Subgroup.centralizer ({tmZ} : Set (Equiv.Perm (Fin 4060))) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hc := hcomm (tmSGen i) (by rw [← hSget i]; simp [tmSTabs])
      have hb : (comp 4060 (tmSGen i) tmTZ == comp 4060 tmTZ (tmSGen i)) = true := beq_iff_eq.2 hc
      exact (((hsgRep i).comp hZT).beq_iff (hZT.comp (hsgRep i))).1 hb
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hzj : ∀ j < 7, TabRep (tmZj j) (tmCg j * tmZ * (tmCg j)⁻¹) := by
    intro j hj
    unfold tmZj conjTab
    exact tabRep_of_rep (rep_compA (rep_compA (rep_tmCGen hj) rep_tmTZ)
      (rep_inv_of_isInvA (rep_tmCGen hj) (hIC j hj))) Array.size_ofFn
  refine ⟨_, hSD, hcard, hSζ, ?_⟩
  intro x hx hx2 hx1 hxc
  obtain ⟨t, ht, htrep⟩ := hE.complete x hx
  unfold tmCentralCover at hcover
  have hcov := (Array.all_eq_true'.1 hcover) t (Array.mem_toList_iff.1 ht)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcov
  have hA : ¬ (t == idTab 4060) = true := fun h => hx1 ((htrep.beq_iff TabRep.idTab).1 h)
  have hB : ¬ (comp 4060 t t == idTab 4060) = false := by
    have : (comp 4060 t t == idTab 4060) = true :=
      ((htrep.comp htrep).beq_iff TabRep.idTab).2 (by rw [hx2])
    rw [this]
    exact Bool.noConfusion
  have hC : ¬ (tmSTabs.all fun g => comp 4060 t g == comp 4060 g t) = false := by
    have : (tmSTabs.all fun g => comp 4060 t g == comp 4060 g t) = true := by
      refine Array.all_eq_true'.2 fun g hg => ?_
      simp only [tmSTabs, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hg
      have key : ∀ i : Fin 4, g = tmSGen i → (comp 4060 t g == comp 4060 g t) = true := by
        intro i hgi
        rw [hgi]
        have hsi : tmSg i ∈ Subgroup.closure (Set.range fun i : Fin 4 => tmSg i) :=
          Subgroup.subset_closure ⟨i, rfl⟩
        have := hxc (tmSg i) hsi
        exact ((htrep.comp (hsgRep i)).beq_iff ((hsgRep i).comp htrep)).2 this
      rcases hg with h | h | h | h
      · exact key 0 h
      · exact key 1 h
      · exact key 2 h
      · exact key 3 h
    rw [this]
    exact Bool.noConfusion
  rcases hcov with ((hA' | hB') | hC') | hD
  · exact absurd hA' hA
  · exact absurd hB' hB
  · exact absurd hC' hC
  · obtain ⟨j, hj, hjt⟩ := List.any_eq_true.1 hD
    have hj7 : j < 7 := List.mem_range.1 hj
    refine ⟨tmCg j, evalSigned_mem mem_gens_AB _, ?_⟩
    exact ((htrep.beq_iff (hzj j hj7)).1 hjt).symm

end Sylow


theorem tmRu_facts :
    ∃ (A B z l : Equiv.Perm (Fin 4060)) (S : Subgroup (Equiv.Perm (Fin 4060))),
      A ∈ ruP ∧ B ∈ ruP ∧ A * ruA0 = ruA0 * A ∧ B * ruA0 = ruA0 * B ∧
      orderOf A = 5 ∧ orderOf B = 7 ∧ orderOf (A * B) = 13 ∧
      orderOf ruA0 = 2 ∧ (∀ p, ruA0 p ≠ p) ∧
      z ∈ Subgroup.closure {A, B} ∧ z * z = 1 ∧ z ≠ 1 ∧ (∃ p, z p = p) ∧
      l ∈ ruP ∧ l * ruA0 * l⁻¹ = ruA0 * z ∧
      ruP ≤ Subgroup.closure {A, B, l * A * l⁻¹, l * B * l⁻¹} ∧
      S ≤ Subgroup.closure {A, B} ∧ Nat.card S = 64 ∧ (∀ x ∈ S, x * z = z * x) ∧
      ∀ x ∈ S, x * x = 1 → x ≠ 1 → (∀ s ∈ S, x * s = s * x) →
        ∃ c ∈ Subgroup.closure {A, B}, c * z * c⁻¹ = x := by
  obtain ⟨S, hSD, hcard, hSz, hcov⟩ := tmRu_S
  exact ⟨tmA, tmB, tmZ, tmL, S, tmA_mem, tmB_mem, tmA_comm, tmB_comm, orderOf_tmA, orderOf_tmB,
    orderOf_tmAB, orderOf_tmA0, ruA0_fixedPointFree, tmZ_mem, tmZ_sq, tmZ_ne, tmZ_fixed,
    tmL_mem, tmL_conj, ruP_le_closure_four, hSD, hcard, hSz, hcov⟩

end CFSG.EvenSporadicStandard.Induction.TMemRu
