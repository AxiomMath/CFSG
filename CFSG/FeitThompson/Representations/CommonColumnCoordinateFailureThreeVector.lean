module

public import CFSG.FeitThompson.Representations.GramArraySameLineIntersection
public import CFSG.FeitThompson.Representations.LengthThreeVectorExtensionEnumeration
public import Mathlib.Data.Fin.VecNotation
import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

variable {ι : Type*}

section SignedPerm

variable {ε : ι → ℤ} {σ : Equiv.Perm ι} {u v : ι → ℤ}

theorem signedPermVec_add :
    signedPermVec σ ε (u + v) = signedPermVec σ ε u + signedPermVec σ ε v := by
  funext k; simp [signedPermVec_apply, mul_add]

theorem signedPermVec_smul (c : ℤ) : signedPermVec σ ε (c • u) = c • signedPermVec σ ε u := by
  funext k
  simp only [signedPermVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable [DecidableEq ι]

theorem signedPermVec_single (p : ι) (c : ℤ) :
    signedPermVec σ ε (Pi.single p c) = Pi.single (σ.symm p) (ε (σ.symm p) * c) := by
  funext k
  by_cases hk : k = σ.symm p
  · subst hk; simp [signedPermVec_apply]
  · have h : σ k ≠ p := fun h => hk (by rw [← h]; simp)
    simp [signedPermVec_apply, h, hk]

theorem signedPermVec_eq_of_eq_three_single {f g : Fin 6 → ι} {α : Fin 6 → ℤ}
    (hα : ∀ k, α k = 1 ∨ α k = -1) (hσ : ∀ k, σ (g k) = f k) (hε : ∀ k, ε (g k) = α k)
    {x y z : Fin 6}
    (hu : u = Pi.single (f x) (α x) + Pi.single (f y) (α y) + Pi.single (f z) (α z)) :
    signedPermVec σ ε u = Pi.single (g x) 1 + Pi.single (g y) 1 + Pi.single (g z) 1 := by
  have key : ∀ k : Fin 6, signedPermVec σ ε (Pi.single (f k) (α k)) = Pi.single (g k) 1 := by
    intro k
    have hsym : σ.symm (f k) = g k := by rw [← hσ k]; simp
    rw [signedPermVec_single, hsym, hε k]
    rcases hα k with h | h <;> rw [h] <;> norm_num
  rw [hu, signedPermVec_add, signedPermVec_add, key x, key y, key z]

end SignedPerm

section Support

theorem ne_zero_of_support_inter_eq_singleton {u v : ι → ℤ} {a : ι}
    (h : Function.support u ∩ Function.support v = {a}) : u a ≠ 0 ∧ v a ≠ 0 :=
  show a ∈ Function.support u ∩ Function.support v from h ▸ rfl

theorem eq_of_support_inter_eq_singleton {u v : ι → ℤ} {a : ι}
    (h : Function.support u ∩ Function.support v = {a}) {c : ι} (hu : u c ≠ 0) (hv : v c ≠ 0) :
    c = a := by
  have hc : c ∈ Function.support u ∩ Function.support v := ⟨hu, hv⟩
  rw [h] at hc
  exact hc

theorem injective_six {a b c d e f : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Injective ![a, b, c, d, e, f] := by
  rw [← List.nodup_ofFn]
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_or,
    and_true, not_false_eq_true]
  exact ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩

end Support

section Aux

variable [DecidableEq ι] [Fintype ι]

theorem exists_third_of_dotProduct_self_eq_three {u : ι → ℤ} (hu : u ⬝ᵥ u = 3) {x y : ι}
    (hx : u x ≠ 0) (hy : u y ≠ 0) (hxy : x ≠ y) :
    ∃ z, u z ≠ 0 ∧ z ≠ x ∧ z ≠ y ∧
      u = Pi.single x (u x) + Pi.single y (u y) + Pi.single z (u z) := by
  set s : Finset ι := {i | u i ≠ 0} with hs
  have hmem : ∀ i, i ∈ s ↔ u i ≠ 0 := by intro i; simp [hs]
  have hxs : x ∈ s := (hmem x).mpr hx
  have hys : y ∈ s.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, (hmem y).mpr hy⟩
  have hcard : #s = 3 := card_support_eq_three_of_dotProduct_self_eq_three hu
  have h1 : #((s.erase x).erase y) = 1 := by
    rw [Finset.card_erase_of_mem hys, Finset.card_erase_of_mem hxs, hcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h1
  have hzmem : z ∈ (s.erase x).erase y := by simp [hz]
  have hzy : z ≠ y := (Finset.mem_erase.mp hzmem).1
  have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hzmem).2).1
  have hsupp : s = {x, y, z} := by
    have h2 : s.erase x = {y, z} := by rw [← Finset.insert_erase hys, hz]
    rw [← Finset.insert_erase hxs, h2]
  refine ⟨z, (hmem z).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzmem)), hzx, hzy, ?_⟩
  have h := sum_single_eq_self (u := u) (s := ({x, y, z} : Finset ι))
    (fun i hi => by rw [← hsupp]; exact (hmem i).mpr hi)
  rw [Finset.sum_insert (by simp [hxy, Ne.symm hzx]), Finset.sum_insert (by simp [Ne.symm hzy]),
    Finset.sum_singleton] at h
  rw [add_assoc]
  exact h.symm

theorem exists_six_indices_of_dotProduct_self_eq_three {u v w : ι → ℤ}
    (hu : u ⬝ᵥ u = 3) (hv : v ⬝ᵥ v = 3) (hw : w ⬝ᵥ w = 3) {a p r : ι}
    (hsuv : Function.support u ∩ Function.support v = {a}) (huv : u a = v a)
    (hsuw : Function.support u ∩ Function.support w = {p}) (huw : u p = w p)
    (hsvw : Function.support v ∩ Function.support w = {r}) (hvw : v r = w r)
    (hza : w a = 0) :
    ∃ (f : Fin 6 → ι) (α : Fin 6 → ℤ), Function.Injective f ∧ (∀ k, α k = 1 ∨ α k = -1) ∧
      f 0 = a ∧ f 1 = p ∧ f 3 = r ∧
      u = Pi.single (f 0) (α 0) + Pi.single (f 1) (α 1) + Pi.single (f 2) (α 2) ∧
      v = Pi.single (f 0) (α 0) + Pi.single (f 3) (α 3) + Pi.single (f 4) (α 4) ∧
      w = Pi.single (f 1) (α 1) + Pi.single (f 3) (α 3) + Pi.single (f 5) (α 5) := by
  obtain ⟨hau, hav⟩ := ne_zero_of_support_inter_eq_singleton hsuv
  obtain ⟨hpu, hpw⟩ := ne_zero_of_support_inter_eq_singleton hsuw
  obtain ⟨hrv, hrw⟩ := ne_zero_of_support_inter_eq_singleton hsvw
  have hap : a ≠ p := fun h => hpw (h ▸ hza)
  have har : a ≠ r := fun h => hrw (h ▸ hza)
  have hpr : p ≠ r := fun h => hap (eq_of_support_inter_eq_singleton hsuv hpu (h ▸ hrv)).symm
  obtain ⟨q, hqu, hqa, hqp, hueq⟩ := exists_third_of_dotProduct_self_eq_three hu hau hpu hap
  obtain ⟨s, hsv, hsa, hsr, hveq⟩ := exists_third_of_dotProduct_self_eq_three hv hav hrv har
  obtain ⟨t, htw, htp, htr, hweq⟩ := exists_third_of_dotProduct_self_eq_three hw hpw hrw hpr
  have hqw : w q = 0 := by
    by_contra h; exact hqp (eq_of_support_inter_eq_singleton hsuw hqu h)
  have hsw : w s = 0 := by
    by_contra h; exact hsr (eq_of_support_inter_eq_singleton hsvw hsv h)
  have hqs : q ≠ s := fun h => hqa (eq_of_support_inter_eq_singleton hsuv hqu (h ▸ hsv))
  have hps : p ≠ s := fun h => hpw (h ▸ hsw)
  have hqr : q ≠ r := fun h => hrw (h ▸ hqw)
  have hat : a ≠ t := fun h => htw (h ▸ hza)
  have hqt : q ≠ t := fun h => htw (h ▸ hqw)
  have hst : s ≠ t := fun h => htw (h ▸ hsw)
  rw [← huv] at hveq
  rw [← huw, ← hvw] at hweq
  refine ⟨![a, p, q, r, s, t], ![u a, u p, u q, v r, v s, w t],
    injective_six hap hqa.symm har hsa.symm hat hqp.symm hpr hps htp.symm hqr hqs hqt hsr.symm
      htr.symm hst, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact eq_one_or_neg_one_of_dotProduct_self_eq_three hu hau
    · exact eq_one_or_neg_one_of_dotProduct_self_eq_three hu hpu
    · exact eq_one_or_neg_one_of_dotProduct_self_eq_three hu hqu
    · exact eq_one_or_neg_one_of_dotProduct_self_eq_three hv hrv
    · exact eq_one_or_neg_one_of_dotProduct_self_eq_three hv hsv
    · exact eq_one_or_neg_one_of_dotProduct_self_eq_three hw htw
  · simpa using hueq
  · simpa using hveq
  · simpa using hweq

end Aux

section Main

variable {μ ν : Type*} [DecidableEq μ] [DecidableEq ν] [Fintype ι]

theorem IsGramArray.exists_six_indices_of_notMem_support [DecidableEq ι] [Nontrivial ν]
    {b : μ → ν → ι → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ : μ}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (j : ν)
    {a : ι} (ha : Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a})
    (hza : b i₃ j a = 0) :
    ∃ (f : Fin 6 → ι) (α : Fin 6 → ℤ), Function.Injective f ∧ (∀ k, α k = 1 ∨ α k = -1) ∧
      f 0 = a ∧
      b i₁ j = Pi.single (f 0) (α 0) + Pi.single (f 1) (α 1) + Pi.single (f 2) (α 2) ∧
      b i₂ j = Pi.single (f 0) (α 0) + Pi.single (f 3) (α 3) + Pi.single (f 4) (α 4) ∧
      b i₃ j = Pi.single (f 1) (α 1) + Pi.single (f 3) (α 3) + Pi.single (f 5) (α 5) := by
  have : Nontrivial μ := ⟨⟨i₁, i₂, h12⟩⟩
  obtain ⟨a₁, ha₁, huv, -⟩ := hb.exists_support_inter_eq_singleton
    (i := i₁) (j := j) (k := i₂) (l := j) (by simp [h12]) (Or.inr rfl)
  rw [Set.singleton_eq_singleton_iff.mp (ha₁.symm.trans ha)] at huv
  obtain ⟨p, hp, huw, -⟩ := hb.exists_support_inter_eq_singleton
    (i := i₁) (j := j) (k := i₃) (l := j) (by simp [h13]) (Or.inr rfl)
  obtain ⟨r, hr, hvw, -⟩ := hb.exists_support_inter_eq_singleton
    (i := i₂) (j := j) (k := i₃) (l := j) (by simp [h23]) (Or.inr rfl)
  obtain ⟨f, α, hfinj, hα, hf0, -, -, hueq, hveq, hweq⟩ :=
    exists_six_indices_of_dotProduct_self_eq_three (hb.dotProduct_self i₁ j)
      (hb.dotProduct_self i₂ j) (hb.dotProduct_self i₃ j) ha huv hp huw hr hvw hza
  exact ⟨f, α, hfinj, hα, hf0, hueq, hveq, hweq⟩

theorem six_le_card_of_isGramArray_of_notMem_support [Nontrivial ν] {b : μ → ν → ι → ℤ}
    (hb : IsGramArray b) {i₁ i₂ i₃ : μ} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (j : ν)
    {a : ι} (ha : Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a})
    (hza : b i₃ j a = 0) : 6 ≤ Fintype.card ι := by
  classical
  obtain ⟨f, -, hfinj, -⟩ := hb.exists_six_indices_of_notMem_support h12 h13 h23 j ha hza
  simpa using Fintype.card_le_of_injective f hfinj

theorem six_le_of_isGramArray_fin {d m n : ℕ} (hn : 2 ≤ n) {b : Fin m → Fin n → Fin d → ℤ}
    (hb : IsGramArray b) {i₁ i₂ i₃ : Fin m} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (j : Fin n) {a : Fin d}
    (ha : Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a})
    (hza : b i₃ j a = 0) : 6 ≤ d :=
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  by simpa using six_le_card_of_isGramArray_of_notMem_support hb h12 h13 h23 j ha hza

theorem exists_signedPermVec_normalization_of_isGramArray_fin {d m n : ℕ} (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {i₁ i₂ i₃ : Fin m}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (j : Fin n) {a : Fin d}
    (ha : Function.support (b i₁ j) ∩ Function.support (b i₂ j) = {a})
    (hza : b i₃ j a = 0) :
    ∃ h6 : 6 ≤ d, ∃ (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ), (∀ k, ε k = 1 ∨ ε k = -1) ∧
      signedPermVec σ ε (b i₁ j) = Pi.single (Fin.castLE h6 0) 1 +
        Pi.single (Fin.castLE h6 1) 1 + Pi.single (Fin.castLE h6 2) 1 ∧
      signedPermVec σ ε (b i₂ j) = Pi.single (Fin.castLE h6 0) 1 +
        Pi.single (Fin.castLE h6 3) 1 + Pi.single (Fin.castLE h6 4) 1 ∧
      signedPermVec σ ε (b i₃ j) = Pi.single (Fin.castLE h6 1) 1 +
        Pi.single (Fin.castLE h6 3) 1 + Pi.single (Fin.castLE h6 5) 1 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨f, α, hfinj, hα, -, hueq, hveq, hweq⟩ :=
    hb.exists_six_indices_of_notMem_support h12 h13 h23 j ha hza
  have h6 : 6 ≤ d := by simpa using Fintype.card_le_of_injective f hfinj
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE h6) f
    (Fin.castLE_injective h6) hfinj
  set ε : Fin d → ℤ := fun l => if h : (l : ℕ) < 6 then α ⟨l, h⟩ else 1 with hεdef
  have hε : ∀ k : Fin 6, ε (Fin.castLE h6 k) = α k := by
    intro k
    have hlt : ((Fin.castLE h6 k : Fin d) : ℕ) < 6 := k.isLt
    rw [hεdef]
    simp only [dif_pos hlt]
    congr 1
  refine ⟨h6, σ, ε, ?_, signedPermVec_eq_of_eq_three_single hα hσ hε hueq,
    signedPermVec_eq_of_eq_three_single hα hσ hε hveq,
    signedPermVec_eq_of_eq_three_single hα hσ hε hweq⟩
  intro k
  rw [hεdef]
  by_cases h : (k : ℕ) < 6
  · simpa [h] using hα ⟨k, h⟩
  · simp [h]

end Main

end CFSG.FeitThompson
