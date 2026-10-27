module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Pair
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterElem

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64

structure RepSys (X : Type*) [Group X] where
  Rep : Pr3 → X → Prop
  sc : List GF64
  valid : Pr3 → Bool
  rep_exists : ∀ {p}, valid p = true → ∃ y, Rep p y
  rep_one : Rep oneP3 1
  rep_mul : ∀ {p q y y'}, Rep p y → Rep q y' → Rep (mulP3 p q) (y * y')
  rep_inv : ∀ {p y}, Rep p y → Rep (invP3 p) y⁻¹
  rep_ext : ∀ {p q y y'}, Rep p y → Rep q y' → eqMod sc p q = true → y = y'
  rep_inj : ∀ {p}, Rep p 1 → eqMod sc p oneP3 = true

namespace RepSys

variable {X : Type*} [Group X] (R : RepSys X)

theorem rep_pow {p : Pr3} {y : X} (h : R.Rep p y) (n : ℕ) : R.Rep (powP3 p n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact R.rep_one
  | succ n ih =>
    rw [pow_succ']
    exact R.rep_mul h ih

theorem rep_mono {e : Array Pr3} {y : ℕ → X} (he : ∀ i < 3, R.Rep (e.getD i oneP3) (y i))
    (v : Array ℕ) :
    R.Rep (monoP3 e v) (y 0 ^ v.getD 0 0 * y 1 ^ v.getD 1 0 * y 2 ^ v.getD 2 0) :=
  R.rep_mul (R.rep_mul (R.rep_pow (he 0 (by norm_num)) _) (R.rep_pow (he 1 (by norm_num)) _))
    (R.rep_pow (he 2 (by norm_num)) _)

end RepSys

structure CheckData where
  e : Array Pr3
  g : Array Pr3
  fv : Array (Array ℕ)
  cj : Array ℕ

@[expose] def checkE (sc : List GF64) (valid : Pr3 → Bool) (d : CheckData) : Bool :=
  d.e.size == 3 && (List.range 3).all (fun i => valid (d.e.getD i oneP3)) &&
    (List.range 3).all (fun i => eqMod sc (powP3 (d.e.getD i oneP3) 3) oneP3) &&
    (List.range 3).all (fun i => (List.range 3).all (fun j =>
      eqMod sc (mulP3 (d.e.getD i oneP3) (d.e.getD j oneP3))
        (mulP3 (d.e.getD j oneP3) (d.e.getD i oneP3)))) &&
    (List.range 3).all (fun a => (List.range 3).all (fun b => (List.range 3).all (fun c =>
      (a == 0 && b == 0 && c == 0) || !eqMod sc (monoP3 d.e #[a, b, c]) oneP3)))

@[expose] def checkG (sc : List GF64) (valid : Pr3 → Bool) (d : CheckData) (k : ℕ) : Bool :=
  valid (d.g.getD k oneP3) &&
    (List.range 3).all (fun s => (List.range 3).all (fun t =>
      (s == 0 && t == 0) ||
        !eqMod sc (mulP3 (powP3 (monoP3 d.e (d.fv.getD (2 * k) #[])) s)
          (powP3 (monoP3 d.e (d.fv.getD (2 * k + 1) #[])) t)) oneP3)) &&
    eqMod sc (mulP3 (mulP3 (d.g.getD k oneP3) (monoP3 d.e (d.fv.getD (2 * k) #[])))
        (invP3 (d.g.getD k oneP3)))
      (mulP3 (powP3 (monoP3 d.e (d.fv.getD (2 * k) #[])) (d.cj.getD (4 * k) 0))
        (powP3 (monoP3 d.e (d.fv.getD (2 * k + 1) #[])) (d.cj.getD (4 * k + 1) 0))) &&
    eqMod sc (mulP3 (mulP3 (d.g.getD k oneP3) (monoP3 d.e (d.fv.getD (2 * k + 1) #[])))
        (invP3 (d.g.getD k oneP3)))
      (mulP3 (powP3 (monoP3 d.e (d.fv.getD (2 * k) #[])) (d.cj.getD (4 * k + 2) 0))
        (powP3 (monoP3 d.e (d.fv.getD (2 * k + 1) #[])) (d.cj.getD (4 * k + 3) 0)))

theorem weakCore_of_check {X : Type*} [Group X] [Finite X] (R : RepSys X) (d : CheckData)
    (hE : checkE R.sc R.valid d = true) (hG : ∀ k < 2, checkG R.sc R.valid d k = true) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      ∀ k < 2, ∀ y, R.Rep (d.g.getD k oneP3) y → y ∈ CFSG.Open.GLBWeakCore 3 E := by
  simp only [checkE, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hE
  obtain ⟨⟨⟨⟨hsz, hvalid⟩, hcube⟩, hcomm⟩, hind⟩ := hE
  have hex : ∀ i < 3, ∃ y : X, R.Rep (d.e.getD i oneP3) y := fun i hi => R.rep_exists (hvalid i hi)
  choose! y hy using hex
  have hy3 : ∀ i < 3, y i ^ 3 = 1 := fun i hi =>
    R.rep_ext (R.rep_pow (hy i hi) 3) R.rep_one (hcube i hi)
  have hyc : ∀ i < 3, ∀ j < 3, y i * y j = y j * y i := fun i hi j hj =>
    R.rep_ext (R.rep_mul (hy i hi) (hy j hj)) (R.rep_mul (hy j hj) (hy i hi)) (hcomm i hi j hj)
  have hmono : ∀ v : Array ℕ, R.Rep (monoP3 d.e v)
      (y 0 ^ v.getD 0 0 * y 1 ^ v.getD 1 0 * y 2 ^ v.getD 2 0) := fun v => R.rep_mono hy v
  have hyind : ∀ a b c : ℕ, a < 3 → b < 3 → c < 3 → y 0 ^ a * y 1 ^ b * y 2 ^ c = 1 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c ha hb hc h1
    have h2 := hmono #[a, b, c]
    simp only [Array.getD_eq_getD_getElem?] at h2
    have h3 : R.Rep (monoP3 d.e #[a, b, c]) 1 := by
      have := h2
      simp only [show (#[a, b, c] : Array ℕ)[0]? = some a from rfl,
        show (#[a, b, c] : Array ℕ)[1]? = some b from rfl,
        show (#[a, b, c] : Array ℕ)[2]? = some c from rfl, Option.getD_some] at this
      rwa [h1] at this
    have h4 := R.rep_inj h3
    have h5 := hind a ha b hb c hc
    rcases h5 with ⟨⟨h0a, h0b⟩, h0c⟩ | h5
    · exact ⟨h0a, h0b, h0c⟩
    · rw [h4] at h5
      exact absurd h5 (by simp)
  have hEc : IsMulCommutative (Subgroup.closure {y 0, y 1, y 2}) ∧
      (∀ g ∈ Subgroup.closure {y 0, y 1, y 2}, g ^ 3 = 1) ∧
      Nat.card (Subgroup.closure {y 0, y 1, y 2}) = 3 ^ 3 :=
    closure_triple (y 0) (y 1) (y 2) (hy3 0 (by norm_num)) (hy3 1 (by norm_num))
      (hy3 2 (by norm_num)) (hyc 0 (by norm_num) 1 (by norm_num))
      (hyc 0 (by norm_num) 2 (by norm_num)) (hyc 1 (by norm_num) 2 (by norm_num)) hyind
  refine ⟨Subgroup.closure {y 0, y 1, y 2}, ⟨hEc.1, hEc.2.1⟩, hEc.2.2, ?_⟩
  intro k hk z hz
  have hGk := hG k hk
  simp only [checkG, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hGk
  obtain ⟨⟨⟨-, hFind⟩, hc1⟩, hc2⟩ := hGk
  set v1 := d.fv.getD (2 * k) #[] with hv1
  set v2 := d.fv.getD (2 * k + 1) #[] with hv2
  set f1 := y 0 ^ v1.getD 0 0 * y 1 ^ v1.getD 1 0 * y 2 ^ v1.getD 2 0 with hf1
  set f2 := y 0 ^ v2.getD 0 0 * y 1 ^ v2.getD 1 0 * y 2 ^ v2.getD 2 0 with hf2
  set E := Subgroup.closure {y 0, y 1, y 2} with hEdef
  have hmem : ∀ a b c : ℕ, y 0 ^ a * y 1 ^ b * y 2 ^ c ∈ E := by
    intro a b c
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hf1E : f1 ∈ E := hmem _ _ _
  have hf2E : f2 ∈ E := hmem _ _ _
  have hf13 : f1 ^ 3 = 1 := hEc.2.1 _ hf1E
  have hf23 : f2 ^ 3 = 1 := hEc.2.1 _ hf2E
  have hf12 : Commute f1 f2 := by
    have := hEc.1.is_comm.comm ⟨f1, hf1E⟩ ⟨f2, hf2E⟩
    exact congrArg Subtype.val this
  have hrf1 : R.Rep (monoP3 d.e v1) f1 := hmono v1
  have hrf2 : R.Rep (monoP3 d.e v2) f2 := hmono v2
  have hFind' : ∀ s t : ℕ, s < 3 → t < 3 → f1 ^ s * f2 ^ t = 1 → s = 0 ∧ t = 0 := by
    intro s t hs ht h1
    have h3 : R.Rep (mulP3 (powP3 (monoP3 d.e v1) s) (powP3 (monoP3 d.e v2) t)) 1 := by
      have := R.rep_mul (R.rep_pow hrf1 s) (R.rep_pow hrf2 t)
      rwa [h1] at this
    have h4 := R.rep_inj h3
    have h5 := hFind s hs t ht
    rcases h5 with ⟨h0s, h0t⟩ | h5
    · exact ⟨h0s, h0t⟩
    · rw [h4] at h5
      exact absurd h5 (by simp)
  obtain ⟨-, -, hFcard⟩ := closure_pair f1 f2 hf13 hf23 hf12 hFind'
  have hFE : Subgroup.closure {f1, f2} ≤ E :=
    (Subgroup.closure_le _).2 (by
      intro a ha
      rcases ha with rfl | rfl
      · exact hf1E
      · exact hf2E)
  have hrz := hz
  have hzi := R.rep_inv hz
  have hconj1 : z * f1 * z⁻¹ = f1 ^ d.cj.getD (4 * k) 0 * f2 ^ d.cj.getD (4 * k + 1) 0 :=
    R.rep_ext (R.rep_mul (R.rep_mul hz hrf1) hzi)
      (R.rep_mul (R.rep_pow hrf1 _) (R.rep_pow hrf2 _)) hc1
  have hconj2 : z * f2 * z⁻¹ = f1 ^ d.cj.getD (4 * k + 2) 0 * f2 ^ d.cj.getD (4 * k + 3) 0 :=
    R.rep_ext (R.rep_mul (R.rep_mul hz hrf2) hzi)
      (R.rep_mul (R.rep_pow hrf1 _) (R.rep_pow hrf2 _)) hc2
  have hF1 : f1 ∈ Subgroup.closure {f1, f2} := Subgroup.subset_closure (by simp)
  have hF2 : f2 ∈ Subgroup.closure {f1, f2} := Subgroup.subset_closure (by simp)
  have hnorm : z ∈ Subgroup.normalizer ((Subgroup.closure {f1, f2} : Subgroup X) : Set X) := by
    apply mem_normalizer_of_conj_mem
    apply conj_mem_of_gens (S := {f1, f2})
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [hconj1]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hF1 _) (Subgroup.pow_mem _ hF2 _)
    · rw [hconj2]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hF1 _) (Subgroup.pow_mem _ hF2 _)
  exact normalizer_le_weakCore_of_E27 (R := E) le_rfl hEc.1 hEc.2.1 hEc.2.2 hFE hFcard hnorm

end CFSG.AGLEmbedding.ChevOuter.U38
