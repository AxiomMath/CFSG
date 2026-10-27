module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Invol
public import Certificates.Data.A5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools Sec2V4 Equiv

namespace Sec2

theorem fixed_pair_aux : ∀ c : Fin 5 → ZMod 2, IsEven c →
    act (swap 2 3 * swap 3 4) c = c → act (swap 0 1 * swap 2 3) c = c →
      c = 0 ∨ c = pair 0 1 := by
  decide

theorem mem_alt_234 : (swap 2 3 * swap 3 4 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
  decide

theorem mem_alt_0123 : (swap 0 1 * swap 2 3 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
  decide

theorem act_234_pair : act (swap 2 3 * swap 3 4) (pair 0 1) = pair 0 1 := by decide

theorem act_0123_pair : act (swap 0 1 * swap 2 3) (pair 0 1) = pair 0 1 := by decide

theorem isEven_smul (a : ZMod 2) {v : Fin 5 → ZMod 2} (hv : IsEven v) : IsEven (a • v) := by
  rcases zmod2_cases a with rfl | rfl
  · rw [zero_smul]
    exact isEven_zero
  · rw [one_smul]
    exact hv

theorem exists_smul_of_equivariant {f : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2)}
    (hadd : ∀ v w, IsEven v → IsEven w → f (v + w) = f v + f w)
    (hequiv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEven v → f (act σ v) = act σ (f v))
    (heven : ∀ v, IsEven v → IsEven (f v)) : ∃ a : ZMod 2, ∀ v, IsEven v → f v = a • v := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0 isEven_zero isEven_zero
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  have hsmul : ∀ (a : ZMod 2) v, IsEven v → f (a • v) = a • f v := by
    intro a v _
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul, zero_smul, h0]
    · rw [one_smul, one_smul]
  have hfix : ∀ σ ∈ alternatingGroup (Fin 5), act σ (pair 0 1) = pair 0 1 →
      act σ (f (pair 0 1)) = f (pair 0 1) := by
    intro σ hσ hσp
    rw [← hequiv σ hσ _ (isEven_pair 0 1), hσp]
  have hc := fixed_pair_aux _ (heven _ (isEven_pair 0 1)) (hfix _ mem_alt_234 act_234_pair)
    (hfix _ mem_alt_0123 act_0123_pair)
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, f (pair 0 1) = a • pair 0 1 := by
    rcases hc with h | h
    · exact ⟨0, by rw [h, zero_smul]⟩
    · exact ⟨1, by rw [h, one_smul]⟩
  have hpair : ∀ k : Fin 5, k ≠ 0 → f (pair 0 k) = a • pair 0 k := by
    intro k hk
    obtain ⟨σ, hσ, h0', h1'⟩ := exists_apply_eq (i := 0) (j := 1) (a := 0) (b := k) (by decide)
      hk.symm
    have e : pair 0 k = act σ (pair 0 1) := by rw [act_pair, h0', h1']
    rw [e, hequiv σ hσ _ (isEven_pair 0 1), ha]
    rfl
  refine ⟨a, fun v hv => ?_⟩
  have hev : ∀ k : Fin 5, IsEven (v k • pair 0 k) := fun k => isEven_smul _ (isEven_pair 0 k)
  rw [even_eq_sum v hv]
  rw [hadd _ _ (isEven_add (isEven_add (hev 1) (hev 2)) (hev 3)) (hev 4),
    hadd _ _ (isEven_add (hev 1) (hev 2)) (hev 3), hadd _ _ (hev 1) (hev 2),
    hsmul _ _ (isEven_pair 0 1), hsmul _ _ (isEven_pair 0 2), hsmul _ _ (isEven_pair 0 3),
    hsmul _ _ (isEven_pair 0 4), hpair 1 (by decide), hpair 2 (by decide), hpair 3 (by decide),
    hpair 4 (by decide)]
  simp only [smul_add, smul_smul, mul_comm]

abbrev Mat2 := Fin 2 → Fin 2 → ZMod 2

@[expose] def matAct (M : Mat2) (m : Pair) : Pair :=
  (M 0 0 • m.1 + M 0 1 • m.2, M 1 0 • m.1 + M 1 1 • m.2)

@[expose] def matMul (M N : Mat2) : Mat2 := fun i j => M i 0 * N 0 j + M i 1 * N 1 j

@[expose] def matOne : Mat2 := fun i j => if i = j then 1 else 0

theorem matAct_matMul (M N : Mat2) (m : Pair) :
    matAct (matMul M N) m = matAct M (matAct N m) := by
  simp only [matAct, matMul, Prod.mk.injEq]
  constructor <;>
  · funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem matAct_matOne (m : Pair) : matAct matOne m = m := by
  simp [matAct, matOne]

theorem smul_pair_inj : ∀ a b : ZMod 2, a • pair 0 1 = b • pair 0 1 → a = b := by decide

theorem mat_eq_of_matAct {M N : Mat2}
    (h : ∀ m : Pair, IsEven m.1 → IsEven m.2 → matAct M m = matAct N m) : M = N := by
  have h1 := h (pair 0 1, 0) (isEven_pair 0 1) isEven_zero
  have h2 := h (0, pair 0 1) isEven_zero (isEven_pair 0 1)
  simp only [matAct, Prod.mk.injEq, smul_zero, add_zero, zero_add] at h1 h2
  funext i j
  fin_cases i <;> fin_cases j
  · exact smul_pair_inj _ _ h1.1
  · exact smul_pair_inj _ _ h2.1
  · exact smul_pair_inj _ _ h1.2
  · exact smul_pair_inj _ _ h2.2

theorem exists_mat_of_equivariant {f : Pair → Pair}
    (hadd : ∀ m n : Pair, IsEven m.1 → IsEven m.2 → IsEven n.1 → IsEven n.2 →
      f (m + n) = f m + f n)
    (hequiv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ m : Pair, IsEven m.1 → IsEven m.2 →
      f (act₂ σ m) = act₂ σ (f m))
    (heven : ∀ m : Pair, IsEven m.1 → IsEven m.2 → IsEven (f m).1 ∧ IsEven (f m).2) :
    ∃ M : Mat2, ∀ m : Pair, IsEven m.1 → IsEven m.2 → f m = matAct M m := by
  have hblock : ∀ (p : Pair → Fin 5 → ZMod 2) (ι : (Fin 5 → ZMod 2) → Pair),
      (∀ m n, p (m + n) = p m + p n) → (∀ σ m, p (act₂ σ m) = act σ (p m)) →
      (∀ m, IsEven m.1 → IsEven m.2 → IsEven (p m)) →
      (∀ v w, ι (v + w) = ι v + ι w) → (∀ σ v, ι (act σ v) = act₂ σ (ι v)) →
      (∀ v, IsEven v → IsEven (ι v).1 ∧ IsEven (ι v).2) →
      ∃ a : ZMod 2, ∀ v, IsEven v → p (f (ι v)) = a • v := by
    intro p ι hp hpσ hpe hι hισ hιe
    refine exists_smul_of_equivariant (fun v w hv hw => ?_) (fun σ hσ v hv => ?_)
      (fun v hv => hpe _ (heven _ (hιe v hv).1 (hιe v hv).2).1
        (heven _ (hιe v hv).1 (hιe v hv).2).2)
    · rw [hι, hadd _ _ (hιe v hv).1 (hιe v hv).2 (hιe w hw).1 (hιe w hw).2, hp]
    · rw [hισ, hequiv σ hσ _ (hιe v hv).1 (hιe v hv).2, hpσ]
  have hι₁ : ∀ v, IsEven v → IsEven ((v, 0) : Pair).1 ∧ IsEven ((v, 0) : Pair).2 :=
    fun v hv => ⟨hv, isEven_zero⟩
  have hι₂ : ∀ v, IsEven v → IsEven ((0, v) : Pair).1 ∧ IsEven ((0, v) : Pair).2 :=
    fun v hv => ⟨isEven_zero, hv⟩
  obtain ⟨a₀₀, h₀₀⟩ := hblock Prod.fst (fun v => (v, 0)) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun m h1 _ => h1) (fun v w => by simp) (fun σ v => by simp [act₂, act_zero]) hι₁
  obtain ⟨a₁₀, h₁₀⟩ := hblock Prod.snd (fun v => (v, 0)) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun m _ h2 => h2) (fun v w => by simp) (fun σ v => by simp [act₂, act_zero]) hι₁
  obtain ⟨a₀₁, h₀₁⟩ := hblock Prod.fst (fun v => (0, v)) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun m h1 _ => h1) (fun v w => by simp) (fun σ v => by simp [act₂, act_zero]) hι₂
  obtain ⟨a₁₁, h₁₁⟩ := hblock Prod.snd (fun v => (0, v)) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun m _ h2 => h2) (fun v w => by simp) (fun σ v => by simp [act₂, act_zero]) hι₂
  refine ⟨![![a₀₀, a₀₁], ![a₁₀, a₁₁]], fun m hm1 hm2 => ?_⟩
  have e : ((m.1, 0) : Pair) + (0, m.2) = m := by simp
  have hf := hadd (m.1, 0) (0, m.2) hm1 isEven_zero isEven_zero hm2
  rw [e] at hf
  rw [hf]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, matAct]
    rw [h₀₀ _ hm1, h₀₁ _ hm2]
    simp
  · simp only [Prod.snd_add, matAct]
    rw [h₁₀ _ hm1, h₁₁ _ hm2]
    simp

@[expose] def invol : Fin 3 → Mat2 :=
  ![![![0, 1], ![1, 0]], ![![1, 1], ![0, 1]], ![![1, 0], ![1, 1]]]

@[expose] def ord3 : Fin 2 → Mat2 := ![![![0, 1], ![1, 1]], ![![1, 1], ![1, 0]]]

theorem invol_cases : ∀ T : Mat2, matMul T T = matOne → T ≠ matOne → ∃ i, T = invol i := by
  decide

theorem ord3_cases : ∀ X : Mat2, (fun i j => matMul X X i j + X i j + matOne i j) = 0 →
    ∃ i, X = ord3 i := by
  decide

theorem conj_cases : ∀ (i : Fin 2) (j k : Fin 3), invol k = invol j ∨
    invol k = matMul (matMul (ord3 i) (invol j)) (matMul (ord3 i) (ord3 i)) ∨
    invol k = matMul (matMul (matMul (ord3 i) (ord3 i)) (invol j)) (ord3 i) := by
  decide

variable {G : Type} [Group G]

section Coord

variable {S Z H : Subgroup G}

@[expose] noncomputable def Coord.conjPair (C : Coord S Z H) (g : G) (m : Pair) : Pair := by
  classical
  exact if h : ∃ s ∈ S, C.Ψ s = m then C.Ψ (g * h.choose * g⁻¹) else 0

theorem Coord.conjPair_Ψ (C : Coord S Z H) (hS : Special S Z) {g : G}
    (hg : g ∈ normalizer (S : Set G)) {s : G} (hs : s ∈ S) :
    C.conjPair g (C.Ψ s) = C.Ψ (g * s * g⁻¹) := by
  classical
  have h : ∃ s' ∈ S, C.Ψ s' = C.Ψ s := ⟨s, hs, rfl⟩
  simp only [Coord.conjPair, h, ↓reduceDIte]
  obtain ⟨hs', heq⟩ := h.choose_spec
  have hgs : ∀ {a : G}, a ∈ S → g * a * g⁻¹ ∈ S := fun ha => (mem_normalizer_iff.mp hg _).mp ha
  rw [C.Ψ_eq_iff hS (hgs hs') (hgs hs)]
  have h1 := (C.Ψ_eq_iff hS hs' hs).mp heq
  have e : g * h.choose * g⁻¹ * (g * s * g⁻¹)⁻¹ = g * (h.choose * s⁻¹) * g⁻¹ := by group
  rw [e]
  exact conj_mem_Z_of_normS hS hg h1

theorem Coord.exists_mat_of_mem (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hSH : normalizer (S : Set G) ≤ normalizer (H : Set G))
    {g : G} (hg : g ∈ normalizer (S : Set G)) (hgH : ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ S) :
    ∃ M : Mat2, ∀ s ∈ S, C.Ψ (g * s * g⁻¹) = matAct M (C.Ψ s) := by
  have hgs : ∀ {a : G}, a ∈ S → g * a * g⁻¹ ∈ S := fun ha => (mem_normalizer_iff.mp hg _).mp ha
  have hadd : ∀ m n : Pair, IsEven m.1 → IsEven m.2 → IsEven n.1 → IsEven n.2 →
      C.conjPair g (m + n) = C.conjPair g m + C.conjPair g n := by
    intro m n hm1 hm2 hn1 hn2
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    obtain ⟨s', hs', hsn⟩ := C.exists_Ψ_eq hn1 hn2
    rw [Prod.mk.eta] at hsm hsn
    subst hsm hsn
    rw [← C.Ψ_mul hS hs hs', C.conjPair_Ψ hS hg (S.mul_mem hs hs'), C.conjPair_Ψ hS hg hs,
      C.conjPair_Ψ hS hg hs', ← C.Ψ_mul hS (hgs hs) (hgs hs')]
    congr 1
    group
  have hequiv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ m : Pair, IsEven m.1 → IsEven m.2 →
      C.conjPair g (act₂ σ m) = act₂ σ (C.conjPair g m) := by
    intro σ hσ m hm1 hm2
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    rw [Prod.mk.eta] at hsm
    subst hsm
    obtain ⟨h, hh⟩ := C.surj ⟨σ, hσ⟩
    have hhs : (h : G) * s * (h : G)⁻¹ ∈ S := (mem_normalizer_iff.mp (hHS h.2) _).mp hs
    have e1 : act₂ σ (C.Ψ s) = C.Ψ ((h : G) * s * (h : G)⁻¹) := by
      rw [C.Ψ_conj hS h hs, hh]
    have hgh : g * h * g⁻¹ ∈ H := (mem_normalizer_iff.mp (hSH hg) _).mp h.2
    have hφ : C.φ ⟨g * h * g⁻¹, hgh⟩ = C.φ h := by
      have hk : (⟨g * h * g⁻¹, hgh⟩ : ↥H) * h⁻¹ ∈ C.φ.ker := by
        rw [C.ker, mem_subgroupOf]
        exact hgH h h.2
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
      exact hk
    rw [e1, C.conjPair_Ψ hS hg hhs, C.conjPair_Ψ hS hg hs]
    have e2 : g * ((h : G) * s * (h : G)⁻¹) * g⁻¹ =
        (g * h * g⁻¹) * (g * s * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
    rw [e2]
    have h3 := C.Ψ_conj hS ⟨g * h * g⁻¹, hgh⟩ (hgs hs)
    simp only at h3
    rw [h3, hφ, hh]
  have heven : ∀ m : Pair, IsEven m.1 → IsEven m.2 →
      IsEven (C.conjPair g m).1 ∧ IsEven (C.conjPair g m).2 := by
    intro m hm1 hm2
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    rw [Prod.mk.eta] at hsm
    subst hsm
    rw [C.conjPair_Ψ hS hg hs]
    exact C.Ψ_even hS (hgs hs)
  obtain ⟨M, hM⟩ := exists_mat_of_equivariant hadd hequiv heven
  exact ⟨M, fun s hs => by
    rw [← C.conjPair_Ψ hS hg hs]
    exact hM _ (C.Ψ_even hS hs).1 (C.Ψ_even hS hs).2⟩

end Coord

end Sec2

end CFSG.ComponentClassification.AS81
