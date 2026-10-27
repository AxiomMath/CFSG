module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step26iiPerm
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Mat
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step213
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Cent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools Sec2V4 Equiv

namespace Sec2

theorem matAct_act₂ (M : Mat2) (π : Perm (Fin 5)) (m : Pair) :
    matAct M (act₂ π m) = act₂ π (matAct M m) :=
  rfl

theorem matMul_matOne (M : Mat2) : matMul M matOne = M := by
  funext i j
  fin_cases j <;> simp [matMul, matOne]

theorem invol_mul_invol : ∀ i j : Fin 3,
    matMul (matMul (invol i) (invol j)) (matMul (invol i) (invol j)) = matOne →
      matMul (invol i) (invol j) = matOne := by
  decide

theorem eq_of_matAct_act₂ {M : Mat2} {ρ : Perm (Fin 5)}
    (h : ∀ m : Pair, IsEven m.1 → IsEven m.2 → matAct M (act₂ ρ m) = m) :
    M = matOne ∧ ρ = 1 := by
  have hp : pair 0 1 ≠ 0 := by decide
  have hx : act ρ (pair 0 1) ≠ 0 := fun h0 => hp (eq_zero_of_act_eq_zero h0)
  have h1 := h (pair 0 1, 0) (isEven_pair 0 1) isEven_zero
  have h2 := h (0, pair 0 1) isEven_zero (isEven_pair 0 1)
  simp only [matAct, act₂, act_zero, smul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  have hone : ∀ a : ZMod 2, a • act ρ (pair 0 1) = pair 0 1 → a = 1 := by
    intro a ha
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul] at ha
      exact absurd ha.symm hp
    · rfl
  have hzero : ∀ a : ZMod 2, a • act ρ (pair 0 1) = 0 → a = 0 := by
    intro a ha
    rcases zmod2_cases a with rfl | rfl
    · rfl
    · rw [one_smul] at ha
      exact absurd ha hx
  have hM : M = matOne := by
    funext i j
    fin_cases i <;> fin_cases j
    · simp [matOne, hone _ h1.1]
    · simp [matOne, hzero _ h2.1]
    · simp [matOne, hzero _ h1.2]
    · simp [matOne, hone _ h2.2]
  refine ⟨hM, eq_one_of_act_eq fun v hv => ?_⟩
  have h3 := h (v, 0) hv isEven_zero
  rw [hM, matAct_matOne] at h3
  exact congrArg Prod.fst h3

variable {G : Type} [Group G] {S Z H : Subgroup G}

@[expose] def Coord.ActsAs (C : Coord S Z H) (d : G) (π : Perm (Fin 5)) (M : Mat2) : Prop :=
  ∀ s ∈ S, C.Ψ (d * s * d⁻¹) = matAct M (act₂ π (C.Ψ s))

theorem Coord.ActsAs.mul {C : Coord S Z H} {a b : G} {π π' : Perm (Fin 5)} {M M' : Mat2}
    (ha : C.ActsAs a π M) (hb : C.ActsAs b π' M') (hbS : b ∈ normalizer (S : Set G)) :
    C.ActsAs (a * b) (π * π') (matMul M M') := by
  intro s hs
  have e : (a * b) * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
  rw [e, ha _ ((mem_normalizer_iff.mp hbS s).mp hs), hb s hs, matAct_matMul, ← act₂_mul]
  rfl

theorem Coord.actsAs_of_mem (C : Coord S Z H) (hS : Special S Z) {s : G} (hs : s ∈ S) :
    C.ActsAs s 1 matOne := by
  intro u hu
  rw [matAct_matOne, act₂_one, C.Ψ_conj_S hS hs hu]

theorem Coord.actsAs_one (C : Coord S Z H) : C.ActsAs 1 1 matOne := by
  intro u _
  rw [matAct_matOne, act₂_one, one_mul, inv_one, mul_one]

theorem Coord.ActsAs.sq_eq {C : Coord S Z H} (hS : Special S Z) {d : G} {π : Perm (Fin 5)}
    {M : Mat2} (hd : C.ActsAs d π M) (hdS : d ∈ normalizer (S : Set G)) (h2 : d * d ∈ S) :
    matMul M M = matOne ∧ π * π = 1 := by
  have hdd := hd.mul hd hdS
  refine eq_of_matAct_act₂ fun m hm1 hm2 => ?_
  obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
  rw [Prod.mk.eta] at hsm
  rw [← hsm, ← hdd s hs, C.Ψ_conj_S hS h2 hs]

theorem Coord.exists_actsAs (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hSH : normalizer (S : Set G) ≤ normalizer (H : Set G))
    {d : G} (hd : d ∈ normalizer (S : Set G)) :
    ∃ (π : Perm (Fin 5)) (M : Mat2), C.ActsAs d π M := by
  have hdH : d ∈ normalizer (H : Set G) := hSH hd
  have hds : ∀ {a : G}, a ∈ S → d * a * d⁻¹ ∈ S := fun ha => (mem_normalizer_iff.mp hd _).mp ha
  have hκ : C.φ.ker.map ((normalizerConj hdH : MulAut ↥H) : ↥H →* ↥H) = C.φ.ker := by
    rw [C.ker]
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_subgroupOf] at hy ⊢
      exact hds hy
    · intro hx
      rw [mem_subgroupOf] at hx
      refine ⟨⟨d⁻¹ * x * d, by simpa using (mem_normalizer_iff.mp (inv_mem hdH) x).mp x.2⟩, ?_, ?_⟩
      · rw [mem_subgroupOf]
        simpa using (mem_normalizer_iff.mp (inv_mem hd) x).mp hx
      · apply Subtype.ext
        show d * (d⁻¹ * x * d) * d⁻¹ = x
        group
  obtain ⟨π, hπ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inl rfl) (descendAut C.φ C.surj (normalizerConj hdH) hκ)
  have hφ : ∀ h : ↥H, ((C.φ (normalizerConj hdH h) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      π * (C.φ h : Perm (Fin 5)) * π⁻¹ := by
    intro h
    rw [← descendAut_apply C.φ C.surj (normalizerConj hdH) hκ h, hπ]
  have hadd : ∀ m n : Pair, IsEven m.1 → IsEven m.2 → IsEven n.1 → IsEven n.2 →
      C.conjPair d (m + n) = C.conjPair d m + C.conjPair d n := by
    intro m n hm1 hm2 hn1 hn2
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    obtain ⟨s', hs', hsn⟩ := C.exists_Ψ_eq hn1 hn2
    rw [Prod.mk.eta] at hsm hsn
    subst hsm hsn
    rw [← C.Ψ_mul hS hs hs', C.conjPair_Ψ hS hd (S.mul_mem hs hs'), C.conjPair_Ψ hS hd hs,
      C.conjPair_Ψ hS hd hs', ← C.Ψ_mul hS (hds hs) (hds hs')]
    congr 1
    group
  have heven : ∀ m : Pair, IsEven m.1 → IsEven m.2 →
      IsEven (C.conjPair d m).1 ∧ IsEven (C.conjPair d m).2 := by
    intro m hm1 hm2
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    rw [Prod.mk.eta] at hsm
    subst hsm
    rw [C.conjPair_Ψ hS hd hs]
    exact C.Ψ_even hS (hds hs)
  have htw : ∀ σ ∈ alternatingGroup (Fin 5), ∀ m : Pair, IsEven m.1 → IsEven m.2 →
      C.conjPair d (act₂ σ m) = act₂ (π * σ * π⁻¹) (C.conjPair d m) := by
    intro σ hσ m hm1 hm2
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    rw [Prod.mk.eta] at hsm
    subst hsm
    obtain ⟨h, hh⟩ := C.surj ⟨σ, hσ⟩
    have hhs : (h : G) * s * (h : G)⁻¹ ∈ S := (mem_normalizer_iff.mp (hHS h.2) _).mp hs
    have e1 : act₂ σ (C.Ψ s) = C.Ψ ((h : G) * s * (h : G)⁻¹) := by
      rw [C.Ψ_conj hS h hs, hh]
    rw [e1, C.conjPair_Ψ hS hd hhs, C.conjPair_Ψ hS hd hs]
    have e2 : d * ((h : G) * s * (h : G)⁻¹) * d⁻¹ = ((normalizerConj hdH h : ↥H) : G) *
        (d * s * d⁻¹) * ((normalizerConj hdH h : ↥H) : G)⁻¹ := by
      rw [coe_normalizerConj_apply]
      group
    rw [e2, C.Ψ_conj hS _ (hds hs), hφ h, hh]
  obtain ⟨M, hM⟩ := exists_mat_of_equivariant (f := fun m => act₂ π⁻¹ (C.conjPair d m))
    (fun m n hm1 hm2 hn1 hn2 => by
      rw [hadd m n hm1 hm2 hn1 hn2, act₂_add])
    (fun σ hσ m hm1 hm2 => by
      rw [htw σ hσ m hm1 hm2, act₂_mul, act₂_mul]
      congr 1
      group)
    (fun m hm1 hm2 => ⟨isEven_act (heven m hm1 hm2).1 _, isEven_act (heven m hm1 hm2).2 _⟩)
  refine ⟨π, M, fun s hs => ?_⟩
  have h1 := hM (C.Ψ s) (C.Ψ_even hS hs).1 (C.Ψ_even hS hs).2
  rw [← C.conjPair_Ψ hS hd hs, matAct_act₂, ← h1, act₂_mul, mul_inv_cancel, act₂_one]

end Sec2

end CFSG.ComponentClassification.AS81
