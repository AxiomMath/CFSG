module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Reach
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.J3F0Invariant

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.RankThree.Asc83Table Subgroup Matrix

namespace J3Pkg

variable {X : Type*} [Group X] [Finite X] {k : Fin 6 → X} (h : J3Pkg k)
include h

theorem exists_realize (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hM : M ∈ matS) :
    ∃ y ∈ Subgroup.closure (Set.range k),
      ∃ hn : y ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X),
        conjMat h.bEq ⟨y, hn⟩ = M := by
  let R : Submonoid (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
    { carrier := {M | ∃ y ∈ Subgroup.closure (Set.range k),
        ∃ hn : y ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X),
          conjMat h.bEq ⟨y, hn⟩ = M}
      one_mem' := by
        refine ⟨1, one_mem _, one_mem _, ?_⟩
        exact conjMat_one h.bEq
      mul_mem' := by
        rintro _ _ ⟨y, hy, hn, rfl⟩ ⟨z, hz, hn', rfl⟩
        exact ⟨y * z, mul_mem hy hz, mul_mem hn hn', conjMat_mul h.bEq ⟨y, hn⟩ ⟨z, hn'⟩⟩ }
  have hgen : ∀ i : Fin 3, actMat ⟨i.val, by omega⟩ ∈ R := by
    intro i
    have hk : k ⟨i.val, by omega⟩ ∈ normalizer (Subgroup.closure (Set.range (xB k)) : Set X) :=
      h.k_mem_normalizer _
    exact ⟨k ⟨i.val, by omega⟩, Subgroup.subset_closure ⟨_, rfl⟩, hk, h.conjMat_gen _ hk⟩
  have hsub : Submonoid.closure {actMat 0, actMat 1, actMat 2} ≤ R := by
    rw [Submonoid.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hgen 0
    · exact hgen 1
    · exact hgen 2
  exact hsub (matS_mem_closure M hM)

@[expose] noncomputable def phi (v : Fin 4 → ZMod 3) : X :=
  ((h.bEq (Multiplicative.ofAdd v) : Subgroup.closure (Set.range (xB k))) : X)

theorem phi_add (v w : Fin 4 → ZMod 3) : h.phi (v + w) = h.phi v * h.phi w := by
  unfold phi
  rw [ofAdd_add, map_mul]
  rfl

theorem phi_zero : h.phi 0 = 1 := by
  unfold phi
  rw [ofAdd_zero, map_one]
  rfl

theorem phi_single (i : Fin 4) : h.phi (Pi.single i 1) = xB k i := by
  unfold phi
  exact basisEquiv_single h.x_pow h.x_comm h.basisProd_injective i

theorem phi_inj {v w : Fin 4 → ZMod 3} (hvw : h.phi v = h.phi w) : v = w := by
  unfold phi at hvw
  have := h.bEq.injective (Subtype.ext hvw)
  exact Multiplicative.ofAdd.injective this

theorem phi_mem (v : Fin 4 → ZMod 3) : h.phi v ∈ F0 k := Subtype.mem _

theorem exists_phi {x : X} (hx : x ∈ F0 k) : ∃ v, h.phi v = x := by
  obtain ⟨g, hg⟩ := h.bEq.surjective ⟨x, hx⟩
  refine ⟨Multiplicative.toAdd g, ?_⟩
  unfold phi
  rw [ofAdd_toAdd, hg]

theorem conj_phi (y : X) (hy : y ∈ Subgroup.closure (Set.range k)) :
    ∃ M ∈ matS, ∀ v, y * h.phi v * y⁻¹ = h.phi (M *ᵥ v) := by
  obtain ⟨hn, hM⟩ := h.matrix_mem y hy
  refine ⟨_, hM, fun v => ?_⟩
  exact conj_coord h.bEq ⟨y, hn⟩ v

theorem phi_eq_prod (v : Fin 4 → ZMod 3) :
    h.phi v = k 3 ^ (v 0).val * (k 4 ^ (v 1).val * (k 5 ^ (v 2).val * (xB k 3) ^ (v 3).val)) := by
  have e1 := coe_basisEquiv h.x_pow h.x_comm h.basisProd_injective v
  unfold phi
  exact e1.trans ((basisProd_xB (k := k) v).trans rfl)

end J3Pkg

@[expose] def F1 {X : Type*} [Group X] (k : Fin 6 → X) : Subgroup X :=
  Subgroup.closure {xB k 1, xB k 2, xB k 3}

namespace J3Pkg

variable {X : Type*} [Group X] [Finite X] {k : Fin 6 → X} (h : J3Pkg k)
include h

@[expose] def coordSub (S : Subgroup X) : AddSubgroup (Fin 4 → ZMod 3) where
  carrier := {v | h.phi v ∈ S}
  zero_mem' := by
    show h.phi 0 ∈ S
    rw [h.phi_zero]; exact one_mem _
  add_mem' := by
    intro v w hv hw
    show h.phi (v + w) ∈ S
    rw [h.phi_add]; exact mul_mem hv hw
  neg_mem' := by
    intro v hv
    show h.phi (-v) ∈ S
    have : h.phi (-v) = (h.phi v)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← h.phi_add, show -v + v = 0 from neg_add_cancel v, h.phi_zero]
    rw [this]; exact inv_mem hv

theorem mem_coordSub {S : Subgroup X} {v : Fin 4 → ZMod 3} : v ∈ h.coordSub S ↔ h.phi v ∈ S :=
  Iff.rfl

theorem phi_e3 : h.phi ![0, 0, 0, 1] = xB k 3 := by
  have : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = Pi.single 3 1 := by
    ext i; fin_cases i <;> simp
  rw [this, h.phi_single]

theorem phi_e1 : h.phi ![0, 1, 0, 0] = xB k 1 := by
  have : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = Pi.single 1 1 := by
    ext i; fin_cases i <;> simp
  rw [this, h.phi_single]

theorem phi_e2 : h.phi ![0, 0, 1, 0] = xB k 2 := by
  have : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = Pi.single 2 1 := by
    ext i; fin_cases i <;> simp
  rw [this, h.phi_single]

theorem phi_mem_F1 {v : Fin 4 → ZMod 3} (hv0 : v 0 = 0) : h.phi v ∈ F1 k := by
  rw [h.phi_eq_prod, hv0]
  have g1 : k 4 ∈ F1 k := Subgroup.subset_closure (by simp [xB])
  have g2 : k 5 ∈ F1 k := Subgroup.subset_closure (by simp [xB])
  have g3 : xB k 3 ∈ F1 k := Subgroup.subset_closure (by simp)
  simp only [ZMod.val_zero, pow_zero, one_mul]
  exact mul_mem (Subgroup.pow_mem _ g1 _) (mul_mem (Subgroup.pow_mem _ g2 _)
    (Subgroup.pow_mem _ g3 _))

theorem mem_F1_iff {x : X} : x ∈ F1 k ↔ ∃ v : Fin 4 → ZMod 3, v 0 = 0 ∧ h.phi v = x := by
  constructor
  · intro hx
    let T : Subgroup X :=
      { carrier := {x | ∃ v : Fin 4 → ZMod 3, v 0 = 0 ∧ h.phi v = x}
        one_mem' := ⟨0, rfl, h.phi_zero⟩
        mul_mem' := by
          rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
          exact ⟨v + w, by simp [hv, hw], h.phi_add v w⟩
        inv_mem' := by
          rintro _ ⟨v, hv, rfl⟩
          refine ⟨-v, by show -(v 0) = 0; rw [hv]; decide, ?_⟩
          rw [eq_inv_iff_mul_eq_one, ← h.phi_add, show -v + v = 0 from neg_add_cancel v,
            h.phi_zero] }
    have hle : F1 k ≤ T := by
      rw [F1, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨_, rfl, h.phi_e1⟩
      · exact ⟨_, rfl, h.phi_e2⟩
      · exact ⟨_, rfl, h.phi_e3⟩
    exact hle hx
  · rintro ⟨v, hv, rfl⟩
    exact h.phi_mem_F1 hv

theorem F1_le_F0 : F1 k ≤ F0 k := fun x hx => by
  obtain ⟨v, -, rfl⟩ := (h.mem_F1_iff).1 hx
  exact h.phi_mem v

theorem card_F1 : Nat.card (F1 k) = 27 := by
  have hge : 27 ≤ Nat.card (F1 k) := by
    let f : (Fin 3 → ZMod 3) → F1 k := fun w =>
      ⟨h.phi (Fin.cons 0 w), h.phi_mem_F1 (by simp)⟩
    have hf : Function.Injective f := by
      intro w w' hww
      have hww' : h.phi (Fin.cons 0 w) = h.phi (Fin.cons 0 w') := by
        simpa [f] using congrArg (fun z : F1 k => (z : X)) hww
      have := h.phi_inj hww'
      have h2 := congrArg (fun u : Fin 4 → ZMod 3 => fun i : Fin 3 => u i.succ) this
      simpa using h2
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hdvd : Nat.card (F1 k) ∣ 81 := by
    rw [← h.card_F0]
    exact Subgroup.card_dvd_of_le (h.F1_le_F0)
  have hne : Nat.card (F1 k) ≠ 81 := by
    intro h81
    have heq : F1 k = F0 k := Subgroup.eq_of_le_of_card_ge h.F1_le_F0 (by rw [h81, h.card_F0])
    have hm : h.phi ![1, 0, 0, 0] ∈ F1 k := by rw [heq]; exact h.phi_mem _
    obtain ⟨v, hv0, hv⟩ := (h.mem_F1_iff).1 hm
    have := h.phi_inj hv
    rw [this] at hv0
    simp at hv0
  have hcases : ∀ d : ℕ, d ∣ 81 → 27 ≤ d → d ≠ 81 → d = 27 := by
    intro d hd h27 h81
    have hd' : d ≤ 81 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> simp_all <;> omega
  exact hcases _ hdvd hge hne

omit [Group X] [Finite X] h in
theorem hyp_row (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hM : M ∈ matS) :
    M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 0 3 = 0 := by
  have hchk : matS.all (fun s => decide (s 0 1 = 0) && decide (s 0 2 = 0) &&
      decide (s 0 3 = 0)) = true := by decide +kernel
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hchk M hM
  exact ⟨h1, h2, h3⟩

theorem conj_F1 (y : X) (hy : y ∈ Subgroup.closure (Set.range k)) (s : X) (hs : s ∈ F1 k) :
    y * s * y⁻¹ ∈ F1 k := by
  obtain ⟨M, hM, hconj⟩ := h.conj_phi y hy
  obtain ⟨v, hv0, rfl⟩ := (h.mem_F1_iff).1 hs
  rw [hconj]
  apply h.phi_mem_F1
  obtain ⟨h1, h2, h3⟩ := hyp_row M hM
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv0, h1, h2, h3]

theorem xB3_ne_one : xB k 3 ≠ 1 := by
  rw [← h.phi_e3]
  exact h.basisProd_ne_one (a := ![0, 0, 0, 1]) (by
    intro h0; have := congrFun h0 3; simp at this)

theorem zpowers_xB3_eq_center (hZ3 : Nat.card (Subgroup.center X) = 3) :
    Subgroup.zpowers (xB k 3) = Subgroup.center X := by
  have hle : Subgroup.zpowers (xB k 3) ≤ Subgroup.center X := by
    rw [Subgroup.zpowers_le]; exact h.zc
  have hord : orderOf (xB k 3) = 3 := by
    have h3 := h.x_pow 3
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) h.xB3_ne_one
    · exact h1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hZ3, Nat.card_zpowers, hord]

theorem invariant_F0 (S : Subgroup X) (hSF : S ≤ F0 k)
    (hinv : ∀ y ∈ Subgroup.closure (Set.range k), ∀ s ∈ S, y * s * y⁻¹ ∈ S) :
    S = ⊥ ∨ S = Subgroup.zpowers (xB k 3) ∨ S = F1 k ∨ S = F0 k := by
  have hS : ∀ M ∈ matS, ∀ v ∈ h.coordSub S, M *ᵥ v ∈ h.coordSub S := by
    intro M hM v hv
    obtain ⟨y, hy, hn, hMy⟩ := h.exists_realize M hM
    have := conj_coord h.bEq ⟨y, hn⟩ v
    rw [hMy] at this
    have h2 : y * h.phi v * y⁻¹ = h.phi (M *ᵥ v) := this
    rw [mem_coordSub, ← h2]
    exact hinv y hy _ hv
  have key : ∀ x ∈ S, ∃ v ∈ h.coordSub S, h.phi v = x := by
    intro x hx
    obtain ⟨v, hv⟩ := h.exists_phi (hSF hx)
    exact ⟨v, by rw [mem_coordSub, hv]; exact hx, hv⟩
  rcases matS_invariant_addSubgroups (h.coordSub S) hS with h0 | h3 | h1 | hall
  · left
    refine (Subgroup.eq_bot_iff_forall S).2 fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := key x hx
    rw [(h0 v).1 hv, h.phi_zero]
  · right; left
    apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := key x hx
      obtain ⟨t, rfl⟩ := (h3 v).1 hv
      have e : t • (![0, 0, 0, 1] : Fin 4 → ZMod 3) =
          (t.val : ℕ) • (![0, 0, 0, 1] : Fin 4 → ZMod 3) := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
      have hp : ∀ n : ℕ, h.phi (n • (![0, 0, 0, 1] : Fin 4 → ZMod 3)) = (xB k 3) ^ n := by
        intro n
        induction n with
        | zero => simpa using h.phi_zero
        | succ n ihn => rw [succ_nsmul, h.phi_add, ihn, h.phi_e3, pow_succ]
      rw [e, hp]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [Subgroup.zpowers_le, ← h.phi_e3]
      exact (h3 ![0, 0, 0, 1]).2 ⟨1, (one_smul _ _).symm⟩
  · right; right; left
    apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := key x hx
      have hv0 : v 0 = 0 := (h1 v).1 hv
      rw [h.phi_eq_prod, hv0]
      have g1 : k 4 ∈ F1 k := Subgroup.subset_closure (by simp [xB])
      have g2 : k 5 ∈ F1 k := Subgroup.subset_closure (by simp [xB])
      have g3 : xB k 3 ∈ F1 k := Subgroup.subset_closure (by simp)
      simp only [ZMod.val_zero, pow_zero, one_mul]
      exact mul_mem (Subgroup.pow_mem _ g1 _) (mul_mem (Subgroup.pow_mem _ g2 _)
        (Subgroup.pow_mem _ g3 _))
    · rw [F1, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [← h.phi_e1]; exact (h1 _).2 rfl
      · rw [← h.phi_e2]; exact (h1 _).2 rfl
      · rw [← h.phi_e3]; exact (h1 _).2 rfl
  · right; right; right
    apply le_antisymm hSF
    intro x hx
    obtain ⟨v, rfl⟩ := h.exists_phi hx
    exact hall v

end J3Pkg

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
