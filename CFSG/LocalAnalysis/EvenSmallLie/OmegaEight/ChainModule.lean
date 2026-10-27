module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coh

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem additive_eq_mulVec {f : V6 → V6} (hadd : ∀ v w, f (v + w) = f v + f w) (v : V6) :
    f v = (Matrix.of fun i j => f (Pi.single j 1) i) *ᵥ v := by
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  let F : V6 →+ V6 := AddMonoidHom.mk' f hadd
  have hsingle : ∀ (j : Fin 6) (c : ZMod 2), f (Pi.single j c) = c • f (Pi.single j 1) := by
    intro j c
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · rw [zero_smul, Pi.single_zero, h0]
    · rw [one_smul]
  conv_lhs => rw [← Finset.univ_sum_single v]
  have : f (∑ j, Pi.single j (v j)) = ∑ j, f (Pi.single j (v j)) := map_sum F _ _
  rw [this]
  ext i
  rw [Finset.sum_apply]
  simp only [mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsingle j (v j), Pi.smul_apply, smul_eq_mul, mul_comm]


theorem endF2 (ε : Eps) : EndF2 ε := by
  intro f hadd heq
  set X : Mat6 := Matrix.of fun i j => f (Pi.single j 1) i
  have hfX := additive_eq_mulVec hadd
  have hXM : ∀ s : Fin 6, genMat ε s * X + X * genMat ε s = 0 := by
    intro s
    have h : X * genMat ε s = genMat ε s * X := by
      rw [Matrix.ext_iff_mulVec]
      intro v
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← hfX, ← hfX, heq]
    rw [h, CharTwo.add_self_eq_zero]
  have hlin : cobLin6 ε X = 0 := by
    ext1 s
    simp only [cobLin6, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    exact hXM s
  have hR : toMat (6 * (6 * 6)) (1 * (6 * 6)) (linBits (1 * (6 * 6)) (6 * (6 * 6)) (cobFb6 ε)) *ᵥ
      vecOfN 6 1 (fun _ => X) = 0 := by
    rw [toMat_linBits_mulVec (cobFb6 ε) (cobF6 ε) (fun j => by rw [toVec_cobFb6, toVec_two_pow])]
    simp only [cobF6, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_apply,
      blocksOfN_vecOfN, LinearMap.proj_apply, hlin, blocksEquivN_symm_apply]
    ext i
    simp [vecOfN]
  obtain ⟨e, he⟩ := endCheck_spec ε _ hR
  rw [toMat_transpose_mulVec6] at he
  have hX : X = e 0 • 1 := by
    have h1 := congrArg (fun y => blocksOfN 6 1 y 0) he
    simp only [blocksOfN_vecOfN, Fin.sum_univ_one] at h1
    have h3 : blocksOfN 6 1 (toVec (1 * (6 * 6)) (packN 6 1 fun _ => id6)) 0 = 1 := by
      rw [blocksOfN_packN]; exact toMat_id6
    have h3' : blocksOfN 6 1 (toVec 36 (packN 6 1 fun _ => id6)) 0 = 1 := h3
    have h4 : ∀ (c : ZMod 2) (y : Fin (1 * (6 * 6)) → ZMod 2),
        blocksOfN 6 1 (c • y) 0 = c • blocksOfN 6 1 y 0 := by
      intro c y; ext a b; simp [blocksOfN]
    rw [h1, h4]
    congr 1
  have hfX' : ∀ v, f v = X *ᵥ v := hfX
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (e 0) with h | h
  · left
    intro v
    rw [hfX', hX, h, zero_smul, zero_mulVec]
  · right
    intro v
    rw [hfX', hX, h, one_smul, one_mulVec]

@[expose] def modBlockM (ε : Eps) (C : ℕ → Mat6) (k : ℕ) : Mat6 :=
  ((∑ j : Fin 6, genMat ε (k / 6) j ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ • C j) *
      genMat ε (k / 6) + genMat ε (k / 6) * C (k % 6)) +
    (C 6) ⟨k / 6 % 6, Nat.mod_lt _ (by norm_num)⟩ ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ •
      genMat ε (k / 6)

theorem toVec_colBits (M : Array ℕ) {l : ℕ} (hl : l < 6) :
    toVec 6 (colBits M l) = fun j => toMat 6 6 M j ⟨l, hl⟩ := by
  ext j
  simp [toVec, colBits, testBit_bitsOf, toMat_apply]

theorem toMat_ite_zero6 (b : Bool) (M : Array ℕ) :
    toMat 6 6 (if b then M else zero6) = bz b • toMat 6 6 M := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, bz_false, zero_smul]
    exact toMat_zero6
  · simp

theorem toMat_modBlock (ε : Eps) (C : ℕ → Array ℕ) {k : ℕ} (hk : k < 36) :
    toMat 6 6 (modBlock ε C k) = modBlockM ε (fun s => toMat 6 6 (C s)) k := by
  have hi : k / 6 < 6 := by omega
  have hl : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  unfold modBlock modBlockM
  rw [toMat_bxor, toMat_bxor, toMat_bmul, toMat_bmul, toMat_combo6, toMat_ite_zero6]
  congr 2
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun d => bz ((colBits (genRows ε (k / 6)) (k % 6)).testBit d) •
      toMat 6 6 (C d)) 6]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have := congrFun (toVec_colBits (genRows ε (k / 6)) hl) j
    rw [toVec] at this
    rw [this]
    rfl
  · congr 1
    show ((C 6).getD (k / 6) 0).testBit (k % 6) = ((C 6).getD (k / 6 % 6) 0).testBit (k % 6)
    rw [Nat.mod_eq_of_lt hi]

theorem modBlockM_congr (ε : Eps) {C C' : ℕ → Mat6} (h : ∀ s < 7, C s = C' s) (k : ℕ) :
    modBlockM ε C k = modBlockM ε C' k := by
  unfold modBlockM
  have hsum : (∑ j : Fin 6, genMat ε (k / 6) j ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ • C j) =
      ∑ j : Fin 6, genMat ε (k / 6) j ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ • C' j :=
    Finset.sum_congr rfl fun j _ => by rw [h j (by omega)]
  rw [hsum, h (k % 6) (by have := Nat.mod_lt k (show 6 > 0 by norm_num); omega), h 6 (by omega)]

theorem modBlockM_add (ε : Eps) (C C' : ℕ → Mat6) (k : ℕ) :
    modBlockM ε (C + C') k = modBlockM ε C k + modBlockM ε C' k := by
  unfold modBlockM
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, add_mul, mul_add, Matrix.add_apply,
    add_smul]
  abel

theorem modBlockM_smul (ε : Eps) (a : ZMod 2) (C : ℕ → Mat6) (k : ℕ) :
    modBlockM ε (a • C) k = a • modBlockM ε C k := by
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) a with rfl | rfl
  · simp [modBlockM]
  · simp

@[expose] def modLin (ε : Eps) : (Fin 7 → Mat6) →ₗ[ZMod 2] (Fin 36 → Mat6) where
  toFun C k := modBlockM ε (fun s => if h : s < 7 then C ⟨s, h⟩ else 0) k
  map_add' C C' := by
    ext1 k
    rw [Pi.add_apply, ← modBlockM_add]
    congr 1
    ext1 s
    by_cases hs : s < 7 <;> simp [hs]
  map_smul' a C := by
    ext1 k
    rw [Pi.smul_apply, RingHom.id_apply, ← modBlockM_smul]
    congr 1
    ext1 s
    by_cases hs : s < 7 <;> simp [hs]

@[expose] def modF (ε : Eps) :
    (Fin (7 * (6 * 6)) → ZMod 2) →ₗ[ZMod 2] (Fin (36 * (6 * 6)) → ZMod 2) :=
  (blocksEquivN 6 36).symm.toLinearMap ∘ₗ modLin ε ∘ₗ (blocksEquivN 6 7).toLinearMap

theorem toVec_modFb (ε : Eps) (v : ℕ) :
    toVec (36 * (6 * 6)) (modFb ε v) = modF ε (toVec (7 * (6 * 6)) v) := by
  rw [modFb, toVec_packN]
  simp only [modF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
    blocksEquivN_apply, modLin, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  ext1 k
  rw [toMat_modBlock ε _ k.isLt]
  refine modBlockM_congr ε (fun s hs => ?_) k
  rw [dite_eq_left hs]
  exact toMat_unpackN 6 7 v ⟨s, hs⟩

theorem modLin_apply (ε : Eps) (C : Fin 7 → Mat6) (k : Fin 36) :
    modLin ε C k =
      (∑ j : Fin 6, genMat ε (k / 6 : ℕ) j ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ •
          C ⟨j, by omega⟩) * genMat ε (k / 6 : ℕ) +
        genMat ε (k / 6 : ℕ) * C ⟨k % 6, by omega⟩ +
      C ⟨6, by norm_num⟩ ⟨k / 6, by omega⟩ ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ •
        genMat ε (k / 6 : ℕ) := by
  have hl : (k : ℕ) % 6 < 7 := by omega
  have hi : (k : ℕ) / 6 % 6 = k / 6 := Nat.mod_eq_of_lt (by omega)
  simp only [modLin, LinearMap.coe_mk, AddHom.coe_mk, modBlockM]
  have h1 : ∀ j : Fin 6, (if h : (j : ℕ) < 7 then C ⟨j, h⟩ else 0) = C ⟨j, by omega⟩ :=
    fun j => dite_eq_left (by omega)
  have h2 : (if h : (k : ℕ) % 6 < 7 then C ⟨k % 6, h⟩ else 0) = C ⟨k % 6, by omega⟩ :=
    dite_eq_left hl
  have h3 : (if h : (6 : ℕ) < 7 then C ⟨6, h⟩ else 0) = C ⟨6, by norm_num⟩ :=
    dite_eq_left (by norm_num)
  have h4 : (⟨(k : ℕ) / 6 % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = ⟨k / 6, by omega⟩ :=
    Fin.ext hi
  simp only [h1, h2, h3]
  rw [h4]

theorem homEndModZero (ε : Eps) : HomEndModZero ε := by
  intro F hv hu heq
  obtain ⟨Fm, hFm⟩ : ∃ Fm : V6 → Mat6, ∀ u v, F u v = Fm u *ᵥ v :=
    ⟨fun u => Matrix.of fun i j => F u (Pi.single j 1) i, fun u v => additive_eq_mulVec (hv u) v⟩
  have hFmu : ∀ u u', ∃ e : ZMod 2, Fm (u + u') = Fm u + Fm u' + e • 1 := by
    intro u u'
    obtain ⟨e, he⟩ := hu u u'
    refine ⟨e, Matrix.ext_iff_mulVec.2 fun v => ?_⟩
    rw [← hFm, he, hFm u, hFm u', add_mulVec, add_mulVec, smul_mulVec, one_mulVec]
  have hP0 : ∃ c : ZMod 2, Fm 0 = ∑ j, (0 : V6) j • Fm (Pi.single j 1) + c • 1 := by
    obtain ⟨e, he⟩ := hFmu 0 0
    refine ⟨e, ?_⟩
    rw [add_zero, CharTwo.add_self_eq_zero, zero_add] at he
    simp [he]
  have hlinP : ∀ w : V6, ∃ c : ZMod 2, Fm w = ∑ j, w j • Fm (Pi.single j 1) + c • 1 := by
    intro w
    have h := Finset.sum_induction (s := Finset.univ) (fun j => Pi.single j (w j))
      (fun w => ∃ c : ZMod 2, Fm w = ∑ j, w j • Fm (Pi.single j 1) + c • 1)
      (fun a b ⟨c, hc⟩ ⟨c', hc'⟩ => by
        obtain ⟨e, he⟩ := hFmu a b
        refine ⟨c + c' + e, ?_⟩
        rw [he, hc, hc']
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        abel)
      hP0
      (fun j _ => by
        rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (w j) with h | h
        · rw [h, Pi.single_zero]; exact hP0
        · refine ⟨0, ?_⟩
          rw [h, zero_smul, add_zero]
          simp [Pi.single_apply])
    simpa only [Finset.univ_sum_single] using h
  have hMeq : ∀ (i : Fin 6) (u : V6), ∃ e : ZMod 2,
      Fm (genMat ε i *ᵥ u) * genMat ε i = genMat ε i * Fm u + e • genMat ε i := by
    intro i u
    obtain ⟨e, he⟩ := heq i u
    refine ⟨e, Matrix.ext_iff_mulVec.2 fun v => ?_⟩
    rw [← mulVec_mulVec, ← hFm, he, add_mulVec, ← mulVec_mulVec, ← hFm, smul_mulVec]
  have hsys : ∀ i l : Fin 6, ∃ c : ZMod 2,
      (∑ j : Fin 6, genMat ε i j l • Fm (Pi.single j 1)) * genMat ε i +
        genMat ε i * Fm (Pi.single l 1) + c • genMat ε i = 0 := by
    intro i l
    obtain ⟨e, he⟩ := hMeq i (Pi.single l 1)
    obtain ⟨c, hc⟩ := hlinP (genMat ε i *ᵥ Pi.single l 1)
    refine ⟨c + e, ?_⟩
    rw [hc, add_mul, smul_mul_assoc, one_mul, mulVec_single_one] at he
    simp only [col_apply] at he
    calc _ = ((∑ j : Fin 6, genMat ε i j l • Fm (Pi.single j 1)) * genMat ε i +
          c • genMat ε i) + (genMat ε i * Fm (Pi.single l 1) + e • genMat ε i) := by
          rw [add_smul]; abel
      _ = 0 := by rw [he, CharTwo.add_self_eq_zero]
  choose Λ hΛ using hsys
  obtain ⟨C, hCj, hC6⟩ : ∃ C : Fin 7 → Mat6,
      (∀ (j : ℕ) (hj : j < 6), C ⟨j, by omega⟩ = Fm (Pi.single ⟨j, hj⟩ 1)) ∧
        C ⟨6, by norm_num⟩ = Matrix.of Λ :=
    ⟨fun s => if h : (s : ℕ) < 6 then Fm (Pi.single ⟨s, h⟩ 1) else Matrix.of Λ,
      fun j hj => by simp [hj], by simp⟩
  have hlin : modLin ε C = 0 := by
    ext1 k
    have hl : (k : ℕ) % 6 < 6 := Nat.mod_lt _ (by norm_num)
    rw [modLin_apply, Pi.zero_apply]
    simp only [hCj, hC6, hl, Fin.is_lt, Fin.eta, Matrix.of_apply]
    exact hΛ ⟨k / 6, by omega⟩ ⟨k % 6, hl⟩
  have hR : toMat (36 * (6 * 6)) (7 * (6 * 6)) (linBits (7 * (6 * 6)) (36 * (6 * 6)) (modFb ε)) *ᵥ
      vecOfN 6 7 C = 0 := by
    rw [toMat_linBits_mulVec (modFb ε) (modF ε) (fun j => by rw [toVec_modFb, toVec_two_pow])]
    simp only [modF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_apply,
      blocksOfN_vecOfN, hlin, blocksEquivN_symm_apply]
    ext i
    simp [vecOfN]
  obtain ⟨e, he⟩ := modCheck_spec ε _ hR
  rw [toMat_transpose_mulVec6] at he
  have hFj : ∀ j : Fin 6, Fm (Pi.single j 1) = e j • 1 := by
    intro j
    have h3 : ∀ m : Fin 6, blocksOfN 6 7 (toVec (7 * 36) ((Array.ofFn (n := 6) fun m =>
        modSol ε m).getD m 0)) ⟨j, by omega⟩ = if j = m then 1 else 0 := by
      intro m
      have h : blocksOfN 6 7 (toVec (7 * (6 * 6)) (modSol ε m)) ⟨j, by omega⟩ =
          if j = m then 1 else 0 := by
        rw [modSol, blocksOfN_packN]
        simp only [Fin.is_lt, ite_true]
        by_cases hjm : j = m
        · rw [ite_eq_left (congrArg Fin.val hjm), ite_eq_left hjm]
          exact toMat_id6
        · rw [ite_eq_right (fun h => hjm (Fin.ext h)), ite_eq_right hjm]
          exact toMat_zero6
      rw [getD_ofFn]
      exact h
    have h1 : blocksEquivN 6 7 (vecOfN 6 7 C) ⟨j, by omega⟩ =
        blocksEquivN 6 7 (∑ c : Fin 6, e c • toVec (7 * 36)
          ((Array.ofFn (n := 6) fun m => modSol ε m).getD c 0)) ⟨j, by omega⟩ := by
      rw [he]
    rw [map_sum, blocksEquivN_apply, blocksOfN_vecOfN, hCj j j.isLt, Fin.eta] at h1
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, blocksEquivN_apply, h3, smul_ite,
      smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h1
    exact h1
  intro u
  obtain ⟨c, hc⟩ := hlinP u
  refine ⟨∑ j, u j * e j + c, fun v => ?_⟩
  have : Fm u = (∑ j, u j * e j + c) • (1 : Mat6) := by
    rw [hc, add_smul, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFj, smul_smul]
  rw [hFm, this, smul_mulVec, one_mulVec]

section HomEnd

variable {G : Type*} [Group G] {ε : Eps} {L U Q P : Subgroup G}
  {a : G} {ψ : V6 → G} {p : Fin 6 → G}

theorem homEndZero (hR : RadicalData ε L U Q P a ψ p) : HomEndZero ε := by
  intro F hadd1 hadd2 heq
  obtain ⟨c, hc⟩ : ∃ c : V6 → ZMod 2, ∀ u v, F u v = c u • v := by
    have h := homEndModZero ε F hadd2
      (fun u u' => ⟨0, fun v => by rw [hadd1, zero_smul, add_zero]⟩)
      (fun i u => ⟨0, fun v => by rw [heq, zero_smul, add_zero]⟩)
    choose c hc using h
    exact ⟨c, hc⟩
  have hval : ∀ s s' : ZMod 2, (s • (Pi.single 0 1 : V6) = s' • Pi.single 0 1) → s = s' := by
    intro s s' h
    have := congrFun h 0
    simpa using this
  have hcadd : ∀ u u', c (u + u') = c u + c u' := fun u u' =>
    hval _ _ (by rw [← hc, hadd1, hc, hc, add_smul])
  have hcM : ∀ (i : Fin 6) u, c (genMat ε i *ᵥ u) = c u := by
    intro i u
    have hMinv : genMat ε i * genInvMat ε i = 1 :=
      _root_.mul_eq_one_comm.1 (genInvMat_mul_genMat ε i)
    have h := heq i u (genInvMat ε i *ᵥ Pi.single 0 1)
    rw [mulVec_mulVec, hMinv, one_mulVec, hc, hc, mulVec_smul, mulVec_mulVec, hMinv,
      one_mulVec] at h
    exact hval _ _ h
  have hcP : ∀ y ∈ Subgroup.closure ((Q : Set G) ∪ Set.range p), ∀ v, c (lin ψ y v) = c v := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | ⟨i, rfl⟩
      · intro v; rw [hR.lin_of_mem_Q hy]
      · intro v; rw [hR.lin_p, hcM]
    | one => intro v; rw [hR.lin_one]
    | mul y z hy hz ihy ihz =>
      intro v
      rw [hR.lin_mul (hR.closure_le_normalizer hy) (hR.closure_le_normalizer hz), ihy, ihz]
    | inv y hy ihy =>
      intro v
      conv_rhs => rw [← hR.lin_inv (hR.closure_le_normalizer hy) v]
      rw [ihy]
  set W₀ : AddSubgroup V6 := (AddMonoidHom.mk' c hcadd).ker with hW₀
  have hW₀P : ∀ x ∈ P, ∀ w ∈ W₀, lin ψ x w ∈ W₀ := by
    intro x hx w hw
    rw [hW₀, AddMonoidHom.mem_ker] at hw ⊢
    change c (lin ψ x w) = 0
    rw [hcP x (hR.P_le hx)]
    exact hw
  have hne : W₀ ≠ ⊥ := by
    rw [Ne, AddSubgroup.eq_bot_iff_forall]
    intro h
    have hs : ∀ j : Fin 6, (Pi.single j 1 : V6) ≠ 0 := fun j h0 => by
      have := congrFun h0 j
      simp at this
    have h01 : (Pi.single 0 1 + Pi.single 1 1 : V6) ≠ 0 := fun h0 => by
      have := congrFun h0 0
      simp at this
    have hk : ∀ w : V6, c w = 0 → w = 0 := fun w hw => h w (AddMonoidHom.mem_ker.2 hw)
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (c (Pi.single 0 1)) with h0 | h0
    · exact hs 0 (hk _ h0)
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (c (Pi.single 1 1)) with h1 | h1
    · exact hs 1 (hk _ h1)
    exact h01 (hk _ (by rw [hcadd, h0, h1]; decide))
  have htop := eq_top_of_ne_bot_v6 hR hW₀P hne
  intro u v
  have hu : u ∈ W₀ := by rw [htop]; exact AddSubgroup.mem_top u
  rw [hc, show c u = 0 from AddMonoidHom.mem_ker.1 hu, zero_smul]

end HomEnd

end CFSG.EvenSmallLie.OmegaEight.Chain
