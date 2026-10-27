module

public import Certificates.Certificate214101
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Blueprint.Chevalley.RootCertificate


theorem twD4T2Check_spec :
    twD4T2RepsOK () = true ∧
      (∀ b ∈ twD4T2Sig (), twD4T2RowOK b (twD4T2Row (twD4T2Vecs ()) b) = true) ∧
      twD4T2Closed (twD4T2Elems.map Prod.fst)
        ((twD4T2Sig ()).map fun b => (b, twD4T2Row (twD4T2Vecs ()) b))
        (KTree.ofSorted (twD4T2Elems.map Prod.fst)) = true ∧
      (∀ e ∈ twD4T2Elems, decodeT Tag.E6.rank e.1 = List.range Tag.E6.rank ∨
        twD4T2Moves (decodeT Tag.E6.rank e.1) e.2.1 e.2.2 = true) ∧
      (∀ t ∈ twD4T2Words.map twD4T2WordTuple, twD4T2Fixes (vec3 (τ := .E6) twD4T2F0) t = true ∧
        e6ScTest e6Certificate twD4T2F0 t = true) ∧
      twD4T2PairsOK (twD4T2ZTab (twD4T2Sig ())) (twD4T2GTab (twD4T2Words.map twD4T2WordTuple)) =
        true := by
  have h := Certificates.certificate214101
  unfold twD4T2Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hreps, hrows⟩, hclosed⟩, hmoves⟩, hwords⟩, hpairs⟩ := h
  simp only [List.all_eq_true, List.forall_mem_map] at hrows
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hmoves
  simp only [List.all_eq_true, Bool.and_eq_true] at hwords
  exact ⟨hreps, hrows, hclosed, hmoves, hwords, hpairs⟩

theorem twIdx3_spec (v : Fin Tag.E6.rank → ZMod 3) :
    twIdx3 v < 3 ^ Tag.E6.rank ∧ vec3OfIndex (τ := .E6) (twIdx3 v) = v := by
  let F : Fin Tag.E6.rank → Fin 3 := fun j => ⟨(v j).val, ZMod.val_lt (v j)⟩
  have hF : twIdx3 v = (finFunctionFinEquiv F : ℕ) := by
    rw [finFunctionFinEquiv_apply]
    rfl
  refine ⟨hF ▸ (finFunctionFinEquiv F).2, ?_⟩
  funext j
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv F) j
  rw [Equiv.symm_apply_apply] at h
  simp only [vec3OfIndex]
  rw [hF, ← h]
  simp [F]

theorem twTriPairing_single (b : Fin Tag.E6.rank → ZMod 3) (j : Fin Tag.E6.rank) :
    triPairing b (Pi.single j 1) = b j := by
  have h := triPairing_zsmul_single b 1 j
  rwa [one_smul, Int.cast_one, mul_one] at h

theorem represents_twD4T2WordTuple (word : List ℕ) :
    e6Certificate.Represents (twD4T2WordTuple word)
      ((coxeterSystem Tag.E6).wordProd (toFinWord3 (τ := .E6) word)) := by
  unfold twD4T2WordTuple
  generalize toFinWord3 (τ := .E6) word = l
  induction l with
  | nil => simpa using represents_one e6Certificate_check
  | cons i l ih =>
    rw [List.foldr_cons, CoxeterSystem.wordProd_cons]
    exact represents_tupleImage e6Certificate_check ih i

theorem mem_charStabilizer_of_twD4T2Fixes {b : Fin Tag.E6.rank → ZMod 3} {t : List ℕ}
    {w : WeylGroup .E6} (hrep : e6Certificate.Represents t w) (h : twD4T2Fixes b t = true) :
    w ∈ charStabilizer (triChar b) := by
  simp only [twD4T2Fixes, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at h
  have key : charComp (triChar b) w = triChar b := lattice_hom_ext fun j => by
    rw [charComp_apply, triChar_apply, triChar_apply, ← (hrep.2 j).2, h j, twTriPairing_single]
  intro v
  have := congrArg (fun χ => χ (Multiplicative.ofAdd v)) key
  simpa only [charComp_apply] using this

theorem twTriPairing_eq_of_emod {b : Fin Tag.E6.rank → ZMod 3} {x y : Fin Tag.E6.rank → ℤ}
    (h : ∀ j, (x j - y j) % 3 = 0) : triPairing b x = triPairing b y := by
  unfold triPairing
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h3 : (((x j - y j : ℤ)) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (x j - y j) 3).2 (Int.dvd_of_emod_eq_zero (h j))
  rw [Int.cast_sub, sub_eq_zero] at h3
  exact h3

theorem twTriPairing_sub (b : Fin Tag.E6.rank → ZMod 3) (x y : Fin Tag.E6.rank → ℤ) :
    triPairing b (x - y) = triPairing b x - triPairing b y := by
  rw [eq_sub_iff_add_eq, ← triPairing_add, sub_add_cancel]

theorem twTriPairing_comb (a c : ZMod 3) (b₁ b₂ : Fin Tag.E6.rank → ZMod 3)
    (x : Fin Tag.E6.rank → ℤ) :
    triPairing (a • b₁ + c • b₂) x = a * triPairing b₁ x + c * triPairing b₂ x := by
  simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem twExists_triPairing_comp (b : Fin Tag.E6.rank → ZMod 3) (t : WeylGroup .E6) :
    ∃ b' : Fin Tag.E6.rank → ZMod 3, ∀ x, triPairing b' x = triPairing b (t • x) := by
  refine ⟨fun j => triPairing b (t • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)), fun x => ?_⟩
  have key : triChar (fun j => triPairing b (t • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) =
      charComp (triChar b) t := lattice_hom_ext fun j => by
    rw [charComp_apply, triChar_apply, triChar_apply, twTriPairing_single]
  have := congrArg (fun χ => χ (Multiplicative.ofAdd x)) key
  simp only [charComp_apply, triChar_apply] at this
  exact Z3.ofAdd_eq_ofAdd_iff.1 this

theorem twArray_getD_toArray {α : Type*} (l : List α) (k : ℕ) (d : α) :
    l.toArray.getD k d = l.getD k d := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem twD4T2ZTab_getD {sig : List ℕ} {k : ℕ} (hk : k < 3 ^ Tag.E6.rank) :
    (twD4T2ZTab sig).getD k [] = (List.range sig.length).filter fun i =>
      decide (triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root (sig.getD i 0)) = 0) := by
  unfold twD4T2ZTab
  rw [twArray_getD_toArray, getD_range_map' _ _ hk]

theorem twD4T2GTab_getD {ts : List (List ℕ)} {k : ℕ} (hk : k < 3 ^ Tag.E6.rank) :
    (twD4T2GTab ts).getD k false = ts.any (twD4T2Fixes (vec3OfIndex (τ := .E6) k)) := by
  unfold twD4T2GTab
  rw [twArray_getD_toArray, getD_range_map' _ _ hk]

theorem represents_twD4T2Img {b : ℕ} {row : List ℕ} (hrow : twD4T2RowOK b row = true)
    (hb : b < e6Certificate.roots.length) {t : List ℕ} {y : WeylGroup .E6}
    (hrep : e6Certificate.Represents t y) :
    e6Certificate.Represents (twD4T2Img row t) (rootReflection (e6Certificate.root b) * y) := by
  simp only [twD4T2RowOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hrow
  have hβ := isRoot_root e6Certificate_check b hb
  refine ⟨by rw [twD4T2Img, List.length_map, hrep.1], fun j => ?_⟩
  have hj : (j : ℕ) < t.length := by rw [hrep.1]; exact j.2
  have hget : (twD4T2Img row t).getD j 0 = row.getD (t.getD j 0) 0 := by
    rw [twD4T2Img, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj]
  obtain ⟨hlt, heq⟩ := hrow _ (hrep.2 j).1
  rw [hget, eq_of_ofFn_beq heq, mul_smul, ← (hrep.2 j).2, rootReflection_smul hβ]
  exact ⟨hlt, rfl⟩

theorem twD4T2_exists_elem {u : WeylGroup .E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) twD4T2F0))) :
    ∃ e ∈ twD4T2Elems, e6Certificate.Represents (decodeT Tag.E6.rank e.1) u := by
  obtain ⟨-, hrows, hclosed, -⟩ := twD4T2Check_spec
  simp only [twD4T2Closed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.forall_mem_map] at hclosed
  obtain ⟨⟨hid, hdec⟩, hcl⟩ := hclosed
  have hkey : ∀ {k : ℕ}, (KTree.ofSorted (twD4T2Elems.map Prod.fst)).mem k = true →
      ∃ e ∈ twD4T2Elems, e.1 = k := fun h => List.mem_map.1 (KTree.mem_of_mem_ofSorted h)
  have step : ∀ (w : WeylGroup .E6) (i : Fin Tag.E6.rank),
      w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈
        kernelRoots (triChar (vec3 (τ := .E6) twD4T2F0)) →
      ∀ y : WeylGroup .E6,
        (∃ e ∈ twD4T2Elems, e6Certificate.Represents (decodeT Tag.E6.rank e.1) y) →
        ∃ e ∈ twD4T2Elems,
          e6Certificate.Represents (decodeT Tag.E6.rank e.1) (w * simple Tag.E6 i * w⁻¹ * y) := by
    rintro w i hβ y ⟨e, he, hrep⟩
    obtain ⟨hβr, hβ0⟩ := mem_kernelRoots_triChar.1 hβ
    obtain ⟨b, hb, hbβ⟩ := exists_root_eq e6Certificate_check hβr
    have hbsig : b ∈ twD4T2Sig () := by
      unfold twD4T2Sig
      exact List.mem_filter.2 ⟨List.mem_range.2 hb, by rw [hbβ]; exact decide_eq_true hβ0⟩
    obtain ⟨hdec', hmem⟩ := hcl e he b hbsig
    obtain ⟨e', he', hk'⟩ := hkey hmem
    refine ⟨e', he', ?_⟩
    rw [hk', hdec', ← rootReflection_eq_conj (w := w) (j := i) rfl, ← hbβ]
    exact represents_twD4T2Img (hrows b hbsig) hb hrep
  unfold kernelWeylGroup at hu
  induction hu using Subgroup.closure_induction_left with
  | one =>
    obtain ⟨e, he, hk⟩ := hkey hid
    exact ⟨e, he, by rw [hk, hdec]; exact represents_one e6Certificate_check⟩
  | mul_left x hx y _ ih =>
    obtain ⟨w, i, hβ, rfl⟩ := hx
    exact step w i hβ y ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨w, i, hβ, rfl⟩ := hx
    have hβr := (mem_kernelRoots_triChar.1 hβ).1
    rw [← rootReflection_eq_conj (w := w) (j := i) rfl, rootReflection_inv hβr,
      rootReflection_eq_conj (w := w) (j := i) rfl]
    exact step w i hβ y ih

theorem twD4T2_eq_one {u : WeylGroup .E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) twD4T2F0)))
    {e₁ e₂ : Fin Tag.E6.rank → ZMod 3} (h₁ : u ∈ charStabilizer (triChar e₁))
    (h₂ : u ∈ charStabilizer (triChar e₂))
    (hE : ∀ α, IsRoot .E6 α → triPairing (vec3 (τ := .E6) twD4T2F0) α = 0 →
      triPairing e₁ α = 0 → triPairing e₂ α ≠ 0) :
    u = 1 := by
  obtain ⟨e, he, hrep⟩ := twD4T2_exists_elem hu
  obtain ⟨-, -, -, hmoves, -⟩ := twD4T2Check_spec
  rcases hmoves e he with h1 | h1
  · rw [h1] at hrep
    exact represents_unique hrep (represents_one e6Certificate_check)
  · exfalso
    simp only [twD4T2Moves, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_finRange, true_implies] at h1
    obtain ⟨hr, hmod⟩ := h1
    have hα : IsRoot .E6 (e6Certificate.root e.2.2) := isRoot_root e6Certificate_check _ hr
    have key : ∀ b : Fin Tag.E6.rank → ZMod 3, u ∈ charStabilizer (triChar b) →
        triPairing b (e6Certificate.root e.2.2) = 0 := by
      intro b hb
      have h := twTriPairing_eq_of_emod (b := b) (x := u • twD4T2Lam e.2.1 - twD4T2Lam e.2.1)
        (y := e6Certificate.root e.2.2) (fun j => by
          have := hmod j
          rw [tupleVec_eq hrep] at this
          simpa only [Pi.sub_apply] using this)
      rw [← h, twTriPairing_sub, triPairing_smul_of_mem hb, sub_self]
    exact hE _ hα (key _ (kernelWeylGroup_le hu)) (key _ h₁) (key _ h₂)

theorem twD4T2_exists_good {e₁ e₂ : Fin Tag.E6.rank → ZMod 3}
    (hE : ∀ α, IsRoot .E6 α → triPairing (vec3 (τ := .E6) twD4T2F0) α = 0 →
      triPairing e₁ α = 0 → triPairing e₂ α ≠ 0) :
    ∃ ab ∈ twD4T2Coeffs, ∃ M : WeylGroup .E6,
      M ∈ charStabilizer (triChar (vec3 (τ := .E6) twD4T2F0)) ∧
        M ∈ charStabilizer (triChar (ab.1 • e₁ + ab.2 • e₂)) ∧
        triPairing (vec3 (τ := .E6) twD4T2F0) (e6Shift M) ≠ 0 := by
  obtain ⟨-, -, -, -, hwords, hpairs⟩ := twD4T2Check_spec
  obtain ⟨k₁, hk₁, rfl⟩ := exists_vec3OfIndex (τ := .E6) e₁
  obtain ⟨k₂, hk₂, rfl⟩ := exists_vec3OfIndex (τ := .E6) e₂
  simp only [twD4T2PairsOK, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.any_eq_true] at hpairs
  rcases hpairs k₁ hk₁ k₂ hk₂ with ⟨i, hi₁, hi₂⟩ | ⟨ab, hab, hg⟩
  · exfalso
    rw [twD4T2ZTab_getD hk₁] at hi₁
    rw [twD4T2ZTab_getD hk₂, List.contains_iff_mem] at hi₂
    obtain ⟨hi, h₁⟩ := List.mem_filter.1 hi₁
    obtain ⟨-, h₂⟩ := List.mem_filter.1 hi₂
    rw [List.mem_range] at hi
    have hs : (twD4T2Sig ()).getD i 0 ∈ twD4T2Sig () := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    have hs' := hs
    unfold twD4T2Sig at hs'
    obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs'
    exact hE _ (isRoot_root e6Certificate_check _ (List.mem_range.1 hs1)) (of_decide_eq_true hs2)
      (of_decide_eq_true h₁) (of_decide_eq_true h₂)
  · refine ⟨ab, hab, ?_⟩
    obtain ⟨hidx, hvec⟩ := twIdx3_spec (ab.1 • vec3OfIndex (τ := .E6) k₁ +
      ab.2 • vec3OfIndex (τ := .E6) k₂)
    rw [twD4T2GTab_getD hidx, hvec, List.any_eq_true] at hg
    obtain ⟨t, ht, hfix⟩ := hg
    obtain ⟨hfix₀, hsc⟩ := hwords t ht
    obtain ⟨word, -, rfl⟩ := List.mem_map.1 ht
    have hrep := represents_twD4T2WordTuple word
    refine ⟨_, mem_charStabilizer_of_twD4T2Fixes hrep hfix₀,
      mem_charStabilizer_of_twD4T2Fixes hrep hfix, ?_⟩
    simp only [e6ScTest, ne_eq, decide_eq_true_eq] at hsc
    rwa [e6ShiftT_eq hrep] at hsc

theorem twNcard_kernel_eq (b : Fin Tag.E6.rank → ZMod 3) :
    {α | IsRoot .E6 α ∧ triPairing b α = 0}.ncard =
      ((List.range e6Certificate.roots.length).filter fun k =>
        decide (triPairing b (e6Certificate.root k) = 0)).length := by
  set l := (List.range e6Certificate.roots.length).filter fun k =>
    decide (triPairing b (e6Certificate.root k) = 0) with hl
  have hnd : l.Nodup := List.nodup_range.filter _
  have hset : {α | IsRoot .E6 α ∧ triPairing b α = 0} =
      e6Certificate.root '' (↑l.toFinset : Set ℕ) := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨hα, h0⟩
      obtain ⟨k, hk, rfl⟩ := exists_root_eq e6Certificate_check hα
      exact ⟨k, List.mem_filter.2 ⟨List.mem_range.2 hk, decide_eq_true h0⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
      exact ⟨isRoot_root e6Certificate_check k (List.mem_range.1 hk1), of_decide_eq_true hk2⟩
  have hinj : Set.InjOn e6Certificate.root (↑l.toFinset : Set ℕ) := by
    intro x hx y hy hxy
    have hnod := e6Certificate_checkNodup
    simp only [checkNodup, decide_eq_true_eq] at hnod
    simp only [Finset.mem_coe, List.mem_toFinset] at hx hy
    exact List.inj_on_of_nodup_map hnod (List.mem_of_mem_filter hx) (List.mem_of_mem_filter hy)
      (congrArg List.ofFn hxy)
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem twNcard_kernel_conj {f b₀ : Fin Tag.E6.rank → ZMod 3} {t : WeylGroup .E6}
    (hpair : ∀ v, triPairing f v = triPairing b₀ (t⁻¹ • v)) :
    {α | IsRoot .E6 α ∧ triPairing f α = 0}.ncard =
      {α | IsRoot .E6 α ∧ triPairing b₀ α = 0}.ncard := by
  have hset : {α | IsRoot .E6 α ∧ triPairing f α = 0} =
      (t • ·) '' {α | IsRoot .E6 α ∧ triPairing b₀ α = 0} := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hα, h0⟩
      exact ⟨t⁻¹ • α, ⟨IsRoot.smul hα t⁻¹, by rw [← hpair]; exact h0⟩, smul_inv_smul t α⟩
    · rintro ⟨β, ⟨hβ, h0⟩, rfl⟩
      exact ⟨IsRoot.smul hβ t, by rw [hpair, inv_smul_smul]; exact h0⟩
  rw [hset, Set.ncard_image_of_injective _ (MulAction.injective t)]

theorem twD4T2_rep_eq_six {ρ : ℕ}
    (hρ : ρ < e6ThreeReps.length)
    (h24 : {α | IsRoot .E6 α ∧
      triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) α = 0}.ncard = 24) :
    ρ = 6 := by
  obtain ⟨hreps, -⟩ := twD4T2Check_spec
  simp only [twD4T2RepsOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hreps
  rcases hreps ρ hρ with h | h
  · exact h
  · rw [twNcard_kernel_eq] at h24
    exact absurd h24 h

theorem twTriPairing_e6Shift_conj {f b₀ : Fin Tag.E6.rank → ZMod 3} {t : WeylGroup .E6}
    (hpair : ∀ v, triPairing f v = triPairing b₀ (t⁻¹ • v)) {M : WeylGroup .E6}
    (hM : M ∈ charStabilizer (triChar b₀)) :
    triPairing f (e6Shift (t * M * t⁻¹)) = triPairing b₀ (e6Shift M) := by
  have hinv : t⁻¹ • e6Shift t + e6Shift t⁻¹ = 0 := by
    rw [← e6Shift_mul, inv_mul_cancel, e6Shift_one]
  have h0 : triPairing b₀ (t⁻¹ • e6Shift t) + triPairing b₀ (e6Shift t⁻¹) = 0 := by
    rw [← triPairing_add, hinv, triPairing_zero]
  rw [e6Shift_mul, e6Shift_mul, triPairing_add, triPairing_add, hpair, hpair, hpair,
    inv_smul_smul, ← mul_smul, ← mul_assoc, inv_mul_cancel, one_mul, triPairing_smul_of_mem hM]
  linear_combination h0

theorem twNotMem_span {f e₁ e₂ : Fin Tag.E6.rank → ZMod 3}
    (hind : LinearIndependent (ZMod 3) ![f, e₁, e₂]) {a b : ZMod 3} (hab : ¬(a = 0 ∧ b = 0)) :
    a • e₁ + b • e₂ ∉ Submodule.span (ZMod 3) {f} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  have h0 := Fintype.linearIndependent_iffₛ.1 hind ![c, 0, 0] ![0, a, b] (by
    simp [Fin.sum_univ_three, hc])
  exact hab ⟨by simpa using (h0 1).symm, by simpa using (h0 2).symm⟩

theorem twD4T2Coeffs_ne : ∀ ab ∈ twD4T2Coeffs, ¬(ab.1 = 0 ∧ ab.2 = 0) := by
  decide

theorem twTriPairing_neg (b : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    triPairing b (-x) = -triPairing b x := by
  have h := triPairing_add b x (-x)
  rw [add_neg_cancel, triPairing_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem twMem_charStabilizer_triChar {b : Fin Tag.E6.rank → ZMod 3} {u : WeylGroup .E6} :
    u ∈ charStabilizer (triChar b) ↔ ∀ x, triPairing b (u • x) = triPairing b x := by
  rw [mem_charStabilizer]
  refine forall_congr' fun x => ?_
  rw [triChar_apply, triChar_apply]
  exact Z3.ofAdd_eq_ofAdd_iff

@[expose] def twD4T2W0Word : List (Fin TwistTag.E6.tag.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
    5, 4, 3, 2, 0] : List (Fin 6))

theorem twWordProd_smul_foldr {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem twD4T2W0_single : ∀ i : Fin TwistTag.E6.tag.rank,
    twD4T2W0Word.foldr (reflect TwistTag.E6.tag) (Pi.single i 1) =
      -Pi.single (TwistTag.E6.perm i) 1 := by
  decide +kernel

theorem twD4T2W0_smul (α : Fin TwistTag.E6.tag.rank → ℤ) :
    (coxeterSystem TwistTag.E6.tag).wordProd twD4T2W0Word • α =
      -(permLattice TwistTag.E6.perm α) := by
  have hf : ∀ i : Fin TwistTag.E6.tag.rank, ∀ c : ℤ,
      (coxeterSystem TwistTag.E6.tag).wordProd twD4T2W0Word •
          (Pi.single i c : Fin TwistTag.E6.tag.rank → ℤ) =
        -(permLattice TwistTag.E6.perm (Pi.single i c : Fin TwistTag.E6.tag.rank → ℤ)) := by
    intro i c
    have e : (Pi.single i c : Fin TwistTag.E6.tag.rank → ℤ) = c • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    have e' : permLattice TwistTag.E6.perm (c • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) =
        c • Pi.single (TwistTag.E6.perm i) 1 := by
      ext j
      simp [permLattice, Pi.single_apply, Equiv.symm_apply_eq]
    rw [e, smul_comm, twWordProd_smul_foldr, twD4T2W0_single, e', smul_neg]
  conv_lhs => rw [← Finset.univ_sum_single α]
  rw [Finset.smul_sum]
  simp only [hf, Finset.sum_neg_distrib]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single α]
  ext j
  simp [permLattice, Finset.sum_apply]

theorem twD4T2W0_exists : ∃ w₀ : WeylGroup .E6, ∀ x : Fin Tag.E6.rank → ℤ,
    w₀ • x = -(permLattice (τ := .E6) TwistTag.E6.perm x) :=
  ⟨_, twD4T2W0_smul⟩

theorem twD4T2_core
    {f e₁ e₂ : Fin Tag.E6.rank → ZMod 3} (hli : LinearIndependent (ZMod 3) ![f, e₁, e₂])
    {u : WeylGroup .E6} (hf : u ∈ charStabilizer (triChar f))
    (h₁ : u ∈ charStabilizer (triChar e₁)) (h₂ : u ∈ charStabilizer (triChar e₂))
    (h24 : {α | IsRoot .E6 α ∧ triPairing f α = 0}.ncard = 24)
    (hSE : ∀ α, IsRoot .E6 α → triPairing f α = 0 → triPairing e₁ α = 0 →
      triPairing e₂ α ≠ 0) :
    ∃ e ∈ Submodule.span (ZMod 3) {f, e₁, e₂}, e ∉ Submodule.span (ZMod 3) {f} ∧
      ∃ M : WeylGroup .E6, M ∈ charStabilizer (triChar f) ∧ M ∈ charStabilizer (triChar e) ∧
        triPairing f (e6Shift M) ≠ 0 ∧ M * u = u * M := by
  have hmem : ∀ {g : Fin Tag.E6.rank → ZMod 3}, g ∈ ({f, e₁, e₂} : Set _) →
      g ∈ Submodule.span (ZMod 3) {f, e₁, e₂} := fun h => Submodule.subset_span h
  by_cases hs : triPairing f (e6Shift u) = 0
  swap
  · refine ⟨e₁, hmem (by simp), ?_, u, hf, h₁, hs, rfl⟩
    have h := twNotMem_span hli (a := 1) (b := 0) (by simp)
    rwa [one_smul, zero_smul, add_zero] at h
  have hk := e6Shift_mem_kernelWeylGroup f hf hs
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 e6ThreeScCheck_spec.1 (triChar f)
  have hpair : ∀ v, triPairing f v =
      triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (t⁻¹ • v) := fun v => by
    have h := ht v
    rw [triChar_apply, triChar_apply] at h
    exact Z3.ofAdd_eq_ofAdd_iff.1 h
  obtain rfl : ρ = 6 := twD4T2_rep_eq_six hρ (by rw [← twNcard_kernel_conj hpair]; exact h24)
  have hrep : e6ThreeReps.getD 6 [] = twD4T2F0 := rfl
  rw [hrep] at ht hpair
  have hk' : t⁻¹ * u * t ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) twD4T2F0)) := by
    rw [kernelWeylGroup_eq_map ht, Subgroup.mem_map] at hk
    obtain ⟨y, hy, hyu⟩ := hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyu
    rw [← hyu]
    simpa [mul_assoc] using hy
  obtain ⟨e₁', he₁'⟩ := twExists_triPairing_comp e₁ t
  obtain ⟨e₂', he₂'⟩ := twExists_triPairing_comp e₂ t
  have hconj : ∀ {b b' : Fin Tag.E6.rank → ZMod 3},
      (∀ x, triPairing b' x = triPairing b (t • x)) →
      u ∈ charStabilizer (triChar b) → t⁻¹ * u * t ∈ charStabilizer (triChar b') := by
    intro b b' hb' hu
    rw [twMem_charStabilizer_triChar] at hu ⊢
    intro x
    rw [hb', hb', mul_smul, mul_smul, smul_inv_smul, hu]
  have hE' : ∀ α, IsRoot .E6 α → triPairing (vec3 (τ := .E6) twD4T2F0) α = 0 →
      triPairing e₁' α = 0 → triPairing e₂' α ≠ 0 := by
    intro α hα h0 h1
    rw [he₂']
    rw [he₁'] at h1
    refine hSE _ (IsRoot.smul hα t) ?_ h1
    rw [hpair, inv_smul_smul]
    exact h0
  have hu1 := twD4T2_eq_one hk' (hconj he₁' h₁) (hconj he₂' h₂) hE'
  have hu : u = 1 := by
    calc u = t * (t⁻¹ * u * t) * t⁻¹ := by group
      _ = 1 := by rw [hu1, mul_one, mul_inv_cancel]
  obtain ⟨ab, hab, M', hM'f, hM'e, hM's⟩ := twD4T2_exists_good hE'
  refine ⟨ab.1 • e₁ + ab.2 • e₂, Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem (by simp)))
    (Submodule.smul_mem _ _ (hmem (by simp))), twNotMem_span hli (twD4T2Coeffs_ne ab hab),
    t * M' * t⁻¹, ?_, ?_, ?_, by rw [hu, mul_one, one_mul]⟩
  · rw [twMem_charStabilizer_triChar] at hM'f ⊢
    intro x
    rw [hpair, hpair, mul_smul, mul_smul, inv_smul_smul, hM'f]
  · rw [twMem_charStabilizer_triChar] at hM'e ⊢
    intro x
    have hy := hM'e (t⁻¹ • x)
    rw [twTriPairing_comb, twTriPairing_comb, he₁', he₂', he₁', he₂', smul_inv_smul] at hy
    rw [twTriPairing_comb, twTriPairing_comb, mul_smul, mul_smul]
    exact hy
  · rw [twTriPairing_e6Shift_conj hpair hM'f]
    exact hM's

theorem d4t2_alpha_lattice
    (w : WeylGroup .E6) (f e₁ e₂ : Fin Tag.E6.rank → ZMod 3)
    (hli : LinearIndependent (ZMod 3) ![f, e₁, e₂])
    (hv : ∀ b ∈ ({f, e₁, e₂} : Set (Fin Tag.E6.rank → ZMod 3)), ∀ x : Fin Tag.E6.rank → ℤ,
      triPairing b (w • permLattice (τ := .E6) TwistTag.E6.perm x) = - triPairing b x)
    (h24 : (kernelRoots (triChar f)).ncard = 24)
    (hSE : ∀ α, IsRoot .E6 α → triPairing f α = 0 → triPairing e₁ α = 0 →
      triPairing e₂ α ≠ 0) :
    ∃ e ∈ Submodule.span (ZMod 3) {f, e₁, e₂}, e ∉ Submodule.span (ZMod 3) {f} ∧
      ∃ M : WeylGroup .E6, M ∈ charStabilizer (triChar f) ∧ M ∈ charStabilizer (triChar e) ∧
        triPairing f (e6Shift M) ≠ 0 ∧
        ∀ x : Fin Tag.E6.rank → ℤ,
          M • (w • permLattice (τ := .E6) TwistTag.E6.perm x) =
            w • permLattice (τ := .E6) TwistTag.E6.perm (M • x) := by
  obtain ⟨w₀, hw₀⟩ := twD4T2W0_exists
  have hperm : ∀ x : Fin Tag.E6.rank → ℤ,
      w • permLattice (τ := .E6) TwistTag.E6.perm x = -((w * w₀) • x) := fun x => by
    rw [mul_smul, hw₀, smul_neg, neg_neg]
  have hst : ∀ b ∈ ({f, e₁, e₂} : Set (Fin Tag.E6.rank → ZMod 3)),
      w * w₀ ∈ charStabilizer (triChar b) := fun b hb =>
    twMem_charStabilizer_triChar.2 fun x => by
      have h := hv b hb x
      rw [hperm, twTriPairing_neg] at h
      exact neg_inj.1 h
  have hk : kernelRoots (triChar f) = {α | IsRoot .E6 α ∧ triPairing f α = 0} :=
    Set.ext fun _ => mem_kernelRoots_triChar
  obtain ⟨e, he, hne, M, hMf, hMe, hMs, hcomm⟩ := twD4T2_core hli (hst f (by simp))
    (hst e₁ (by simp)) (hst e₂ (by simp)) (by rw [← hk]; exact h24) hSE
  refine ⟨e, he, hne, M, hMf, hMe, hMs, fun x => ?_⟩
  rw [hperm, hperm, smul_neg, ← mul_smul, ← mul_smul, hcomm]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
