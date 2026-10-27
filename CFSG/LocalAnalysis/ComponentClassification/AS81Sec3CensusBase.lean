
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs

public section

namespace CFSG.ComponentClassification.AS81.Census

open CFSG.Fischer CFSG.PSL3Four.Native QuadraticMap CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

abbrev V₀ : Type := Fin 6 → F4

instance : Finite (V₀ ≃ₗ[F4] V₀) :=
  Finite.of_injective (fun e : V₀ ≃ₗ[F4] V₀ => (e : V₀ → V₀)) DFunLike.coe_injective

theorem F4_eq_of_val {x y : F4} (h : x.code.val = y.code.val) : x = y := by
  cases x
  cases y
  simp only [F4.mk.injEq]
  exact Fin.ext h

theorem encodeV_lt (v : V₀) : encodeV v < 4096 := by
  have h0 := (v 0).code.isLt
  have h1 := (v 1).code.isLt
  have h2 := (v 2).code.isLt
  have h3 := (v 3).code.isLt
  have h4 := (v 4).code.isLt
  have h5 := (v 5).code.isLt
  unfold encodeV
  omega

theorem decodeV_encodeV (v : V₀) : decodeV (encodeV v) = v := by
  have h0 := (v 0).code.isLt
  have h1 := (v 1).code.isLt
  have h2 := (v 2).code.isLt
  have h3 := (v 3).code.isLt
  have h4 := (v 4).code.isLt
  have h5 := (v 5).code.isLt
  funext i
  apply F4_eq_of_val
  simp only [decodeV]
  fin_cases i <;> simp only [encodeV, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    pow_zero, pow_one, Nat.reducePow] <;> omega

theorem encodeV_decodeV {n : ℕ} (hn : n < 4096) : encodeV (decodeV n) = n := by
  simp only [encodeV, decodeV, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, Nat.reducePow, Nat.div_one]
  have e3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have e5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [e3, e4, e5, Nat.reducePow]
  omega

theorem encodeV_injective : Function.Injective encodeV := fun v w h => by
  rw [← decodeV_encodeV v, ← decodeV_encodeV w, h]

@[expose] noncomputable def toLin (M : Array ℕ) : V₀ →ₗ[F4] V₀ where
  toFun := applyF M
  map_add' v w := by
    funext i
    simp only [applyF, Pi.add_apply]
    ring
  map_smul' c v := by
    funext i
    simp only [applyF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem toLin_apply (M : Array ℕ) (v : V₀) : toLin M v = applyF M v := rfl

theorem applyC_encodeV (M : Array ℕ) (v : V₀) : applyC M (encodeV v) = encodeV (toLin M v) := by
  rw [applyC, decodeV_encodeV, toLin_apply]

theorem toLin_single (M : Array ℕ) (i : Fin 6) : toLin M (Pi.single i 1) = decodeV M[i.val]! := by
  funext j
  fin_cases i <;> simp [toLin_apply, applyF]

theorem linMap_ext {f g : V₀ →ₗ[F4] V₀} (h : ∀ i : Fin 6, f (Pi.single i 1) = g (Pi.single i 1)) :
    f = g :=
  LinearMap.pi_ext' fun i => LinearMap.ext_ring (by simpa using h i)

theorem matMul_getElem (A B : Array ℕ) (i : Fin 6) : (matMul A B)[i.val]! = applyC A B[i.val]! := by
  rw [matMul, getElem!_pos _ _ (by simp), Array.getElem_ofFn]
  rfl

theorem toLin_matMul (A B : Array ℕ) : toLin (matMul A B) = toLin A ∘ₗ toLin B := by
  refine linMap_ext fun i => ?_
  rw [toLin_single, LinearMap.comp_apply, toLin_single, matMul_getElem, applyC, decodeV_encodeV,
    toLin_apply]

theorem toLin_idMat : toLin idMat = LinearMap.id := by
  refine linMap_ext fun i => ?_
  rw [toLin_single, LinearMap.id_apply]
  fin_cases i <;> decide

@[expose] noncomputable def B₀ : LinearMap.BilinForm F4 V₀ :=
  LinearMap.mk₂ F4
    (fun v w => v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2 + v 4 * w 5 + v 5 * w 4)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem B₀_apply (v w : V₀) :
    B₀ v w = v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2 + v 4 * w 5 + v 5 * w 4 := rfl

theorem qF_add (v w : V₀) : qF (v + w) = qF v + qF w + B₀ v w := by
  simp only [qF, B₀_apply, Pi.add_apply]
  linear_combination (v 0 * w 0 + v 1 * w 1 + v 4 * w 4 + v 5 * w 5) * F4.two_eq_zero

@[expose] noncomputable def Q₀ : QuadraticForm F4 V₀ where
  toFun := qF
  toFun_smul c v := by
    simp only [qF, Pi.smul_apply, smul_eq_mul]
    ring
  exists_companion' := ⟨B₀, qF_add⟩

theorem Q₀_apply (v : V₀) : Q₀ v = qF v := rfl

theorem polar_Q₀ (v w : V₀) : polar Q₀ v w = B₀ v w := by
  rw [polar, Q₀_apply, Q₀_apply, Q₀_apply, qF_add]
  ring

theorem Q₀_nondegenerate : (polarBilin Q₀).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
  have h : ∀ j : Fin 6, B₀ v (Pi.single j 1) = 0 := fun j => by
    rw [← polar_Q₀]
    exact hv _
  funext i
  fin_cases i
  · simpa [B₀_apply, Pi.single_apply] using h 1
  · simpa [B₀_apply, Pi.single_apply] using h 0
  · simpa [B₀_apply, Pi.single_apply] using h 3
  · simpa [B₀_apply, Pi.single_apply] using h 2
  · simpa [B₀_apply, Pi.single_apply] using h 5
  · simpa [B₀_apply, Pi.single_apply] using h 4

@[expose] noncomputable def tsMap : (Fin 3 → F4) →ₗ[F4] V₀ where
  toFun a := ![F4.ω * a 0, a 0, a 1, 0, F4.ω * a 2, a 2]
  map_add' a b := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c a := by
    funext i
    fin_cases i <;> simp <;> ring

theorem tsMap_injective : Function.Injective tsMap := by
  intro a b h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h5 := congrFun h 5
  simp [tsMap] at h1 h2 h5
  funext i
  fin_cases i
  · exact h1
  · exact h2
  · exact h5

theorem Q₀_isPlusType : CFSG.GroupTheory.WeirSylow.IsPlusType Q₀ := by
  refine ⟨LinearMap.range tsMap, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj tsMap_injective, Module.finrank_fin_fun,
      Module.finrank_fin_fun]
  · rintro _ ⟨a, rfl⟩
    have hω : F4.ω * F4.ω + F4.ω + 1 = 0 := by decide
    rw [Q₀_apply]
    simp only [tsMap, LinearMap.coe_mk, AddHom.coe_mk, qF]
    simp
    linear_combination (a 0 * a 0 + a 2 * a 2) * hω

theorem card_O : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₀) = 1974067200 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := F4)
    Q₀_nondegenerate (m := 2) (by rw [Module.finrank_fin_fun]) (ε := 1)
    (Or.inl ⟨rfl, Q₀_isPlusType⟩)
  have hK : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  have hprod : ∏ i ∈ Finset.Icc 1 2, (((Nat.card F4 : ℤ) ^ 2) ^ i - 1) = 3825 := by
    rw [hK]
    decide
  rw [hprod, hK] at h
  have h' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₀) : ℤ) = 1974067200 := by
    rw [h]
    norm_num
  exact_mod_cast h'

theorem toLin_injective {M : Array ℕ} (h : isomOK M = true) : Function.Injective (toLin M) := by
  simp only [isomOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨-, hM⟩ := h
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rcases (hM (encodeV v) (encodeV_lt v)).2 with h0 | h0
  · rw [← decodeV_encodeV v, h0]
    funext i
    fin_cases i <;> decide
  · exfalso
    apply h0
    rw [applyC_encodeV, hv]
    rfl

theorem toLin_isometry {M : Array ℕ} (h : isomOK M = true) (v : V₀) : Q₀ (toLin M v) = Q₀ v := by
  simp only [isomOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨-, hM⟩ := h
  have := (hM (encodeV v) (encodeV_lt v)).1
  rw [decodeV_encodeV] at this
  exact this

@[expose] noncomputable def ofArr (M : Array ℕ) (h : isomOK M = true) :
    TauCeti.QuadraticMap.orthogonalGroup Q₀ :=
  ⟨LinearEquiv.ofInjectiveEndo (toLin M) (toLin_injective h),
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => toLin_isometry h v⟩

theorem ofArr_apply {M : Array ℕ} (h : isomOK M = true) (v : V₀) :
    ((ofArr M h : TauCeti.QuadraticMap.orthogonalGroup Q₀) : V₀ ≃ₗ[F4] V₀) v = toLin M v := rfl

theorem ofArr_mul {A B C : Array ℕ} (hA : isomOK A = true) (hB : isomOK B = true)
    (hC : isomOK C = true) (h : matMul A B = C) : ofArr A hA * ofArr B hB = ofArr C hC := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change toLin A (toLin B v) = toLin C v
  rw [← h, toLin_matMul, LinearMap.comp_apply]

theorem ofArr_eq_one {A : Array ℕ} (hA : isomOK A = true) (h : A = idMat) : ofArr A hA = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change toLin A v = v
  rw [h, toLin_idMat, LinearMap.id_apply]

@[expose] def N0 : Set V₀ := {v | ∀ i, (v i).code.val < 2}

@[expose] def Rep (t : Tab) (φ : Set V₀) : Prop :=
  t.toList.Pairwise (· < ·) ∧ ∀ n, n ∈ t.toList ↔ ∃ v ∈ φ, encodeV v = n

theorem Rep.lt_of_mem {t : Tab} {φ : Set V₀} (h : Rep t φ) {n : ℕ} (hn : n ∈ t.toList) :
    n < 4096 := by
  obtain ⟨v, -, rfl⟩ := (h.2 n).mp hn
  exact encodeV_lt v

theorem Rep.tab_eq {t t' : Tab} {φ : Set V₀} (h : Rep t φ) (h' : Rep t' φ) : t = t' :=
  Array.toList_inj.mp (List.Pairwise.eq_of_mem_iff h.1 h'.1 fun n => by rw [h.2, h'.2])

theorem Rep.set_eq {t : Tab} {φ ψ : Set V₀} (h : Rep t φ) (h' : Rep t ψ) : φ = ψ := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := (h'.2 _).mp ((h.2 _).mpr ⟨v, hv, rfl⟩)
    rwa [encodeV_injective hwv] at hw
  · intro hv
    obtain ⟨w, hw, hwv⟩ := (h.2 _).mp ((h'.2 _).mpr ⟨v, hv, rfl⟩)
    rwa [encodeV_injective hwv] at hw

theorem rep_of_mergeSort {l : List ℕ} {φ : Set V₀} (hl : l.Nodup)
    (hmem : ∀ n, n ∈ l ↔ ∃ v ∈ φ, encodeV v = n) :
    Rep (l.mergeSort (· ≤ ·)).toArray φ := by
  have hperm := List.mergeSort_perm l (· ≤ ·)
  have hsort := List.pairwise_mergeSort' (· ≤ · : ℕ → ℕ → Prop) l
  have hnd : (l.mergeSort (· ≤ ·)).Nodup := hperm.nodup_iff.mpr hl
  refine ⟨?_, fun n => ?_⟩
  · rw [List.toList_toArray]
    refine (hsort.and hnd).imp ?_
    intro a b ⟨hab, hne⟩
    omega
  · rw [List.toList_toArray, hperm.mem_iff, hmem]

theorem rep_formStep {t : Tab} {φ : Set V₀} (h : Rep t φ) {M : Array ℕ}
    (hM : Function.Injective (toLin M)) : Rep (formStep M t) (toLin M '' φ) := by
  unfold Census.formStep
  refine rep_of_mergeSort ?_ fun n => ?_
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (h.1.imp ne_of_lt)
    obtain ⟨v, -, rfl⟩ := (h.2 x).mp hx
    obtain ⟨w, -, rfl⟩ := (h.2 y).mp hy
    rw [applyC_encodeV, applyC_encodeV] at hxy
    rw [hM (encodeV_injective hxy)]
  · rw [List.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (h.2 m).mp hm
      exact ⟨toLin M v, ⟨v, hv, rfl⟩, (applyC_encodeV M v).symm⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨encodeV v, (h.2 _).mpr ⟨v, hv, rfl⟩, applyC_encodeV M v⟩

theorem formStepT_actTab {t : Tab} {φ : Set V₀} (h : Rep t φ) (M : Array ℕ) :
    formStepT (actTab M) t = formStep M t := by
  unfold Census.formStepT Census.formStep
  have e : t.toList.map (fun n => (actTab M)[n]!) = t.toList.map (applyC M) :=
    List.map_congr_left fun n hn => by
      have hn' := h.lt_of_mem hn
      rw [actTab, getElem!_pos _ _ (by simpa using hn'), Array.getElem_ofFn]
  rw [e]

@[expose] def bitsV (b : ℕ) : V₀ := fun i =>
  ⟨⟨b / 2 ^ i.val % 2, lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)⟩⟩

theorem bitsV_mem (b : ℕ) : bitsV b ∈ N0 := fun _ => Nat.mod_lt _ (by norm_num)

@[expose] def idx (v : V₀) : ℕ :=
  (v 0).code.val + 2 * ((v 1).code.val + 2 * ((v 2).code.val + 2 * ((v 3).code.val +
    2 * ((v 4).code.val + 2 * (v 5).code.val))))

theorem idx_lt {v : V₀} (hv : v ∈ N0) : idx v < 64 := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  unfold idx
  omega

theorem bitsV_idx {v : V₀} (hv : v ∈ N0) : bitsV (idx v) = v := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  funext i
  apply F4_eq_of_val
  simp only [bitsV]
  fin_cases i <;> simp only [idx, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    pow_zero, pow_one, Nat.reducePow, Nat.div_one] <;> omega

theorem idx_bitsV {b : ℕ} (hb : b < 64) : idx (bitsV b) = b := by
  simp only [idx, bitsV, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    Nat.div_one]
  have e3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have e5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [e3, e4, e5, Nat.reducePow]
  omega

theorem encodeV_bitsV (b : ℕ) : encodeV (bitsV b) = f2code b := by
  simp only [encodeV, bitsV, f2code, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, Nat.div_one]
  rfl

theorem f2point_encodeV {v : V₀} (hv : v ∈ N0) : f2point (encodeV v) = idx v := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  simp only [f2point, encodeV, idx]
  generalize (v 0).code.val = a0 at h0 ⊢
  generalize (v 1).code.val = a1 at h1 ⊢
  generalize (v 2).code.val = a2 at h2 ⊢
  generalize (v 3).code.val = a3 at h3 ⊢
  generalize (v 4).code.val = a4 at h4 ⊢
  generalize (v 5).code.val = a5 at h5 ⊢
  generalize hn : a0 + 4 * (a1 + 4 * (a2 + 4 * (a3 + 4 * (a4 + 4 * a5)))) = n
  have e0 : n % 4 = a0 := by omega
  have e1 : n / 4 % 4 = a1 := by omega
  have e2 : n / 16 % 4 = a2 := by omega
  have e3 : n / 64 % 4 = a3 := by omega
  have e4 : n / 256 % 4 = a4 := by omega
  have e5 : n / 1024 % 4 = a5 := by omega
  rw [e0, e1, e2, e3, e4, e5]

theorem rep_n0 : Rep n0Tab N0 := by
  unfold Census.n0Tab
  refine rep_of_mergeSort ?_ fun n => ?_
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    rw [List.mem_range] at hx hy
    rw [← encodeV_bitsV, ← encodeV_bitsV] at hxy
    have := congrArg idx (encodeV_injective hxy)
    rwa [idx_bitsV hx, idx_bitsV hy] at this
  · rw [List.mem_map]
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨bitsV b, bitsV_mem b, encodeV_bitsV b⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨idx v, List.mem_range.mpr (idx_lt hv), ?_⟩
      rw [← encodeV_bitsV, bitsV_idx hv]

theorem toLin_mem_N0 {M : Array ℕ} (hM : f2Mat M = true) {v : V₀} (hv : v ∈ N0) :
    toLin M v ∈ N0 := by
  simp only [f2Mat, isF2, allBelow_eq_true, decide_eq_true_eq] at hM
  have hF : ∀ k : Fin 6, ∀ i : Fin 6, (decodeV M[k.val]! i).code.val < 2 := fun k i =>
    hM k k.isLt i i.isLt
  have hadd : ∀ a b : F4, a.code.val < 2 → b.code.val < 2 → (a + b).code.val < 2 := by decide
  have hmul : ∀ a b : F4, a.code.val < 2 → b.code.val < 2 → (a * b).code.val < 2 := by decide
  intro i
  rw [toLin_apply, applyF]
  refine hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hmul _ _ (hv 0) (hF 0 i))
    (hmul _ _ (hv 1) (hF 1 i))) (hmul _ _ (hv 2) (hF 2 i))) (hmul _ _ (hv 3) (hF 3 i)))
    (hmul _ _ (hv 4) (hF 4 i))) (hmul _ _ (hv 5) (hF 5 i))

theorem tree_rep {step : ℕ → Tab → Tab} {k : ℕ} {root : Tab} {E : Enum}
    (h : treeOK step k root E = true) {f : ℕ → Set V₀ → Set V₀}
    (hf : ∀ j < k, ∀ t φ, Rep t φ → Rep (step j t) (f j φ)) {φ₀ : Set V₀} (hroot : Rep root φ₀)
    (P : Set V₀ → Prop) (hP₀ : P φ₀) (hP : ∀ j < k, ∀ φ, P φ → P (f j φ)) :
    ∀ i < E.tabs.size, ∃ φ, P φ ∧ Rep E.tabs[i]! φ := by
  obtain ⟨-, h0, -, -, htree⟩ := treeOK_spec h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨φ₀, hP₀, h0 ▸ hroot⟩
    · obtain ⟨hpar, hlab, he⟩ := htree i hi hi0
      obtain ⟨φ, hφ, hrep⟩ := ih _ hpar (hpar.trans hi)
      exact ⟨f _ φ, hP _ hlab φ hφ, he ▸ hf _ hlab _ _ hrep⟩

section Facts

abbrev OV : Type := TauCeti.QuadraticMap.orthogonalGroup Q₀

@[expose] noncomputable def Stab : Subgroup OV := MulAction.stabilizer OV N0

theorem smul_N0_eq (g : OV) (φ : Set V₀) :
    g • φ = (fun v => (g : V₀ ≃ₗ[F4] V₀) v) '' φ := by
  ext v
  simp only [Set.mem_smul_set, Set.mem_image]
  rfl

theorem ofArr_smul {M : Array ℕ} (h : isomOK M = true) (φ : Set V₀) :
    ofArr M h • φ = toLin M '' φ := by
  rw [smul_N0_eq]
  rfl

theorem rep_smul {t : Tab} {φ : Set V₀} (ht : Rep t φ) {M : Array ℕ} (h : isomOK M = true) :
    Rep (formStep M t) (ofArr M h • φ) := by
  rw [ofArr_smul]
  exact rep_formStep ht (toLin_injective h)

theorem N0_finite : N0.Finite := Set.toFinite N0

theorem mem_stab_of_f2 {M : Array ℕ} (h : isomOK M = true) (hM : f2Mat M = true) :
    ofArr M h ∈ MulAction.stabilizer OV N0 := by
  rw [MulAction.mem_stabilizer_iff, ofArr_smul]
  have hsub : toLin M '' N0 ⊆ N0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact toLin_mem_N0 hM hv
  refine Set.eq_of_subset_of_ncard_le hsub ?_ N0_finite
  rw [Set.ncard_image_of_injective _ (toLin_injective h)]

theorem apply_mem_N0 {g : OV} (hg : g ∈ MulAction.stabilizer OV N0) {v : V₀} (hv : v ∈ N0) :
    (g : V₀ ≃ₗ[F4] V₀) v ∈ N0 := by
  have h : g • N0 = N0 := hg
  rw [← h, smul_N0_eq]
  exact ⟨v, hv, rfl⟩

@[expose] noncomputable def sigmaFun (g : MulAction.stabilizer OV N0) (b : Fin 64) : Fin 64 :=
  ⟨idx (((g : OV) : V₀ ≃ₗ[F4] V₀) (bitsV b)), idx_lt (apply_mem_N0 g.2 (bitsV_mem b))⟩

theorem bitsV_sigmaFun (g : MulAction.stabilizer OV N0) (b : Fin 64) :
    bitsV (sigmaFun g b) = ((g : OV) : V₀ ≃ₗ[F4] V₀) (bitsV b) :=
  bitsV_idx (apply_mem_N0 g.2 (bitsV_mem b))

theorem sigmaFun_mul (g h : MulAction.stabilizer OV N0) (b : Fin 64) :
    sigmaFun (g * h) b = sigmaFun g (sigmaFun h b) := by
  apply Fin.ext
  change idx (((g : OV) : V₀ ≃ₗ[F4] V₀) (((h : OV) : V₀ ≃ₗ[F4] V₀) (bitsV b))) =
    idx (((g : OV) : V₀ ≃ₗ[F4] V₀) (bitsV (sigmaFun h b)))
  rw [bitsV_sigmaFun]

theorem sigmaFun_one (b : Fin 64) : sigmaFun 1 b = b :=
  Fin.ext (idx_bitsV b.isLt)

@[expose] noncomputable def sigma : MulAction.stabilizer OV N0 →* Equiv.Perm (Fin 64) where
  toFun g := ⟨sigmaFun g, sigmaFun g⁻¹, fun b => by rw [← sigmaFun_mul, inv_mul_cancel,
    sigmaFun_one], fun b => by rw [← sigmaFun_mul, mul_inv_cancel, sigmaFun_one]⟩
  map_one' := Equiv.ext sigmaFun_one
  map_mul' g h := Equiv.ext fun b => sigmaFun_mul g h b

theorem tabRep_f2perm {M : Array ℕ} (h : isomOK M = true) (hM : f2Mat M = true) :
    TabRep (f2perm M) (sigma ⟨ofArr M h, mem_stab_of_f2 h hM⟩) := by
  refine ⟨by simp [f2perm], fun b => ?_⟩
  rw [f2perm, getElem!_pos _ _ (by simp), Array.getElem_ofFn]
  change f2point (applyC M (f2code b.val)) = idx (toLin M (bitsV b))
  rw [← encodeV_bitsV, applyC_encodeV, f2point_encodeV (toLin_mem_N0 hM (bitsV_mem b))]

theorem foldl_range_sum (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun s j => s + f j) 0 = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

abbrev Pos : Type := Σ j : Fin 20, Fin (orbits[j.val]!).tabs.size

theorem card_orbit_mul :
    Nat.card (MulAction.orbit OV N0) * Nat.card (MulAction.stabilizer OV N0) = 1974067200 := by
  rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup OV N0), card_O]

theorem ofArr_mul_eq_one {A B : Array ℕ} (hA : isomOK A = true) (hB : isomOK B = true)
    (h : matMul A B = idMat) : ofArr A hA * ofArr B hB = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change toLin A (toLin B v) = v
  rw [← LinearMap.comp_apply, ← toLin_matMul, h, toLin_idMat, LinearMap.id_apply]

theorem ofArr_comm {A B : Array ℕ} (hA : isomOK A = true) (hB : isomOK B = true)
    (h : matMul A B = matMul B A) : ofArr A hA * ofArr B hB = ofArr B hB * ofArr A hA := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change toLin A (toLin B v) = toLin B (toLin A v)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← toLin_matMul, ← toLin_matMul, h]

theorem ofArr_mul_eq_mul {A B C D : Array ℕ} (hA : isomOK A = true) (hB : isomOK B = true)
    (hC : isomOK C = true) (hD : isomOK D = true) (h : matMul A B = matMul C D) :
    ofArr A hA * ofArr B hB = ofArr C hC * ofArr D hD := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change toLin A (toLin B v) = toLin C (toLin D v)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← toLin_matMul, ← toLin_matMul, h]

theorem foldl_mul_apply (a : ℕ → OV) (Ms : Array (Array ℕ))
    (ha : ∀ x < 4, ∀ v, ((a x : OV) : V₀ ≃ₗ[F4] V₀) v = toLin Ms[x]! v) :
    ∀ (w : List ℕ), (∀ x ∈ w, x < 4) → ∀ (r : OV) (R : Array ℕ),
      (∀ v, (r : V₀ ≃ₗ[F4] V₀) v = toLin R v) →
      ∀ v, ((w.foldl (fun r x => r * a x) r : OV) : V₀ ≃ₗ[F4] V₀) v =
        toLin (w.foldl (fun r x => matMul r Ms[x]!) R) v
  | [], _, r, R, hr, v => hr v
  | x :: w, hw, r, R, hr, v => by
    simp only [List.foldl_cons]
    refine foldl_mul_apply a Ms ha w (fun y hy => hw y (List.mem_cons_of_mem x hy)) _ _
      (fun v => ?_) v
    rw [toLin_matMul, LinearMap.comp_apply, ← ha x (hw x List.mem_cons_self), ← hr]
    rfl

theorem foldl_mul_mem {H : Subgroup OV} (a : ℕ → OV) (ha : ∀ x < 4, a x ∈ H) :
    ∀ (w : List ℕ), (∀ x ∈ w, x < 4) → ∀ r ∈ H, w.foldl (fun r x => r * a x) r ∈ H
  | [], _, _, hr => hr
  | x :: w, hw, r, hr => by
    simp only [List.foldl_cons]
    exact foldl_mul_mem a ha w (fun y hy => hw y (List.mem_cons_of_mem x hy)) _
      (mul_mem hr (ha x (hw x List.mem_cons_self)))

end Facts

end CFSG.ComponentClassification.AS81.Census
