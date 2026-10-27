module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Norton

public section

namespace CFSG.QuasithinUnique.Setup.X3E

open Finset

@[expose] def Fl (N n : ℕ) : Submodule (ZMod 2) (Vec N) where
  carrier := {v | ∀ k : Fin N, n ≤ k.val → v k = 0}
  add_mem' := by
    intro u v hu hv k hk
    simp [hu k hk, hv k hk]
  zero_mem' := by intro k _; rfl
  smul_mem' := by
    intro c v hv k hk
    simp [hv k hk]

theorem Fl_zero (N : ℕ) : Fl N 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext k
  exact hv k (Nat.zero_le _)

theorem Fl_self (N : ℕ) : Fl N N = ⊤ := by
  rw [eq_top_iff]
  intro v _ k hk
  exact absurd k.isLt (by omega)

@[expose] noncomputable def resL (N n0 d : ℕ) : Vec N →ₗ[ZMod 2] Vec d where
  toFun v := fun k => if h : n0 + k.val < N then v ⟨n0 + k.val, h⟩ else 0
  map_add' u v := by funext k; by_cases h : n0 + k.val < N <;> simp [h]
  map_smul' c v := by funext k; by_cases h : n0 + k.val < N <;> simp [h]

@[expose] noncomputable def embL (N n0 d : ℕ) : Vec d →ₗ[ZMod 2] Vec N where
  toFun s := fun j => if h : n0 ≤ j.val ∧ j.val - n0 < d then s ⟨j.val - n0, h.2⟩ else 0
  map_add' u v := by funext j; by_cases h : n0 ≤ j.val ∧ j.val - n0 < d <;> simp [h]
  map_smul' c v := by funext j; by_cases h : n0 ≤ j.val ∧ j.val - n0 < d <;> simp [h]

theorem resL_embL {N n0 d : ℕ} (h : n0 + d ≤ N) (s : Vec d) : resL N n0 d (embL N n0 d s) = s := by
  funext k
  have h1 : n0 + k.val < N := by omega
  have h2 : n0 ≤ n0 + k.val ∧ n0 + k.val - n0 < d := ⟨by omega, by omega⟩
  show (if h : n0 + k.val < N then
      (if h' : n0 ≤ (n0 + k.val) ∧ (n0 + k.val) - n0 < d then s ⟨(n0 + k.val) - n0, h'.2⟩ else 0)
      else 0) = s k
  simp only [h1, h2, ↓reduceDIte]
  exact Fin.ext (by simp)

theorem embL_mem {N n0 d : ℕ} (s : Vec d) : embL N n0 d s ∈ Fl N (n0 + d) := by
  intro k hk
  have h2 : ¬ (n0 ≤ k.val ∧ k.val - n0 < d) := by omega
  show (if h : n0 ≤ k.val ∧ k.val - n0 < d then s ⟨k.val - n0, h.2⟩ else 0) = 0
  simp only [h2, ↓reduceDIte]

theorem resL_low {N n0 d : ℕ} {w : Vec N} (hw : w ∈ Fl N n0) : resL N n0 d w = 0 := by
  funext k
  show (if h : n0 + k.val < N then w ⟨n0 + k.val, h⟩ else 0) = 0
  split_ifs with h
  · exact hw _ (by simp)
  · rfl

theorem sub_embL_res_mem {N n0 d : ℕ} (h : n0 + d ≤ N) {v : Vec N} (hv : v ∈ Fl N (n0 + d)) :
    v - embL N n0 d (resL N n0 d v) ∈ Fl N n0 := by
  intro k hk
  show v k - (embL N n0 d (resL N n0 d v)) k = 0
  by_cases h2 : n0 ≤ k.val ∧ k.val - n0 < d
  · have h3 : n0 + (k.val - n0) < N := by omega
    have h4 : (⟨n0 + (k.val - n0), h3⟩ : Fin N) = k := Fin.ext (by simp; omega)
    show v k - (if h : n0 ≤ k.val ∧ k.val - n0 < d then
      (if h' : n0 + (k.val - n0) < N then v ⟨n0 + (k.val - n0), h'⟩ else 0) else 0) = 0
    simp only [h2, h3, ↓reduceDIte, h4]
    exact sub_self _
  · have : (embL N n0 d (resL N n0 d v)) k = 0 := by
      show (if h : n0 ≤ k.val ∧ k.val - n0 < d then _ else 0) = 0
      simp only [h2, ↓reduceDIte]
    rw [this]
    exact (sub_zero _).trans (hv k (by omega))

theorem mem_Fl_of_resL_eq_zero {N n0 d : ℕ} (h : n0 + d ≤ N) {v : Vec N} (hv : v ∈ Fl N (n0 + d))
    (h0 : resL N n0 d v = 0) : v ∈ Fl N n0 := by
  have := sub_embL_res_mem h hv
  rw [h0, map_zero] at this
  have e : v - (0 : Vec N) = v := sub_zero v
  rwa [e] at this

@[expose] noncomputable def blockMap (N n0 d : ℕ) (X : Vec N →ₗ[ZMod 2] Vec N) :
    Vec d →ₗ[ZMod 2] Vec d :=
  (resL N n0 d).comp (X.comp (embL N n0 d))

theorem block_rel {N n0 d : ℕ} (h : n0 + d ≤ N) {X : Vec N →ₗ[ZMod 2] Vec N}
    (hX : ∀ v ∈ Fl N n0, X v ∈ Fl N n0) {v : Vec N} (hv : v ∈ Fl N (n0 + d)) :
    resL N n0 d (X v) = blockMap N n0 d X (resL N n0 d v) := by
  have hlow := sub_embL_res_mem h hv
  have e : v = (v - embL N n0 d (resL N n0 d v)) + embL N n0 d (resL N n0 d v) :=
    (sub_add_cancel v _).symm
  conv_lhs => rw [e]
  rw [map_add, map_add, resL_low (hX _ hlow), zero_add]
  rfl

theorem ns_mono {ns : ℕ → ℕ} {nSteps : ℕ} (hmono : ∀ i < nSteps, ns i < ns (i + 1)) :
    ∀ i j, i ≤ j → j ≤ nSteps → ns i ≤ ns j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hj
    exact le_trans (ih (by omega)) (hmono j (by omega)).le

theorem chain_jh {N : ℕ} (ns : ℕ → ℕ) (nSteps : ℕ) (hns0 : ns 0 = 0) (hnsN : ns nSteps = N)
    (hmono : ∀ i < nSteps, ns i < ns (i + 1))
    (g : Bool → (Vec N →ₗ[ZMod 2] Vec N))
    (hinv : ∀ i ≤ nSteps, ∀ b, ∀ v ∈ Fl N (ns i), g b v ∈ Fl N (ns i))
    (hirr : ∀ i < nSteps, IrredPair (fun b => blockMap N (ns i) (ns (i + 1) - ns i) (g b)))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (gW : Bool → (W →ₗ[ZMod 2] W)) (hW : IrredPair gW) (hWne : (⊤ : Submodule (ZMod 2) W) ≠ ⊥)
    (φ : Vec N →ₗ[ZMod 2] W) (hφ : Function.Surjective φ)
    (hφeq : ∀ b v, φ (g b v) = gW b (φ v)) :
    ∃ i < nSteps, ∃ Ψ : Vec (ns (i + 1) - ns i) ≃ₗ[ZMod 2] W,
      ∀ b s, Ψ (blockMap N (ns i) (ns (i + 1) - ns i) (g b) s) = gW b (Ψ s) := by
  classical
  let P : ℕ → Prop := fun i => Submodule.map φ (Fl N (ns i)) ≠ ⊥
  have hPN : P nSteps := by
    show Submodule.map φ (Fl N (ns nSteps)) ≠ ⊥
    rw [hnsN, Fl_self, Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
    exact hWne
  have hP0 : ¬ P 0 := by
    show ¬ (Submodule.map φ (Fl N (ns 0)) ≠ ⊥)
    rw [hns0, Fl_zero, Submodule.map_bot]
    simp
  have hex : ∃ i, P i := ⟨nSteps, hPN⟩
  have hi₀ : P (Nat.find hex) := Nat.find_spec hex
  have hi₀pos : Nat.find hex ≠ 0 := fun h => hP0 (h ▸ hi₀)
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnP : ¬ P i := Nat.find_min hex (by omega)
  have hle : i + 1 ≤ nSteps := hi ▸ Nat.find_min' hex hPN
  rw [hi] at hi₀
  have hn0lt : ns i < ns (i + 1) := hmono i (by omega)
  have hn1N : ns (i + 1) ≤ N := hnsN ▸ ns_mono hmono (i + 1) nSteps hle le_rfl
  refine ⟨i, by omega, ?_⟩
  have hirr' := hirr i (by omega)
  have hinv0 := hinv i (by omega)
  have hinv1 := hinv (i + 1) hle
  have hnP' : Submodule.map φ (Fl N (ns i)) = ⊥ := not_not.mp hnP
  have hi₀' : Submodule.map φ (Fl N (ns (i + 1))) ≠ ⊥ := hi₀
  clear hirr hinv hnP hi₀ hmono hex hi₀pos hi hle hPN hP0
  generalize ns i = n0 at hirr' hinv0 hnP' hn0lt ⊢
  generalize ns (i + 1) = n1 at hirr' hinv1 hi₀' hn1N hn0lt ⊢
  obtain ⟨d, rfl⟩ : ∃ d, n1 = n0 + d := ⟨n1 - n0, by omega⟩
  have hd : n0 + d - n0 = d := by omega
  rw [hd] at hirr' ⊢
  have hwin : n0 + d ≤ N := hn1N
  have hφlow : ∀ v ∈ Fl N n0, φ v = 0 := by
    intro v hv
    have : φ v ∈ Submodule.map φ (Fl N n0) := ⟨v, hv, rfl⟩
    rw [hnP'] at this
    exact this
  let K : Submodule (ZMod 2) (Vec N) := LinearMap.ker φ ⊓ Fl N (n0 + d)
  let R : Submodule (ZMod 2) (Vec d) := K.map (resL N n0 d)
  have hRinv : Inv (fun b => blockMap N n0 d (g b)) R := by
    intro b s hs
    obtain ⟨v, ⟨hvker, hvFl⟩, rfl⟩ := hs
    refine ⟨g b v, ⟨?_, hinv1 b v hvFl⟩, ?_⟩
    · show φ (g b v) = 0
      rw [hφeq, LinearMap.mem_ker.mp hvker, map_zero]
    · exact block_rel hwin (hinv0 b) hvFl
  have hKlow : R = ⊤ → False := by
    intro hR
    apply hi₀'
    rw [eq_bot_iff]
    rintro w ⟨u, hu, rfl⟩
    rw [Submodule.mem_bot]
    have hres : resL N n0 d u ∈ R := by rw [hR]; trivial
    obtain ⟨v, ⟨hvker, hvFl⟩, hvres⟩ := hres
    have hdiff : u - v ∈ Fl N (n0 + d) := Submodule.sub_mem _ hu hvFl
    have hres0 : resL N n0 d (u - v) = 0 := by
      rw [map_sub, hvres]; exact sub_self _
    have hlow : u - v ∈ Fl N n0 := mem_Fl_of_resL_eq_zero hwin hdiff hres0
    have h1 := hφlow _ hlow
    have h2 : φ v = 0 := LinearMap.mem_ker.mp hvker
    rw [map_sub, h2, sub_zero] at h1
    exact h1
  have hR : R = ⊥ := (hirr' R hRinv).resolve_right hKlow
  have hKle : ∀ v ∈ K, v ∈ Fl N n0 := by
    intro v hv
    have : resL N n0 d v ∈ R := ⟨v, hv, rfl⟩
    rw [hR, Submodule.mem_bot] at this
    exact mem_Fl_of_resL_eq_zero hwin hv.2 this
  let Ψ : Vec d →ₗ[ZMod 2] W := φ.comp (embL N n0 d)
  have hinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).mpr fun s hs => ?_
    have hs' : φ (embL N n0 d s) = 0 := hs
    have hmem : embL N n0 d s ∈ K := ⟨hs', embL_mem s⟩
    have := resL_low (d := d) (hKle _ hmem)
    rw [resL_embL hwin] at this
    exact this
  have himg_inv : Inv gW (Submodule.map φ (Fl N (n0 + d))) := by
    intro b w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨g b v, hinv1 b v hv, hφeq b v⟩
  have himg_top : Submodule.map φ (Fl N (n0 + d)) = ⊤ :=
    (hW _ himg_inv).resolve_left hi₀'
  have hsurj : Function.Surjective Ψ := by
    intro w
    have : w ∈ Submodule.map φ (Fl N (n0 + d)) := by rw [himg_top]; trivial
    obtain ⟨v, hv, rfl⟩ := this
    refine ⟨resL N n0 d v, ?_⟩
    have h1 := hφlow _ (sub_embL_res_mem hwin hv)
    rw [map_sub, sub_eq_zero] at h1
    exact h1.symm
  refine ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, ?_⟩
  intro b s
  show φ (embL N n0 d (blockMap N n0 d (g b) s)) = gW b (φ (embL N n0 d s))
  rw [← hφeq]
  have hv : g b (embL N n0 d s) ∈ Fl N (n0 + d) := hinv1 b _ (embL_mem s)
  have h1 := hφlow _ (sub_embL_res_mem hwin hv)
  rw [map_sub, sub_eq_zero] at h1
  exact h1.symm

theorem papply_lt' {N n : ℕ} {cols : List ℕ} (h : ∀ j < n, cols.getD j 0 < 2 ^ n) {v : ℕ}
    (hv : v < 2 ^ n) : papply N cols v < 2 ^ n := by
  unfold papply
  suffices hs : ∀ m : ℕ, ∀ init, init < 2 ^ n →
      (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ cols.getD j 0 else acc) init
        < 2 ^ n by
    exact hs N 0 (by positivity)
  intro m
  induction m with
  | zero => intro init hi; simpa using hi
  | succ m ih =>
    intro init hi
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h1 := ih init hi
    split_ifs with hbit
    · have hm : m < n := by
        by_contra hge
        have hle : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv hle)
        rw [this] at hbit
        exact Bool.false_ne_true hbit
      exact Nat.xor_lt_two_pow h1 (h m hm)
    · exact h1

theorem toVec_mem_Fl {N n x : ℕ} (hx : x < 2 ^ n) : toVec N x ∈ Fl N n := by
  intro k hk
  have hle : 2 ^ n ≤ 2 ^ k.val := Nat.pow_le_pow_right (by norm_num) hk
  simp [toVec_apply, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle)]

theorem lt_of_mem_Fl {N n : ℕ} {v : Vec N} (hv : v ∈ Fl N n) {x : ℕ} (hx : x < 2 ^ N)
    (hxv : toVec N x = v) : x < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases hiN : i < N
  · have := hv ⟨i, hiN⟩ hi
    rw [← hxv, toVec_apply] at this
    by_contra hne
    have hne' : x.testBit i = true := by simpa using hne
    simp [hne'] at this
  · have hle : 2 ^ N ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle)

theorem lin_mem_Fl {N n : ℕ} {cols : List ℕ} (h : ∀ j < n, cols.getD j 0 < 2 ^ n) {v : Vec N}
    (hv : v ∈ Fl N n) : lin N cols v ∈ Fl N n := by
  obtain ⟨x, hx, rfl⟩ := exists_toVec v
  have hxn := lt_of_mem_Fl hv hx rfl
  rw [← toVec_papply]
  exact toVec_mem_Fl (papply_lt' h hxn)

theorem resL_toVec {N n0 d : ℕ} (h : n0 + d ≤ N) (m : ℕ) :
    resL N n0 d (toVec N m) = toVec d ((m >>> n0) % 2 ^ d) := by
  funext k
  have h1 : n0 + k.val < N := by omega
  show (if h : n0 + k.val < N then toVec N m ⟨n0 + k.val, h⟩ else 0) = _
  simp only [h1, ↓reduceDIte, toVec_apply]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [k.isLt]

theorem embL_single {N n0 d : ℕ} (h : n0 + d ≤ N) (k : Fin d) :
    embL N n0 d (Pi.single k 1) = Pi.single ⟨n0 + k.val, by omega⟩ (1 : ZMod 2) := by
  funext j
  show (if h' : n0 ≤ j.val ∧ j.val - n0 < d then (Pi.single k (1 : ZMod 2) : Vec d)
    ⟨j.val - n0, h'.2⟩ else 0) = _
  by_cases hj : j = ⟨n0 + k.val, by omega⟩
  · subst hj
    have h2 : n0 ≤ n0 + k.val ∧ n0 + k.val - n0 < d := ⟨by omega, by omega⟩
    simp only [h2]
    simp
  · have : (Pi.single ⟨n0 + k.val, by omega⟩ (1 : ZMod 2) : Vec N) j = 0 := by
      simp [hj]
    rw [this]
    by_cases h2 : n0 ≤ j.val ∧ j.val - n0 < d
    · simp only [h2]
      have : (⟨j.val - n0, h2.2⟩ : Fin d) ≠ k := by
        intro e
        apply hj
        apply Fin.ext
        have := congrArg Fin.val e
        simp at this
        simp
        omega
      simp [this]
    · simp [h2]

@[expose] def blkCols (cols : List ℕ) (n0 d : ℕ) : List ℕ :=
  (List.range d).map fun k => (cols.getD (n0 + k) 0 >>> n0) % 2 ^ d

theorem blkCols_lt (cols : List ℕ) (n0 d : ℕ) : ∀ j < d, (blkCols cols n0 d).getD j 0 < 2 ^ d := by
  intro j hj
  unfold blkCols
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some]
  exact Nat.mod_lt _ (by positivity)

theorem blockMap_lin {N n0 d : ℕ} (h : n0 + d ≤ N) (cols : List ℕ) :
    blockMap N n0 d (lin N cols) = lin d (blkCols cols n0 d) := by
  symm
  apply lin_eq_of_cols
  intro k
  show _ = resL N n0 d (lin N cols (embL N n0 d (Pi.single k 1)))
  rw [embL_single h, lin_single, resL_toVec h]
  congr 1
  unfold blkCols
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.isLt]
  simp

end CFSG.QuasithinUnique.Setup.X3E
