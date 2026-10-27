module

public import CFSG.GF2Type.Smith1979W3.Cert690.Statements

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

theorem exists_code (g : V₀ ≃ₗ[ZMod 2] V₀) :
    ∃ m < 2 ^ 36, Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m := by
  have hcard : Fintype.card (Fin (2 ^ 36)) =
      Fintype.card (Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Matrix.card_matrix]
    simp
  have hinj : Function.Injective (fun m : Fin (2 ^ 36) => Code.mat (m : ℕ)) := by
    intro a b hab
    exact Fin.ext (Code.eq_of_mat_eq a.isLt b.isLt hab)
  obtain ⟨m, hm⟩ := Function.Injective.surjective_of_finite (Fintype.equivOfCardEq hcard) hinj
    (LinearMap.toMatrix' (g : V₀ →ₗ[ZMod 2] V₀))
  exact ⟨m, m.isLt, hm.symm⟩

theorem vec_injective_of_lt {a b : ℕ} (ha : a < 64) (hb : b < 64)
    (h : Code.vec a = Code.vec b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 6
  · exact Code.testBit_eq_of_bitZ_eq (congrFun h ⟨k, hk⟩)
  · have ha' : a < 2 ^ k := by
      calc a < 64 := ha
        _ = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb' : b < 2 ^ k := by
      calc b < 64 := hb
        _ = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt ha', Nat.testBit_eq_false_of_lt hb']

theorem exists_vec (v : V₀) : ∃ n < 64, Code.vec n = v := by
  have h : ∀ u : V₀, ∃ n : Fin 64, Code.vec (n : ℕ) = u := by decide +kernel
  obtain ⟨n, hn⟩ := h v
  exact ⟨n, n.isLt, hn⟩

theorem apply_vec_of_hasCode {g : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m) (n : ℕ) :
    g (Code.vec n) = Code.vec (Code.act m n) := by
  calc g (Code.vec n) =
        (LinearMap.toMatrix' (g : V₀ →ₗ[ZMod 2] V₀)).mulVec (Code.vec n) :=
        (LinearMap.toMatrix'_mulVec _ _).symm
    _ = (Code.mat m).mulVec (Code.vec n) := by rw [hg]
    _ = Code.vec (Code.act m n) := (Code.vec_act m n).symm

theorem exists_equiv_of_mul_eq_one {a b : ℕ} (h : Code.mul a b = Code.one) :
    ∃ g : V₀ ≃ₗ[ZMod 2] V₀, Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) a := by
  have hmat : Code.mat a * Code.mat b = 1 := by
    rw [← Code.mat_mul, h, Code.mat_one]
  let f : V₀ →ₗ[ZMod 2] V₀ := Matrix.toLin' (Code.mat a)
  let g0 : V₀ →ₗ[ZMod 2] V₀ := Matrix.toLin' (Code.mat b)
  have hf : LinearMap.toMatrix' f = Code.mat a := LinearMap.toMatrix'_toLin' _
  have hfg : f ∘ₗ g0 = LinearMap.id := by
    rw [show f ∘ₗ g0 = Matrix.toLin' (Code.mat a * Code.mat b) from by
      rw [Matrix.toLin'_mul]]
    rw [hmat, Matrix.toLin'_one]
  have hsurj : Function.Surjective f := fun y => ⟨g0 y, by
    have h := congrArg (fun φ : V₀ →ₗ[ZMod 2] V₀ => φ y) hfg
    simpa using h⟩
  have hinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  show LinearMap.toMatrix' ((LinearEquiv.ofBijective f ⟨hinj, hsurj⟩ :
    V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) = Code.mat a
  exact hf

theorem code_mul_assoc (a b c : ℕ) :
    Code.mul (Code.mul a b) c = Code.mul a (Code.mul b c) := by
  apply Code.eq_of_mat_eq (Code.mul_lt _ _) (Code.mul_lt _ _)
  rw [Code.mat_mul, Code.mat_mul, Code.mat_mul, Code.mat_mul, Matrix.mul_assoc]

theorem code_mul_one_of_lt {a : ℕ} (ha : a < 2 ^ 36) : Code.mul a Code.one = a := by
  apply Code.eq_of_mat_eq (Code.mul_lt a Code.one) ha
  rw [Code.mat_mul, Code.mat_one, mul_one]

theorem code_mul_foldl (c p : ℕ) (l : List ℕ) :
    Code.mul c (l.foldl Code.mul p) = l.foldl Code.mul (Code.mul c p) := by
  induction l generalizing p with
  | nil => rfl
  | cons m l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (Code.mul p m), code_mul_assoc]

theorem code_mul_foldl_one_of_lt {c : ℕ} (hc : c < 2 ^ 36) (l : List ℕ) :
    Code.mul c (l.foldl Code.mul Code.one) = l.foldl Code.mul c := by
  rw [code_mul_foldl, code_mul_one_of_lt hc]

theorem getElem!_eq_getElem_of_lt {α : Type*} [Inhabited α] {l : List α} {i : ℕ}
    (h : i < l.length) : l[i]! = l[i] := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < l.length := by simpa using h
      simpa using ih h'

theorem getElem!_mem_of_lt {gens : List ℕ} {i : ℕ} (h : i < gens.length) :
    gens[i]! ∈ gens := by
  rw [getElem!_eq_getElem_of_lt h]
  exact List.getElem_mem h

theorem foldl_map_mem {gens E : List ℕ}
    (closed : ∀ c ∈ E, ∀ g ∈ gens, Code.mul c g ∈ E) {c : ℕ} (hc : c ∈ E) :
    ∀ (w : List ℕ), (∀ i ∈ w, i < gens.length) →
      (w.map fun i => gens[i]!).foldl Code.mul c ∈ E
  | [], _ => hc
  | i :: w, hw => by
    rw [List.map_cons, List.foldl_cons]
    exact foldl_map_mem closed
      (closed c hc (gens[i]!) (getElem!_mem_of_lt (hw i (by simp))))
      w (fun j hj => hw j (by simp [hj]))

theorem hasCode_foldl_mul {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hx : Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c) :
    ∀ {gs : List (V₀ ≃ₗ[ZMod 2] V₀)} {l : List ℕ},
      List.Forall₂ (fun (g : V₀ ≃ₗ[ZMod 2] V₀) (m : ℕ) =>
        Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m) gs l →
      Code.HasCode ((gs.foldl (· * ·) x : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (l.foldl Code.mul c)
  | [], [], .nil => hx
  | g :: gs, m :: l, .cons hg h => hasCode_foldl_mul (hx.mul hg) h

theorem foldl_mul_mem_subgroup {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hx : x ∈ H) :
    ∀ {l : List G}, (∀ y ∈ l, y ∈ H) → l.foldl (· * ·) x ∈ H
  | [], _ => hx
  | y :: l, h => by
    rw [List.foldl_cons]
    exact foldl_mul_mem_subgroup (H.mul_mem hx (h y (by simp)))
      (fun z hz => h z (by simp [hz]))

structure EnumCert (gens : List ℕ) (E : List ℕ) : Prop where
  one_mem : Code.one ∈ E
  lt : ∀ c ∈ E, c < 2 ^ 36
  nodup : E.Nodup
  closed : ∀ c ∈ E, ∀ g ∈ gens, Code.mul c g ∈ E
  gen_inv : ∀ g ∈ gens, ∃ h ∈ E, Code.mul g h = Code.one
  reach : ∀ c ∈ E, ∃ w : List ℕ, (∀ i ∈ w, i < gens.length) ∧
    c = (w.map fun i => gens[i]!).foldl Code.mul Code.one

theorem EnumCert.exists_mem {gens E : List ℕ} (h : EnumCert gens E) {c : ℕ} (hc : c ∈ E) :
    ∃ g ∈ codeSubgroup gens, Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c := by
  classical
  obtain ⟨w, hw, hcw⟩ := h.reach c hc
  have hex : ∀ i, i < gens.length → ∃ g : V₀ ≃ₗ[ZMod 2] V₀,
      Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) gens[i]! := by
    intro i hi
    obtain ⟨hcode, _, hmul⟩ := h.gen_inv gens[i]! (getElem!_mem_of_lt hi)
    exact exists_equiv_of_mul_eq_one hmul
  let genOf : ℕ → V₀ ≃ₗ[ZMod 2] V₀ := fun i =>
    if hi : i < gens.length then Classical.choose (hex i hi) else 1
  have hgenOf : ∀ i (hi : i < gens.length),
      Code.HasCode (genOf i : V₀ →ₗ[ZMod 2] V₀) gens[i]! := by
    intro i hi
    simp only [genOf, dif_pos hi]
    exact Classical.choose_spec (hex i hi)
  have hforall : ∀ (w : List ℕ), (∀ i ∈ w, i < gens.length) →
      List.Forall₂ (fun (g : V₀ ≃ₗ[ZMod 2] V₀) (m : ℕ) =>
        Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m) (w.map genOf)
        (w.map fun i => gens[i]!) := by
    intro w
    induction w with
    | nil => intro _; exact .nil
    | cons i w ih =>
      intro hw
      exact .cons (hgenOf i (hw i (by simp)))
        (ih fun j hj => hw j (by simp [hj]))
  refine ⟨(w.map genOf).foldl (· * ·) 1, ?_, ?_⟩
  · refine foldl_mul_mem_subgroup (H := codeSubgroup gens) (Subgroup.one_mem _) ?_
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure ⟨gens[i]!, getElem!_mem_of_lt (hw i hi),
      hgenOf i (hw i hi)⟩
  · rw [hcw]
    exact hasCode_foldl_mul Code.hasCode_one (hforall w hw)

theorem EnumCert.exists_code_mem {gens E : List ℕ} (h : EnumCert gens E)
    {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ codeSubgroup gens) :
    ∃ c ∈ E, Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c := by
  classical
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  let P : (V₀ ≃ₗ[ZMod 2] V₀) → Prop := fun x =>
    ∃ c ∈ E, Code.HasCode (x : V₀ →ₗ[ZMod 2] V₀) c
  have hPone : P 1 := ⟨Code.one, h.one_mem, Code.hasCode_one⟩
  have hPmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨c, hcE, hc⟩ ⟨d, hdE, hd⟩
    obtain ⟨w, hw, hdw⟩ := h.reach d hdE
    refine ⟨Code.mul c d, ?_, hc.mul hd⟩
    rw [hdw, code_mul_foldl_one_of_lt (h.lt c hcE)]
    exact foldl_map_mem h.closed hcE w hw
  have hPinv : ∀ x, P x → P x⁻¹ := by
    intro x hx
    obtain ⟨c, hcE, hc⟩ := hx
    have hpow : ∀ k : ℕ, P (x ^ k) := by
      intro k
      induction k with
      | zero => simpa using hPone
      | succ k ih => rw [pow_succ]; exact hPmul _ _ ih ⟨c, hcE, hc⟩
    have hxpow : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    have hinv : x ^ (orderOf x - 1) = x⁻¹ := mul_eq_one_iff_eq_inv.mp hxpow
    rw [← hinv]
    exact hpow (orderOf x - 1)
  have hPgens : ∀ x ∈ {g : V₀ ≃ₗ[ZMod 2] V₀ | ∃ m ∈ gens,
      Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m}, P x := by
    rintro x ⟨m, hm, hxm⟩
    obtain ⟨hcode, hcodeE, hmul⟩ := h.gen_inv m hm
    obtain ⟨y, _, hycode⟩ := h.exists_mem hcodeE
    have hPy : P y := ⟨hcode, hcodeE, hycode⟩
    have hPxy : P (x * y) := ⟨Code.one, h.one_mem, by
      have hxy := hxm.mul hycode
      rwa [hmul] at hxy⟩
    rw [(mul_inv_cancel_right x y).symm]
    exact hPmul _ _ hPxy (hPinv y hPy)
  have key : ∀ x ∈ codeSubgroup gens, P x := by
    intro x hx
    refine Subgroup.closure_induction (k := {g : V₀ ≃ₗ[ZMod 2] V₀ | ∃ m ∈ gens,
      Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m}) (p := fun x _ => P x) ?_ ?_ ?_ ?_ hx
    · exact hPgens
    · exact hPone
    · intro a b _ _ ha hb
      exact hPmul a b ha hb
    · intro a _ ha
      exact hPinv a ha
  exact key g hg

theorem EnumCert.natCard {gens E : List ℕ} (h : EnumCert gens E) :
    Nat.card (codeSubgroup gens) = E.length := by
  classical
  let f : codeSubgroup gens → {c // c ∈ E} := fun g =>
    ⟨Classical.choose (h.exists_code_mem g.2),
      (Classical.choose_spec (h.exists_code_mem g.2)).1⟩
  let ginv : {c // c ∈ E} → codeSubgroup gens := fun c =>
    ⟨Classical.choose (h.exists_mem c.2),
      (Classical.choose_spec (h.exists_mem c.2)).1⟩
  have hleft : Function.LeftInverse ginv f := by
    intro g
    apply Subtype.ext
    apply Code.HasCode.eq_of_equiv
    · exact (Classical.choose_spec (h.exists_mem (f g).2)).2
    · exact (Classical.choose_spec (h.exists_code_mem g.2)).2
  have hright : Function.RightInverse ginv f := by
    intro c
    apply Subtype.ext
    exact Code.HasCode.code_eq (Classical.choose_spec (h.exists_code_mem (ginv c).2)).2
      (Classical.choose_spec (h.exists_mem c.2)).2
      (h.lt _ (Classical.choose_spec (h.exists_code_mem (ginv c).2)).1)
      (h.lt c.1 c.2)
  let e : codeSubgroup gens ≃ {c // c ∈ E} :=
    { toFun := f, invFun := ginv, left_inv := hleft, right_inv := hright }
  calc Nat.card (codeSubgroup gens) = Nat.card {c // c ∈ E} := Nat.card_congr e
    _ = E.length := by
        rw [← Nat.card_congr (List.Nodup.getEquiv E h.nodup), Nat.card_fin]

theorem EnumCert.mem_iff {gens E : List ℕ} (h : EnumCert gens E)
    {g : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ}
    (hgc : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) c) (hc : c < 2 ^ 36) :
    g ∈ codeSubgroup gens ↔ c ∈ E := by
  constructor
  · intro hg
    obtain ⟨d, hdE, hd⟩ := h.exists_code_mem hg
    rw [hgc.code_eq hd hc (h.lt d hdE)]
    exact hdE
  · intro hcE
    obtain ⟨g', hg', hg'c⟩ := h.exists_mem hcE
    rw [← hg'c.eq_of_equiv hgc]
    exact hg'

theorem mem_O₀_of_isoQ {minus : Bool} {g : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m)
    (h : ∀ n < 64, qB minus (Code.act m n) = qB minus n) : g ∈ O₀ minus := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨n, hn, rfl⟩ := exists_vec v
  rw [apply_vec_of_hasCode hg n, qModel_vec, qModel_vec, h n hn]

theorem isoQ_of_mem_O₀ {minus : Bool} {g : V₀ ≃ₗ[ZMod 2] V₀} {m : ℕ}
    (hg : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m) (h : g ∈ O₀ minus) :
    ∀ n < 64, qB minus (Code.act m n) = qB minus n := by
  intro n _
  have hmem : qModel minus (g (Code.vec n)) = qModel minus (Code.vec n) :=
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup h _
  rw [apply_vec_of_hasCode hg n, qModel_vec, qModel_vec] at hmem
  revert hmem
  cases h1 : qB minus (Code.act m n) <;> cases h2 : qB minus n <;> simp [h1, h2]

theorem codeSubgroup_map_wordC_le_O₀ {minus : Bool} (ws : List (List ℕ))
    (hl : ∀ w ∈ ws, ∀ n ∈ w, qB minus n = true) :
    codeSubgroup (ws.map wordC) ≤ O₀ minus := by
  rw [codeSubgroup, Subgroup.closure_le]
  rintro g ⟨m, hm, hgm⟩
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  rw [show g = wordProd w from hgm.eq_of_equiv (hasCode_wordProd w)]
  exact wordProd_mem_orthogonalGroup (hl w hw)

theorem codeSubgroup_map_wordC_le_omega {minus : Bool} (ws : List (List ℕ))
    (hl : ∀ w ∈ ws, ∀ n ∈ w, qB minus n = true)
    (he : ∀ w ∈ ws, Even w.length) :
    codeSubgroup (ws.map wordC) ≤ Ω₀ minus := by
  rw [codeSubgroup, Subgroup.closure_le]
  rintro g ⟨m, hm, hgm⟩
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  rw [show g = wordProd w from hgm.eq_of_equiv (hasCode_wordProd w)]
  exact (wordProd_mem_omegaGroup_iff (hl w hw)).mpr (he w hw)

private theorem finrank_V₀ : Module.finrank (ZMod 2) V₀ = 6 := Module.finrank_fin_fun (ZMod 2)

private theorem card_V₀ : Nat.card V₀ = 64 := natCard_eq_sixtyFour (V := V₀) finrank_V₀

private theorem ncard_zero_qPlus : {v : V₀ | qPlus v = 0}.ncard = 36 := by
  have hc : {v : V₀ | qPlus v = 0} = {v : V₀ | qPlus v = 1}ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rcases zmod2_eq_zero_or_eq_one (qPlus v) with h | h <;> simp [h]
  have h1 := Set.ncard_add_ncard_compl {v : V₀ | qPlus v = 1}
  rw [ncard_qPlus, ← hc, card_V₀] at h1
  omega

private theorem ncard_zero_qMinus : {v : V₀ | qMinus v = 0}.ncard = 28 := by
  have hc : {v : V₀ | qMinus v = 0} = {v : V₀ | qMinus v = 1}ᶜ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rcases zmod2_eq_zero_or_eq_one (qMinus v) with h | h <;> simp [h]
  have h1 := Set.ncard_add_ncard_compl {v : V₀ | qMinus v = 1}
  rw [ncard_qMinus, ← hc, card_V₀] at h1
  omega

private theorem card_orthogonalGroup_of_ncard_zero {Q : QuadraticForm (ZMod 2) V₀}
    (hQ : Q.polarBilin.Nondegenerate) (h : {v : V₀ | Q v = 0}.ncard = 36) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 40320 := by
  have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq (V := V₀) (Q := Q) hQ (m := 3)
    (by rw [finrank_V₀])
  rw [h] at h1
  have h2 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [h2] at h1
  omega

private theorem card_orthogonalGroup_of_ncard_zero' {Q : QuadraticForm (ZMod 2) V₀}
    (hQ : Q.polarBilin.Nondegenerate) (h : {v : V₀ | Q v = 0}.ncard = 28) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 51840 := by
  have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq (V := V₀) (Q := Q) hQ (m := 3)
    (by rw [finrank_V₀])
  rw [h] at h1
  have h2 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [h2] at h1
  omega

private theorem card_O₀_false : Nat.card (O₀ false) = 40320 := by
  refine card_orthogonalGroup_of_ncard_zero (Q := qModel false) (qModel_nondegenerate false) ?_
  rw [qModel_false]
  exact ncard_zero_qPlus

private theorem card_O₀_true : Nat.card (O₀ true) = 51840 := by
  refine card_orthogonalGroup_of_ncard_zero' (Q := qModel true) (qModel_nondegenerate true) ?_
  rw [qModel_true]
  exact ncard_zero_qMinus

private theorem card_Ω₀_false : Nat.card (Ω₀ false) = 20160 := by
  have h := S12DW.card_orthogonalGroup_eq (Q := qModel false) (qModel_nondegenerate false)
  rw [card_O₀_false] at h
  change Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (qModel false)
    (qModel_nondegenerate false)) = 20160
  omega

private theorem card_Ω₀_true : Nat.card (Ω₀ true) = 25920 := by
  have h := S12DW.card_orthogonalGroup_eq (Q := qModel true) (qModel_nondegenerate true)
  rw [card_O₀_true] at h
  change Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (qModel true)
    (qModel_nondegenerate true)) = 25920
  omega

theorem natCard_O₀ (minus : Bool) :
    Nat.card (O₀ minus) = if minus then 51840 else 40320 := by
  cases minus
  · exact card_O₀_false
  · exact card_O₀_true

theorem natCard_Ω₀ (minus : Bool) :
    Nat.card (Ω₀ minus) = if minus then 25920 else 20160 := by
  cases minus
  · exact card_Ω₀_false
  · exact card_Ω₀_true

theorem eq_of_le_of_natCard {H K : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (h : H ≤ K)
    (hc : Nat.card H = Nat.card K) : H = K := by
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  exact Subgroup.eq_of_le_of_card_ge h (le_of_eq hc.symm)

@[expose] def omegaWords : Bool → List (List ℕ)
  | false => [[57, 56, 29, 28], [29, 28], [57, 56, 49, 48], [53, 52, 49, 48], [12, 3]]
  | true => [[49, 48, 13, 12], [49, 48], [21, 20], [17, 16], [48, 3]]

@[expose] def oWords : Bool → List (List ℕ)
  | false => [[57, 56, 29, 28], [29, 28], [57, 56, 49, 48], [53, 52, 49, 48], [48, 12, 3]]
  | true => [[49, 48, 13, 12], [49, 48], [21, 20], [17, 16], [48, 12, 3]]

theorem oWords_eq_dropLast (minus : Bool) :
    oWords minus = (omegaWords minus).dropLast ++ [[48, 12, 3]] := by
  cases minus <;> rfl

theorem omegaWords_letters (minus : Bool) :
    ∀ w ∈ omegaWords minus, ∀ n ∈ w, qB minus n = true := by
  cases minus <;> decide +kernel

theorem omegaWords_even (minus : Bool) :
    ∀ w ∈ omegaWords minus, Even w.length := by
  cases minus <;> decide +kernel

theorem oWords_letters (minus : Bool) :
    ∀ w ∈ oWords minus, ∀ n ∈ w, qB minus n = true := by
  cases minus <;> decide +kernel

theorem omegaWords_code_false :
    (omegaWords false).map wordC =
      [34647329153, 35704297409, 34630292097, 34630549889, 34629255234] := by
  decide +kernel

theorem omegaWords_code_true :
    (omegaWords true).map wordC =
      [35721076609, 35720809665, 35704292801, 35704030401, 17718853698] := by
  decide +kernel

theorem oWords_code_false :
    (oWords false).map wordC =
      [34647329153, 35704297409, 34630292097, 34630549889, 17717821506] := by
  decide +kernel

theorem oWords_code_true :
    (oWords true).map wordC =
      [35721076609, 35720809665, 35704292801, 35704030401, 17717821506] := by
  decide +kernel

theorem kPGLGens_eq_wordC :
    kPGLGens = ([[57, 56, 29, 28], [53, 52, 49, 48], [48, 12, 3]].map wordC) := by
  decide +kernel

theorem kPGL0Gens_eq_wordC :
    kPGL0Gens = ([[49, 48, 23, 13, 12, 3], [13, 11, 7, 3]].map wordC) := by
  decide +kernel

theorem KPGL_le_O₀ : KPGL ≤ O₀ false := by
  rw [KPGL, kPGLGens_eq_wordC]
  exact codeSubgroup_map_wordC_le_O₀ (minus := false) _ (by decide +kernel)

theorem KPGL0_le_Ω₀ : KPGL0 ≤ Ω₀ false := by
  rw [KPGL0, kPGL0Gens_eq_wordC]
  exact codeSubgroup_map_wordC_le_omega (minus := false) _ (by decide +kernel) (by decide +kernel)

end CFSG.GF2Type.Smith1979W3.Cert690

end
