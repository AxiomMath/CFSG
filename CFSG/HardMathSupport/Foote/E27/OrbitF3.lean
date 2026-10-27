module

public import CFSG.Monster.B.Pinned.Primes.ThreeAction
public import CFSG.Monster.B.Pinned.Primes.Extraspecial

public section

namespace CFSG.HardMathSupport.Foote.E27.OrbitF3

open CFSG.Monster.B.Pinned
open scoped Matrix

variable (d : ℕ)

@[expose] def lmulD (A B : List (List ℕ)) : List (List ℕ) := A.map fun r => lvecMul 3 d r B

@[expose] def lidD : List (List ℕ) :=
  (List.range d).map fun i => (List.range d).map fun j => if i = j then 1 else 0

@[expose] def lpowD (A : List (List ℕ)) : ℕ → List (List ℕ)
  | 0 => lidD d
  | e + 1 => lmulD d (lpowD A e) A

variable {d}

theorem lmulD_length (A B : List (List ℕ)) : (lmulD d A B).length = A.length := by
  simp [lmulD]

theorem lidD_length : (lidD d).length = d := by simp [lidD]

theorem lpowD_length (A : List (List ℕ)) : ∀ e, (lpowD d A e).length = d
  | 0 => lidD_length
  | e + 1 => by rw [lpowD, lmulD_length, lpowD_length A e]

theorem rowsMat_lmulD {A : List (List ℕ)} (hA : A.length = d) (B : List (List ℕ)) :
    rowsMat 3 d (lmulD d A B) = rowsMat 3 d A * rowsMat 3 d B := by
  ext i j
  have hi : (i : ℕ) < A.length := lt_of_lt_of_eq i.2 hA.symm
  have e : (lmulD d A B).getD i [] = lvecMul 3 d (A.getD i []) B := by
    rw [lmulD, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  have := congrFun (rowsVec_lvecMul 3 d (A.getD i []) B) j
  simp only [rowsVec] at this
  simp only [rowsMat, Matrix.of_apply, e, this, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    rowsVec]

theorem rowsMat_lidD : rowsMat 3 d (lidD d) = 1 := by
  ext i j
  simp only [lidD, rowsMat, Matrix.of_apply, Matrix.one_apply, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range i.2, List.getElem?_range j.2, Option.map_some,
    Option.getD_some]
  by_cases h : i = j
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem rowsMat_lpowD (A : List (List ℕ)) : ∀ e, rowsMat 3 d (lpowD d A e) = rowsMat 3 d A ^ e
  | 0 => by rw [lpowD, rowsMat_lidD, pow_zero]
  | e + 1 => by rw [lpowD, rowsMat_lmulD (lpowD_length A e), rowsMat_lpowD A e, pow_succ]

theorem coe_prod_eq_rowsMat : ∀ (us : List (GL (Fin d) (ZMod 3))) (rs : List (List (List ℕ))),
    List.Forall₂ (fun (u : GL (Fin d) (ZMod 3)) (r : List (List ℕ)) =>
      (u : Matrix (Fin d) (Fin d) (ZMod 3)) = rowsMat 3 d r) us rs →
    ∀ (g : GL (Fin d) (ZMod 3)) (acc : List (List ℕ)), acc.length = d →
      (g : Matrix (Fin d) (Fin d) (ZMod 3)) = rowsMat 3 d acc →
      ((g * us.prod : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) =
        rowsMat 3 d (rs.foldl (lmulD d) acc)
  | [], [], _, g, acc, _, hg => by simpa using hg
  | u :: us, r :: rs, h, g, acc, hacc, hg => by
    rw [List.forall₂_cons] at h
    rw [List.prod_cons, ← mul_assoc, List.foldl_cons]
    refine coe_prod_eq_rowsMat us rs h.2 (g * u) (lmulD d acc r) (by rw [lmulD_length, hacc]) ?_
    rw [Units.val_mul, hg, h.1, rowsMat_lmulD hacc]

theorem coe_prod_eq_rowsMat_one (us : List (GL (Fin d) (ZMod 3))) (rs : List (List (List ℕ)))
    (h : List.Forall₂ (fun (u : GL (Fin d) (ZMod 3)) (r : List (List ℕ)) =>
      (u : Matrix (Fin d) (Fin d) (ZMod 3)) = rowsMat 3 d r) us rs) :
    ((us.prod : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) =
      rowsMat 3 d (rs.foldl (lmulD d) (lidD d)) := by
  have := coe_prod_eq_rowsMat us rs h 1 (lidD d) lidD_length (by rw [Units.val_one, rowsMat_lidD])
  rwa [one_mul] at this

variable (d) in
@[expose] def bfsLayerD (gens : List (List (List ℕ))) (bm : ℕ) (F : List (List ℕ)) :
    ℕ × List (List ℕ) :=
  F.foldl (fun st u => gens.foldl (fun st' G => bfsAdd st' (lvecMul 3 d u G)) st) (bm, [])

variable (d) in
@[expose] def bfsD (gens : List (List (List ℕ))) : ℕ → ℕ → List (List ℕ) → List (List ℕ) →
    List (List ℕ)
  | 0, _, F, acc => F ++ acc
  | fuel + 1, bm, F, acc =>
    match F with
    | [] => acc
    | _ :: _ =>
      let r := bfsLayerD d gens bm F
      bfsD gens fuel r.1 r.2 (F ++ acc)

variable (d) in
@[expose] def orbitOKD (gens : List (List (List ℕ))) (L : List (List ℕ)) : Bool :=
  match distinctBits L 0 with
  | none => false
  | some bm => L.all fun w => gens.all fun G => bm.testBit (lcode (lvecMul 3 d w G))

theorem orbitOKD_spec {gens : List (List (List ℕ))} {L : List (List ℕ)}
    (h : orbitOKD d gens L = true) :
    (L.map lcode).Nodup ∧ ∀ w ∈ L, ∀ G ∈ gens, ∃ w' ∈ L, lcode w' = lcode (lvecMul 3 d w G) := by
  unfold orbitOKD at h
  split at h
  · exact absurd h (by simp)
  · rename_i bm hbm
    obtain ⟨h1, h2, -⟩ := distinctBits_spec L 0 bm hbm
    refine ⟨h2, fun w hw G hG => ?_⟩
    have := List.all_eq_true.1 (List.all_eq_true.1 h w hw) G hG
    rcases (h1 _).1 this with h0 | h0
    · simp at h0
    · exact h0

theorem bfsLayerD_inv {P : List ℕ → Prop} {gens : List (List (List ℕ))}
    (hP : ∀ u, P u → ∀ G ∈ gens, P (lvecMul 3 d u G)) :
    ∀ (F : List (List ℕ)) (st : ℕ × List (List ℕ)), (∀ w ∈ st.2, P w) → (∀ u ∈ F, P u) →
      ∀ w ∈ (F.foldl (fun st u => gens.foldl (fun st' G => bfsAdd st' (lvecMul 3 d u G)) st)
        st).2, P w
  | [], st, hst, _ => hst
  | u :: F, st, hst, hF => by
    rw [List.foldl_cons]
    refine bfsLayerD_inv hP F _ ?_ (fun u' hu' => hF u' (List.mem_cons_of_mem _ hu'))
    have hu := hF u (List.mem_cons_self ..)
    have key : ∀ (gs : List (List (List ℕ))) (st' : ℕ × List (List ℕ)), (∀ G ∈ gs, G ∈ gens) →
        (∀ w ∈ st'.2, P w) →
        ∀ w ∈ (gs.foldl (fun st' G => bfsAdd st' (lvecMul 3 d u G)) st').2, P w := by
      intro gs
      induction gs with
      | nil => intro st' _ h; exact h
      | cons G gs ih =>
        intro st' hgs h
        rw [List.foldl_cons]
        refine ih _ (fun G' hG' => hgs G' (List.mem_cons_of_mem _ hG')) ?_
        intro w hw
        rcases mem_bfsAdd hw with rfl | hw
        · exact hP u hu G (hgs G (List.mem_cons_self ..))
        · exact h w hw
    exact key gens st (fun G hG => hG) hst

theorem bfsD_inv {P : List ℕ → Prop} {gens : List (List (List ℕ))}
    (hP : ∀ u, P u → ∀ G ∈ gens, P (lvecMul 3 d u G)) :
    ∀ (fuel bm : ℕ) (F acc : List (List ℕ)), (∀ w ∈ F, P w) → (∀ w ∈ acc, P w) →
      ∀ w ∈ bfsD d gens fuel bm F acc, P w
  | 0, bm, F, acc, hF, hacc => by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hF w hw
    · exact hacc w hw
  | fuel + 1, bm, [], acc, _, hacc => by
    intro w hw
    simp only [bfsD] at hw
    exact hacc w hw
  | fuel + 1, bm, u :: F, acc, hF, hacc => by
    intro w hw
    simp only [bfsD] at hw
    refine bfsD_inv hP fuel _ _ _ (bfsLayerD_inv hP (u :: F) (bm, []) (by simp) hF) ?_ w hw
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hF w hw
    · exact hacc w hw

theorem mem_bfsD (gens : List (List (List ℕ))) :
    ∀ (fuel bm : ℕ) (F acc : List (List ℕ)), ∀ w ∈ F ++ acc, w ∈ bfsD d gens fuel bm F acc
  | 0, bm, F, acc => fun w hw => hw
  | fuel + 1, bm, [], acc => fun w hw => by simpa [bfsD] using hw
  | fuel + 1, bm, u :: F, acc => fun w hw => by
    simp only [bfsD]
    exact mem_bfsD gens fuel _ _ _ w (List.mem_append_right _ hw)

variable (d) in
@[expose] def ValidD (w : List ℕ) : Prop := w.length = d ∧ ∀ x ∈ w, x < 3

theorem validD_lvecMul (v : List ℕ) (M : List (List ℕ)) : ValidD d (lvecMul 3 d v M) :=
  ⟨lvecMul_length 3 d v M, lvecMul_lt (by norm_num) v M⟩

theorem rowsVec_injD {v w : List ℕ} (hv : ValidD d v) (hw : ValidD d w)
    (h : rowsVec 3 d v = rowsVec 3 d w) : v = w := by
  apply List.ext_getElem (hv.1.trans hw.1.symm)
  intro i hi hi'
  have hid : i < d := hv.1 ▸ hi
  have e := congrFun h ⟨i, hid⟩
  simp only [rowsVec, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
  have h1 := hv.2 _ (List.getElem_mem hi)
  have h2 := hw.2 _ (List.getElem_mem hi')
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at e
  exact e

variable (d) in
@[ext] structure RowVD where
  vec : Fin d → ZMod 3

instance rowActionD : MulAction (GL (Fin d) (ZMod 3)) (RowVD d) where
  smul g w := ⟨w.vec ᵥ* ((g⁻¹ : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3))⟩
  one_smul w := RowVD.ext (by
    show w.vec ᵥ* (((1 : GL (Fin d) (ZMod 3))⁻¹ : GL (Fin d) (ZMod 3)) :
      Matrix (Fin d) (Fin d) (ZMod 3)) = w.vec
    rw [inv_one, Units.val_one, Matrix.vecMul_one])
  mul_smul g h w := RowVD.ext (by
    show w.vec ᵥ* (((g * h)⁻¹ : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) =
      (w.vec ᵥ* ((h⁻¹ : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3))) ᵥ*
        ((g⁻¹ : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3))
    rw [mul_inv_rev, Units.val_mul, Matrix.vecMul_vecMul])

theorem vec_smulD {K : Subgroup (GL (Fin d) (ZMod 3))} (g : K) (w : RowVD d) :
    (g • w).vec = w.vec ᵥ* ((((g : GL (Fin d) (ZMod 3))⁻¹ : GL (Fin d) (ZMod 3))) :
      Matrix (Fin d) (Fin d) (ZMod 3)) :=
  rfl

theorem mem_stabilizer_of_fix {K : Subgroup (GL (Fin d) (ZMod 3))} (g : K) {v : Fin d → ZMod 3}
    (h : v ᵥ* ((g : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) = v) :
    g ∈ MulAction.stabilizer K (⟨v⟩ : RowVD d) := by
  rw [MulAction.mem_stabilizer_iff]
  apply RowVD.ext
  rw [vec_smulD]
  show v ᵥ* (((g : GL (Fin d) (ZMod 3))⁻¹ : GL (Fin d) (ZMod 3)) :
    Matrix (Fin d) (Fin d) (ZMod 3)) = v
  conv_lhs => rw [← h]
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

section Orbit

variable {gens : List (GL (Fin d) (ZMod 3))} {rows : List (List (List ℕ))}

theorem ncard_orbit_of_bfs (hlen : gens.length = rows.length)
    (hrows : ∀ (i : ℕ) (h₁ : i < gens.length) (h₂ : i < rows.length),
      ((gens[i] : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) =
        rowsMat 3 d rows[i])
    {b : List ℕ} (hb : ValidD d b) (fuel : ℕ) (hok : orbitOKD d rows
      (bfsD d rows fuel (1 <<< lcode b) [b] []) = true) :
    (MulAction.orbit (Subgroup.closure {g | g ∈ gens}) (⟨rowsVec 3 d b⟩ : RowVD d)).ncard =
      (bfsD d rows fuel (1 <<< lcode b) [b] []).length := by
  set K : Subgroup (GL (Fin d) (ZMod 3)) := Subgroup.closure {g | g ∈ gens} with hK
  set L := bfsD d rows fuel (1 <<< lcode b) [b] [] with hL
  set v : Fin d → ZMod 3 := rowsVec 3 d b with hv
  have hgen : ∀ G ∈ rows, ∃ t ∈ K, (t : Matrix (Fin d) (Fin d) (ZMod 3)) = rowsMat 3 d G := by
    intro G hG
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hG
    have hi' : i < gens.length := hlen ▸ hi
    exact ⟨gens[i], Subgroup.subset_closure (List.getElem_mem hi'), hrows i hi' hi⟩
  let Reach : List ℕ → Prop := fun w =>
    ValidD d w ∧ ∃ g ∈ K, rowsVec 3 d w = v ᵥ* (g : Matrix (Fin d) (Fin d) (ZMod 3))
  have hstep : ∀ u, Reach u → ∀ G ∈ rows, Reach (lvecMul 3 d u G) := by
    rintro u ⟨-, g, hg, hgu⟩ G hG
    obtain ⟨t, ht, htG⟩ := hgen G hG
    refine ⟨validD_lvecMul u G, g * t, mul_mem hg ht, ?_⟩
    rw [rowsVec_lvecMul, hgu, Units.val_mul, ← Matrix.vecMul_vecMul, htG]
  have hreach : ∀ w ∈ L, Reach w := by
    refine bfsD_inv hstep fuel _ [b] [] ?_ (by simp)
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    exact ⟨hb, 1, one_mem _, by rw [Units.val_one, Matrix.vecMul_one]⟩
  have hbL : b ∈ L := mem_bfsD _ fuel _ [b] [] b (by simp)
  let S : Set (Fin d → ZMod 3) := {u | ∃ w ∈ L, u = rowsVec 3 d w}
  have hclosed : ∀ u ∈ S, ∀ G ∈ rows, u ᵥ* rowsMat 3 d G ∈ S := by
    rintro u ⟨w, hw, rfl⟩ G hG
    obtain ⟨w', hw', he⟩ := (orbitOKD_spec hok).2 w hw G hG
    have := lcode_inj (hreach w' hw').1.2 (validD_lvecMul w G).2
      ((hreach w' hw').1.1.trans (validD_lvecMul w G).1.symm) he
    exact ⟨w', hw', by rw [this, rowsVec_lvecMul]⟩
  have hinv : ∀ g ∈ K, ∀ u ∈ S, u ᵥ* (g : Matrix (Fin d) (Fin d) (ZMod 3)) ∈ S := by
    intro g hg
    have hg' : g ∈ Submonoid.closure ({g | g ∈ gens} : Set (GL (Fin d) (ZMod 3))) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact hg
    clear hg
    induction hg' using Submonoid.closure_induction with
    | mem t ht =>
      intro u hu
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      have hi' : i < rows.length := hlen ▸ hi
      rw [hrows i hi hi']
      exact hclosed u hu _ (List.getElem_mem hi')
    | one => intro u hu; rwa [Units.val_one, Matrix.vecMul_one]
    | mul a c _ _ iha ihc =>
      intro u hu
      rw [Units.val_mul, ← Matrix.vecMul_vecMul]
      exact ihc _ (iha u hu)
  have horbit : {w : Fin d → ZMod 3 | ∃ g ∈ K, w = v ᵥ* (g : Matrix (Fin d) (Fin d) (ZMod 3))} =
      S := by
    ext u
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hinv g hg _ ⟨b, hbL, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨-, g, hg, e⟩ := hreach w hw
      exact ⟨g, hg, e⟩
  have hncard : S.ncard = L.length := by
    have hnd : L.Nodup := (orbitOKD_spec hok).1.of_map _
    have hnd' : (L.map (rowsVec 3 d)).Nodup :=
      hnd.map_on fun x hx y hy h => rowsVec_injD (hreach x hx).1 (hreach y hy).1 h
    have e : S = ↑(L.map (rowsVec 3 d)).toFinset := by
      ext u
      simp only [S, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', List.length_map]
  have himage : RowVD.vec '' MulAction.orbit K (⟨v⟩ : RowVD d) = S := by
    rw [← horbit]
    ext u
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨(g : GL (Fin d) (ZMod 3))⁻¹, inv_mem g.2, vec_smulD g _⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨(⟨g, hg⟩⁻¹ : K) • (⟨v⟩ : RowVD d), ⟨_, rfl⟩, ?_⟩
      rw [vec_smulD, Subgroup.coe_inv, inv_inv]
  rw [← Set.ncard_image_of_injective _ (fun a c h => RowVD.ext h), himage, hncard]

theorem card_eq_mul_card_stabilizer (K : Subgroup (GL (Fin d) (ZMod 3))) (w : RowVD d) :
    Nat.card K = Nat.card (MulAction.stabilizer K w) * (MulAction.orbit K w).ncard := by
  have hidx := MulAction.index_stabilizer K w
  rw [← hidx]
  exact (MulAction.stabilizer K w).card_mul_index.symm

end Orbit

open Subgroup in
theorem nine_dvd_card_of_commute {G : Type*} [Group G] [Finite G] {x y : G} (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hx1 : x ≠ 1) (hc : x * y = y * x) (hy0 : y ≠ 1) (hy1 : y ≠ x)
    (hy2 : y ≠ x ^ 2) : 9 ∣ Nat.card G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy0
  have hyQ : y ∉ zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hk' : x ^ (k % 3) = y := by
      have h' := zpow_mod_orderOf x k
      rw [hox, Nat.cast_ofNat] at h'
      rw [h', hk]
    have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h3 with h | h | h <;> rw [h] at hk'
    · exact hy0 (by rw [← hk', zpow_zero])
    · exact hy1 (by rw [← hk', zpow_one])
    · exact hy2 (by rw [← hk']; norm_cast)
  have hconj : ∀ g ∈ zpowers x, y⁻¹ * g * y ∈ zpowers x := by
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have hcomm : x ^ k * y = y * x ^ k := (Commute.zpow_left (show Commute x y from hc) k).eq
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    exact zpow_mem (mem_zpowers x) k
  have hcard := CFSG.Monster.B.Pinned.card_sup_zpowers hoy hyQ hconj
  rw [Nat.card_zpowers, hox] at hcard
  rw [show (9 : ℕ) = 3 * 3 by norm_num, ← hcard]
  exact Subgroup.card_subgroup_dvd_card _

theorem nine_dvd_card_stabilizer {K : Subgroup (GL (Fin d) (ZMod 3))} {w : RowVD d}
    {a b : GL (Fin d) (ZMod 3)} (ha : a ∈ K) (hb : b ∈ K)
    (hfa : w.vec ᵥ* (a : Matrix (Fin d) (Fin d) (ZMod 3)) = w.vec)
    (hfb : w.vec ᵥ* (b : Matrix (Fin d) (Fin d) (ZMod 3)) = w.vec) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hc : a * b = b * a) (hb0 : b ≠ 1) (hb1 : b ≠ a)
    (hb2 : b ≠ a ^ 2) : 9 ∣ Nat.card (MulAction.stabilizer K w) := by
  have hwa : (⟨a, ha⟩ : K) ∈ MulAction.stabilizer K w := mem_stabilizer_of_fix _ hfa
  have hwb : (⟨b, hb⟩ : K) ∈ MulAction.stabilizer K w := mem_stabilizer_of_fix _ hfb
  let ι : MulAction.stabilizer K w →* GL (Fin d) (ZMod 3) :=
    K.subtype.comp (MulAction.stabilizer K w).subtype
  have hι : Function.Injective ι := fun x y h => Subtype.ext (Subtype.ext h)
  have hx : ι ⟨⟨a, ha⟩, hwa⟩ = a := rfl
  have hy : ι ⟨⟨b, hb⟩, hwb⟩ = b := rfl
  have hne : ∀ x y : MulAction.stabilizer K w, ι x ≠ ι y → x ≠ y := fun x y h e => h (e ▸ rfl)
  refine nine_dvd_card_of_commute (x := ⟨⟨a, ha⟩, hwa⟩) (y := ⟨⟨b, hb⟩, hwb⟩) (hι ?_) (hι ?_)
    (hne _ _ ?_) (hι ?_) (hne _ _ ?_) (hne _ _ ?_) (hne _ _ ?_)
  · rw [map_pow, hx, map_one, ha3]
  · rw [map_pow, hy, map_one, hb3]
  · rw [hx, map_one]; exact ha1
  · rw [map_mul, map_mul, hx, hy, hc]
  · rw [hy, map_one]; exact hb0
  · rw [hy, hx]; exact hb1
  · rw [hy, map_pow, hx]; exact hb2

@[expose] def fixSub {K : Subgroup (GL (Fin d) (ZMod 3))} (w : RowVD d) (u : Fin d → ZMod 3) :
    Subgroup (MulAction.stabilizer K w) :=
  (MulAction.stabilizer (GL (Fin d) (ZMod 3)) (⟨u⟩ : RowVD d)).comap
    (K.subtype.comp (MulAction.stabilizer K w).subtype)

theorem mem_fixSub {K : Subgroup (GL (Fin d) (ZMod 3))} {w : RowVD d} {u : Fin d → ZMod 3}
    (g : MulAction.stabilizer K w) :
    g ∈ fixSub w u ↔ u ᵥ* (((g : K) : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) =
      u := by
  set t : GL (Fin d) (ZMod 3) := ((g : K) : GL (Fin d) (ZMod 3))
  show t • (⟨u⟩ : RowVD d) = ⟨u⟩ ↔ _
  constructor
  · intro h
    have h' := congrArg RowVD.vec h
    change u ᵥ* ((t⁻¹ : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) = u at h'
    conv_lhs => rw [← h']
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  · intro h
    apply RowVD.ext
    change u ᵥ* ((t⁻¹ : GL (Fin d) (ZMod 3)) : Matrix (Fin d) (Fin d) (ZMod 3)) = u
    conv_lhs => rw [← h]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

open Subgroup in
theorem twentySeven_dvd_card_stabilizer {K : Subgroup (GL (Fin d) (ZMod 3))} {w : RowVD d}
    {a b c : GL (Fin d) (ZMod 3)} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (hfa : w.vec ᵥ* (a : Matrix (Fin d) (Fin d) (ZMod 3)) = w.vec)
    (hfb : w.vec ᵥ* (b : Matrix (Fin d) (Fin d) (ZMod 3)) = w.vec)
    (hfc : w.vec ᵥ* (c : Matrix (Fin d) (Fin d) (ZMod 3)) = w.vec)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) (u₁ u₂ : Fin d → ZMod 3)
    (h1a : u₁ ᵥ* (a : Matrix (Fin d) (Fin d) (ZMod 3)) = u₁)
    (h1b : u₁ ᵥ* (b : Matrix (Fin d) (Fin d) (ZMod 3)) ≠ u₁)
    (h2a : u₂ ᵥ* (a : Matrix (Fin d) (Fin d) (ZMod 3)) = u₂)
    (h2b : u₂ ᵥ* (b : Matrix (Fin d) (Fin d) (ZMod 3)) = u₂)
    (h2c : u₂ ᵥ* (c : Matrix (Fin d) (Fin d) (ZMod 3)) ≠ u₂) :
    27 ∣ Nat.card (MulAction.stabilizer K w) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := MulAction.stabilizer K w
  let ι : S →* GL (Fin d) (ZMod 3) := K.subtype.comp S.subtype
  have hι : Function.Injective ι := fun x y h => Subtype.ext (Subtype.ext h)
  let x : S := ⟨⟨a, ha⟩, mem_stabilizer_of_fix _ hfa⟩
  let y : S := ⟨⟨b, hb⟩, mem_stabilizer_of_fix _ hfb⟩
  let z : S := ⟨⟨c, hc⟩, mem_stabilizer_of_fix _ hfc⟩
  have hx : ι x = a := rfl
  have hy : ι y = b := rfl
  have hz : ι z = c := rfl
  have hox : orderOf x = 3 := orderOf_eq_prime (hι (by rw [map_pow, hx, map_one, ha3]))
    (fun h => ha1 (by rw [← hx, h, map_one]))
  have hoy : orderOf y = 3 := orderOf_eq_prime (hι (by rw [map_pow, hy, map_one, hb3]))
    (fun h => h1b (by rw [show b = 1 by rw [← hy, h, map_one], Units.val_one,
      Matrix.vecMul_one]))
  have hoz : orderOf z = 3 := orderOf_eq_prime (hι (by rw [map_pow, hz, map_one, hc3]))
    (fun h => h2c (by rw [show c = 1 by rw [← hz, h, map_one], Units.val_one,
      Matrix.vecMul_one]))
  have hxy : x * y = y * x := hι (by rw [map_mul, map_mul, hx, hy, hab])
  have hxz : x * z = z * x := hι (by rw [map_mul, map_mul, hx, hz, hac])
  have hyz : y * z = z * y := hι (by rw [map_mul, map_mul, hy, hz, hbc])
  have hyQ : y ∉ zpowers x := by
    intro h
    have hle : zpowers x ≤ fixSub w u₁ := by
      rw [zpowers_le, mem_fixSub]
      exact h1a
    exact h1b ((mem_fixSub y).mp (hle h))
  have hconj1 : ∀ g ∈ zpowers x, y⁻¹ * g * y ∈ zpowers x := by
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have hcomm : x ^ k * y = y * x ^ k := (Commute.zpow_left (show Commute x y from hxy) k).eq
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    exact zpow_mem (mem_zpowers x) k
  have hcard1 := CFSG.Monster.B.Pinned.card_sup_zpowers hoy hyQ hconj1
  rw [Nat.card_zpowers, hox] at hcard1
  set P := zpowers x ⊔ zpowers y with hP
  have hzQ : z ∉ P := by
    intro h
    have hle : P ≤ fixSub w u₂ := by
      refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_fixSub]
      · exact h2a
      · exact h2b
    exact h2c ((mem_fixSub z).mp (hle h))
  have hPC : P ≤ centralizer ({z} : Set S) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
    · exact hxz
    · exact hyz
  have hconj2 : ∀ g ∈ P, z⁻¹ * g * z ∈ P := by
    intro g hg
    have hgz : g * z = z * g := (mem_centralizer_singleton_iff.mp (hPC hg))
    rw [mul_assoc, hgz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hg
  have hcard2 := CFSG.Monster.B.Pinned.card_sup_zpowers hoz hzQ hconj2
  rw [hcard1] at hcard2
  rw [show (27 : ℕ) = 3 * 3 * 3 by norm_num, ← hcard2]
  exact Subgroup.card_subgroup_dvd_card _

end CFSG.HardMathSupport.Foote.E27.OrbitF3
