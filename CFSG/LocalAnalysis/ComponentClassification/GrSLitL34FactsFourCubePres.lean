module

public import CFSG.Certificates.WordPresentation
public import Certificates.Certificate22217
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubeAction

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open Matrix Subgroup CFSG.CosetTable CFSG.Certificates

abbrev Gam (d : V4) : Type := PG 5 (qRels d)

theorem card_gam_le {d : V4} (hd : d = 0 ∨ d = d1) :
    Finite (Gam d) ∧ Nat.card (Gam d) ≤ 512 := by
  rcases hd with rfl | rfl
  · exact Certificates.certificate22217.1
  · exact Certificates.certificate22217.2

noncomputable def pgHom {m : ℕ} {G : Type*} [Group G] (ws : List (List (Fin m × Bool)))
    (x : Fin m → G) (h : ∀ w ∈ ws, signedProd x w = 1) : PG m ws →* G :=
  PresentedGroup.toGroup (f := x) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk_eq_signedProd]
    exact h w hw)

theorem pgHom_of {m : ℕ} {G : Type*} [Group G] (ws : List (List (Fin m × Bool))) (x : Fin m → G)
    (h : ∀ w ∈ ws, signedProd x w = 1) (i : Fin m) : pgHom ws x h (PresentedGroup.of i) = x i :=
  PresentedGroup.toGroup.of _

theorem range_pgHom {m : ℕ} {G : Type*} [Group G] (ws : List (List (Fin m × Bool)))
    (x : Fin m → G) (h : ∀ w ∈ ws, signedProd x w = 1) :
    (pgHom ws x h).range = closure (Set.range x) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext i
  simp [pgHom_of]

theorem signedProd_replicate_letter {m : ℕ} {G : Type*} [Group G] (x : Fin m → G) (i : Fin m)
    (b : Bool) (k : ℕ) :
    signedProd x (List.replicate k (i, b)) = (if b then x i else (x i)⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, signedProd_cons, ih, pow_succ']

@[expose] def e3 (i : Fin 3) : V4 := Pi.single i 1

variable {L : Type*} [Group L] {T : Subgroup L} [hT : T.Normal] (ι : T ≃* Multiplicative V4)

@[expose] noncomputable def gensL (a b : L) : Fin 5 → L :=
  ![(elt ι (e3 0) : L), (elt ι (e3 1) : L), (elt ι (e3 2) : L), a, b]

omit hT in
theorem vec_elt_e3 (v : V4) :
    vec ι (((elt ι (e3 2))⁻¹ ^ (v 2).val) * ((elt ι (e3 1))⁻¹ ^ (v 1).val) *
      ((elt ι (e3 0))⁻¹ ^ (v 0).val)) = -v := by
  simp only [vec_mul, vec_pow, vec_inv, vec_elt, e3]
  have hv : ∀ x : ZMod 4, x.val • (1 : ZMod 4) = x := fun x => by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
  fin_cases r <;> simp [hv]

omit hT in
theorem signedProd_tInv (a b : L) (v : V4) :
    signedProd (gensL ι a b) (tInv v) = ((elt ι v)⁻¹ : T) := by
  have hv : ((elt ι v)⁻¹ : T) =
      ((elt ι (e3 2))⁻¹ ^ (v 2).val) * ((elt ι (e3 1))⁻¹ ^ (v 1).val) *
        ((elt ι (e3 0))⁻¹ ^ (v 0).val) := by
    apply vec_injective ι
    rw [vec_elt_e3, vec_inv, vec_elt]
  rw [hv, tInv, signedProd_append, signedProd_append, signedProd_replicate_letter,
    signedProd_replicate_letter, signedProd_replicate_letter]
  simp only [Bool.false_eq_true, ↓reduceIte, Subgroup.coe_mul, Subgroup.coe_pow,
    Subgroup.coe_inv]
  rfl

omit hT in
theorem gensL_t (a b : L) (i : Fin 3) : gensL ι a b (tLetter i) = (elt ι (e3 i) : L) := by
  fin_cases i <;> rfl

theorem rels_gensL {a b : L} (ha : mat ι a = X0) (hb : mat ι b = Bm) (ha2 : a * a = 1)
    (hb2 : b * b = 1) {d : V4} (hd : (a * b) ^ 4 = (elt ι d : L)) :
    ∀ w ∈ qRels d, signedProd (gensL ι a b) w = 1 := by
  have hcomm := T_comm ι
  have h4 : ∀ i : Fin 3, ((elt ι (e3 i) : L)) ^ 4 = 1 := by
    intro i
    have : (elt ι (e3 i)) ^ 4 = 1 := vec_injective ι (by
      rw [vec_pow, vec_elt, vec_one]
      funext r
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      have : ((4 : ℕ) : ZMod 4) = 0 := by decide
      rw [this, zero_mul])
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hc : ∀ i j : Fin 3, ((elt ι (e3 i) : L)) * (elt ι (e3 j) : L) *
      ((elt ι (e3 i) : L))⁻¹ * ((elt ι (e3 j) : L))⁻¹ = 1 := by
    intro i j
    have := hcomm (elt ι (e3 i)) (elt ι (e3 j))
    have h' := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h'
    rw [h']
    group
  have hact : ∀ {g : L} {M : Mat4}, mat ι g = M → ∀ i : Fin 3,
      g * (elt ι (e3 i) : L) * g⁻¹ * ((elt ι (fun r => M r i))⁻¹ : T) = 1 := by
    intro g M hg i
    have h1 : conjT g (elt ι (e3 i)) = elt ι (fun r => M r i) := by
      apply vec_injective ι
      rw [vec_conj, vec_elt, vec_elt, hg, e3, Matrix.mulVec_single_one]
      rfl
    have h2 : g * (elt ι (e3 i) : L) * g⁻¹ = (elt ι (fun r => M r i) : L) := by
      rw [← h1]
      rfl
    rw [h2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  have hrel : ∀ (g : Fin 5) (M : Mat4), mat ι (gensL ι a b g) = M → ∀ i : Fin 3,
      signedProd (gensL ι a b) (actRel g M i) = 1 := by
    intro g M hM i
    unfold actRel
    rw [signedProd_append, signedProd_tInv]
    have e : signedProd (gensL ι a b) [(g, true), (tLetter i, true), (g, false)] =
        gensL ι a b g * (elt ι (e3 i) : L) * (gensL ι a b g)⁻¹ := by
      simp only [signedProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        ↓reduceIte, Bool.false_eq_true, mul_one, gensL_t, mul_assoc]
    rw [e]
    exact hact hM i
  intro w hw
  simp only [qRels, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · rw [signedProd_replicate_letter]; exact h4 0
  · rw [signedProd_replicate_letter]; exact h4 1
  · rw [signedProd_replicate_letter]; exact h4 2
  · simpa [signedProd, gensL, mul_assoc] using hc 0 1
  · simpa [signedProd, gensL, mul_assoc] using hc 0 2
  · simpa [signedProd, gensL, mul_assoc] using hc 1 2
  · exact hrel 3 X0 ha 0
  · exact hrel 3 X0 ha 1
  · exact hrel 3 X0 ha 2
  · exact hrel 4 Bm hb 0
  · exact hrel 4 Bm hb 1
  · exact hrel 4 Bm hb 2
  · simpa [signedProd, gensL] using ha2
  · simpa [signedProd, gensL] using hb2
  · rw [signedProd_append, signedProd_tInv]
    have e : signedProd (gensL ι a b)
        [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true), (3, true), (4, true)] =
        (a * b) ^ 4 := by
      simp only [signedProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        ↓reduceIte, mul_one]
      show a * (b * (a * (b * (a * (b * (a * b)))))) = (a * b) ^ 4
      rw [pow_succ, pow_succ, pow_succ, pow_one]
      simp only [mul_assoc]
    rw [e, hd, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]

noncomputable def gamHom {a b : L} (ha : mat ι a = X0) (hb : mat ι b = Bm) (ha2 : a * a = 1)
    (hb2 : b * b = 1) {d : V4} (hd : (a * b) ^ 4 = (elt ι d : L)) : Gam d →* L :=
  pgHom (qRels d) (gensL ι a b) (rels_gensL ι ha hb ha2 hb2 hd)

omit hT in
theorem vec_e3 (v : V4) :
    vec ι ((elt ι (e3 0)) ^ (v 0).val * (elt ι (e3 1)) ^ (v 1).val *
      (elt ι (e3 2)) ^ (v 2).val) = v := by
  simp only [vec_mul, vec_pow, vec_elt, e3]
  have hv : ∀ x : ZMod 4, x.val • (1 : ZMod 4) = x := fun x => by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply]
  fin_cases r <;> simp [hv]

@[expose] def d8Mats : List Mat4 :=
  [1, X0, Bm, X0 * Bm, Bm * X0, X0 * Bm * X0, Bm * X0 * Bm, X0 * Bm * X0 * Bm]

theorem d8Mats_nodup : d8Mats.Nodup := by decide

@[expose] def d8Elts (a b : L) : List L :=
  [1, a, b, a * b, b * a, a * b * a, b * a * b, a * b * a * b]

variable {a b : L} (ha : mat ι a = X0) (hb : mat ι b = Bm) (ha2 : a * a = 1) (hb2 : b * b = 1)
  {d : V4} (hd : (a * b) ^ 4 = (elt ι d : L))

include ha hb in
theorem map_d8Elts : (d8Elts a b).map (mat ι) = d8Mats := by
  simp only [d8Elts, d8Mats, List.map_cons, List.map_nil, mat_mul, mat_one, ha, hb]

include ha2 hb2 hd in
theorem T_le_range : T ≤ (gamHom ι ha hb ha2 hb2 hd).range := by
  intro t ht
  have hgen : ∀ i : Fin 5, gensL ι a b i ∈ (gamHom ι ha hb ha2 hb2 hd).range :=
    fun i => ⟨PresentedGroup.of i, pgHom_of _ _ _ i⟩
  have e : (⟨t, ht⟩ : T) = (elt ι (e3 0)) ^ ((vec ι ⟨t, ht⟩) 0).val *
      (elt ι (e3 1)) ^ ((vec ι ⟨t, ht⟩) 1).val * (elt ι (e3 2)) ^ ((vec ι ⟨t, ht⟩) 2).val :=
    vec_injective ι (by rw [vec_e3])
  have := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_pow] at this
  rw [this]
  exact mul_mem (mul_mem (pow_mem (hgen 0) _) (pow_mem (hgen 1) _)) (pow_mem (hgen 2) _)

include ha2 hb2 hd in
theorem d8Elts_mem : ∀ g ∈ d8Elts a b, g ∈ (gamHom ι ha hb ha2 hb2 hd).range := by
  have h3 : a ∈ (gamHom ι ha hb ha2 hb2 hd).range := ⟨PresentedGroup.of 3, pgHom_of _ _ _ 3⟩
  have h4 : b ∈ (gamHom ι ha hb ha2 hb2 hd).range := ⟨PresentedGroup.of 4, pgHom_of _ _ _ 4⟩
  intro g hg
  simp only [d8Elts, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact one_mem _
    | exact h3
    | exact h4
    | exact mul_mem h3 h4
    | exact mul_mem h4 h3
    | exact mul_mem (mul_mem h3 h4) h3
    | exact mul_mem (mul_mem h4 h3) h4
    | exact mul_mem (mul_mem (mul_mem h3 h4) h3) h4

omit hT in
include ι in
theorem card_T : Nat.card T = 64 := by
  rw [Nat.card_congr ι.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

include ha hb ha2 hb2 hd in
theorem card_range_ge [Finite L] : 512 ≤ Nat.card (gamHom ι ha hb ha2 hb2 hd).range := by
  set H := (gamHom ι ha hb ha2 hb2 hd).range with hH
  have hmem := d8Elts_mem ι ha hb ha2 hb2 hd
  have hT := T_le_range ι ha hb ha2 hb2 hd
  have hlen : (d8Elts a b).length = 8 := rfl
  let F : Fin 8 × T → H := fun p =>
    ⟨(d8Elts a b)[p.1.val]'(by rw [hlen]; exact p.1.2) * p.2,
      mul_mem (hmem _ (List.getElem_mem _)) (hT p.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨k, t⟩ ⟨k', t'⟩ he
    have he' : (d8Elts a b)[k.val]'(by rw [hlen]; exact k.2) * (t : L) =
        (d8Elts a b)[k'.val]'(by rw [hlen]; exact k'.2) * (t' : L) := congrArg Subtype.val he
    have hm := congrArg (mat ι) he'
    rw [mat_mul, mat_mul, mat_of_mem ι t.2, mat_of_mem ι t'.2, mul_one, mul_one] at hm
    have hk : k = k' := by
      have hmap := map_d8Elts ι ha hb
      have e1 : mat ι ((d8Elts a b)[k.val]'(by rw [hlen]; exact k.2)) = d8Mats[k.val]'(by
          rw [← hmap, List.length_map, hlen]; exact k.2) := by
        simp only [← hmap, List.getElem_map]
      have e2 : mat ι ((d8Elts a b)[k'.val]'(by rw [hlen]; exact k'.2)) = d8Mats[k'.val]'(by
          rw [← hmap, List.length_map, hlen]; exact k'.2) := by
        simp only [← hmap, List.getElem_map]
      rw [e1, e2] at hm
      exact Fin.ext ((List.Nodup.getElem_inj_iff d8Mats_nodup).1 hm)
    subst hk
    refine Prod.ext rfl (Subtype.ext (mul_left_cancel he'))
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin, card_T ι] at this

include ha hb ha2 hb2 hd in
theorem gamHom_injective [Finite L] (hfin : Finite (Gam d)) (hcard : Nat.card (Gam d) ≤ 512) :
    Function.Injective (gamHom ι ha hb ha2 hb2 hd) := by
  have hsurj : Function.Surjective (gamHom ι ha hb ha2 hb2 hd).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hbij := hsurj.bijective_of_nat_card_le (hcard.trans (card_range_ge ι ha hb ha2 hb2 hd))
  intro g g' hgg
  exact hbij.1 (Subtype.ext hgg)

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
