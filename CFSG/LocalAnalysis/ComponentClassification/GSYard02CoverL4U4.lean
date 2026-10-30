module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverGH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02NotGen4

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Matrix CFSG.GH74.L5U5 CFSG.Open

section Join

variable {G : Type} [Group G]

@[expose] def l4uKlein {x z : G} (hx : x * x = 1) (hz : z * z = 1) (hxz : x * z = z * x) :
    Subgroup G where
  carrier := {g | g = 1 ∨ g = x ∨ g = z ∨ g = x * z}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    have hzx : z * x = x * z := hxz.symm
    have hx' : ∀ g : G, x * (x * g) = g := fun g => by rw [← mul_assoc, hx, one_mul]
    have hz' : ∀ g : G, z * (z * g) = g := fun g => by rw [← mul_assoc, hz, one_mul]
    have hzx' : ∀ g : G, z * (x * g) = x * (z * g) := fun g => by
      rw [← mul_assoc, hzx, mul_assoc]
    show a * b = 1 ∨ a * b = x ∨ a * b = z ∨ a * b = x * z
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
      simp [mul_assoc, hx, hz, hx', hz', hzx, hzx']
  inv_mem' := by
    intro a ha
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
    show a⁻¹ = 1 ∨ a⁻¹ = x ∨ a⁻¹ = z ∨ a⁻¹ = x * z
    rcases ha with ha | ha | ha | ha
    · exact Or.inl (by rw [ha, inv_one])
    · exact Or.inr (Or.inl (by rw [ha, hxi]))
    · exact Or.inr (Or.inr (Or.inl (by rw [ha, hzi])))
    · exact Or.inr (Or.inr (Or.inr (by rw [ha, _root_.mul_inv_rev, hxi, hzi, hxz])))

theorem wp1_mem_klein {x z : G} (hx : x * x = 1) (hz : z * z = 1) (hxz : x * z = z * x)
    {g : G} : g ∈ l4uKlein hx hz hxz ↔ g = 1 ∨ g = x ∨ g = z ∨ g = x * z := Iff.rfl

theorem wp1_xz_sq {x z : G} (hx : x * x = 1) (hz : z * z = 1) (hxz : x * z = z * x) :
    (x * z) ^ 2 = 1 := by
  have hc : Commute x z := hxz
  rw [hc.mul_pow, sq x, sq z, hx, hz, one_mul]

theorem l4uKlein_isKleinFour {x z : G} (hx : x * x = 1) (hz : z * z = 1)
    (hxz : x * z = z * x) (hx1 : x ≠ 1) (hz1 : z ≠ 1) (hxz' : x ≠ z) :
    IsKleinFour (l4uKlein hx hz hxz) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ ?_
  · have hset : ((l4uKlein hx hz hxz : Subgroup G) : Set G) = {1, x, z, x * z} := by
      ext g
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact wp1_mem_klein hx hz hxz
    have hne1x : (1 : G) ≠ x := fun h => hx1 h.symm
    have hne1z : (1 : G) ≠ z := fun h => hz1 h.symm
    have hne1xz : (1 : G) ≠ x * z := fun h => hxz' (mul_right_cancel (h.symm.trans hz.symm))
    have hnexxz : x ≠ x * z := fun h => hz1 (mul_left_cancel (h.symm.trans (mul_one x).symm))
    have hnezxz : z ≠ x * z := fun h => hx1 (mul_right_cancel (h.symm.trans (one_mul z).symm))
    have h1 : (1 : G) ∉ ({x, z, x * z} : Set G) := by
      rintro (h | h | h)
      · exact hne1x h
      · exact hne1z h
      · exact hne1xz h
    have h2 : x ∉ ({z, x * z} : Set G) := by
      rintro (h | h)
      · exact hxz' h
      · exact hnexxz h
    have h3 : z ∉ ({x * z} : Set G) := fun h => hnezxz h
    have e1 := Set.ncard_insert_of_notMem h1
    have e2 := Set.ncard_insert_of_notMem h2
    have e3 := Set.ncard_insert_of_notMem h3
    have e4 := Set.ncard_singleton (x * z)
    calc Nat.card (l4uKlein hx hz hxz)
        = ((l4uKlein hx hz hxz : Subgroup G) : Set G).ncard :=
          Nat.card_coe_set_eq ((l4uKlein hx hz hxz : Subgroup G) : Set G)
      _ = ({1, x, z, x * z} : Set G).ncard := by rw [hset]
      _ = 4 := by omega
  · intro g hg
    rcases (wp1_mem_klein hx hz hxz).1 hg with h | h | h | h
    · rw [h, one_pow]
    · rw [h, sq]; exact hx
    · rw [h, sq]; exact hz
    · rw [h]; exact wp1_xz_sq hx hz hxz

theorem l4u_exists_nontriv {E : Subgroup G} (hE : IsKleinFour E) (z : G) :
    ∃ e ∈ E, e ≠ 1 ∧ e ≠ z := by
  by_contra hcon
  have hcon' : ∀ e ∈ E, e = 1 ∨ e = z := by
    intro e he
    by_contra h
    push Not at h
    exact hcon ⟨e, he, h.1, h.2⟩
  have hsub : (E : Set G) ⊆ {1, z} := by
    intro e he
    rcases hcon' e he with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h4 : Nat.card E = 4 := hE.card_four
  have hle : (E : Set G).ncard ≤ ({1, z} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, z} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({z} : Set G)
    rw [Set.ncard_singleton] at this
    exact this
  have h5 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  omega

theorem wp1_comm_of_kf {E : Subgroup G} (hE : IsKleinFour E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x :=
  FooteLit.commute_of_sq_eq_one (fun _ h => FooteLit.sq_eq_one_of_isKleinFour hE h) hx hy

theorem wp1_comm_klein {x z c : G} (hx : x * x = 1) (hz : z * z = 1) (hxz : x * z = z * x)
    (hcx : c * x = x * c) (hcz : c * z = z * c) {g : G} (hg : g ∈ l4uKlein hx hz hxz) :
    c * g = g * c := by
  rcases (wp1_mem_klein hx hz hxz).1 hg with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact hcx
  · rw [h]; exact hcz
  · rw [h]
    calc c * (x * z) = (c * x) * z := (mul_assoc _ _ _).symm
      _ = (x * c) * z := by rw [hcx]
      _ = x * (c * z) := mul_assoc _ _ _
      _ = x * (z * c) := by rw [hcz]
      _ = (x * z) * c := (mul_assoc _ _ _).symm

theorem wp1_le_cent {B : Subgroup G} {y z : G} (hy : y * y = 1) (hz : z * z = 1)
    (hyz : y * z = z * y) (hBy : ∀ g ∈ B, g * y = y * g) (hBz : ∀ g ∈ B, g * z = z * g) :
    B ≤ Subgroup.centralizer (l4uKlein hy hz hyz : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (wp1_comm_klein hy hz hyz (hBy g hg) (hBz g hg) hk).symm

theorem wp1_adj {x y z : G} (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxz : x * z = z * x) (hyz : y * z = z * y) (hzc : ∀ g : G, z * g = g * z)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hz1 : z ≠ 1) (hxz' : x ≠ z)
    (hyz' : y ≠ z) :
    CommFourAdj G (l4uKlein hx hz hxz) (l4uKlein hy hz hyz) :=
  ⟨l4uKlein_isKleinFour hx hz hxz hx1 hz1 hxz', l4uKlein_isKleinFour hy hz hyz hy1 hz1 hyz',
    wp1_le_cent hy hz hyz
      (fun _ hg => (wp1_comm_klein hx hz hxz hxy.symm hyz hg).symm)
      (fun g _ => (hzc g).symm)⟩

theorem l4u_join {S : Subgroup G} {z d : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ g : G, z * g = g * z)
    (hd2 : d * d = 1) (hd1 : d ≠ 1) (hdz : d ≠ z)
    (hgood : ∀ e ∈ S, e * e = 1 → e ≠ 1 → e ≠ z →
      e * d = d * e ∨ ∃ y ∈ S, y * y = 1 ∧ y ≠ 1 ∧ y ≠ z ∧ y * d = d * y ∧ y * e = e * y)
    (E F : Subgroup G) (hE : IsKleinFour E) (hES : E ≤ S) (hF : IsKleinFour F) (hFS : F ≤ S) :
    Relation.ReflTransGen (CommFourAdj G) E F := by
  have hdz' : d * z = z * d := (hzc d).symm
  have key : ∀ E' : Subgroup G, IsKleinFour E' → E' ≤ S →
      Relation.ReflTransGen (CommFourAdj G) E' (l4uKlein hd2 hz2 hdz') := by
    intro E' hE' hES'
    obtain ⟨e, heE, he1, hez⟩ := l4u_exists_nontriv hE' z
    have he2 : e * e = 1 := (sq e).symm.trans (FooteLit.sq_eq_one_of_isKleinFour hE' heE)
    have hez' : e * z = z * e := (hzc e).symm
    have hWe : CommFourAdj G E' (l4uKlein he2 hz2 hez') :=
      ⟨hE', l4uKlein_isKleinFour he2 hz2 hez' he1 hz1 hez,
        wp1_le_cent he2 hz2 hez' (fun g hg => wp1_comm_of_kf hE' hg heE)
          (fun g _ => (hzc g).symm)⟩
    have step1 : Relation.ReflTransGen (CommFourAdj G) E' (l4uKlein he2 hz2 hez') :=
      Relation.ReflTransGen.single hWe
    rcases hgood e (hES' heE) he2 he1 hez with hed | ⟨y, hyS, hy2, hy1, hyz, hyd, hye⟩
    · exact step1.tail (wp1_adj he2 hd2 hz2 hez' hdz' hzc hed he1 hd1 hz1 hez hdz)
    · have hyz' : y * z = z * y := (hzc y).symm
      exact (step1.tail (wp1_adj he2 hy2 hz2 hez' hyz' hzc hye.symm he1 hy1 hz1 hez hyz)).tail
        (wp1_adj hy2 hd2 hz2 hyz' hdz' hzc hyd hy1 hd1 hz1 hyz hdz)
  exact (key E hE hES).trans (reflTransGen_commFourAdj_symm (key F hF hFS))

end Join

section Block

variable {F : Type} [Field F]

theorem wp2a_diag_sq :
    (Matrix.diagonal ![(1 : F), -1] : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal ![(1 : F), -1] =
      1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem wp2a_det_mul (a b : GL (Fin 2) F) :
    ((a * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det := by
  rw [Units.val_mul, Matrix.det_mul]

theorem wp2a_det_inv (a : GL (Fin 2) F) :
    ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ((a : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
  have h := wp2a_det_mul a a⁻¹
  rw [mul_inv_cancel, Units.val_one, Matrix.det_one] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

theorem wp2a_swap_mul_diag (a b : GL (Fin 2) F) :
    swapGL F * diagGL a b = diagGL b a * swapGL F := by
  have h := swapGL_mul_diagGL_mul_inv (F := F) a b
  rw [swapGL_inv] at h
  rw [← h, mul_assoc, swapGL_mul_self, mul_one]

theorem wp2a_diag_swap_mul_diag (a b a' b' : GL (Fin 2) F) :
    diagGL a b * swapGL F * diagGL a' b' = diagGL (a * b') (b * a') * swapGL F := by
  rw [mul_assoc, wp2a_swap_mul_diag, ← mul_assoc, diagGL_mul]

@[expose] def reflGL2 : GL (Fin 2) F :=
  Units.mk (Matrix.diagonal ![1, -1]) (Matrix.diagonal ![1, -1]) wp2a_diag_sq wp2a_diag_sq

@[expose] def l4uS (D : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 4) F) where
  carrier := {g | ∃ a ∈ D, ∃ b ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det =
      (b : Matrix (Fin 2) (Fin 2) F).det ∧ (g = diagGL a b ∨ g = diagGL a b * swapGL F)}
  one_mem' := ⟨1, D.one_mem, 1, D.one_mem, rfl, Or.inl diagGL_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, hab, rfl | rfl⟩ ⟨a', ha', b', hb', hab', rfl | rfl⟩
    · refine ⟨a * a', D.mul_mem ha ha', b * b', D.mul_mem hb hb', ?_, Or.inl ?_⟩
      · rw [wp2a_det_mul, wp2a_det_mul, hab, hab']
      · rw [diagGL_mul]
    · refine ⟨a * a', D.mul_mem ha ha', b * b', D.mul_mem hb hb', ?_, Or.inr ?_⟩
      · rw [wp2a_det_mul, wp2a_det_mul, hab, hab']
      · rw [← mul_assoc, diagGL_mul]
    · refine ⟨a * b', D.mul_mem ha hb', b * a', D.mul_mem hb ha', ?_, Or.inr ?_⟩
      · rw [wp2a_det_mul, wp2a_det_mul, hab, hab']
      · rw [wp2a_diag_swap_mul_diag]
    · refine ⟨a * b', D.mul_mem ha hb', b * a', D.mul_mem hb ha', ?_, Or.inl ?_⟩
      · rw [wp2a_det_mul, wp2a_det_mul, hab, hab']
      · rw [← mul_assoc, wp2a_diag_swap_mul_diag, mul_assoc, swapGL_mul_self, mul_one]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, hab, rfl | rfl⟩
    · refine ⟨a⁻¹, D.inv_mem ha, b⁻¹, D.inv_mem hb, ?_, Or.inl ?_⟩
      · rw [wp2a_det_inv, wp2a_det_inv, hab]
      · rw [diagGL_inv]
    · refine ⟨b⁻¹, D.inv_mem hb, a⁻¹, D.inv_mem ha, ?_, Or.inr ?_⟩
      · rw [wp2a_det_inv, wp2a_det_inv, hab]
      · rw [_root_.mul_inv_rev, swapGL_inv, diagGL_inv, wp2a_swap_mul_diag]

private theorem wp2b_coe_refl :
    ((reflGL2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![1, -1] := rfl

theorem wp2b_refl_sq : (reflGL2 : GL (Fin 2) F) * reflGL2 = 1 := by
  apply Units.ext
  rw [Units.val_mul, wp2b_coe_refl, Matrix.diagonal_mul_diagonal, Units.val_one,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem wp2b_det_refl :
    ((reflGL2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  rw [wp2b_coe_refl, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem wp2b_det_neg_one :
    ((-1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Units.val_neg, Units.val_one]
  simp [Matrix.det_neg]

theorem wp2b_mem_l4uS {D : Subgroup (GL (Fin 2) F)} {g : GL (Fin 4) F} :
    g ∈ l4uS D ↔ ∃ a ∈ D, ∃ b ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det =
      (b : Matrix (Fin 2) (Fin 2) F).det ∧ (g = diagGL a b ∨ g = diagGL a b * swapGL F) :=
  Iff.rfl

theorem wp2b_swap_mul_diag (a b : GL (Fin 2) F) :
    swapGL F * diagGL a b = diagGL b a * swapGL F := by
  rw [← swapGL_mul_diagGL_mul_inv a b, inv_mul_cancel_right]

theorem wp2b_diag_comm_xy (a b : GL (Fin 2) F) :
    diagGL a b * xyGL F = xyGL F * diagGL a b := by
  rw [xyGL, diagGL_mul, diagGL_mul, mul_one, one_mul, mul_neg_one, neg_one_mul]

theorem l4uS_le_K4 (M : ModelData F) {D : Subgroup (GL (Fin 2) F)} (hD : ∀ a ∈ D, a ∈ M.U2)
    (hdet : ∀ a ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
      (a : Matrix (Fin 2) (Fin 2) F).det = -1) : l4uS D ≤ M.K4 := by
  intro g hg
  obtain ⟨a, ha, b, hb, hab, rfl | rfl⟩ := wp2b_mem_l4uS.1 hg
  · rw [M.mem_K4, det_diagGL, ← hab]
    refine ⟨(M.diag_mem_iff a b).2 ⟨hD a ha, hD b hb⟩, ?_⟩
    rcases hdet a ha with h | h <;> rw [h] <;> norm_num
  · rw [M.mem_K4, Units.val_mul, Matrix.det_mul, det_diagGL, coe_swapGL, det_wMat, ← hab]
    refine ⟨M.U4.mul_mem ((M.diag_mem_iff a b).2 ⟨hD a ha, hD b hb⟩) M.swap_mem, ?_⟩
    rcases hdet a ha with h | h <;> rw [h] <;> norm_num

theorem l4uS_good (M : ModelData F) (h2 : (2 : F) ≠ 0) {D : Subgroup (GL (Fin 2) F)}
    (hD : ∀ a ∈ D, a ∈ M.U2)
    (hdet : ∀ a ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
      (a : Matrix (Fin 2) (Fin 2) F).det = -1) (hrefl : reflGL2 ∈ D) :
    ∀ e ∈ l4uS D, e * e = 1 → e ≠ 1 → e ≠ xGL F →
      e * xyGL F = xyGL F * e ∨ ∃ y ∈ l4uS D, y * y = 1 ∧ y ≠ 1 ∧ y ≠ xGL F ∧
        y * xyGL F = xyGL F * y ∧ y * e = e * y := by
  intro e he he2 _ _
  obtain ⟨a, ha, b, -, -, rfl | rfl⟩ := wp2b_mem_l4uS.1 he
  · exact Or.inl (wp2b_diag_comm_xy a b)
  right
  have hee : diagGL a b * swapGL F * (diagGL a b * swapGL F) = diagGL (a * b) (b * a) := by
    rw [mul_assoc, ← mul_assoc (swapGL F), wp2b_swap_mul_diag, mul_assoc, swapGL_mul_self,
      mul_one, diagGL_mul]
  rw [hee, ← diagGL_one] at he2
  obtain rfl : b = a⁻¹ := eq_inv_of_mul_eq_one_right (diagGL_inj he2).1
  have hF : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hcD : a⁻¹ * reflGL2 * a ∈ D := D.mul_mem (D.mul_mem (D.inv_mem ha) hrefl) ha
  have hdetc : ((reflGL2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ((a⁻¹ * reflGL2 * a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']
  have hc2 : a⁻¹ * reflGL2 * a * (a⁻¹ * reflGL2 * a) = 1 := by
    calc a⁻¹ * reflGL2 * a * (a⁻¹ * reflGL2 * a) = a⁻¹ * (reflGL2 * reflGL2) * a := by group
      _ = 1 := by rw [wp2b_refl_sq, mul_one, inv_mul_cancel]
  refine ⟨diagGL reflGL2 (a⁻¹ * reflGL2 * a),
    wp2b_mem_l4uS.2 ⟨reflGL2, hrefl, _, hcD, hdetc, Or.inl rfl⟩, ?_, ?_, ?_,
    wp2b_diag_comm_xy _ _, ?_⟩
  · rw [diagGL_mul, wp2b_refl_sq, hc2, diagGL_one]
  · intro h
    rw [← diagGL_one] at h
    have h' := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F).det)
      (diagGL_inj h).1
    simp only [wp2b_det_refl, Units.val_one, Matrix.det_one] at h'
    exact hF h'
  · intro h
    rw [xGL] at h
    have h' := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F).det)
      (diagGL_inj h).1
    simp only [wp2b_det_refl, wp2b_det_neg_one] at h'
    exact hF h'
  · have e1 : reflGL2 * a = a * (a⁻¹ * reflGL2 * a) := by group
    have e2 : a⁻¹ * reflGL2 * a * a⁻¹ = a⁻¹ * reflGL2 := by group
    rw [mul_assoc (diagGL a a⁻¹), wp2b_swap_mul_diag, ← mul_assoc, ← mul_assoc, diagGL_mul,
      diagGL_mul, e1, e2]

theorem wp3_det_reflGL2 : ((reflGL2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  show (Matrix.diagonal ![(1 : F), -1]).det = -1
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem wp3_neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have h' := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h'
  exact h2 (by linear_combination -h')

theorem wp3_swapGL_ne_diagGL (h2 : (2 : F) ≠ 0) (a b : GL (Fin 2) F) :
    swapGL F ≠ diagGL a b := by
  intro h
  have key := swapGL_mul_diagGL_mul_inv (F := F) (-1) 1
  rw [h, diagGL_inv, diagGL_mul, diagGL_mul] at key
  have e1 : a * -1 * a⁻¹ = (-1 : GL (Fin 2) F) := by
    rw [mul_neg_one, neg_mul, mul_inv_cancel]
  have e2 : b * 1 * b⁻¹ = (1 : GL (Fin 2) F) := by
    rw [mul_one, mul_inv_cancel]
  rw [e1, e2] at key
  exact wp3_neg_one_ne_one h2 (diagGL_inj key).1

theorem wp3_diagGL_ne_diagGL_mul_swapGL (h2 : (2 : F) ≠ 0) (a b a' b' : GL (Fin 2) F) :
    diagGL a b ≠ diagGL a' b' * swapGL F := by
  intro h
  have hs : swapGL F = (diagGL a' b')⁻¹ * diagGL a b := eq_inv_mul_of_mul_eq h.symm
  rw [diagGL_inv, diagGL_mul] at hs
  exact wp3_swapGL_ne_diagGL h2 _ _ hs

theorem wp3_card_half {α : Type*} [Finite α] (P : α → Prop) (e : α ≃ α)
    (h : ∀ a, P a ↔ ¬ P (e a)) : Nat.card {a // P a} * 2 = Nat.card α := by
  classical
  have h1 : Nat.card {a // P a} = Nat.card {a // ¬ P a} :=
    Nat.card_congr (e.subtypeEquiv (p := P) (q := fun a => ¬ P a) h)
  rw [Nat.card_congr (Equiv.sumCompl P).symm, Nat.card_sum, ← h1, mul_two]

theorem wp3_card_pairs [Finite F] {D : Subgroup (GL (Fin 2) F)} (h2 : (2 : F) ≠ 0)
    (hdet : ∀ a ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
      (a : Matrix (Fin 2) (Fin 2) F).det = -1) (hrefl : reflGL2 ∈ D) :
    Nat.card {p : ↥D × ↥D // ((p.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ((p.2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det} * 2 = Nat.card D ^ 2 := by
  have h1 : (1 : F) ≠ -1 := fun h => h2 (by linear_combination h)
  rw [sq, ← Nat.card_prod]
  refine wp3_card_half _ ((Equiv.mulRight (⟨reflGL2, hrefl⟩ : ↥D)).prodCongr (Equiv.refl _)) ?_
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  show (a : Matrix (Fin 2) (Fin 2) F).det = (b : Matrix (Fin 2) (Fin 2) F).det ↔
    ¬ ((a * reflGL2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (b : Matrix (Fin 2) (Fin 2) F).det
  rw [Units.val_mul, Matrix.det_mul, wp3_det_reflGL2]
  rcases hdet a ha with h | h <;> rcases hdet b hb with h' | h' <;> simp [h, h', h1, h1.symm]

theorem wp3_card_l4uS_eq [Finite F] {D : Subgroup (GL (Fin 2) F)} (h2 : (2 : F) ≠ 0) :
    Nat.card (l4uS D) = Nat.card {p : ↥D × ↥D // ((p.1 : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = ((p.2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det} *
        2 := by
  let f : {p : ↥D × ↥D // ((p.1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ((p.2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det} × Bool → ↥(l4uS D) := fun q =>
    ⟨bif q.2 then diagGL (q.1.1.1 : GL (Fin 2) F) q.1.1.2 * swapGL F
      else diagGL (q.1.1.1 : GL (Fin 2) F) q.1.1.2,
      q.1.1.1, q.1.1.1.2, q.1.1.2, q.1.1.2.2, q.1.2, by cases q.2 <;> simp⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨⟨a, b⟩, hab⟩, _ | _⟩ ⟨⟨⟨a', b'⟩, hab'⟩, _ | _⟩ h <;>
      have h' := congrArg Subtype.val h
    · have hh : diagGL (a : GL (Fin 2) F) b = diagGL a' b' := h'
      obtain ⟨e1, e2⟩ := diagGL_inj hh
      obtain rfl : a = a' := Subtype.ext e1
      obtain rfl : b = b' := Subtype.ext e2
      rfl
    · exact absurd h' (wp3_diagGL_ne_diagGL_mul_swapGL h2 _ _ _ _)
    · exact absurd h'.symm (wp3_diagGL_ne_diagGL_mul_swapGL h2 _ _ _ _)
    · have hh : diagGL (a : GL (Fin 2) F) b = diagGL a' b' := mul_right_cancel h'
      obtain ⟨e1, e2⟩ := diagGL_inj hh
      obtain rfl : a = a' := Subtype.ext e1
      obtain rfl : b = b' := Subtype.ext e2
      rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨g, a, ha, b, hb, hab, rfl | rfl⟩
    · exact ⟨(⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩, false), rfl⟩
    · exact ⟨(⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩, true), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

theorem card_l4uS [Finite F] {D : Subgroup (GL (Fin 2) F)} (h2 : (2 : F) ≠ 0)
    (hdet : ∀ a ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
      (a : Matrix (Fin 2) (Fin 2) F).det = -1) (hrefl : reflGL2 ∈ D) :
    Nat.card (l4uS D) = Nat.card D ^ 2 := by
  rw [wp3_card_l4uS_eq h2]
  exact wp3_card_pairs h2 hdet hrefl

end Block

section Sylow

variable {F : Type} [Field F]

theorem wp4_reflGL2_coe :
    ((reflGL2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![1, -1] := by
  first
    | simp [reflGL2]
    | (unfold reflGL2; rfl)
    | (delta reflGL2; rfl)

theorem wp4_reflGL2_mul_self : (reflGL2 : GL (Fin 2) F) * reflGL2 = 1 := by
  apply Units.ext
  rw [Units.val_mul, wp4_reflGL2_coe, Matrix.diagonal_mul_diagonal, Units.val_one]
  first
    | (ext i j; fin_cases i <;> fin_cases j <;> simp)
    | (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.one_apply])

theorem wp4_reflGL2_ne_one (h2 : (2 : F) ≠ 0) : (reflGL2 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have h' : (-1 : F) = 1 := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 1) h
    simpa [wp4_reflGL2_coe] using this
  exact h2 (by linear_combination -h')

theorem wp4_neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have h' : (-1 : F) = 1 := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simpa using this
  exact h2 (by linear_combination -h')

theorem wp4_reflGL2_ne_neg_one (h2 : (2 : F) ≠ 0) : (reflGL2 : GL (Fin 2) F) ≠ -1 := by
  intro h
  have h' : (1 : F) = -1 := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simpa [wp4_reflGL2_coe] using this
  exact h2 (by linear_combination h')

theorem wp4_mem_klein {G : Type} [Group G] {x z : G} (hx : x * x = 1) (hz : z * z = 1)
    (hxz : x * z = z * x) {g : G} :
    g ∈ l4uKlein hx hz hxz ↔ g = 1 ∨ g = x ∨ g = z ∨ g = x * z := by
  first
    | exact Iff.rfl
    | simp [l4uKlein]

theorem wp4_klein_sylow [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hrefl : reflGL2 ∈ M.U2) :
    ∃ Q : Sylow 2 ↥M.U2, (⟨reflGL2, hrefl⟩ : ↥M.U2) ∈ Q.toSubgroup ∧
      (⟨-1, M.neg_mem⟩ : ↥M.U2) ∈ Q.toSubgroup := by
  haveI : Finite (GL (Fin 2) F) :=
    Finite.of_injective (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
      Units.val_injective
  have hx : (⟨reflGL2, hrefl⟩ : ↥M.U2) * ⟨reflGL2, hrefl⟩ = 1 :=
    Subtype.ext (show (reflGL2 : GL (Fin 2) F) * reflGL2 = 1 from wp4_reflGL2_mul_self)
  have hz : (⟨-1, M.neg_mem⟩ : ↥M.U2) * ⟨-1, M.neg_mem⟩ = 1 :=
    Subtype.ext (show (-1 : GL (Fin 2) F) * -1 = 1 by simp)
  have hxz : (⟨reflGL2, hrefl⟩ : ↥M.U2) * ⟨-1, M.neg_mem⟩ =
      ⟨-1, M.neg_mem⟩ * ⟨reflGL2, hrefl⟩ :=
    Subtype.ext (show (reflGL2 : GL (Fin 2) F) * -1 = -1 * reflGL2 by simp)
  have hx1 : (⟨reflGL2, hrefl⟩ : ↥M.U2) ≠ 1 := fun h =>
    wp4_reflGL2_ne_one h2 (congrArg Subtype.val h)
  have hz1 : (⟨-1, M.neg_mem⟩ : ↥M.U2) ≠ 1 := fun h =>
    wp4_neg_one_ne_one h2 (congrArg Subtype.val h)
  have hxz' : (⟨reflGL2, hrefl⟩ : ↥M.U2) ≠ ⟨-1, M.neg_mem⟩ := fun h =>
    wp4_reflGL2_ne_neg_one h2 (congrArg Subtype.val h)
  haveI hK : IsKleinFour ↥(l4uKlein hx hz hxz) :=
    l4uKlein_isKleinFour hx hz hxz hx1 hz1 hxz'
  have h4 : Nat.card ↥(l4uKlein hx hz hxz) = 4 := IsKleinFour.card_four
  have hcard : Nat.card ↥(l4uKlein hx hz hxz) = 2 ^ 2 := h4.trans (by norm_num)
  have hP : IsPGroup 2 ↥(l4uKlein hx hz hxz) := IsPGroup.iff_card.2 ⟨2, hcard⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  exact ⟨Q, hQ ((wp4_mem_klein hx hz hxz).2 (Or.inr (Or.inl rfl))),
    hQ ((wp4_mem_klein hx hz hxz).2 (Or.inr (Or.inr (Or.inl rfl))))⟩

theorem exists_D_of_model [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hrefl : reflGL2 ∈ M.U2)
    (hdet2 : ∀ a ∈ M.U2, ∀ k : ℕ, a ^ (2 ^ k) = 1 →
      (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨ (a : Matrix (Fin 2) (Fin 2) F).det = -1) :
    ∃ D : Subgroup (GL (Fin 2) F), (∀ a ∈ D, a ∈ M.U2) ∧ (-1 : GL (Fin 2) F) ∈ D ∧
      reflGL2 ∈ D ∧ (∀ a ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
        (a : Matrix (Fin 2) (Fin 2) F).det = -1) ∧
      ∃ k t : ℕ, Nat.card D = 2 ^ k ∧ Odd t ∧ Nat.card M.U2 = 2 ^ k * t := by
  haveI : Finite (GL (Fin 2) F) :=
    Finite.of_injective (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
      Units.val_injective
  obtain ⟨Q, hxQ, hzQ⟩ := wp4_klein_sylow M h2 hrefl
  have hD : IsPGroup 2 ↥(Q.toSubgroup.map M.U2.subtype) := Q.isPGroup'.map M.U2.subtype
  have hmemU : ∀ a ∈ Q.toSubgroup.map M.U2.subtype, a ∈ M.U2 := by
    rintro a ⟨x, -, rfl⟩
    first
      | exact x.2
      | simpa using x.2
  refine ⟨Q.toSubgroup.map M.U2.subtype, hmemU,
    Subgroup.mem_map.2 ⟨⟨-1, M.neg_mem⟩, hzQ, rfl⟩,
    Subgroup.mem_map.2 ⟨⟨reflGL2, hrefl⟩, hxQ, rfl⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨k, hk⟩ := hD ⟨a, ha⟩
    refine hdet2 a (hmemU a ha) k ?_
    simpa using congrArg Subtype.val hk
  · have hn : Nat.card ↥M.U2 ≠ 0 := Nat.card_pos.ne'
    refine ⟨(Nat.card ↥M.U2).factorization 2,
      Nat.card ↥M.U2 / 2 ^ (Nat.card ↥M.U2).factorization 2, ?_, ?_, ?_⟩
    · have hcardQ : Nat.card ↥Q.toSubgroup = 2 ^ (Nat.card ↥M.U2).factorization 2 :=
        Q.card_eq_multiplicity
      rw [Subgroup.card_map_of_injective M.U2.subtype_injective, hcardQ]
    · exact Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two hn)
    · exact (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm

theorem card_K4_eq_sq [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hU : ∃ c : ℕ, Odd c ∧ Nat.card M.U2 = 2 * Nat.card M.H2 * c)
    (hK4 : ∃ m : ℕ, Odd m ∧ Nat.card M.K4 = 2 * (Nat.card M.U2 * Nat.card M.H2) * m)
    {k t : ℕ} (hUt : Nat.card M.U2 = 2 ^ k * t) (ht : Odd t) :
    ∃ t' : ℕ, Odd t' ∧ Nat.card M.K4 = 2 ^ (2 * k) * t' := by
  obtain ⟨c, hc, hUc⟩ := hU
  obtain ⟨m, hm, hKm⟩ := hK4
  have arith : ∀ {u v K c₀ m₀ k₀ t₀ : ℕ}, Odd c₀ → Odd m₀ → Odd t₀ →
      u = 2 * v * c₀ → K = 2 * (u * v) * m₀ → u = 2 ^ k₀ * t₀ →
      ∃ t' : ℕ, Odd t' ∧ K = 2 ^ (2 * k₀) * t' := by
    intro u v K c₀ m₀ k₀ t₀ hc₀ hm₀ ht₀ e1 e2 e3
    have key : K * c₀ = 2 ^ (2 * k₀) * (t₀ ^ 2 * m₀) := by
      calc K * c₀ = 2 * (u * v) * m₀ * c₀ := by rw [e2]
        _ = u * (2 * v * c₀) * m₀ := by ring
        _ = u * u * m₀ := by rw [← e1]
        _ = (2 ^ k₀ * t₀) * (2 ^ k₀ * t₀) * m₀ := by rw [← e3]
        _ = 2 ^ (2 * k₀) * (t₀ ^ 2 * m₀) := by ring
    have hcop : Nat.Coprime (2 ^ (2 * k₀)) c₀ :=
      Nat.Coprime.pow_left (2 * k₀) (Nat.coprime_two_left.mpr hc₀)
    have hdvd : 2 ^ (2 * k₀) ∣ K := hcop.dvd_of_dvd_mul_right ⟨t₀ ^ 2 * m₀, key⟩
    obtain ⟨t', ht'⟩ := hdvd
    refine ⟨t', ?_, ht'⟩
    have h3 : 2 ^ (2 * k₀) * (t' * c₀) = 2 ^ (2 * k₀) * (t₀ ^ 2 * m₀) := by
      calc 2 ^ (2 * k₀) * (t' * c₀) = (2 ^ (2 * k₀) * t') * c₀ := by ring
        _ = K * c₀ := by rw [← ht']
        _ = 2 ^ (2 * k₀) * (t₀ ^ 2 * m₀) := key
    have h1 : t' * c₀ = t₀ ^ 2 * m₀ := Nat.eq_of_mul_eq_mul_left (by positivity) h3
    have h4 : Odd (t' * c₀) := by
      rw [h1]
      exact (ht₀.pow).mul hm₀
    exact (Nat.odd_mul.mp h4).1
  exact arith hc hm ht hUc hKm hUt

theorem wp6_neg_one_ne_one_gl2 (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have h0 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h0
  exact h2 (by linear_combination (-1 : F) * h0)

theorem wp6_xyK_ne_one (M : ModelData F) (h2 : (2 : F) ≠ 0) : M.xyK ≠ 1 := by
  intro h
  have h1 : xyGL F = 1 := congrArg Subtype.val h
  rw [xyGL, ← diagGL_one] at h1
  exact wp6_neg_one_ne_one_gl2 h2 (diagGL_inj h1).2

theorem wp6_xyK_ne_xK (M : ModelData F) (h2 : (2 : F) ≠ 0) : M.xyK ≠ M.xK := by
  intro h
  have h1 : xyGL F = xGL F := congrArg Subtype.val h
  rw [xyGL, xGL] at h1
  exact wp6_neg_one_ne_one_gl2 h2 (diagGL_inj h1).1.symm

theorem wp6_factorization_two {m t : ℕ} (ht : Odd t) : (2 ^ m * t).factorization 2 = m := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) ht.pos.ne', Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.2 ht) (even_iff_two_dvd.2 h)), add_zero]

theorem wp6_hgood (M : ModelData F) (h2 : (2 : F) ≠ 0) {D : Subgroup (GL (Fin 2) F)}
    (hD : ∀ a ∈ D, a ∈ M.U2)
    (hdet : ∀ a ∈ D, (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
      (a : Matrix (Fin 2) (Fin 2) F).det = -1) (hrefl : reflGL2 ∈ D)
    (hSK : l4uS D ≤ M.K4) :
    ∀ e ∈ (l4uS D).subgroupOf M.K4, e * e = 1 → e ≠ 1 → e ≠ M.xK →
      e * M.xyK = M.xyK * e ∨ ∃ y ∈ (l4uS D).subgroupOf M.K4, y * y = 1 ∧ y ≠ 1 ∧
        y ≠ M.xK ∧ y * M.xyK = M.xyK * y ∧ y * e = e * y := by
  intro e he he2 he1 hex
  have he2' : (e : GL (Fin 4) F) * e = 1 := by
    have := congrArg Subtype.val he2
    exact this
  rcases l4uS_good M h2 hD hdet hrefl (e : GL (Fin 4) F) (Subgroup.mem_subgroupOf.1 he) he2'
      (fun h => he1 (Subtype.ext h)) (fun h => hex (Subtype.ext h)) with
    h | ⟨y, hyS, hy2, hy1, hyx, hyd, hye⟩
  · exact Or.inl (Subtype.ext h)
  · refine Or.inr ⟨⟨y, hSK hyS⟩, Subgroup.mem_subgroupOf.2 hyS, Subtype.ext hy2,
      fun h => hy1 (congrArg Subtype.val h), fun h => hyx (congrArg Subtype.val h),
      Subtype.ext hyd, Subtype.ext hye⟩

theorem sylowFourJoined_block [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hrefl : reflGL2 ∈ M.U2)
    (hU : ∃ c : ℕ, Odd c ∧ Nat.card M.U2 = 2 * Nat.card M.H2 * c)
    (hK4 : ∃ m : ℕ, Odd m ∧ Nat.card M.K4 = 2 * (Nat.card M.U2 * Nat.card M.H2) * m)
    (hdet2 : ∀ a ∈ M.U2, ∀ k : ℕ, a ^ (2 ^ k) = 1 →
      (a : Matrix (Fin 2) (Fin 2) F).det = 1 ∨ (a : Matrix (Fin 2) (Fin 2) F).det = -1) :
    SylowFourJoined ↥M.K4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD, -, hreflD, hdet, k, t, hDcard, ht, hUt⟩ := exists_D_of_model M h2 hrefl hdet2
  obtain ⟨t', ht', hK⟩ := card_K4_eq_sq M h2 hU hK4 hUt ht
  have hSK : l4uS D ≤ M.K4 := l4uS_le_K4 M hD hdet
  have hcard : Nat.card ((l4uS D).subgroupOf M.K4) =
      2 ^ (Nat.card ↥M.K4).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, card_l4uS h2 hdet hreflD,
      hDcard, hK, wp6_factorization_two ht', ← pow_mul']
  have hP : ((Sylow.ofCard _ hcard : Sylow 2 ↥M.K4) : Subgroup ↥M.K4) =
      (l4uS D).subgroupOf M.K4 := Sylow.coe_ofCard _ _
  refine sylowFourJoined_of_sylow (Sylow.ofCard _ hcard) fun E₁ E₂ hE₁ hE₁P hE₂ hE₂P => ?_
  exact l4u_join (S := (l4uS D).subgroupOf M.K4) (z := M.xK) (d := M.xyK)
    (Subtype.ext xGL_mul_self) (fun h => xGL_ne_one h2 (congrArg Subtype.val h))
    (fun g => Subtype.ext (xGL_comm (g : GL (Fin 4) F)))
    (Subtype.ext xyGL_mul_self) (wp6_xyK_ne_one M h2) (wp6_xyK_ne_xK M h2)
    (wp6_hgood M h2 hD hdet hreflD hSK) E₁ E₂ hE₁ (hE₁P.trans hP.le) hE₂ (hE₂P.trans hP.le)

end Sylow

section Models

variable {F : Type} [Field F]

theorem sylowFourJoined_SL4 [Finite F] (hF : Nat.card F % 4 = 3) :
    SylowFourJoined ↥(ModelData.lin F).K4 := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  obtain ⟨c, hc, hqc⟩ : ∃ c : ℕ, Odd c ∧ Nat.card F - 1 = 2 * c :=
    ⟨2 * (Nat.card F / 4) + 1, ⟨Nat.card F / 4, rfl⟩, by omega⟩
  refine sylowFourJoined_block (ModelData.lin F) h2 (Subgroup.mem_top _) ?_ ?_ ?_
  · refine ⟨c, hc, ?_⟩
    have hU : Nat.card ↥(ModelData.lin F).U2 = Nat.card (GL (Fin 2) F) :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    have hH : Nat.card ↥(ModelData.lin F).H2 = Nat.card ↥(StatedSL 2 F) := rfl
    rw [hU, hH, CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_gl_two,
      CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSL_two, hqc]
    generalize Nat.card F ^ 2 - 1 = r
    ring
  · obtain ⟨m, hm, hK⟩ := CFSG.GH74.GLS.Stage2.Final.ModelOrd.odd_index_lin F h2
    rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_centralizer_yK (ModelData.lin F) h2] at hK
    exact ⟨m, hm, hK⟩
  · intro a _ k hk
    have hu1 : (Matrix.GeneralLinearGroup.det a) ^ (2 ^ k) = 1 := by
      rw [← map_pow, hk, map_one]
    have hcard : Nat.card Fˣ = 2 * c := by rw [Nat.card_units, hqc]
    have hdvd1 : orderOf (Matrix.GeneralLinearGroup.det a) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hu1
    have hdvd2 : orderOf (Matrix.GeneralLinearGroup.det a) ∣ 2 * c :=
      hcard ▸ orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf (Matrix.GeneralLinearGroup.det a)) c :=
      Nat.Coprime.coprime_dvd_left hdvd1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hc))
    have hsq : (Matrix.GeneralLinearGroup.det a) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd2)
    have hsq' : ((a : Matrix (Fin 2) (Fin 2) F).det) ^ 2 = 1 := by
      have := congrArg (fun v : Fˣ => (v : F)) hsq
      simpa using this
    exact sq_eq_one_iff.mp hsq'

variable {p f : ℕ}

theorem wp7b_arith {q : ℕ} (hq : q % 4 = 1) (U H : ℕ)
    (hH : (H : ℤ) = (q : ℤ) * ((q : ℤ) ^ 2 - 1))
    (hU : (U : ℤ) = (q : ℤ) * (((q : ℤ) + 1) * ((q : ℤ) ^ 2 - 1))) :
    ∃ c : ℕ, Odd c ∧ U = 2 * H * c := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 4 * s + 1 := ⟨q / 4, by omega⟩
  refine ⟨2 * s + 1, ⟨s, rfl⟩, ?_⟩
  apply Nat.cast_injective (R := ℤ)
  push_cast at hH hU ⊢
  rw [hU, hH]
  ring

theorem wp7b_det_conjTr (σ : F ≃+* F) {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    (CFSG.LieType.Universal.Unitary.conjTr σ A).det = σ A.det := by
  rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.det_transpose]
  exact (RingHom.map_det (σ : F →+* F) A).symm

theorem wp7b_pm_one {x : F} {q k : ℕ} (hq : q % 4 = 1) (h1 : x ^ q * x = 1)
    (h2 : x ^ (2 ^ k) = 1) : x = 1 ∨ x = -1 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 4 * s + 1 := ⟨q / 4, by omega⟩
  have hq1 : x ^ (4 * s + 1 + 1) = 1 := by rw [pow_succ]; exact h1
  have hc : (x ^ 2) ^ (2 * s + 1) = 1 := by
    rw [← pow_mul, show 2 * (2 * s + 1) = 4 * s + 1 + 1 by ring]
    exact hq1
  have hk : (x ^ 2) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]
  have hcop : Nat.Coprime (2 ^ k) (2 * s + 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 ⟨s, rfl⟩)
  have h3 : (x ^ 2) ^ (Nat.gcd (2 ^ k) (2 * s + 1)) = 1 := pow_gcd_eq_one.2 ⟨hk, hc⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h3
  exact sq_eq_one_iff.1 h3

theorem sylowFourJoined_SU4 [Finite F] [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) : SylowFourJoined ↥(ModelData.uni hF).K4 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact hf
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
    ⟨Fact.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact hodd.pow)
  refine sylowFourJoined_block (ModelData.uni hF) h2 ?_ ?_ ?_ ?_
  · show reflGL2 ∈ uniGL (CFSG.LieType.BorelTits.unitaryInvolution F p f) 2
    rw [mem_uniGL]
    show CFSG.LieType.Universal.Unitary.conjTr _ (Matrix.diagonal ![(1 : F), -1]) *
      Matrix.diagonal ![(1 : F), -1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Universal.Unitary.conjTr, Matrix.mul_apply, Fin.sum_univ_two]
  · have hH := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 2) (by norm_num)
    rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.prod_Icc_two_two,
      show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at hH
    have hU := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_uniGL_int h (n := 2) (by norm_num)
    rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.prod_Icc_one_two,
      show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at hU
    exact wp7b_arith hq _ _ hH hU
  · obtain ⟨m, hm, hK⟩ := CFSG.GH74.GLS.Stage2.Final.ModelOrd.odd_index_uni hF hp2
    refine ⟨m, hm, ?_⟩
    rw [hK, CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_centralizer_yK (ModelData.uni hF) h2]
  · intro a ha k hk
    have ha' : a ∈ uniGL (CFSG.LieType.BorelTits.unitaryInvolution F p f) 2 := ha
    have h1 := congrArg Matrix.det ((mem_uniGL _).1 ha')
    rw [Matrix.det_mul, wp7b_det_conjTr, Matrix.det_one,
      CFSG.LieType.BorelTits.unitaryInvolution_apply] at h1
    have h2k : (a : Matrix (Fin 2) (Fin 2) F).det ^ (2 ^ k) = 1 := by
      rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hk, Units.val_one, Matrix.det_one]
    exact wp7b_pm_one hq h1 h2k

end Models

section Kernels

variable {F : Type} [Field F]

theorem l4u_centre_statedProj_SL4 [Finite F] :
    Subgroup.center (StatedProj (StatedSL 4 F)) = ⊥ := by
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 F)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  refine CFSG.Semidihedral.CoreFreeDihedral.center_eq_bot_of_simple_nonabelian ?_
  obtain ⟨E, hEm⟩ : ∃ E : GL (Fin 4) F,
      (E : Matrix (Fin 4) (Fin 4) F) = _root_.Matrix.transvection 0 1 1 :=
    ⟨_root_.Matrix.GeneralLinearGroup.transvection 0 1 (by decide) 1, by first | rfl | simp⟩
  obtain ⟨E', hE'm⟩ : ∃ E : GL (Fin 4) F,
      (E : Matrix (Fin 4) (Fin 4) F) = _root_.Matrix.transvection 1 2 1 :=
    ⟨_root_.Matrix.GeneralLinearGroup.transvection 1 2 (by decide) 1, by first | rfl | simp⟩
  have hE : E ∈ StatedSL 4 F :=
    CFSG.Open.StatedAPI.mem_statedSL_of_det
      (by rw [hEm]; exact _root_.Matrix.det_transvection_of_ne _ _ (by decide) _)
  have hE' : E' ∈ StatedSL 4 F :=
    CFSG.Open.StatedAPI.mem_statedSL_of_det
      (by rw [hE'm]; exact _root_.Matrix.det_transvection_of_ne _ _ (by decide) _)
  refine ⟨QuotientGroup.mk ⟨E, hE⟩, QuotientGroup.mk ⟨E', hE'⟩, fun h => ?_⟩
  have h' : (QuotientGroup.mk ((⟨E, hE⟩ : StatedSL 4 F) * ⟨E', hE'⟩) :
        StatedProj (StatedSL 4 F)) =
      QuotientGroup.mk ((⟨E', hE'⟩ : StatedSL 4 F) * ⟨E, hE⟩) := by
    first
      | exact h
      | (rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact h)
      | simpa [QuotientGroup.mk_mul] using h
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSL 4 F) _ _).1 h'
  have hu' : (E' : Matrix (Fin 4) (Fin 4) F) * (E : Matrix (Fin 4) (Fin 4) F) =
      (E : Matrix (Fin 4) (Fin 4) F) * (E' : Matrix (Fin 4) (Fin 4) F) *
        ((u : F) • (1 : Matrix (Fin 4) (Fin 4) F)) := by
    first | exact hu | simpa using hu
  rw [hEm, hE'm] at hu'
  have h02 := congrFun (congrFun hu' 0) 2
  have hL : ((_root_.Matrix.transvection (1 : Fin 4) 2 (1 : F) *
      _root_.Matrix.transvection 0 1 1 : Matrix (Fin 4) (Fin 4) F) 0 2) = 0 := by
    first
      | (simp [_root_.Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.single_apply, Matrix.one_apply]; done)
      | (simp +decide [_root_.Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.single_apply, Matrix.one_apply]; done)
      | (rw [_root_.Matrix.transvection_mul_apply_of_ne (1 : Fin 4) 2 0 2 (by decide) (1 : F)]
         simp [_root_.Matrix.transvection])
  have hR : ((_root_.Matrix.transvection (0 : Fin 4) 1 (1 : F) *
      _root_.Matrix.transvection 1 2 1 * ((u : F) • (1 : Matrix (Fin 4) (Fin 4) F)) :
      Matrix (Fin 4) (Fin 4) F) 0 2) = (u : F) := by
    first
      | (simp [_root_.Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.single_apply, Matrix.one_apply]; done)
      | (simp +decide [_root_.Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.single_apply, Matrix.one_apply]; done)
      | (rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
          _root_.Matrix.transvection_mul_apply_same (0 : Fin 4) 1 2 (1 : F)]
         simp [_root_.Matrix.transvection])
  exact u.ne_zero (hR.symm.trans (h02.symm.trans hL))

theorem l4u_exists_nonker {H : Subgroup (GL (Fin 4) F)} {Q : Type} [Group Q] [Finite Q]
    (hZ : Subgroup.center (StatedProj H) = ⊥) (π : H →* Q) (hπ : Function.Surjective π)
    (hker : ∀ g : H, π g = 1 → ∃ c : Fˣ, (g : GL (Fin 4) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) c)
    (hcen : Subgroup.center Q ≠ ⊥) :
    ∃ g : H, (∃ c : Fˣ, (g : GL (Fin 4) F) = Matrix.GeneralLinearGroup.scalar (Fin 4) c) ∧
      π g ≠ 1 := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcen
  obtain ⟨g₀, hg₀⟩ := hπ (z : Q)
  have hzc : ∀ q : Q, q * (z : Q) = (z : Q) * q := Subgroup.mem_center_iff.1 z.2
  have hmem : (QuotientGroup.mk g₀ : StatedProj H) ∈ Subgroup.center (StatedProj H) := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨c, hc⟩ := hker ((x * g₀)⁻¹ * (g₀ * x)) (by
      rw [map_mul, map_inv, map_mul, map_mul, hg₀, hzc (π x), inv_mul_cancel])
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    exact ⟨c, hc.symm⟩
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨g₀, ⟨c, hc.symm⟩, ?_⟩
  rw [hg₀]
  exact fun h => hz1 (Subtype.ext h)

theorem wp9_val_pow_four {g : GL (Fin 4) F} {c : Fˣ}
    (hc : g = Matrix.GeneralLinearGroup.scalar (Fin 4) c)
    (hdet : (g : Matrix (Fin 4) (Fin 4) F).det = 1) : (c : F) ^ 4 = 1 := by
  rw [hc] at hdet
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using
    hdet

theorem wp9_sq_eq_neg_one {b : F} (h4 : b ^ 4 = 1) (h1 : b ≠ 1) (hm1 : b ≠ -1) :
    b ^ 2 = -1 := by
  have hfact : (b - 1) * (b + 1) * (b ^ 2 + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 hfact with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact (h1 (by linear_combination h)).elim
    · exact (hm1 (by linear_combination h)).elim
  · linear_combination h

theorem l4u_ker_pm_one {H : Subgroup (GL (Fin 4) F)} {Q : Type} [Group Q]
    (hdet : ∀ g ∈ H, (g : Matrix (Fin 4) (Fin 4) F).det = 1)
    (π : H →* Q)
    (hker : ∀ g : H, π g = 1 → ∃ c : Fˣ, (g : GL (Fin 4) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) c)
    (hnonker : ∃ g : H, (∃ c : Fˣ, (g : GL (Fin 4) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) c) ∧ π g ≠ 1) :
    ∀ g : H, π g = 1 → (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = -1 := by
  obtain ⟨g₀, ⟨c₀, hc₀⟩, hπ₀⟩ := hnonker
  intro g hg
  obtain ⟨c, hc⟩ := hker g hg
  by_contra hne
  have hb1 : (c : F) ≠ 1 := by
    intro h
    apply hne
    left
    rw [hc, show c = 1 from Units.ext h, map_one]
  have hbm1 : (c : F) ≠ -1 := by
    intro h
    apply hne
    right
    rw [hc, show c = -1 from Units.ext (by rw [Units.val_neg, Units.val_one]; exact h),
      CFSG.GH74.L5U5.scalar_neg_one_eq]
  have hb4 : (c : F) ^ 4 = 1 := wp9_val_pow_four hc (hdet _ g.2)
  have ha4 : (c₀ : F) ^ 4 = 1 := wp9_val_pow_four hc₀ (hdet _ g₀.2)
  have hb2 : (c : F) ^ 2 = -1 := wp9_sq_eq_neg_one hb4 hb1 hbm1
  have hkey : ∃ k : ℕ, c₀ = c ^ k := by
    have hfact : ((c₀ : F) - 1) * ((c₀ : F) + 1) * ((c₀ : F) - c) * ((c₀ : F) + c) = 0 := by
      linear_combination ha4 - ((c₀ : F) ^ 2 - 1) * hb2
    rcases mul_eq_zero.1 hfact with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact ⟨0, Units.ext (by rw [pow_zero, Units.val_one]; linear_combination h)⟩
        · exact ⟨2, Units.ext (by rw [Units.val_pow_eq_pow_val]; linear_combination h - hb2)⟩
      · exact ⟨1, Units.ext (by rw [pow_one]; linear_combination h)⟩
    · exact ⟨3, Units.ext (by
        rw [Units.val_pow_eq_pow_val]; linear_combination h - (c : F) * hb2)⟩
  obtain ⟨k, hk⟩ := hkey
  have hg₀ : g₀ = g ^ k := Subtype.ext (by rw [Subgroup.coe_pow, hc, hc₀, hk, map_pow])
  exact hπ₀ (by rw [hg₀, map_pow, hg, one_pow])

end Kernels

section Leaves

variable {F : Type} [Field F]

theorem l4u_iso_psl4 (G : Type) [Group G] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel G .PSL 4 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedSL 4 F)) := by
  rcases h with ⟨-, hcl⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩
  · obtain ⟨-, K, hK, hfin, hcard, hiso⟩ := hcl
    exact ⟨K, hK, hfin, hcard, hiso⟩
  all_goals exact absurd hn (by norm_num)

theorem l4u_iso_psu4 (G : Type) [Group G] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel G .PSU 4 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (p ^ f) ^ 2 ∧
      Nonempty (G ≃* StatedProj (StatedSU 4 (p ^ f) K)) := by
  rcases h with ⟨-, hcl⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩
  · obtain ⟨-, K, hK, hfin, hcard, hiso⟩ := hcl
    exact ⟨K, hK, hfin, hcard, hiso⟩
  all_goals exact absurd hn (by norm_num)

theorem l4u_ker_scalar {H : Subgroup (GL (Fin 4) F)} {Q : Type} [Group Q]
    (e : Q ⧸ Subgroup.center Q ≃* StatedProj H) (π : H →* Q)
    (hπe : ∀ g : H, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g) :
    ∀ g : H, π g = 1 → ∃ c : Fˣ, (g : GL (Fin 4) F) = Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
  intro g hg
  have h1 : (QuotientGroup.mk g : StatedProj H) = 1 := by
    rw [← hπe g, hg, QuotientGroup.mk_one, map_one]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc.symm⟩

end Leaves

section ScalarCentral

variable {F : Type} [Field F]

theorem l4u_scalar_central {H : Subgroup (GL (Fin 4) F)} (c : Fˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ H) :
    (⟨Matrix.GeneralLinearGroup.scalar (Fin 4) c, hc⟩ : H) ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.1 hz (h : GL (Fin 4) F)

end ScalarCentral

theorem coverLeafL4_holds
 : CoverLeafL4 := by
  intro Q _ _ hQ p f hp hp2 hf _hq h
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hG := CFSG.GH74.Generic.genericKnownFacts_of_griess hGA
  obtain ⟨hquasi, hz, h2z, -, -, hgen⟩ := hQ
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := l4u_iso_psl4 (Q ⧸ Subgroup.center Q) h
  have hodd : Odd (Nat.card F) := by
    rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2F : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  obtain ⟨π, hπs, hπe⟩ := hG.psl4_cover Q hquasi h2z F hodd e
  have hker := l4u_ker_scalar e π hπe
  have hZ : Subgroup.center (StatedProj (StatedSL 4 F)) = ⊥ := l4u_centre_statedProj_SL4
  have hnonker := l4u_exists_nonker hZ π hπs hker hz
  by_cases h4 : Nat.card F % 4 = 3
  · have hinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro g hg
      obtain ⟨c, hc⟩ := hker g hg
      have hcen : g ∈ Subgroup.center (StatedSL 4 F) := by
        rw [CFSG.GH74.L5U5.center_statedSL_eq, Subgroup.mem_subgroupOf]
        rw [StatedScalars, MonoidHom.mem_range]
        exact ⟨c, hc.symm⟩
      rcases (CFSG.GH74.L5U5.mem_center_statedSL_four_iff h4 g).1 hcen with h1 | h1
      · exact Subtype.ext h1
      · obtain ⟨g₀, hg₀, hπg₀⟩ := hnonker
        have hcen₀ : g₀ ∈ Subgroup.center (StatedSL 4 F) := by
          rw [CFSG.GH74.L5U5.center_statedSL_eq, Subgroup.mem_subgroupOf]
          rw [StatedScalars, MonoidHom.mem_range]
          obtain ⟨c₀, hc₀⟩ := hg₀
          exact ⟨c₀, hc₀.symm⟩
        rcases (CFSG.GH74.L5U5.mem_center_statedSL_four_iff h4 g₀).1 hcen₀ with h0 | h0
        · have hg₁ : g₀ = 1 := Subtype.ext h0
          exact (hπg₀ (by rw [hg₁, map_one])).elim
        · have hg₁ : g₀ = g := Subtype.ext (h0.trans h1.symm)
          exact (hπg₀ (by rw [hg₁, hg])).elim
    exact SylowFourJoined.of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπs⟩)
      (sylowFourJoined_SL4 h4)
  · have hi : ∃ i : F, i * i = -1 := by
      haveI := Fintype.ofFinite F
      have hsq : IsSquare (-1 : F) := by
        rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card]
        omega
      obtain ⟨r, hr⟩ := hsq
      exact ⟨r, hr.symm⟩
    obtain ⟨i, hi⟩ := hi
    have hpm := l4u_ker_pm_one (fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSL hg) π hker hnonker
    exact (not_gen4_of_SL4 hi h2F π (fun g hg => hpm g (MonoidHom.mem_ker.1 hg)) hgen).elim

theorem coverLeafU4_holds
 : CoverLeafU4 := by
  intro Q _ _ hQ p f hp hp2 hf _hq h
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hG := CFSG.GH74.Generic.genericKnownFacts_of_griess hGA
  obtain ⟨hquasi, hz, h2z, -, -, hgen⟩ := hQ
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := l4u_iso_psu4 (Q ⧸ Subgroup.center Q) h
  have hq_odd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hKodd : Odd (Nat.card K) := by
    rw [hK]; exact hq_odd.pow
  have h2K : (2 : K) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hKodd
  obtain ⟨π, hπs, hπe⟩ := hG.psu4_cover Q hquasi h2z K (p ^ f) hK hq_odd e
  have hker := l4u_ker_scalar e π hπe
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center (StatedProj (StatedSU 4 (p ^ f) K)) = ⊥ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_center_bot_pu hK (by norm_num) (by simp)
  have hnonker := l4u_exists_nonker hZ π hπs hker hz
  by_cases h4 : p ^ f % 4 = 1
  · have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      { prime := hp, one_le := hf, card := by rw [hK, ← pow_mul, mul_comm] }
    haveI : CharP K p := hUFD.charP
    have hinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro g hg
      obtain ⟨c, hc⟩ := hker g hg
      have hsc : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) K := by
        rw [← hc]; exact g.2
      have hcen : g ∈ Subgroup.center (StatedSU 4 (p ^ f) K) := by
        have hg_eq : g = ⟨Matrix.GeneralLinearGroup.scalar (Fin 4) c, hsc⟩ := Subtype.ext hc
        rw [hg_eq]
        exact l4u_scalar_central c hsc
      rcases (CFSG.GH74.L5U5.mem_center_statedSU_four_iff hK h4 g).1 hcen with h1 | h1
      · exact Subtype.ext h1
      · obtain ⟨g₀, hg₀, hπg₀⟩ := hnonker
        have hcen₀ : g₀ ∈ Subgroup.center (StatedSU 4 (p ^ f) K) := by
          obtain ⟨c₀, hc₀⟩ := hg₀
          have hsc₀ : Matrix.GeneralLinearGroup.scalar (Fin 4) c₀ ∈ StatedSU 4 (p ^ f) K := by
            rw [← hc₀]; exact g₀.2
          have hg_eq₀ : g₀ = ⟨Matrix.GeneralLinearGroup.scalar (Fin 4) c₀, hsc₀⟩ := Subtype.ext hc₀
          rw [hg_eq₀]
          exact l4u_scalar_central c₀ hsc₀
        rcases (CFSG.GH74.L5U5.mem_center_statedSU_four_iff hK h4 g₀).1 hcen₀ with h0 | h0
        · have hg₁ : g₀ = 1 := Subtype.ext h0
          exact (hπg₀ (by rw [hg₁, map_one])).elim
        · have hg₁ : g₀ = g := Subtype.ext (h0.trans h1.symm)
          exact (hπg₀ (by rw [hg₁, hg])).elim
    exact SylowFourJoined.of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπs⟩)
      (sylowFourJoined_SU4 hK hp2 h4)
  · have h4' : p ^ f % 4 = 3 := by
      have hodd := hq_odd
      rw [Nat.odd_iff] at hodd
      omega
    have hq2 : (p ^ f) ^ 2 % 4 = 1 := by
      rw [Nat.pow_mod, h4']
    have hi : ∃ i : K, i * i = -1 := by
      haveI := Fintype.ofFinite K
      have hsq : IsSquare (-1 : K) := by
        rw [FiniteField.isSquare_neg_one_iff, Fintype.card_eq_nat_card, hK, hq2]
        norm_num
      obtain ⟨r, hr⟩ := hsq
      exact ⟨r, hr.symm⟩
    obtain ⟨i, hi⟩ := hi
    have hpm := l4u_ker_pm_one (fun g hg => CFSG.Open.StatedAPI.det_of_mem_statedSU hg) π hker hnonker
    exact (not_gen4_of_SU4 hq_odd h4' hK hi h2K π (fun g hg => hpm g (MonoidHom.mem_ker.1 hg)) hgen).elim

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
