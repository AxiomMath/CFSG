module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSymplectic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine
import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabRealThree

public section

namespace CFSG.AGLEmbeddingD2.HeisSymplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.CurtisTits
  CFSG.AGLEmbeddingD2.SquareSymplectic TauCeti.GLSymplecticFin CFSG.LieType.Steinberg

section Small

@[expose] def f2 (F : Type) [Field F] [CharP F 2] : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

theorem map_transvection {R S : Type*} [CommRing R] [CommRing S] {m : Type*} [Fintype m]
    [DecidableEq m] (f : R →+* S) (p q : m) (c : R) :
    (Matrix.transvection p q c).map f = Matrix.transvection p q (f c) := by
  ext a b
  simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply]
  split_ifs <;> simp

variable (F : Type) [Field F]

@[expose] def x4 : Matrix (Fin 4) (Fin 4) F :=
  transvection 0 1 1 * transvection 2 3 1 * transvection 2 1 1

@[expose] def y4 : Matrix (Fin 4) (Fin 4) F :=
  transvection 1 2 1 * transvection 1 0 1 * transvection 3 2 1

variable {F}

theorem x4_map [CharP F 2] : x4 F = (RingHom.mapMatrix (f2 F)) (x4 (ZMod 2)) := by
  simp only [x4, map_mul, RingHom.mapMatrix_apply, map_transvection, map_one]

theorem y4_map [CharP F 2] : y4 F = (RingHom.mapMatrix (f2 F)) (y4 (ZMod 2)) := by
  simp only [y4, map_mul, RingHom.mapMatrix_apply, map_transvection, map_one]

theorem x4_mul_self [CharP F 2] : x4 F * x4 F = 1 := by
  rw [x4_map, ← map_mul, show x4 (ZMod 2) * x4 (ZMod 2) = 1 by decide, map_one]

theorem y4_mul_self [CharP F 2] : y4 F * y4 F = 1 := by
  rw [y4_map, ← map_mul, show y4 (ZMod 2) * y4 (ZMod 2) = 1 by decide, map_one]

theorem x4_mul_y4_pow_five [CharP F 2] : (x4 F * y4 F) ^ 5 = 1 := by
  rw [x4_map, y4_map, ← map_mul, ← map_pow, show (x4 (ZMod 2) * y4 (ZMod 2)) ^ 5 = 1 by decide,
    map_one]

theorem x4_mul_y4_ne_one [CharP F 2] : x4 F * y4 F ≠ 1 := by
  intro h
  rw [x4_map, y4_map, ← map_mul, ← map_one (RingHom.mapMatrix (f2 F) (m := Fin 4)),
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  exact (show x4 (ZMod 2) * y4 (ZMod 2) ≠ 1 by decide) (Matrix.map_injective (f2 F).injective h)

end Small

section Embed

variable {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def restrictEmb (e : κ ↪ ι) :
    (coordFix (Finset.univ.map e) : Subgroup (GL ι F)) →* Matrix κ κ F where
  toFun g := Matrix.of fun i j => ((g : GL ι F) : Matrix ι ι F) (e i) (e j)
  map_one' := by
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  map_mul' g h := by
    ext i j
    have hgh : (((g * h : ↥(coordFix (Finset.univ.map e))) : GL ι F) : Matrix ι ι F) =
        ((g : GL ι F) : Matrix ι ι F) * ((h : GL ι F) : Matrix ι ι F) := rfl
    simp only [Matrix.of_apply, hgh, Matrix.mul_apply]
    rw [← Finset.sum_map Finset.univ e
      (fun c => ((g : GL ι F) : Matrix ι ι F) (e i) c * ((h : GL ι F) : Matrix ι ι F) c (e j))]
    refine (Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_).symm
    have hac : e i ≠ c := fun h' => hc (Finset.mem_map.2 ⟨i, Finset.mem_univ _, h'⟩)
    rw [g.2 (e i) c (Or.inr hc), Matrix.one_apply_ne hac, zero_mul]

theorem restrictEmb_apply (e : κ ↪ ι) (g : (coordFix (Finset.univ.map e) : Subgroup (GL ι F)))
    (i j : κ) : restrictEmb e g i j = ((g : GL ι F) : Matrix ι ι F) (e i) (e j) := rfl

theorem restrictEmb_injective (e : κ ↪ ι) : Function.Injective (restrictEmb (F := F) e) := by
  intro g h hgh
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  by_cases hab : a ∈ Finset.univ.map e ∧ b ∈ Finset.univ.map e
  · obtain ⟨⟨i, -, rfl⟩, ⟨j, -, rfl⟩⟩ :=
      And.intro (Finset.mem_map.1 hab.1) (Finset.mem_map.1 hab.2)
    exact congrFun (congrFun hgh i) j
  · rw [not_and_or] at hab
    rw [g.2 a b hab, h.2 a b hab]

omit [DecidableEq κ] in
theorem transvectionUnit_mem_coordFix (e : κ ↪ ι) {p q : κ} (hpq : p ≠ q) (c : F) :
    TauCeti.transvectionUnit (e.injective.ne hpq) c ∈ coordFix (Finset.univ.map e) := by
  intro a b hab
  have hne : ¬ (e p = a ∧ e q = b) := fun ⟨h1, h2⟩ => by
    rcases hab with ha | hb
    · exact ha (Finset.mem_map.2 ⟨p, Finset.mem_univ _, h1⟩)
    · exact hb (Finset.mem_map.2 ⟨q, Finset.mem_univ _, h2⟩)
  simp [TauCeti.coe_transvectionUnit, Matrix.transvection, hne]

theorem restrictEmb_transvectionUnit (e : κ ↪ ι) {p q : κ} (hpq : p ≠ q) (c : F) :
    restrictEmb e ⟨TauCeti.transvectionUnit (e.injective.ne hpq) c,
      transvectionUnit_mem_coordFix e hpq c⟩ = Matrix.transvection p q c := by
  ext i j
  simp [restrictEmb_apply, TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.single_apply,
    Matrix.one_apply, e.injective.eq_iff]

end Embed

section A3

variable {n : ℕ} {F : Type} [Field F]

@[expose] def piece (n c m : ℕ) : Set (Fin n) := {i | c ≤ i.val ∧ i.val < c + m}

@[expose] def emb4 (c : ℕ) (hc : c + 3 < n) : Fin 4 ↪ Fin n where
  toFun k := ⟨c + k.val, by have := k.isLt; omega⟩
  inj' k l h := Fin.ext (by simpa using congrArg Fin.val h)

theorem leviSp_transvectionUnit_mem_up {i j : Fin n} (hij : i ≠ j) (hj : j.val = i.val + 1)
    (c : F) :
    leviSp n F (TauCeti.transvectionUnit hij c) ∈ rankOne (rootDatum n F).rootGroup i := by
  have hk : i.val + 1 < n := hj ▸ j.isLt
  obtain rfl : j = ⟨i.val + 1, hk⟩ := Fin.ext hj
  have h := elt_difference_eq_leviHom (n := n) (F := F) hij c
  change leviSp n F (TauCeti.transvectionUnit hij c) ∈ _
  change (equivStatedSp n F) (TauCeti.GLSymplecticFin.leviHom (TauCeti.transvectionUnit hij c)) ∈ _
  rw [← h]
  exact le_sup_left (a := (rootDatum n F).rootGroup (Pi.single i 1))
    (elt_mem_rootGroup (stdVec_shortPos_eq hk) c)

theorem leviSp_transvectionUnit_mem_down {i j : Fin n} (hij : i ≠ j) (hi : i.val = j.val + 1)
    (c : F) :
    leviSp n F (TauCeti.transvectionUnit hij c) ∈ rankOne (rootDatum n F).rootGroup j := by
  have hk : j.val + 1 < n := hi ▸ i.isLt
  obtain rfl : i = ⟨j.val + 1, hk⟩ := Fin.ext hi
  have h := elt_difference_eq_leviHom (n := n) (F := F) hij c
  change leviSp n F (TauCeti.transvectionUnit hij c) ∈ _
  change (equivStatedSp n F) (TauCeti.GLSymplecticFin.leviHom (TauCeti.transvectionUnit hij c)) ∈ _
  rw [← h]
  exact le_sup_right (b := (rootDatum n F).rootGroup (-Pi.single j 1))
    (elt_mem_rootGroup (stdVec_shortNeg_eq hk) c)

variable (F) (c : ℕ) (hc : c + 3 < n)

@[expose] noncomputable def tuA (p q : Fin 4) (h : p ≠ q) : GL (Fin n) F :=
  TauCeti.transvectionUnit ((emb4 c hc).injective.ne h) 1

@[expose] noncomputable def XA : GL (Fin n) F :=
  tuA F c hc 0 1 (by decide) * tuA F c hc 2 3 (by decide) * tuA F c hc 2 1 (by decide)

@[expose] noncomputable def YA : GL (Fin n) F :=
  tuA F c hc 1 2 (by decide) * tuA F c hc 1 0 (by decide) * tuA F c hc 3 2 (by decide)

variable {F c hc}

theorem tuA_mem (p q : Fin 4) (h : p ≠ q) :
    tuA F c hc p q h ∈ coordFix (Finset.univ.map (emb4 c hc)) :=
  transvectionUnit_mem_coordFix (emb4 c hc) h 1

theorem XA_mem : XA F c hc ∈ coordFix (Finset.univ.map (emb4 c hc)) :=
  mul_mem (mul_mem (tuA_mem _ _ _) (tuA_mem _ _ _)) (tuA_mem _ _ _)

theorem YA_mem : YA F c hc ∈ coordFix (Finset.univ.map (emb4 c hc)) :=
  mul_mem (mul_mem (tuA_mem _ _ _) (tuA_mem _ _ _)) (tuA_mem _ _ _)

theorem restrictEmb_tuA (p q : Fin 4) (h : p ≠ q) :
    restrictEmb (emb4 c hc) ⟨tuA F c hc p q h, tuA_mem p q h⟩ = Matrix.transvection p q 1 :=
  restrictEmb_transvectionUnit (emb4 c hc) h 1

theorem restrictEmb_XA : restrictEmb (emb4 c hc) ⟨XA F c hc, XA_mem⟩ = x4 F := by
  have h : (⟨XA F c hc, XA_mem⟩ : ↥(coordFix (Finset.univ.map (emb4 c hc)))) =
      ⟨_, tuA_mem 0 1 (by decide)⟩ * ⟨_, tuA_mem 2 3 (by decide)⟩ * ⟨_, tuA_mem 2 1 (by decide)⟩ :=
    rfl
  rw [h, map_mul, map_mul, restrictEmb_tuA, restrictEmb_tuA, restrictEmb_tuA]
  rfl

theorem restrictEmb_YA : restrictEmb (emb4 c hc) ⟨YA F c hc, YA_mem⟩ = y4 F := by
  have h : (⟨YA F c hc, YA_mem⟩ : ↥(coordFix (Finset.univ.map (emb4 c hc)))) =
      ⟨_, tuA_mem 1 2 (by decide)⟩ * ⟨_, tuA_mem 1 0 (by decide)⟩ * ⟨_, tuA_mem 3 2 (by decide)⟩ :=
    rfl
  rw [h, map_mul, map_mul, restrictEmb_tuA, restrictEmb_tuA, restrictEmb_tuA]
  rfl

section

variable [CharP F 2]

theorem XA_mul_self : XA F c hc * XA F c hc = 1 := by
  have h : (⟨XA F c hc, XA_mem⟩ * ⟨XA F c hc, XA_mem⟩ :
      ↥(coordFix (Finset.univ.map (emb4 c hc)))) = 1 := by
    apply restrictEmb_injective (F := F) (emb4 c hc)
    rw [map_mul, restrictEmb_XA, map_one]
    exact x4_mul_self
  exact congrArg Subtype.val h

theorem YA_mul_self : YA F c hc * YA F c hc = 1 := by
  have h : (⟨YA F c hc, YA_mem⟩ * ⟨YA F c hc, YA_mem⟩ :
      ↥(coordFix (Finset.univ.map (emb4 c hc)))) = 1 := by
    apply restrictEmb_injective (F := F) (emb4 c hc)
    rw [map_mul, restrictEmb_YA, map_one]
    exact y4_mul_self
  exact congrArg Subtype.val h

theorem XA_mul_YA_pow_five : (XA F c hc * YA F c hc) ^ 5 = 1 := by
  have h : (⟨XA F c hc, XA_mem⟩ * ⟨YA F c hc, YA_mem⟩ :
      ↥(coordFix (Finset.univ.map (emb4 c hc)))) ^ 5 = 1 := by
    apply restrictEmb_injective (F := F) (emb4 c hc)
    rw [map_pow, map_mul, restrictEmb_XA, restrictEmb_YA, map_one]
    exact x4_mul_y4_pow_five
  exact congrArg Subtype.val h

theorem XA_mul_YA_ne_one : XA F c hc * YA F c hc ≠ 1 := by
  intro h
  have h' : (⟨XA F c hc, XA_mem⟩ * ⟨YA F c hc, YA_mem⟩ :
      ↥(coordFix (Finset.univ.map (emb4 c hc)))) = 1 := Subtype.ext h
  have := congrArg (restrictEmb (F := F) (emb4 c hc)) h'
  rw [map_mul, restrictEmb_XA, restrictEmb_YA, map_one] at this
  exact x4_mul_y4_ne_one this

end

open CFSG.AGLEmbeddingD2.ParabLevi in
theorem A3_elements [CharP F 2] (c : ℕ) (hc : c + 3 < n) :
    ∃ x y : StatedSp n F, x ∈ leviM (rootDatum n F) (piece n c 3) ∧
      y ∈ leviM (rootDatum n F) (piece n c 3) ∧ x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 5 = 1 ∧
      x * y ≠ 1 := by
  have e0 : (emb4 c hc 0).val = c := rfl
  have e1 : (emb4 c hc 1).val = c + 1 := rfl
  have e2 : (emb4 c hc 2).val = c + 2 := rfl
  have e3 : (emb4 c hc 3).val = c + 3 := rfl
  have h0 : emb4 c hc 0 ∈ piece n c 3 := ⟨by omega, by omega⟩
  have h1 : emb4 c hc 1 ∈ piece n c 3 := ⟨by omega, by omega⟩
  have h2 : emb4 c hc 2 ∈ piece n c 3 := ⟨by omega, by omega⟩
  have u01 : leviSp n F (tuA F c hc 0 1 (by decide)) ∈ leviM (rootDatum n F) (piece n c 3) :=
    rankOne_le_leviM h0 (leviSp_transvectionUnit_mem_up _ (by omega) 1)
  have u23 : leviSp n F (tuA F c hc 2 3 (by decide)) ∈ leviM (rootDatum n F) (piece n c 3) :=
    rankOne_le_leviM h2 (leviSp_transvectionUnit_mem_up _ (by omega) 1)
  have d21 : leviSp n F (tuA F c hc 2 1 (by decide)) ∈ leviM (rootDatum n F) (piece n c 3) :=
    rankOne_le_leviM h1 (leviSp_transvectionUnit_mem_down _ (by omega) 1)
  have u12 : leviSp n F (tuA F c hc 1 2 (by decide)) ∈ leviM (rootDatum n F) (piece n c 3) :=
    rankOne_le_leviM h1 (leviSp_transvectionUnit_mem_up _ (by omega) 1)
  have d10 : leviSp n F (tuA F c hc 1 0 (by decide)) ∈ leviM (rootDatum n F) (piece n c 3) :=
    rankOne_le_leviM h0 (leviSp_transvectionUnit_mem_down _ (by omega) 1)
  have d32 : leviSp n F (tuA F c hc 3 2 (by decide)) ∈ leviM (rootDatum n F) (piece n c 3) :=
    rankOne_le_leviM h2 (leviSp_transvectionUnit_mem_down _ (by omega) 1)
  refine ⟨leviSp n F (XA F c hc), leviSp n F (YA F c hc), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [XA, map_mul, map_mul]
    exact mul_mem (mul_mem u01 u23) d21
  · rw [YA, map_mul, map_mul]
    exact mul_mem (mul_mem u12 d10) d32
  · rw [sq, ← map_mul, XA_mul_self, map_one]
  · rw [sq, ← map_mul, YA_mul_self, map_one]
  · rw [← map_mul, ← map_pow, XA_mul_YA_pow_five, map_one]
  · intro h
    rw [← map_mul, ← map_one (leviSp n F)] at h
    exact XA_mul_YA_ne_one (leviSp_injective h)

end A3

section C2Small

variable (F : Type) [Field F]

@[expose] def pa4 : Matrix (Fin 4) (Fin 4) F := 1 + single 0 1 1 - single 3 2 1

@[expose] def qa4 : Matrix (Fin 4) (Fin 4) F := 1 + single 1 0 1 - single 2 3 1

@[expose] def pb4 : Matrix (Fin 4) (Fin 4) F := 1 + single 1 3 1

@[expose] def qb4 : Matrix (Fin 4) (Fin 4) F := 1 + single 3 1 1

@[expose] def xc4 : Matrix (Fin 4) (Fin 4) F := pa4 F * qb4 F

@[expose] def yc4 : Matrix (Fin 4) (Fin 4) F := qa4 F * pb4 F

variable {F}

theorem pa4_map [CharP F 2] : pa4 F = (RingHom.mapMatrix (f2 F)) (pa4 (ZMod 2)) := by
  ext i j
  simp [pa4, RingHom.mapMatrix_apply, Matrix.single_apply, Matrix.one_apply, apply_ite (f2 F)]

theorem qa4_map [CharP F 2] : qa4 F = (RingHom.mapMatrix (f2 F)) (qa4 (ZMod 2)) := by
  ext i j
  simp [qa4, RingHom.mapMatrix_apply, Matrix.single_apply, Matrix.one_apply, apply_ite (f2 F)]

theorem pb4_map [CharP F 2] : pb4 F = (RingHom.mapMatrix (f2 F)) (pb4 (ZMod 2)) := by
  ext i j
  simp [pb4, RingHom.mapMatrix_apply, Matrix.single_apply, Matrix.one_apply, apply_ite (f2 F)]

theorem qb4_map [CharP F 2] : qb4 F = (RingHom.mapMatrix (f2 F)) (qb4 (ZMod 2)) := by
  ext i j
  simp [qb4, RingHom.mapMatrix_apply, Matrix.single_apply, Matrix.one_apply, apply_ite (f2 F)]

theorem xc4_map [CharP F 2] : xc4 F = (RingHom.mapMatrix (f2 F)) (xc4 (ZMod 2)) := by
  rw [xc4, xc4, map_mul, ← pa4_map, ← qb4_map]

theorem yc4_map [CharP F 2] : yc4 F = (RingHom.mapMatrix (f2 F)) (yc4 (ZMod 2)) := by
  rw [yc4, yc4, map_mul, ← qa4_map, ← pb4_map]

theorem xc4_mul_self [CharP F 2] : xc4 F * xc4 F = 1 := by
  rw [xc4_map, ← map_mul, show xc4 (ZMod 2) * xc4 (ZMod 2) = 1 by decide, map_one]

theorem yc4_mul_self [CharP F 2] : yc4 F * yc4 F = 1 := by
  rw [yc4_map, ← map_mul, show yc4 (ZMod 2) * yc4 (ZMod 2) = 1 by decide, map_one]

theorem xc4_mul_yc4_pow_five [CharP F 2] : (xc4 F * yc4 F) ^ 5 = 1 := by
  rw [xc4_map, yc4_map, ← map_mul, ← map_pow,
    show (xc4 (ZMod 2) * yc4 (ZMod 2)) ^ 5 = 1 by decide, map_one]

theorem xc4_mul_yc4_ne_one [CharP F 2] : xc4 F * yc4 F ≠ 1 := by
  intro h
  rw [xc4_map, yc4_map, ← map_mul, ← map_one (RingHom.mapMatrix (f2 F) (m := Fin 4)),
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  exact (show xc4 (ZMod 2) * yc4 (ZMod 2) ≠ 1 by decide) (Matrix.map_injective (f2 F).injective h)

end C2Small

section C2

variable {n : ℕ} {F : Type} [Field F]

@[expose] def emb4C (a b : Fin n) (hab : a ≠ b) : Fin 4 ↪ Fin n ⊕ Fin n where
  toFun k := ![Sum.inl a, Sum.inl b, Sum.inr a, Sum.inr b] k
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm]

theorem elt_mem_coordFix {r : RootSubgroupIndex n} {S : Finset (Fin n ⊕ Fin n)}
    (h1 : (pos1 r).1 ∈ S ∧ (pos1 r).2 ∈ S) (h2 : (pos2 r).1 ∈ S ∧ (pos2 r).2 ∈ S) (c : F) :
    ((elt r c : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈ coordFix S := by
  intro x y hxy
  have hx1 : (x, y) ≠ pos1 r := fun h => by
    have hxe : x = (pos1 r).1 := congrArg Prod.fst h
    have hye : y = (pos1 r).2 := congrArg Prod.snd h
    rcases hxy with hx | hy
    · exact hx (by rw [hxe]; exact h1.1)
    · exact hy (by rw [hye]; exact h1.2)
  have hx2 : (x, y) ≠ pos2 r := fun h => by
    have hxe : x = (pos2 r).1 := congrArg Prod.fst h
    have hye : y = (pos2 r).2 := congrArg Prod.snd h
    rcases hxy with hx | hy
    · exact hx (by rw [hxe]; exact h2.1)
    · exact hy (by rw [hye]; exact h2.2)
  change mat n F (elt r c) x y = _
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply, E_eq_zero r hx1 hx2, smul_zero, add_zero]

variable (F) in
@[expose] noncomputable def PaC {a b : Fin n} (hab : a ≠ b) : StatedSp n F :=
  elt (RootSubgroupIndex.difference a b hab) 1

variable (F) in
@[expose] noncomputable def QaC {a b : Fin n} (hab : a ≠ b) : StatedSp n F :=
  elt (RootSubgroupIndex.difference b a hab.symm) 1

variable (F) in
@[expose] noncomputable def PbC (b : Fin n) : StatedSp n F :=
  elt (RootSubgroupIndex.positiveLong b) 1

variable (F) in
@[expose] noncomputable def QbC (b : Fin n) : StatedSp n F :=
  elt (RootSubgroupIndex.negativeLong b) 1

variable {a b : Fin n} (hab : a ≠ b)

theorem PaC_mem : ((PaC F hab : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
    coordFix (Finset.univ.map (emb4C a b hab)) :=
  elt_mem_coordFix ⟨Finset.mem_map.2 ⟨0, Finset.mem_univ _, rfl⟩,
    Finset.mem_map.2 ⟨1, Finset.mem_univ _, rfl⟩⟩
    ⟨Finset.mem_map.2 ⟨3, Finset.mem_univ _, rfl⟩, Finset.mem_map.2 ⟨2, Finset.mem_univ _, rfl⟩⟩ 1

theorem QaC_mem : ((QaC F hab : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
    coordFix (Finset.univ.map (emb4C a b hab)) :=
  elt_mem_coordFix ⟨Finset.mem_map.2 ⟨1, Finset.mem_univ _, rfl⟩,
    Finset.mem_map.2 ⟨0, Finset.mem_univ _, rfl⟩⟩
    ⟨Finset.mem_map.2 ⟨2, Finset.mem_univ _, rfl⟩, Finset.mem_map.2 ⟨3, Finset.mem_univ _, rfl⟩⟩ 1

theorem PbC_mem : ((PbC F b : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
    coordFix (Finset.univ.map (emb4C a b hab)) :=
  elt_mem_coordFix ⟨Finset.mem_map.2 ⟨1, Finset.mem_univ _, rfl⟩,
    Finset.mem_map.2 ⟨3, Finset.mem_univ _, rfl⟩⟩
    ⟨Finset.mem_map.2 ⟨1, Finset.mem_univ _, rfl⟩, Finset.mem_map.2 ⟨3, Finset.mem_univ _, rfl⟩⟩ 1

theorem QbC_mem : ((QbC F b : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
    coordFix (Finset.univ.map (emb4C a b hab)) :=
  elt_mem_coordFix ⟨Finset.mem_map.2 ⟨3, Finset.mem_univ _, rfl⟩,
    Finset.mem_map.2 ⟨1, Finset.mem_univ _, rfl⟩⟩
    ⟨Finset.mem_map.2 ⟨3, Finset.mem_univ _, rfl⟩, Finset.mem_map.2 ⟨1, Finset.mem_univ _, rfl⟩⟩ 1

theorem restrictEmb_elt (e : Fin 4 ↪ Fin n ⊕ Fin n) {r : RootSubgroupIndex n} (c : F)
    {g : StatedSp n F} (hg : g = elt r c)
    (h : (g : GL (Fin n ⊕ Fin n) F) ∈ coordFix (Finset.univ.map e)) (i j : Fin 4) :
    restrictEmb e ⟨_, h⟩ i j = (1 + c • E F r) (e i) (e j) := by
  subst hg
  rw [restrictEmb_apply]
  exact congrFun (congrFun (mat_elt r c) _) _

theorem restrictEmb_PaC : restrictEmb (emb4C a b hab) ⟨_, PaC_mem hab⟩ = pa4 F := by
  ext i j
  rw [restrictEmb_elt (r := RootSubgroupIndex.difference a b hab) (g := PaC F hab) _ 1 rfl]
  fin_cases i <;> fin_cases j <;> simp [emb4C, pa4, E, hab, hab.symm]

theorem restrictEmb_QaC : restrictEmb (emb4C a b hab) ⟨_, QaC_mem hab⟩ = qa4 F := by
  ext i j
  rw [restrictEmb_elt (r := RootSubgroupIndex.difference b a hab.symm) (g := QaC F hab) _ 1 rfl]
  fin_cases i <;> fin_cases j <;> simp [emb4C, qa4, E, hab, hab.symm]

theorem restrictEmb_PbC : restrictEmb (emb4C a b hab) ⟨_, PbC_mem hab⟩ = pb4 F := by
  ext i j
  rw [restrictEmb_elt (r := RootSubgroupIndex.positiveLong b) (g := PbC F b) _ 1 rfl]
  fin_cases i <;> fin_cases j <;> simp [emb4C, pb4, E, hab, hab.symm]

theorem restrictEmb_QbC : restrictEmb (emb4C a b hab) ⟨_, QbC_mem hab⟩ = qb4 F := by
  ext i j
  rw [restrictEmb_elt (r := RootSubgroupIndex.negativeLong b) (g := QbC F b) _ 1 rfl]
  fin_cases i <;> fin_cases j <;> simp [emb4C, qb4, E, hab, hab.symm]

variable (F) in
@[expose] noncomputable def PaC' : ↥(coordFix (Finset.univ.map (emb4C a b hab)) :
    Subgroup (GL (Fin n ⊕ Fin n) F)) := ⟨_, PaC_mem hab⟩

variable (F) in
@[expose] noncomputable def QaC' : ↥(coordFix (Finset.univ.map (emb4C a b hab)) :
    Subgroup (GL (Fin n ⊕ Fin n) F)) := ⟨_, QaC_mem hab⟩

variable (F) in
@[expose] noncomputable def PbC' : ↥(coordFix (Finset.univ.map (emb4C a b hab)) :
    Subgroup (GL (Fin n ⊕ Fin n) F)) := ⟨_, PbC_mem hab⟩

variable (F) in
@[expose] noncomputable def QbC' : ↥(coordFix (Finset.univ.map (emb4C a b hab)) :
    Subgroup (GL (Fin n ⊕ Fin n) F)) := ⟨_, QbC_mem hab⟩

section

variable [CharP F 2]

theorem C2_x_sq : (PaC F hab * QbC F b) * (PaC F hab * QbC F b) = 1 := by
  have h : (PaC' F hab * QbC' F hab) * (PaC' F hab * QbC' F hab) = 1 := by
    apply restrictEmb_injective (F := F) (emb4C a b hab)
    rw [map_mul, map_mul, PaC', QbC', restrictEmb_PaC, restrictEmb_QbC, map_one]
    exact xc4_mul_self
  exact Subtype.ext (congrArg (fun z : ↥(coordFix (Finset.univ.map (emb4C a b hab))) =>
    (z : GL (Fin n ⊕ Fin n) F)) h)

theorem C2_y_sq : (QaC F hab * PbC F b) * (QaC F hab * PbC F b) = 1 := by
  have h : (QaC' F hab * PbC' F hab) * (QaC' F hab * PbC' F hab) = 1 := by
    apply restrictEmb_injective (F := F) (emb4C a b hab)
    rw [map_mul, map_mul, QaC', PbC', restrictEmb_QaC, restrictEmb_PbC, map_one]
    exact yc4_mul_self
  exact Subtype.ext (congrArg (fun z : ↥(coordFix (Finset.univ.map (emb4C a b hab))) =>
    (z : GL (Fin n ⊕ Fin n) F)) h)

theorem C2_xy_pow : ((PaC F hab * QbC F b) * (QaC F hab * PbC F b)) ^ 5 = 1 := by
  have h : ((PaC' F hab * QbC' F hab) * (QaC' F hab * PbC' F hab)) ^ 5 = 1 := by
    apply restrictEmb_injective (F := F) (emb4C a b hab)
    rw [map_pow, map_mul, map_mul, map_mul, PaC', QbC', QaC', PbC', restrictEmb_PaC,
      restrictEmb_QbC, restrictEmb_QaC, restrictEmb_PbC, map_one]
    exact xc4_mul_yc4_pow_five
  exact Subtype.ext (congrArg (fun z : ↥(coordFix (Finset.univ.map (emb4C a b hab))) =>
    (z : GL (Fin n ⊕ Fin n) F)) h)

theorem C2_xy_ne : (PaC F hab * QbC F b) * (QaC F hab * PbC F b) ≠ 1 := by
  intro h
  have h' : (PaC' F hab * QbC' F hab) * (QaC' F hab * PbC' F hab) = 1 :=
    Subtype.ext (congrArg (Subtype.val : StatedSp n F → GL (Fin n ⊕ Fin n) F) h)
  have := congrArg (restrictEmb (F := F) (emb4C a b hab)) h'
  rw [map_mul, map_mul, map_mul, PaC', QbC', QaC', PbC', restrictEmb_PaC, restrictEmb_QbC,
    restrictEmb_QaC, restrictEmb_PbC, map_one] at this
  exact xc4_mul_yc4_ne_one this

end

theorem PaC_mem_rankOne (hb : b.val = a.val + 1) :
    PaC F hab ∈ rankOne (rootDatum n F).rootGroup a := by
  have hk : a.val + 1 < n := hb ▸ b.isLt
  obtain rfl : b = ⟨a.val + 1, hk⟩ := Fin.ext hb
  exact le_sup_left (a := (rootDatum n F).rootGroup (Pi.single a 1))
    (elt_mem_rootGroup (stdVec_shortPos_eq hk) 1)

theorem QaC_mem_rankOne (hb : b.val = a.val + 1) :
    QaC F hab ∈ rankOne (rootDatum n F).rootGroup a := by
  have hk : a.val + 1 < n := hb ▸ b.isLt
  obtain rfl : b = ⟨a.val + 1, hk⟩ := Fin.ext hb
  exact le_sup_right (b := (rootDatum n F).rootGroup (-Pi.single a 1))
    (elt_mem_rootGroup (stdVec_shortNeg_eq hk) 1)

theorem PbC_mem_rankOne (hbn : b.val + 1 = n) :
    PbC F b ∈ rankOne (rootDatum n F).rootGroup b :=
  le_sup_left (a := (rootDatum n F).rootGroup (Pi.single b 1))
    (elt_mem_rootGroup (stdVec_positiveLong_eq (by omega)) 1)

theorem QbC_mem_rankOne (hbn : b.val + 1 = n) :
    QbC F b ∈ rankOne (rootDatum n F).rootGroup b :=
  le_sup_right (b := (rootDatum n F).rootGroup (-Pi.single b 1))
    (elt_mem_rootGroup (stdVec_negativeLong_eq (by omega)) 1)

open CFSG.AGLEmbeddingD2.ParabLevi in
theorem C2_elements [CharP F 2] (hb : b.val = a.val + 1) (hbn : b.val + 1 = n) :
    ∃ x y : StatedSp n F, x ∈ leviM (rootDatum n F) {a, b} ∧ y ∈ leviM (rootDatum n F) {a, b} ∧
      x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 5 = 1 ∧ x * y ≠ 1 := by
  have hab : a ≠ b := fun h => by rw [h] at hb; omega
  have ha : a ∈ ({a, b} : Set (Fin n)) := Set.mem_insert _ _
  have hbm : b ∈ ({a, b} : Set (Fin n)) := Set.mem_insert_of_mem _ rfl
  refine ⟨PaC F hab * QbC F b, QaC F hab * PbC F b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (rankOne_le_leviM ha (PaC_mem_rankOne hab hb))
      (rankOne_le_leviM hbm (QbC_mem_rankOne hbn))
  · exact mul_mem (rankOne_le_leviM ha (QaC_mem_rankOne hab hb))
      (rankOne_le_leviM hbm (PbC_mem_rankOne hbn))
  · rw [sq]
    exact C2_x_sq hab
  · rw [sq]
    exact C2_y_sq hab
  · exact C2_xy_pow hab
  · exact C2_xy_ne hab

end C2

section A1

variable {F : Type} [Field F] [CharP F 2]

theorem sl2_matrix_pow_five {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    (!![1 + ω, 1; ω, 1] : Matrix (Fin 2) (Fin 2) F) ^ 5 = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (8 + 19 * ω + 8 * ω ^ 2 + ω ^ 3) * hω + (-4 - 6 * ω) * h2
  · simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (13 + 7 * ω + ω ^ 2) * hω + (-4) * h2
  · simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (13 * ω + 7 * ω ^ 2 + ω ^ 3) * hω + (-4 * ω) * h2
  · simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (8 + 6 * ω + ω ^ 2) * hω + (-4 - 2 * ω) * h2

theorem sl2_real {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    (sl2Upper (1 : F)) ^ 2 = 1 ∧ (sl2Lower ω) ^ 2 = 1 ∧
      (sl2Upper (1 : F) * sl2Lower ω) ^ 5 = 1 ∧ sl2Upper (1 : F) * sl2Lower ω ≠ 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hxy : ((sl2Upper (1 : F) * sl2Lower ω : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![1 + ω, 1; ω, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, CFSG.LieType.Steinberg.Sp.coe_sl2Upper,
      CFSG.LieType.Steinberg.Sp.coe_sl2Lower]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨CFSG.AGLEmbeddingD2.ParabRealThree.sl2Upper_one_sq, ?_, ?_, ?_⟩
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, CFSG.LieType.Steinberg.Sp.coe_sl2Lower,
      Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination ω * h2
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, hxy, Matrix.SpecialLinearGroup.coe_one,
      sl2_matrix_pow_five hω]
  · intro h
    have := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp only [hxy, Matrix.SpecialLinearGroup.coe_one] at this
    simp at this

end A1

section Real

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] {Y : Type*} [Group Y] {π : StatedSp n F →* Y}
  {J : Subgroup Y}

open CFSG.AGLEmbeddingD2.ParabLevi in
theorem realOver_rankOne {ω : F} (hω : ω ^ 2 + ω + 1 = 0) {k : Fin n}
    (hk : rankOne (rootDatum n F).rootGroup k ≤ J.comap π) :
    CFSG.AGLEmbeddingD2.HeisEngine.RealOver 5 π (rankOne (rootDatum n F).rootGroup k) J := by
  obtain ⟨φ, hφ, hrange⟩ := exists_rankOne_eq_range (n := n) (F := F) k
  obtain ⟨hx2, hy2, h5, hne⟩ := sl2_real hω
  have hx : φ (sl2Upper 1) ∈ rankOne (rootDatum n F).rootGroup k := hrange ▸ ⟨_, rfl⟩
  have hy : φ (sl2Lower ω) ∈ rankOne (rootDatum n F).rootGroup k := hrange ▸ ⟨_, rfl⟩
  refine CFSG.AGLEmbeddingD2.HeisEngine.RealOver.of_involutions' (by decide) hx hy ?_ ?_ ?_ ?_
    (hk (mul_mem hx hy))
  · rw [← map_pow, hx2, map_one]
  · rw [← map_pow, hy2, map_one]
  · rw [← map_mul, ← map_pow, h5, map_one]
  · intro h
    rw [← map_mul, ← map_one φ] at h
    exact hne (hφ h)

open CFSG.AGLEmbeddingD2.ParabLevi in
theorem realOver_A3 (c : ℕ) (hc : c + 3 < n)
    (hL : leviM (rootDatum n F) (piece n c 3) ≤ J.comap π) :
    CFSG.AGLEmbeddingD2.HeisEngine.RealOver 5 π (leviM (rootDatum n F) (piece n c 3)) J := by
  obtain ⟨x, y, hx, hy, hx2, hy2, h5, hne⟩ := A3_elements (F := F) c hc
  exact CFSG.AGLEmbeddingD2.HeisEngine.RealOver.of_involutions' (by decide) hx hy hx2 hy2 h5 hne
    (hL (mul_mem hx hy))

open CFSG.AGLEmbeddingD2.ParabLevi in
theorem realOver_C2 {a b : Fin n} (hb : b.val = a.val + 1) (hbn : b.val + 1 = n)
    (hL : leviM (rootDatum n F) {a, b} ≤ J.comap π) :
    CFSG.AGLEmbeddingD2.HeisEngine.RealOver 5 π (leviM (rootDatum n F) {a, b}) J := by
  obtain ⟨x, y, hx, hy, hx2, hy2, h5, hne⟩ := C2_elements (F := F) hb hbn
  exact CFSG.AGLEmbeddingD2.HeisEngine.RealOver.of_involutions' (by decide) hx hy hx2 hy2 h5 hne
    (hL (mul_mem hx hy))

end Real

end CFSG.AGLEmbeddingD2.HeisSymplectic
