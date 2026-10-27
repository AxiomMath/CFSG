module

public import CFSG.GH74.Generic.BProg.B2.T4L5Inv
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.B3aGen

open CFSG CFSG.GH74.GLS Matrix Subgroup
open CFSG.GH74.Generic.BProg.B2.T4.L5Inv CFSG.GH74.Generic.BProg.B2.T4.L5Count

section Abstract

variable {X P : Type} [Group X] [Group P]

theorem le_map_ker_of_perfect {A : Type} [CommGroup A] (f : X →* P) (ψ : X →* A) {L : Subgroup P}
    (hLX : L ≤ f.range) (hperf : ⁅L, L⁆ = L) : L ≤ ψ.ker.map f := by
  rw [← hperf]
  calc ⁅L, L⁆ ≤ ⁅f.range, f.range⁆ := Subgroup.commutator_mono hLX hLX
    _ = Subgroup.map f ⁅(⊤ : Subgroup X), ⊤⁆ := by rw [MonoidHom.range_eq_map, Subgroup.map_commutator]
    _ ≤ ψ.ker.map f := Subgroup.map_mono (Abelianization.commutator_subset_ker ψ)

theorem le_map_ker_of_quasisimple {W : Type} [Monoid W] (f : X →* P) (φ : X →* W) {L : Subgroup P}
    (hq : CFSG.IsQuasisimple ↥L) (hLX : L ≤ f.range) {u : X} (hu : φ u = 1) (huL : f u ∈ L)
    (hnc : ¬ ∀ l ∈ L, f u * l = l * f u) : L ≤ φ.ker.map f := by
  set N : Subgroup P := φ.ker.map f ⊓ L with hN
  have hNn : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨⟨k, hk, hkn⟩, hnL⟩ := hn
    obtain ⟨y, hy⟩ := hLX l.2
    have hk' : φ k = 1 := hk
    refine ⟨⟨y * k * y⁻¹, (MonoidHom.mem_ker).2 ?_, ?_⟩, ?_⟩
    · rw [map_mul, map_mul, hk', mul_one, ← map_mul, mul_inv_cancel, map_one]
    · simp only [map_mul, map_inv, hy, hkn, Subgroup.coe_mul, Subgroup.coe_inv]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact L.mul_mem (L.mul_mem l.2 hnL) (L.inv_mem l.2)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hNn with htop | hcen
  · intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ N.subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 this).1
  · exfalso
    apply hnc
    intro l hl
    have hmem : (⟨f u, huL⟩ : ↥L) ∈ N.subgroupOf L :=
      Subgroup.mem_subgroupOf.2 ⟨⟨u, hu, rfl⟩, huL⟩
    have := Subgroup.mem_center_iff.1 (hcen hmem) ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm

theorem eq_of_isComponent_le {Y : Type} [Group Y] [Finite Y] {Q Q' : Subgroup Y}
    (hQ : CFSG.IsComponent Q) (hQ' : CFSG.IsComponent Q') (hle : Q ≤ Q') : Q = Q' := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hQ' hQ.2 with h | h
  · exact le_antisymm hle h
  · exfalso
    have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hQ.1.1
    have hbot : ⁅Q, Q⁆ = ⊥ := le_bot_iff.1 (h ▸ Subgroup.commutator_mono hle le_rfl)
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hQ.1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥Q)
    apply hx
    have h1 : (x : Y) ∈ ⁅Q, Q⁆ := by rw [hperf]; exact x.2
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subtype.ext h1

theorem isQuasisimple_of_isCompIn {Y : Type} [Group Y] {C L : Subgroup Y} (h : IsCompIn C L) :
    CFSG.IsQuasisimple ↥L :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

theorem eq_of_isCompIn_le {Y : Type} [Group Y] [Finite Y] {C Q Q' : Subgroup Y}
    (hQ : IsCompIn C Q) (hQ' : IsCompIn C Q') (hle : Q ≤ Q') : Q = Q' := by
  have h := eq_of_isComponent_le hQ.2 hQ'.2 (Subgroup.subgroupOf_mono C hle)
  have h2 := Subgroup.subgroupOf_inj.1 h
  rwa [inf_eq_left.2 hQ.1, inf_eq_left.2 hQ'.1] at h2

end Abstract

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

theorem centralizer_map_mulEquiv (e : Y ≃* Y') (t : Y) :
    (centralizer ({t} : Set Y)).map e.toMonoidHom = centralizer ({e t} : Set Y') := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.1 hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hw']
  · intro hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    refine ⟨e.symm z, Subgroup.mem_centralizer_singleton_iff.2 ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz

theorem isCompIn_map (e : Y ≃* Y') {C L : Subgroup Y} (h : IsCompIn C L) :
    IsCompIn (C.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  obtain ⟨hLC, hcomp⟩ := h
  refine ⟨Subgroup.map_mono hLC, ?_⟩
  let e' : ↥C ≃* ↥(C.map e.toMonoidHom) := e.subgroupMap C
  have hmap : (L.subgroupOf C).map e'.toMonoidHom =
      (L.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
      exact ⟨⟨k, hLC hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
  have := CFSG.LocalCores.isComponent_map_mulEquiv e' hcomp
  rwa [hmap] at this

@[expose] def B3aAt (t : Y) (L : Subgroup Y) : Prop :=
  IsCompIn (centralizer ({t} : Set Y)) L →
    (∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z * z = 1 → z = 1) →
    (∃ a ∈ L, ∃ b ∈ L, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) →
    ∃ e : Y, e * e = 1 ∧ e ≠ 1 ∧ (∀ l ∈ L, e * l = l * e) ∧
      ∃ L' : Subgroup Y, IsCompIn (centralizer ({e} : Set Y)) L' ∧ L ≤ L' ∧ L ≠ L'

theorem b3aAt_of_mulEquiv (e : Y ≃* Y') {t : Y} {L : Subgroup Y}
    (h : B3aAt (e t) (L.map e.toMonoidHom)) : B3aAt t L := by
  intro hL hZ h4
  have hL' : IsCompIn (centralizer ({e t} : Set Y')) (L.map e.toMonoidHom) := by
    rw [← centralizer_map_mulEquiv]
    exact isCompIn_map e hL
  have hZ' : ∀ z ∈ L.map e.toMonoidHom, (∀ l ∈ L.map e.toMonoidHom, z * l = l * z) → z * z = 1 →
      z = 1 := by
    rintro _ ⟨w, hw, rfl⟩ hc hsq
    simp only [MulEquiv.coe_toMonoidHom] at hc hsq ⊢
    have hw1 : w = 1 := by
      refine hZ w hw (fun l hl => e.injective ?_) (e.injective ?_)
      · rw [map_mul, map_mul]
        exact hc (e l) ⟨l, hl, rfl⟩
      · rw [map_mul, hsq, map_one]
    rw [hw1, map_one]
  have h4' : ∃ a ∈ L.map e.toMonoidHom, ∃ b ∈ L.map e.toMonoidHom, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧
      b ≠ 1 ∧ a ≠ b ∧ a * b = b * a := by
    obtain ⟨a, ha, b, hb, haa, hbb, ha1, hb1, hab, hc⟩ := h4
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, haa, map_one]
    · rw [← map_mul, hbb, map_one]
    · exact fun h1 => ha1 (e.injective (by rw [h1, map_one]))
    · exact fun h1 => hb1 (e.injective (by rw [h1, map_one]))
    · exact fun h1 => hab (e.injective h1)
    · rw [← map_mul, ← map_mul, hc]
  obtain ⟨u, huu, hu1, huc, L'', hL'', hle, hne⟩ := h hL' hZ' h4'
  refine ⟨e.symm u, ?_, ?_, ?_, L''.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← map_mul, huu, map_one]
  · exact fun h1 => hu1 (e.symm.injective (by rw [h1, map_one]))
  · intro l hl
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact huc (e l) ⟨l, hl, rfl⟩
  · have := isCompIn_map e.symm hL''
    rwa [centralizer_map_mulEquiv] at this
  · intro l hl
    refine ⟨e l, hle ⟨l, hl, rfl⟩, ?_⟩
    simp
  · intro heq
    apply hne
    rw [heq, Subgroup.map_map]
    ext z
    simp

end Transport

section Matrices

variable {F : Type} [Field F]

@[expose] def blkGL (I : Finset (Fin 5)) : Subgroup (GL (Fin 5) F) where
  carrier := {A | ∀ i j, (i ∉ I ∨ j ∉ I) →
    (A : Matrix (Fin 5) (Fin 5) F) i j = (1 : Matrix (Fin 5) (Fin 5) F) i j}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_ofPred_eq, CFSG.SeitzReduction.LinearPilot.agrees_one_iff] at hA hB ⊢
    rw [Units.val_mul]
    exact ⟨by rw [Matrix.mul_assoc, hB.1, hA.1], by rw [← Matrix.mul_assoc, hA.2, hB.2]⟩
  inv_mem' := by
    intro A hA
    simp only [Set.mem_ofPred_eq, CFSG.SeitzReduction.LinearPilot.agrees_one_iff] at hA ⊢
    have h1 : ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * (A : Matrix (Fin 5) (Fin 5) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (A : Matrix (Fin 5) (Fin 5) F) * ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hA.1, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    · conv_lhs => rw [← hA.2, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem mem_blkGL {I : Finset (Fin 5)} {A : GL (Fin 5) F} :
    A ∈ blkGL I ↔ ∀ i j, (i ∉ I ∨ j ∉ I) →
      (A : Matrix (Fin 5) (Fin 5) F) i j = (1 : Matrix (Fin 5) (Fin 5) F) i j :=
  Iff.rfl

theorem blkGL_mono {I J : Finset (Fin 5)} (h : I ⊆ J) : blkGL (F := F) I ≤ blkGL J :=
  fun _ hA i j hij => hA i j (hij.imp (fun hi hiI => hi (h hiI)) (fun hj hjI => hj (h hjI)))

theorem entry_eq_zero_of_comm {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) {c : GL (Fin 5) F}
    (hc : c * sgnGL ε hε = sgnGL ε hε * c) {i j : Fin 5} (hij : ε i ≠ ε j) :
    (c : Matrix (Fin 5) (Fin 5) F) i j = 0 := by
  have h := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) i j) hc
  simp only [Units.val_mul, coe_sgnGL, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h' : (c : Matrix (Fin 5) (Fin 5) F) i j * (ε j - ε i) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0).symm hij

theorem comm_of_entry {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) {c : GL (Fin 5) F}
    (h : ∀ i j, ε i ≠ ε j → (c : Matrix (Fin 5) (Fin 5) F) i j = 0) :
    c * sgnGL ε hε = sgnGL ε hε * c := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, coe_sgnGL, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : ε i = ε j
  · rw [hij, mul_comm]
  · rw [h i j hij, zero_mul, mul_zero]

@[expose] def oneAt (m : Fin 5) : Fin 5 → F := fun i => if i = m then 1 else -1

theorem oneAt_sq (m i : Fin 5) : oneAt (F := F) m i * oneAt m i = 1 := by
  unfold oneAt
  split_ifs <;> simp

theorem prod_oneAt (m : Fin 5) : ∏ i, oneAt (F := F) m i = 1 := by
  rw [Fin.prod_univ_five]
  fin_cases m <;> simp [oneAt]

theorem oneAt_ne (h2 : (2 : F) ≠ 0) {m i : Fin 5} (hi : i ≠ m) : oneAt (F := F) m i ≠ oneAt m m := by
  have e1 : oneAt (F := F) m i = -1 := by simp [oneAt, hi]
  have e2 : oneAt (F := F) m m = 1 := by simp [oneAt]
  rw [e1, e2]
  exact neg_one_ne_one h2

theorem stdSign_four : stdSign (F := F) 4 = oneAt 4 := by
  funext i
  fin_cases i <;> simp [stdSign, oneAt]

theorem prod_stdSign {k : ℕ} (hk : k = 2 ∨ k = 4) : ∏ i, stdSign (F := F) k i = 1 := by
  rw [Fin.prod_univ_five]
  rcases hk with rfl | rfl <;> simp [stdSign]

theorem eq_one_or_neg_one_of_sq (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 2) (Fin 2) F} (hA : A * A = 1)
    (hdet : A.det = 1) : A = 1 ∨ A = -1 := by
  rw [Matrix.det_fin_two] at hdet
  have h00 := congrFun (congrFun hA 0) 0
  have h01 := congrFun (congrFun hA 0) 1
  have h10 := congrFun (congrFun hA 1) 0
  have h11 := congrFun (congrFun hA 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  have htr : A 0 0 + A 1 1 ≠ 0 := by
    intro h
    apply h2
    have : A 1 1 = - A 0 0 := by linear_combination h
    rw [this] at hdet h11
    linear_combination -h00 - hdet
  have hb : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_right htr
  have hc : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.1 this).resolve_right htr
  rw [hb, zero_mul, add_zero] at h00
  rw [hc, zero_mul, zero_add] at h11
  rw [hb, zero_mul, sub_zero] at hdet
  have had : A 0 0 = A 1 1 := by
    have : A 0 0 * (A 0 0 - A 1 1) = 0 := by linear_combination h00 - hdet
    rcases mul_eq_zero.1 this with h | h
    · rw [h, mul_zero] at h00
      exact absurd h00 (zero_ne_one)
    · exact sub_eq_zero.1 h
  rcases eq_one_or_neg_one h00 with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, h]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, h]

theorem stdSign_two_lo {i : Fin 5} (hi : i.val < 2) : stdSign (F := F) 2 i = -1 := by
  simp [stdSign, hi]

theorem stdSign_two_hi {i : Fin 5} (hi : 2 ≤ i.val) : stdSign (F := F) 2 i = 1 := by
  simp [stdSign, show ¬ i.val < 2 by omega]

theorem stdSign_two_ne (h2 : (2 : F) ≠ 0) {i j : Fin 5} (hi : i.val < 2) (hj : 2 ≤ j.val) :
    stdSign (F := F) 2 i ≠ stdSign 2 j := by
  rw [stdSign_two_lo hi, stdSign_two_hi hj]
  exact neg_one_ne_one h2

@[expose] def blk2 (A : Matrix (Fin 5) (Fin 5) F) : Matrix (Fin 2) (Fin 2) F :=
  !![A 0 0, A 0 1; A 1 0, A 1 1]

theorem blk2_one : blk2 (1 : Matrix (Fin 5) (Fin 5) F) = 1 := by
  rw [blk2, Matrix.one_fin_two]
  simp

theorem blk2_mul (A B : Matrix (Fin 5) (Fin 5) F) (h02 : A 0 2 = 0) (h03 : A 0 3 = 0)
    (h04 : A 0 4 = 0) (h12 : A 1 2 = 0) (h13 : A 1 3 = 0) (h14 : A 1 4 = 0) :
    blk2 (A * B) = blk2 A * blk2 B := by
  rw [blk2, blk2, blk2, Matrix.mul_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_five, h02, h03, h04, h12, h13, h14, zero_mul, add_zero]

theorem val_lt_two_of_not_mem {i : Fin 5} (h : i ∉ ({2, 3, 4} : Finset (Fin 5))) : i.val < 2 := by
  fin_cases i <;> simp_all

theorem val_lt_two_of_sign (h2 : (2 : F) ≠ 0) {i j : Fin 5} (hi : i.val < 2)
    (h : stdSign (F := F) 2 i = stdSign 2 j) : j.val < 2 := by
  by_contra hj
  push Not at hj
  exact stdSign_two_ne h2 hi hj h

theorem lt_two_cases {i : Fin 5} (hi : i.val < 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp_all

end Matrices

section Model

variable {F : Type} [Field F] {P : Type} [Group P]

structure Model (S : Subgroup (GL (Fin 5) F)) (π : ↥S →* P) : Prop where
  two : (2 : F) ≠ 0
  det : ∀ s ∈ S, (s : Matrix (Fin 5) (Fin 5) F).det = 1
  surj : Function.Surjective π
  ker : ∀ s : ↥S, π s = 1 → ∃ c : F,
    ((s : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = c • (1 : Matrix (Fin 5) (Fin 5) F)
  sgn : ∀ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1), ∏ i, ε i = 1 → sgnGL ε hε ∈ S
  quasi : ∀ m : Fin 5, CFSG.IsQuasisimple ↥(((blkGL (Finset.univ.erase m)).comap S.subtype).map π)
  std : ∀ v : P, v * v = 1 → v ≠ 1 → ∃ k, (k = 2 ∨ k = 4) ∧ ∃ g : P, ∃ s : ↥S,
    (s : GL (Fin 5) F) = sgnGL (stdSign k) (stdSign_sq k) ∧ g * v * g⁻¹ = π s

@[expose] def blkP (S : Subgroup (GL (Fin 5) F)) (π : ↥S →* P) (I : Finset (Fin 5)) : Subgroup P :=
  ((blkGL I).comap S.subtype).map π

namespace Model

variable {S : Subgroup (GL (Fin 5) F)} {π : ↥S →* P} (M : Model S π)
include M

theorem scalar_of_ker {s : ↥S} (hs : π s = 1) : ∃ c : F,
    ((s : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = c • (1 : Matrix (Fin 5) (Fin 5) F) ∧ c ^ 5 = 1 := by
  obtain ⟨c, hc⟩ := M.ker s hs
  refine ⟨c, hc, ?_⟩
  have := M.det _ s.2
  rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
  exact this

theorem eq_of_sq {u w : ↥S} (hu : u * u = 1) (hw : w * w = 1) (h : π u = π w) : u = w := by
  have hz : π (u * w⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, hc, hc5⟩ := M.scalar_of_ker hz
  have hu' : ((u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      c • ((w : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    have e : (u : GL (Fin 5) F) = ((u * w⁻¹ : ↥S) : GL (Fin 5) F) * (w : GL (Fin 5) F) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [e, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul]
  have hsq : c * c = 1 := by
    have h1 : ((u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * ((u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, hu]
      rfl
    have h2 : ((w : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * ((w : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, hw]
      rfl
    rw [hu', Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this
  have hc1 : c = 1 := by
    calc c = c * (c * c) * (c * c) := by rw [hsq]; ring
      _ = c ^ 5 := by ring
      _ = 1 := hc5
  have : u * w⁻¹ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc1, one_smul]
    rfl
  exact mul_inv_eq_one.1 this

theorem comm_of_comm {t c : ↥S} (ht : t * t = 1) (h : π c * π t = π t * π c) : c * t = t * c := by
  have hsq : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := by
    calc (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hπ : π (c * t * c⁻¹) = π t := by
    rw [map_mul, map_mul, map_inv, h]
    group
  have := M.eq_of_sq hsq ht hπ
  calc c * t = (c * t * c⁻¹) * c := by group
    _ = t * c := by rw [this]

theorem centralizer_proj {t : ↥S} (ht : t * t = 1) :
    centralizer ({π t} : Set P) = (centralizer ({t} : Set ↥S)).map π := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := M.surj x
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    exact ⟨c, Subgroup.mem_centralizer_singleton_iff.2 (M.comm_of_comm ht hx), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']

theorem exists_lift_sq {a : P} (ha : a * a = 1) : ∃ b : ↥S, b * b = 1 ∧ π b = a := by
  obtain ⟨b, hb⟩ := M.surj a
  have hz : π (b * b) = 1 := by rw [map_mul, hb, ha]
  obtain ⟨c, hc, hc5⟩ := M.scalar_of_ker hz
  refine ⟨b ^ 5, ?_, ?_⟩
  · have h1 : b ^ 5 * b ^ 5 = (b * b) ^ 5 := by
      calc b ^ 5 * b ^ 5 = b ^ 10 := by rw [← pow_add]
        _ = (b * b) ^ 5 := by rw [← sq, ← pow_mul]
    rw [h1]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, smul_pow, one_pow, hc5, one_smul]
    rfl
  · rw [map_pow, hb]
    calc a ^ 5 = (a * a) * (a * a) * a := by
          rw [show (5 : ℕ) = 2 + 2 + 1 from rfl, pow_add, pow_add, sq, pow_one]
      _ = a := by rw [ha]; group

theorem mem_of_sq {Y : Subgroup ↥S} {u : ↥S} (hu : u * u = 1) (h : π u ∈ Y.map π) : u ∈ Y := by
  obtain ⟨y, hy, hyu⟩ := h
  have hz : π (u * y⁻¹) = 1 := by rw [map_mul, map_inv, hyu, mul_inv_cancel]
  obtain ⟨c, hc, hc5⟩ := M.scalar_of_ker hz
  have hu5 : u ^ 5 = u := by
    calc u ^ 5 = (u ^ 2) ^ 2 * u := by rw [← pow_mul, ← pow_succ]
      _ = (u * u) * (u * u) * u := by rw [sq, sq]
      _ = u := by rw [hu]; group
  have hmat : ((u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      c • ((y : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    have e : (u : GL (Fin 5) F) = ((u * y⁻¹ : ↥S) : GL (Fin 5) F) * (y : GL (Fin 5) F) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [e, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul]
  have : u = y ^ 5 := by
    rw [← hu5]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hmat,
      smul_pow, hc5, one_smul]
  rw [this]
  exact Y.pow_mem hy 5

@[expose] def sgnS (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) : ↥S :=
  ⟨sgnGL ε hε, M.sgn ε hε hdet⟩

theorem sgnS_sq (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) :
    M.sgnS ε hε hdet * M.sgnS ε hε hdet = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [sgnS, Subgroup.coe_mul, Units.val_mul, coe_sgnGL, Matrix.diagonal_mul_diagonal,
    Subgroup.coe_one, Units.val_one]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  exact hε i

theorem entry_eq_zero {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) {c : ↥S}
    (hc : c ∈ centralizer ({M.sgnS ε hε hdet} : Set ↥S)) {i j : Fin 5} (hij : ε i ≠ ε j) :
    ((c : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i j = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : (c : GL (Fin 5) F) * sgnGL ε hε = sgnGL ε hε * (c : GL (Fin 5) F) := by
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, sgnS] at this
    exact this
  exact entry_eq_zero_of_comm hε hc' hij

@[expose] noncomputable def entryHom (m : Fin 5) :
    ↥(centralizer ({M.sgnS (oneAt m) (oneAt_sq m) (prod_oneAt m)} : Set ↥S)) →* Fˣ :=
  MonoidHom.toHomUnits
    { toFun := fun c => (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) m m
      map_one' := by simp
      map_mul' := by
        intro c d
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
        rw [Finset.sum_eq_single m]
        · intro k _ hk
          rw [M.entry_eq_zero (oneAt_sq m) (prod_oneAt m) c.2 (oneAt_ne M.two hk).symm, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ m) h }

theorem entryHom_apply (m : Fin 5) (c) :
    ((M.entryHom m c : Fˣ) : F) = (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) m m := rfl

theorem map_ker_entryHom (m : Fin 5) :
    (M.entryHom m).ker.map (centralizer ({M.sgnS (oneAt m) (oneAt_sq m) (prod_oneAt m)} : Set ↥S)).subtype =
      (blkGL (Finset.univ.erase m)).comap S.subtype := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd : M.entryHom m d = 1 := hd
    have hdm : (((d : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) m m = 1 := by
      have := congrArg Units.val hd
      rw [entryHom_apply] at this
      exact this
    simp only [Subgroup.mem_comap, Subgroup.coe_subtype, mem_blkGL, Finset.mem_erase,
      Finset.mem_univ, and_true, not_not]
    intro i j hij
    rcases hij with rfl | rfl
    · by_cases hj : j = i
      · subst hj; rw [hdm, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne (Ne.symm hj)]
        exact M.entry_eq_zero (oneAt_sq _) (prod_oneAt _) d.2 (oneAt_ne M.two hj).symm
    · by_cases hi : i = j
      · subst hi; rw [hdm, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hi]
        exact M.entry_eq_zero (oneAt_sq _) (prod_oneAt _) d.2 (oneAt_ne M.two hi)
  · intro hc
    simp only [Subgroup.mem_comap, Subgroup.coe_subtype, mem_blkGL, Finset.mem_erase,
      Finset.mem_univ, and_true, not_not] at hc
    have hcent : c ∈ centralizer ({M.sgnS (oneAt m) (oneAt_sq m) (prod_oneAt m)} : Set ↥S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, sgnS]
      refine comm_of_entry (oneAt_sq m) fun i j hij => ?_
      have hne : i ≠ j := fun h => hij (h ▸ rfl)
      by_cases hi : i = m
      · rw [hc i j (Or.inl hi), Matrix.one_apply_ne hne]
      · by_cases hj : j = m
        · rw [hc i j (Or.inr hj), Matrix.one_apply_ne hne]
        · exact absurd (by simp [oneAt, hi, hj]) hij
    refine ⟨⟨c, hcent⟩, (MonoidHom.mem_ker).2 ?_, rfl⟩
    apply Units.ext
    rw [entryHom_apply, Units.val_one]
    show (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) m m = 1
    rw [hc m m (Or.inl rfl), Matrix.one_apply_eq]

theorem isCompIn_blk (m : Fin 5) :
    IsCompIn (centralizer ({π (M.sgnS (oneAt m) (oneAt_sq m) (prod_oneAt m))} : Set P))
      (blkP S π (Finset.univ.erase m)) := by
  set t := M.sgnS (oneAt m) (oneAt_sq m) (prod_oneAt m) with ht
  set X := centralizer ({t} : Set ↥S) with hX
  have hC : centralizer ({π t} : Set P) = (π.comp X.subtype).range := by
    rw [M.centralizer_proj (M.sgnS_sq _ _ _), MonoidHom.range_comp, Subgroup.range_subtype]
  have hB : blkP S π (Finset.univ.erase m) = (M.entryHom m).ker.map (π.comp X.subtype) := by
    rw [blkP, ← M.map_ker_entryHom m, Subgroup.map_map]
  have hle : blkP S π (Finset.univ.erase m) ≤ centralizer ({π t} : Set P) := by
    rw [hB, hC]
    exact Subgroup.map_le_range _ _
  refine ⟨hle, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm (M.quasi m)
  · refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : P) ∈ (π.comp X.subtype).range := hC ▸ g.2
    obtain ⟨y, hy⟩ := hg
    rw [hB] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := hn
    have hk' : M.entryHom m k = 1 := hk
    refine ⟨y * k * y⁻¹, (MonoidHom.mem_ker).2 ?_, ?_⟩
    · rw [map_mul, map_mul, hk', mul_one, map_inv, mul_inv_cancel]
    · simp only [map_mul, map_inv, hy, hkn, Subgroup.coe_mul, Subgroup.coe_inv]

theorem coe_sgnS (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) :
    ((M.sgnS ε hε hdet : ↥S) : GL (Fin 5) F) = sgnGL ε hε := rfl

theorem sgnS_ne_one {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) {i j : Fin 5}
    (hij : ε i ≠ ε j) : π (M.sgnS ε hε hdet) ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := M.ker _ h1
  apply hij
  have hi := congrFun (congrFun hc i) i
  have hj := congrFun (congrFun hc j) j
  rw [coe_sgnS, coe_sgnGL, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at hi hj
  rw [hi, hj]

theorem sgnS_oneAt_mem_blk (m : Fin 5) :
    M.sgnS (oneAt m) (oneAt_sq m) (prod_oneAt m) ∈ (blkGL (Finset.univ.erase m)).comap S.subtype := by
  simp only [Subgroup.mem_comap, Subgroup.coe_subtype, mem_blkGL, Finset.mem_erase,
    Finset.mem_univ, and_true, not_not]
  intro i j hij
  rw [coe_sgnS, coe_sgnGL]
  by_cases hij' : i = j
  · subst hij'
    rcases hij with rfl | rfl <;> simp [oneAt]
  · rw [Matrix.diagonal_apply_ne _ hij', Matrix.one_apply_ne hij']

theorem false_of_four [Finite P] {L : Subgroup P}
    (hL : IsCompIn (centralizer ({π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4))} : Set P)) L)
    (hZ : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z * z = 1 → z = 1) : False := by
  set t := M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4) with ht
  set X := centralizer ({t} : Set ↥S) with hX
  have hC : centralizer ({π t} : Set P) = (π.comp X.subtype).range := by
    rw [M.centralizer_proj (M.sgnS_sq _ _ _), MonoidHom.range_comp, Subgroup.range_subtype]
  have hq := isQuasisimple_of_isCompIn hL
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  have hLB : L ≤ blkP S π (Finset.univ.erase 4) := by
    have h1 := le_map_ker_of_perfect (π.comp X.subtype) (M.entryHom 4) (by rw [← hC]; exact hL.1) hperf
    rw [blkP, ← M.map_ker_entryHom 4, Subgroup.map_map]
    exact h1
  have heq := eq_of_isCompIn_le hL (M.isCompIn_blk 4) hLB
  have htL : π t ∈ L := by
    rw [heq]
    exact Subgroup.mem_map_of_mem π (M.sgnS_oneAt_mem_blk 4)
  have htc : ∀ l ∈ L, π t * l = l * π t := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hl)).symm
  have htt : π t * π t = 1 := by rw [← map_mul, M.sgnS_sq, map_one]
  exact M.sgnS_ne_one (oneAt_sq 4) (prod_oneAt 4) (i := 0) (j := 4) (oneAt_ne M.two (by decide))
    (hZ _ htL htc htt)

@[expose] noncomputable def blk2Hom (Z : Subgroup ↥S)
    (hZ : Z ≤ centralizer ({M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl))} : Set ↥S)) :
    ↥Z →* Matrix (Fin 2) (Fin 2) F where
  toFun c := blk2 (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
  map_one' := blk2_one
  map_mul' := by
    intro c d
    have hz : ∀ i j : Fin 5, i.val < 2 → 2 ≤ j.val →
        (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i j = 0 :=
      fun i j hi hj => M.entry_eq_zero _ _ (hZ c.2) (stdSign_two_ne M.two hi hj)
    exact blk2_mul _ _ (hz 0 2 (by decide) (by decide)) (hz 0 3 (by decide) (by decide))
      (hz 0 4 (by decide) (by decide)) (hz 1 2 (by decide) (by decide)) (hz 1 3 (by decide) (by decide))
      (hz 1 4 (by decide) (by decide))

theorem blk2Hom_apply (Z : Subgroup ↥S) (hZ) (c : ↥Z) :
    M.blk2Hom Z hZ c = blk2 (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := rfl

theorem le_blk_of_two [Finite P] {L : Subgroup P}
    (hL : IsCompIn (centralizer ({π (M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)))} :
      Set P)) L)
    (hZ : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z * z = 1 → z = 1)
    (h4 : ∃ a ∈ L, ∃ b ∈ L, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) :
    L ≤ blkP S π {2, 3, 4} := by
  set t := M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)) with ht
  set X := centralizer ({t} : Set ↥S) with hX
  have hC : centralizer ({π t} : Set P) = (π.comp X.subtype).range := by
    rw [M.centralizer_proj (M.sgnS_sq _ _ _), MonoidHom.range_comp, Subgroup.range_subtype]
  have hq := isQuasisimple_of_isCompIn hL
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  set ψ : ↥X →* Fˣ := (Matrix.detMonoidHom.comp (M.blk2Hom X le_rfl)).toHomUnits with hψ
  have h1 : L ≤ ψ.ker.map (π.comp X.subtype) :=
    le_map_ker_of_perfect _ ψ (by rw [← hC]; exact hL.1) hperf
  set Y : Subgroup ↥S := ψ.ker.map X.subtype with hY
  have hYX : Y ≤ X := Subgroup.map_subtype_le _
  have hLY : L ≤ Y.map π := by
    rw [hY, Subgroup.map_map]
    exact h1
  have hLY' : L ≤ (π.comp Y.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hLY
  have hdetY : ∀ y ∈ Y, (blk2 (((y : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)).det = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ψ x = 1 := hx
    have := congrArg Units.val hx'
    exact this
  obtain ⟨a, ha, b, hb, haa, hbb, ha1, hb1, hab, habc⟩ := h4
  obtain ⟨a', ha'a', ha'⟩ := M.exists_lift_sq haa
  obtain ⟨b', hb'b', hb'⟩ := M.exists_lift_sq hbb
  have ha'Y : a' ∈ Y := M.mem_of_sq ha'a' (by rw [ha']; exact hLY ha)
  have hb'Y : b' ∈ Y := M.mem_of_sq hb'b' (by rw [hb']; exact hLY hb)
  have hcomm : a' * b' = b' * a' := by
    have hsq : (a' * b' * a'⁻¹) * (a' * b' * a'⁻¹) = 1 := by
      calc (a' * b' * a'⁻¹) * (a' * b' * a'⁻¹) = a' * (b' * b') * a'⁻¹ := by group
        _ = 1 := by rw [hb'b']; group
    have hπ : π (a' * b' * a'⁻¹) = π b' := by
      rw [map_mul, map_mul, map_inv, ha', hb', habc]
      group
    have := M.eq_of_sq hsq hb'b' hπ
    calc a' * b' = (a' * b' * a'⁻¹) * a' := by group
      _ = b' * a' := by rw [this]
  have hblk : ∀ (y : ↥S) (hy : y ∈ Y), y * y = 1 →
      blk2 (((y : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 ∨
        blk2 (((y : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = -1 := by
    intro y hy hyy
    refine eq_one_or_neg_one_of_sq M.two ?_ (hdetY y hy)
    have h := congrArg (M.blk2Hom Y hYX) (show (⟨y, hy⟩ : ↥Y) * ⟨y, hy⟩ = 1 from Subtype.ext hyy)
    rw [map_mul, map_one] at h
    exact h
  have hinv : ∀ w ∈ L, w * w = 1 → w ≠ 1 → ¬ ∀ l ∈ L, w * l = l * w :=
    fun w hw hww hw1 hc => hw1 (hZ w hw hc hww)
  have key : ∃ u : ↥Y, M.blk2Hom Y hYX u = 1 ∧ (π.comp Y.subtype) u ∈ L ∧
      ¬ ∀ l ∈ L, (π.comp Y.subtype) u * l = l * (π.comp Y.subtype) u := by
    rcases hblk a' ha'Y ha'a' with hA | hA
    · exact ⟨⟨a', ha'Y⟩, hA, by simpa [ha'] using ha, by simpa [ha'] using hinv a ha haa ha1⟩
    rcases hblk b' hb'Y hb'b' with hB | hB
    · exact ⟨⟨b', hb'Y⟩, hB, by simpa [hb'] using hb, by simpa [hb'] using hinv b hb hbb hb1⟩
    refine ⟨⟨a', ha'Y⟩ * ⟨b', hb'Y⟩, ?_, ?_, ?_⟩
    · rw [map_mul, blk2Hom_apply, blk2Hom_apply]
      simp only
      rw [hA, hB, neg_mul_neg, one_mul]
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, ha', hb']
      exact L.mul_mem ha hb
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, ha', hb']
      refine hinv (a * b) (L.mul_mem ha hb) ?_ ?_
      · calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [habc]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [haa, hbb, one_mul]
      · intro h
        apply hab
        calc a = a * (b * b) := by rw [hbb, mul_one]
          _ = (a * b) * b := by group
          _ = b := by rw [h, one_mul]
  obtain ⟨u, hu1, huL, hnc⟩ := key
  have h2 := le_map_ker_of_quasisimple (π.comp Y.subtype) (M.blk2Hom Y hYX) hq hLY' hu1 huL hnc
  refine h2.trans ?_
  rw [blkP, ← Subgroup.map_map]
  refine Subgroup.map_mono ?_
  rintro _ ⟨y, hy, rfl⟩
  have hy' : M.blk2Hom Y hYX y = 1 := hy
  rw [blk2Hom_apply] at hy'
  have hyX : (y : ↥S) ∈ X := hYX y.2
  have e00 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 0 0 = 1 := by
    simpa [blk2] using congrFun (congrFun hy' 0) 0
  have e01 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 0 1 = 0 := by
    simpa [blk2] using congrFun (congrFun hy' 0) 1
  have e10 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 1 0 = 0 := by
    simpa [blk2] using congrFun (congrFun hy' 1) 0
  have e11 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 1 1 = 1 := by
    simpa [blk2] using congrFun (congrFun hy' 1) 1
  have hz : ∀ i j : Fin 5, stdSign (F := F) 2 i ≠ stdSign 2 j →
      ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) i j = 0 :=
    fun i j hij => M.entry_eq_zero _ _ hyX hij
  simp only [Subgroup.mem_comap, Subgroup.coe_subtype, mem_blkGL]
  intro i j hij
  by_cases hs : stdSign (F := F) 2 i = stdSign 2 j
  · have hboth : i.val < 2 ∧ j.val < 2 := by
      rcases hij with hi | hj
      · have hi' := val_lt_two_of_not_mem hi
        exact ⟨hi', val_lt_two_of_sign M.two hi' hs⟩
      · have hj' := val_lt_two_of_not_mem hj
        exact ⟨val_lt_two_of_sign M.two hj' hs.symm, hj'⟩
    rcases lt_two_cases hboth.1 with rfl | rfl <;> rcases lt_two_cases hboth.2 with rfl | rfl
    · rw [e00, Matrix.one_apply_eq]
    · rw [e01, Matrix.one_apply_ne (by decide)]
    · rw [e10, Matrix.one_apply_ne (by decide)]
    · rw [e11, Matrix.one_apply_eq]
  · have hne : i ≠ j := fun h => hs (h ▸ rfl)
    rw [hz i j hs, Matrix.one_apply_ne hne]

theorem b3aAt_two [Finite P] (L : Subgroup P) :
    B3aAt (π (M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)))) L := by
  intro hL hZ h4
  have hLB := M.le_blk_of_two hL hZ h4
  set e := M.sgnS (oneAt 1) (oneAt_sq 1) (prod_oneAt 1) with he
  have hec : ∀ l ∈ L, π e * l = l * π e := by
    intro l hl
    obtain ⟨b, hb, rfl⟩ := hLB hl
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, he, coe_sgnS]
    refine (comm_of_entry (oneAt_sq 1) fun i j hij => ?_).symm
    have hb' : (b : GL (Fin 5) F) ∈ blkGL {2, 3, 4} := hb
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    have hout : i ∉ ({2, 3, 4} : Finset (Fin 5)) ∨ j ∉ ({2, 3, 4} : Finset (Fin 5)) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hi, hj⟩ := hcon
      apply hij
      have hi1 : i ≠ 1 := by rintro rfl; simp at hi
      have hj1 : j ≠ 1 := by rintro rfl; simp at hj
      simp [oneAt, hi1, hj1]
    rw [hb' i j hout, Matrix.one_apply_ne hne]
  have hee : π e * π e = 1 := by rw [← map_mul, M.sgnS_sq, map_one]
  have he1 : π e ≠ 1 :=
    M.sgnS_ne_one (oneAt_sq 1) (prod_oneAt 1) (i := 0) (j := 1) (oneAt_ne M.two (by decide))
  refine ⟨π e, hee, he1, hec, blkP S π (Finset.univ.erase 1), M.isCompIn_blk 1, ?_, ?_⟩
  · exact hLB.trans (Subgroup.map_mono (Subgroup.comap_mono (blkGL_mono (by decide))))
  · intro heq
    have heL : π e ∈ L := by
      rw [heq]
      exact Subgroup.mem_map_of_mem π (M.sgnS_oneAt_mem_blk 1)
    exact he1 (hZ _ heL hec hee)

theorem b3aAt_four [Finite P] (L : Subgroup P) :
    B3aAt (π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4))) L :=
  fun hL hZ _ => (M.false_of_four hL hZ).elim

theorem b3aAt [Finite P] {t : P} (ht : t * t = 1) (ht1 : t ≠ 1) (L : Subgroup P) : B3aAt t L := by
  obtain ⟨k, hk, g, s, hs, hg⟩ := M.std t ht ht1
  apply b3aAt_of_mulEquiv (MulAut.conj g)
  have hconj : (MulAut.conj g) t = π s := by rw [MulAut.conj_apply]; exact hg
  rw [hconj]
  rcases hk with rfl | rfl
  · have : s = M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)) := Subtype.ext hs
    rw [this]
    exact M.b3aAt_two _
  · have : s = M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4) := by
      apply Subtype.ext
      rw [hs, coe_sgnS]
      apply Units.ext
      rw [coe_sgnGL, coe_sgnGL, stdSign_four]
    rw [this]
    exact M.b3aAt_four _

end Model

@[expose] def B3aFact (J : Type) [Group J] : Prop :=
  ∀ t : J, t * t = 1 → t ≠ 1 → ∀ L : Subgroup J, B3aAt t L

theorem b3aFact_of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (h : B3aFact J') :
    B3aFact J := by
  intro t ht ht1 L
  apply b3aAt_of_mulEquiv e
  exact h (e t) (by rw [← map_mul, ht, map_one]) (fun h1 => ht1 (e.injective (by rw [h1, map_one]))) _

theorem Model.b3aFact [Finite P] {S : Subgroup (GL (Fin 5) F)} {π : ↥S →* P} (M : Model S π) :
    B3aFact P :=
  fun _ ht ht1 L => M.b3aAt ht ht1 L

end Model

end CFSG.GH74.Generic.BProg.B2.T4.B3aGen
