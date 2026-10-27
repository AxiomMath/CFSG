module

public import CFSG.GH74.Generic.BProg.B2.T3S1Abs
public import CFSG.GH74.Generic.BProg.B3.S1DiagActFrame
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.GH74.Generic.BProg.B2.T3S1

open CFSG Matrix

variable {F : Type} [Field F]

@[expose] def IsSignVec (ε : Fin 4 → F) : Prop := (∀ i, ε i * ε i = 1) ∧ ε 0 * ε 1 * ε 2 * ε 3 = 1

variable (F) in
@[expose] def signDiag4 : Subgroup (GL (Fin 4) F) where
  carrier := {g | ∃ ε : Fin 4 → F, IsSignVec ε ∧ (g : Matrix (Fin 4) (Fin 4) F) = diagonal ε}
  mul_mem' := by
    rintro a b ⟨ε, ⟨hε, hεp⟩, ha⟩ ⟨δ, ⟨hδ, hδp⟩, hb⟩
    refine ⟨ε * δ, ⟨fun i => ?_, ?_⟩, ?_⟩
    · simp only [Pi.mul_apply]
      calc ε i * δ i * (ε i * δ i) = (ε i * ε i) * (δ i * δ i) := by ring
        _ = 1 := by rw [hε, hδ, one_mul]
    · simp only [Pi.mul_apply]
      calc ε 0 * δ 0 * (ε 1 * δ 1) * (ε 2 * δ 2) * (ε 3 * δ 3)
          = (ε 0 * ε 1 * ε 2 * ε 3) * (δ 0 * δ 1 * δ 2 * δ 3) := by ring
        _ = 1 := by rw [hεp, hδp, one_mul]
    · show ((a * b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
      rw [Units.val_mul, ha, hb, diagonal_mul_diagonal]
      rfl
  one_mem' := ⟨1, ⟨fun _ => mul_one 1, by simp⟩, by rw [Units.val_one]; exact diagonal_one.symm⟩
  inv_mem' := by
    rintro a ⟨ε, hε, ha⟩
    refine ⟨ε, hε, ?_⟩
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ha, diagonal_mul_diagonal, show (fun i => ε i * ε i) = fun _ => (1 : F) from funext hε.1,
      diagonal_one]

theorem comm_of_diag {g h : GL (Fin 4) F} {ε δ : Fin 4 → F}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = diagonal ε) (hh : (h : Matrix (Fin 4) (Fin 4) F) = diagonal δ) :
    g * h = h * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, hh, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem mul_self_of_mem_signDiag4 {g : GL (Fin 4) F} (hg : g ∈ signDiag4 F) : g * g = 1 := by
  obtain ⟨ε, hε, hg⟩ := hg
  apply Units.ext
  rw [Units.val_mul, hg, diagonal_mul_diagonal, Units.val_one,
    show (fun i => ε i * ε i) = fun _ => (1 : F) from funext hε.1, diagonal_one]

theorem comm_of_mem_signDiag4 {g h : GL (Fin 4) F} (hg : g ∈ signDiag4 F) (hh : h ∈ signDiag4 F) :
    g * h = h * g := by
  obtain ⟨ε, -, hg⟩ := hg
  obtain ⟨δ, -, hh⟩ := hh
  exact comm_of_diag hg hh

theorem det_of_mem_signDiag4 {g : GL (Fin 4) F} (hg : g ∈ signDiag4 F) :
    (g : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  obtain ⟨ε, ⟨-, hεp⟩, hg⟩ := hg
  rw [hg, det_diagonal, Fin.prod_univ_four, hεp]

theorem isElementaryAbelian_of_forall' {X : Type*} [Group X] {U : Subgroup X}
    (hab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hsq : ∀ u ∈ U, u * u = 1) :
    CFSG.IsElementaryAbelian 2 ↥U := CFSG.IsElementaryAbelian.two_of_forall_mul_self hab hsq

theorem eq_one_or_neg_one_of_mul_self {a : F} (ha : a * a = 1) : a = 1 ∨ a = -1 := by
  have : (a - 1) * (a + 1) = 0 := by linear_combination ha
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

@[expose] def bsign (b : Bool) : F := if b then -1 else 1

theorem bsign_mul_self (b : Bool) : (bsign b : F) * bsign b = 1 := by
  cases b <;> simp [bsign]

theorem bsign_injective (h2 : (2 : F) ≠ 0) : Function.Injective (bsign : Bool → F) := by
  have hneg : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination (-1 : F) * h
  intro a b hab
  cases a <;> cases b <;> simp_all [bsign, hneg.symm]

open Classical in
theorem bsign_decide {a : F} (ha : a * a = 1) : bsign (decide (a = -1)) = a := by
  unfold bsign
  split_ifs with h
  · exact (of_decide_eq_true h).symm
  · rcases eq_one_or_neg_one_of_mul_self ha with h1 | h1
    · exact h1.symm
    · exact absurd (decide_eq_true h1) h

@[expose] def signVec (s : Fin 3 → Bool) : Fin 4 → F :=
  ![bsign (s 0), bsign (s 1), bsign (s 2), bsign (s 0) * bsign (s 1) * bsign (s 2)]

theorem isSignVec_signVec (s : Fin 3 → Bool) : IsSignVec (signVec s : Fin 4 → F) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp only [signVec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, bsign_mul_self]
    calc bsign (s 0) * bsign (s 1) * bsign (s 2) * (bsign (s 0) * bsign (s 1) * bsign (s 2))
        = (bsign (s 0) * bsign (s 0)) * (bsign (s 1) * bsign (s 1)) *
            (bsign (s 2) * bsign (s 2)) := by ring
      _ = (1 : F) := by rw [bsign_mul_self, bsign_mul_self, bsign_mul_self]; ring
  · simp only [signVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    calc bsign (s 0) * bsign (s 1) * bsign (s 2) * (bsign (s 0) * bsign (s 1) * bsign (s 2))
        = (bsign (s 0) * bsign (s 0)) * (bsign (s 1) * bsign (s 1)) *
            (bsign (s 2) * bsign (s 2)) := by ring
      _ = (1 : F) := by rw [bsign_mul_self, bsign_mul_self, bsign_mul_self]; ring

@[expose] def signElt (s : Fin 3 → Bool) : ↥(signDiag4 F) :=
  ⟨⟨diagonal (signVec s), diagonal (signVec s), by
      rw [diagonal_mul_diagonal, show (fun i => (signVec s : Fin 4 → F) i * signVec s i) =
        fun _ => (1 : F) from funext (isSignVec_signVec s).1, diagonal_one], by
      rw [diagonal_mul_diagonal, show (fun i => (signVec s : Fin 4 → F) i * signVec s i) =
        fun _ => (1 : F) from funext (isSignVec_signVec s).1, diagonal_one]⟩,
    ⟨signVec s, isSignVec_signVec s, rfl⟩⟩

theorem card_signDiag4 (h2 : (2 : F) ≠ 0) : Nat.card ↥(signDiag4 F) = 8 := by
  classical
  have hbij : Function.Bijective (signElt : (Fin 3 → Bool) → ↥(signDiag4 F)) := by
    constructor
    · intro s t hst
      have h := congrArg (fun g : ↥(signDiag4 F) => ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hst
      simp only [signElt] at h
      have hd := Matrix.diagonal_injective h
      funext i
      fin_cases i
      · exact bsign_injective h2 (congrFun hd 0)
      · exact bsign_injective h2 (congrFun hd 1)
      · exact bsign_injective h2 (congrFun hd 2)
    · rintro ⟨g, ε, ⟨hε, hεp⟩, hg⟩
      refine ⟨fun i => decide (ε i.castSucc = -1), ?_⟩
      apply Subtype.ext
      apply Units.ext
      show diagonal (signVec _) = (g : Matrix (Fin 4) (Fin 4) F)
      rw [hg]
      congr 1
      have h3 : ε 3 = ε 0 * ε 1 * ε 2 := by
        have := hε 0
        have := hε 1
        have := hε 2
        linear_combination (ε 0 * ε 1 * ε 2) * hεp - ε 3 * (ε 1 * ε 1) * (ε 2 * ε 2) * hε 0 -
          ε 3 * (ε 2 * ε 2) * hε 1 - ε 3 * hε 2
      funext i
      fin_cases i
      · exact bsign_decide (hε 0)
      · exact bsign_decide (hε 1)
      · exact bsign_decide (hε 2)
      · show bsign _ * bsign _ * bsign _ = ε 3
        rw [h3]
        exact congr_arg₂ (· * ·) (congr_arg₂ (· * ·) (bsign_decide (hε 0)) (bsign_decide (hε 1)))
          (bsign_decide (hε 2))
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  simp

theorem exists_diag_frame (h2 : (2 : F) ≠ 0) (E : Subgroup (GL (Fin 4) F)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    ∃ P : GL (Fin 4) F, ∀ x ∈ E, ∃ μ : Fin 4 → F, (∀ j, μ j * μ j = 1) ∧
      ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal μ := by
  obtain ⟨b, μ, hb⟩ := B3.S1DiagActFrame.exists_eigenbasis h2 E hcomm hsq
  obtain ⟨P, hP⟩ := B3.S1DiagActFrame.exists_gl_of_basis b
  refine ⟨P, fun x hx => ⟨μ ⟨x, hx⟩, fun j => ?_, ?_⟩⟩
  · have h1 : Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        (Matrix.toLin' ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) (b j)) = b j := by
      have := congrArg (fun m : GL (Fin 4) F => Matrix.toLin' (m : Matrix (Fin 4) (Fin 4) F) (b j))
        (hsq x hx)
      simpa [B3.S1DiagActFrame.toLin'_gl_mul] using this
    rw [hb ⟨x, hx⟩, map_smul, hb ⟨x, hx⟩, smul_smul] at h1
    have h3 : (μ ⟨x, hx⟩ j * μ ⟨x, hx⟩ j - 1) • b j = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  · apply B3.S1DiagActFrame.conj_eq_diagonal
    rw [hP]
    exact B3.S1DiagActFrame.eigen_matrix b _ (μ ⟨x, hx⟩) (hb ⟨x, hx⟩)

theorem mem_signDiag4_of_frame {P x : GL (Fin 4) F} {μ : Fin 4 → F} (hμ : ∀ j, μ j * μ j = 1)
    (hx : ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal μ)
    (hdet : (x : Matrix (Fin 4) (Fin 4) F).det = 1) : P⁻¹ * x * P ∈ signDiag4 F := by
  refine ⟨μ, ⟨hμ, ?_⟩, hx⟩
  have h1 : ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  rw [hx, det_diagonal, Fin.prod_univ_four] at h1
  exact h1

theorem frame_mul_diag {P x d : GL (Fin 4) F} {δ : Fin 4 → F}
    (hd : (d : Matrix (Fin 4) (Fin 4) F) = diagonal δ) (hx : P⁻¹ * x * P ∈ signDiag4 F) :
    (P * d)⁻¹ * x * (P * d) ∈ signDiag4 F := by
  obtain ⟨ε, hε, hxε⟩ := hx
  have hc : (P⁻¹ * x * P) * d = d * (P⁻¹ * x * P) := comm_of_diag hxε hd
  have e : (P * d)⁻¹ * x * (P * d) = P⁻¹ * x * P := by
    calc (P * d)⁻¹ * x * (P * d) = d⁻¹ * ((P⁻¹ * x * P) * d) := by group
      _ = d⁻¹ * (d * (P⁻¹ * x * P)) := by rw [hc]
      _ = P⁻¹ * x * P := by group
  rw [e]
  exact ⟨ε, hε, hxε⟩

theorem isE8_comap {X : Type*} [Group X] (ι : X →* GL (Fin 4) F) (hι : Function.Injective ι)
    (h2 : (2 : F) ≠ 0) (P : GL (Fin 4) F) (hP : ∀ d ∈ signDiag4 F, P * d * P⁻¹ ∈ ι.range) :
    IsE8 (((signDiag4 F).map (MulAut.conj P).toMonoidHom).comap ι) := by
  set W : Subgroup (GL (Fin 4) F) := (signDiag4 F).map (MulAut.conj P).toMonoidHom with hW
  have hWι : W ≤ ι.range := by
    rintro _ ⟨d, hd, rfl⟩
    exact hP d hd
  have hWmem : ∀ w ∈ W, ∃ d ∈ signDiag4 F, w = P * d * P⁻¹ := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  refine ⟨isElementaryAbelian_of_forall' ?_ ?_, ?_⟩
  · intro u hu v hv
    apply hι
    obtain ⟨d, hd, hdu⟩ := hWmem _ hu
    obtain ⟨d', hd', hdv⟩ := hWmem _ hv
    rw [map_mul, map_mul, hdu, hdv]
    have := comm_of_mem_signDiag4 hd hd'
    calc P * d * P⁻¹ * (P * d' * P⁻¹) = P * (d * d') * P⁻¹ := by group
      _ = P * (d' * d) * P⁻¹ := by rw [this]
      _ = P * d' * P⁻¹ * (P * d * P⁻¹) := by group
  · intro u hu
    apply hι
    obtain ⟨d, hd, hdu⟩ := hWmem _ hu
    rw [map_mul, map_one, hdu]
    calc P * d * P⁻¹ * (P * d * P⁻¹) = P * (d * d) * P⁻¹ := by group
      _ = 1 := by rw [mul_self_of_mem_signDiag4 hd]; group
  · have hcard : Nat.card ↥(W.comap ι) = Nat.card ↥W := by
      refine Nat.card_congr (Equiv.ofBijective (fun x : ↥(W.comap ι) => (⟨ι x, x.2⟩ : ↥W)) ⟨?_, ?_⟩)
      · intro a b hab
        exact Subtype.ext (hι (congrArg Subtype.val hab))
      · rintro ⟨w, hw⟩
        obtain ⟨x, hx⟩ := hWι hw
        exact ⟨⟨x, show ι x ∈ W by rw [hx]; exact hw⟩, Subtype.ext hx⟩
    rw [hcard, hW, Subgroup.card_map_of_injective (MulAut.conj P).injective, card_signDiag4 h2]

theorem conj_of_frames {X : Type*} [Group X] (ι : X →* GL (Fin 4) F) (hι : Function.Injective ι)
    (h2 : (2 : F) ≠ 0) {E E' : Subgroup X} (hE : Nat.card E = 8) (hE' : Nat.card E' = 8)
    {P P' : GL (Fin 4) F} (hP : ∀ e ∈ E, P⁻¹ * ι e * P ∈ signDiag4 F)
    (hP' : ∀ e ∈ E', P'⁻¹ * ι e * P' ∈ signDiag4 F) {k : X} (hk : ι k = P' * P⁻¹) :
    E' = E.map (MulAut.conj k).toMonoidHom := by
  classical
  have : Finite ↥(signDiag4 F) := Nat.finite_of_card_ne_zero (by rw [card_signDiag4 h2]; norm_num)
  let f : ↥E → ↥(signDiag4 F) := fun e => ⟨P⁻¹ * ι e * P, hP e e.2⟩
  let f' : ↥E' → ↥(signDiag4 F) := fun e => ⟨P'⁻¹ * ι e * P', hP' e e.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : P⁻¹ * ι a * P = P⁻¹ * ι b * P := congrArg Subtype.val hab
    have h2 : ι a = ι b := by simpa using h1
    exact Subtype.ext (hι h2)
  have hf' : Function.Injective f' := by
    intro a b hab
    have h1 : P'⁻¹ * ι a * P' = P'⁻¹ * ι b * P' := congrArg Subtype.val hab
    have h2 : ι a = ι b := by simpa using h1
    exact Subtype.ext (hι h2)
  have hfb := hf.bijective_of_nat_card_le (by rw [card_signDiag4 h2, hE])
  have hfb' := hf'.bijective_of_nat_card_le (by rw [card_signDiag4 h2, hE'])
  have hkey : ∀ e e' : X, P⁻¹ * ι e * P = P'⁻¹ * ι e' * P' → e' = k * e * k⁻¹ := by
    intro e e' h
    apply hι
    rw [map_mul, map_mul, map_inv, hk]
    calc ι e' = P' * (P'⁻¹ * ι e' * P') * P'⁻¹ := by group
      _ = P' * (P⁻¹ * ι e * P) * P'⁻¹ := by rw [h]
      _ = P' * P⁻¹ * ι e * (P' * P⁻¹)⁻¹ := by group
  ext g
  constructor
  · intro hg
    obtain ⟨e, he⟩ := hfb.2 (f' ⟨g, hg⟩)
    have h1 : P⁻¹ * ι e * P = P'⁻¹ * ι g * P' := congrArg Subtype.val he
    refine ⟨e, e.2, ?_⟩
    rw [hkey _ _ h1]
    rfl
  · rintro ⟨e, he, rfl⟩
    obtain ⟨e', he'⟩ := hfb'.2 (f ⟨e, he⟩)
    have h1 : P⁻¹ * ι e * P = P'⁻¹ * ι e' * P' := (congrArg Subtype.val he').symm
    have h2 := hkey _ _ h1
    show k * e * k⁻¹ ∈ E'
    rw [← h2]
    exact e'.2

end CFSG.GH74.Generic.BProg.B2.T3S1
