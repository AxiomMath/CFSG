module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Twist
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Tower
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.HSFLit.Sec5E

open Sec8

@[expose] def mT : TwData 2 where
  qmulT := 458142180
  qinvT := 228
  actT :=
    115250851497421717747342496335014895522487098589767803297517968855715194090000
  cocT := 1157425104503701504

@[expose] def nfTabT : ℕ :=
  76727831481120511368847570923555888528248416402920301246096430755815636369664 + 2 ^ 256 *
  (339934314352767261867520758278504887994)

theorem mT_valid : mT.Valid where
  qmul_assoc := by decide +kernel
  qone_mul := by decide +kernel
  qmul_one := by decide +kernel
  qinv_mul := by decide +kernel
  act_ex := by decide +kernel
  act_one := by decide +kernel
  act_mul := by decide +kernel
  coc_one_left := by decide +kernel
  coc_one_right := by decide +kernel
  coc_cocycle := by decide +kernel

abbrev T2M : Type := mT.Carrier

instance : Group T2M := TwData.group mT_valid

namespace T2M

@[expose] def x : T2M := ⟨0, 1⟩
@[expose] def w : T2M := ⟨0, 2⟩
@[expose] def z : T2M := ⟨1, 0⟩
@[expose] def y : T2M := ⟨2, 0⟩
@[expose] def t : T2M := ⟨4, 0⟩
@[expose] def k : T2M := ⟨8, 0⟩

@[expose] def gens : List T2M := [x, w, z, y, t, k]

@[expose] def nfBits (a : T2M) : List Bool :=
  (List.range 6).map fun i => (tget nfTabT 6 (16 * a.g.val + a.a.val)).testBit i

theorem nf_spec : ∀ a : T2M, a = nfProd gens (nfBits a) := by decide +kernel

structure PcX {X : Type*} [Group X] (x' w' z' y' t' k' : X) : Prop where
  x_sq : x' * x' = z'
  x_w : x' * w' * x'⁻¹ = w'
  x_z : x' * z' * x'⁻¹ = z'
  x_y : x' * y' * x'⁻¹ = z' * y'
  x_t : x' * t' * x'⁻¹ = t'
  x_k : x' * k' * x'⁻¹ = k'
  w_sq : w' * w' = 1
  w_z : w' * z' * w'⁻¹ = z'
  w_y : w' * y' * w'⁻¹ = y'
  w_t : w' * t' * w'⁻¹ = z' * t'
  w_k : w' * k' * w'⁻¹ = k'
  z_sq : z' * z' = 1
  z_y : z' * y' * z'⁻¹ = y'
  z_t : z' * t' * z'⁻¹ = t'
  z_k : z' * k' * z'⁻¹ = k'
  y_sq : y' * y' = 1
  y_t : y' * t' * y'⁻¹ = t'
  y_k : y' * k' * y'⁻¹ = k'
  t_sq : t' * t' = 1
  t_k : t' * k' * t'⁻¹ = k'
  k_sq : k' * k' = 1

theorem pcRel_of {X : Type*} [Group X] {x' w' z' y' t' k' : X}
    (h : PcX x' w' z' y' t' k') :
    PcRel [(x, x'), (w, w'), (z, z'), (y, y'), (t, t'), (k, k')] := by
  refine ⟨⟨[false, true, false, false, false], ?_, by simpa [nfProd] using h.x_sq⟩, ?_, ?_, ?_⟩
  · show x * x = nfProd [w, z, y, t, k] [false, true, false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · refine ⟨[true, false, false, false, false], ?_, by simpa [nfProd] using h.x_w⟩
      show x * w * x⁻¹ = nfProd [w, z, y, t, k] [true, false, false, false, false]
      decide +kernel
    · refine ⟨[false, true, false, false, false], ?_, by simpa [nfProd] using h.x_z⟩
      show x * z * x⁻¹ = nfProd [w, z, y, t, k] [false, true, false, false, false]
      decide +kernel
    · refine ⟨[false, true, true, false, false], ?_, by simpa [nfProd] using h.x_y⟩
      show x * y * x⁻¹ = nfProd [w, z, y, t, k] [false, true, true, false, false]
      decide +kernel
    · refine ⟨[false, false, false, true, false], ?_, by simpa [nfProd] using h.x_t⟩
      show x * t * x⁻¹ = nfProd [w, z, y, t, k] [false, false, false, true, false]
      decide +kernel
    · refine ⟨[false, false, false, false, true], ?_, by simpa [nfProd] using h.x_k⟩
      show x * k * x⁻¹ = nfProd [w, z, y, t, k] [false, false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 5, x ≠ nfProd [w, z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false, false, false], ?_, by simpa [nfProd] using h.w_sq⟩, ?_, ?_, ?_⟩
  · show w * w = nfProd [z, y, t, k] [false, false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨[true, false, false, false], ?_, by simpa [nfProd] using h.w_z⟩
      show w * z * w⁻¹ = nfProd [z, y, t, k] [true, false, false, false]
      decide +kernel
    · refine ⟨[false, true, false, false], ?_, by simpa [nfProd] using h.w_y⟩
      show w * y * w⁻¹ = nfProd [z, y, t, k] [false, true, false, false]
      decide +kernel
    · refine ⟨[true, false, true, false], ?_, by simpa [nfProd] using h.w_t⟩
      show w * t * w⁻¹ = nfProd [z, y, t, k] [true, false, true, false]
      decide +kernel
    · refine ⟨[false, false, false, true], ?_, by simpa [nfProd] using h.w_k⟩
      show w * k * w⁻¹ = nfProd [z, y, t, k] [false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 4, w ≠ nfProd [z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false, false], ?_, by simpa [nfProd] using h.z_sq⟩, ?_, ?_, ?_⟩
  · show z * z = nfProd [y, t, k] [false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨[true, false, false], ?_, by simpa [nfProd] using h.z_y⟩
      show z * y * z⁻¹ = nfProd [y, t, k] [true, false, false]
      decide +kernel
    · refine ⟨[false, true, false], ?_, by simpa [nfProd] using h.z_t⟩
      show z * t * z⁻¹ = nfProd [y, t, k] [false, true, false]
      decide +kernel
    · refine ⟨[false, false, true], ?_, by simpa [nfProd] using h.z_k⟩
      show z * k * z⁻¹ = nfProd [y, t, k] [false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 3, z ≠ nfProd [y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false], ?_, by simpa [nfProd] using h.y_sq⟩, ?_, ?_, ?_⟩
  · show y * y = nfProd [t, k] [false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨[true, false], ?_, by simpa [nfProd] using h.y_t⟩
      show y * t * y⁻¹ = nfProd [t, k] [true, false]
      decide +kernel
    · refine ⟨[false, true], ?_, by simpa [nfProd] using h.y_k⟩
      show y * k * y⁻¹ = nfProd [t, k] [false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 2, y ≠ nfProd [t, k] bs
    decide +kernel
  refine ⟨⟨[false], ?_, by simpa [nfProd] using h.t_sq⟩, ?_, ?_, ?_⟩
  · show t * t = nfProd [k] [false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · refine ⟨[true], ?_, by simpa [nfProd] using h.t_k⟩
      show t * k * t⁻¹ = nfProd [k] [true]
      decide +kernel
  · show ∀ bs ∈ allBits 1, t ≠ nfProd [k] bs
    decide +kernel
  refine ⟨⟨[], ?_, by simpa [nfProd] using h.k_sq⟩, ?_, ?_, ?_⟩
  · show k * k = nfProd [] []
    decide +kernel
  · intro r hr
    simp at hr
  · show ∀ bs ∈ allBits 0, k ≠ nfProd [] bs
    decide +kernel
  trivial


theorem exists_hom {X : Type*} [Group X] {x' w' z' y' t' k' : X}
    (h : PcX x' w' z' y' t' k') :
    ∃ ι : T2M →* X, ι x = x' ∧ ι w = w' ∧ ι z = z' ∧ ι y = y' ∧ ι t = t' ∧ ι k = k' := by
  obtain ⟨F, hF, -⟩ := exists_hom_of_pcRel _ (pcRel_of h) (fun a =>
    ⟨nfBits a, by simpa [nfBits] using mem_allBits (nfBits a), nf_spec a⟩)
  exact ⟨F, hF (x, x') (by simp), hF (w, w') (by simp), hF (z, z') (by simp),
    hF (y, y') (by simp), hF (t, t') (by simp), hF (k, k') (by simp)⟩

theorem center_cases : ∀ a : T2M, (∀ g ∈ gens, g * a = a * g) →
    a = 1 ∨ a = z ∨ a = k ∨ a = z * k := by
  decide +kernel

theorem card_eq : Nat.card T2M = 2 ^ 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (TwData.Carrier.equiv mT), Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  norm_num

theorem isPGroup : IsPGroup 2 T2M := IsPGroup.of_card card_eq

theorem injective_of {X : Type*} [Group X] (ι : T2M →* X) (hz : ι z ≠ 1) (hk : ι k ≠ 1)
    (hzk : ι z * ι k ≠ 1) : Function.Injective ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent T2M := isPGroup.isNilpotent
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨a, hak, hac⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  rcases center_cases a (fun g _ => Subgroup.mem_center_iff.mp hac g) with h1 | h1 | h1 | h1
  · exact ha1' h1
  · rw [h1] at hak; exact hz hak
  · rw [h1] at hak; exact hk hak
  · rw [h1] at hak
    have h2 : ι (z * k) = 1 := hak
    rw [map_mul] at h2
    exact hzk h2

@[expose] def homOf (ix iy iw it ik : T2M) (a : T2M) : T2M :=
  (if a.a.val.testBit 0 then ix * ix else 1) * (if a.a.val.testBit 1 then iy else 1) *
    (if a.a.val.testBit 2 then it else 1) * (if a.a.val.testBit 3 then ik else 1) *
    (if a.g.val.testBit 0 then ix else 1) * (if a.g.val.testBit 1 then iw else 1)

theorem elem_decomp : ∀ a : T2M, a = homOf x y w t k a := by decide +kernel

theorem map_eq_homOf {G : Type*} [Group G] (φ ψ : T2M →* G) {ix iy iw it ik : T2M}
    (hx : φ x = ψ ix) (hy : φ y = ψ iy) (hw : φ w = ψ iw) (ht : φ t = ψ it) (hk : φ k = ψ ik)
    (a : T2M) : φ a = ψ (homOf ix iy iw it ik a) := by
  conv_lhs => rw [elem_decomp a]
  simp only [homOf, map_mul, apply_ite φ, apply_ite ψ, map_one, hx, hy, hw, ht, hk]

section homOf

variable (ix iy iw it ik : T2M)

theorem homOf_t : homOf ix iy iw it ik t = it := by simp +decide [homOf]

end homOf

@[expose] def sw2 (a : T2M) : T2M := homOf (x * w) y w (y * t) k a

@[ext] structure SigD where
  ax : T2M
  ay : T2M
  aw : T2M
  bx : T2M
  by_ : T2M
  bw : T2M

instance SigD.instDecidableEq : DecidableEq SigD := fun p q =>
  if h : p.ax = q.ax ∧ p.ay = q.ay ∧ p.aw = q.aw ∧ p.bx = q.bx ∧ p.by_ = q.by_ ∧ p.bw = q.bw then
    isTrue (SigD.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  else isFalse fun e => h (by subst e; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

namespace SigD

variable (p : SigD)

@[expose] def sig (a : T2M) : T2M := homOf p.ax p.ay p.aw (t * k) (z * k) a

@[expose] def sigInv (a : T2M) : T2M := homOf p.bx p.by_ p.bw (t * k * z) (z * k) a

@[expose] def sw22 (a : T2M) : T2M := p.sig (sw2 (p.sigInv a))

@[expose] def sq (a : T2M) : T2M := p.sw22 (sw2 a)

@[expose] def sf (a : T2M) : T2M := p.sq (p.sq a)

end SigD

@[expose] def repList : List SigD := [
    ⟨⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨3, 1⟩, ⟨0, 2⟩⟩,
    ⟨⟨0, 1⟩, ⟨2, 1⟩, ⟨8, 2⟩, ⟨0, 1⟩, ⟨3, 1⟩, ⟨9, 2⟩⟩,
    ⟨⟨0, 1⟩, ⟨10, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨10, 1⟩, ⟨0, 2⟩⟩,
    ⟨⟨0, 1⟩, ⟨10, 1⟩, ⟨8, 2⟩, ⟨0, 1⟩, ⟨10, 1⟩, ⟨9, 2⟩⟩,
    ⟨⟨8, 1⟩, ⟨6, 1⟩, ⟨4, 3⟩, ⟨9, 1⟩, ⟨7, 1⟩, ⟨5, 3⟩⟩,
    ⟨⟨8, 1⟩, ⟨6, 1⟩, ⟨12, 3⟩, ⟨9, 1⟩, ⟨7, 1⟩, ⟨12, 3⟩⟩,
    ⟨⟨8, 1⟩, ⟨14, 1⟩, ⟨4, 3⟩, ⟨9, 1⟩, ⟨14, 1⟩, ⟨5, 3⟩⟩,
    ⟨⟨8, 1⟩, ⟨14, 1⟩, ⟨12, 3⟩, ⟨9, 1⟩, ⟨14, 1⟩, ⟨12, 3⟩⟩
  ]

@[expose] def repList' : List SigD := [
    ⟨⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨3, 1⟩, ⟨0, 2⟩⟩,
    ⟨⟨0, 1⟩, ⟨10, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨10, 1⟩, ⟨0, 2⟩⟩,
    ⟨⟨8, 1⟩, ⟨6, 1⟩, ⟨4, 3⟩, ⟨9, 1⟩, ⟨7, 1⟩, ⟨5, 3⟩⟩,
    ⟨⟨8, 1⟩, ⟨14, 1⟩, ⟨12, 3⟩, ⟨9, 1⟩, ⟨14, 1⟩, ⟨12, 3⟩⟩
  ]

@[expose] def InT (a : T2M) : Prop := a.g.val.testBit 1 = false

instance : DecidablePred InT := fun a => inferInstanceAs (Decidable (a.g.val.testBit 1 = false))

@[expose] def Zl : List T2M := [⟨0, 0⟩, ⟨1, 0⟩, ⟨8, 0⟩, ⟨9, 0⟩]

@[expose] def InE1 (a : T2M) : Prop := a.g = 0

instance : DecidablePred InE1 := fun a => inferInstanceAs (Decidable (a.g = 0))

@[expose] def E2l : List T2M := [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 0⟩, ⟨5, 0⟩, ⟨6, 1⟩, ⟨7, 1⟩,
  ⟨8, 0⟩, ⟨9, 0⟩, ⟨10, 1⟩, ⟨11, 1⟩, ⟨12, 0⟩, ⟨13, 0⟩, ⟨14, 1⟩, ⟨15, 1⟩]

@[expose] def E3l : List T2M := [⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨3, 0⟩, ⟨3, 2⟩,
  ⟨8, 0⟩, ⟨8, 2⟩, ⟨9, 0⟩, ⟨9, 2⟩, ⟨10, 0⟩, ⟨10, 2⟩, ⟨11, 0⟩, ⟨11, 2⟩]

@[expose] def E5l : List T2M := [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 3⟩, ⟨3, 3⟩, ⟨4, 3⟩, ⟨5, 3⟩, ⟨6, 0⟩, ⟨7, 0⟩,
  ⟨8, 0⟩, ⟨9, 0⟩, ⟨10, 3⟩, ⟨11, 3⟩, ⟨12, 3⟩, ⟨13, 3⟩, ⟨14, 0⟩, ⟨15, 0⟩]

@[expose] def tEl : List T2M := [⟨4, 0⟩, ⟨5, 0⟩, ⟨6, 0⟩, ⟨7, 0⟩, ⟨12, 0⟩, ⟨13, 0⟩, ⟨14, 0⟩, ⟨15, 0⟩]

namespace SigD

variable (p : SigD)

@[expose] def E6l : List T2M := E5l.map p.sig

@[expose] def E3'l : List T2M := E3l.map p.sig

@[expose] def S16 : List T2M :=
  tEl ++ tEl.map p.sig ++ tEl.map (fun e => sw2 (p.sig e)) ++
    tEl.map (fun e => p.sig (sw2 (p.sig e)))

@[expose] def reps (i : Fin 4) : T2M :=
  match i with
  | 0 => t
  | 1 => t * y
  | 2 => p.sig (t * y)
  | 3 => sw2 (p.sig (t * y))

@[expose] def InN (a : T2M) : Prop := a ∈ E3l ∧ a ∈ p.E3'l

instance : DecidablePred p.InN := fun a => inferInstanceAs (Decidable (a ∈ E3l ∧ a ∈ p.E3'l))

@[expose] def InM0 (a : T2M) : Prop := ∀ n ∈ E3l, n ∈ p.E3'l → a * n = n * a

instance : DecidablePred p.InM0 := fun a =>
  inferInstanceAs (Decidable (∀ n ∈ E3l, n ∈ p.E3'l → a * n = n * a))

@[expose] def ws : T2M := if p.sig w * w ∈ Zl then w else y * w

end SigD

end T2M

end CFSG.ComponentClassification.HSFLit.Sec5E
