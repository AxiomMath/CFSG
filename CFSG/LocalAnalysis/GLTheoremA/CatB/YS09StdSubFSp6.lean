module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09StdSubF
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB
  CFSG.Sporadic.Co2Smith Matrix

namespace StdSp6

@[expose] def Yp : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

@[expose] def Pm (a : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 2) := Yp ^ a.val

theorem Pm_add : ∀ a b : ZMod 3, Pm (a + b) = Pm a * Pm b := by decide

theorem Sv_h1 : ∀ v : ZMod 3 × ZMod 3 × ZMod 3,
    pb ![Pm v.1, Pm v.2.2, Pm v.2.1] * pb ![Pm (-v.1), Pm (-v.2.2), Pm (-v.2.1)] = 1 := by decide

theorem Sv_symp : ∀ v : ZMod 3 × ZMod 3 × ZMod 3,
    (pb ![Pm v.1, Pm v.2.2, Pm v.2.1]).transpose * Matrix.fromBlocks 0 1 (-1) 0 *
      pb ![Pm v.1, Pm v.2.2, Pm v.2.1] = Matrix.fromBlocks 0 1 (-1) 0 := by decide

theorem Sv_h2 : ∀ v : ZMod 3 × ZMod 3 × ZMod 3,
    pb ![Pm (-v.1), Pm (-v.2.2), Pm (-v.2.1)] * pb ![Pm v.1, Pm v.2.2, Pm v.2.1] = 1 := by decide

@[expose] def Sv (v : ZMod 3 × ZMod 3 × ZMod 3) : Sp62 :=
  mkSpG (pb ![Pm v.1, Pm v.2.2, Pm v.2.1]) (pb ![Pm (-v.1), Pm (-v.2.2), Pm (-v.2.1)])
    (Sv_h1 v) (Sv_h2 v) (Sv_symp v)

theorem Sv_mul (x y : ZMod 3 × ZMod 3 × ZMod 3) : Sv (x + y) = Sv x * Sv y :=
  Subtype.ext (Units.ext (by
    show pb ![Pm (x.1 + y.1), Pm (x.2.2 + y.2.2), Pm (x.2.1 + y.2.1)] =
      pb ![Pm x.1, Pm x.2.2, Pm x.2.1] * pb ![Pm y.1, Pm y.2.2, Pm y.2.1]
    rw [pb_mul]
    congr 1
    funext i
    fin_cases i <;> simp [Pm_add]))

@[expose] def tau6 : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* Sp62 :=
  MonoidHom.mk' (fun v => Sv v.toAdd) fun x y => Sv_mul x.toAdd y.toAdd

theorem tau6_key : ∀ v : ZMod 3 × ZMod 3 × ZMod 3,
    pb ![Pm v.1, Pm v.2.2, Pm v.2.1] = 1 → v = 0 := by decide

theorem tau6_injective : Function.Injective tau6 := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hm : pb ![Pm v.toAdd.1, Pm v.toAdd.2.2, Pm v.toAdd.2.1] = 1 := by
    have := congrArg (fun g : Sp62 => (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2))).val :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) hv
    exact this
  exact Multiplicative.toAdd.injective (tau6_key _ hm)

@[expose] def UM (p q r s c : ZMod 2) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.fromBlocks !![1, 0, 0; 0, 1, 0; r, s, 1] !![0, 0, p; 0, 0, q; p, q, c] 0
    !![1, 0, r; 0, 1, s; 0, 0, 1]

theorem UM_mul (p q r s c p' q' r' s' c' : ZMod 2) :
    UM p q r s c * UM p' q' r' s' c' =
      UM (p + p') (q + q') (r + r') (s + s') (c + c' + (p * r' + q * s' + r * p' + s * q')) := by
  unfold UM
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[expose] def Ux (x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  UM x.1 x.2.1 x.2.2.1 x.2.2.2.1 (x.2.2.2.2 + x.1 * x.2.2.1 + x.2.1 * x.2.2.2.1)

theorem Ux_one_mul : ∀ x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2,
    Ux x * Ux x = 1 := by decide

theorem Ux_mul (x y : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : Ux x * Ux y = Ux (x + y) := by
  show UM _ _ _ _ _ * UM _ _ _ _ _ = UM (x.1 + y.1) (x.2.1 + y.2.1) (x.2.2.1 + y.2.2.1)
    (x.2.2.2.1 + y.2.2.2.1) (x.2.2.2.2 + y.2.2.2.2 + (x.1 + y.1) * (x.2.2.1 + y.2.2.1) +
      (x.2.1 + y.2.1) * (x.2.2.2.1 + y.2.2.2.1))
  rw [UM_mul]
  congr 1
  ring

theorem Ux_symp : ∀ x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2,
    (Ux x).transpose * Matrix.fromBlocks 0 1 (-1) 0 * Ux x = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide

@[expose] def UMsp (x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : Sp62 :=
  mkSpG (Ux x) (Ux x) (Ux_one_mul x) (Ux_one_mul x) (Ux_symp x)

@[expose] def psi6 : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) →* Sp62 :=
  MonoidHom.mk' (fun x => UMsp x.toAdd) fun x y => Subtype.ext (Units.ext (Ux_mul x.toAdd y.toAdd).symm)

theorem psi6_injective : Function.Injective psi6 := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hm : Ux v.toAdd = 1 := by
    have := congrArg (fun g : Sp62 => (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2))).val :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) hv
    exact this
  have key : ∀ x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2, Ux x = 1 → x = 0 := by decide
  exact Multiplicative.toAdd.injective (key _ hm)

theorem card_T6 : Nat.card (psi6.range) = 2 ^ 5 := by
  rw [card_range_eq_of_injective psi6 psi6_injective, Nat.card_congr Multiplicative.toAdd,
    Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  norm_num

theorem isPGroup_T6 : IsPGroup 2 psi6.range := IsPGroup.of_card card_T6

@[expose] def actX (a c' : ZMod 3) (x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
  let p' := Pm a 0 0 * x.1 + Pm a 0 1 * x.2.2.1
  let q' := Pm c' 0 0 * x.2.1 + Pm c' 0 1 * x.2.2.2.1
  let r' := Pm a 1 0 * x.1 + Pm a 1 1 * x.2.2.1
  let s' := Pm c' 1 0 * x.2.1 + Pm c' 1 1 * x.2.2.2.1
  (p', q', r', s', x.2.2.2.2 + x.1 * x.2.2.1 + x.2.1 * x.2.2.2.1 + p' * r' + q' * s')

theorem conj_Sv : ∀ a c' : ZMod 3, ∀ x : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2,
    (Sv (a, 0, c') * UMsp x * (Sv (a, 0, c'))⁻¹ : Sp62).val = Ux (actX a c' x) := by
  decide +kernel

theorem conj_mem (a c' : ZMod 3) (y : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    Sv (a, 0, c') * UMsp y * (Sv (a, 0, c'))⁻¹ = UMsp (actX a c' y) :=
  Subtype.ext (Units.ext (conj_Sv a c' y))

theorem hFN_T6 (x : Multiplicative (ZMod 3 × ZMod 3)) (t : Sp62) (ht : t ∈ psi6.range) :
    tau6 (emb13 x) * t * (tau6 (emb13 x))⁻¹ ∈ psi6.range := by
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 ht
  have hτ : tau6 (emb13 x) = Sv (x.toAdd.1, 0, x.toAdd.2) := rfl
  have hψ : psi6 y = UMsp y.toAdd := rfl
  rw [hτ, hψ, conj_mem]
  exact MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (actX x.toAdd.1 x.toAdd.2 y.toAdd), rfl⟩

theorem hTc_T6 : ∃ t ∈ psi6.range, ∃ x : Multiplicative (ZMod 3 × ZMod 3),
    t * tau6 (emb13 x) ≠ tau6 (emb13 x) * t := by
  refine ⟨psi6 (Multiplicative.ofAdd (1, 0, 0, 0, 0)), MonoidHom.mem_range.2 ⟨_, rfl⟩,
    Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)), ?_⟩
  intro h
  have hτ : tau6 (emb13 (Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)))) =
      Sv (1, 0, 0) := rfl
  have hc : Sv (1, 0, 0) * psi6 (Multiplicative.ofAdd (1, 0, 0, 0, 0)) * (Sv (1, 0, 0))⁻¹ =
      psi6 (Multiplicative.ofAdd (1, 0, 0, 0, 0)) := by
    rw [← hτ, ← h, mul_inv_cancel_right]
  have hc' : Sv (1, 0, 0) * UMsp (1, 0, 0, 0, 0) * (Sv (1, 0, 0))⁻¹ = UMsp (1, 0, 0, 0, 0) := hc
  rw [conj_mem] at hc'
  have hv := congrArg (fun g : Sp62 => (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2))).val :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) hc'
  have hne : Ux (actX 1 0 (1, 0, 0, 0, 0)) ≠ Ux (1, 0, 0, 0, 0) := by decide
  exact hne hv

theorem card_center_dvd_two_sp6two (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G]
    [Finite G] {K : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K)
    (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isSp6two) :
    Nat.card (Subgroup.center ↥K) ∣ 2 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isSp6two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
  · rw [h1, h2] at hm
    have hdvd := card_center_dvd_of_table hGA hK hm (a := 1) (b := 1) (c := 2) (d := 1)
      (by decide) (by decide) (by norm_num)
    exact hdvd.trans (by norm_num)
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

end StdSp6

end CFSG.LocalAnalysis.GLTheoremA.CatB
