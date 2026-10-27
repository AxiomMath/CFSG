module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E5
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMB02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL.Q8

open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.Steinberg.Sp
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C5O (Om5Data)
open scoped Matrix MatrixGroups


section Prelim

variable {F : Type} [Field F]

theorem toGL_conjAut {R : Type*} [CommRing R] (d : GL (Fin 2) R) (b : SL(2, R)) :
    Matrix.SpecialLinearGroup.toGL (Q3T6.conjAut d b) =
      d * Matrix.SpecialLinearGroup.toGL b * d⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact Q3T6.coe_conjSL d b

theorem glm_refl (g : GL (Fin 2) F) : glm (RingEquiv.refl F) g = g := by
  apply Units.ext
  ext i j
  rfl

theorem mem_sup_of_commute {G : Type*} [Group G] {P Q : Subgroup G}
    (h : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) {e : G} (he : e ∈ P ⊔ Q) :
    ∃ x ∈ P, ∃ y ∈ Q, e = x * y := by
  rw [Subgroup.sup_eq_closure] at he
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ he
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, Q.one_mem, (mul_one x).symm⟩
    · exact ⟨1, P.one_mem, x, hx, (one_mul x).symm⟩
  · exact ⟨1, P.one_mem, 1, Q.one_mem, (mul_one 1).symm⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, P.mul_mem hy₁ hy₂, z₁ * z₂, Q.mul_mem hz₁ hz₂, ?_⟩
    calc y₁ * z₁ * (y₂ * z₂) = y₁ * (z₁ * y₂) * z₂ := by group
      _ = y₁ * (y₂ * z₁) * z₂ := by rw [← h y₂ hy₂ z₁ hz₁]
      _ = y₁ * y₂ * (z₁ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, P.inv_mem hy, z⁻¹, Q.inv_mem hz, ?_⟩
    calc (y * z)⁻¹ = z⁻¹ * y⁻¹ := by group
      _ = y⁻¹ * z⁻¹ := by rw [← h y⁻¹ (P.inv_mem hy) z⁻¹ (Q.inv_mem hz)]

theorem longBlock_mul_eq_one (a b : SL(2, F))
    (h : longBlock F 2 0 a * longBlock F 2 1 b = 1) : a = 1 ∧ b = 1 := by
  have hm := congrArg (mat 2 F) h
  rw [map_mul, map_one, mat_longBlock, mat_longBlock] at hm
  have e := fun i j => congrFun (congrFun hm i) j
  have e00 := e (Sum.inl 0) (Sum.inl 0)
  have e01 := e (Sum.inl 0) (Sum.inr 0)
  have e10 := e (Sum.inr 0) (Sum.inl 0)
  have e11 := e (Sum.inr 0) (Sum.inr 0)
  have f00 := e (Sum.inl 1) (Sum.inl 1)
  have f01 := e (Sum.inl 1) (Sum.inr 1)
  have f10 := e (Sum.inr 1) (Sum.inl 1)
  have f11 := e (Sum.inr 1) (Sum.inr 1)
  simp [blockMat, Matrix.mul_apply, Fintype.sum_sum_type] at e00 e01 e10 e11 f00 f01 f10 f11
  constructor
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [f00, f01, f10, f11]

end Prelim

section Share

structure TwinShareQ {Y₁ Y₂ : Type} [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    (Φ₁ : Set (Subgroup Y₁)) (A₁ A₁' : Subgroup Y₁) (z₁ a₁ b₁ : Y₁)
    (Φ₂ : Set (Subgroup Y₂)) (A₂ A₂' : Subgroup Y₂) (z₂ a₂ b₂ : Y₂)
    {M : Type} [Group M] [Finite M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) (L L' : Subgroup M) :
    Prop where
  data₁ : Om5Data Y₁ Φ₁ A₁ A₁' z₁ a₁ b₁
  data₂ : Om5Data Y₂ Φ₂ A₂ A₂' z₂ a₂ b₂
  sup : L ⊔ L' = ⊤
  odd₁ : Odd (Nat.card π₁.ker)
  odd₂ : Odd (Nat.card π₂.ker)
  map₁ : L.map π₁ ≤ A₁ ∧ L'.map π₁ ≤ A₁'
  map₂ : L.map π₂ ≤ A₂ ∧ L'.map π₂ ≤ A₂'
  card₁ : Nat.card (L.map π₁) = 8 ∧ Nat.card (L'.map π₁) = 8
  card₂ : Nat.card (L.map π₂) = 8 ∧ Nat.card (L'.map π₂) = 8

variable {F : Type} [Field F] (r : ZMod 3 ≃+* F)

theorem sub_eq_map_Qsub [Finite F] {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
    {z' : Y} (fr : Frame F Y Φ A A' z') (h2 : (2 : F) ≠ 0) (k : Fin 2) {H : Subgroup Y}
    (hH : H ≤ (longRootSp2 F 2 k).map fr.ψ) (hc : Nat.card H = 8) :
    H = (Qsub r).map (fr.ψ.comp (longBlock F 2 k)) :=
  eq_map_Qsub_of_card r _ (injective_ψ_longBlock fr h2 k) H (by rw [range_ψ_longBlock]; exact hH) hc

theorem exp4_of_twin {Y : Type} [Group Y] {P : Type} [Group P] (ψ : StatedSp 2 F →* Y) (π : P →* Y)
    {L L' : Subgroup P} (hsup : L ⊔ L' = ⊤)
    (hL : L.map π = (Qsub r).map (ψ.comp (longBlock F 2 0)))
    (hL' : L'.map π = (Qsub r).map (ψ.comp (longBlock F 2 1))) (m : P) : (π m) ^ 4 = 1 := by
  have hm : π m ∈ L.map π ⊔ L'.map π := by
    rw [← Subgroup.map_sup, hsup]
    exact ⟨m, trivial, rfl⟩
  have hcomm : ∀ x ∈ L.map π, ∀ y ∈ L'.map π, x * y = y * x := by
    intro x hx y hy
    rw [hL] at hx
    rw [hL'] at hy
    obtain ⟨b, -, rfl⟩ := hx
    obtain ⟨b', -, rfl⟩ := hy
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [← map_mul, ← map_mul, commute_L 0 (⟨b, rfl⟩ : longBlock F 2 0 b ∈ longRootSp2 F 2 0)
      (⟨b', rfl⟩ : longBlock F 2 1 b' ∈ longRootSp2 F 2 (Fin.rev 0))]
  obtain ⟨x, hx, y, hy, hxe⟩ := mem_sup_of_commute hcomm hm
  rw [hxe]
  have hxy : x * y = y * x := hcomm x hx y hy
  have hx4 : x ^ 4 = 1 := by
    rw [hL] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [← map_pow, ← map_pow, Qsub_one_pow r hb, map_one, map_one]
  have hy4 : y ^ 4 = 1 := by
    rw [hL'] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [← map_pow, ← map_pow, Qsub_one_pow r hb, map_one, map_one]
  rw [(show Commute x y from hxy).mul_pow, hx4, hy4, one_mul]

theorem pow4_of_block {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
    (fr : Frame F Y Φ A A' z') (h2 : (2 : F) ≠ 0) (k : Fin 2) {b : SL(2, F)}
    (h : (fr.ψ (longBlock F 2 k b)) ^ 4 = 1) : b ^ 4 = 1 := by
  have h1 : fr.ψ (longBlock F 2 k (b ^ 4)) = 1 := by
    rw [map_pow, map_pow]
    exact h
  have h1' : longBlock F 2 k (b ^ 4) ∈ fr.ψ.ker := h1
  rw [fr.ker, mem_spScalars_iff] at h1'
  rcases h1' with h1 | h1
  · exact longBlock_injective k (by rw [h1, map_one])
  · exact absurd (h1 ▸ (⟨b ^ 4, rfl⟩ : longBlock F 2 k (b ^ 4) ∈ longRootSp2 F 2 k))
      (negOne_not_mem_L h2 k)

theorem ker_le_of_exp4 {P Y Y' : Type} [Group P] [Group Y] [Group Y'] (πa : P →* Y) (πb : P →* Y')
    (hodd : Odd (Nat.card πa.ker)) (hexp : ∀ m, (πb m) ^ 4 = 1) : πa.ker ≤ πb.ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  have h1 : orderOf n ∣ Nat.card πa.ker := by
    have := orderOf_dvd_natCard (⟨n, hn⟩ : ↥πa.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hoddn : Odd (orderOf n) := Odd.of_dvd_nat hodd h1
  have h2 : orderOf (πb n) ∣ orderOf n := orderOf_map_dvd πb n
  have h3 : orderOf (πb n) ∣ 4 := orderOf_dvd_of_pow_eq_one (hexp n)
  have hodd' : Odd (orderOf (πb n)) := Odd.of_dvd_nat hoddn h2
  have hcop : Nat.Coprime (orderOf (πb n)) 4 := by
    have h22 : Nat.Coprime (orderOf (πb n)) 2 := Nat.coprime_two_right.mpr hodd'
    simpa using h22.pow_right 2
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h3)

variable {Y₁ Y₂ : Type} [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
  {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ a₁ b₁ : Y₁}
  {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ a₂ b₂ : Y₂}
  {M : Type} [Group M] [Finite M] {π₁ : M →* Y₁} {π₂ : M →* Y₂} {L L' : Subgroup M}

theorem TwinShareQ.setup
    (hT : TwinShareQ Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L') :
    ∃ (fr₁ : Frame (GaloisField 3 1) Y₁ Φ₁ A₁ A₁' z₁) (fr₂ : Frame (GaloisField 3 1) Y₂ Φ₂ A₂ A₂' z₂)
      (d : Fin 2 → GL (Fin 2) (GaloisField 3 1)),
      π₁.ker = π₂.ker ∧
      (∀ (k : Fin 2) (b : SL(2, GaloisField 3 1)), b ^ 4 = 1 →
        ∃ m : M, π₁ m = fr₁.ψ (longBlock (GaloisField 3 1) 2 k b)) ∧
      (∀ (k : Fin 2) (m : M) (b : SL(2, GaloisField 3 1)),
        π₁ m = fr₁.ψ (longBlock (GaloisField 3 1) 2 k b) → b ^ 4 = 1) ∧
      (∀ (k : Fin 2) (m : M) (b : SL(2, GaloisField 3 1)),
        π₂ m = fr₂.ψ (longBlock (GaloisField 3 1) 2 k b) → b ^ 4 = 1) ∧
      (∀ (k : Fin 2) (m : M) (b : SL(2, GaloisField 3 1)),
        π₁ m = fr₁.ψ (longBlock (GaloisField 3 1) 2 k b) →
          π₂ m = fr₂.ψ (longBlock (GaloisField 3 1) 2 k (Q3T6.conjAut (d k) b))) := by
  classical
  obtain ⟨fr₁⟩ := Q3T8.Asc77.C5O.M.exists_frame hT.data₁
  obtain ⟨fr₂⟩ := Q3T8.Asc77.C5O.M.exists_frame hT.data₂
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf 1 (by norm_num)
  have hF : Nat.card (GaloisField 3 1) = 3 := Q3T7P25.natCard_gf3
  haveI : Finite (GaloisField 3 1) := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨r⟩ := nonempty_ringEquiv hF
  have hL₁ := sub_eq_map_Qsub r fr₁ h2 0 (H := L.map π₁)
    (by rw [← fr₁.hA]; exact hT.map₁.1) hT.card₁.1
  have hL₁' := sub_eq_map_Qsub r fr₁ h2 1 (H := L'.map π₁)
    (by rw [← fr₁.hA']; exact hT.map₁.2) hT.card₁.2
  have hL₂ := sub_eq_map_Qsub r fr₂ h2 0 (H := L.map π₂)
    (by rw [← fr₂.hA]; exact hT.map₂.1) hT.card₂.1
  have hL₂' := sub_eq_map_Qsub r fr₂ h2 1 (H := L'.map π₂)
    (by rw [← fr₂.hA']; exact hT.map₂.2) hT.card₂.2
  have hexp₁ := exp4_of_twin r fr₁.ψ π₁ hT.sup hL₁ hL₁'
  have hexp₂ := exp4_of_twin r fr₂.ψ π₂ hT.sup hL₂ hL₂'
  have hker : π₁.ker = π₂.ker :=
    le_antisymm (ker_le_of_exp4 π₁ π₂ hT.odd₁ hexp₂) (ker_le_of_exp4 π₂ π₁ hT.odd₂ hexp₁)
  let f₁ : Fin 2 → ↥(Qsub r) →* Y₁ := fun k =>
    (fr₁.ψ.comp (longBlock (GaloisField 3 1) 2 k)).comp (Qsub r).subtype
  let f₂ : Fin 2 → ↥(Qsub r) →* Y₂ := fun k =>
    (fr₂.ψ.comp (longBlock (GaloisField 3 1) 2 k)).comp (Qsub r).subtype
  have hf₁ : ∀ k, Function.Injective (f₁ k) := fun k =>
    (injective_ψ_longBlock fr₁ h2 k).comp (Subgroup.subtype_injective _)
  have hf₂ : ∀ k, Function.Injective (f₂ k) := fun k =>
    (injective_ψ_longBlock fr₂ h2 k).comp (Subgroup.subtype_injective _)
  have hr₁ : ∀ k, (f₁ k).range = (Qsub r).map (fr₁.ψ.comp (longBlock (GaloisField 3 1) 2 k)) :=
    fun k => by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hr₂ : ∀ k, (f₂ k).range = (Qsub r).map (fr₂.ψ.comp (longBlock (GaloisField 3 1) 2 k)) :=
    fun k => by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨θ₀, hθ₀⟩ := exists_twin_iso π₁ π₂ hker L (f₁ 0) (f₂ 0) (hf₁ 0) (hf₂ 0)
    (by rw [hL₁, hr₁]) (by rw [hL₂, hr₂])
  obtain ⟨θ₁, hθ₁⟩ := exists_twin_iso π₁ π₂ hker L' (f₁ 1) (f₂ 1) (hf₁ 1) (hf₂ 1)
    (by rw [hL₁', hr₁]) (by rw [hL₂', hr₂])
  obtain ⟨d₀, hd₀⟩ := exists_conj_of_aut r θ₀
  obtain ⟨d₁, hd₁⟩ := exists_conj_of_aut r θ₁
  have htoGL : ∀ x y : SL(2, GaloisField 3 1), Matrix.SpecialLinearGroup.toGL x =
      Matrix.SpecialLinearGroup.toGL y → x = y := fun x y h =>
    Subtype.ext (congrArg (fun u : GL (Fin 2) (GaloisField 3 1) =>
      (u : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) h)
  have hθc₀ : ∀ b : ↥(Qsub r), ((θ₀ b : ↥(Qsub r)) : SL(2, GaloisField 3 1)) =
      Q3T6.conjAut d₀ (b : SL(2, GaloisField 3 1)) := fun b =>
    htoGL _ _ (by rw [hd₀ b, toGL_conjAut])
  have hθc₁ : ∀ b : ↥(Qsub r), ((θ₁ b : ↥(Qsub r)) : SL(2, GaloisField 3 1)) =
      Q3T6.conjAut d₁ (b : SL(2, GaloisField 3 1)) := fun b =>
    htoGL _ _ (by rw [hd₁ b, toGL_conjAut])
  refine ⟨fr₁, fr₂, fun k => if k = 0 then d₀ else d₁, hker, ?_, ?_, ?_, ?_⟩
  · intro k b hb
    have hbQ : b ∈ Qsub r := (mem_Qsub r b).mpr hb
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · have : f₁ 0 ⟨b, hbQ⟩ ∈ L.map π₁ := by
        rw [hL₁, ← hr₁]
        exact ⟨_, rfl⟩
      obtain ⟨m, -, hm⟩ := this
      exact ⟨m, hm⟩
    · have : f₁ 1 ⟨b, hbQ⟩ ∈ L'.map π₁ := by
        rw [hL₁', ← hr₁]
        exact ⟨_, rfl⟩
      obtain ⟨m, -, hm⟩ := this
      exact ⟨m, hm⟩
  · intro k m b hm
    apply pow4_of_block fr₁ h2 k
    rw [← hm]
    exact hexp₁ m
  · intro k m b hm
    apply pow4_of_block fr₂ h2 k
    rw [← hm]
    exact hexp₂ m
  · intro k m b hm
    have hb : b ^ 4 = 1 := by
      apply pow4_of_block fr₁ h2 k
      rw [← hm]
      exact hexp₁ m
    have hbQ : b ∈ Qsub r := (mem_Qsub r b).mpr hb
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · have h1 := hθ₀ m ⟨b, hbQ⟩ hm
      simp only [if_true]
      rw [h1]
      show fr₂.ψ (longBlock (GaloisField 3 1) 2 0 ((θ₀ ⟨b, hbQ⟩ : ↥(Qsub r)) : SL(2, GaloisField 3 1))) = _
      rw [hθc₀]
    · have h1 := hθ₁ m ⟨b, hbQ⟩ hm
      simp only [one_ne_zero, if_false]
      rw [h1]
      show fr₂.ψ (longBlock (GaloisField 3 1) 2 1 ((θ₁ ⟨b, hbQ⟩ : ↥(Qsub r)) : SL(2, GaloisField 3 1))) = _
      rw [hθc₁]

end Share

section Rel

variable {F : Type} [Field F]
  {Y₁ : Type} [Group Y₁] {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ : Y₁}
  {Y₂ : Type} [Group Y₂] {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ : Y₂}
  {P : Type} [Group P]

theorem scl_of_comm (r : ZMod 3 ≃+* F) (H : GL (Fin 2) F)
    (h : ∀ b : SL(2, F), b ^ 4 = 1 →
      H * Matrix.SpecialLinearGroup.toGL b = Matrix.SpecialLinearGroup.toGL b * H) :
    ∃ ℓ : Fˣ, H = scl ℓ := by
  obtain ⟨c, hc⟩ := scalar_of_comm r (A := (H : Matrix (Fin 2) (Fin 2) F)) (fun b hb =>
    congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) (h b hb))
  have hdet : IsUnit (H : Matrix (Fin 2) (Fin 2) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp H.isUnit
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    rw [hc, Matrix.det_zero] at hdet
    exact not_isUnit_zero hdet
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, hc, Matrix.smul_one_eq_diagonal]
  rfl

theorem fix_block_relQ (r : ZMod 3 ≃+* F) (hF : Nat.card F = 3) (h2 : (2 : F) ≠ 0)
    (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁) (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂) (π₁ : P →* Y₁) (π₂ : P →* Y₂)
    (d : GL (Fin 2) F) (k : Fin 2)
    (hrel : ∀ (m : P) (b : SL(2, F)), π₁ m = fr₁.ψ (longBlock F 2 k b) →
      π₂ m = fr₂.ψ (longBlock F 2 k (Q3T6.conjAut d b)))
    (hsurj : ∀ b : SL(2, F), b ^ 4 = 1 → ∃ m : P, π₁ m = fr₁.ψ (longBlock F 2 k b))
    (γ₁ : Y₁ ≃* Y₁) (γ₂ : Y₂ ≃* Y₂) (G₁ G₂ : gsp 2 F) (σ₁ σ₂ : F ≃+* F)
    (hG₁ : ∀ x, γ₁ (fr₁.ψ x) = fr₁.ψ (conjSp 2 F G₁ (fieldSp 2 F σ₁ x)))
    (hG₂ : ∀ x, γ₂ (fr₂.ψ x) = fr₂.ψ (conjSp 2 F G₂ (fieldSp 2 F σ₂ x)))
    {g₁ g₂ : Fin 2 → GL (Fin 2) F}
    (hg₁ : gm G₁ = bd (fun k => (g₁ k : Matrix (Fin 2) (Fin 2) F)))
    (hg₂ : gm G₂ = bd (fun k => (g₂ k : Matrix (Fin 2) (Fin 2) F)))
    (hγ : ∀ m : P, ∃ m' : P, π₁ m' = γ₁ (π₁ m) ∧ π₂ m' = γ₂ (π₂ m)) :
    σ₁ = σ₂ ∧ ∃ ℓ : Fˣ, g₂ k * glm σ₂ d = scl ℓ * (d * g₁ k) := by
  have hσ₁ : σ₁ = RingEquiv.refl F := Q3T7P25.ringEquiv_eq3 hF _ _
  have hσ₂ : σ₂ = RingEquiv.refl F := Q3T7P25.ringEquiv_eq3 hF _ _
  have key : ∀ b : SL(2, F), b ^ 4 = 1 →
      Q3T6.conjAut d (slSemi (g₁ k) σ₁ b) = slSemi (g₂ k) σ₂ (Q3T6.conjAut d b) := by
    intro b hb
    obtain ⟨m, hm⟩ := hsurj b hb
    obtain ⟨m', e1, e2⟩ := hγ m
    rw [hm, hG₁, conjSp_fieldSp_longBlock_gl G₁ hg₁] at e1
    rw [hrel m b hm, hG₂, conjSp_fieldSp_longBlock_gl G₂ hg₂, hrel m' _ e1] at e2
    exact injective_ψ_longBlock fr₂ h2 k e2
  subst hσ₁ hσ₂
  refine ⟨rfl, ?_⟩
  have hcomm : ∀ b : SL(2, F), b ^ 4 = 1 →
      ((g₂ k * d)⁻¹ * (d * g₁ k)) * Matrix.SpecialLinearGroup.toGL b =
        Matrix.SpecialLinearGroup.toGL b * ((g₂ k * d)⁻¹ * (d * g₁ k)) := by
    intro b hb
    have e := congrArg Matrix.SpecialLinearGroup.toGL (key b hb)
    rw [toGL_conjAut, slg_slSemi, slg_slSemi, toGL_conjAut] at e
    simp only [glm_refl] at e
    calc (g₂ k * d)⁻¹ * (d * g₁ k) * Matrix.SpecialLinearGroup.toGL b =
        (g₂ k * d)⁻¹ * (d * (g₁ k * Matrix.SpecialLinearGroup.toGL b * (g₁ k)⁻¹) * d⁻¹) *
          (d * g₁ k) := by group
      _ = (g₂ k * d)⁻¹ * (g₂ k * (d * Matrix.SpecialLinearGroup.toGL b * d⁻¹) * (g₂ k)⁻¹) *
          (d * g₁ k) := by rw [e]
      _ = Matrix.SpecialLinearGroup.toGL b * ((g₂ k * d)⁻¹ * (d * g₁ k)) := by group
  obtain ⟨ℓ, hℓ⟩ := scl_of_comm r _ hcomm
  refine ⟨ℓ⁻¹, ?_⟩
  rw [glm_refl]
  have h1 : d * g₁ k = g₂ k * d * scl ℓ := by
    rw [← hℓ]
    group
  calc g₂ k * d = d * g₁ k * (scl ℓ)⁻¹ := by rw [h1]; group
    _ = scl ℓ⁻¹ * (d * g₁ k) := by
      rw [map_inv]
      exact ((scl_commute ℓ⁻¹ (d * g₁ k)).eq).symm ▸ rfl

theorem swap_block_relQ (r : ZMod 3 ≃+* F) (hF : Nat.card F = 3) (h2 : (2 : F) ≠ 0)
    (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁) (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂) (π₁ : P →* Y₁) (π₂ : P →* Y₂)
    (hker : π₁.ker = π₂.ker) (d : GL (Fin 2) F) (k : Fin 2)
    (hrel : ∀ (m : P) (b : SL(2, F)), π₁ m = fr₁.ψ (longBlock F 2 k b) →
      π₂ m = fr₂.ψ (longBlock F 2 k (Q3T6.conjAut d b)))
    (hsurj : ∀ b : SL(2, F), b ^ 4 = 1 → ∃ m : P, π₁ m = fr₁.ψ (longBlock F 2 k b))
    (hblk₂ : ∀ (m : P) (b : SL(2, F)), π₂ m = fr₂.ψ (longBlock F 2 k b) → b ^ 4 = 1)
    (ψ : Y₁ ≃* Y₂) (ψ' : Y₂ ≃* Y₁) (Q Q' : gsp 2 F) (π π' : F ≃+* F)
    (hQ : ∀ x, ψ (fr₁.ψ x) = fr₂.ψ (conjSp 2 F Q (fieldSp 2 F π x)))
    (hQ' : ∀ x, ψ' (fr₂.ψ x) = fr₁.ψ (conjSp 2 F Q' (fieldSp 2 F π' x)))
    {p p' : Fin 2 → GL (Fin 2) F}
    (hp : gm Q = bd (fun k => (p k : Matrix (Fin 2) (Fin 2) F)))
    (hp' : gm Q' = bd (fun k => (p' k : Matrix (Fin 2) (Fin 2) F)))
    (hψ : ∀ m : P, ∃ m' : P, π₂ m' = ψ (π₁ m) ∧ π₁ m' = ψ' (π₂ m)) :
    π' = π ∧ ∃ lam : Fˣ, p' k * glm π d = scl lam * (d⁻¹ * p k) := by
  have hπ' : π' = RingEquiv.refl F := Q3T7P25.ringEquiv_eq3 hF _ _
  have hπ : π = RingEquiv.refl F := Q3T7P25.ringEquiv_eq3 hF _ _
  set θ : MulAut SL(2, F) := Q3T6.conjAut d with hθdef
  have hθ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ b) =
      d * Matrix.SpecialLinearGroup.toGL b * d⁻¹ := fun b => toGL_conjAut d b
  have hrel' : ∀ (m : P) (c : SL(2, F)), π₂ m = fr₂.ψ (longBlock F 2 k c) →
      π₁ m = fr₁.ψ (longBlock F 2 k (θ⁻¹ c)) := fun m c hm => by
    have hc4 : c ^ 4 = 1 := hblk₂ m c hm
    obtain ⟨m₀, hm₀⟩ := hsurj (θ⁻¹ c) (by rw [← map_pow, hc4, map_one])
    have h0 := hrel m₀ _ hm₀
    rw [show Q3T6.conjAut d (θ⁻¹ c) = c from by simp [hθdef], ← hm] at h0
    have h1 : m₀⁻¹ * m ∈ π₁.ker := by
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, h0, inv_mul_cancel]
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1, hm₀]
  have key : ∀ b : SL(2, F), b ^ 4 = 1 →
      slSemi (p' k) π' (θ b) = θ⁻¹ (slSemi (p k) π b) := by
    intro b hb
    obtain ⟨m, hm⟩ := hsurj b hb
    obtain ⟨m', e1, e2⟩ := hψ m
    rw [hm, hQ, conjSp_fieldSp_longBlock_gl Q hp] at e1
    rw [hrel m b hm, hQ', conjSp_fieldSp_longBlock_gl Q' hp', hrel' m' _ e1] at e2
    exact (injective_ψ_longBlock fr₁ h2 k e2).symm
  subst hπ' hπ
  refine ⟨rfl, ?_⟩
  have hcomm : ∀ b : SL(2, F), b ^ 4 = 1 →
      ((d⁻¹ * p k)⁻¹ * (p' k * d)) * Matrix.SpecialLinearGroup.toGL b =
        Matrix.SpecialLinearGroup.toGL b * ((d⁻¹ * p k)⁻¹ * (p' k * d)) := by
    intro b hb
    have e := congrArg Matrix.SpecialLinearGroup.toGL (key b hb)
    rw [slg_slSemi, hθ, slg_inv_apply hθ, slg_slSemi] at e
    simp only [glm_refl] at e
    calc (d⁻¹ * p k)⁻¹ * (p' k * d) * Matrix.SpecialLinearGroup.toGL b =
        (d⁻¹ * p k)⁻¹ * (p' k * (d * Matrix.SpecialLinearGroup.toGL b * d⁻¹) * (p' k)⁻¹) *
          (p' k * d) := by group
      _ = (d⁻¹ * p k)⁻¹ * (d⁻¹ * (p k * Matrix.SpecialLinearGroup.toGL b * (p k)⁻¹) * d) *
          (p' k * d) := by rw [e]
      _ = Matrix.SpecialLinearGroup.toGL b * ((d⁻¹ * p k)⁻¹ * (p' k * d)) := by group
  obtain ⟨ℓ, hℓ⟩ := scl_of_comm r _ hcomm
  refine ⟨ℓ, ?_⟩
  rw [glm_refl]
  have h1 : p' k * d = d⁻¹ * p k * scl ℓ := by
    rw [← hℓ]
    group
  rw [h1]
  exact ((scl_commute ℓ (d⁻¹ * p k)).eq).symm

end Rel

section Main

variable {F : Type} [Field F]
  {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}

theorem pow_two_mul_of_inner (r : ZMod 3 ≃+* F) [Finite F] (fr : Frame F Y Φ A A' z') {w₀ w₁ : SL(2, F)}
    {N : ℕ} (h : (fr.ψ (longBlock F 2 0 w₀ * longBlock F 2 1 w₁)) ^ N = 1) :
    w₀ ^ (2 * N) = 1 ∧ w₁ ^ (2 * N) = 1 := by
  have hcomm : Commute (longBlock F 2 0 w₀) (longBlock F 2 1 w₁) :=
    commute_L 0 (⟨w₀, rfl⟩ : longBlock F 2 0 w₀ ∈ longRootSp2 F 2 0)
      (⟨w₁, rfl⟩ : longBlock F 2 1 w₁ ∈ longRootSp2 F 2 (Fin.rev 0))
  have h1 : fr.ψ ((longBlock F 2 0 w₀ * longBlock F 2 1 w₁) ^ N) = 1 := by
    rw [map_pow]
    exact h
  have h2 : (longBlock F 2 0 w₀ * longBlock F 2 1 w₁) ^ N ∈ spScalars 2 F := by
    rw [← fr.ker]
    exact h1
  have h3 : ((longBlock F 2 0 w₀ * longBlock F 2 1 w₁) ^ N) ^ 2 = 1 := by
    rw [pow_two]
    exact Q3T7P25.mul_self_of_mem_spScalars h2
  rw [← pow_mul, mul_comm N 2, hcomm.mul_pow, ← map_pow, ← map_pow] at h3
  exact longBlock_mul_eq_one _ _ h3

variable {Y₁ Y₂ : Type} [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
  {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ a₁ b₁ : Y₁}
  {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ a₂ b₂ : Y₂}
  {M : Type} [Group M] [Finite M] {π₁ : M →* Y₁} {π₂ : M →* Y₂} {L L' : Subgroup M}

theorem twinComm
    (hT : TwinShareQ Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L')
    (γ₁ δ₁ : Y₁ ≃* Y₁) (γ₂ δ₂ : Y₂ ≃* Y₂)
    (hγ₁A : A₁.map γ₁.toMonoidHom = A₁) (hγ₂A : A₂.map γ₂.toMonoidHom = A₂)
    (hδ₁A : A₁.map δ₁.toMonoidHom = A₁) (hδ₂A : A₂.map δ₂.toMonoidHom = A₂)
    (hγ : ∀ m : M, ∃ m' : M, π₁ m' = γ₁ (π₁ m) ∧ π₂ m' = γ₂ (π₂ m))
    (hδ : ∀ m : M, ∃ m' : M, π₁ m' = δ₁ (π₁ m) ∧ π₂ m' = δ₂ (π₂ m))
    (hord : ∃ n : ℕ, ∀ y : Y₁, (fun e => γ₁ (δ₁ (γ₁.symm (δ₁.symm e)))) ^[2 ^ n] y = y) :
    ∃ w : M, (∀ y : Y₁, γ₁ (δ₁ (γ₁.symm (δ₁.symm y))) = π₁ w * y * (π₁ w)⁻¹) ∧
      ∀ y : Y₂, γ₂ (δ₂ (γ₂.symm (δ₂.symm y))) = π₂ w * y * (π₂ w)⁻¹ := by
  obtain ⟨fr₁, fr₂, d, hker, hsurj, hblk₁, hblk₂, hrel⟩ := hT.setup
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf 1 hp
  have h4 : Nat.card (GaloisField 3 1) = 3 := Q3T7P25.natCard_gf3
  have hF : ringChar (GaloisField 3 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 1) 3]
    exact hp
  obtain ⟨r⟩ := nonempty_ringEquiv h4
  have hθ : ∀ k b, Matrix.SpecialLinearGroup.toGL (Q3T6.conjAut (d k) b) =
      d k * Matrix.SpecialLinearGroup.toGL b * (d k)⁻¹ := fun k b => toGL_conjAut (d k) b
  obtain ⟨G₁, σ₁, hG₁⟩ := Frame.exists_lift_iso h2 fr₁ fr₁ γ₁
  obtain ⟨N₁, τ₁, hN₁⟩ := Frame.exists_lift_iso h2 fr₁ fr₁ δ₁
  obtain ⟨G₂, σ₂, hG₂⟩ := Frame.exists_lift_iso h2 fr₂ fr₂ γ₂
  obtain ⟨N₂, τ₂, hN₂⟩ := Frame.exists_lift_iso h2 fr₂ fr₂ δ₂
  obtain ⟨g₁, hg₁, hdg₁⟩ := exists_gl_blocks G₁ (isBD_gm_of_conjSp_longInv h2 G₁ σ₁
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₁ fr₁ γ₁ G₁ σ₁ hG₁ hγ₁A.le))
  obtain ⟨n₁, hn₁, hdn₁⟩ := exists_gl_blocks N₁ (isBD_gm_of_conjSp_longInv h2 N₁ τ₁
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₁ fr₁ δ₁ N₁ τ₁ hN₁ hδ₁A.le))
  obtain ⟨g₂, hg₂, hdg₂⟩ := exists_gl_blocks G₂ (isBD_gm_of_conjSp_longInv h2 G₂ σ₂
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₂ fr₂ γ₂ G₂ σ₂ hG₂ hγ₂A.le))
  obtain ⟨n₂, hn₂, hdn₂⟩ := exists_gl_blocks N₂ (isBD_gm_of_conjSp_longInv h2 N₂ τ₂
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₂ fr₂ δ₂ N₂ τ₂ hN₂ hδ₂A.le))
  have rγ := fun k => fix_block_relQ r h4 h2 fr₁ fr₂ π₁ π₂ (d k) k (hrel k) (hsurj k)
    γ₁ γ₂ G₁ G₂ σ₁ σ₂ hG₁ hG₂ hg₁ hg₂ hγ
  have rδ := fun k => fix_block_relQ r h4 h2 fr₁ fr₂ π₁ π₂ (d k) k (hrel k) (hsurj k)
    δ₁ δ₂ N₁ N₂ τ₁ τ₂ hN₁ hN₂ hn₁ hn₂ hδ
  obtain ⟨hσ, -⟩ := rγ 0
  obtain ⟨hτ, -⟩ := rδ 0
  subst hσ hτ
  choose ℓ hℓ using fun k => (rγ k).2
  choose κ hκ using fun k => (rδ k).2
  set C₁ : gsp 2 (GaloisField 3 1) := G₁ * gspFieldMap σ₁ N₁ * gspFieldMap τ₁ G₁⁻¹ * N₁⁻¹
    with hC₁def
  set c₁ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => g₁ k * glm σ₁ (n₁ k) * (glm τ₁ (g₁ k))⁻¹ * (n₁ k)⁻¹ with hc₁def
  have hC₁ : gm C₁ = bd (fun k => (c₁ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₁def, gm_comm_bd G₁ N₁ N₁ σ₁ τ₁ hg₁ hn₁ hn₁]
    simp only [map_inv, hc₁def]
  have hc1 : ∀ x, γ₁ (δ₁ (γ₁.symm (δ₁.symm (fr₁.ψ x)))) = fr₁.ψ (conjSp 2 _ C₁ x) := fun x => by
    rw [comm_apply_of_lift fr₁.ψ γ₁ δ₁ (conjSp 2 _ G₁ * fieldSp 2 _ σ₁)
      (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) hG₁ hN₁ x, comm_conjSp_fieldSp]
  set C₂ : gsp 2 (GaloisField 3 1) := G₂ * gspFieldMap σ₁ N₂ * gspFieldMap τ₁ G₂⁻¹ * N₂⁻¹
    with hC₂def
  set c₂ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => g₂ k * glm σ₁ (n₂ k) * (glm τ₁ (g₂ k))⁻¹ * (n₂ k)⁻¹ with hc₂def
  have hC₂ : gm C₂ = bd (fun k => (c₂ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₂def, gm_comm_bd G₂ N₂ N₂ σ₁ τ₁ hg₂ hn₂ hn₂]
    simp only [map_inv, hc₂def]
  have hc2 : ∀ x, γ₂ (δ₂ (γ₂.symm (δ₂.symm (fr₂.ψ x)))) = fr₂.ψ (conjSp 2 _ C₂ x) := fun x => by
    rw [comm_apply_of_lift fr₂.ψ γ₂ δ₂ (conjSp 2 _ G₂ * fieldSp 2 _ σ₁)
      (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) hG₂ hN₂ x, comm_conjSp_fieldSp]
  have hμG₁ : mu G₁ ≠ 0 := Units.ne_zero _
  have hμN₁ : mu N₁ ≠ 0 := Units.ne_zero _
  obtain ⟨s, hs⟩ := isSquare_comm_det hF σ₁ τ₁ hμG₁ hμN₁
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    have h1 : τ₁ (mu G₁) ≠ 0 := (map_ne_zero τ₁).mpr hμG₁
    have h2 : σ₁ (mu N₁) ≠ 0 := (map_ne_zero σ₁).mpr hμN₁
    simp_all
  have hdc : ∀ k, ((c₁ k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det =
      mu G₁ * σ₁ (mu N₁) * (τ₁ (mu G₁))⁻¹ * (mu N₁)⁻¹ := fun k => by
    simp only [hc₁def, det_gl_mul, det_gl_inv, det_glm, hdg₁, hdn₁]
  obtain ⟨w₀, hw₀⟩ := exists_sl_smul hs0 ((hdc 0).trans hs)
  obtain ⟨w₁, hw₁⟩ := exists_sl_smul hs0 ((hdc 1).trans hs)
  have hg₂' : ∀ k, g₂ k = scl (ℓ k) * (d k * g₁ k * (glm σ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hℓ k)]
    group
  have hn₂' : ∀ k, n₂ k = scl (κ k) * (d k * n₁ k * (glm τ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hκ k)]
    group
  have htr : ∀ k, c₂ k = scl (ℓ k * Units.map (σ₁ : _ →* _) (κ k) *
      (Units.map (τ₁ : _ →* _) (ℓ k))⁻¹ * (κ k)⁻¹) * (d k * c₁ k * (d k)⁻¹) := fun k => by
    simp only [hc₁def, hc₂def]
    rw [hg₂' k, hn₂' k]
    exact fix_transport (d k) (g₁ k) (n₁ k) σ₁ τ₁ (ℓ k) (κ k)
  have hν : ∀ k, ((d k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det ≠ 0 := fun k =>
    (Matrix.isUnits_det_units (d k)).ne_zero
  have hr := fix_ratio hp σ₁ τ₁ (hν 0) (hν 1) hμG₁ hμN₁ (ℓ 0) (ℓ 1) (κ 0) (κ 1)
    (det_rel (hdg₁ 0) (hdg₂ 0) (hℓ 0)) (det_rel (hdg₁ 1) (hdg₂ 1) (hℓ 1))
    (det_rel (hdn₁ 0) (hdn₂ 0) (hκ 0)) (det_rel (hdn₁ 1) (hdn₂ 1) (hκ 1))
  set r' := ℓ 0 * Units.map (σ₁ : _ →* _) (κ 0) * (Units.map (τ₁ : _ →* _) (ℓ 0))⁻¹ * (κ 0)⁻¹
    with hrdef
  have hw'₀ : ((c₂ 0 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r' : GaloisField 3 1) * s) •
      ((Q3T6.conjAut (d 0) w₀ : SL(2, GaloisField 3 1)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 0]
    exact conj_smul_eq (hθ 0) hw₀ _
  have hw'₁ : ((c₂ 1 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r' : GaloisField 3 1) * s) •
      ((Q3T6.conjAut (d 1) w₁ : SL(2, GaloisField 3 1)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 1, ← hr]
    exact conj_smul_eq (hθ 1) hw₁ _
  have hinn := fun y => fr₁.inner_of_lift (fun y => γ₁ (δ₁ (γ₁.symm (δ₁.symm y)))) C₁ hc1 hC₁ hs0
    w₀ w₁ hw₀ hw₁ y
  set u : Y₁ := fr₁.ψ (longBlock (GaloisField 3 1) 2 0 w₀ * longBlock (GaloisField 3 1) 2 1 w₁)
    with hu
  have hiter : ∀ (k : ℕ) (y : Y₁),
      (fun e => γ₁ (δ₁ (γ₁.symm (δ₁.symm e)))) ^[k] y = u ^ k * y * (u ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, hinn, pow_succ']
      group
  obtain ⟨n, hn⟩ := hord
  have hcent : ∀ x : Y₁, u ^ (2 ^ n) * x = x * u ^ (2 ^ n) := fun x => by
    have h1 := (hiter (2 ^ n) x).symm.trans (hn x)
    calc u ^ (2 ^ n) * x = (u ^ (2 ^ n) * x * (u ^ (2 ^ n))⁻¹) * u ^ (2 ^ n) := by group
      _ = x * u ^ (2 ^ n) := by rw [h1]
  have hu1 : u ^ (2 ^ n) = 1 := Q3T8.Asc77.C5O.M.Frame.centerless fr₁ h4 hcent
  obtain ⟨hw₀4, hw₁4⟩ := pow_two_mul_of_inner r fr₁ (N := 2 ^ n) hu1
  have hw₀' : w₀ ^ 4 = 1 := pow4_of_pow_two_pow r (n := n + 1) (by rw [pow_succ, mul_comm]; exact hw₀4)
  have hw₁' : w₁ ^ 4 = 1 := pow4_of_pow_two_pow r (n := n + 1) (by rw [pow_succ, mul_comm]; exact hw₁4)
  obtain ⟨m₀, hm₀⟩ := hsurj 0 w₀ hw₀'
  obtain ⟨m₁, hm₁⟩ := hsurj 1 w₁ hw₁'
  refine ⟨m₀ * m₁, fun y => ?_, fun y => ?_⟩
  · rw [hinn y, map_mul π₁, hm₀, hm₁, ← map_mul]
  · rw [fr₂.inner_of_lift (fun y => γ₂ (δ₂ (γ₂.symm (δ₂.symm y)))) C₂ hc2 hC₂
      (mul_ne_zero r'.ne_zero hs0) (Q3T6.conjAut (d 0) w₀) (Q3T6.conjAut (d 1) w₁) hw'₀ hw'₁ y,
      map_mul π₂, hrel 0 m₀ w₀ hm₀, hrel 1 m₁ w₁ hm₁, ← map_mul]

theorem twinCommSwap
    (hT : TwinShareQ Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L')
    (ψ : Y₁ ≃* Y₂) (ψ' : Y₂ ≃* Y₁) (δ₁ : Y₁ ≃* Y₁) (δ₂ : Y₂ ≃* Y₂)
    (hψA : A₁.map ψ.toMonoidHom = A₂) (hψ'A : A₂.map ψ'.toMonoidHom = A₁)
    (hδ₁A : A₁.map δ₁.toMonoidHom = A₁) (hδ₂A : A₂.map δ₂.toMonoidHom = A₂)
    (hψ : ∀ m : M, ∃ m' : M, π₂ m' = ψ (π₁ m) ∧ π₁ m' = ψ' (π₂ m))
    (hδ : ∀ m : M, ∃ m' : M, π₁ m' = δ₁ (π₁ m) ∧ π₂ m' = δ₂ (π₂ m))
    (hord : ∃ n : ℕ, ∀ y : Y₁, (fun e => ψ' (δ₂ (ψ'.symm (δ₁.symm e)))) ^[2 ^ n] y = y) :
    ∃ w : M, (∀ y : Y₁, ψ' (δ₂ (ψ'.symm (δ₁.symm y))) = π₁ w * y * (π₁ w)⁻¹) ∧
      ∀ y : Y₂, ψ (δ₁ (ψ.symm (δ₂.symm y))) = π₂ w * y * (π₂ w)⁻¹ := by
  obtain ⟨fr₁, fr₂, d, hker, hsurj, hblk₁, hblk₂, hrel⟩ := hT.setup
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf 1 hp
  have h4 : Nat.card (GaloisField 3 1) = 3 := Q3T7P25.natCard_gf3
  have hF : ringChar (GaloisField 3 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 1) 3]
    exact hp
  obtain ⟨r⟩ := nonempty_ringEquiv h4
  have hθ : ∀ k b, Matrix.SpecialLinearGroup.toGL (Q3T6.conjAut (d k) b) =
      d k * Matrix.SpecialLinearGroup.toGL b * (d k)⁻¹ := fun k b => toGL_conjAut (d k) b
  obtain ⟨P, π, hP⟩ := Frame.exists_lift_iso h2 fr₁ fr₂ ψ
  obtain ⟨P', π', hP'⟩ := Frame.exists_lift_iso h2 fr₂ fr₁ ψ'
  obtain ⟨N₁, τ₁, hN₁⟩ := Frame.exists_lift_iso h2 fr₁ fr₁ δ₁
  obtain ⟨N₂, τ₂, hN₂⟩ := Frame.exists_lift_iso h2 fr₂ fr₂ δ₂
  obtain ⟨pb, hpb, hdpb⟩ := exists_gl_blocks P (isBD_gm_of_conjSp_longInv h2 P π
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₁ fr₂ ψ P π hP hψA.le))
  obtain ⟨pb', hpb', hdpb'⟩ := exists_gl_blocks P' (isBD_gm_of_conjSp_longInv h2 P' π'
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₂ fr₁ ψ' P' π' hP' hψ'A.le))
  obtain ⟨n₁, hn₁, hdn₁⟩ := exists_gl_blocks N₁ (isBD_gm_of_conjSp_longInv h2 N₁ τ₁
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₁ fr₁ δ₁ N₁ τ₁ hN₁ hδ₁A.le))
  obtain ⟨n₂, hn₂, hdn₂⟩ := exists_gl_blocks N₂ (isBD_gm_of_conjSp_longInv h2 N₂ τ₂
    (Q3T8.Asc77.C5O.M.Frame.lift_longInv h2 h4 fr₂ fr₂ δ₂ N₂ τ₂ hN₂ hδ₂A.le))
  have rψ := fun k => swap_block_relQ r h4 h2 fr₁ fr₂ π₁ π₂ hker (d k) k (hrel k) (hsurj k)
    (hblk₂ k) ψ ψ' P P' π π' hP hP' hpb hpb' hψ
  have rδ := fun k => fix_block_relQ r h4 h2 fr₁ fr₂ π₁ π₂ (d k) k (hrel k) (hsurj k)
    δ₁ δ₂ N₁ N₂ τ₁ τ₂ hN₁ hN₂ hn₁ hn₂ hδ
  obtain ⟨hπ, -⟩ := rψ 0
  obtain ⟨hτ, -⟩ := rδ 0
  have hπ' := hπ.symm
  subst hπ' hτ
  choose lam hlam using fun k => (rψ k).2
  choose κ hκ using fun k => (rδ k).2
  set C₁ : gsp 2 (GaloisField 3 1) := P' * gspFieldMap π N₂ * gspFieldMap τ₁ P'⁻¹ * N₁⁻¹
    with hC₁def
  set c₁ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => pb' k * glm π (n₂ k) * (glm τ₁ (pb' k))⁻¹ * (n₁ k)⁻¹ with hc₁def
  have hC₁ : gm C₁ = bd (fun k => (c₁ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₁def, gm_comm_bd P' N₂ N₁ π τ₁ hpb' hn₂ hn₁]
    simp only [map_inv, hc₁def]
  have hc1 : ∀ x, ψ' (δ₂ (ψ'.symm (δ₁.symm (fr₁.ψ x)))) = fr₁.ψ (conjSp 2 _ C₁ x) := fun x => by
    rw [comm_apply_of_lift_swap fr₁.ψ fr₂.ψ ψ' δ₁ δ₂ (conjSp 2 _ P' * fieldSp 2 _ π)
      (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) hP' hN₁ hN₂ x,
      comm_conjSp_fieldSp_gen]
  set C₂ : gsp 2 (GaloisField 3 1) := P * gspFieldMap π N₁ * gspFieldMap τ₁ P⁻¹ * N₂⁻¹
    with hC₂def
  set c₂ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => pb k * glm π (n₁ k) * (glm τ₁ (pb k))⁻¹ * (n₂ k)⁻¹ with hc₂def
  have hC₂ : gm C₂ = bd (fun k => (c₂ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₂def, gm_comm_bd P N₁ N₂ π τ₁ hpb hn₁ hn₂]
    simp only [map_inv, hc₂def]
  have hc2 : ∀ x, ψ (δ₁ (ψ.symm (δ₂.symm (fr₂.ψ x)))) = fr₂.ψ (conjSp 2 _ C₂ x) := fun x => by
    rw [comm_apply_of_lift_swap fr₂.ψ fr₁.ψ ψ δ₂ δ₁ (conjSp 2 _ P * fieldSp 2 _ π)
      (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) hP hN₂ hN₁ x,
      comm_conjSp_fieldSp_gen]
  have hμP : mu P ≠ 0 := Units.ne_zero _
  have hμN₁ : mu N₁ ≠ 0 := Units.ne_zero _
  have hμN₂ : mu N₂ ≠ 0 := Units.ne_zero _
  have hν : ∀ k, ((d k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det ≠ 0 := fun k =>
    (Matrix.isUnits_det_units (d k)).ne_zero
  have hκrel := fun k => det_rel (hdn₁ k) (hdn₂ k) (hκ k)
  obtain ⟨s, hs⟩ := isSquare_swap_det hF π τ₁ hμP hμN₁ (hν 0) (κ 0) (hκrel 0)
  have hne : mu P * π (mu N₁) * (τ₁ (mu P))⁻¹ * (mu N₂)⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hμP ((map_ne_zero π).mpr hμN₁))
      (inv_ne_zero ((map_ne_zero τ₁).mpr hμP))) (inv_ne_zero hμN₂)
  have hs0 : s ≠ 0 := fun h => hne (by rw [hs, h, mul_zero])
  have hdc : ∀ k, ((c₂ k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det =
      mu P * π (mu N₁) * (τ₁ (mu P))⁻¹ * (mu N₂)⁻¹ := fun k => by
    simp only [hc₂def, det_gl_mul, det_gl_inv, det_glm, hdpb, hdn₁, hdn₂]
  obtain ⟨w₀, hw₀⟩ := exists_sl_smul hs0 ((hdc 0).trans hs)
  obtain ⟨w₁, hw₁⟩ := exists_sl_smul hs0 ((hdc 1).trans hs)
  have hp' : ∀ k, pb' k = scl (lam k) * ((d k)⁻¹ * pb k * (glm π (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hlam k)]
    group
  have hn₂' : ∀ k, n₂ k = scl (κ k) * (d k * n₁ k * (glm τ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hκ k)]
    group
  have htr : ∀ k, c₁ k = scl (lam k * Units.map (π : _ →* _) (κ k) *
      (Units.map (τ₁ : _ →* _) (lam k))⁻¹ * κ k) * ((d k)⁻¹ * c₂ k * d k) := fun k => by
    simp only [hc₁def, hc₂def]
    rw [hp' k, hn₂' k]
    exact swap_transport (d k) (pb k) (n₁ k) π τ₁ (lam k) (κ k)
  have hr := swap_ratio hp π τ₁ (hν 0) (hν 1) hμP hμN₁ (lam 0) (lam 1) (κ 0) (κ 1)
    (det_rel_swap (hdpb 0) (hdpb' 0) (hlam 0)) (det_rel_swap (hdpb 1) (hdpb' 1) (hlam 1))
    (hκrel 0) (hκrel 1)
  set r' := lam 0 * Units.map (π : _ →* _) (κ 0) * (Units.map (τ₁ : _ →* _) (lam 0))⁻¹ * κ 0
    with hrdef
  have hw'₀ : ((c₁ 0 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r' : GaloisField 3 1) * s) •
      ((((Q3T6.conjAut (d 0))⁻¹ w₀ : SL(2, GaloisField 3 1))) :
        Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 0]
    exact conj_smul_eq_inv (hθ 0) hw₀ _
  have hw'₁ : ((c₁ 1 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r' : GaloisField 3 1) * s) •
      ((((Q3T6.conjAut (d 1))⁻¹ w₁ : SL(2, GaloisField 3 1))) :
        Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 1, ← hr]
    exact conj_smul_eq_inv (hθ 1) hw₁ _
  have hinn := fun y => fr₁.inner_of_lift (fun y => ψ' (δ₂ (ψ'.symm (δ₁.symm y)))) C₁ hc1 hC₁
    (mul_ne_zero r'.ne_zero hs0) ((Q3T6.conjAut (d 0))⁻¹ w₀) ((Q3T6.conjAut (d 1))⁻¹ w₁) hw'₀
    hw'₁ y
  set u : Y₁ := fr₁.ψ (longBlock (GaloisField 3 1) 2 0 ((Q3T6.conjAut (d 0))⁻¹ w₀) *
    longBlock (GaloisField 3 1) 2 1 ((Q3T6.conjAut (d 1))⁻¹ w₁)) with hu
  have hiter : ∀ (k : ℕ) (y : Y₁),
      (fun e => ψ' (δ₂ (ψ'.symm (δ₁.symm e)))) ^[k] y = u ^ k * y * (u ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, hinn, pow_succ']
      group
  obtain ⟨n, hn⟩ := hord
  have hcent : ∀ x : Y₁, u ^ (2 ^ n) * x = x * u ^ (2 ^ n) := fun x => by
    have h1 := (hiter (2 ^ n) x).symm.trans (hn x)
    calc u ^ (2 ^ n) * x = (u ^ (2 ^ n) * x * (u ^ (2 ^ n))⁻¹) * u ^ (2 ^ n) := by group
      _ = x * u ^ (2 ^ n) := by rw [h1]
  have hu1 : u ^ (2 ^ n) = 1 := Q3T8.Asc77.C5O.M.Frame.centerless fr₁ h4 hcent
  obtain ⟨hw₀4, hw₁4⟩ := pow_two_mul_of_inner r fr₁ (N := 2 ^ n) hu1
  have hw₀' : ((Q3T6.conjAut (d 0))⁻¹ w₀) ^ 4 = 1 :=
    pow4_of_pow_two_pow r (n := n + 1) (by rw [pow_succ, mul_comm]; exact hw₀4)
  have hw₁' : ((Q3T6.conjAut (d 1))⁻¹ w₁) ^ 4 = 1 :=
    pow4_of_pow_two_pow r (n := n + 1) (by rw [pow_succ, mul_comm]; exact hw₁4)
  obtain ⟨m₀, hm₀⟩ := hsurj 0 _ hw₀'
  obtain ⟨m₁, hm₁⟩ := hsurj 1 _ hw₁'
  have e₀ : π₂ m₀ = fr₂.ψ (longBlock (GaloisField 3 1) 2 0 w₀) := by
    rw [hrel 0 m₀ _ hm₀, show (Q3T6.conjAut (d 0)) ((Q3T6.conjAut (d 0))⁻¹ w₀) = w₀ from by simp]
  have e₁ : π₂ m₁ = fr₂.ψ (longBlock (GaloisField 3 1) 2 1 w₁) := by
    rw [hrel 1 m₁ _ hm₁, show (Q3T6.conjAut (d 1)) ((Q3T6.conjAut (d 1))⁻¹ w₁) = w₁ from by simp]
  refine ⟨m₀ * m₁, fun y => ?_, fun y => ?_⟩
  · rw [hinn y, map_mul π₁, hm₀, hm₁, ← map_mul]
  · rw [fr₂.inner_of_lift (fun y => ψ (δ₁ (ψ.symm (δ₂.symm y)))) C₂ hc2 hC₂ hs0 w₀ w₁ hw₀ hw₁ y,
      map_mul π₂, e₀, e₁, ← map_mul]

end Main

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL.Q8
