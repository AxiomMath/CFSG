module

public import CFSG.Certificates.Kernel.X2E6SylSound
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index

public section

namespace CFSG.KC.X2E6Syl

open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6 CFSG.Open
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk

theorem braid_check : ∀ i j : Fin 6,
    pwL (mulL (reflL i) (reflL j)) (braidLength (Tag.E6.cartan i j * Tag.E6.cartan j i)) = idL := by
  decide +kernel

theorem coxeterOrder_eq_braidLength' (c : ℤ) : TauCeti.coxeterOrder c = braidLength c := by
  unfold braidLength
  split_ifs with h₀ h₁ h₂ h₃ h₄
  · rw [h₀, TauCeti.coxeterOrder_zero]
  · rw [h₁, TauCeti.coxeterOrder_one]
  · rw [h₂, TauCeti.coxeterOrder_two]
  · rw [h₃, TauCeti.coxeterOrder_three]
  · rw [h₄, TauCeti.coxeterOrder_four]
  · exact TauCeti.coxeterOrder_eq_zero_iff.2 (by simp [h₀, h₁, h₂, h₃, h₄])

theorem isLiftable_reflGL :
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan Tag.E6)).IsLiftable
      fun i : Fin Tag.E6.rank => reflGL i := by
  intro i j
  have hM : (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan Tag.E6)) i j =
      braidLength (Tag.E6.cartan i j * Tag.E6.cartan j i) := by
    rw [← coxeterOrder_eq_braidLength']
    simp [CFSG.LieType.RootSystem.coxeterMatrix]
  rw [hM]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one]
  have e := congrArg dec (braid_check i j)
  have hr : ∀ k : Fin Tag.E6.rank, refl' k = reflGL k := fun k => by
    have hk : (k : ℕ) < 6 := k.isLt
    rw [refl', dif_pos hk]
    rfl
  rw [dec_pwL, dec_mulL, dec_reflL, dec_reflL, dec_idL, hr, hr] at e
  exact e

@[expose] noncomputable def wHom : WeylGroup Tag.E6 →* GL6 :=
  (coxeterSystem Tag.E6).lift ⟨fun i : Fin Tag.E6.rank => reflGL i, isLiftable_reflGL⟩

theorem range_wHom : wHom.range = W3 := by
  rw [MonoidHom.range_eq_map, ← (coxeterSystem Tag.E6).subgroup_closure_range_simple,
    MonoidHom.map_closure, W3, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, wHom,
    (coxeterSystem Tag.E6).lift_apply_simple isLiftable_reflGL]
  rfl

theorem card_W3_dvd :
    Nat.card W3 ∣ 51840 := by
  rw [← range_wHom, ← CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6]
  exact Subgroup.card_range_dvd wHom

theorem factorization_card_W3
    {gw : List (List ℕ)} (hq : qOK gw = true) : (Nat.card W3).factorization 3 = 4 := by
  have h81 : 3 ^ 4 ∣ Nat.card W3 := by
    have := Subgroup.card_dvd_of_le (qSub_le gw)
    rwa [card_qSub hq] at this
  have hd := card_W3_dvd
  have hne : Nat.card W3 ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.pos_of_dvd_of_pos hd (by norm_num))
  have hge : 4 ≤ (Nat.card W3).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hne).1 h81
  have hle : (Nat.card W3).factorization 3 ≤ (51840 : ℕ).factorization 3 :=
    (Nat.factorization_le_iff_dvd hne (by norm_num)).2 hd 3
  have h5 : (51840 : ℕ).factorization 3 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_three, show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  omega

theorem exists_conj_le_qSub
    {gw : List (List ℕ)} (hq : qOK gw = true) {R : Subgroup GL6} (hRW : R ≤ W3)
    (hp : IsPGroup 3 R) : ∃ g ∈ W3, ∀ x ∈ R, g⁻¹ * x * g ∈ qSub gw := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q' : Subgroup W3 := (qSub gw).subgroupOf W3
  have hQ'card : Nat.card Q' = 3 ^ (Nat.card W3).factorization 3 := by
    rw [factorization_card_W3 hq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (qSub_le gw)).toEquiv,
      card_qSub hq]
    norm_num
  let S0 : Sylow 3 W3 := Sylow.ofCard Q' hQ'card
  let R' : Subgroup W3 := R.subgroupOf W3
  have hpR' : IsPGroup 3 R' :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hRW).symm
  obtain ⟨S, hS⟩ := hpR'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W3 S0 S
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxS : (⟨x, hRW hx⟩ : W3) ∈ (S : Subgroup W3) := hS (Subgroup.mem_subgroupOf.2 hx)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨y, hy, hyx⟩ := hxS
  have hy' : y ∈ Q' := by
    have : (S0 : Subgroup W3) = Q' := Sylow.coe_ofCard _ _
    rwa [← this]
  have hyq : (y : GL6) ∈ qSub gw := hy'
  have e : g⁻¹ * ⟨x, hRW hx⟩ * g = y := by
    rw [← hyx, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' : (g : GL6)⁻¹ * x * g = y := congrArg Subtype.val e
  rw [e']
  exact hyq

theorem cartanForm_rootRefl (i : Fin 6) (α β : Fin 6 → ℤ) :
    cartanForm (rootRefl i α) (rootRefl i β) = cartanForm α β := by
  fin_cases i <;> simp [cartanForm, rootRefl, Fin.sum_univ_six, cartanE6] <;> ring

theorem pair_rootRefl (i : Fin 6) (α : Fin 6 → ℤ) (f : Fin 6 → ZMod 3) :
    ∑ k, ((rootRefl i α k : ℤ) : ZMod 3) * Matrix.mulVec (reflMat i) f k =
      ∑ k, ((α k : ℤ) : ZMod 3) * f k := by
  fin_cases i <;>
    simp [rootRefl, reflMat, cartanE6, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring

@[expose] def rootReflQ (i : Fin 6) : (Fin 6 → ℚ) →ₗ[ℚ] (Fin 6 → ℚ) where
  toFun v j := if j = i then v i - ∑ k, v k * (cartanE6 k i : ℚ) else v j
  map_add' v w := by
    funext j
    by_cases h : j = i
    · simp only [h, if_true, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring
    · simp [h]
  map_smul' c v := by
    funext j
    by_cases h : j = i
    · simp only [h, if_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
        mul_sub, mul_assoc]
    · simp [h]

theorem rootReflQ_cast (i : Fin 6) (α : Fin 6 → ℤ) :
    rootReflQ i (fun k => ((α k : ℤ) : ℚ)) = fun k => ((rootRefl i α k : ℤ) : ℚ) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [rootReflQ, rootRefl]
  · simp [rootReflQ, rootRefl, h]

theorem rootReflQ_rootReflQ (i : Fin 6) (v : Fin 6 → ℚ) : rootReflQ i (rootReflQ i v) = v := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [rootReflQ, Fin.sum_univ_six, cartanE6] <;> ring

theorem rootRankQ_image (i : Fin 6) (C : Set (Fin 6 → ℤ)) :
    rootRankQ (rootRefl i '' C) = rootRankQ C := by
  let L : (Fin 6 → ℚ) ≃ₗ[ℚ] (Fin 6 → ℚ) :=
    LinearEquiv.ofInvolutive (rootReflQ i) (rootReflQ_rootReflQ i)
  have hset : (fun α : Fin 6 → ℤ => fun k => ((α k : ℤ) : ℚ)) '' (rootRefl i '' C) =
      L '' ((fun α : Fin 6 → ℤ => fun k => ((α k : ℤ) : ℚ)) '' C) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun α _ => ?_
    exact (rootReflQ_cast i α).symm
  have hspan : ∀ X : Set (Fin 6 → ℚ), Submodule.span ℚ (L '' X) =
      (Submodule.span ℚ X).map (L : (Fin 6 → ℚ) →ₗ[ℚ] (Fin 6 → ℚ)) := fun X => by
    rw [Submodule.map_span, LinearEquiv.coe_coe]
  unfold rootRankQ
  rw [hset, hspan, LinearEquiv.finrank_map_eq]

theorem rootGood_reflMat (i : Fin 6) {F : Set (Fin 6 → ZMod 3)} (h : RootGood F) :
    RootGood ((fun v => Matrix.mulVec (reflMat i) v) '' F) := by
  obtain ⟨C, hC, hconn, hrank, horth⟩ := h
  refine ⟨rootRefl i '' C, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    exact rootsE6_closed (hC hα) i
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have key : ∀ z, Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ cartanForm a b ≠ 0) x z →
        Relation.ReflTransGen (fun a b => a ∈ rootRefl i '' C ∧ b ∈ rootRefl i '' C ∧
          cartanForm a b ≠ 0) (rootRefl i x) (rootRefl i z) := by
      intro z hz
      induction hz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        exact ih.tail ⟨⟨b, hbc.1, rfl⟩, ⟨c, hbc.2.1, rfl⟩, by
          rw [cartanForm_rootRefl]; exact hbc.2.2⟩
    exact key y (hconn x hx y hy)
  · rw [rootRankQ_image]
    exact hrank
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨f, hf, rfl⟩
    rw [pair_rootRefl]
    exact horth α hα f hf

theorem reflGL_inv' (j : Fin 6) : (reflGL j)⁻¹ = reflGL j := by
  have hsq : reflGL j * reflGL j = 1 := Units.ext (by simpa [reflGL] using reflMat_mul_self j)
  exact inv_eq_of_mul_eq_one_right hsq

theorem rootGood_image {g : GL6} (hg : g ∈ W3) {F : Set (Fin 6 → ZMod 3)} (h : RootGood F) :
    RootGood ((fun v => Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' F) := by
  have key : ∀ g ∈ W3, (∀ F, RootGood F →
      RootGood ((fun v => Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' F)) ∧
      (∀ F, RootGood F → RootGood
        ((fun v => Matrix.mulVec ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' F)) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [reflGL_inv']
      exact ⟨fun F hF => rootGood_reflMat j hF, fun F hF => rootGood_reflMat j hF⟩
    | one => exact ⟨fun F hF => by simpa using hF, fun F hF => by simpa using hF⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun F hF => ?_, fun F hF => ?_⟩
      · have e : (fun v => Matrix.mulVec ((x * y : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' F =
            (fun v => Matrix.mulVec (x : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) ''
              ((fun v => Matrix.mulVec (y : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' F) := by
          rw [Set.image_image]
          simp [Matrix.mulVec_mulVec]
        rw [e]
        exact hx.1 _ (hy.1 F hF)
      · have e : (fun v => Matrix.mulVec (((x * y)⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) ''
            F = (fun v => Matrix.mulVec ((y⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) ''
              ((fun v => Matrix.mulVec ((x⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' F) := by
          rw [Set.image_image, mul_inv_rev]
          simp [Matrix.mulVec_mulVec]
        rw [e]
        exact hy.2 _ (hx.2 F hF)
    | inv x _ hx =>
      refine ⟨fun F hF => hx.2 F hF, fun F hF => ?_⟩
      rw [inv_inv]
      exact hx.1 F hF
  exact (key g hg).1 F h

theorem isElemAbelian_map' {G H : Type*} [Group G] [Group H] (f : G →* H) {p : ℕ}
    {E : Subgroup G} (h : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, hx, rfl⟩ := a
    obtain ⟨_, y, hy, rfl⟩ := b
    apply Subtype.ext
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (h.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h.2 x hx, map_one]

theorem fixVec_conj (c : GL6) (R : Subgroup GL6) :
    fixVec (R.map (MulAut.conj c).toMonoidHom) =
      (fun v => Matrix.mulVec (c : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' fixVec R := by
  ext v
  constructor
  · intro hv
    refine ⟨Matrix.mulVec ((c⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) v, fun g hg => ?_, ?_⟩
    · have h1 := hv (c * g * c⁻¹) ⟨g, hg, rfl⟩
      have e : ((c * g * c⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
          (c : Matrix (Fin 6) (Fin 6) (ZMod 3)) * g * ((c⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
        simp [Units.val_mul]
      rw [e] at h1
      have h2 := congrArg (Matrix.mulVec ((c⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))) h1
      simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc] using h2
    · simp [Matrix.mulVec_mulVec]
  · rintro ⟨w, hw, rfl⟩ _ ⟨g, hg, rfl⟩
    change Matrix.mulVec ((c * g * c⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))
      (Matrix.mulVec (c : Matrix (Fin 6) (Fin 6) (ZMod 3)) w) = _
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    simp [← Matrix.mulVec_mulVec, hw g hg]

theorem mulVec_unit_injective (c : GL6) :
    Function.Injective fun v => Matrix.mulVec (c : Matrix (Fin 6) (Fin 6) (ZMod 3)) v := by
  intro v w h
  have h2 := congrArg (Matrix.mulVec ((c⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))) h
  simpa [Matrix.mulVec_mulVec] using h2

theorem card_fixVec_conj (c : GL6) (R : Subgroup GL6) :
    Nat.card (fixVec (R.map (MulAut.conj c).toMonoidHom)) = Nat.card (fixVec R) := by
  rw [fixVec_conj, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_image_of_injective _ (mulVec_unit_injective c)]

theorem x2e6WeylCore_of_checks
    {gw : List (List ℕ)} {mel fixS : List (List ℕ)} {fixE : List (List (List ℕ))}
    {fixY : List (List (ℕ × List (List ℕ)))} {wit : List Wit}
    (hq : qOK gw = true) (hf : famOK gw mel = true) (hx : fixOK gw mel fixS fixE fixY wit = true) :
    X2E6WeylCore := by
  have conj : ∀ R : Subgroup GL6, R ≤ W3 → IsElemAbelian 3 R → ∀ r : ℕ, Nat.card R = 3 ^ r →
      ∃ g ∈ W3, R.map (MulAut.conj g⁻¹).toMonoidHom ≤ qSub gw ∧
        IsElemAbelian 3 (R.map (MulAut.conj g⁻¹).toMonoidHom) ∧
        Nat.card (R.map (MulAut.conj g⁻¹).toMonoidHom) = 3 ^ r := by
    intro R hRW hA r hr
    have hp : IsPGroup 3 R := IsPGroup.of_card hr
    obtain ⟨g, hgW, hg⟩ := exists_conj_le_qSub hq hRW hp
    refine ⟨g, hgW, ?_, isElemAbelian_map' _ hA, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have e : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
        simp [MulAut.conj_apply]
      rw [e]
      exact hg x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hr]
  refine ⟨fun R hRW hA r hr => ?_, fun R hRW hA r hr hr1 U hU hcard => ?_⟩
  · obtain ⟨g, -, hle, hA', hr'⟩ := conj R hRW hA r hr
    obtain ⟨h1, h2, -⟩ := claims_qSub hq hf hx hle hA' hr'
    refine ⟨h1, fun h => ?_⟩
    rw [← card_fixVec_conj g⁻¹ R]
    exact h2 h
  · subst hr1
    obtain ⟨g, hgW, hle, hA', hr'⟩ := conj R hRW hA 1 hr
    obtain ⟨-, -, h3⟩ := claims_qSub hq hf hx hle hA' hr'
    obtain ⟨hle81, hw⟩ := h3 rfl
    have hfixR : Nat.card (fixVec R) ≤ 81 := by rwa [card_fixVec_conj] at hle81
    have hU81 : 81 ≤ Nat.card U := by simpa using hcard
    have hUle : Nat.card (U : Set (Fin 6 → ZMod 3)) ≤ Nat.card (fixVec R) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hU (Set.toFinite _)
    have hUeq : (U : Set (Fin 6 → ZMod 3)) = fixVec R := by
      have e1 := Nat.card_coe_set_eq (fixVec R)
      have e2 := Nat.card_coe_set_eq (U : Set (Fin 6 → ZMod 3))
      have : Nat.card (U : Set (Fin 6 → ZMod 3)) = Nat.card U := rfl
      exact Set.eq_of_subset_of_ncard_le hU (by omega)
    have hUc : Nat.card (U : Set (Fin 6 → ZMod 3)) = Nat.card U := rfl
    have h81R : 81 ≤ Nat.card (fixVec (R.map (MulAut.conj g⁻¹).toMonoidHom)) := by
      rw [card_fixVec_conj]
      omega
    obtain ⟨F', hF'sub, hF'card, hF'good⟩ := hw h81R
    let L : (Fin 6 → ZMod 3) →+ (Fin 6 → ZMod 3) :=
      (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) (ZMod 3))).toAddMonoidHom
    refine ⟨F'.map L, ?_, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      rw [hUeq]
      have hv' := hF'sub hv
      rw [fixVec_conj] at hv'
      obtain ⟨w, hw', rfl⟩ := hv'
      change Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) (ZMod 3))
        (Matrix.mulVec ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) w) ∈ fixVec R
      simpa [Matrix.mulVec_mulVec] using hw'
    · rw [← hF'card]
      exact Nat.card_congr (AddSubgroup.equivMapOfInjective F' L (mulVec_unit_injective g)).toEquiv.symm
    · have e : ((F'.map L : AddSubgroup (Fin 6 → ZMod 3)) : Set (Fin 6 → ZMod 3)) =
          (fun v => Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) v) '' (F' : Set _) := by
        ext v
        simp [L]
      rw [e]
      exact rootGood_image hgW hF'good

end CFSG.KC.X2E6Syl

end
