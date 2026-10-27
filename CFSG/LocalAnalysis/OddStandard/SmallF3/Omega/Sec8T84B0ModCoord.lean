module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModBlk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModRes

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

theorem exists_hom_section {P Q : Type} [CommGroup P] [CommGroup Q] (hP : ∀ x : P, x * x = 1)
    (f : P →* Q) (hf : Function.Surjective f) :
    ∃ s : Q →* P, ∀ q : Q, f (s q) = q := by
  have hQ : ∀ y : Q, y * y = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    rw [← map_mul, hP x, map_one]
  letI : Module (ZMod 2) (Additive P) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact hP (Additive.toMul x)
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact hQ (Additive.toMul x)
  let fL : Additive P →ₗ[ZMod 2] Additive Q := (MonoidHom.toAdditive f).toZModLinearMap 2
  have hsurj : LinearMap.range fL = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro q
    obtain ⟨p, hp⟩ := hf (Additive.toMul q)
    exact ⟨Additive.ofMul p, by simp [fL, hp]⟩
  obtain ⟨g, hg⟩ := fL.exists_rightInverse_of_surjective hsurj
  refine ⟨MonoidHom.toAdditive.symm g.toAddMonoidHom, fun q => ?_⟩
  have := LinearMap.congr_fun hg (Additive.ofMul q)
  simpa [fL] using this

private noncomputable def prodSumMulEquiv :
    Multiplicative (Fin 4 → ZMod 2) × Multiplicative (Fin 4 → ZMod 2) ≃*
      Multiplicative (Fin 4 ⊕ Fin 4 → ZMod 2) where
  toFun p :=
    Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd p.1) (Multiplicative.toAdd p.2))
  invFun v :=
    (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (Sum.inl i),
     Multiplicative.ofAdd fun j => Multiplicative.toAdd v (Sum.inr j))
  left_inv p := by
    apply Prod.ext
    · funext i; simp
    · funext j; simp
  right_inv v := by
    funext i
    cases i <;> rfl
  map_mul' p q := by
    funext i
    cases i <;> rfl

theorem exists_adapted {G : Type} [Group G] (E B : Subgroup G) (hE : IsElemAb2 E 8) (hBE : B ≤ E)
    (u : MulAut ↥E) (hu2 : u * u = 1) (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B)
    (hrange : ∀ b ∈ B, ∃ e : ↥E, (e : G) * ((u e : ↥E) : G)⁻¹ = b)
    (eB : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)) :
    ∃ θ : ↥E ≃* Multiplicative (Fin 4 ⊕ Fin 4 → ZMod 2),
      (∀ b : ↥B, θ (embB hBE b) =
        Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd (eB b)) 0)) ∧
      Acts θ u (blk 1 1) := by
  classical
  obtain ⟨⟨hEcomm, hEexp⟩, _hEcard⟩ := hE
  haveI : IsMulCommutative E := hEcomm
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (setLike_mul_comm a.2 b.2) }
  letI : CommGroup ↥B :=
    { (inferInstance : Group ↥B) with
      mul_comm := fun a b => Subtype.ext (setLike_mul_comm (hBE a.2) (hBE b.2)) }
  have hsqE : ∀ x : ↥E, x * x = 1 := fun x =>
    Subtype.ext (by simpa [pow_two] using hEexp x x.2)
  have hinvE : ∀ x : ↥E, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsqE x)
  have huu : ∀ x : ↥E, u (u x) = x := by
    intro x
    have h := congrArg (fun g : MulAut ↥E => g x) hu2
    simpa [MulAut.mul_apply] using h
  have hu_embB : ∀ b : ↥B, u (embB hBE b) = embB hBE b :=
    fun b => (hfix (embB hBE b)).2 b.2
  have hmem : ∀ e : ↥E, u (e * (u e)⁻¹) = e * (u e)⁻¹ := by
    intro e
    rw [map_mul, map_inv, huu e, hinvE (u e), hinvE e]
    exact mul_comm _ _
  let φ : ↥E →* ↥B :=
    { toFun := fun e => ⟨(e : G) * (((u e : ↥E) : G))⁻¹, (hfix (e * (u e)⁻¹)).1 (hmem e)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun e1 e2 => by
        apply Subtype.ext
        have hEeq : (e1 * e2) * (u (e1 * e2))⁻¹
            = (e1 * (u e1)⁻¹) * (e2 * (u e2)⁻¹) := by
          rw [map_mul, mul_inv_rev]
          ac_rfl
        simpa using congrArg Subtype.val hEeq }
  have φ_apply : ∀ e : ↥E, (φ e : G) = (e : G) * (((u e : ↥E) : G))⁻¹ := fun _ => rfl
  have hker : ∀ e : ↥E, φ e = 1 ↔ (e : G) ∈ B := by
    intro e
    constructor
    · intro h
      have h1 : (e : G) * (((u e : ↥E) : G))⁻¹ = 1 := by
        have := congrArg (fun b : ↥B => (b : G)) h
        simpa [φ_apply] using this
      have h2 : (e : G) = ((u e : ↥E) : G) := by
        have := congrArg (fun g : G => g * ((u e : ↥E) : G)) h1
        simpa [mul_assoc] using this
      exact (hfix e).1 (Subtype.ext h2).symm
    · intro he
      have hue : u e = e := (hfix e).2 he
      apply Subtype.ext
      rw [φ_apply, hue]
      simp
  have hφsurj : Function.Surjective φ := by
    intro b
    obtain ⟨e, he⟩ := hrange (b : G) b.2
    exact ⟨e, Subtype.ext he⟩
  obtain ⟨s, hs⟩ := exists_hom_section hsqE φ hφsurj
  let xE : ↥E →* ↥E := (MonoidHom.id ↥E) * (s.comp φ)⁻¹
  have xE_apply : ∀ e : ↥E, xE e = e * (s (φ e))⁻¹ := fun _ => rfl
  let xOfHom : ↥E →* ↥B :=
    { toFun := fun e => ⟨(xE e : G), (hker (xE e)).1 (by
          show φ (xE e) = 1
          rw [xE_apply, map_mul, map_inv, hs]
          simp)⟩
      map_one' := Subtype.ext (congrArg (Subtype.val : ↥E → G) xE.map_one)
      map_mul' := fun e1 e2 =>
        Subtype.ext (congrArg (Subtype.val : ↥E → G) (xE.map_mul e1 e2)) }
  have xOfHom_apply : ∀ e : ↥E, (xOfHom e : G) = (xE e : G) := fun _ => rfl
  have xOf_apply : ∀ e : ↥E, embB hBE (xOfHom e) = xE e := fun _ => Subtype.ext rfl
  have decomp_eq : ∀ e : ↥E, embB hBE (xOfHom e) * s (φ e) = e := by
    intro e
    rw [xOf_apply, xE_apply, mul_assoc, inv_mul_cancel, mul_one]
  have hu_s : ∀ y : ↥B, u (s y) = embB hBE y * s y := by
    intro y
    have h : (s y : ↥E) * (u (s y))⁻¹ = embB hBE y := by
      apply Subtype.ext
      have := congrArg (fun b : ↥B => (b : G)) (hs y)
      simpa [φ_apply, embB] using this
    have h2 : (s y : ↥E) = embB hBE y * u (s y) := by
      have := congrArg (fun z : ↥E => z * u (s y)) h
      simpa [mul_assoc] using this
    have h3 : (embB hBE y)⁻¹ * s y = u (s y) := by
      conv_lhs => rw [h2]
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [← h3, hinvE]
  have hφ_emb : ∀ b : ↥B, φ (embB hBE b) = 1 := by
    intro b
    apply Subtype.ext
    rw [φ_apply, hu_embB b]
    simp
  have hu_w : ∀ w : ↥E, u w = embB hBE (xOfHom w) * embB hBE (φ w) * s (φ w) := by
    intro w
    conv_lhs => rw [← decomp_eq w]
    rw [map_mul, hu_embB, hu_s, mul_assoc]
  have hφ_uw : ∀ w : ↥E, φ (u w) = φ w := by
    intro w
    rw [hu_w w]
    simp only [map_mul, hφ_emb, hs, one_mul]
  have hxE_uw : ∀ w : ↥E, xE (u w) = xE w * embB hBE (φ w) := by
    intro w
    rw [xE_apply (u w), hφ_uw w, hu_w w, ← xOf_apply w]
    simp [mul_assoc]
  have hxOf_uw : ∀ w : ↥E, xOfHom (u w) = xOfHom w * φ w := by
    intro w
    apply Subtype.ext
    simpa [xOfHom_apply, embB] using congrArg Subtype.val (hxE_uw w)
  have hxOf_embB : ∀ b : ↥B, xOfHom (embB hBE b) = b := by
    intro b
    apply Subtype.ext
    change (xE (embB hBE b) : G) = (b : G)
    rw [xE_apply, hφ_emb b]
    simp [embB]
  let decompHom : ↥E →* ↥B × ↥B := xOfHom.prod φ
  have decompHom_apply : ∀ e : ↥E, decompHom e = (xOfHom e, φ e) := fun _ => rfl
  let decomp : ↥E ≃* ↥B × ↥B := MulEquiv.ofBijective decompHom (by
    constructor
    · intro e1 e2 h
      have h1 : xOfHom e1 = xOfHom e2 := congrArg Prod.fst h
      have h2 : φ e1 = φ e2 := congrArg Prod.snd h
      calc e1 = embB hBE (xOfHom e1) * s (φ e1) := (decomp_eq e1).symm
        _ = embB hBE (xOfHom e2) * s (φ e2) := by rw [h1, h2]
        _ = e2 := decomp_eq e2
    · rintro ⟨b1, b2⟩
      refine ⟨embB hBE b1 * s b2, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change (xE (embB hBE b1 * s b2) : G) = (b1 : G)
        rw [xE_apply]
        rw [show φ (embB hBE b1 * s b2) = b2 by
              rw [map_mul, hφ_emb b1, hs b2, one_mul]]
        simp [mul_assoc, embB]
      · change φ (embB hBE b1 * s b2) = b2
        rw [map_mul, hφ_emb b1, hs b2, one_mul])
  let θ : ↥E ≃* Multiplicative (Fin 4 ⊕ Fin 4 → ZMod 2) :=
    decomp.trans ((eB.prodCongr eB).trans prodSumMulEquiv)
  have hθ : ∀ w : ↥E, Multiplicative.toAdd (θ w) =
      Sum.elim (Multiplicative.toAdd (eB (xOfHom w)))
        (Multiplicative.toAdd (eB (φ w))) := fun _ => rfl
  have hθ_embB : ∀ b : ↥B, θ (embB hBE b) =
      Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd (eB b)) 0) := by
    intro b
    have h1 : Multiplicative.toAdd (θ (embB hBE b)) =
        Sum.elim (Multiplicative.toAdd (eB b)) 0 := by
      rw [hθ (embB hBE b), hxOf_embB b, hφ_emb b, map_one]
      simp
    rw [← ofAdd_toAdd (θ (embB hBE b)), h1]
  have hActs : Acts θ u (blk 1 1) := by
    intro w
    rw [hθ (u w), hθ w, blk_mulVec]
    simp only [Matrix.one_mulVec]
    funext i
    cases i with
    | inl i =>
        simp only [Sum.elim_inl]
        rw [hxOf_uw w, map_mul, toAdd_mul]
    | inr j =>
        simp only [Sum.elim_inr]
        rw [hφ_uw w]
  exact ⟨θ, hθ_embB, hActs⟩

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
