module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyPerm

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Root

variable {F : Type*} [Field F]

theorem sl_mulVec_inv (h : SL(2, F)) (v : Fin 2 → F) :
    ((h⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
      ((h : Matrix (Fin 2) (Fin 2) F).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem sl_mulVec_inv' (h : SL(2, F)) (v : Fin 2 → F) :
    (h : Matrix (Fin 2) (Fin 2) F).mulVec
      (((h⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem root_conj_iff (ℓ₀ : Submodule F (Fin 2 → F)) (g₀ g : SL(2, F)) :
    ((∀ v ∈ ℓ₀, ((g₀⁻¹ * g * g₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
      ∀ v, ((g₀⁻¹ * g * g₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ₀) ↔
    ((∀ w ∈ ℓ₀.map (Matrix.mulVecLin (g₀ : Matrix (Fin 2) (Fin 2) F)),
        (g : Matrix (Fin 2) (Fin 2) F).mulVec w = w) ∧
      ∀ w, (g : Matrix (Fin 2) (Fin 2) F).mulVec w - w ∈
        ℓ₀.map (Matrix.mulVecLin (g₀ : Matrix (Fin 2) (Fin 2) F))) := by
  have happ : ∀ v, ((g₀⁻¹ * g * g₀ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec v =
      ((g₀⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
        ((g : Matrix (Fin 2) (Fin 2) F).mulVec ((g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v)) := by
    intro v
    simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  have hmem : ∀ w, w ∈ ℓ₀.map (Matrix.mulVecLin (g₀ : Matrix (Fin 2) (Fin 2) F)) ↔
      ∃ v ∈ ℓ₀, (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v = w := by
    intro w
    simp [Submodule.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := (hmem w).1 hw
      have e := h1 v hv
      rw [happ] at e
      have e2 := congrArg (fun x => (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec x) e
      simp only [sl_mulVec_inv'] at e2
      exact e2
    · intro w
      rw [hmem]
      refine ⟨((g₀⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec
        ((g : Matrix (Fin 2) (Fin 2) F).mulVec w) -
          ((g₀⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w, ?_, ?_⟩
      · have e := h2 (((g₀⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w)
        rw [happ, sl_mulVec_inv'] at e
        exact e
      · rw [Matrix.mulVec_sub, sl_mulVec_inv', sl_mulVec_inv']
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro v hv
      have e := h1 ((g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v) ((hmem _).2 ⟨v, hv, rfl⟩)
      rw [happ, e, sl_mulVec_inv]
    · intro v
      obtain ⟨u, hu, hue⟩ := (hmem _).1 (h2 ((g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v))
      rw [happ]
      have e : (g : Matrix (Fin 2) (Fin 2) F).mulVec ((g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v) =
          (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec u +
            (g₀ : Matrix (Fin 2) (Fin 2) F).mulVec v := by
        rw [hue]
        abel
      rw [e, ← Matrix.mulVec_add, sl_mulVec_inv]
      simpa using hu

end Root

section Natural

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] [Finite V] in
theorem natural_conj_image {L A A₀ : Subgroup (V ≃ₗ[ZMod 2] V)} (θe : ↥L ≃* SL(2, F))
    {k : V ≃ₗ[ZMod 2] V} (hk : k ∈ L) (hconj : ∀ x, x ∈ A ↔ k⁻¹ * x * k ∈ A₀)
    (g : SL(2, F)) :
    g ∈ (A.subgroupOf L).map θe.toMonoidHom ↔
      (θe ⟨k, hk⟩)⁻¹ * g * θe ⟨k, hk⟩ ∈ (A₀.subgroupOf L).map θe.toMonoidHom := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : (a : V ≃ₗ[ZMod 2] V) ∈ A := ha
    have hka : k⁻¹ * (a : V ≃ₗ[ZMod 2] V) * k ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem hk) a.2) hk
    refine ⟨⟨_, hka⟩, (hconj _).1 ha', ?_⟩
    show θe ⟨k⁻¹ * a * k, hka⟩ = (θe ⟨k, hk⟩)⁻¹ * θe a * θe ⟨k, hk⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · rintro ⟨a₀, ha₀, he⟩
    have ha₀' : (a₀ : V ≃ₗ[ZMod 2] V) ∈ A₀ := ha₀
    have hka : k * (a₀ : V ≃ₗ[ZMod 2] V) * k⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hk a₀.2) (L.inv_mem hk)
    refine ⟨⟨_, hka⟩, (hconj _).2 (by simpa [mul_assoc] using ha₀'), ?_⟩
    have hh : θe a₀ = (θe ⟨k, hk⟩)⁻¹ * g * θe ⟨k, hk⟩ := he
    show θe ⟨k * a₀ * k⁻¹, hka⟩ = g
    have e2 : (⟨k * a₀ * k⁻¹, hka⟩ : ↥L) = ⟨k, hk⟩ * a₀ * ⟨k, hk⟩⁻¹ := Subtype.ext rfl
    rw [e2, map_mul, map_mul, map_inv, hh]
    group

theorem isSylowOf_two_of {G : Type*} [Group G] [Finite G] {S K : Subgroup G}
    (h : IsSylowTwoOf S K) : CFSG.ABGLocalTools.IsSylowOf 2 S K :=
  CFSG.ABGLocalTools.isSylowOf_iff.2 h

theorem isSylowTwoOf_of_natData (ctx : FamilyCtx H T n F r Lc) {i : Fin r}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hN : NatData (Lc i) A (ctx.α i)) :
    IsSylowTwoOf A (Lc i) := by
  have hodd := odd_index_natData (by have := ctx.hn; omega) ctx.hF (ctx.α i)
    (ctx.layer.center_trivial i) hN
  refine ⟨hN.1, ?_, ?_⟩
  · exact IsPGroup.of_card (hN.2.1.trans ctx.hF)
  · intro hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem natData_of_moving (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i) (i : Fin r) :
    ∃ A₀, IsMinOffender H A₀ ∧ ⁅Lc i, A₀⁆ ≠ ⊥ ∧ NatData (Lc i) A₀ (ctx.α i) := by
  obtain ⟨A₀, hA₀, hLA₀⟩ := ctx.layer.moving i
  have hmove : ⁅Lc i, A₀⁆ ≠ ⊥ := by
    rw [hLA₀]
    exact ctx.hLc.ne_bot i
  rcases alt_dichotomy ctx hA₀ i hmove with hN | ⟨-, -, hnle, -⟩
  · exact ⟨A₀, hA₀, hmove, hN⟩
  · exact absurd (hglob i A₀ hA₀ hmove) hnle

theorem natural_family (ctx : FamilyCtx H T n F r Lc)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i) :
    NaturalFamily H F r Lc := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hB : ∀ i, blockB H (Lc i) = Lc i := fun i =>
    le_antisymm (blockB_le_of fun A hA hmove => hglob i A hA hmove) (Lc_le_blockB ctx i)
  refine ⟨hB, ?_, ?_, ?_⟩
  · rw [offenderJ_eq ctx, ctx.layer.K_eq]
    exact iSup_congr hB
  · intro i
    obtain ⟨A₀, hA₀, hmove₀, hN₀⟩ := natData_of_moving ctx hglob i
    have hSA₀ : IsSylowTwoOf A₀ (Lc i) := isSylowTwoOf_of_natData ctx hN₀
    obtain ⟨-, -, β, hβ, ℓ₀, hℓ₀1, hℓ₀⟩ := hN₀
    have hθinj : Function.Injective (thetaL (Lc i) (ctx.α i)) :=
      thetaL_injective (ctx.α i) (ctx.layer.center_trivial i)
    let θe : ↥(Lc i) ≃* SL(2, F) :=
      MulEquiv.ofBijective (thetaL (Lc i) (ctx.α i)) ⟨hθinj, thetaL_surjective (Lc i) (ctx.α i)⟩
    have hθe : θe.toMonoidHom = thetaL (Lc i) (ctx.α i) := MonoidHom.ext fun _ => rfl
    refine ⟨θe, β, fun l u u' hu' => hβ l u u' hu', ?_⟩
    intro A hAS
    obtain ⟨k, hk, hkA⟩ :=
      (isSylowOf_two_of hSA₀).exists_mem_conj (isSylowOf_two_of hAS)
    let g₀ : SL(2, F) := θe ⟨k, hk⟩
    have hinj : Function.Injective (Matrix.mulVecLin (g₀ : Matrix (Fin 2) (Fin 2) F)) := by
      intro v w h
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at h
      have h' := congrArg (((g₀⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec) h
      rwa [sl_mulVec_inv, sl_mulVec_inv] at h'
    refine ⟨ℓ₀.map (Matrix.mulVecLin (g₀ : Matrix (Fin 2) (Fin 2) F)), ?_, fun g => ?_⟩
    · rw [← (Submodule.equivMapOfInjective _ hinj ℓ₀).finrank_eq]
      exact hℓ₀1
    · rw [natural_conj_image θe hk hkA g, hθe, hℓ₀]
      exact root_conj_iff ℓ₀ g₀ g
  · intro A
    constructor
    · intro hA
      obtain ⟨-, i, hi, -⟩ := ctx.layer.offender A hA
      refine ⟨i, ?_⟩
      have hAL := hglob i A hA hi
      rcases alt_dichotomy ctx hA i hi with hN | ⟨-, -, hnle, -⟩
      · exact isSylowTwoOf_of_natData ctx hN
      · exact absurd hAL hnle
    · rintro ⟨i, hAS⟩
      obtain ⟨A₀, hA₀, hmove₀, hN₀⟩ := natData_of_moving ctx hglob i
      obtain ⟨k, hk, hkA⟩ := (isSylowOf_two_of (isSylowTwoOf_of_natData ctx hN₀)).exists_mem_conj
        (isSylowOf_two_of hAS)
      have hconj : A = conjSub k A₀ := by
        ext x
        rw [mem_conjSub]
        exact hkA x
      rw [hconj]
      exact hA₀.conj ((ctx.hLc.isComp i).1 hk)

omit [Finite V] in
theorem not_natural_and_deleted (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc)
    (hdel : DeletedFamily H n r Lc) : False := by
  obtain ⟨Ω, _, _, hΩ, ψ, β, -, hψL, -⟩ := hdel.model ⟨0, ctx.layer.r_pos⟩
  have htop : (Lc ⟨0, ctx.layer.r_pos⟩).subgroupOf (blockB H (Lc ⟨0, ctx.layer.r_pos⟩)) = ⊤ := by
    rw [eq_top_iff]
    intro b _
    show (b : V ≃ₗ[ZMod 2] V) ∈ Lc ⟨0, ctx.layer.r_pos⟩
    exact (SetLike.ext_iff.1 (hnat.B_eq ⟨0, ctx.layer.r_pos⟩) _).1 b.2
  rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.2 ψ.surjective] at hψL
  exact alternatingGroup_ne_top (by omega) hψL.symm

end Natural

end CFSG.QuasithinUnique.Setup.Lift
