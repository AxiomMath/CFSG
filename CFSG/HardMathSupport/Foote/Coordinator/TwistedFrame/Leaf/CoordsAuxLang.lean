module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxField
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxTorus

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

@[expose] def MonomialProp {τ : Tag} {F : Type} [Field F] (w : WeylGroup τ)
    (ε : (Fin τ.rank → ℤ) → F) : Prop :=
  ∀ x ∈ Qθ τ F,
    canonicalRep (coxeterSystem τ) F w * x * (canonicalRep (coxeterSystem τ) F w)⁻¹ ∈ Qθ τ F ∧
    ∀ β ∈ Deg1 τ, heisCoord τ F (canonicalRep (coxeterSystem τ) F w * x *
      (canonicalRep (coxeterSystem τ) F w)⁻¹) (w • β) = ε β * heisCoord τ F x β

@[expose] def Bset (c : TwClass) : Set (Fin c.tag.rank → ℤ) :=
  {β | β ∈ Deg1 c.tag ∧ β ∈ c.S₁}

section Lang

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

@[expose] def bc : ModGL τ K →* ModGL τ D.L := baseChangeGL (algebraMap K D.L)

@[expose] def Ψ (q : ModGL τ K) : ModGL τ D.L := D.g⁻¹ * bc D q * D.g

@[expose] def κ (q : ModGL τ K) : (Fin τ.rank → ℤ) → D.L := heisCoord τ D.L (Ψ D q)

@[expose] def IsSig (ε : (Fin τ.rank → ℤ) → D.L) (v : (Fin τ.rank → ℤ) → D.L) : Prop :=
  (∀ β, β ∉ Deg1 τ → v β = 0) ∧ ∀ β ∈ Deg1 τ, v (w • β) = ε β * D.Fr (v β)

theorem bc_Qθ {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    bc D q ∈ Qθ τ D.L ∧
      heisCoord τ D.L (bc D q) = fun β => algebraMap K D.L (heisCoord τ K q β) := by
  refine Qθ_induction (P := fun q => bc D q ∈ Qθ τ D.L ∧
      heisCoord τ D.L (bc D q) = fun β => algebraMap K D.L (heisCoord τ K q β)) ?_ ?_ ?_ ?_ ?_ q hq
  · refine ⟨by rw [map_one]; exact one_mem _, ?_⟩
    rw [map_one, heisCoord_one, heisCoord_one]
    funext β
    simp
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    refine ⟨by rw [map_mul]; exact mul_mem hxQ hyQ, ?_⟩
    rw [map_mul, (heisCoord_spec τ D.L).mul _ hxQ _ hyQ, (heisCoord_spec τ K).mul _ hx _ hy, hxc,
      hyc]
    funext β
    simp only [Pi.add_apply, map_add]
  · rintro x hx ⟨hxQ, hxc⟩
    refine ⟨by rw [map_inv]; exact inv_mem hxQ, ?_⟩
    rw [map_inv, heisCoord_inv hxQ, heisCoord_inv hx, hxc]
    funext β
    simp only [Pi.neg_apply, map_neg]
  · intro β hβ t
    have e : bc D (pinnedX τ K β t) = pinnedX τ D.L β (algebraMap K D.L t) := baseChangeGL_pinnedX _ _ _
    rw [e]
    refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hβ _, ?_⟩
    rw [(heisCoord_spec τ D.L).pinnedX_deg1 β hβ, (heisCoord_spec τ K).pinnedX_deg1 β hβ]
    funext γ
    by_cases h : γ = β
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  · intro t
    have e : bc D (pinnedX τ K (highRoot τ) t) =
        pinnedX τ D.L (highRoot τ) (algebraMap K D.L t) := baseChangeGL_pinnedX _ _ _
    rw [e]
    refine ⟨Uθ_le_Qθ (mem_rootSubgroup.2 ⟨_, rfl⟩), ?_⟩
    rw [(heisCoord_spec τ D.L).pinnedX_highRoot, (heisCoord_spec τ K).pinnedX_highRoot]
    funext γ
    simp

theorem Ψ_Qθ {q : ModGL τ K} (hq : q ∈ Qθ τ K) : Ψ D q ∈ Qθ τ D.L := by
  have h := Lθ_conj_mem_Qθ (inv_mem D.g_mem) (bc_Qθ D hq).1
  rwa [inv_inv] at h

theorem Ψ_mul (q q' : ModGL τ K) : Ψ D (q * q') = Ψ D q * Ψ D q' := by
  unfold Ψ
  rw [map_mul]
  group

theorem κ_mul {q q' : ModGL τ K} (hq : q ∈ Qθ τ K) (hq' : q' ∈ Qθ τ K) :
    κ D (q * q') = κ D q + κ D q' := by
  unfold κ
  rw [Ψ_mul, (heisCoord_spec τ D.L).mul _ (Ψ_Qθ D hq) _ (Ψ_Qθ D hq')]

theorem κ_eq_zero_iff {q : ModGL τ K} (hq : q ∈ Qθ τ K) : κ D q = 0 ↔ q ∈ Uθ τ K := by
  obtain ⟨hbQ, hbc⟩ := bc_Qθ D hq
  constructor
  · intro h
    have h1 : Ψ D q ∈ Uθ τ D.L := ((heisCoord_spec τ D.L).eq_zero_iff _ (Ψ_Qθ D hq)).1 h
    have h2 : bc D q ∈ Uθ τ D.L := by
      have := Lθ_conj_mem_Uθ D.g_mem h1
      have e : D.g * Ψ D q * D.g⁻¹ = bc D q := by unfold Ψ; group
      rwa [e] at this
    have h3 := ((heisCoord_spec τ D.L).eq_zero_iff _ hbQ).2 h2
    rw [hbc] at h3
    refine ((heisCoord_spec τ K).eq_zero_iff _ hq).1 ?_
    funext β
    have := congrFun h3 β
    simpa using this
  · intro h
    have h0 := ((heisCoord_spec τ K).eq_zero_iff _ hq).2 h
    have h1 : heisCoord τ D.L (bc D q) = 0 := by
      rw [hbc, h0]
      funext β
      simp
    have h2 : bc D q ∈ Uθ τ D.L := ((heisCoord_spec τ D.L).eq_zero_iff _ hbQ).1 h1
    have h3 : Ψ D q ∈ Uθ τ D.L := Lθ_conj_mem_Uθ (inv_mem D.g_mem) h2 |> fun h => by
      rwa [inv_inv] at h
    exact ((heisCoord_spec τ D.L).eq_zero_iff _ (Ψ_Qθ D hq)).2 h3

theorem κ_support {q : ModGL τ K} (hq : q ∈ Qθ τ K) {β : Fin τ.rank → ℤ} (hβ : β ∉ Deg1 τ) :
    κ D q β = 0 :=
  (heisCoord_spec τ D.L).support _ (Ψ_Qθ D hq) β hβ

theorem frob_bc {q : ModGL τ K} (hq : q ∈ Qθ τ K) : frob (τ := τ) D.Fr (bc D q) = bc D q := by
  haveI : Fintype K := Fintype.ofFinite K
  have hfix : ∀ t : K, D.Fr (algebraMap K D.L t) = algebraMap K D.L t := by
    intro t
    rw [D.hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  refine Qθ_induction (P := fun q => frob (τ := τ) D.Fr (bc D q) = bc D q) ?_ ?_ ?_ ?_ ?_ q hq
  · simp
  · intro x y _ _ hx hy
    rw [map_mul, map_mul, hx, hy]
  · intro x _ hx
    rw [map_inv, map_inv, hx]
  · intro β _ t
    have e : bc D (pinnedX τ K β t) = pinnedX τ D.L β (algebraMap K D.L t) := baseChangeGL_pinnedX _ _ _
    rw [e, frob_pinnedX, hfix]
  · intro t
    have e : bc D (pinnedX τ K (highRoot τ) t) =
        pinnedX τ D.L (highRoot τ) (algebraMap K D.L t) := baseChangeGL_pinnedX _ _ _
    rw [e, frob_pinnedX, hfix]

theorem frob_g : frob (τ := τ) D.Fr D.g = D.g * canonicalRep (coxeterSystem τ) D.L w := D.lang

theorem frob_Ψ {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    frob (τ := τ) D.Fr (Ψ D q) =
      (canonicalRep (coxeterSystem τ) D.L w)⁻¹ * Ψ D q * canonicalRep (coxeterSystem τ) D.L w := by
  unfold Ψ
  rw [map_mul, map_mul, map_inv, frob_bc D hq, frob_g]
  group

theorem κ_isSig (hw : w • highRoot τ = highRoot τ) {ε : (Fin τ.rank → ℤ) → D.L}
    (hε : MonomialProp w ε) {q : ModGL τ K} (hq : q ∈ Qθ τ K) : IsSig D ε (κ D q) := by
  refine ⟨fun β hβ => κ_support D hq hβ, fun β hβ => ?_⟩
  have hΨ := Ψ_Qθ D hq
  obtain ⟨hxQ, hxc⟩ := frob_Qθ (τ := τ) D.Fr hΨ
  have hconj : canonicalRep (coxeterSystem τ) D.L w * frob (τ := τ) D.Fr (Ψ D q) *
      (canonicalRep (coxeterSystem τ) D.L w)⁻¹ = Ψ D q := by
    rw [frob_Ψ D hq]
    group
  obtain ⟨-, hε'⟩ := hε _ hxQ
  have := hε' β hβ
  rw [hconj, hxc] at this
  exact this

theorem exists_lift (hw : w • highRoot τ = highRoot τ) {ε : (Fin τ.rank → ℤ) → D.L}
    (hε : MonomialProp w ε) {v : (Fin τ.rank → ℤ) → D.L} (hv : IsSig D ε v) :
    ∃ q ∈ Qθ τ K, κ D q = v := by
  classical
  obtain ⟨lst, hnd, hmem⟩ := CoordAux.exists_list_Deg1 (τ := τ)
  obtain ⟨hxbQ, hxbc⟩ := heisCoord_prodX (K := D.L) hnd (fun β hβ => (hmem β).1 hβ) v
  set xb := CoordAux.prodX lst v with hxb
  have hxbv : heisCoord τ D.L xb = v := by
    funext ν
    rw [hxbc ν]
    by_cases hν : ν ∈ lst
    · rw [if_pos hν]
    · rw [if_neg hν]
      exact (hv.1 ν (fun h => hν ((hmem ν).2 h))).symm
  have hyQ : D.g * xb * D.g⁻¹ ∈ Qθ τ D.L := Lθ_conj_mem_Qθ D.g_mem hxbQ
  set y := D.g * xb * D.g⁻¹ with hy
  obtain ⟨hx'Q, hx'c⟩ := frob_Qθ (τ := τ) D.Fr hxbQ
  obtain ⟨hnx'Q, hnx'⟩ := hε _ hx'Q
  have hw' : w⁻¹ • highRoot τ = highRoot τ := by rw [inv_smul_eq_iff, hw]
  have hcoord : heisCoord τ D.L (canonicalRep (coxeterSystem τ) D.L w * frob (τ := τ) D.Fr xb * (canonicalRep (coxeterSystem τ) D.L w)⁻¹) = v := by
    funext γ
    by_cases hγ : γ ∈ Deg1 τ
    · have hβ : w⁻¹ • γ ∈ Deg1 τ := by
        refine CoordAux.mem_Deg1.2 ⟨IsRoot.smul (CoordAux.mem_Deg1.1 hγ).1 w⁻¹, ?_⟩
        rw [degθ_smul_of_fix hw']
        exact (CoordAux.mem_Deg1.1 hγ).2
      have h1 := hnx' (w⁻¹ • γ) hβ
      rw [smul_inv_smul, hx'c, hxbv] at h1
      rw [h1]
      have h2 := hv.2 (w⁻¹ • γ) hβ
      rw [smul_inv_smul] at h2
      exact h2.symm
    · rw [(heisCoord_spec τ D.L).support _ hnx'Q γ hγ, hv.1 γ hγ]
  have hz₀ : canonicalRep (coxeterSystem τ) D.L w * frob (τ := τ) D.Fr xb * (canonicalRep (coxeterSystem τ) D.L w)⁻¹ * xb⁻¹ ∈ Uθ τ D.L :=
    mul_inv_mem_Uθ_of_coord_eq hnx'Q hxbQ (by rw [hcoord, hxbv])
  have hFy : frob (τ := τ) D.Fr y = (D.g * (canonicalRep (coxeterSystem τ) D.L w * frob (τ := τ) D.Fr xb * (canonicalRep (coxeterSystem τ) D.L w)⁻¹ * xb⁻¹) * D.g⁻¹) * y := by
    rw [hy, map_mul, map_mul, map_inv, frob_g]
    group
  have hz₁ : D.g * (canonicalRep (coxeterSystem τ) D.L w * frob (τ := τ) D.Fr xb * (canonicalRep (coxeterSystem τ) D.L w)⁻¹ * xb⁻¹) * D.g⁻¹ ∈ Uθ τ D.L :=
    Lθ_conj_mem_Uθ D.g_mem hz₀
  obtain ⟨hFyQ, hFyc⟩ := frob_Qθ (τ := τ) D.Fr hyQ
  have hFycoord : heisCoord τ D.L (frob (τ := τ) D.Fr y) = heisCoord τ D.L y := by
    rw [hFy, (heisCoord_spec τ D.L).mul _ (Uθ_le_Qθ hz₁) _ hyQ,
      ((heisCoord_spec τ D.L).eq_zero_iff _ (Uθ_le_Qθ hz₁)).2 hz₁, zero_add]
  have hfixy : ∀ β, D.Fr (heisCoord τ D.L y β) = heisCoord τ D.L y β := fun β => by
    have := congrFun hFyc β
    rw [hFycoord] at this
    exact this.symm
  have hrange : ∀ β, ∃ k : K, algebraMap K D.L k = heisCoord τ D.L y β := fun β =>
    CoordsAux.mem_range_algebraMap_of_pow_card (by rw [← D.hFr]; exact hfixy β)
  choose f hf using hrange
  have hfsupp : ∀ β, β ∉ Deg1 τ → f β = 0 := fun β hβ => by
    apply (algebraMap K D.L).injective
    rw [hf β, (heisCoord_spec τ D.L).support _ hyQ β hβ, map_zero]
  obtain ⟨q, hqQ, hqc⟩ := (heisCoord_spec τ K).surj f hfsupp
  refine ⟨q, hqQ, ?_⟩
  obtain ⟨hbQ, hbc⟩ := bc_Qθ D hqQ
  have hbcy : heisCoord τ D.L (bc D q) = heisCoord τ D.L y := by
    rw [hbc, hqc]
    funext β
    exact hf β
  have hz₂ : bc D q * y⁻¹ ∈ Uθ τ D.L := mul_inv_mem_Uθ_of_coord_eq hbQ hyQ hbcy
  have hΨq : Ψ D q = (D.g⁻¹ * (bc D q * y⁻¹) * D.g) * xb := by
    unfold Ψ
    rw [hy]
    group
  have hz₃ : D.g⁻¹ * (bc D q * y⁻¹) * D.g ∈ Uθ τ D.L := by
    have := Lθ_conj_mem_Uθ (inv_mem D.g_mem) hz₂
    rwa [inv_inv] at this
  unfold κ
  rw [hΨq, (heisCoord_spec τ D.L).mul _ (Uθ_le_Qθ hz₃) _ hxbQ,
    ((heisCoord_spec τ D.L).eq_zero_iff _ (Uθ_le_Qθ hz₃)).2 hz₃, zero_add, hxbv]

end Lang

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
