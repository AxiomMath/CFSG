module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4H1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem injective_of_natural {G : Type*} [Group G] {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (L : Subgroup G)
    (I : Submodule (ZMod 2) W) (hI : ∀ l ∈ L, ∀ v ∈ I, ρ l v ∈ I)
    (hIL : I ≤ Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ v ∈ I, w = ρ l v - v})
    (ψ : L →* orthElementaryGroup (quadPlus 4 K)) (hψ : Function.Surjective ψ)
    (hψc : ∀ l : L, ψ l = 1 → ∀ l' : L, l * l' = l' * l)
    (p : I →+ (Fin 4 ⊕ Fin 4 → K)) (hp : Function.Surjective p)
    (hpe : ∀ (l : L) (v w : I), (w : W) = ρ l v →
      p w = (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (p v))
    (hker : ∀ v : I, p v = 0 → ∀ l ∈ L, ρ l v = v) :
    Function.Injective p := by
  classical
  let : Module (ZMod 2) (Fin 4 ⊕ Fin 4 → K) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      rw [two_nsmul]
      funext i
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      calc x i + x i = (2 : K) * x i := by ring
        _ = 0 := by rw [h2, zero_mul]
  let τ : L → I →+ I := fun l =>
    { toFun := fun v => ⟨ρ l.1 v.1, hI l.1 l.2 v.1 v.2⟩
      map_zero' := by ext; simp
      map_add' := by intro v w; ext; simp [map_add] }
  have τ_apply : ∀ (l : L) (v : I), (τ l v : W) = ρ l.1 v.1 := fun l v => rfl
  have τ_mul : ∀ (l l' : L) (v : I), τ (l * l') v = τ l (τ l' v) := by
    intro l l' v
    apply Subtype.ext
    show ρ (l.1 * l'.1) v.1 = ρ l.1 (ρ l'.1 v.1)
    rw [map_mul, Module.End.mul_apply]
  have τ_ker : ∀ (l : L) (z : ↥p.ker), τ l (z : I) = (z : I) := by
    intro l z
    apply Subtype.ext
    exact hker (z : I) (AddMonoidHom.mem_ker.1 z.2) l.1 l.2
  let pL : I →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → K) := p.toZModLinearMap 2
  have hpL : Function.Surjective pL := by
    intro x
    obtain ⟨y, hy⟩ := hp x
    exact ⟨y, by rw [AddMonoidHom.coe_toZModLinearMap]; exact hy⟩
  obtain ⟨s0, hs0⟩ :=
    LinearMap.exists_rightInverse_of_surjective pL (LinearMap.range_eq_top.2 hpL)
  have hs0app : ∀ x : (Fin 4 ⊕ Fin 4 → K), p (s0 x) = x := by
    intro x
    have h := congrArg (fun f : (Fin 4 ⊕ Fin 4 → K) →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → K) => f x) hs0
    simpa [pL, AddMonoidHom.coe_toZModLinearMap] using h
  let cFun : L → (Fin 4 ⊕ Fin 4 → K) → ↥p.ker := fun l x =>
    ⟨τ l (s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x)) - s0 x, by
      rw [AddMonoidHom.mem_ker, map_sub]
      have h1 : p (τ l (s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x))) =
          (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
            (p (s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
              (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x))) :=
        hpe l _ _ rfl
      rw [h1]
      have hx1 : p (s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x)) =
          ((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x := hs0app _
      have hx2 : p (s0 x) = x := hs0app x
      rw [hx1, hx2, LinearEquiv.apply_symm_apply, sub_self]⟩
  have cFun_add : ∀ (l : L) (x y : (Fin 4 ⊕ Fin 4 → K)),
      cFun l (x + y) = cFun l x + cFun l y := by
    intro l x y
    apply Subtype.ext
    simp only [cFun, map_add, AddSubgroup.coe_add]
    abel
  let c : L → (Fin 4 ⊕ Fin 4 → K) →+ ↥p.ker := fun l => AddMonoidHom.mk' (cFun l) (cFun_add l)
  have c_apply : ∀ (l : L) (x : (Fin 4 ⊕ Fin 4 → K)), (c l x : I) =
      τ l (s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x)) - s0 x := fun l x => rfl

  have hsymm : ∀ (l l' : L) (x : Fin 4 ⊕ Fin 4 → K),
      (((ψ (l * l') : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x) =
      (((ψ l' : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm
        ((((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x))) := by
    intro l l' x
    have hmul : ((ψ (l * l') : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        ((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) *
        ((ψ l' : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := by
      rw [map_mul]
      rfl
    rw [hmul, LinearEquiv.symm_apply_eq]
    simp [LinearEquiv.mul_apply]
  have hc : ∀ l l' : L, c (l * l') = c l + homAct (ψ l) (c l') := by
    intro l l'
    refine AddMonoidHom.ext fun x => ?_
    apply Subtype.ext
    show (c (l * l') x : I) = (c l x + homAct (ψ l) (c l') x : I)
    rw [show homAct (ψ l) (c l') x =
      (c l' (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x)) from rfl]
    rw [c_apply, c_apply, c_apply]
    rw [hsymm l l' x]
    rw [τ_mul l l']
    have h1 : τ l' (s0 (((ψ l' : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm
          ((((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x)))) =
        (c l' ((((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x)) : I) +
          s0 ((((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm x)) := by
      rw [c_apply]
      abel
    rw [h1, map_add, τ_ker]
    abel

  have hfix_z : ∀ (z : L) (hz : ψ z = 1) (e : orthElementaryGroup (quadPlus 4 K)),
      homAct e (c z) = c z := by
    intro z hz e
    obtain ⟨l, hl⟩ := hψ e
    rw [← hl]
    have hsymm1 : (1 : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).symm = 1 := by
      rw [show (1 : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        LinearEquiv.refl K (Fin 4 ⊕ Fin 4 → K) from rfl, LinearEquiv.refl_symm]
    have hone : homAct (1 : orthElementaryGroup (quadPlus 4 K)) (c l) = c l := by
      refine AddMonoidHom.ext fun x => ?_
      simp only [homAct, AddMonoidHom.comp_apply]
      rw [show ((1 : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = 1 from Subgroup.coe_one _, hsymm1]
      simp
    have h1 : c (z * l) = c z + c l := by
      rw [hc z l, hz, hone]
    have h2 : c (l * z) = c l + homAct (ψ l) (c z) := hc l z
    have h3 : z * l = l * z := hψc z hz l
    rw [h3] at h1
    have h5 : c z + c l = c l + homAct (ψ l) (c z) := h1.symm.trans h2
    have h6 : c l + c z = c l + homAct (ψ l) (c z) := by
      rw [add_comm (c l) (c z)]
      exact h5
    exact (add_left_cancel h6).symm
  have hcz0 : ∀ (z : L) (hz : ψ z = 1), c z = 0 := by
    intro z hz
    exact eq_zero_of_homAct_eq (c z) (fun e => hfix_z z hz e)
  have hc_indep : ∀ (l l' : L), ψ l = ψ l' → c l = c l' := by
    intro l l' hl
    have hz : ψ (l⁻¹ * l') = 1 := by
      rw [map_mul, map_inv, hl, inv_mul_cancel]
    have hz0 : c (l⁻¹ * l') = 0 := hcz0 (l⁻¹ * l') hz
    have hzz : l * (l⁻¹ * l') = l' := by group
    have hgoal : c l' = c l := by
      calc c l' = c (l * (l⁻¹ * l')) := by rw [hzz]
        _ = c l + homAct (ψ l) (c (l⁻¹ * l')) := hc l (l⁻¹ * l')
        _ = c l + homAct (ψ l) 0 := by rw [hz0]
        _ = c l := by simp [homAct]
    exact hgoal.symm
  let d : orthElementaryGroup (quadPlus 4 K) → (Fin 4 ⊕ Fin 4 → K) →+ ↥p.ker :=
    fun e => c (Function.surjInv hψ e)
  have hd : ∀ e e' : orthElementaryGroup (quadPlus 4 K),
      d (e * e') = d e + homAct e (d e') := by
    intro e e'
    have hl : ψ (Function.surjInv hψ e) = e := Function.surjInv_eq hψ e
    have hl' : ψ (Function.surjInv hψ e') = e' := Function.surjInv_eq hψ e'
    have hprod : ψ (Function.surjInv hψ e * Function.surjInv hψ e') = e * e' := by
      rw [map_mul, hl, hl']
    have h1 : c (Function.surjInv hψ (e * e')) =
        c (Function.surjInv hψ e * Function.surjInv hψ e') :=
      hc_indep _ _ (by rw [Function.surjInv_eq hψ (e * e'), hprod])
    change c (Function.surjInv hψ (e * e')) =
      c (Function.surjInv hψ e) + homAct e (c (Function.surjInv hψ e'))
    rw [h1, hc, hl]
  obtain ⟨f, hf⟩ := exists_eq_homAct_sub d hd
  let fI : (Fin 4 ⊕ Fin 4 → K) →+ I := (p.ker).subtype.comp f
  let sH : (Fin 4 ⊕ Fin 4 → K) →+ I := s0.toAddMonoidHom - fI
  let s : (Fin 4 ⊕ Fin 4 → K) →ₗ[ZMod 2] I := sH.toZModLinearMap 2
  have hs_app : ∀ x : (Fin 4 ⊕ Fin 4 → K), (s x : I) = s0 x - (f x : I) := fun x => rfl
  have hs_p : ∀ x : (Fin 4 ⊕ Fin 4 → K), p (s x) = x := by
    intro x
    rw [hs_app x, map_sub, hs0app]
    have h0 : p ((f x : ↥p.ker) : I) = 0 := AddMonoidHom.mem_ker.1 (f x).2
    rw [h0, sub_zero]
  have hs_equiv : ∀ (l : L) (x : (Fin 4 ⊕ Fin 4 → K)),
      τ l (s x) = s (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) := by
    intro l x
    have hcl : c l = d (ψ l) :=
      hc_indep l (Function.surjInv hψ (ψ l)) (Function.surjInv_eq hψ (ψ l)).symm
    have hfval : (d (ψ l) (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I) =
        (f x : I) - (f (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I) := by
      have h := congrArg (fun g : (Fin 4 ⊕ Fin 4 → K) →+ ↥p.ker =>
        g (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x)) (hf (ψ l))
      have h2 : ((homAct (ψ l) f - f) (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : ↥p.ker) =
          f x - f (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) := by
        rw [AddMonoidHom.sub_apply, show homAct (ψ l) f (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) = f x from by
          simp [homAct]]
      rw [h2] at h
      exact congrArg Subtype.val h
    have hcval : (c l (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I) =
        (f x : I) - (f (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I) := by
      rw [hcl]
      exact hfval
    have hcapp : (c l (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I) =
        τ l (s0 x) - s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) := by
      rw [c_apply, LinearEquiv.symm_apply_apply]
    rw [hs_app x, hs_app (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x)]
    rw [map_sub, τ_ker l (f x)]
    have h3 : τ l (s0 x) - s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) =
        (f x : I) - (f (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I) := by
      rw [← hcapp, hcval]
    calc τ l (s0 x) - (f x : I)
        = (τ l (s0 x) - s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x)) +
          (s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) - (f x : I)) := by abel
      _ = ((f x : I) - (f (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I)) +
          (s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) - (f x : I)) := by rw [h3]
      _ = s0 (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) -
          (f (((ψ l : orthElementaryGroup (quadPlus 4 K)) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x) : I) := by abel

  let S : Submodule (ZMod 2) I := LinearMap.range s
  have hgen : {w : W | ∃ l ∈ L, ∃ v ∈ I, w = ρ l v - v} ⊆
      (S.map I.subtype : Set W) := by
    rintro w ⟨l, hl, v, hv, rfl⟩
    let vI : I := ⟨v, hv⟩
    have hker_v : p (vI - s (p vI)) = 0 := by
      rw [map_sub, hs_p, sub_self]
    have hfix : τ ⟨l, hl⟩ (vI - s (p vI)) = vI - s (p vI) :=
      τ_ker ⟨l, hl⟩ ⟨vI - s (p vI), hker_v⟩
    have hdecomp : vI = s (p vI) + (vI - s (p vI)) := by abel
    have hτeq : τ ⟨l, hl⟩ vI =
        s (((ψ ⟨l, hl⟩ : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (p vI)) +
          (vI - s (p vI)) := by
      conv_lhs => rw [hdecomp]
      rw [map_add, hs_equiv, hfix]
    have hdiff : τ ⟨l, hl⟩ vI - vI =
        s (((ψ ⟨l, hl⟩ : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (p vI)) - s (p vI) := by
      rw [hτeq]
      abel
    have hdiff' : τ ⟨l, hl⟩ vI - vI =
        s ((((ψ ⟨l, hl⟩ : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (p vI)) - p vI) := by
      rw [hdiff, map_sub]
    refine Submodule.mem_map.2 ⟨s ((((ψ ⟨l, hl⟩ : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (p vI)) - p vI), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · show (s ((((ψ ⟨l, hl⟩ : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (p vI)) - p vI) : W) = ρ l v - v
      rw [← hdiff']
      rfl
  have hIle : I ≤ S.map I.subtype := hIL.trans (Submodule.span_le.2 hgen)
  have hmemS : ∀ v : I, v ∈ S := by
    intro v
    obtain ⟨y, hyS, hyv⟩ := Submodule.mem_map.1 (hIle v.2)
    have hyv' : y = v := Subtype.ext hyv
    rwa [hyv'] at hyS
  intro a b hab
  have hmem : a - b ∈ S := hmemS (a - b)
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hmem
  have hpab : p (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hx0 : x = 0 := by
    have h1 : p (a - b) = x := by rw [← hx]; exact hs_p x
    rw [h1] at hpab
    exact hpab
  have hzero : a - b = 0 := by
    rw [← hx, hx0, map_zero]
  exact sub_eq_zero.1 hzero

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
