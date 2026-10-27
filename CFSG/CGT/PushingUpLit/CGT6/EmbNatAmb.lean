module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.BHS
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem isNatBy_of_isNatSectionBy {V X : Subgroup Γ} [V.Normal] (hV : IsElemAbelian 2 V)
    {S M : Type*} [Group S] [Group M] {act : S → M → M}
    (hfaith : ∀ s : S, (∀ m, act s m = m) → s = 1) (hfix : ∀ m : M, (∀ s, act s m = m) → m = 1)
    (h : @IsNatSectionBy ↥V (commGroupOfElemAbelian hV) S M _ _ act (autOn X V) (BHS6.commOn hV X) ⊥) :
    IsNatBy act X ⁅X, V⁆ ∧ (⁅X, V⁆ : Subgroup Γ) ⊓ Subgroup.centralizer (X : Set Γ) = ⊥ ∧
      X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup Γ) : Set Γ) ≤
        Subgroup.centralizer (V : Set Γ) := by
  classical
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := h
  have hXV : X ≤ Subgroup.normalizer (V : Set Γ) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  have hcomm : BHS6.commOn hV X = (⁅X, V⁆ : Subgroup Γ).subgroupOf V := commOn_eq hV hXV
  have hXVV : (⁅X, V⁆ : Subgroup Γ) ≤ V := commutator_le_of_le_normalizer hXV
  let ιe : ↥(BHS6.commOn hV X) ≃* ↥(⁅X, V⁆ : Subgroup Γ) :=
    (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hXVV)
  have hιe : ∀ p : ↥(BHS6.commOn hV X), ((ιe p : ↥(⁅X, V⁆ : Subgroup Γ)) : Γ) = ((p : ↥V) : Γ) :=
    fun p => rfl
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have : p ∈ β.ker := hp
    rw [hβk, Subgroup.bot_subgroupOf] at this
    exact this
  let ρ : ↥X →* ↥(autOn X V) := actOnRange V X hXV
  have hρs : Function.Surjective ρ := actOnRange_surjective V X hXV
  have hρk : ρ.ker = (X ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf X := ker_actOnRange V X hXV
  have hρapp : ∀ (x : ↥X) (p : ↥(BHS6.commOn hV X)),
      ((((ρ x : ↥(autOn X V)) : MulAut ↥V) ((p : ↥V)) : ↥V) : Γ) =
        (x : Γ) * ((p : ↥V) : Γ) * (x : Γ)⁻¹ := fun x p => actOn_apply_coe hXV x p
  have hconjmem : ∀ (x : ↥X) (p : ↥(BHS6.commOn hV X)),
      (((ρ x : ↥(autOn X V)) : MulAut ↥V) (p : ↥V)) ∈ BHS6.commOn hV X := by
    intro x p
    have h1 := (ρ x).2
    have hp : (p : ↥V) ∈ BHS6.commOn hV X := p.2
    unfold BHS6.commOn at hp ⊢
    let _ : CommGroup ↥V := commGroupOfElemAbelian hV
    exact G6.apply_mem_commV (fun y hy => by
      have : (ρ x).1 * y * ((ρ x).1)⁻¹ ∈ autOn X V := by
        exact (autOn X V).mul_mem ((autOn X V).mul_mem h1 hy) ((autOn X V).inv_mem h1)
      exact this) hp
  have hfixed : ∀ (x : ↥X) (p : ↥(BHS6.commOn hV X)),
      ((x : Γ) * ((p : ↥V) : Γ) * (x : Γ)⁻¹ = ((p : ↥V) : Γ)) → act (θ (ρ x)) (β p) = β p := by
    intro x p hxp
    have hpp : (((ρ x : ↥(autOn X V)) : MulAut ↥V) (p : ↥V)) = (p : ↥V) :=
      Subtype.ext (by rw [hρapp]; exact hxp)
    have := hβe (ρ x) p (by rw [hpp]; exact p.2)
    rw [← this]
    congr 1
    exact Subtype.ext hpp
  have hker : X ⊓ Subgroup.centralizer (V : Set Γ) = X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup Γ) : Set Γ) := by
    refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le hXVV)) ?_
    rintro x ⟨hxX, hxC⟩
    have hall : ∀ m : M, act (θ (ρ ⟨x, hxX⟩)) m = m := by
      intro m
      obtain ⟨p, rfl⟩ := hβs m
      refine hfixed ⟨x, hxX⟩ p ?_
      have hpW : ((p : ↥V) : Γ) ∈ (⁅X, V⁆ : Subgroup Γ) := (hιe p) ▸ (ιe p).2
      have := Subgroup.mem_centralizer_iff.mp hxC _ hpW
      calc x * ((p : ↥V) : Γ) * x⁻¹ = ((p : ↥V) : Γ) * x * x⁻¹ := by rw [← this]
        _ = ((p : ↥V) : Γ) := by group
    have h1 : θ (ρ ⟨x, hxX⟩) = 1 := hfaith _ hall
    have h2 : ρ ⟨x, hxX⟩ = 1 := θ.injective (by rw [h1, map_one])
    have h3 : (⟨x, hxX⟩ : ↥X) ∈ ρ.ker := h2
    rw [hρk] at h3
    exact ⟨hxX, (Subgroup.mem_inf.mp h3).2⟩
  have hCfree : (⁅X, V⁆ : Subgroup Γ) ⊓ Subgroup.centralizer (X : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwW, hwC⟩
    obtain ⟨p, hp⟩ := ιe.surjective ⟨w, hwW⟩
    have hpw : ((p : ↥V) : Γ) = w := by rw [← hιe p, hp]
    have hall : ∀ s : S, act s (β p) = β p := by
      intro s
      obtain ⟨y, rfl⟩ := θ.surjective s
      obtain ⟨x, rfl⟩ := hρs y
      refine hfixed x p ?_
      have := Subgroup.mem_centralizer_iff.mp hwC (x : Γ) x.2
      rw [hpw]
      calc (x : Γ) * w * (x : Γ)⁻¹ = w * (x : Γ) * (x : Γ)⁻¹ := by rw [← this]
        _ = w := by group
    have h1 : β p = 1 := hfix _ hall
    have h2 : p = 1 := hβinj (by rw [h1, map_one])
    rw [Subgroup.mem_bot, ← hpw, h2]
    rfl
  refine ⟨⟨θ.toMonoidHom.comp ρ, β.comp ιe.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩, hCfree,
    fun x hx => (hker.ge hx).2⟩
  · exact θ.surjective.comp hρs
  · rw [← hker, ← hρk]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro hx
      exact θ.injective (by rw [hx, map_one])
    · intro hx
      rw [hx, map_one]
  · exact hβs.comp ιe.symm.surjective
  · rw [hCfree, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (hβinj.comp ιe.symm.injective)
  · intro e w hw
    obtain ⟨p, rfl⟩ := ιe.surjective w
    have hcp : (ρ e : MulAut ↥V) (p : ↥V) ∈ BHS6.commOn hV X := hconjmem e p
    have hιp : ιe ⟨(ρ e : MulAut ↥V) (p : ↥V), hcp⟩ =
        ⟨(e : Γ) * ((ιe p : ↥(⁅X, V⁆ : Subgroup Γ)) : Γ) * (e : Γ)⁻¹, hw⟩ := by
      apply Subtype.ext
      rw [hιe]
      exact hρapp e p
    have := hβe (ρ e) p hcp
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [← hιp, MulEquiv.symm_apply_apply]
    exact this

end CFSG.CGT.PushingUpLit.CGT6
