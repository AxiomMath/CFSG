module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf58Shapes
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Inj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf60SlotGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

namespace TwinDisc

namespace E64

@[expose] def E64AutModel : Prop :=
  Subgroup.center ↥e64Sub = ⊥ ∧
    ∀ (θ : MulAut ↥e64Sub) {α : Finset (Fin 7)}, α ∈ e64Sets → ∀ (h : α.card = 4),
      (∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h true → θ x = x) →
      (∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h false → θ x = x) →
        ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub,
          (∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), (y : AEQ 7) ∈ memBar α' h' b) →
            θ y = c * y * c⁻¹


section Gen

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem aeIdentOn_toHom {n : ℕ} {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AEQ n)}
    (hgen : pSpan Φ = ⊤) (I : AEIdentOn Φ n 𝒜 H) :
    ∃ f : X →* AEQ n, f.range = H ∧ f.ker ≤ Subgroup.center X ∧
      (∀ x : X, f x = I.φ ⟨x, hgen ▸ Subgroup.mem_top x⟩) ∧
      ∀ L ∈ Φ, (L.subgroupOf (pSpan Φ)).map I.φ = L.map f := by
  have hmem : ∀ x : X, x ∈ pSpan Φ := fun x => hgen ▸ Subgroup.mem_top x
  let ε : X →* ↥(pSpan Φ) :=
    { toFun := fun x => ⟨x, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hεinj : Function.Injective ε := fun x y h => congrArg Subtype.val h
  have hεsurj : Function.Surjective ε := fun z => ⟨z.1, Subtype.ext rfl⟩
  refine ⟨I.φ.comp ε, ?_, ?_, fun x => rfl, fun L hL => ?_⟩
  · refine Eq.trans ?_ I.range_eq
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ε x, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := hεsurj z
      exact ⟨x, rfl⟩
  · intro x hx
    have hx' : ε x ∈ I.φ.ker := hx
    have hc := I.ker_le hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    exact hεinj (by rw [map_mul, map_mul]; exact hc (ε g))
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.1, Subgroup.mem_subgroupOf.mp hz, by
        show I.φ (ε z.1) = I.φ z
        rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ε x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem exists_induced_aut' {G : Type} [Group G] (f : X →* G) (hf : Function.Surjective f)
    (hNc : f.ker ≤ Subgroup.center X) (hZ : Subgroup.center G = ⊥) (α : MulAut X) :
    ∃ β : MulAut G, ∀ x : X, β (f x) = f (α x) := by
  have hle : f.ker.map α.toMonoidHom ≤ f.ker := by
    rintro _ ⟨n, hn, rfl⟩
    have hcen : α n ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.mp (hNc hn) (α.symm g)
      calc g * α n = α (α.symm g * n) := by simp
        _ = α (n * α.symm g) := by rw [h1]
        _ = α n * g := by simp
    have hc2 : f (α n) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g'
      obtain ⟨g, rfl⟩ := hf g'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen g]
    rw [hZ, Subgroup.mem_bot] at hc2
    exact hc2
  have heq : f.ker.map α.toMonoidHom = f.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective α.injective])
  have heq' : f.ker.map (α : X →* X) = f.ker := heq
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  refine ⟨e.symm.trans ((QuotientGroup.congr f.ker f.ker α heq').trans e), fun x => ?_⟩
  have h1 : e.symm (f x) = (x : X ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 := QuotientGroup.congr_mk f.ker f.ker α heq' x
  calc (e.symm.trans ((QuotientGroup.congr f.ker f.ker α heq').trans e)) (f x)
      = e (QuotientGroup.congr f.ker f.ker α heq' (e.symm (f x))) := rfl
    _ = e (QuotientGroup.congr f.ker f.ker α heq' (x : X ⧸ f.ker)) := by rw [h1]
    _ = e (((α x : X)) : X ⧸ f.ker) := by rw [h2]
    _ = f (α x) := rfl

end Gen

theorem sqTriOn_of_e64 (hmodel : E64AutModel) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hS : Q8Section X Φ)
    (I : AEIdentOn Φ 7 e64Sets e64Sub) : SqTriOn X Φ := by
  intro A B x₀ hA hB hxA hxB α hα4 hperm hfixA hfixB
  left
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  obtain ⟨f, hrange, hker, hfx, hmap⟩ := aeIdentOn_toHom hgen I
  have hlab : ∀ L ∈ Φ, ∃ α ∈ e64Sets, ∃ (h : α.card = 4) (b : Bool), L.map f = memBar α h b := by
    intro L hL
    obtain ⟨α, hα, h, b, hl⟩ := I.label L hL
    exact ⟨α, hα, h, b, (hmap L hL).symm.trans hl⟩
  have h2 : ∀ L ∈ Φ, IsPGroup 2 ↥L :=
    members_two_phi (by norm_num) hS I.φ I.ker_le (fun L hL => by
      obtain ⟨α, -, h, b, hl⟩ := I.label L hL
      exact ⟨α, h, b, hl⟩)
  have h8 : ∀ L ∈ Φ, Nat.card ↥L = 8 := by
    intro L hL
    obtain ⟨e⟩ := hS.q8 L hL L (TL4.Vtx.isSylow2In_self (h2 L hL))
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hN2 : IsPGroup 2 f.ker :=
    (TL4.Vtx.isPGroup_center_of_oddFree hS.oddFree).to_le hker
  have hz : ∀ K ∈ Φ, ∀ α ∈ e64Sets, ∀ (h : α.card = 4) (b : Bool), K.map f = memBar α h b →
      ∀ z : X, IsUniqueInvolution K z → f z = zBar α h := by
    intro K hK α hα h b hl z hzK
    have hlK : (K.subgroupOf (pSpan Φ)).map I.φ = memBar α h b := (hmap K hK).trans hl
    rw [hfx]
    exact phi_map_eq_zBar I.φ (by norm_num) hK (h8 K hK) hlK hzK
  have hno : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → z ∉ f.ker := by
    intro K hK z hzK hzk
    obtain ⟨α, hα, h, b, hl⟩ := hlab K hK
    have h1 := hz K hK α hα h b hl z hzK
    rw [MonoidHom.mem_ker] at hzk
    exact zBar_ne_one (by norm_num) α h (h1.symm.trans hzk)
  obtain ⟨hker0, hinj⟩ := inj_members_of_twoGroupKernel hS h2 f hN2 hno
  have hmem : ∀ x, f x ∈ e64Sub := fun x => hrange ▸ ⟨x, rfl⟩
  let f₀ : X →* ↥e64Sub := f.codRestrict e64Sub hmem
  have hf₀s : Function.Surjective f₀ := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hf₀c : f₀.ker ≤ Subgroup.center X := fun x hx =>
    hker (by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx)
  obtain ⟨θ, hθ⟩ := exists_induced_aut' f₀ hf₀s hf₀c hmodel.1 α
  obtain ⟨hBΦ, hBA, -⟩ := hB
  obtain ⟨α₁, hα₁, h₁, b₁, hlA⟩ := hlab A hA
  obtain ⟨α₂, hα₂, h₂, b₂, hlB⟩ := hlab B hBΦ
  have hzA := hz A hA α₁ hα₁ h₁ b₁ hlA x₀ hxA
  have hzB := hz B hBΦ α₂ hα₂ h₂ b₂ hlB x₀ hxB
  have hαeq : α₁ = α₂ := AE.eq_of_zBar_eq (by norm_num) (hzA.symm.trans hzB)
  subst hαeq
  have hbne : b₁ ≠ b₂ := by
    intro hb
    subst hb
    exact hBA (hinj B hBΦ A hA (hlB.trans hlA.symm))
  have fixOf : ∀ {L : Subgroup X}, (∀ a ∈ L, α a = a) →
      ∀ x : ↥e64Sub, (x : AEQ 7) ∈ L.map f → θ x = x := by
    intro L hL x hx
    obtain ⟨a, ha, hax⟩ := hx
    have hx' : x = f₀ a := Subtype.ext hax.symm
    rw [hx', hθ a, hL a ha]
  have hfixA' := fixOf hfixA
  have hfixB' := fixOf hfixB
  have hcore : ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub,
      (∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), (y : AEQ 7) ∈ memBar α' h' b) →
        θ y = c * y * c⁻¹ := by
    cases b₁ <;> cases b₂
    · exact absurd rfl hbne
    · exact hmodel.2 θ hα₁ h₁ (fun x hx => hfixB' x (by rw [hlB]; exact hx))
        (fun x hx => hfixA' x (by rw [hlA]; exact hx))
    · exact hmodel.2 θ hα₁ h₁ (fun x hx => hfixA' x (by rw [hlA]; exact hx))
        (fun x hx => hfixB' x (by rw [hlB]; exact hx))
    · exact absurd rfl hbne
  obtain ⟨c, hcc, hconj⟩ := hcore
  have hθeq : ∀ y : ↥e64Sub, θ y = c * y * c⁻¹ := by
    have hhom : θ.toMonoidHom.comp f₀ = (MulAut.conj c).toMonoidHom.comp f₀ := by
      have hle : omegaGen Φ ≤ MonoidHom.eqLocus (θ.toMonoidHom.comp f₀)
          ((MulAut.conj c).toMonoidHom.comp f₀) := by
        refine iSup₂_le fun L hL l hl => ?_
        obtain ⟨α', hα', h', b', hl'⟩ := hlab L hL
        have hfl : ((f₀ l : ↥e64Sub) : AEQ 7) ∈ memBar α' h' b' := by
          rw [← hl']
          exact ⟨l, hl, rfl⟩
        have h3 := hconj (f₀ l) ⟨α', hα', h', b', hfl⟩
        have h4 : (θ.toMonoidHom.comp f₀) l = ((MulAut.conj c).toMonoidHom.comp f₀) l := by
          simpa [MulAut.conj_apply] using h3
        exact h4
      rw [hS.gen] at hle
      refine MonoidHom.ext fun x => ?_
      exact hle (Subgroup.mem_top x)
    intro y
    obtain ⟨x, rfl⟩ := hf₀s y
    have := congrArg (fun g : X →* ↥e64Sub => g x) hhom
    simpa [MulAut.conj_apply] using this
  have hθ2 : ∀ y : ↥e64Sub, θ (θ y) = y := by
    intro y
    have hc1 : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    rw [hθeq, hθeq, hc1]
    calc c * (c * y * c) * c = (c * c) * y * (c * c) := by group
      _ = y := by rw [hcc]; group
  have hζf : ∀ x : X, f ((α * α) x) = f x := by
    intro x
    have : f₀ ((α * α) x) = f₀ x := by
      calc f₀ ((α * α) x) = f₀ (α (α x)) := rfl
        _ = θ (f₀ (α x)) := (hθ (α x)).symm
        _ = θ (θ (f₀ x)) := by rw [hθ x]
        _ = f₀ x := hθ2 _
    exact congrArg Subtype.val this
  have hperm2 : ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map (α * α).toMonoidHom = L' := by
    intro L hL
    obtain ⟨L₁, hL₁, hL₁e⟩ := hperm L hL
    obtain ⟨L₂, hL₂, hL₂e⟩ := hperm L₁ hL₁
    refine ⟨L₂, hL₂, ?_⟩
    rw [← hL₂e, ← hL₁e, Subgroup.map_map]
    rfl
  exact mulAut_eq_one_of_trivial_mod hS.gen f (α * α) hperm2 hζf hinj hker0

theorem sqTriShape_e64 (hmodel : E64AutModel) : SqTriShape shapeE64 := by
  intro X _ _ Φ hS _ hshape
  obtain ⟨I⟩ := hshape
  exact sqTriOn_of_e64 hmodel hS I

theorem discUZetaTriAt_e64_of_model {n : ℕ} (hmodel : E64AutModel) :
    DiscUZetaTriAt n shapeE64 :=
  discUZetaTriAt_of_sqTriShape (sqTriShape_e64 hmodel)

end E64

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
