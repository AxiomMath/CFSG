module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.A6InA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Elem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.OddCore

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std

theorem eq_on_of_comm_alt6 {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) {G : Type} [Group G] {ρ : G →* MulAut V} (X : Subgroup G)
    (e : X ≃* alternatingGroup (Fin 6)) (U Uo : Subgroup V) (hU : Nat.card U = 16)
    (hmem : ∀ x ∈ X, ∀ v ∈ U, ρ x v ∈ U) (hfix : ∀ v : V, (∀ x ∈ X, ρ x v = v) ↔ v ∈ Uo)
    (hinf : U ⊓ Uo = ⊥) (g : MulAut V) (hgU : ∀ u ∈ U, g u ∈ U) (hgU' : ∀ u ∈ U, g⁻¹ u ∈ U)
    (hg : ∀ x ∈ X, g * ρ x = ρ x * g) : ∀ u ∈ U, g u = u := by
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hU]; norm_num)
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
  have : IsSimpleGroup X := e.isSimpleGroup
  let ψ : X →* MulAut U := restrictAut (ρ.comp X.subtype) U (fun h u hu => hmem h h.2 u hu)
  have hψ : ∀ (x : X) (u : U), ((ψ x u : U) : V) = ρ x u := fun x u => rfl
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases ψ.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact hk
    · exfalso
      have h1 : ∀ u ∈ U, u ∈ Uo := by
        intro u hu
        refine (hfix u).1 fun x hx => ?_
        have hxk : (⟨x, hx⟩ : X) ∈ ψ.ker := by rw [hk]; exact mem_top _
        have := hψ ⟨x, hx⟩ ⟨u, hu⟩
        rw [MonoidHom.mem_ker.1 hxk] at this
        exact this.symm
      have h2 : U = ⊥ := eq_bot_iff.2 fun u hu => by
        have : u ∈ U ⊓ Uo := ⟨hu, h1 u hu⟩
        rwa [hinf] at this
      rw [h2, Subgroup.card_bot] at hU
      omega
  let A : Subgroup (MulAut U) := ψ.range
  let eA : A ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hinj).symm.trans e
  let g₁ : MulAut U :=
    { toFun := fun u => ⟨g u, hgU u u.2⟩
      invFun := fun u => ⟨g⁻¹ u, hgU' u u.2⟩
      left_inv := fun u => Subtype.ext (by
        show g⁻¹ (g u) = u
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply])
      right_inv := fun u => Subtype.ext (by
        show g (g⁻¹ u) = u
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply])
      map_mul' := fun a b => Subtype.ext (map_mul g (a : V) (b : V)) }
  have hg₁ : ∀ a ∈ A, g₁ * a = a * g₁ := by
    rintro _ ⟨x, rfl⟩
    ext u
    show g ((ψ x u : U) : V) = ((ψ x (g₁ u) : U) : V)
    rw [hψ x u, hψ x (g₁ u)]
    show g (ρ x u) = ρ x (g u)
    exact congrArg (fun f : MulAut V => f (u : V)) (hg x x.2)
  have hc' : ∀ x y : U, x * y = y * x := fun x y => Subtype.ext (hc x y)
  have hs' : ∀ x : U, x * x = 1 := fun x => Subtype.ext (hs x)
  have h1 := eq_one_of_comm_alt6 hc' hs' hU A eA g₁ hg₁
  intro u hu
  have := congrArg (fun f : MulAut U => ((f ⟨u, hu⟩ : U) : V)) h1
  exact this

theorem Config.eq_one_of_comm {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] {ρ : G →* MulAut V}
    (c : Config ρ) (g : MulAut V) (hg : ∀ x ∈ c.C ⊔ c.D, g * ρ x = ρ x * g) : g = 1 := by
  have hgC : ∀ x ∈ c.C, g * ρ x = ρ x * g := fun x hx => hg x (mem_sup_left hx)
  have hgD : ∀ x ∈ c.D, g * ρ x = ρ x * g := fun x hx => hg x (mem_sup_right hx)
  have hpres : ∀ (X : Subgroup G) (U : Subgroup V), (∀ v : V, (∀ x ∈ X, ρ x v = v) ↔ v ∈ U) →
      (∀ x ∈ X, g * ρ x = ρ x * g) → (∀ u ∈ U, g u ∈ U) ∧ (∀ u ∈ U, g⁻¹ u ∈ U) := by
    intro X U hfix hgX
    have hcomm : ∀ x ∈ X, ∀ v : V, ρ x (g v) = g (ρ x v) := fun x hx v => by
      have := congrArg (fun f : MulAut V => f v) (hgX x hx)
      exact this.symm
    refine ⟨fun u hu => (hfix _).1 fun x hx => ?_, fun u hu => (hfix _).1 fun x hx => ?_⟩
    · rw [hcomm x hx, (hfix u).2 hu x hx]
    · have hu' := (hfix u).2 hu x hx
      apply g.injective
      have hgg : g (g⁻¹ u) = u := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      have : g (ρ x (g⁻¹ u)) = g (g⁻¹ u) := by
        rw [← hcomm x hx, hgg, hu']
      exact this
  obtain ⟨h1, h1'⟩ := hpres c.D c.U₁ c.D_fix hgD
  obtain ⟨h2, h2'⟩ := hpres c.C c.U₂ c.C_fix hgC
  have e1 := eq_on_of_comm_alt6 hc hs c.C c.eC c.U₁ c.U₂ c.card_U₁ c.C_mem c.C_fix c.inf_U g h1 h1'
    hgC
  have e2 := eq_on_of_comm_alt6 hc hs c.D c.eD c.U₂ c.U₁ c.card_U₂ c.D_mem c.D_fix
    (by rw [inf_comm]; exact c.inf_U) g h2 h2' hgD
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  obtain ⟨eP⟩ := sup_mulEquiv_prod (C := c.U₁) (D := c.U₂) (fun x _ y _ => hc x y) c.inf_U
  have htop : c.U₁ ⊔ c.U₂ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr eP.toEquiv, Nat.card_prod, c.card_U₁, c.card_U₂, hV]
  let F : Subgroup V :=
    { carrier := {v | g v = v}
      mul_mem' := fun {a b} ha hb => by
        show g (a * b) = a * b
        rw [map_mul, show g a = a from ha, show g b = b from hb]
      one_mem' := map_one g
      inv_mem' := fun {a} ha => by
        show g a⁻¹ = a⁻¹
        rw [map_inv, show g a = a from ha] }
  have hF : c.U₁ ⊔ c.U₂ ≤ F := sup_le (fun u hu => e1 u hu) (fun u hu => e2 u hu)
  ext v
  rw [MulAut.one_apply]
  have hv : v ∈ F := hF (htop ▸ mem_top v)
  exact hv

theorem Config.fusionOddCore_eq_bot {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    {ρ : G →* MulAut V} (hρ : Function.Injective ρ) (c : Config ρ) : fusionOddCore G = ⊥ :=
  c.fusionOddCore_eq_bot_of_cent hc hs hV hρ fun g hg => c.eq_one_of_comm hc hs hV g hg

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
