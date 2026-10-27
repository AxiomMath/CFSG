module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFiveStep0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFiveExtract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerE1Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Diag

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

@[expose] def InnerD8Config.diagHom (c : InnerD8Config L t) : ↥c.L₁ →* G where
  toFun l := (l : G) * (t * l * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h : Commute (b : G) (t * a * t⁻¹) := c.pair.comm b b.2 a a.2
    simp only [Subgroup.coe_mul]
    calc (a : G) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h.eq]
      _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group

theorem InnerD8Config.diagHom_apply (c : InnerD8Config L t) (l : ↥c.L₁) :
    c.diagHom l = (l : G) * (t * l * t⁻¹) := rfl

theorem InnerD8Config.diag_mem_commutator (c : InnerD8Config L t)
    (htL : t ∈ centralizer (L : Set G)) (hin : centralizer ({t} : Set G) = L ⊔ zpowers t)
    {l : G} (hl : l ∈ c.L₁) :
    l * (t * l * t⁻¹) ∈ ⁅L ⊓ centralizer ({c.u} : Set G), L ⊓ centralizer ({c.u} : Set G)⁆ := by
  have ht : t * t = 1 := c.pair.t_sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 htL a ha
  set D : Subgroup G := c.diagHom.range with hD
  have hperf : Group.IsPerfect ↥c.L₁ := by
    have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.ofSurjective (f := c.eL₁.symm.toMonoidHom) c.eL₁.symm.surjective
  have hDD : ⁅D, D⁆ = D := by
    have h2 : (⁅(⊤ : Subgroup ↥c.L₁), ⊤⁆ : Subgroup ↥c.L₁) = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [hD, MonoidHom.range_eq_map, ← Subgroup.map_commutator, h2]
  have hDt : D ≤ L ⊔ zpowers t := by
    rintro _ ⟨k, rfl⟩
    rw [← hin, mem_centralizer_singleton_iff, InnerD8Config.diagHom_apply]
    have hk : Commute (k : G) (t * k * t⁻¹) := c.pair.comm k k.2 k k.2
    have h1 : t * ((k : G) * (t * k * t⁻¹)) * t⁻¹ = (k : G) * (t * k * t⁻¹) := by
      calc t * ((k : G) * (t * k * t⁻¹)) * t⁻¹
          = (t * k * t⁻¹) * ((t * t) * k * (t * t)⁻¹) := by group
        _ = (t * k * t⁻¹) * k := by rw [ht]; group
        _ = (k : G) * (t * k * t⁻¹) := hk.eq.symm
    have h2 : t * ((k : G) * (t * k * t⁻¹)) = ((k : G) * (t * k * t⁻¹)) * t :=
      mul_inv_eq_iff_eq_mul.1 h1
    first | exact h2 | exact h2.symm
  have hDu : D ≤ centralizer ({c.u} : Set G) := by
    rintro _ ⟨k, rfl⟩
    rw [InnerD8Config.diagHom_apply]
    exact mul_mem (c.pair.K_le k.2)
      (mul_mem (mul_mem c.pair.t_mem (c.pair.K_le k.2)) (inv_mem c.pair.t_mem))
  have hDL : D ≤ L := by
    rw [← hDD]
    exact (Subgroup.commutator_mono hDt hDt).trans (commutator_sup_zpowers_le htL)
  have hmem : l * (t * l * t⁻¹) ∈ D := ⟨⟨l, hl⟩, rfl⟩
  rw [← hDD] at hmem
  exact Subgroup.commutator_mono (le_inf hDL hDu) (le_inf hDL hDu) hmem

end Diag

theorem exists_alt6_orderOf_eq_five : ∃ a : alternatingGroup (Fin 6), orderOf a = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, ?_⟩
  exact orderOf_eq_prime (by decide) (by decide)

section Assembly


theorem hsInnerB4_of_five (hC : CatE16)
    (h51 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsSporadic ↥L .HS →
      ∀ u ∈ L, orderOf u = 2 → Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 2880 →
      ∀ f ∈ ⁅L ⊓ centralizer ({u} : Set G), L ⊓ centralizer ({u} : Set G)⁆, orderOf f = 5 →
        FiveLocal51 L u f)
    (h53 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsSporadic ↥L .HS →
      FiveLocal53 L) :
    HSInnerB4 := by
  intro G _ _ L hS t htL ht2 hin S z n hf c hρ
  have e : FiveEnv c := ⟨hS.2.1, htL, ht2, hin, ⟨S, z, n, hf⟩, hρ⟩
  obtain ⟨a, ha⟩ := exists_alt6_orderOf_eq_five
  set f₀ : G := ((c.eL₁.symm a : ↥c.L₁) : G) with hf₀def
  have hf₀ : f₀ ∈ c.L₁ := (c.eL₁.symm a).2
  have h5 : orderOf f₀ = 5 := by
    rw [hf₀def, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  have ht2' : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hfh5 : orderOf (c.fhat f₀) = 5 := InnerD8ConfigC.orderOf_fhat (c := c) hf₀ h5
  have hfhD := c.toInnerD8Config.diag_mem_commutator htL hin hf₀
  have h51' : FiveLocal51 L c.u (c.fhat f₀) :=
    h51 G L hS.2.1 c.u c.u_mem c.u_ord c.card_centralizer_u (c.fhat f₀) hfhD hfh5
  obtain ⟨A, hA, hdec⟩ := InnerD8ConfigC.FiveA0_of_51 (c := c) (f₀ := f₀) h51'
  have H53 := h53 G L hS.2.1
  have hAN := InnerD8ConfigC.centralizer_N₅_ge_A0 (c := c) e autA6Five_prop H53 hf₀ h5 hA
  have hCt : centralizer ({t} : Set G) ⊓ centralizer (c.N₅ f₀ : Set G) ≤ c.N₅ f₀ ⊔ A := by
    rw [InnerD8ConfigC.centralizer_t_inf_centralizer_N₅ (c := c) e autA6Five_prop H53 hf₀ h5 h51',
      hdec]
    exact sup_le_sup_right (zpowers_le.2 (InnerD8ConfigC.fhat_mem_N₅ (c := c) (f₀ := f₀))) A
  have hN25 : Nat.card (c.N₅ f₀) = 25 := InnerD8ConfigC.card_N₅ (c := c) hf₀ h5
  have hCu : Nat.card ↥(centralizer ({c.u} : Set G) ⊓ centralizer (c.N₅ f₀ : Set G)) =
      16 * Nat.card (c.N₅ f₀) := by
    rw [hN25]
    exact InnerD8ConfigC.card_P_inf_centralizer_N₅ (c := c) e autA6Five_prop hf₀ h5
  have hNodd : Odd (Nat.card (c.N₅ f₀)) := by rw [hN25]; decide
  have hNab : ∀ x ∈ c.N₅ f₀, ∀ y ∈ c.N₅ f₀, x * y = y * x := fun x hx y hy =>
    InnerD8ConfigC.N₅_comm (c := c) hf₀ hx hy
  have htN : ∀ n ∈ c.N₅ f₀, t * n * t⁻¹ ∈ c.N₅ f₀ := fun n hn =>
    (mem_normalizer_iff.1 (InnerD8ConfigC.t_mem_normalizer_N₅ (c := c) (f₀ := f₀)) n).1 hn
  have hCtop : centralizer (c.N₅ f₀ : Set G) ≠ ⊤ := by
    intro htop
    have htC : t ∈ centralizer (c.N₅ f₀ : Set G) := htop ▸ mem_top t
    have h1 : f₀ * t = t * f₀ :=
      mem_centralizer_iff.1 htC f₀ (InnerD8ConfigC.f₀_mem_N₅ (c := c) (f₀ := f₀))
    have h2 : c.ftw f₀ = f₀ := by
      show t * f₀ * t⁻¹ = f₀
      rw [← h1, mul_inv_cancel_right]
    have h3 : f₀ ∈ zpowers f₀ ⊓ zpowers (c.ftw f₀) :=
      ⟨mem_zpowers _, by rw [h2]; exact mem_zpowers _⟩
    rw [InnerD8ConfigC.zpowers_inf_zpowers_ftw (c := c) hf₀, mem_bot] at h3
    rw [h3, orderOf_one] at h5
    exact absurd h5 (by decide)
  have hAt : ∀ x ∈ A, t * x = x * t := fun x hx =>
    (mem_centralizer_iff.1 htL x (hA.le hx).1).symm
  have hmod := commute_mod_of_X5 hC hS.1.kProper (c.N₅ f₀) hNab hNodd hCtop t ht2' htN A
    hA.iso hAN hAt hCt c.u hA.u_mem c.u_ord hCu
  exact c.toInnerD8Config.exists_pgl29_involution hρ
    (fun a ha => exists_outer_involution_fix_five a ha) f₀ hf₀ h5 hmod

end Assembly

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
