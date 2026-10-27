module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13R

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem Zs_comm {a b : G} (ha : a ∈ c.Zs) (hb : b ∈ c.Zs) : a * b = b * a :=
  c.Zs_comm_Qs ha (c.Zs_le_Qs hb)

theorem card_Zs' : Nat.card ↥c.Zs = 4 := c.h.card_Zs c.hα

@[expose] def Cprime {R : Subgroup G} (hRN : R ≤ c.N1) (x : G) : Subgroup G where
  carrier := {r | r ∈ R ∧ r * x * r⁻¹ * x⁻¹ ∈ c.Zs}
  mul_mem' := by
    rintro r r' ⟨hr, hrx⟩ ⟨hr', hr'x⟩
    refine ⟨mul_mem hr hr', ?_⟩
    have hc : r * (r' * x * r'⁻¹ * x⁻¹) = (r' * x * r'⁻¹ * x⁻¹) * r := c.Zs_comm_N1 hr'x (hRN hr)
    have e : r * r' * x * (r * r')⁻¹ * x⁻¹ =
        (r * (r' * x * r'⁻¹ * x⁻¹) * r⁻¹) * (r * x * r⁻¹ * x⁻¹) := by group
    rw [e, hc]
    have : (r' * x * r'⁻¹ * x⁻¹) * r * r⁻¹ = r' * x * r'⁻¹ * x⁻¹ := by group
    rw [this]
    exact mul_mem hr'x hrx
  one_mem' := ⟨R.one_mem, by simp⟩
  inv_mem' := by
    rintro r ⟨hr, hrx⟩
    refine ⟨inv_mem hr, ?_⟩
    have hc : r * (r * x * r⁻¹ * x⁻¹) = (r * x * r⁻¹ * x⁻¹) * r := c.Zs_comm_N1 hrx (hRN hr)
    have e : r⁻¹ * x * r⁻¹⁻¹ * x⁻¹ = r⁻¹ * (r * x * r⁻¹ * x⁻¹)⁻¹ * r := by group
    rw [e]
    have : r⁻¹ * (r * x * r⁻¹ * x⁻¹)⁻¹ * r = (r * x * r⁻¹ * x⁻¹)⁻¹ := by
      have h2 : r⁻¹ * (r * x * r⁻¹ * x⁻¹)⁻¹ * r = (r⁻¹ * (r * x * r⁻¹ * x⁻¹) * r)⁻¹ := by group
      rw [h2]
      congr 1
      calc r⁻¹ * (r * x * r⁻¹ * x⁻¹) * r = r⁻¹ * ((r * x * r⁻¹ * x⁻¹) * r) := by group
        _ = r⁻¹ * (r * (r * x * r⁻¹ * x⁻¹)) := by rw [hc]
        _ = r * x * r⁻¹ * x⁻¹ := by group
    rw [this]
    exact inv_mem hrx

theorem Cprime_le {R : Subgroup G} (hRN : R ≤ c.N1) (x : G) : c.Cprime hRN x ≤ R :=
  fun _ hr => hr.1

@[expose] noncomputable def cmtHom {R : Subgroup G} (hRN : R ≤ c.N1) (x : G) :
    ↥(c.Cprime hRN x) →* ↥c.Zs where
  toFun r := ⟨r * x * (r : G)⁻¹ * x⁻¹, r.2.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' r r' := by
    apply Subtype.ext
    obtain ⟨hr, hrx⟩ := r.2
    obtain ⟨hr', hr'x⟩ := r'.2
    have hc : (r : G) * (r' * x * (r' : G)⁻¹ * x⁻¹) = (r' * x * (r' : G)⁻¹ * x⁻¹) * r :=
      c.Zs_comm_N1 hr'x (hRN hr)
    show (r : G) * r' * x * ((r : G) * r')⁻¹ * x⁻¹ =
      ((r : G) * x * (r : G)⁻¹ * x⁻¹) * ((r' : G) * x * (r' : G)⁻¹ * x⁻¹)
    have e : (r : G) * r' * x * ((r : G) * r')⁻¹ * x⁻¹ =
        ((r : G) * (r' * x * (r' : G)⁻¹ * x⁻¹) * (r : G)⁻¹) * ((r : G) * x * (r : G)⁻¹ * x⁻¹) := by
      group
    rw [e, hc]
    have h2 : (r' * x * (r' : G)⁻¹ * x⁻¹) * (r : G) * (r : G)⁻¹ = r' * x * (r' : G)⁻¹ * x⁻¹ := by
      group
    rw [h2]
    exact c.Zs_comm hr'x hrx

theorem card_cent_Rhat_le {R : Subgroup G} (hRN : R ≤ c.N1) (hZR : c.Zs ≤ R)
    (hKR : R ⊓ c.KR ≤ c.Zs) {x : G} (hx : x ∈ R) :
    Nat.card ↥(c.Rhat R ⊓ centralizer
        ({c.rho ⟨x, hRN hx⟩} : Set (MulAut ↥E × MulAut ↥E))) ≤
      Nat.card ↥(R ⊓ centralizer ({x} : Set G)) := by
  classical
  have hC'N : c.Cprime hRN x ≤ c.N1 := (c.Cprime_le hRN x).trans hRN
  let ρ' : ↥(c.Cprime hRN x) →* MulAut ↥E × MulAut ↥E :=
    c.rho.comp (Subgroup.inclusion hC'N)
  have hZC : ∀ a ∈ c.Zs, a ∈ c.Cprime hRN x := by
    intro a ha
    refine ⟨hZR ha, ?_⟩
    have : x * a = a * x := c.Zs_comm_N1 ha (hRN hx)
    have e : a * x * a⁻¹ * x⁻¹ = 1 := by rw [← this]; group
    rw [e]; exact c.Zs.one_mem
  have hk4 : 4 ≤ Nat.card ρ'.ker := by
    let f : ↥c.Zs → ↥ρ'.ker := fun a =>
      ⟨⟨a, hZC a a.2⟩, by
        rw [MonoidHom.mem_ker]
        exact c.rho_Zs a.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun u : ↥ρ'.ker => ((u : ↥(c.Cprime hRN x)) : G)) hab
    have := Nat.card_le_card_of_injective f hf
    rw [c.card_Zs'] at this
    exact this
  have hmul : Nat.card ρ'.ker * Nat.card ρ'.range = Nat.card ↥(c.Cprime hRN x) :=
    Subgroup.card_ker_mul_card_range ρ'
  have hrange : Nat.card ↥(c.Rhat R ⊓ centralizer
        ({c.rho ⟨x, hRN hx⟩} : Set (MulAut ↥E × MulAut ↥E))) ≤ Nat.card ρ'.range := by
    refine Subgroup.card_le_of_le ?_
    rintro p ⟨hp, hpc⟩
    obtain ⟨r, hrR, rfl⟩ := c.mem_Rhat.1 hp
    have hcomm : c.rho r * c.rho ⟨x, hRN hx⟩ = c.rho ⟨x, hRN hx⟩ * c.rho r :=
      mem_centralizer_singleton_iff.1 hpc
    have hrx : (r : G) * x * (r : G)⁻¹ * x⁻¹ ∈ c.N1 :=
      mul_mem (mul_mem (mul_mem r.2 (hRN hx)) (inv_mem r.2)) (inv_mem (hRN hx))
    have hρ1 : c.rho ⟨(r : G) * x * (r : G)⁻¹ * x⁻¹, hrx⟩ = 1 := by
      have e : (⟨(r : G) * x * (r : G)⁻¹ * x⁻¹, hrx⟩ : ↥c.N1) =
          r * ⟨x, hRN hx⟩ * r⁻¹ * ⟨x, hRN hx⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hrxR : (r : G) * x * (r : G)⁻¹ * x⁻¹ ∈ R :=
      mul_mem (mul_mem (mul_mem hrR hx) (inv_mem hrR)) (inv_mem hx)
    have hZ : (r : G) * x * (r : G)⁻¹ * x⁻¹ ∈ c.Zs :=
      hKR ⟨hrxR, c.mem_KR.2 ⟨hrx, hρ1⟩⟩
    exact ⟨⟨(r : G), hrR, hZ⟩, rfl⟩
  have hj : Nat.card ↥(c.Cprime hRN x) ≤ 4 * Nat.card ↥(R ⊓ centralizer ({x} : Set G)) := by
    let j := c.cmtHom hRN x
    have h1 := Subgroup.card_ker_mul_card_range j
    have h2 : Nat.card j.range ≤ 4 := by
      have := Nat.card_le_card_of_injective (Subtype.val : j.range → ↥c.Zs)
        Subtype.val_injective
      rwa [c.card_Zs'] at this
    have h3 : Nat.card j.ker ≤ Nat.card ↥(R ⊓ centralizer ({x} : Set G)) := by
      have hmem : ∀ r : j.ker, (r : ↥(c.Cprime hRN x)).1 ∈ R ⊓ centralizer ({x} : Set G) := by
        intro r
        refine ⟨r.1.2.1, mem_centralizer_singleton_iff.2 ?_⟩
        have h0 : j r.1 = 1 := r.2
        have h00 : (r.1 : G) * x * (r.1 : G)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h0
        exact cmt_eq_one_iff.1 h00
      refine Nat.card_le_card_of_injective (fun r => ⟨(r : ↥(c.Cprime hRN x)).1, hmem r⟩) ?_
      intro a b hab
      have h5 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h5)
    calc Nat.card ↥(c.Cprime hRN x) = Nat.card j.ker * Nat.card j.range := h1.symm
      _ ≤ Nat.card ↥(R ⊓ centralizer ({x} : Set G)) * 4 := Nat.mul_le_mul h3 h2
      _ = 4 * Nat.card ↥(R ⊓ centralizer ({x} : Set G)) := by ring
  have h4 : 4 * Nat.card ↥(c.Rhat R ⊓ centralizer
      ({c.rho ⟨x, hRN hx⟩} : Set (MulAut ↥E × MulAut ↥E))) ≤
      4 * Nat.card ↥(R ⊓ centralizer ({x} : Set G)) :=
    calc 4 * _ ≤ 4 * Nat.card ρ'.range := Nat.mul_le_mul_left 4 hrange
      _ ≤ Nat.card ρ'.ker * Nat.card ρ'.range := Nat.mul_le_mul_right _ hk4
      _ = Nat.card ↥(c.Cprime hRN x) := hmul
      _ ≤ _ := hj
  omega

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
