module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx22

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Dsub {G : Type} [Group G] (S U : Subgroup G) (h : G) : Subgroup G :=
  Wsub S U ⊓ centralizer ({h} : Set G)

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem A_le_gen (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hVx : Vof S K₁ W₂ = zpowers x) :
    Aof S K₁ W₂ h ≤ zpowers x ⊔ zpowers (h⁻¹ * x * h) := by
  have hVh : conjugate (Vof S K₁ W₂) h ≤ zpowers (h⁻¹ * x * h) := by
    intro a₂ ha₂
    have h1 : h * a₂ * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 ha₂
    rw [hVx] at h1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    have h2 := conj_zpow (a := h⁻¹) (b := x) (i := i)
    rw [inv_inv] at h2
    rw [h2, hi]
    group
  apply sup_le
  · rw [← hVx]; exact le_sup_left
  · exact hVh.trans le_sup_right

theorem mem_A_of_fix (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hVx : Vof S K₁ W₂ = zpowers x) {g : G}
    (hgS : g ∈ S) (hgx : x * g = g * x) (hgx' : (h⁻¹ * x * h) * g = g * (h⁻¹ * x * h)) :
    g ∈ Aof S K₁ W₂ h := by
  rw [← hs.cent_eq hII hq hrec]
  refine Subgroup.mem_inf.2 ⟨hgS, Subgroup.mem_centralizer_iff.2 (fun a ha => ?_)⟩
  have hC : zpowers x ⊔ zpowers (h⁻¹ * x * h) ≤ centralizer ({g} : Set G) := by
    apply sup_le
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]; exact hgx
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]; exact hgx'
  have h1 := hC (hs.A_le_gen hII hq hrec hVx ha)
  exact Subgroup.mem_centralizer_singleton_iff.1 h1

theorem theta_surj (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ b ∈ Aof S K₁ W₂ h, ∃ a ∈ Aof S K₁ W₂ h, (h⁻¹ * a * h) * a⁻¹ = b := by
  intro b hb
  let θ : ↥(Aof S K₁ W₂ h) → ↥(Aof S K₁ W₂ h) := fun a =>
    ⟨(h⁻¹ * (a : G) * h) * (a : G)⁻¹,
      mul_mem ((hs.A_conj hII hq hrec hk a.2).2) (inv_mem a.2)⟩
  have hinj : Function.Injective θ := by
    intro a b hab
    have h1 : (h⁻¹ * (a : G) * h) * (a : G)⁻¹ = (h⁻¹ * (b : G) * h) * (b : G)⁻¹ :=
      congrArg Subtype.val hab
    have hpA := (hs.A_conj hII hq hrec hk a.2).2
    have hqA := (hs.A_conj hII hq hrec hk b.2).2
    have hbaA : (b : G)⁻¹ * (a : G) ∈ Aof S K₁ W₂ h := mul_mem (inv_mem b.2) a.2
    have hp : h⁻¹ * (a : G) * h = (h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G)) := by
      calc h⁻¹ * (a : G) * h = ((h⁻¹ * (a : G) * h) * (a : G)⁻¹) * (a : G) := by group
        _ = ((h⁻¹ * (b : G) * h) * (b : G)⁻¹) * (a : G) := by rw [h1]
        _ = (h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G)) := by group
    have hc1 : (h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G)) =
        ((b : G)⁻¹ * (a : G)) * (h⁻¹ * (b : G) * h) := hs.A_comm hII hq hrec _ hqA _ hbaA
    have hc2 : (b : G)⁻¹ * (a : G) = (a : G) * (b : G)⁻¹ := by
      have := hs.A_comm hII hq hrec _ (inv_mem b.2) _ a.2
      exact this
    have hn : h⁻¹ * ((a : G) * (b : G)⁻¹) * h = (a : G) * (b : G)⁻¹ := by
      calc h⁻¹ * ((a : G) * (b : G)⁻¹) * h
          = (h⁻¹ * (a : G) * h) * (h⁻¹ * (b : G) * h)⁻¹ := by group
        _ = ((h⁻¹ * (b : G) * h) * ((b : G)⁻¹ * (a : G))) * (h⁻¹ * (b : G) * h)⁻¹ := by rw [hp]
        _ = (((b : G)⁻¹ * (a : G)) * (h⁻¹ * (b : G) * h)) * (h⁻¹ * (b : G) * h)⁻¹ := by rw [hc1]
        _ = (b : G)⁻¹ * (a : G) := by group
        _ = (a : G) * (b : G)⁻¹ := hc2
    have hn1 := hs.A_fixed_trivial hII hq hrec hk (mul_mem a.2 (inv_mem b.2)) hn
    exact Subtype.ext (mul_inv_eq_one.1 hn1)
  obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.1 hinj ⟨b, hb⟩
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

theorem mem_Dsub_iff {d : G} : d ∈ Dsub S U h ↔ d ∈ Wsub S U ∧ d * h = h * d := by
  unfold Dsub
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem D_inf_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Aof S K₁ W₂ h ⊓ Dsub S U h = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have hd := (mem_Dsub_iff).1 ha.2
  have h1 : h⁻¹ * a * h = a := by
    have e : h⁻¹ * a * h = h⁻¹ * (a * h) := by group
    rw [e, hd.2]; group
  exact hs.A_fixed_trivial hII hq hrec hk ha.1 h1

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
