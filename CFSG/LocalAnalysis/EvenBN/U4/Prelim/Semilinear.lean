module

public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup Module

section Crossed

variable {G : Type*} [Group G]

theorem crossed_image_trivial_or_top {N X E I : Subgroup G} {t : G}
    (hX : CFSG.IsElementaryAbelian 2 X) (hsup : E ⊔ zpowers t = X) (ht : t ∉ E)
    (hNX : N ≤ normalizer (X : Set G)) (hNE : N ≤ normalizer (E : Set G))
    (hI : I ≤ N ⊓ centralizer ({t} : Set G))
    (htrans : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 → ∃ c ∈ I, c * e * c⁻¹ = e') :
    N ⊓ centralizer (E : Set G) ≤ centralizer ({t} : Set G) ∨
      CFSG.LocalAnalysis.EvenBN.Common.RegularNormalData N X E (N ⊓ centralizer (E : Set G)) t := by
  have htX : t ∈ X := hsup ▸ mem_sup_right (mem_zpowers t)
  have hEX : E ≤ X := hsup ▸ le_sup_left
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : X) ⟨y, hy⟩)
  have ht2 : t * t = 1 := by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian t htX
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcross : ∀ y ∈ N, y⁻¹ * t * y * t ∈ E := by
    intro y hy
    have hyX : y⁻¹ * t * y ∈ X := by
      have := (mem_normalizer_iff.mp (hNX (N.inv_mem hy)) t).mp htX
      rwa [inv_inv] at this
    have hyE : y⁻¹ * t * y ∉ E := fun hE => ht (by
      have := (mem_normalizer_iff.mp (hNE hy) _).mp hE
      simpa [mul_assoc] using this)
    have hEt : ∀ e ∈ E, e * t = t * e := fun e he => hcommX e (hEX he) t htX
    rw [← hsup, CFSG.EvenSmallLie.UnitarySix.YamadaD.mem_sup_zpowers_iff ht2 hEt] at hyX
    exact hyX.resolve_left hyE
  by_cases hall : N ⊓ centralizer (E : Set G) ≤ centralizer ({t} : Set G)
  · exact Or.inl hall
  right
  obtain ⟨y₀, hy₀, hy₀t⟩ := IsConcreteLE.not_le_iff_exists.mp hall
  set e₀ := y₀⁻¹ * t * y₀ * t
  have he₀E : e₀ ∈ E := hcross y₀ hy₀.1
  have he₀1 : e₀ ≠ 1 := by
    intro h1
    apply hy₀t
    rw [mem_centralizer_singleton_iff]
    have : y₀⁻¹ * t * y₀ = t := by
      calc y₀⁻¹ * t * y₀ = e₀ * t⁻¹ := by simp [e₀, mul_assoc]
        _ = t := by rw [h1, one_mul, htinv]
    calc y₀ * t = y₀ * (y₀⁻¹ * t * y₀) := by rw [this]
      _ = t * y₀ := by group
  have honto : ∀ e ∈ E, ∃ y ∈ N ⊓ centralizer (E : Set G), y⁻¹ * t * y * t = e := by
    intro e he
    by_cases he1 : e = 1
    · exact ⟨1, one_mem _, by rw [he1]; simp [ht2]⟩
    obtain ⟨c, hc, hce⟩ := htrans e₀ he₀E he₀1 e he he1
    have hcN : c ∈ N := (hI hc).1
    have hct : c * t = t * c := mem_centralizer_singleton_iff.mp (hI hc).2
    refine ⟨c * y₀ * c⁻¹, mem_inf.mpr ⟨N.mul_mem (N.mul_mem hcN hy₀.1) (N.inv_mem hcN), ?_⟩, ?_⟩
    · rw [mem_centralizer_iff]
      intro x hx
      have hx' : c⁻¹ * x * c ∈ E := by
        have := (mem_normalizer_iff.mp (hNE (N.inv_mem hcN)) x).mp hx
        rwa [inv_inv] at this
      have := mem_centralizer_iff.mp hy₀.2 _ hx'
      calc x * (c * y₀ * c⁻¹) = c * ((c⁻¹ * x * c) * y₀) * c⁻¹ := by group
        _ = c * (y₀ * (c⁻¹ * x * c)) * c⁻¹ := by rw [this]
        _ = c * y₀ * c⁻¹ * x := by group
    · have hct' : c⁻¹ * t = t * c⁻¹ := by
        calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
          _ = t * c⁻¹ := by group
      rw [← hce]
      calc (c * y₀ * c⁻¹)⁻¹ * t * (c * y₀ * c⁻¹) * t
          = c * y₀⁻¹ * (c⁻¹ * t) * c * y₀ * c⁻¹ * t := by group
        _ = c * y₀⁻¹ * (t * c⁻¹) * c * y₀ * c⁻¹ * t := by rw [hct']
        _ = c * (y₀⁻¹ * t * y₀) * (c⁻¹ * t) := by group
        _ = c * (y₀⁻¹ * t * y₀) * (t * c⁻¹) := by rw [hct']
        _ = c * e₀ * c⁻¹ := by simp only [e₀]; group
  refine ⟨hX, hsup, ht, hNX, hNE, le_rfl, fun e he => subset_closure ?_⟩
  obtain ⟨y, hy, hye⟩ := honto e he
  refine ⟨y⁻¹, inv_mem hy, 1, one_mem _, ?_⟩
  have hte : e * t = t * e := hcommX e (hEX he) t htX
  have key : t * e * t = e := by rw [← hte, mul_assoc, ht2, mul_one]
  rw [one_mul, inv_one, mul_one, commutatorElement_def, inv_inv, htinv]
  calc e = t * e * t := key.symm
    _ = t * (y⁻¹ * t * y * t) * t := by rw [hye]
    _ = t * y⁻¹ * t * y * (t * t) := by group
    _ = t * y⁻¹ * t * y := by rw [ht2, mul_one]

end Crossed

section TwoPart

variable {H F W : Type*} [Group H] [Field F] [Finite F] [AddCommGroup W] [Module F W]

theorem card_ringHom_le {f : ℕ} (hF : Nat.card F = 2 ^ f) : Nat.card (F →+* F) ≤ f := by
  classical
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow hF'
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hrank : finrank (ZMod 2) F = f := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF', ZMod.card] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : (F →+* F) → (F →ₐ[ZMod 2] F) := fun σ =>
    { σ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (σ.comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)) r }
  have he : Function.Injective e := fun σ τ hστ => RingHom.ext fun x =>
    congrArg (fun φ : F →ₐ[ZMod 2] F => φ x) hστ
  calc Nat.card (F →+* F) ≤ Nat.card (F →ₐ[ZMod 2] F) := Nat.card_le_card_of_injective e he
    _ ≤ finrank (ZMod 2) F := card_algHom_le_finrank (ZMod 2) F F
    _ = f := hrank

theorem not_two_pow_dvd_index_ker [Finite H] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hW : finrank F W = 1) (ρ : H →* AddMonoid.End W)
    (hρ : ∀ h, ∃ σ : F →+* F, ∀ (c : F) (w : W), ρ h (c • w) = σ c • ρ h w) :
    ¬ 2 ^ f ∣ ρ.ker.index := by
  classical
  obtain ⟨v₀, hv₀, hspan⟩ := finrank_eq_one_iff'.mp hW
  have hinj := smul_left_injective F hv₀
  have hinv : ∀ (h : H) (w : W), ρ h (ρ h⁻¹ w) = w := fun h w => by
    change (ρ h * ρ h⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  choose σ hσ using hρ
  have huniq : ∀ (h : H) (τ : F →+* F), (∀ (c : F) (w : W), ρ h (c • w) = τ c • ρ h w) →
      τ = σ h := by
    intro h τ hτ
    ext c
    apply hinj
    change τ c • v₀ = σ h c • v₀
    rw [← hinv h v₀, ← hτ, hσ]
  let Φ : H →* (F →+* F) :=
    { toFun := σ
      map_one' := (huniq 1 (RingHom.id F) (fun c w => by rw [map_one]; rfl)).symm
      map_mul' := fun h h' => (huniq (h * h') ((σ h).comp (σ h')) (fun c w => by
        rw [map_mul]
        change ρ h (ρ h' (c • w)) = _ • ρ h (ρ h' w)
        rw [hσ, hσ]
        rfl)).symm }
  set H₀ := Φ.toHomUnits.ker
  have hH₀ : ∀ h : H, h ∈ H₀ ↔ σ h = RingHom.id F := by
    intro h
    rw [MonoidHom.mem_ker, Units.ext_iff]
    rfl
  choose μ hμ using fun h : H => hspan (ρ h v₀)
  have hscal : ∀ h ∈ H₀, ∀ w : W, ρ h w = μ h • w := by
    intro h hh w
    obtain ⟨d, rfl⟩ := hspan w
    rw [hσ, (hH₀ h).mp hh, RingHom.id_apply, ← hμ, smul_comm]
  have hker : ρ.ker ≤ H₀ := by
    intro h hh
    rw [hH₀]
    exact (huniq h (RingHom.id F) (fun c w => by
      rw [(MonoidHom.mem_ker).mp hh]; rfl)).symm
  let μhom : H₀ →* F :=
    { toFun := fun h => μ h
      map_one' := hinj (by
        change μ 1 • v₀ = (1 : F) • v₀
        rw [← hscal 1 (one_mem _), map_one, one_smul]; rfl)
      map_mul' := fun h h' => hinj (by
        change μ (h * h' : H) • v₀ = (μ h * μ h') • v₀
        rw [← hscal _ (H₀.mul_mem h.2 h'.2), mul_smul, ← hscal _ h'.2, ← hscal _ h.2, map_mul]
        rfl) }
  set μunit := μhom.toHomUnits
  have hkerμ : μunit.ker = ρ.ker.subgroupOf H₀ := by
    ext h
    rw [MonoidHom.mem_ker, Units.ext_iff, mem_subgroupOf, MonoidHom.mem_ker]
    change μ h = 1 ↔ _
    constructor
    · intro h1
      ext w
      rw [hscal _ h.2, h1, one_smul]
      rfl
    · intro h1
      apply hinj
      change μ h • v₀ = (1 : F) • v₀
      rw [← hscal _ h.2, h1, one_smul]
      rfl
  have hidx : ρ.ker.index = ρ.ker.relIndex H₀ * H₀.index := (relIndex_mul_index hker).symm
  have hrel : ρ.ker.relIndex H₀ ∣ 2 ^ f - 1 := by
    rw [relIndex, ← hkerμ, index_ker, ← hF, ← Nat.card_units]
    exact card_subgroup_dvd_card _
  have hH₀idx : H₀.index ≤ f := by
    have : Finite (F →+* F) :=
      Finite.of_injective (fun τ : F →+* F => (τ : F → F)) DFunLike.coe_injective
    rw [index_ker]
    calc Nat.card Φ.toHomUnits.range ≤ Nat.card (F →+* F)ˣ :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ ≤ Nat.card (F →+* F) := Nat.card_le_card_of_injective _ Units.val_injective
      _ ≤ f := card_ringHom_le hF
  have hpos : 0 < H₀.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  intro hdvd
  have hodd : Nat.Coprime (2 ^ f) (ρ.ker.relIndex H₀) := by
    refine Nat.Coprime.coprime_dvd_right hrel ?_
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [Nat.coprime_self_sub_right h1]
    exact Nat.coprime_one_right _
  rw [hidx] at hdvd
  have h2 := Nat.le_of_dvd hpos (hodd.dvd_of_dvd_mul_left hdvd)
  have h3 : f < 2 ^ f := Nat.lt_two_pow_self
  omega

theorem false_of_two_part [Finite H] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hW : finrank F W = 1)
    (ρ : H →* AddMonoid.End W)
    (hρ : ∀ h, ∃ σ : F →+* F, ∀ (c : F) (w : W), ρ h (c • w) = σ c • ρ h w)
    {S : Subgroup H} (hS : ρ.ker ≤ S) (hdvd : 2 ^ f ∣ S.index) : False :=
  not_two_pow_dvd_index_ker hF hW ρ hρ (hdvd.trans (index_dvd_of_le hS))

end TwoPart

section Orbit

variable {G : Type*} [Group G]

theorem card_conj_set_eq_relIndex (H : Subgroup G) (t : G) :
    Nat.card {x | ∃ g ∈ H, x = g⁻¹ * t * g} = (centralizer ({t} : Set G)).relIndex H := by
  let : MulAction H G := MulAction.compHom G
    ((MulAut.conj : G →* MulAut G).comp H.subtype)
  have horbit : MulAction.orbit H t = {x | ∃ g ∈ H, x = g⁻¹ * t * g} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨(g : G)⁻¹, H.inv_mem g.2, ?_⟩
      change (g : G) * t * (g : G)⁻¹ = _
      rw [inv_inv]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩⁻¹, ?_⟩
      change ((⟨g, hg⟩⁻¹ : H) : G) * t * ((⟨g, hg⟩⁻¹ : H) : G)⁻¹ = _
      simp
  have hstab : MulAction.stabilizer H t = (centralizer ({t} : Set G)).subgroupOf H := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    change (g : G) * t * (g : G)⁻¹ = t ↔ _
    constructor
    · intro h
      calc (g : G) * t = (g : G) * t * (g : G)⁻¹ * g := by group
        _ = t * g := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  rw [← horbit, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, hstab, relIndex]

theorem not_two_pow_dvd_card_conj_set {F W : Type*} [Field F] [Finite F] [AddCommGroup W]
    [Module F W] {H : Subgroup G} [Finite H] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hW : finrank F W = 1) (ρ : H →* AddMonoid.End W)
    (hρ : ∀ h, ∃ σ : F →+* F, ∀ (c : F) (w : W), ρ h (c • w) = σ c • ρ h w) {t : G}
    (hker : ∀ h : H, ρ h = 1 → (h : G) * t = t * h) :
    ¬ 2 ^ f ∣ Nat.card {x | ∃ g ∈ H, x = g⁻¹ * t * g} := by
  intro hdvd
  rw [card_conj_set_eq_relIndex] at hdvd
  refine false_of_two_part hF hW ρ hρ (S := (centralizer ({t} : Set G)).subgroupOf H)
    (fun h hh => ?_) hdvd
  rw [mem_subgroupOf, mem_centralizer_singleton_iff]
  exact hker h (MonoidHom.mem_ker.mp hh)

end Orbit

end CFSG.LocalAnalysis.EvenBN.U4
