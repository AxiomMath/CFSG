module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

theorem twentySeven_dvd_card_eqLocus_of_twist {S : Type*} [Group S] [Finite S]
    (Z : Subgroup S) [Z.Normal] (hZc : Z ≤ Subgroup.center S) (hZ3 : Nat.card Z ∣ 3)
    (σ : MulAut S) (π : MulAut (S ⧸ Z)) (hπ : ∀ g : S, π (g : S ⧸ Z) = ((σ g : S) : S ⧸ Z))
    (K : Subgroup S) (hK : ∀ k ∈ K, σ k = k) (h27 : 27 ∣ Nat.card K) (g₀ z₀ : S) (hz₀ : z₀ ∈ Z)
    (hg₀ : σ g₀ = z₀ * g₀) (hord : orderOf z₀ = 3) :
    27 ∣ Nat.card (π.toMonoidHom.eqLocus (MonoidHom.id (S ⧸ Z))) := by
  classical
  have hcen : ∀ z ∈ Z, ∀ g : S, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZc hz) g
  set C : Subgroup (S ⧸ Z) := π.toMonoidHom.eqLocus (MonoidHom.id (S ⧸ Z)) with hC
  let H : Subgroup S := C.comap (QuotientGroup.mk' Z)
  have hmemH : ∀ g : S, g ∈ H ↔ (σ g)⁻¹ * g ∈ Z := by
    intro g
    change π (g : S ⧸ Z) = (g : S ⧸ Z) ↔ _
    rw [hπ, QuotientGroup.eq]
  have hZH : Z ≤ H := by
    intro z hz
    rw [hmemH]
    have h1 : ((σ z : S) : S ⧸ Z) = 1 := by
      rw [← hπ, (QuotientGroup.eq_one_iff z).2 hz, map_one]
    have h2 : σ z ∈ Z := (QuotientGroup.eq_one_iff _).1 h1
    exact Z.mul_mem (Z.inv_mem h2) hz
  have hKH : K ≤ H := by
    intro k hk
    rw [hmemH, hK k hk, inv_mul_cancel]
    exact Z.one_mem
  let ψ : H →* S := MonoidHom.mk' (fun g => (σ g.1)⁻¹ * g.1) (by
    intro a b
    have hz := (hmemH a.1).1 a.2
    have hc := hcen _ hz ((σ b.1)⁻¹)
    calc (σ ((a * b : H) : S))⁻¹ * ((a * b : H) : S)
        = (σ b.1)⁻¹ * ((σ a.1)⁻¹ * a.1) * b.1 := by
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]; group
      _ = ((σ a.1)⁻¹ * a.1) * (σ b.1)⁻¹ * b.1 := by rw [hc]
      _ = ((σ a.1)⁻¹ * a.1) * ((σ b.1)⁻¹ * b.1) := by group)
  have hψ : ∀ g : H, ψ g = (σ g.1)⁻¹ * g.1 := fun g => rfl
  have hker27 : 27 ∣ Nat.card ψ.ker := by
    have hle : K.subgroupOf H ≤ ψ.ker := by
      intro k hk
      rw [MonoidHom.mem_ker, hψ]
      have := hK k.1 hk
      show (σ k.1)⁻¹ * k.1 = 1
      rw [this, inv_mul_cancel]
    refine h27.trans ?_
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  have hval0 : (σ g₀)⁻¹ * g₀ = z₀⁻¹ := by
    rw [hg₀, mul_inv_rev, mul_assoc, ← hcen z₀⁻¹ (Z.inv_mem hz₀) g₀, inv_mul_cancel_left]
  have hg₀H : g₀ ∈ H := by
    rw [hmemH, hval0]
    exact Z.inv_mem hz₀
  have hrange3 : 3 ∣ Nat.card ψ.range := by
    let x : ψ.range := ⟨z₀⁻¹, ⟨⟨g₀, hg₀H⟩, by rw [hψ]; exact hval0⟩⟩
    have hx : orderOf x = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact (orderOf_inv z₀).trans hord
    exact hx ▸ orderOf_dvd_natCard x
  have h81 : 81 ∣ Nat.card H := by
    rw [← Subgroup.card_ker_mul_card_range ψ]
    have := mul_dvd_mul hker27 hrange3
    omega
  let ρ : H →* C := (QuotientGroup.mk' Z).subgroupComap C
  have hρsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective c.1
    exact ⟨⟨g, show QuotientGroup.mk' Z g ∈ C by
      rw [QuotientGroup.mk'_apply]; exact hg ▸ c.2⟩, Subtype.ext hg⟩
  have hkerρ : ρ.ker = Z.subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have : (g.1 : S ⧸ Z) = 1 := congrArg Subtype.val hg
      exact (QuotientGroup.eq_one_iff _).1 this
    · intro hg
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 hg)
  have hcardρ : Nat.card ρ.ker = Nat.card Z := by
    rw [hkerρ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
  have hmul := Subgroup.card_ker_mul_card_of_surjective hρsurj
  rw [hcardρ] at hmul
  have hCeq : Nat.card C = Nat.card ↥(π.toMonoidHom.eqLocus (MonoidHom.id (S ⧸ Z))) := rfl
  rw [← hCeq]
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ3 with h1 | h3
  · rw [h1, one_mul] at hmul
    rw [← hmul] at h81
    omega
  · rw [h3] at hmul
    rw [← hmul] at h81
    omega

end CFSG.HardMathSupport.Malle.E27Lie
