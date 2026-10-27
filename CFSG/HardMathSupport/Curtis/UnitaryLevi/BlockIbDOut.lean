module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {Y : Type*} [Group Y]

@[expose] noncomputable def outHom (L : Subgroup Y) :
    Subgroup.normalizer (L : Set Y) →* Outer L :=
  (QuotientGroup.mk' (inner L)).comp L.normalizerMonoidHom

theorem mem_sup_centralizer_of_outHom_eq_one {L : Subgroup Y}
    {x : Subgroup.normalizer (L : Set Y)} (hx : outHom L x = 1) :
    (x : Y) ∈ L ⊔ Subgroup.centralizer (L : Set Y) := by
  set a : MulAut L := L.normalizerMonoidHom x with ha
  have hψ : QuotientGroup.mk' (inner L) a = 1 := hx
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  have hcent : (l : Y)⁻¹ * (x : Y) ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨y, hy⟩)
    change (l : Y) * y * (l : Y)⁻¹ = (x : Y) * y * (x : Y)⁻¹ at h1
    calc y * ((l : Y)⁻¹ * x) = (l : Y)⁻¹ * ((l : Y) * y * (l : Y)⁻¹) * x := by group
      _ = (l : Y)⁻¹ * ((x : Y) * y * (x : Y)⁻¹) * x := by rw [h1]
      _ = (l : Y)⁻¹ * x * y := by group
  rw [show (x : Y) = (l : Y) * ((l : Y)⁻¹ * x) by group]
  exact Subgroup.mul_mem_sup l.2 hcent

theorem mul_comm_of_card_pow_three {G : Type*} [Group G] [Finite G] {n : ℕ}
    (h : Nat.card G = 3 ^ n) (hn : n ≤ 1) (a b : G) : a * b = b * a := by
  interval_cases n
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 (by simpa using h)).1
    exact Subsingleton.elim _ _
  · have : IsCyclic G := isCyclic_of_prime_card (p := 3) (by simpa using h)
    exact (IsCyclic.commGroup (α := G)).mul_comm a b

theorem three_pgroup_normalizer_out [Finite Y] {L U : Subgroup Y}
    (hUN : U ≤ Subgroup.normalizer (L : Set Y)) (hU3 : IsPGroup 3 U)
    (hout : ¬ 9 ∣ Nat.card (Outer L)) :
    (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set Y)) ∧
      Nat.card U ≤ 3 * Nat.card ↥(U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))) := by
  have : Finite L := Finite.of_injective _ L.subtype_injective
  have : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  set φ : U →* Outer L := (outHom L).comp (Subgroup.inclusion hUN) with hφ
  set R : Subgroup (Outer L) := φ.range with hR
  have hR3 : IsPGroup 3 R := hU3.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  obtain ⟨n, hn⟩ := hR3.exists_card_eq
  have hRdvd : Nat.card R ∣ Nat.card (Outer L) := Subgroup.card_subgroup_dvd_card R
  have hn1 : n ≤ 1 := by
    by_contra hlt
    apply hout
    have h1 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    rw [hn] at hRdvd
    exact h1.trans hRdvd
  have hker : ∀ g : U, φ g = 1 → (g : Y) ∈ L ⊔ Subgroup.centralizer (L : Set Y) := fun g hg => by
    have := mem_sup_centralizer_of_outHom_eq_one (x := ⟨(g : Y), hUN g.2⟩) hg
    exact this
  refine ⟨fun a ha b hb => ?_, ?_⟩
  · have hcomm : ∀ x y : R, x * y = y * x := mul_comm_of_card_pow_three hn hn1
    have h1 := hcomm ⟨φ ⟨a, ha⟩, ⟨_, rfl⟩⟩ ⟨φ ⟨b, hb⟩, ⟨_, rfl⟩⟩
    have h2 : φ (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
      have h3 := congrArg Subtype.val h1
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h3
    exact hker _ h2
  · have hcard := Subgroup.card_ker_mul_card_range φ
    have hRle : Nat.card R ≤ 3 := by
      rw [hn]
      calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
        _ = 3 := by norm_num
    have hle : Nat.card φ.ker ≤ Nat.card ↥(U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))) := by
      have hsub : φ.ker.map U.subtype ≤ U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) := by
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨g.2, hker g hg⟩
      calc Nat.card φ.ker = Nat.card (φ.ker.map U.subtype) :=
            (Nat.card_congr (Subgroup.equivMapOfInjective φ.ker U.subtype U.subtype_injective).toEquiv)
        _ ≤ _ := Subgroup.card_le_of_le hsub
    calc Nat.card U = Nat.card φ.ker * Nat.card φ.range := hcard.symm
      _ ≤ Nat.card ↥(U ⊓ (L ⊔ Subgroup.centralizer (L : Set Y))) * 3 :=
          Nat.mul_le_mul hle hRle
      _ = _ := by ring

end CFSG.HardMathSupport.Curtis.UnitaryLevi
