module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119G
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119F

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)

theorem rigid
    (hEA : ∀ A : Subgroup (MulAut ↥E), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (Q₁ : Subgroup G) (hQ₁M : Q₁ ≤ normalizer ((S ⊔ E : Subgroup G) : Set G))
    (φ : ↥Q₁ ≃* ↥c.Qs)
    (hZ : ∀ x : G, (x ∈ Q₁ ∧ ∀ q ∈ Q₁, x * q = q * x) ↔ x ∈ c.Zs) :
    Q₁ = c.Qs := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZQ₁ : c.Zs ≤ Q₁ := fun a ha => ((hZ a).2 ha).1
  have hQ₁N1 : Q₁ ≤ c.N1 := by
    intro q hq
    have hc : α * q = q * α := ((hZ α).2 c.alpha_mem_Zs).2 q hq
    rw [c.mem_N1]
    refine ⟨c.M_le_Nc (hQ₁M hq), ?_⟩
    calc q * α * q⁻¹ = α * q * q⁻¹ := by rw [← hc]
      _ = α := by group
  let rQ : ↥Q₁ →* (MulAut ↥E × MulAut ↥E) := c.rho.comp (Subgroup.inclusion hQ₁N1)
  have hker_iff : ∀ x : ↥Q₁, rQ x = 1 ↔ (x : G) ∈ c.Zs := by
    intro x
    constructor
    · intro hx
      have hxQs : (x : G) ∈ c.Qs := by
        apply c.mem_Qs_of_inn hπ (hQ₁M x.2) (hQ₁N1 x.2)
        have h1 : c.rho ⟨(x : G), hQ₁N1 x.2⟩ = 1 := hx
        rw [h1]
        exact one_mem _
      exact c.mem_Zs_of_rho_one hxQs hx
    · intro hx
      exact c.rho_Zs hx
  have hphi : ∀ u : ↥Q₁, ((φ u : ↥c.Qs) : G) ∈ c.Zs → (u : G) ∈ c.Zs := by
    intro u hu
    refine (hZ u).1 ⟨u.2, fun q hq => ?_⟩
    have hcomm : (φ u : G) * ((φ ⟨q, hq⟩ : ↥c.Qs) : G) =
        ((φ ⟨q, hq⟩ : ↥c.Qs) : G) * (φ u : G) :=
      c.Zs_comm_Qs hu (φ ⟨q, hq⟩).2
    have hinj : φ (u * ⟨q, hq⟩) = φ (⟨q, hq⟩ * u) := by
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      exact hcomm
    exact congrArg Subtype.val (φ.injective hinj)
  have hcommQ : ∀ x y : ↥Q₁, (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ c.Zs := by
    intro x y
    refine hphi (x * y * x⁻¹ * y⁻¹) ?_
    have e : ((φ (x * y * x⁻¹ * y⁻¹) : ↥c.Qs) : G) =
        (φ x : G) * (φ y : G) * (φ x : G)⁻¹ * (φ y : G)⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact c.comm_Qs_mem (φ x).2 (φ y).2
  have hsqQ : ∀ x : ↥Q₁, (x : G) * (x : G) ∈ c.Zs := by
    intro x
    refine hphi (x * x) ?_
    have e : ((φ (x * x) : ↥c.Qs) : G) = (φ x : G) * (φ x : G) := by
      simp only [map_mul, Subgroup.coe_mul]
    rw [e]
    exact c.sq_Qs_mem (φ x).2
  have hRcomm_el : ∀ x y : ↥Q₁, rQ (x * y) = rQ (y * x) := by
    intro x y
    have hc : rQ (x * y * x⁻¹ * y⁻¹) = 1 := (hker_iff _).2 (hcommQ x y)
    rw [show x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) by group, map_mul, hc, one_mul]
  have hRsq_el : ∀ x : ↥Q₁, rQ x * rQ x = 1 := by
    intro x
    rw [← map_mul]
    exact (hker_iff _).2 (hsqQ x)
  set R : Subgroup (MulAut ↥E × MulAut ↥E) := rQ.range with hR
  have hRcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := by
    intro r hr r' hr'
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hr
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hr'
    rw [← map_mul, ← map_mul, hRcomm_el]
  have hRsq : ∀ r ∈ R, r * r = 1 := by
    intro r hr
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hr
    exact hRsq_el x
  have hZfin : Nat.card rQ.ker = 4 := by
    have hk : rQ.ker = c.Zs.subgroupOf Q₁ := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, hker_iff]
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ₁).toEquiv, c.Zs_card]
  have hQ1card : Nat.card ↥Q₁ = 1024 := by
    rw [Nat.card_congr φ.toEquiv, c.card_Qs]
  have hRcard : Nat.card R = 256 := by
    have h1 := Subgroup.card_ker_mul_card_range rQ
    rw [hZfin, hQ1card, ← hR] at h1
    omega
  set P₁ : Subgroup (MulAut ↥E) := R.map (MonoidHom.fst _ _) with hP₁
  set P₂ : Subgroup (MulAut ↥E) := R.map (MonoidHom.snd _ _) with hP₂
  have hP₁comm : ∀ a ∈ P₁, ∀ b ∈ P₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.1 hb
    have := congrArg Prod.fst (hRcomm r hr r' hr')
    exact this
  have hP₁sq : ∀ a ∈ P₁, a * a = 1 := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 ha
    have := congrArg Prod.fst (hRsq r hr)
    exact this
  have hP₂comm : ∀ a ∈ P₂, ∀ b ∈ P₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.1 hb
    have := congrArg Prod.snd (hRcomm r hr r' hr')
    exact this
  have hP₂sq : ∀ a ∈ P₂, a * a = 1 := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 ha
    have := congrArg Prod.snd (hRsq r hr)
    exact this
  have hP₁card : Nat.card P₁ ≤ 16 := hEA P₁ hP₁comm hP₁sq
  have hP₂card : Nat.card P₂ ≤ 16 := hEA P₂ hP₂comm hP₂sq
  have hRle : R ≤ P₁.prod P₂ := by
    intro r hr
    exact Subgroup.mem_prod.2 ⟨Subgroup.mem_map.2 ⟨r, hr, rfl⟩, Subgroup.mem_map.2 ⟨r, hr, rfl⟩⟩
  have hprod : Nat.card (P₁.prod P₂) = Nat.card P₁ * Nat.card P₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv P₁ P₂).toEquiv, Nat.card_prod]
  have hle256 : Nat.card R ≤ Nat.card (P₁.prod P₂) := Subgroup.card_le_of_le hRle
  have hmul : 256 ≤ Nat.card P₁ * Nat.card P₂ := by
    rw [hRcard, hprod] at hle256
    exact hle256
  have hP₁16 : Nat.card P₁ = 16 := by
    by_contra hne
    have hlt : Nat.card P₁ ≤ 15 := by omega
    have : Nat.card P₁ * Nat.card P₂ ≤ 15 * 16 := Nat.mul_le_mul hlt hP₂card
    omega
  have hP₂16 : Nat.card P₂ = 16 := by
    by_contra hne
    have hlt : Nat.card P₂ ≤ 15 := by omega
    have : Nat.card P₁ * Nat.card P₂ ≤ 16 * 15 := Nat.mul_le_mul hP₁card hlt
    omega
  have hRprod : R = P₁.prod P₂ :=
    Subgroup.eq_of_le_of_card_ge hRle (le_of_eq (by rw [hprod, hP₁16, hP₂16, hRcard]))
  have hP₁Inn : P₁ ≤ innAutE E := by
    intro a ha
    have h1 : (a, (1 : MulAut ↥E)) ∈ R := by
      rw [hRprod]
      exact Subgroup.mem_prod.2 ⟨ha, one_mem _⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 h1
    have h2 : c.rho ⟨(x : G), hQ₁N1 x.2⟩ = (a, 1) := hx
    have hπeq := c.pi_eq_of_mem_M hπ (hQ₁M x.2) (hQ₁N1 x.2)
    rw [h2] at hπeq
    have hπa : π a = π 1 := hπeq
    rw [map_one] at hπa
    exact (hπ.ker a).1 hπa
  have hP₂Inn : P₂ ≤ innAutE E := by
    intro b hb
    have h1 : ((1 : MulAut ↥E), b) ∈ R := by
      rw [hRprod]
      exact Subgroup.mem_prod.2 ⟨one_mem _, hb⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 h1
    have h2 : c.rho ⟨(x : G), hQ₁N1 x.2⟩ = (1, b) := hx
    have hπeq := c.pi_eq_of_mem_M hπ (hQ₁M x.2) (hQ₁N1 x.2)
    rw [h2] at hπeq
    have hπb : π 1 = π b := hπeq
    rw [map_one] at hπb
    exact (hπ.ker b).1 hπb.symm
  have hP₁eq : P₁ = innAutE E :=
    Subgroup.eq_of_le_of_card_ge hP₁Inn (le_of_eq (by rw [c.card_innE, hP₁16]))
  have hP₂eq : P₂ = innAutE E :=
    Subgroup.eq_of_le_of_card_ge hP₂Inn (le_of_eq (by rw [c.card_innE, hP₂16]))
  have hRInn : R = (innAutE E).prod (innAutE E) := by
    rw [hRprod, hP₁eq, hP₂eq]
  have hQ₁Qs : Q₁ ≤ c.Qs := by
    intro q hq
    have h1 : rQ ⟨q, hq⟩ ∈ R := MonoidHom.mem_range.2 ⟨⟨q, hq⟩, rfl⟩
    rw [hRInn] at h1
    have hinn : (c.rho ⟨q, hQ₁N1 hq⟩).1 ∈ innAutE E := (Subgroup.mem_prod.1 h1).1
    exact c.mem_Qs_of_inn hπ (hQ₁M hq) (hQ₁N1 hq) hinn
  exact Subgroup.eq_of_le_of_card_ge hQ₁Qs (le_of_eq (by rw [c.card_Qs, hQ1card]))

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
