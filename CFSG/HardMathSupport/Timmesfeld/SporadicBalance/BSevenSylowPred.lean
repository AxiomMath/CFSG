module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.Monster.Existence.StdOdd.Cert.Base
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.Existence.StdOdd.Cert

theorem forall_of_sylow_elementary {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp3 : ¬ p ^ 3 ∣ Nat.card G) {x₀ y₀ : G} (hx₀ : orderOf x₀ = p) (hy₀ : orderOf y₀ = p)
    (h : Commute x₀ y₀) (hind : y₀ ∉ Subgroup.zpowers x₀) (reps : Set G)
    (h0 : ∃ r ∈ reps, IsConj r x₀) (hi : ∀ i < p, ∃ r ∈ reps, IsConj r (x₀ ^ i * y₀))
    (P : G → Prop) (hconj : ∀ a b : G, IsConj a b → P a → P b)
    (hgen : ∀ a b : G, Subgroup.zpowers a = Subgroup.zpowers b → P a → P b)
    (hreps : ∀ r ∈ reps, P r) : ∀ y : G, orderOf y = p → P y := by
  intro y hy
  obtain ⟨S, hS⟩ := exists_sylow_eq_commProd hp3 hx₀ hy₀ h hind
  have hyp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow S hyp
  rw [hS] at hg
  obtain ⟨a, b, hab⟩ := hg
  have hconjy : IsConj (g⁻¹ * y * g) y := isConj_iff.2 ⟨g, by group⟩
  have hord : orderOf (g⁻¹ * y * g) = p := by rw [orderOf_inv_mul_mul, hy]
  have hpp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  suffices hy' : P (g⁻¹ * y * g) from hconj _ _ hconjy hy'
  by_cases hb : (p : ℤ) ∣ b
  · have hyb : y₀ ^ b = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hy₀]; exact hb)
    have hmem : g⁻¹ * y * g ∈ Subgroup.zpowers x₀ := ⟨a, by rw [hab, hyb, mul_one]⟩
    have hzp : Subgroup.zpowers (g⁻¹ * y * g) = Subgroup.zpowers x₀ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hmem)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hx₀])
    obtain ⟨r, hr, hrc⟩ := h0
    exact hgen _ _ hzp.symm (hconj r x₀ hrc (hreps r hr))
  · have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)
    have hcop : IsCoprime (p : ℤ) b := (Irreducible.coprime_iff_not_dvd hpint.irreducible).2 hb
    obtain ⟨u, v, huv⟩ := hcop
    have hvb : v * b = 1 + (-u) * p := by linarith
    have hpow : ∀ w : G, w ^ p = 1 → w ^ (v * b) = w := fun w hw => by
      rw [hvb, zpow_add, zpow_one, zpow_mul', zpow_natCast, hw, one_zpow, mul_one]
    set y' := g⁻¹ * y * g
    have hy'p : y' ^ p = 1 := hord ▸ pow_orderOf_eq_one y'
    obtain ⟨i, hi'⟩ : ∃ i : ℕ, (a * v) % (p : ℤ) = i :=
      ⟨((a * v) % (p : ℤ)).toNat, (Int.toNat_of_nonneg (Int.emod_nonneg _ hpp.ne')).symm⟩
    have hip : i < p := by
      have := Int.emod_lt_of_pos (a * v) hpp
      omega
    have hz : y' ^ v = x₀ ^ i * y₀ := by
      have h1 : x₀ ^ (a * v) = x₀ ^ i := by
        rw [← zpow_mod_orderOf, hx₀, hi', zpow_natCast]
      have h2 : y₀ ^ (b * v) = y₀ := by
        rw [mul_comm, hpow y₀ (hy₀ ▸ pow_orderOf_eq_one y₀)]
      rw [hab, (h.zpow_zpow a b).mul_zpow, ← zpow_mul, ← zpow_mul, h1, h2]
    have hzy : (y' ^ v) ^ b = y' := by rw [← zpow_mul, hpow y' hy'p]
    have hzp : Subgroup.zpowers (x₀ ^ i * y₀) = Subgroup.zpowers y' :=
      le_antisymm
        (Subgroup.zpowers_le.2 (Subgroup.mem_zpowers_iff.2 ⟨v, hz⟩))
        (Subgroup.zpowers_le.2 (Subgroup.mem_zpowers_iff.2 ⟨b, by rw [← hz]; exact hzy⟩))
    obtain ⟨r, hr, hrc⟩ := hi i hip
    exact hgen _ _ hzp (hconj r _ hrc (hreps r hr))

theorem centralizerProp_of_isConj {G : Type*} [Group G] (p : ℕ) {a b : G} (h : IsConj a b)
    (ha : GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) = ⊥ ∧
      ∀ r ∈ Subgroup.centralizer ({a} : Set G), orderOf r ≠ 6) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) = ⊥ ∧
      ∀ r ∈ Subgroup.centralizer ({b} : Set G), orderOf r ≠ 6 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  obtain ⟨ha1, ha2⟩ := ha
  have hψ : Function.Injective (MulAut.conj c : G ≃* G).toMonoidHom :=
    (MulAut.conj c : G ≃* G).injective
  have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
    (MulAut.conj c : G ≃* G).toMonoidHom hψ (Subgroup.centralizer ({a} : Set G))
  have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
    (MulAut.conj c : G ≃* G).toMonoidHom hψ ⊤ a
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj c : G ≃* G).surjective,
    top_inf_eq] at hc
  have hs : (MulAut.conj c : G ≃* G).toMonoidHom a = c * a * c⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hs] at hc
  rw [hc, ha1, Subgroup.map_bot] at hmap
  refine ⟨hmap.symm, fun r hr => ?_⟩
  have hr' : c⁻¹ * r * c ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hr ⊢
    calc c⁻¹ * r * c * a = c⁻¹ * (r * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * r) * c := by rw [hr]
      _ = a * (c⁻¹ * r * c) := by group
  have := ha2 _ hr'
  rwa [orderOf_inv_mul_mul] at this

theorem centralizerProp_of_zpowers_eq {G : Type*} [Group G] (p : ℕ) {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b)
    (ha : GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) = ⊥ ∧
      ∀ r ∈ Subgroup.centralizer ({a} : Set G), orderOf r ≠ 6) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) = ⊥ ∧
      ∀ r ∈ Subgroup.centralizer ({b} : Set G), orderOf r ≠ 6 := by
  rwa [← centralizer_singleton_eq_of_zpowers_eq h]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
