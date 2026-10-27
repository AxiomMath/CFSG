module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GH74.GLS.IVK.Statements.Sec9b
public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.GH74.GLS.Stage4.T2CentSL
public import CFSG.GH74.GLS.Stage4.T2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section Abelian

variable {G : Type} [Group G] [Finite G]

theorem t2F1_three_abelian {Gs : Type} [Group Gs] {n : ℕ} (hn : n ≠ 0) {z : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) {N : T2N1 G} {u : G} (hLoc : Ch6Loc5 N u)
    (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) :
    ∀ Q : Subgroup G, Q ≤ K₁ ⊔ K₂ → IsPGroup 3 ↥Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hSet.finite₁
  have := hSet.finite₂
  intro Q hQK hQp
  have hX₁K : N.X₁ ≤ K₁ := by
    rw [← hK₁, hLoc.K₁_eq]; exact le_sup_left
  have hX₂K : N.X₂ ≤ K₂ := by
    rw [← hK₂, hLoc.K₂_eq]; exact le_sup_left
  have hcomm12 : ∀ x ∈ N.X₁, ∀ y ∈ N.X₂, x * y = y * x := fun x hx y hy => hSet.comm x (hX₁K hx) y (hX₂K hy)
  have hX₁c : Nat.card ↥N.X₁ = 3 ^ n := by rw [hLoc.card_X₁, hq₁]
  have hX₂c : Nat.card ↥N.X₂ = 3 ^ n := by rw [hLoc.card_X₂, hq₂]
  have hexp : (3 ^ n).minFac = 3 := Nat.Prime.pow_minFac Nat.prime_three hn
  have hX₁e : ∀ x ∈ N.X₁, x ^ 3 = 1 := fun x hx => by
    have := hLoc.X₁_exp x hx; rw [hq₁, hexp] at this; exact this
  have hX₂e : ∀ x ∈ N.X₂, x ^ 3 = 1 := fun x hx => by
    have := hLoc.X₂_exp x hx; rw [hq₂, hexp] at this; exact this
  have hinter : N.X₁ ⊓ N.X₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxz : x ∈ Subgroup.zpowers z := by
      rw [← hSet.inter_eq]; exact ⟨hX₁K hx.1, hX₂K hx.2⟩
    have hz2 : z ^ 2 = 1 := by rw [← hSet.central.1]; exact pow_orderOf_eq_one z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
    have hx2 : x ^ 2 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
    have hx3 := hX₁e x hx.1
    have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
    rw [Subgroup.mem_bot, this, hx3, hx2]; group
  set A : Subgroup G := N.X₁ ⊔ N.X₂ with hA
  have hAK : A ≤ K₁ ⊔ K₂ := sup_le (hX₁K.trans le_sup_left) (hX₂K.trans le_sup_right)
  have hAcard : Nat.card ↥A = 3 ^ (2 * n) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute N.X₁ N.X₂ hcomm12).1
    rw [hinter, Subgroup.card_bot, hX₁c, hX₂c] at h
    rw [mul_one] at h
    rw [h, ← pow_add, two_mul]
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm12 x).1 hx
    obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_comm hcomm12 y).1 hy
    have h1 : a * a' = a' * a := by
      have := hLoc.X₁_comm a ha a' ha'; exact this
    have h2 : b * b' = b' * b := by
      have := hLoc.X₂_comm b hb b' hb'; exact this
    have h3 : b * a' = a' * b := (hcomm12 a' ha' b hb).symm
    have h4 : b' * a = a * b' := (hcomm12 a ha b' hb').symm
    have e1 : a * b * (a' * b') = (a * a') * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [h3]
        _ = (a * a') * (b * b') := by group
    have e2 : a' * b' * (a * b) = (a' * a) * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [h4]
        _ = (a' * a) * (b' * b) := by group
    rw [e1, e2, h1, h2]
  have hK : Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card ↥K₁ * Nat.card ↥K₂ := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ hSet.comm).1
    rwa [hSet.inter_card] at h
  have hK₁c : Nat.card ↥K₁ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
    obtain ⟨e⟩ := hSet.iso₁
    rw [Nat.card_congr e.toEquiv, t2C_card_sl2, hSet.card₁]
  have hK₂c : Nat.card ↥K₂ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
    obtain ⟨e⟩ := hSet.iso₂
    rw [Nat.card_congr e.toEquiv, t2C_card_sl2, hSet.card₂]
  have h3n : 3 ∣ 3 ^ n := dvd_pow_self 3 hn
  have h2n : 2 ≤ 3 ^ n := by
    have := Nat.le_of_dvd (by positivity) h3n
    have h0 : 0 < 3 ^ n := by positivity
    omega
  have hm : (3 ^ n) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (3 ^ n) ^ 2 := by nlinarith
    omega
  have hnd : ¬ 3 ∣ (3 ^ n) ^ 2 - 1 := by
    have h3 : 3 ∣ (3 ^ n) ^ 2 := dvd_pow h3n (by norm_num)
    have h1 : 1 ≤ (3 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    generalize (3 ^ n) ^ 2 = X at h3 h1 ⊢
    omega
  have hval : (Nat.card ↥(K₁ ⊔ K₂)).factorization 3 = 2 * n := by
    have hprod : Nat.card ↥(K₁ ⊔ K₂) * 2 = (3 ^ n * ((3 ^ n) ^ 2 - 1)) ^ 2 := by
      rw [hK, hK₁c, hK₂c]
      exact (sq _).symm
    have hK0 : Nat.card ↥(K₁ ⊔ K₂) ≠ 0 := Nat.card_pos.ne'
    have h1 : (Nat.card ↥(K₁ ⊔ K₂) * 2).factorization 3 =
        ((3 ^ n * ((3 ^ n) ^ 2 - 1)) ^ 2).factorization 3 := by rw [hprod]
    rw [Nat.factorization_mul hK0 (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.factorization_mul (by positivity) hm, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, Nat.Prime.factorization_pow Nat.prime_three] at h1
    have h2 : (2 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [h2] at h1
    simpa using h1
  set K : Subgroup G := K₁ ⊔ K₂ with hKdef
  have hA'p : IsPGroup 3 ↥(A.subgroupOf K) := by
    refine IsPGroup.of_card (n := 2 * n) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hAcard]
  obtain ⟨T', hT'⟩ := hA'p.exists_le_sylow
  have hT'card : Nat.card ↥(T' : Subgroup ↥K) = 3 ^ (2 * n) := by
    rw [Sylow.card_eq_multiplicity T', hval]
  have hA'T' : A.subgroupOf K = (T' : Subgroup ↥K) := by
    refine Subgroup.eq_of_le_of_card_ge hT' ?_
    rw [hT'card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hAcard]
  have hQ'p : IsPGroup 3 ↥(Q.subgroupOf K) := hQp.comap_subtype (K := K)
  obtain ⟨T, hT⟩ := hQ'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K T' T
  have hTc : ∀ x ∈ (T : Subgroup ↥K), ∀ y ∈ (T : Subgroup ↥K), x * y = y * x := by
    intro x hx y hy
    rw [← hg, Sylow.coe_subgroup_smul] at hx hy
    obtain ⟨x', hx', hxx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
    obtain ⟨y', hy', hyy⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    rw [← hA'T'] at hx' hy'
    have hx'A : (x' : G) ∈ A := Subgroup.mem_subgroupOf.1 hx'
    have hy'A : (y' : G) ∈ A := Subgroup.mem_subgroupOf.1 hy'
    have hc : x' * y' = y' * x' := Subtype.ext (hAc _ hx'A _ hy'A)
    have hxx' : x = g * x' * g⁻¹ := by
      rw [← hxx]; simp [MulAut.smul_def, MulAut.conj_apply]
    have hyy' : y = g * y' * g⁻¹ := by
      rw [← hyy]; simp [MulAut.smul_def, MulAut.conj_apply]
    rw [hxx', hyy']
    calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
      _ = g * (y' * x') * g⁻¹ := by rw [hc]
      _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group
  intro x hx y hy
  have hxK : x ∈ K := hQK hx
  have hyK : y ∈ K := hQK hy
  have hxT : (⟨x, hxK⟩ : ↥K) ∈ (T : Subgroup ↥K) := hT (Subgroup.mem_subgroupOf.2 hx)
  have hyT : (⟨y, hyK⟩ : ↥K) ∈ (T : Subgroup ↥K) := hT (Subgroup.mem_subgroupOf.2 hy)
  exact congrArg Subtype.val (hTc _ hxT _ hyT)

end Abelian

@[expose] def Ch6T2F1Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 3 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      Ch6Bad3 G →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ f : G, orderOf f = r →
              (∃ S : Sylow 2 G, (∀ s ∈ (S : Subgroup G), s * z = z * s) ∧
                f ∈ centralizer ((S : Subgroup G) : Set G)) →
                ∃ (m : ℕ) (hzC : z ∈ centralizer ({f} : Set G)), n = r * m ∧
                  Hyp94Loc (↥(centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({f} : Set G))) Gs
                    (QuotientGroup.mk (⟨z, hzC⟩ : ↥(centralizer ({f} : Set G)))) .G2 3 m

end CFSG.GH74.GLS.Stage4.Rest
