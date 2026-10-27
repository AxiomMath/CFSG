module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Dickson.I271

section Fixed

variable {K : Type*} [Group K] [Finite K]

@[expose] def fixedSubgroupOf (σ : MulAut K) : Subgroup K :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id K)

theorem mem_fixedSubgroupOf {σ : MulAut K} {x : K} : x ∈ fixedSubgroupOf σ ↔ σ x = x := Iff.rfl

theorem card_fixedSubgroupOf_modEq {p : ℕ} [Fact p.Prime] (σ : MulAut K) (hσ : σ ^ p = 1) :
    Nat.card K ≡ Nat.card (fixedSubgroupOf σ) [MOD p] := by
  classical
  set H : Subgroup (MulAut K) := Subgroup.zpowers σ with hH
  have hHp : IsPGroup p H := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
  have hmod := hHp.card_modEq_card_fixedPoints K
  have hfix : Nat.card (MulAction.fixedPoints H K) = Nat.card (fixedSubgroupOf σ) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      have hpow : ∀ k : ℤ, (σ ^ k) x = x := by
        intro k
        induction k using Int.induction_on with
        | zero => simp
        | succ n ih =>
          rw [zpow_add_one]
          show (σ ^ (n : ℤ)) (σ x) = x
          rw [show σ x = x from hx]
          exact ih
        | pred n ih =>
          rw [zpow_sub_one]
          show (σ ^ (-(n : ℤ))) (σ⁻¹ x) = x
          have : σ⁻¹ x = x := by
            rw [MulAut.inv_apply]
            exact σ.symm_apply_eq.2 hx.symm
          rw [this]
          exact ih
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      show (g : MulAut K) x = x
      rw [← hk]
      exact hpow k
  rw [hfix] at hmod
  exact hmod

theorem exists_fixed_orderOf_eq_prime {p : ℕ} [hp : Fact p.Prime] (σ : MulAut K) (hσ : σ ^ p = 1)
    (hdvd : p ∣ Nat.card K) : ∃ y : K, orderOf y = p ∧ σ y = y := by
  have hmod := card_fixedSubgroupOf_modEq (p := p) σ hσ
  have h0 : p ∣ Nat.card (fixedSubgroupOf σ) := by
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := fixedSubgroupOf σ) p h0
  refine ⟨(y : K), ?_, y.2⟩
  rw [Subgroup.orderOf_coe]
  exact hy

end Fixed

section RankOne

variable {K : Type*} [Group K] [Finite K]

theorem card_le_of_elemAbelian_of_unique {p : ℕ} [hp : Fact p.Prime] {k : K} (hk : orderOf k = p)
    (huniq : ∀ x : K, x ^ p = 1 → x * k = k * x → x ∈ Subgroup.zpowers k)
    {E : Subgroup K} (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p := by
  classical
  have hzk : Nat.card (Subgroup.zpowers k) = p := by rw [Nat.card_zpowers, hk]
  have hkp : IsPGroup p (Subgroup.zpowers k) := IsPGroup.of_card (n := 1) (by rw [hzk, pow_one])
  obtain ⟨P₀, hkP⟩ := hkp.exists_le_sylow
  have hkP₀ : k ∈ (P₀ : Subgroup K) := hkP (Subgroup.mem_zpowers k)
  have hP₀p : IsPGroup p (P₀ : Subgroup K) := P₀.isPGroup'
  have hnt : Nontrivial (P₀ : Subgroup K) := by
    refine ⟨⟨⟨k, hkP₀⟩, 1, fun h => ?_⟩⟩
    have : k = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hk
    exact hp.out.one_lt.ne hk
  haveI : Nontrivial (Subgroup.center (P₀ : Subgroup K)) := hP₀p.center_nontrivial
  have hZp : IsPGroup p (Subgroup.center (P₀ : Subgroup K)) := hP₀p.to_subgroup _
  have hZdvd : p ∣ Nat.card (Subgroup.center (P₀ : Subgroup K)) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exfalso
      have := Nat.card_eq_one_iff_unique.1 h
      exact (not_subsingleton _) this.1
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (P₀ : Subgroup K)) p hZdvd
  have hzo : orderOf ((z : (P₀ : Subgroup K)) : K) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzc : ∀ y ∈ (P₀ : Subgroup K), y * ((z : (P₀ : Subgroup K)) : K) =
      ((z : (P₀ : Subgroup K)) : K) * y := by
    intro y hy
    have := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hzp : ((z : (P₀ : Subgroup K)) : K) ^ p = 1 := by
    have := pow_orderOf_eq_one ((z : (P₀ : Subgroup K)) : K)
    rwa [hzo] at this
  have hzmem : ((z : (P₀ : Subgroup K)) : K) ∈ Subgroup.zpowers k :=
    huniq _ hzp (hzc k hkP₀).symm
  have hzne : ((z : (P₀ : Subgroup K)) : K) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    exact hp.out.one_lt.ne hzo
  have hzgen : Subgroup.zpowers ((z : (P₀ : Subgroup K)) : K) = Subgroup.zpowers k := by
    have hle : Subgroup.zpowers ((z : (P₀ : Subgroup K)) : K) ≤ Subgroup.zpowers k :=
      (Subgroup.zpowers_le).2 hzmem
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hzk, Nat.card_zpowers, hzo]
  have hkz : k ∈ Subgroup.zpowers ((z : (P₀ : Subgroup K)) : K) := by
    rw [hzgen]; exact Subgroup.mem_zpowers k
  have hkc : ∀ y ∈ (P₀ : Subgroup K), y * k = k * y := by
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hkz
    rw [← hn]
    exact ((Commute.zpow_right (show Commute y ((z : (P₀ : Subgroup K)) : K) from hzc y hy) n)).eq
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨P', hEP'⟩ := hEp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K P₀ P'
  have hEconj : E ≤ (Subgroup.zpowers k).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hxP : x ∈ ((g • P₀ : Sylow p K) : Subgroup K) := hEP' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
    have hy : g⁻¹ * x * g ∈ (P₀ : Subgroup K) := by
      have := hxP
      rwa [MulAut.smul_def] at this
    have hyp : (g⁻¹ * x * g) ^ p = 1 := by
      have : (g⁻¹ * x * g) ^ p = g⁻¹ * x ^ p * g := by
        have := conj_pow (a := g⁻¹) (b := x) (i := p)
        simpa using this
      rw [this, hE.2 x hx]; group
    have hyk := huniq _ hyp (hkc _ hy)
    refine ⟨g⁻¹ * x * g, hyk, ?_⟩
    simp [MulAut.conj_apply]
    group
  calc Nat.card E ≤ Nat.card ((Subgroup.zpowers k).map (MulAut.conj g).toMonoidHom) :=
        Subgroup.card_le_of_le hEconj
    _ = Nat.card (Subgroup.zpowers k) :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
    _ = p := hzk

end RankOne

end CFSG.HardMathSupport.Dickson.I271
