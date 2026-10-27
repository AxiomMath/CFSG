module

public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding

section Arith

private theorem sq_sub_one_eq {p : ℕ} (hp : 1 ≤ p) : p ^ 2 - 1 = (p + 1) * (p - 1) := by
  zify [Nat.one_le_pow 2 p hp, hp]
  ring

private theorem sq_pow_half_eq {p : ℕ} {K : Type*} [Monoid K] (hp : Odd p) (x : K) :
    (x ^ 2) ^ ((p + 1) / 2) = x ^ (p + 1) := by
  rw [← pow_mul]
  congr 1
  obtain ⟨r, rfl⟩ := hp
  omega

end Arith

section Field

variable {p : ℕ} [Fact p.Prime] {μ : (GaloisField p 2)ˣ}

private theorem coe_pow_eq_one_iff (hμ : orderOf μ = p ^ 2 - 1) (n : ℕ) :
    (μ : GaloisField p 2) ^ n = 1 ↔ p ^ 2 - 1 ∣ n := by
  rw [← Units.val_pow_eq_pow_val, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one, hμ]

theorem sq_pow_half_mem_bot (hp2 : p ≠ 2) (hμ : orderOf μ = p ^ 2 - 1) :
    ((μ : GaloisField p 2) ^ 2) ^ ((p + 1) / 2) ∈ (⊥ : Subfield (GaloisField p 2)) := by
  have hp : p.Prime := Fact.out
  rw [Subfield.mem_bot_iff_pow_eq_self _ p, sq_pow_half_eq (hp.odd_of_ne_two hp2), ← pow_mul]
  have h1 : (μ : GaloisField p 2) ^ (p ^ 2) = μ := by
    have h := (coe_pow_eq_one_iff hμ (p ^ 2 - 1)).mpr dvd_rfl
    rw [← Nat.sub_add_cancel (Nat.one_le_pow 2 p hp.pos), pow_succ, h, one_mul]
  calc (μ : GaloisField p 2) ^ ((p + 1) * p) = (μ : GaloisField p 2) ^ (p ^ 2) * μ ^ p := by
        rw [← pow_add]
        congr 1
        ring
    _ = (μ : GaloisField p 2) ^ (p + 1) := by rw [h1, pow_succ']

theorem orderOf_sq_pow_half (hp2 : p ≠ 2) (hμ : orderOf μ = p ^ 2 - 1) :
    orderOf (((μ : GaloisField p 2) ^ 2) ^ ((p + 1) / 2)) = p - 1 := by
  have hp : p.Prime := Fact.out
  have key : ∀ n : ℕ, (((μ : GaloisField p 2) ^ 2) ^ ((p + 1) / 2)) ^ n = 1 ↔ p - 1 ∣ n := by
    intro n
    rw [sq_pow_half_eq (hp.odd_of_ne_two hp2), ← pow_mul, coe_pow_eq_one_iff hμ,
      sq_sub_one_eq hp.pos, mul_comm (p + 1) n, mul_comm (p + 1) (p - 1)]
    exact Nat.mul_dvd_mul_iff_right (Nat.succ_pos p)
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((key _).mpr dvd_rfl))
    ((key _).mp (pow_orderOf_eq_one _))

theorem sq_pow_notMem_bot (hp2 : p ≠ 2) (hμ : orderOf μ = p ^ 2 - 1) {k : ℕ} (hk0 : 0 < k)
    (hk : k < (p + 1) / 2) :
    ((μ : GaloisField p 2) ^ 2) ^ k ∉ (⊥ : Subfield (GaloisField p 2)) := by
  have hp : p.Prime := Fact.out
  have hodd := hp.odd_of_ne_two hp2
  intro hmem
  rw [Subfield.mem_bot_iff_pow_eq_self _ p] at hmem
  have hx0 : ((μ : GaloisField p 2) ^ 2) ^ k ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (Units.ne_zero μ))
  have h1 : (((μ : GaloisField p 2) ^ 2) ^ k) ^ (p - 1) = 1 := by
    refine mul_right_cancel₀ hx0 ?_
    rw [← pow_succ, Nat.sub_add_cancel hp.pos, hmem, one_mul]
  rw [← pow_mul, ← pow_mul, coe_pow_eq_one_iff hμ, sq_sub_one_eq hp.pos] at h1
  have h2 : p + 1 ∣ 2 * k :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.sub_pos_of_lt hp.one_lt)
      (by simpa only [mul_comm k, mul_assoc] using h1)
  have h3 := Nat.le_of_dvd (by omega) h2
  obtain ⟨r, rfl⟩ := hodd
  omega

theorem mem_bot_of_mul_mem (L : AddSubgroup (GaloisField p 2)) (hL : Nat.card L = p)
    {γ : GaloisField p 2} (hγ : ∀ w ∈ L, γ * w ∈ L) : γ ∈ (⊥ : Subfield (GaloisField p 2)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨w, hw, hw0⟩ := (L.bot_or_exists_ne_zero).resolve_left fun h => by
    rw [h, AddSubgroup.card_bot] at hL
    exact hp.one_lt.ne hL
  have hmem := mem_zmultiples_of_prime_card hL (g := (⟨w, hw⟩ : L))
    (g' := (⟨γ * w, hγ w hw⟩ : L)) (fun h => hw0 (congrArg Subtype.val h))
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hn' : (n : GaloisField p 2) * w = γ * w := by
    simpa only [AddSubgroup.coe_zsmul, zsmul_eq_mul] using congrArg Subtype.val hn
  rw [mem_bot_iff_intCast p (GaloisField p 2)]
  exact ⟨n, mul_right_cancel₀ hw0 hn'⟩

theorem not_forall_mul_mem_of_card_eq (hp2 : p ≠ 2) (hμ : orderOf μ = p ^ 2 - 1) {k : ℕ}
    (hk0 : 0 < k) (hk : k < (p + 1) / 2) (L : AddSubgroup (GaloisField p 2))
    (hL : Nat.card L = p) : ¬ ∀ w ∈ L, ((μ : GaloisField p 2) ^ 2) ^ k * w ∈ L :=
  fun h => sq_pow_notMem_bot hp2 hμ hk0 hk (mem_bot_of_mul_mem L hL h)

end Field

theorem exists_scalar_torus_element {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {B X : Subgroup G}
    (htorus : ∃ φ : Multiplicative (GaloisField p 2) ≃* X, ∀ μ : (GaloisField p 2)ˣ,
      ∃ t ∈ B, ∀ a, t * (φ a : G) * t⁻¹ =
        φ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a))) :
    ∃ (t : G) (lam : ℕ), t ∈ B ∧ t ∈ Subgroup.normalizer (X : Set G) ∧ ¬ p ∣ lam - 1 ∧
      0 < lam ∧ (∀ x ∈ X, t ^ ((p + 1) / 2) * x * (t ^ ((p + 1) / 2))⁻¹ = x ^ lam) ∧
      ∀ k, 0 < k → k < (p + 1) / 2 → ∀ Y : Subgroup G, Y ≤ X → Nat.card Y = p →
        t ^ k ∉ Subgroup.normalizer (Y : Set G) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨φ, htor⟩ := htorus
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hord : orderOf μ = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_units,
      GaloisField.card p 2 (by norm_num)]
  obtain ⟨t, htB, ht⟩ := htor μ
  have hc0 : (μ : GaloisField p 2) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero μ)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℕ,
      (lam : GaloisField p 2) = ((μ : GaloisField p 2) ^ 2) ^ ((p + 1) / 2) := by
    have h := sq_pow_half_mem_bot hp2 hord
    rw [← ZMod.fieldRange_castHom_eq_bot p] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a.val, by rw [← ha, ← map_natCast (ZMod.castHom (dvd_refl p) (GaloisField p 2)),
      ZMod.natCast_zmod_val]⟩
  have hord1 := orderOf_sq_pow_half hp2 hord
  have hlam0 : 0 < lam := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.cast_zero] at hlam
    exact pow_ne_zero _ hc0 hlam.symm
  have hlam1 : ¬ p ∣ lam - 1 := by
    intro hdvd
    have h1 : (lam : GaloisField p 2) = 1 := by
      have h := (CharP.cast_eq_zero_iff (GaloisField p 2) p (lam - 1)).mpr hdvd
      rw [Nat.cast_sub hlam0, Nat.cast_one, sub_eq_zero] at h
      exact h
    rw [hlam] at h1
    rw [orderOf_eq_one_iff.mpr h1] at hord1
    have := hp.two_le
    omega
  refine ⟨t, lam, htB, mem_normalizer_of_torus_conj φ hc0 ht, hlam1, hlam0, fun x hx => ?_,
    fun k hk0 hkm Y hYX hY hnorm => ?_⟩
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hxa : (φ a : G) = x := congrArg Subtype.val ha
    have hpow : Multiplicative.ofAdd ((lam : GaloisField p 2) * Multiplicative.toAdd a) =
        a ^ lam := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, toAdd_pow, nsmul_eq_mul]
    rw [← hxa, conj_pow_of_torus_conj φ ht, ← hlam, hpow, map_pow, Subgroup.coe_pow]
  · let L : AddSubgroup (GaloisField p 2) :=
      { carrier := {c | (φ (Multiplicative.ofAdd c) : G) ∈ Y}
        zero_mem' := by
          change (φ (Multiplicative.ofAdd 0) : G) ∈ Y
          rw [ofAdd_zero, map_one, Subgroup.coe_one]
          exact Y.one_mem
        add_mem' := fun {a b} ha hb => by
          change (φ (Multiplicative.ofAdd (a + b)) : G) ∈ Y
          rw [ofAdd_add, map_mul, Subgroup.coe_mul]
          exact Y.mul_mem ha hb
        neg_mem' := fun {a} ha => by
          change (φ (Multiplicative.ofAdd (-a)) : G) ∈ Y
          rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
          exact Y.inv_mem ha }
    have hLmem : ∀ c, c ∈ L ↔ (φ (Multiplicative.ofAdd c) : G) ∈ Y := fun c => Iff.rfl
    have hLcard : Nat.card L = p := by
      let e : L → Y := fun c => ⟨(φ (Multiplicative.ofAdd (c : GaloisField p 2)) : G), c.2⟩
      have he : Function.Bijective e := by
        refine ⟨fun c c' h => ?_, fun y => ?_⟩
        · have h0 : (φ (Multiplicative.ofAdd (c : GaloisField p 2)) : G) =
              (φ (Multiplicative.ofAdd (c' : GaloisField p 2)) : G) :=
            congrArg (fun y : Y => (y : G)) h
          exact Subtype.ext (Multiplicative.ofAdd.injective (φ.injective (Subtype.ext h0)))
        · obtain ⟨a, ha⟩ := φ.surjective ⟨y, hYX y.2⟩
          have hya : (φ a : G) = y := congrArg Subtype.val ha
          refine ⟨⟨Multiplicative.toAdd a, (hLmem _).mpr (by rw [ofAdd_toAdd, hya]; exact y.2)⟩, ?_⟩
          refine Subtype.ext ?_
          change (φ (Multiplicative.ofAdd (Multiplicative.toAdd a)) : G) = y
          rw [ofAdd_toAdd]
          exact hya
      exact (Nat.card_congr (Equiv.ofBijective e he)).trans hY
    refine not_forall_mul_mem_of_card_eq hp2 hord hk0 hkm L hLcard fun w hw => ?_
    have h := (Subgroup.mem_normalizer_iff.mp hnorm (φ (Multiplicative.ofAdd w))).mp
      ((hLmem w).mp hw)
    rw [conj_pow_of_torus_conj φ ht k, toAdd_ofAdd] at h
    exact (hLmem _).mpr h

end CFSG.AGLEmbeddingD2
