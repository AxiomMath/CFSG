module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28U
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4ElemDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Finkelstein

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {L T U₁ : Subgroup G} {f q : ℕ} {y d : G}

theorem Sec3.IsTorus.existsUnique_pow (hy : Sec3.IsTorus L T y) (hX : Sec3.Facts L T q)
    (h : Sec3 G L T) {a b : G} (ha : a ∈ gmsA L T) (hb : b ∈ gmsA L T) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : ∃! k : ℕ, k < q - 1 ∧ y ^ k * a * (y ^ k)⁻¹ = b := by
  have hord := hy.orderOf_aut hX h
  have hq := hX.four_le
  obtain ⟨m, hm⟩ := hy.trans a ha b hb ha1 hb1
  have hneg : ((hy.aut ^ (-(m : ℤ))) ⟨a, ha⟩ : G) = b := by
    rw [hy.aut_zpow_apply, ← hm, zpow_neg, inv_inv, zpow_natCast]
  have hkey : hy.aut ^ ((m * (q - 2)) % (q - 1)) = hy.aut ^ (-(m : ℤ)) := by
    rw [← hord, pow_mod_orderOf, zpow_neg, zpow_natCast, eq_inv_iff_mul_eq_one, ← pow_add]
    have : m * (q - 2) + m = m * (q - 1) := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    rw [this, pow_mul', ← hord, pow_orderOf_eq_one, one_pow]
  refine ⟨(m * (q - 2)) % (q - 1), ⟨Nat.mod_lt _ (by omega), ?_⟩, ?_⟩
  · rw [← hy.aut_pow_apply _ ⟨a, ha⟩, hkey, hneg]
  · rintro k ⟨hk, hkb⟩
    set k₀ := (m * (q - 2)) % (q - 1) with hk₀
    have hk₀lt : k₀ < q - 1 := Nat.mod_lt _ (by omega)
    have hk₀b : y ^ k₀ * a * (y ^ k₀)⁻¹ = b := by
      rw [← hy.aut_pow_apply _ ⟨a, ha⟩, hkey, hneg]
    have hfix : y ^ ((k₀ : ℤ) - k) * a * (y ^ ((k₀ : ℤ) - k))⁻¹ = a := by
      have hc : y ^ ((k₀ : ℤ) - k) = (y ^ k)⁻¹ * y ^ k₀ := by
        rw [sub_eq_neg_add, zpow_add, zpow_neg, zpow_natCast, zpow_natCast]
      rw [hc]
      calc (y ^ k)⁻¹ * y ^ k₀ * a * ((y ^ k)⁻¹ * y ^ k₀)⁻¹
          = (y ^ k)⁻¹ * (y ^ k₀ * a * (y ^ k₀)⁻¹) * y ^ k := by group
        _ = (y ^ k)⁻¹ * (y ^ k * a * (y ^ k)⁻¹) * y ^ k := by rw [hk₀b, hkb]
        _ = a := by group
    have h1 : hy.aut ^ ((k₀ : ℤ) - k) = 1 := by
      apply MulEquiv.ext
      intro c
      apply Subtype.ext
      change ((hy.aut ^ ((k₀ : ℤ) - k)) c : G) = c
      rw [hy.aut_zpow_apply]
      exact hy.eq_of_conj_eq ha ha1 hfix c.2
    rw [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at h1
    have h2 := pow_inj_mod.mp h1
    rw [hord, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk₀lt] at h2
    exact h2.symm

namespace Push28Out

omit [Finite G] in
theorem pow_conj_A (hO : Push28Out L T U₁ q y d) (hy : Sec3.IsTorus L T y) (k : ℕ) :
    ∀ a ∈ gmsA L T, d ^ k * a * (d ^ k)⁻¹ = y ^ k * a * (y ^ k)⁻¹ := by
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    have hka : y ^ k * a * (y ^ k)⁻¹ ∈ gmsA L T :=
      (mem_normalizer_iff.mp (pow_mem hy.mem_normalizer_gmsA k) a).mp ha
    calc d ^ (k + 1) * a * (d ^ (k + 1))⁻¹ = d * (d ^ k * a * (d ^ k)⁻¹) * d⁻¹ := by group
      _ = y * (y ^ k * a * (y ^ k)⁻¹) * y⁻¹ := by rw [ih a ha, hO.conj_A _ hka]
      _ = y ^ (k + 1) * a * (y ^ (k + 1))⁻¹ := by group

theorem lt (hO : Push28Out L T U₁ (2 ^ f) y d) (hX : Sec3.Facts L T (2 ^ f)) (h : Sec3 G L T)
    (hf : 3 ≤ f) : gmsA L T < U₁ := by
  refine lt_of_le_of_ne hO.A_le fun heq => ?_
  have h1 := hO.card
  rw [← heq, (hX.sylow h).1] at h1
  have h8 : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  nlinarith

theorem finkelstein
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) (hX : Sec3.Facts L T (2 ^ f))
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f) {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1) :
    ((∃ k : ℕ, 1 ≤ k ∧ Nonempty (U₁ ≃* (Fin f → Multiplicative (ZMod (2 ^ k))))) ∧
      ((∀ u ∈ U₁, t * u * t⁻¹ = u⁻¹) ∨ ∀ u ∈ U₁, (u * t) ^ 2 = 1 → u ∈ gmsA L T)) ∨
    IsElemAbelian 2 U₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  have hq := hX.four_le
  have htt : t ^ 2 = 1 := hVel.2 t (mem_sup_right ht)
  have htt2 : t * t = 1 := by rw [← sq]; exact htt
  have htN : t ∈ normalizer (U₁ : Set G) := hO.le_normalizer (mem_inf.mp ht).1
  set τ : MulAut U₁ := U₁.normalizerMonoidHom ⟨t, htN⟩ with hτ
  set δ : MulAut U₁ := U₁.normalizerMonoidHom ⟨d, hO.mem_normalizer⟩ with hδ
  have hτa : ∀ u : U₁, ((τ u : U₁) : G) = t * u * t⁻¹ := fun u =>
    normalizerMonoidHom_apply_apply_coe _ _ u
  have hδa : ∀ (k : ℕ) (u : U₁), (((δ ^ k) u : U₁) : G) = d ^ k * u * (d ^ k)⁻¹ := by
    intro k u
    rw [hδ, ← map_pow, normalizerMonoidHom_apply_apply_coe]
    rfl
  have hcard : Nat.card U₁ = 2 ^ (2 * f) := by rw [hO.card, ← pow_mul, mul_comm]
  have hτ2 : τ ^ 2 = 1 := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    show (((τ ^ 2) u : U₁) : G) = u
    rw [sq, MulAut.mul_apply, hτa, hτa]
    calc t * (t * ↑u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
      _ = u := by rw [htt2]; group
  have hcomm : τ * δ = δ * τ := by
    have hdt : (⟨t, htN⟩ : normalizer (U₁ : Set G)) * ⟨d, hO.mem_normalizer⟩ =
        ⟨d, hO.mem_normalizer⟩ * ⟨t, htN⟩ := Subtype.ext (by
      show t * d = d * t
      have := hO.conj_T₀ t ht
      calc t * d = d * t * d⁻¹ * d := by rw [this]
        _ = d * t := by group)
    rw [hτ, hδ, ← map_mul, ← map_mul, hdt]
  have hord : orderOf δ = 2 ^ f - 1 := by
    rw [orderOf_eq_iff (by omega)]
    refine ⟨MulEquiv.ext fun u => Subtype.ext ?_, fun m hm hm0 h1 => ?_⟩
    · rw [hδa, hO.pow_conj u u.2]
      rfl
    · have hA : ∀ a ∈ gmsA L T, y ^ m * a * (y ^ m)⁻¹ = a := by
        intro a ha
        have h2 : (((δ ^ m) ⟨a, hO.A_le ha⟩ : U₁) : G) = a := by rw [h1]; rfl
        rw [hδa] at h2
        rw [← hO.pow_conj_A hy m a ha]
        exact h2
      have h3 := orderOf_dvd_of_pow_eq_one ((hy.aut_pow_eq_one_iff m).mpr hA)
      rw [hy.orderOf_aut hX h] at h3
      exact absurd (Nat.le_of_dvd hm0 h3) (by omega)
  have hreg : ∀ a b : U₁, τ a = a → τ b = b → a ≠ 1 → b ≠ 1 →
      ∃! k : ℕ, k < 2 ^ f - 1 ∧ (δ ^ k) a = b := by
    intro a b ha hb ha1 hb1
    have hmemA : ∀ c : U₁, τ c = c → (c : G) ∈ gmsA L T := by
      intro c hc
      rw [← hO.centralizer_eq t ht ht1]
      refine mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have := congrArg Subtype.val hc
      rw [hτa] at this
      calc (c : G) * t = t * c * t⁻¹ * t := by rw [this]
        _ = t * c := by group
    have haA := hmemA a ha
    have hbA := hmemA b hb
    have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
    have hb1' : (b : G) ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    refine (existsUnique_congr fun k => ?_).mp (hy.existsUnique_pow hX h haA hbA ha1' hb1')
    rw [← hO.pow_conj_A hy k _ haA, ← hδa k a]
    constructor
    · rintro ⟨hk, hk'⟩
      exact ⟨hk, Subtype.ext hk'⟩
    · rintro ⟨hk, hk'⟩
      exact ⟨hk, congrArg Subtype.val hk'⟩
  rcases finkelsteinLemmaSq U₁ f (by omega) hcard τ δ hτ2 hcomm hord hreg with h3 | h4 | h5
  · obtain ⟨hk, hinv⟩ := h3
    refine Or.inl ⟨hk, Or.inl fun u hu => ?_⟩
    have := congrArg Subtype.val (hinv ⟨u, hu⟩)
    rw [hτa] at this
    exact this
  · obtain ⟨hk, hconj⟩ := h4
    refine Or.inl ⟨hk, Or.inr fun u hu hut => ?_⟩
    have h6 : (⟨u, hu⟩ : U₁) * τ ⟨u, hu⟩ = 1 := by
      apply Subtype.ext
      show u * ((τ ⟨u, hu⟩ : U₁) : G) = 1
      rw [hτa]
      calc u * (t * u * t⁻¹) = (u * t) * (u * t) * (t * t)⁻¹ := by group
        _ = 1 := by rw [← sq (u * t), hut, htt2]; group
    obtain ⟨v, hv⟩ := hconj _ h6
    have h7 : u = (v : G) * (t * v * t⁻¹)⁻¹ := by
      have := congrArg Subtype.val hv
      rw [coe_mul, coe_inv, hτa] at this
      exact this
    rw [h7]
    have h8 := inv_mem (hO.comm_mem t ht v v.2)
    have e1 : (t * ↑v * t⁻¹ * (↑v)⁻¹)⁻¹ = ↑v * (t * ↑v * t⁻¹)⁻¹ := by group
    rwa [e1] at h8
  · obtain ⟨hc, hsq2, -, -⟩ := h5
    refine Or.inr ⟨⟨⟨hc⟩⟩, fun x hx => ?_⟩
    have := congrArg Subtype.val (hsq2 ⟨x, hx⟩)
    simpa using this

theorem sec4
    (hO : Push28Out L T U₁ (2 ^ f) y d) (hy : Sec3.IsTorus L T y) (hX : Sec3.Facts L T (2 ^ f))
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f) :
    Sec4Homo L T U₁ (2 ^ f) ∨ Sec4Elem L T U₁ (2 ^ f) := by
  obtain ⟨-, hA₁sq, -⟩ := hX.sylow h
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.T₀_ne_bot
  have ht₀1' : t₀ ≠ 1 := fun h1 => ht₀1 (Subtype.ext h1)
  have hlt := hO.lt hX h hf
  have hbase : (∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) → Sec4Base L T U₁ := fun hc =>
    { A_le := hO.A_le
      mul_comm := hc
      le_normalizer := hO.le_normalizer
      inf_eq_bot := hO.inf_eq_bot
      centralizer_eq := hO.centralizer_eq
      comm_mem := hO.comm_mem }
  rcases hO.finkelstein hy hX h hF hf ht₀ ht₀1' with ⟨⟨k, -, ⟨eU⟩⟩, -⟩ | hel
  · left
    have hc : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := by
      intro a ha b hb
      have h1 : eU (⟨a, ha⟩ * ⟨b, hb⟩) = eU (⟨b, hb⟩ * ⟨a, ha⟩) := by
        rw [map_mul, map_mul, mul_comm]
      exact congrArg Subtype.val (eU.injective h1)
    have hk2 : k = 2 := by
      have h1 : Nat.card U₁ = (2 ^ k) ^ f := by
        rw [Nat.card_congr eU.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin f),
          Fintype.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      rw [hO.card, ← pow_mul, ← pow_mul] at h1
      have h2 := Nat.pow_right_injective (le_refl 2) h1
      have hf0 : 0 < f := by omega
      exact Nat.eq_of_mul_eq_mul_left hf0 (by linarith)
    have homega : ∀ u ∈ U₁, u ^ 2 = 1 → u ∈ gmsA L T := by
      subst hk2
      intro u hu hu2
      set x := eU ⟨u, hu⟩ with hx
      have hx2 : x ^ 2 = 1 := by
        rw [hx, ← map_pow]
        have : (⟨u, hu⟩ : U₁) ^ 2 = 1 := Subtype.ext hu2
        rw [this, map_one]
      have key : ∀ a : ZMod (2 ^ 2), a + a = 0 → ∃ b : ZMod (2 ^ 2), b + b = a := by decide
      have hxi : ∀ i, Multiplicative.toAdd (x i) + Multiplicative.toAdd (x i) = 0 := by
        intro i
        have := congrFun hx2 i
        rw [Pi.pow_apply, Pi.one_apply, pow_two (x i)] at this
        rw [← toAdd_mul, this, toAdd_one]
      choose b hb using fun i => key _ (hxi i)
      have hz : (fun i => Multiplicative.ofAdd (b i)) * (fun i => Multiplicative.ofAdd (b i)) =
          x := by
        funext i
        show Multiplicative.ofAdd (b i) * Multiplicative.ofAdd (b i) = x i
        rw [← ofAdd_add, hb i, ofAdd_toAdd]
      set w := eU.symm (fun i => Multiplicative.ofAdd (b i)) with hw
      have hww : w * w = ⟨u, hu⟩ :=
        eU.injective (by rw [map_mul, hw, MulEquiv.apply_symm_apply, hz])
      have hww' : (w : G) * w = u := congrArg Subtype.val hww
      rw [← hww']
      exact hO.sq_mem w w.2
    exact
      { toSec4Base := hbase hc
        lt := hlt
        exp4 := fun u hu => by
          have h1 : u ^ 4 = (u * u) ^ 2 := by
            rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq u]
          rw [h1]
          exact hA₁sq _ (hO.sq_mem u hu)
        omega := homega
        card := hO.card
        dichotomy := fun t ht ht1 => by
          rcases hO.finkelstein hy hX h hF hf ht ht1 with ⟨-, hd'⟩ | hel
          · exact hd'
          · exfalso
            have hle : U₁ ≤ gmsA L T := fun u hu => homega u hu (hel.2 u hu)
            exact hlt.ne' (le_antisymm hle hO.A_le)
        sylow := hO.sylow }
  · right
    exact
      { toSec4Base := hbase fun a ha b hb =>
          congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        lt := hlt
        elem := hel
        card := hO.card
        sylow := hO.sylow }

end Push28Out

end CFSG.ComponentClassification.GMS78
