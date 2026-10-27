module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCentralizerBasic
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartNormalizer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

section Bender

variable {K : Type} [Group K] [Finite K]

theorem rankOne_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) :=
  (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one

theorem exists_dihedral_autCentralizer_unitary {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) :
    ∃ χ : autCentralizer (rootCenter (Q : Subgroup K)) →* DihedralGroup (2 ^ n + 1),
      ∀ γ, χ γ = 1 ↔ (γ : MulAut K) ∈ (Q : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
  obtain ⟨D, hinf, hsup, hnorm, -, ⟨eD⟩⟩ := h.lemma_3_6_c_unitary Q
  obtain ⟨π, -, hπ⟩ := exists_proj_of_complement hinf hsup hnorm
  refine ⟨eD.toMonoidHom.comp π, fun γ => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hπ]

theorem exists_odd_centralizer_rootCenter_unitary
    {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K) :
    ∃ k₀ ∈ centralizer (rootCenter (Q : Subgroup K) : Set K), k₀ ∉ (Q : Subgroup K) ∧
      ∃ b : ℕ, Odd b ∧ k₀ ^ b = 1 := by
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  set K₀ := fixCartan (Q : Subgroup K) t₀ with hK₀
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ d ∈ K₀, d ≠ 1 := by
    rcases h.cases' with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨-, he, hn⟩
    · exact absurd hi (by norm_num)
    · exact absurd hi (by norm_num)
    · have hcard : Nat.card K₀ = e := hc.card_fixCartan
      have h2 : 2 ≤ e := he ▸ two_le_unitary_e hn
      by_contra hne
      push Not at hne
      have : K₀ = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hne x hx)
      rw [this, card_bot] at hcard
      omega
  have hd₀C : d₀ ∈ cartan (Q : Subgroup K) t₀ := fixCartan_le_cartan _ _ hd₀
  refine ⟨d₀, ?_, fun hd₀Q => hd₀1 ?_, Nat.card (cartan (Q : Subgroup K) t₀),
    hc.odd_card_cartan, ?_⟩
  · rw [hc.centralizer_rootCenter_eq]
    exact mem_sup_right hd₀
  · have h1 : d₀ ∈ (Q : Subgroup K) ⊓ cartan (Q : Subgroup K) t₀ := mem_inf.mpr ⟨hd₀Q, hd₀C⟩
    rw [hc.inf_eq, mem_bot] at h1
    exact h1
  · exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hd₀C)

omit [Finite K] in
theorem conj_mem_autCentralizer {V : Subgroup K} {k : K} (hk : k ∈ centralizer (V : Set K)) :
    MulAut.conj k ∈ autCentralizer V := by
  intro z hz
  rw [MulAut.conj_apply, ← mem_centralizer_iff.mp hk z hz, mul_inv_cancel_right]

theorem le_map_conj_of_isPGroup_unitary {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {X : Subgroup (MulAut K)}
    (hXC : X ≤ autCentralizer (rootCenter (Q : Subgroup K))) (hX : IsPGroup 2 X)
    (hXn : ∀ k ∈ centralizer (rootCenter (Q : Subgroup K) : Set K),
      MulAut.conj k ∈ normalizer (X : Set (MulAut K))) :
    X ≤ (Q : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
  obtain ⟨χ, hχ⟩ := exists_dihedral_autCentralizer_unitary h Q
  obtain ⟨k₀, hk₀C, hk₀Q, b, hb, hk₀b⟩ := exists_odd_centralizer_rootCenter_unitary h Q
  have hn : 1 ≤ n := by have := h.two_le.2; omega
  set κ : autCentralizer (rootCenter (Q : Subgroup K)) := ⟨MulAut.conj k₀,
    conj_mem_autCentralizer hk₀C⟩ with hκ
  have hκ1 : χ κ ≠ 1 := by
    intro h1
    obtain ⟨y, hy, hyk⟩ := (hχ κ).mp h1
    have hyk' : y = k₀ := by
      have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
        rw [injective_iff_map_eq_one]
        intro g hg
        have hg' : g ∈ center K := by
          rw [mem_center_iff]
          intro x
          have := congrArg (fun σ : MulAut K => σ x) hg
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc x * g = (g * x * g⁻¹) * g := by rw [this]
            _ = g * x := by group
        rw [h.center_eq_bot, mem_bot] at hg'
        exact hg'
      exact hinj hyk
    exact hk₀Q (hyk' ▸ hy)
  have hκb : (χ κ) ^ b = 1 := by
    rw [← map_pow]
    have : κ ^ b = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hκ]
      change (MulAut.conj k₀) ^ b = 1
      rw [← map_pow, hk₀b, map_one])
    rw [this, map_one]
  intro γ hγ
  set γ' : autCentralizer (rootCenter (Q : Subgroup K)) := ⟨γ, hXC hγ⟩ with hγ'
  have h2pow : ∀ δ ∈ X, ∀ hδ : δ ∈ autCentralizer (rootCenter (Q : Subgroup K)),
      ∃ k : ℕ, (χ ⟨δ, hδ⟩) ^ (2 ^ k) = 1 := by
    intro δ hδX hδ
    obtain ⟨k, hk⟩ := hX ⟨δ, hδX⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨δ, hδ⟩ : autCentralizer (rootCenter (Q : Subgroup K))) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  obtain ⟨a, ha⟩ := h2pow γ hγ (hXC hγ)
  have hcomm : ((⁅γ', κ⁆ : autCentralizer (rootCenter (Q : Subgroup K))) : MulAut K) ∈ X := by
    have hκX := hXn k₀ hk₀C
    have h1 : MulAut.conj k₀ * γ⁻¹ * (MulAut.conj k₀)⁻¹ ∈ X :=
      (mem_normalizer_iff.mp hκX γ⁻¹).mp (inv_mem hγ)
    have e : ((⁅γ', κ⁆ : autCentralizer (rootCenter (Q : Subgroup K))) : MulAut K) =
        γ * (MulAut.conj k₀ * γ⁻¹ * (MulAut.conj k₀)⁻¹) := by
      rw [commutatorElement_def, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv, hγ', hκ]
      group
    rw [e]
    exact mul_mem hγ h1
  obtain ⟨c, hc⟩ := h2pow _ hcomm (⁅γ', κ⁆ : autCentralizer (rootCenter (Q : Subgroup K))).2
  rw [Subtype.coe_eta, map_commutatorElement] at hc
  rcases dihedral_eq_one_or_eq_one_of_commutator (rankOne_odd_two_pow_add_one hn) ha hκb hb hc with
    h1 | h1
  · exact (hχ γ').mp h1
  · exact absurd h1 hκ1

omit [Finite K] in
theorem forall_apply_eq_of_pow_odd {Q Z : Subgroup K} (hZ2 : ∀ z ∈ Z, z * z = 1) {δ : MulAut K}
    (hδZ : ∀ z ∈ Z, δ z = z) (hδQ : ∀ x ∈ Q, x⁻¹ * δ x ∈ Z) {m : ℕ} (hm : Odd m)
    (hδm : δ ^ m = 1) : ∀ x ∈ Q, δ x = x := by
  intro x hx
  set z := x⁻¹ * δ x with hz
  have hzZ : z ∈ Z := hδQ x hx
  have hδx : δ x = x * z := by rw [hz]; group
  have hpow : ∀ k : ℕ, (δ ^ k) x = x * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hδx, hδZ z hzZ, pow_succ']
      group
  have h1 := hpow m
  rw [hδm, MulAut.one_apply] at h1
  have hzm : z ^ m = 1 := by
    have := congrArg (fun y => x⁻¹ * y) h1
    simpa using this.symm
  obtain ⟨j, rfl⟩ := hm
  have hz1 : z = 1 := by
    rw [pow_succ, pow_mul, sq, hZ2 z hzZ, one_pow, one_mul] at hzm
    exact hzm
  rw [hδx, hz1, mul_one]

theorem mem_map_conj_of_forall_mem_rootCenter_unitary {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {γ : MulAut K}
    (hγ : γ ∈ autCentralizer (rootCenter (Q : Subgroup K)))
    (hγQ : ∀ x ∈ (Q : Subgroup K), x⁻¹ * γ x ∈ rootCenter (Q : Subgroup K)) :
    γ ∈ (Q : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
  classical
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  set Z := rootCenter (Q : Subgroup K) with hZ
  have hZQ : Z ≤ (Q : Subgroup K) := rootCenter_le _
  have hZc : ∀ z ∈ Z, ∀ y ∈ (Q : Subgroup K), z * y = y * z := fun z hz y hy =>
    ((mem_rootCenter_iff.mp hz).2 y hy).symm
  have hnormQ : ∀ δ ∈ autCentralizer Z, ∀ x ∈ (Q : Subgroup K), δ x ∈ (Q : Subgroup K) :=
    fun δ hδ => h.mem_of_centralizes_rootCenter Q δ hδ
  let W : Subgroup (MulAut K) :=
    { carrier := {δ | δ ∈ autCentralizer Z ∧ ∀ x ∈ (Q : Subgroup K), x⁻¹ * δ x ∈ Z}
      mul_mem' := by
        rintro δ₁ δ₂ ⟨h₁, h₁Q⟩ ⟨h₂, h₂Q⟩
        refine ⟨mul_mem h₁ h₂, fun x hx => ?_⟩
        have e : x⁻¹ * (δ₁ * δ₂) x = x⁻¹ * δ₁ x * (x⁻¹ * δ₂ x) := by
          rw [MulAut.mul_apply]
          have hδ₂ : δ₂ x = x * (x⁻¹ * δ₂ x) := by group
          rw [hδ₂, map_mul, h₁ _ (h₂Q x hx)]
          group
        rw [e]
        exact mul_mem (h₁Q x hx) (h₂Q x hx)
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      inv_mem' := by
        rintro δ ⟨hδ, hδQ⟩
        refine ⟨inv_mem hδ, fun x hx => ?_⟩
        have hy : δ⁻¹ x ∈ (Q : Subgroup K) := hnormQ δ⁻¹ (inv_mem hδ) x hx
        have h1 := hδQ _ hy
        have e : δ (δ⁻¹ x) = x := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        rw [e] at h1
        have e2 : x⁻¹ * δ⁻¹ x = ((δ⁻¹ x)⁻¹ * x)⁻¹ := by group
        rw [e2]
        exact inv_mem h1 }
  have hWC : W ≤ autCentralizer Z := fun δ hδ => hδ.1
  have hWp : IsPGroup 2 W := by
    intro δ
    have hord : orderOf (δ : MulAut K) ≠ 0 := (isOfFinOrder_of_finite (δ : MulAut K)).orderOf_pos.ne'
    obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd hord
    refine ⟨a, Subtype.ext ?_⟩
    set δ' := (δ : MulAut K) ^ (2 ^ a) with hδ'
    have hδ'W : δ' ∈ W := pow_mem δ.2 _
    have hδ'm : δ' ^ m = 1 := by
      rw [hδ', ← pow_mul, ← hdec, pow_orderOf_eq_one]
    have hfix := forall_apply_eq_of_pow_odd (fun z hz => hc.center_sq z hz)
      hδ'W.1 hδ'W.2 hm hδ'm
    obtain ⟨r, hr, hδ'r⟩ := h.lemma_3_6_a Q δ' hfix
    have hδ'2 : δ' ^ 2 = 1 := by
      ext y
      rw [sq, MulAut.mul_apply, hδ'r, hδ'r, MulAut.one_apply]
      have hrr : r * r = 1 := hc.center_sq r hr
      calc r * (r * y * r⁻¹) * r⁻¹ = (r * r) * y * (r * r)⁻¹ := by group
        _ = y := by rw [hrr]; group
    have hd : orderOf δ' ∣ Nat.gcd 2 m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hδ'2) (orderOf_dvd_of_pow_eq_one hδ'm)
    have hg : Nat.gcd 2 m = 1 := (Nat.coprime_two_left.mpr hm)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    simpa [hδ'] using hd
  have hWn : ∀ k ∈ centralizer (Z : Set K), MulAut.conj k ∈ normalizer (W : Set (MulAut K)) := by
    intro k hk
    have hkB : k ∈ borel (Q : Subgroup K) := by
      rw [hc.centralizer_rootCenter_eq] at hk
      exact sup_le (le_borel _) ((fixCartan_le_cartan _ _).trans (cartan_le_borel _ _)) hk
    have hconjW : ∀ k ∈ centralizer (Z : Set K), k ∈ borel (Q : Subgroup K) →
        ∀ δ ∈ W, MulAut.conj k * δ * (MulAut.conj k)⁻¹ ∈ W := by
      intro k hk hkB δ hδ
      refine ⟨mul_mem (mul_mem (conj_mem_autCentralizer hk) hδ.1)
        (inv_mem (conj_mem_autCentralizer hk)), fun x hx => ?_⟩
      have hx' : k⁻¹ * x * k ∈ (Q : Subgroup K) := (mem_normalizer_iff''.mp hkB x).mp hx
      have h1 := hδ.2 _ hx'
      set z := (k⁻¹ * x * k)⁻¹ * δ (k⁻¹ * x * k) with hzdef
      have hδx : δ (k⁻¹ * x * k) = k⁻¹ * x * k * z := by rw [hzdef]; group
      have hkz : k * z * k⁻¹ = z := by
        rw [← mem_centralizer_iff.mp hk z h1, mul_inv_cancel_right]
      have e : x⁻¹ * (MulAut.conj k * δ * (MulAut.conj k)⁻¹) x = z := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
          hδx, MulAut.conj_apply]
        calc x⁻¹ * (k * (k⁻¹ * x * k * z) * k⁻¹) = x⁻¹ * x * (k * z * k⁻¹) := by group
          _ = z := by rw [hkz]; group
      rw [e]
      exact h1
    refine mem_normalizer_iff.mpr fun δ => ⟨fun hδ => hconjW k hk hkB δ hδ, fun hδ => ?_⟩
    have hk' : k⁻¹ ∈ centralizer (Z : Set K) := inv_mem hk
    have h1 := hconjW k⁻¹ hk' (inv_mem hkB) _ hδ
    rw [map_inv] at h1
    simpa [mul_assoc] using h1
  exact le_map_conj_of_isPGroup_unitary h Q hWC hWp hWn ⟨hγ, hγQ⟩

end Bender

end CFSG.SeitzReduction.RankOne
