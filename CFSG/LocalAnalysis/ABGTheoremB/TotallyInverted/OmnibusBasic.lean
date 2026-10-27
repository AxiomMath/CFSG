module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusSetting

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Omnibus

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

section Signalizers

theorem mem_signalizersPerm (hσ : σ.IsValid) (Δ : Data σ r) {H R : Subgroup G} (hRH : R ≤ H)
    (hR : IsPGroup r R) (hTR : σ.T ≤ Subgroup.normalizer (R : Set G))
    (hperm : (R : Set G) * σ.C = σ.C * R) : R ∈ signalizersPerm H σ.T σ.C r := by
  refine ⟨⟨hRH, hR, hTR, ?_⟩, hperm⟩
  rw [inf_comm]
  exact inf_eq_bot_of_two_odd (T_isPGroup hσ) (odd_card_of_isPGroup Δ.prime Δ.ne_two hR)

theorem exists_le_mem_maximals {𝓢 : Set (Subgroup G)} {R : Subgroup G} (hR : R ∈ 𝓢) :
    ∃ R' ∈ maximals 𝓢, R ≤ R' := by
  obtain ⟨R', hRR', hmax⟩ := 𝓢.toFinite.exists_le_maximal hR
  exact ⟨R', ⟨hmax.prop, fun R'' hR'' hle => le_antisymm (hmax.2 hR'' hle) hle⟩, hRR'⟩

omit [Finite G] in
theorem mem_maximals_of_le {H H' U : Subgroup G}
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) (hUH' : U ≤ H') (hH' : H' ≤ H) :
    U ∈ maximals (signalizersPerm H' σ.T σ.C r) := by
  obtain ⟨⟨⟨-, hUp, hTU, hUT⟩, hperm⟩, hmax⟩ := hU
  refine ⟨⟨⟨hUH', hUp, hTU, hUT⟩, hperm⟩, fun R hR hle => hmax R ?_ hle⟩
  obtain ⟨⟨hRH, hRp, hTR, hRT⟩, hRperm⟩ := hR
  exact ⟨⟨hRH.trans hH', hRp, hTR, hRT⟩, hRperm⟩

end Signalizers

section Parts

theorem inf_Ns_mem_signalizersPerm (hσ : σ.IsValid) {H H' U : Subgroup G}
    (hU : U ∈ signalizersPerm H σ.T σ.C r) (i : Fin 3) (hH' : U ⊓ σ.Ns i ≤ H') :
    U ⊓ σ.Ns i ∈ signalizersPerm H' σ.T σ.C r := by
  obtain ⟨⟨-, hUp, hTU, hUT⟩, hperm⟩ := hU
  refine ⟨⟨hH', hUp.to_le inf_le_left,
    fun t ht => mem_normalizer_inf (hTU ht) (T_le_normalizer_Ns hσ i ht), ?_⟩,
    inf_mul_comm_of_le (C_le_Ns i) hperm⟩
  rw [eq_bot_iff, ← hUT]
  exact inf_le_inf_right _ inf_le_left

theorem mem_centralizer_F₀_of_odd (Δ : Data σ r) {g : G}
    (hgF : g ∈ Subgroup.normalizer (σ.F₀ : Set G))
    (hgC : g ∈ σ.C) (hodd : Odd (orderOf g)) :
    g ∈ Subgroup.centralizer (σ.F₀ : Set G) := by
  have key : ∀ k : ℕ, ∀ a ∈ σ.F₀, a ^ 2 ^ k = 1 → g * a * g⁻¹ = a := by
    intro k
    induction k with
    | zero =>
      intro a _ ha
      rw [pow_zero, pow_one] at ha
      rw [ha]
      group
    | succ k ih =>
      intro a ha ha2
      set b := g * a * g⁻¹ with hb
      have hbF : b ∈ σ.F₀ := (Subgroup.mem_normalizer_iff.mp hgF a).mp ha
      have ha2F : a ^ 2 ∈ σ.F₀ := σ.F₀.pow_mem ha 2
      have hsq : g * a ^ 2 * g⁻¹ = a ^ 2 :=
        ih _ ha2F (by rw [← pow_mul, ← pow_succ']; exact ha2)
      have hb2 : b ^ 2 = a ^ 2 := by
        rw [hb, show (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group, hsq]
      set t := b * a⁻¹ with ht
      have htF : t ∈ σ.F₀ := σ.F₀.mul_mem hbF (σ.F₀.inv_mem ha)
      have hcomm : a⁻¹ * b = b * a⁻¹ := Δ.F₀_abelian _ (σ.F₀.inv_mem ha) _ hbF
      have ht2 : t ^ 2 = 1 := by
        rw [ht, pow_two, show b * a⁻¹ * (b * a⁻¹) = b * (a⁻¹ * b) * a⁻¹ by group, hcomm,
          show b * (b * a⁻¹) * a⁻¹ = b ^ 2 * (a ^ 2)⁻¹ by rw [pow_two, pow_two]; group, hb2,
          mul_inv_cancel]
      have htT : t ∈ σ.T := Δ.F₀_omega t htF ht2
      have hgt : g * t * g⁻¹ = t := by
        rw [comm_of_mem_C hgC htT |>.symm]
        group
      have hiter : ∀ j : ℕ, g ^ j * a * (g ^ j)⁻¹ = t ^ j * a := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ', show g * g ^ j * a * (g * g ^ j)⁻¹ = g * (g ^ j * a * (g ^ j)⁻¹) * g⁻¹ by
            group, ihj, show g * (t ^ j * a) * g⁻¹ = (g * t * g⁻¹) ^ j * (g * a * g⁻¹) by
            rw [conj_pow]; group, hgt, ← hb, show b = t * a by rw [ht]; group, pow_succ]
          group
      have hm := hiter (orderOf g)
      rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at hm
      have htm : t ^ orderOf g = 1 := by
        have := congrArg (· * a⁻¹) hm
        simpa using this.symm
      obtain ⟨q, hq⟩ := hodd
      have ht1 : t = 1 := by
        rw [hq, pow_succ, pow_mul, ht2, one_pow, one_mul] at htm
        exact htm
      have : b = a := by rw [show b = t * a by rw [ht]; group, ht1, one_mul]
      exact this
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨k, hk⟩ := Δ.F₀_sylow.isPGroup ⟨a, ha⟩
  have hk' : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have := key k a ha hk'
  calc a * g = g * a * g⁻¹ * g := by rw [this]
    _ = g * a := by group

theorem mem_centralizer_F₀_of_mem_C (Δ : Data σ r) {g : G}
    (hgF : g ∈ Subgroup.normalizer (σ.F₀ : Set G))
    (hgC : g ∈ σ.C) : g ∈ Subgroup.centralizer (σ.F₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hodd : Odd (orderOf (g ^ 2 ^ a)) := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hab]; exact dvd_mul_right _ _), hab,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hb
  have h1 : g ^ 2 ^ a ∈ Subgroup.centralizer (σ.F₀ : Set G) :=
    mem_centralizer_F₀_of_odd Δ (Subgroup.pow_mem _ hgF _) (Subgroup.pow_mem _ hgC _) hodd
  have hgb2 : IsPGroup 2 (Subgroup.zpowers (g ^ b)) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm,
      ← hab, pow_orderOf_eq_one, one_zpow]
  have hle : σ.F₀ ⊔ Subgroup.zpowers (g ^ b) ≤ σ.C :=
    sup_le F₀_le_C ((Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ hgC _))
  have hp : IsPGroup 2 (σ.F₀ ⊔ Subgroup.zpowers (g ^ b) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' Δ.F₀_sylow.isPGroup hgb2
      ((Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ hgF _))
  have heq := Δ.F₀_sylow.eq_of_le le_sup_left hle hp
  have h2F : g ^ b ∈ σ.F₀ := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have h2 : g ^ b ∈ Subgroup.centralizer (σ.F₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Δ.F₀_abelian f hf _ h2F
  have hcop : Nat.Coprime (2 ^ a) b :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hb)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hg : g = (g ^ 2 ^ a) ^ u * (g ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm _ u,
      mul_comm _ v]
    rw [show u * ((2 ^ a : ℕ) : ℤ) + v * (b : ℤ) = 1 by exact_mod_cast huv, zpow_one]
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ h1 _) (Subgroup.zpow_mem _ h2 _)

theorem mem_C_of_mem_sup (hσ : σ.IsValid) (Δ : Data σ r) {Y : Subgroup G} (hY : Odd (Nat.card Y))
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) (hperm : (Y : Set G) * σ.C = σ.C * Y)
    {n : G} (hn : n ∈ Y ⊔ σ.C) (hnF : n ∈ Subgroup.normalizer (σ.F₀ : Set G)) : n ∈ σ.C := by
  have hnT : n ∈ Subgroup.normalizer (σ.T : Set G) := by
    apply mem_normalizer_of_conj_le
    intro t ht
    have h1 : n * t * n⁻¹ ∈ σ.F₀ := (Subgroup.mem_normalizer_iff.mp hnF t).mp (T_le_F₀ hσ ht)
    apply Δ.F₀_omega _ h1
    have := T_isKleinFour hσ
    rw [show (n * t * n⁻¹) ^ 2 = n * (t * t) * n⁻¹ by rw [pow_two]; group,
      kleinFour_mul_self ht]
    group
  obtain ⟨y, hy, c, hc, rfl⟩ := mem_sup_of_mul_comm hperm hn
  have hyT : y ∈ Subgroup.normalizer (σ.T : Set G) := by
    have : y = y * c * c⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hnT (Subgroup.inv_mem _ (C_le_normalizer_T hc))
  have hyC : y ∈ σ.C := mem_centralizer_of_mem_normalizer (T_isPGroup hσ) hY hTY hy hyT
  exact σ.C.mul_mem hyC hc

theorem isSylowOf_F₀_sup (Δ : Data σ r) {Y : Subgroup G} (hY : Odd (Nat.card Y))
    (hperm : (Y : Set G) * σ.C = σ.C * Y) : IsSylowOf 2 σ.F₀ (Y ⊔ σ.C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hFp, hFidx⟩ := isSylowOf_iff.mp Δ.F₀_sylow
  refine isSylowOf_iff.mpr ⟨F₀_le_C.trans le_sup_right, hFp, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ F₀_le_C le_sup_right,
    relIndex_sup_of_mul_comm hperm]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hFidx h
  · exact (Nat.not_even_iff_odd.mpr (hY.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)))
      (even_iff_two_dvd.mpr h)

theorem hasNormalPComplement_sup (hσ : σ.IsValid) (Δ : Data σ r) {Y : Subgroup G}
    (hY : Odd (Nat.card Y))
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) (hperm : (Y : Set G) * σ.C = σ.C * Y) :
    CFSG.HasNormalPComplement 2 ↥(Y ⊔ σ.C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := Y ⊔ σ.C with hX
  obtain ⟨Q, hQ⟩ := isSylowOf_F₀_sup Δ hY hperm
  apply CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer 2 Q
  intro q hq
  refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hq, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hnF : (n : G) ∈ Subgroup.normalizer (σ.F₀ : Set G) := by
    apply mem_normalizer_of_conj_le
    intro f hf
    rw [← hQ] at hf ⊢
    obtain ⟨q', hq', rfl⟩ := hf
    exact ⟨n * q' * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn q').mp hq', rfl⟩
  have hnC : (n : G) ∈ σ.C := mem_C_of_mem_sup hσ Δ hY hTY hperm n.2 hnF
  have hcent := mem_centralizer_F₀_of_mem_C Δ hnF hnC
  have hqF : (q : G) ∈ σ.F₀ := by rw [← hQ]; exact ⟨q, hq, rfl⟩
  apply Subtype.ext
  exact ((Subgroup.mem_centralizer_iff.mp hcent) q hqF).symm

theorem isSylowOf_sup_of_perm (hσ : σ.IsValid) (Δ : Data σ r) {H U Y : Subgroup G}
    (hCH : σ.C ≤ H) (hYH : Y ≤ H) (hY : Odd (Nat.card Y))
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) (hperm : (Y : Set G) * σ.C = σ.C * Y)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) (hUY : U ≤ Y)
    (hV : ∀ V : Subgroup G, IsSylowOf r V (Y ⊔ σ.C) → U ≤ V →
      σ.T ≤ Subgroup.normalizer (V : Set G) → (V : Set G) * σ.C = σ.C * V) :
    IsSylowOf r U (Y ⊔ σ.C) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  set X : Subgroup G := Y ⊔ σ.C with hXdef
  have hX := hasNormalPComplement_sup hσ Δ hY hTY hperm
  set K : Subgroup G := oddCoreIn X with hKdef
  have hKodd : Odd (Nat.card K) := odd_card_oddCoreIn X
  have hTX : σ.T ≤ X := (σ.T_le_C hσ).trans le_sup_right
  have hTK : σ.T ≤ Subgroup.normalizer (K : Set G) := hTX.trans (le_normalizer_oddCoreIn X)
  obtain ⟨⟨⟨-, hUp, hTU, -⟩, -⟩, hmax⟩ := hU
  have hUK : U ≤ K := le_oddCoreIn_of_hasNormalPComplement hX (hUY.trans le_sup_left)
    (odd_card_of_isPGroup Δ.prime Δ.ne_two hUp)
  obtain ⟨V, hVK, hUV, hTV⟩ :=
    exists_isSylowOf_le_normalizer_of_le (T_isPGroup hσ) hKodd hTK hUK hUp hTU
  have hVX : IsSylowOf r V X := by
    obtain ⟨hVle, hVp, hVidx⟩ := isSylowOf_iff.mp hVK
    obtain ⟨k, hk⟩ := exists_relIndex_oddCoreIn_eq_two_pow hX
    have hk' : K.relIndex X = 2 ^ k := hk
    refine isSylowOf_iff.mpr ⟨hVle.trans (oddCoreIn_le X), hVp, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hVle (oddCoreIn_le X), hk']
    intro hdvd
    rcases (Nat.Prime.dvd_mul Δ.prime).mp hdvd with h | h
    · exact hVidx h
    · exact Δ.ne_two ((Nat.prime_dvd_prime_iff_eq Δ.prime Nat.prime_two).mp
        (Δ.prime.dvd_of_dvd_pow h))
  have hVmem : V ∈ signalizersPerm H σ.T σ.C r :=
    mem_signalizersPerm hσ Δ (hVX.le.trans (sup_le hYH hCH)) hVX.isPGroup hTV
      (hV V hVX hUV hTV)
  have hVU : V = U := hmax V hVmem hUV
  rw [← hVU]
  exact hVX

theorem isSylowOf_sup (hσ : σ.IsValid) (Δ : Data σ r) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) : IsSylowOf r U (U ⊔ σ.C) := by
  obtain ⟨⟨⟨hUH, hUp, hTU, -⟩, hperm⟩, -⟩ := id hU
  exact isSylowOf_sup_of_perm hσ Δ hCH hUH (odd_card_of_isPGroup Δ.prime Δ.ne_two hUp) hTU
    hperm hU le_rfl fun V hV hUV _ => mul_comm_of_le_of_le_sup hperm hUV hV.le

theorem isSylowOf_inf_C (hσ : σ.IsValid) (Δ : Data σ r) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) : IsSylowOf r (U ⊓ σ.C) σ.C := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨-, hUp, hUidx⟩ := isSylowOf_iff.mp (isSylowOf_sup hσ Δ hCH hU)
  have hperm := hU.1.2
  refine isSylowOf_iff.mpr ⟨inf_le_right, hUp.to_le inf_le_left, ?_⟩
  rwa [Subgroup.inf_relIndex_right, ← relIndex_sup_of_mul_comm hperm.symm, sup_comm]

theorem comp_eq_inf_block (Δ : Data σ r) {U R₀ Y : Subgroup G} {i : Fin 3}
    (hY : IsBlock σ r i Y) (hR₀C : R₀ ≤ σ.C) (hR₀p : IsPGroup r R₀) (hR₀U : R₀ ≤ U ⊓ σ.Ns i)
    (hUi : ((U ⊓ σ.Ns i : Subgroup G) : Set G) * σ.C = σ.C * (U ⊓ σ.Ns i : Subgroup G))
    (hle : U ⊓ σ.Ns i ≤ R₀ ⊔ Y) :
    ((U ⊓ σ.Ns i ⊓ Y : Subgroup G) : Set G) = comp σ U i ∧
      σ.C ≤ Subgroup.normalizer ((U ⊓ σ.Ns i ⊓ Y : Subgroup G) : Set G) := by
  have hR₀N : R₀ ≤ Subgroup.normalizer (Y : Set G) := hR₀C.trans hY.normalized
  have hRYp : IsPGroup r (R₀ ⊔ Y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hR₀p hY.isPGroup hR₀N
  have hRYodd : Odd (Nat.card (R₀ ⊔ Y : Subgroup G)) :=
    odd_card_of_isPGroup Δ.prime Δ.ne_two hRYp
  have hcoe : ((R₀ ⊔ Y : Subgroup G) : Set G) = R₀ * Y :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hR₀N
  refine ⟨?_, ?_⟩
  · ext u
    constructor
    · rintro ⟨⟨huU, huN⟩, huY⟩
      exact ⟨huU, mem_Ns_iff.mp huN, hY.inverted u huY⟩
    · rintro ⟨huU, hux, huinv⟩
      have huN : u ∈ σ.Ns i := mem_Ns_iff.mpr hux
      have hu : u ∈ ((R₀ ⊔ Y : Subgroup G) : Set G) := hle ⟨huU, huN⟩
      rw [hcoe] at hu
      obtain ⟨ρ, hρ, y, hy, hρy⟩ := hu
      have hρy' : ρ * y = u := hρy
      subst hρy'
      have hρC : ρ ∈ σ.C := hR₀C hρ
      have hxρ : σ.xs (i + 1) * ρ * (σ.xs (i + 1))⁻¹ = ρ := by
        rw [comm_of_mem_C hρC (xs_mem_T (i + 1))]
        group
      have hkey : y * ρ * y⁻¹ = ρ⁻¹ := by
        have h1 : σ.xs (i + 1) * (ρ * y) * (σ.xs (i + 1))⁻¹ = ρ * y⁻¹ := by
          rw [show σ.xs (i + 1) * (ρ * y) * (σ.xs (i + 1))⁻¹ =
            (σ.xs (i + 1) * ρ * (σ.xs (i + 1))⁻¹) * (σ.xs (i + 1) * y * (σ.xs (i + 1))⁻¹) by
            group, hxρ, hY.inverted y hy]
        rw [h1, mul_inv_rev] at huinv
        calc y * ρ * y⁻¹ = y * (ρ * y⁻¹) := by group
          _ = y * (y⁻¹ * ρ⁻¹) := by rw [huinv]
          _ = ρ⁻¹ := by group
      have hρ1 : ρ = 1 := eq_one_of_conj_eq_inv_of_odd hRYodd
        (Subgroup.mem_sup_left hρ) (Subgroup.inv_mem _ (Subgroup.mem_sup_right hy))
        (by rw [inv_inv]; exact hkey)
      subst hρ1
      rw [one_mul] at huU huN
      rw [one_mul]
      exact ⟨⟨huU, huN⟩, hy⟩
  · have heq : U ⊓ σ.Ns i ⊓ Y = (U ⊓ σ.Ns i ⊔ σ.C) ⊓ Y := by
      apply le_antisymm (inf_le_inf_right _ le_sup_left)
      rintro g ⟨hgUC, hgY⟩
      obtain ⟨c, hc, u, hu, rfl⟩ := mem_sup_of_mul_comm' hUi hgUC
      have hu' : u ∈ ((R₀ ⊔ Y : Subgroup G) : Set G) := hle hu
      rw [hcoe] at hu'
      obtain ⟨ρ, hρ, y, hy, rfl⟩ := hu'
      have hcρ : c * ρ = 1 := by
        apply hY.eq_one_of_mem_C Δ.prime Δ.ne_two _ (σ.C.mul_mem hc (hR₀C hρ))
        have : c * ρ = c * (ρ * y) * y⁻¹ := by group
        rw [this]
        exact Y.mul_mem hgY (Y.inv_mem hy)
      have hc' : c = ρ⁻¹ := eq_inv_of_mul_eq_one_left hcρ
      refine ⟨?_, hgY⟩
      rw [hc']
      exact (U ⊓ σ.Ns i).mul_mem ((U ⊓ σ.Ns i).inv_mem (hR₀U hρ)) hu
    rw [heq]
    intro c hc
    exact mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_right hc))
      (hY.normalized hc)

theorem exists_comp (hσ : σ.IsValid) (Δ : Data σ r) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) (i : Fin 3) :
    ∃ V : Subgroup G, (V : Set G) = comp σ U i ∧ σ.C ≤ Subgroup.normalizer (V : Set G) ∧
      (V ≤ σ.Ps r i ∨ V ≤ R Δ i ∨ V ≤ Rs Δ i) := by
  set R₀ : Subgroup G := U ⊓ σ.C with hR₀def
  have hR₀ : IsSylowOf r R₀ σ.C := isSylowOf_inf_C hσ Δ hCH hU
  have hUi : U ⊓ σ.Ns i ∈ signalizersPerm (σ.Ns i) σ.T σ.C r :=
    inf_Ns_mem_signalizersPerm hσ hU.1 i inf_le_right
  have hR₀U : R₀ ≤ U ⊓ σ.Ns i := le_inf inf_le_left (inf_le_right.trans (C_le_Ns i))
  obtain ⟨U', hU'max, hUiU'⟩ := exists_le_mem_maximals hUi
  have hmem : U' ∈ {U | U ∈ maximals (signalizersPerm (σ.Ns i) σ.T σ.C r) ∧ R₀ ≤ U} :=
    ⟨hU'max, hR₀U.trans hUiU'⟩
  rw [Δ.lemma72 i R₀ hR₀] at hmem
  obtain ⟨Y, hYb, hYc, hU'Y⟩ : ∃ Y : Subgroup G, IsBlock σ r i Y ∧
      (Y ≤ σ.Ps r i ∨ Y ≤ R Δ i ∨ Y ≤ Rs Δ i) ∧ U' = R₀ ⊔ Y := by
    split_ifs at hmem with hq
    · rcases hmem with h | h
      · exact ⟨R Δ i, isBlock_R Δ hσ i, Or.inr (Or.inl le_rfl), by rw [h, R, sup_assoc]⟩
      · exact ⟨Rs Δ i, isBlock_Rs Δ hσ i, Or.inr (Or.inr le_rfl), by
          rw [Set.mem_singleton_iff] at h
          rw [h, Rs, sup_assoc]⟩
    · exact ⟨σ.Ps r i, isBlock_Ps Δ i, Or.inl le_rfl, hmem⟩
  obtain ⟨hcomp, hnorm⟩ := comp_eq_inf_block Δ hYb inf_le_right hR₀.isPGroup hR₀U hUi.2
    (hUiU'.trans hU'Y.le)
  refine ⟨U ⊓ σ.Ns i ⊓ Y, hcomp, hnorm, ?_⟩
  rcases hYc with h | h | h
  · exact Or.inl (inf_le_right.trans h)
  · exact Or.inr (Or.inl (inf_le_right.trans h))
  · exact Or.inr (Or.inr (inf_le_right.trans h))

omit [Finite G] in
theorem fourInverted_subset_comp (U : Subgroup G) :
    fourInverted U σ.x σ.x₂ ⊆ comp σ U 0 ∧ fourInverted U σ.x₂ σ.x ⊆ comp σ U 1 ∧
      fourInverted U (σ.x * σ.x₂) σ.x ⊆ comp σ U 2 := by
  have hcomm : ∀ {a k : G}, a * k * a⁻¹ = k → a * k = k * a := fun {a k} h => by
    calc a * k = a * k * a⁻¹ * a := by group
      _ = k * a := by rw [h]
  refine ⟨?_, ?_, ?_⟩
  · rintro k ⟨hkU, hk1, hk2⟩
    exact ⟨hkU, hcomm hk1, hk2⟩
  · rintro k ⟨hkU, hk1, hk2⟩
    refine ⟨hkU, hcomm hk1, ?_⟩
    change σ.x * σ.x₂ * k * (σ.x * σ.x₂)⁻¹ = k⁻¹
    rw [show σ.x * σ.x₂ * k * (σ.x * σ.x₂)⁻¹ = σ.x * (σ.x₂ * k * σ.x₂⁻¹) * σ.x⁻¹ by group, hk1,
      hk2]
  · rintro k ⟨hkU, hk1, hk2⟩
    exact ⟨hkU, hcomm hk1, hk2⟩

theorem eq_pCoreIn_sup_inf (hσ : σ.IsValid) (Δ : Data σ r) {H U : Subgroup G}
    (hCH : σ.C ≤ H) (hU : U ∈ maximals (signalizersPerm H σ.T σ.C r)) :
    U = pCoreIn r (U ⊔ σ.C) ⊔ (U ⊓ σ.C) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨⟨⟨-, hUp, hTU, -⟩, hperm⟩, -⟩ := id hU
  refine le_antisymm ?_ (sup_le (pCoreIn_le_of_isSylowOf (isSylowOf_sup hσ Δ hCH hU))
    inf_le_left)
  have hcore : ∀ i : Fin 3, comp σ U i ⊆ (pCoreIn r (U ⊔ σ.C) : Set G) := by
    intro i
    obtain ⟨V, hV, hCV, -⟩ := exists_comp hσ Δ hCH hU i
    have hVU : V ≤ U := by
      intro v hv
      have : v ∈ (V : Set G) := hv
      rw [hV] at this
      exact this.1
    rw [← hV]
    exact le_pCoreIn_sup_of_le hperm hUp hVU hCV
  have := T_isKleinFour hσ
  obtain ⟨-, hdec⟩ := four_group_T_decomposition (odd_card_of_isPGroup Δ.prime Δ.ne_two hUp)
    hTU σ.x_mem_T σ.x₂_mem_T (x_ne_one hσ) (x₂_ne_one hσ) hσ.x_ne_x₂
  obtain ⟨h0, h1, h2⟩ := fourInverted_subset_comp (σ := σ) U
  intro u hu
  have hu' : u ∈ (U : Set G) := hu
  rw [hdec] at hu'
  obtain ⟨w, ⟨w', ⟨u₀, hu₀, v₁, hv₁, rfl⟩, v₂, hv₂, rfl⟩, v₃, hv₃, rfl⟩ := hu'
  have hu₀' : u₀ ∈ U ⊓ σ.C := hu₀
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_right hu₀') ?_) ?_) ?_
  · exact Subgroup.mem_sup_left (hcore 0 (h0 hv₁))
  · exact Subgroup.mem_sup_left (hcore 1 (h1 hv₂))
  · exact Subgroup.mem_sup_left (hcore 2 (h2 hv₃))

theorem pCoreIn_sup_mem_signalizers (Δ : Data σ r) {H U : Subgroup G} (hCH : σ.C ≤ H)
    (hUH : U ≤ H) : pCoreIn r (U ⊔ σ.C) ∈ signalizers H σ.C r := by
  set V : Subgroup G := pCoreIn r (U ⊔ σ.C) with hVdef
  have hCV : σ.C ≤ Subgroup.normalizer (V : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreIn r _)
  refine ⟨(pCoreIn_le r _).trans (sup_le hUH hCH), isPGroup_pCoreIn r _, hCV, ?_⟩
  rw [eq_bot_iff, ← Δ.Op_C]
  exact le_pCoreIn inf_le_right (fun c hc => mem_normalizer_inf (hCV hc)
    (Subgroup.le_normalizer hc)) ((isPGroup_pCoreIn r _).to_le inf_le_left)

end Parts

end CFSG.ABGTheoremB.TotallyInverted.Omnibus
