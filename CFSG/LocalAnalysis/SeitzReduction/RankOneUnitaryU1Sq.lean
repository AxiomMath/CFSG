module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Comm

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem sq_mem_of_mem_u3U₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    {x : G} (hx : x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) : x ^ 2 ∈ R₂ := by
  have hcomm := fun {a b : G} (ha : a ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G))
    (hb : b ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) =>
    h.comm_mem_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg ha hb
  obtain ⟨-, -, -, hU₁sq⟩ := h.u3U_lambda_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, hNA, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨htriv, hcH, hU₁c, -⟩ := h.u3U_lambda_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  obtain ⟨hYU₁, -, -, -, -, hcov⟩ := h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  set U := u3U L T R₂ t E with hU
  set U₁ := u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) with hU₁
  set H := szT₁ L T ⊔ R₂ with hH
  have hUY := u3U_le_normalizer L T R₂ t E
  have hUH : U ≤ normalizer (H : Set G) := fun y hy => (mem_inf.mp (hNR₁ (hUY hy))).1
  have hU₁U : U₁ ≤ U := inf_le_left
  obtain ⟨K, _, _, _, σ, hKcard, -, u, uu, hcoord, hA₁u, d, hdL, hdT, μ, hμ0, hμord, hdμ⟩ :=
    h.exists_rootCoords_cartan_of_card_sylow hS2
  have hdA : d ∈ normalizer (szA L T t : Set G) := h.inf_normalizer_le_normalizer_szA ⟨hdL, hdT⟩
  have hdU₁ : d ∈ normalizer (U₁ : Set G) := hYU₁ (hNA hdA)
  have hdH : d ∈ normalizer (H : Set G) := (mem_inf.mp (hNR₁ (hNA hdA))).1
  have hdR₂ : d ∈ normalizer (R₂ : Set G) := (mem_inf.mp (hNR₁ (hNA hdA))).2
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  obtain ⟨ψ, hψ⟩ := exists_coord_sup hR (u := u) fun w hw w' hw' hww' => by
    have h1 : w⁻¹ * w' ∈ szA₁ (szT₁ L T) := by rw [← hR.inf]; exact hww'
    have h2 := (hA₁u _ (mul_mem (inv_mem hw) hw')).mp h1
    rw [hcoord.u_mul_inv hw hw'] at h2
    exact (sub_eq_zero.mp h2).symm
  have hψadd : ∀ a ∈ H, ∀ b ∈ H, ψ (a * b) = ψ a + ψ b := by
    intro a ha b hb
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    obtain ⟨w', hw', r', hr', rfl⟩ := hR.mem_sup_iff.mp hb
    have hrw : r * w' = w' * r := (hR.commT₁ w' hw' r hr).symm
    have e : w * r * (w' * r') = (w * w') * (r * r') := by
      calc w * r * (w' * r') = w * (r * w') * r' := by group
        _ = w * (w' * r) * r' := by rw [hrw]
        _ = (w * w') * (r * r') := by group
    rw [e, hψ _ (mul_mem hw hw') _ (mul_mem hr hr'), hψ w hw r hr, hψ w' hw' r' hr',
      hcoord.mul_u w hw w' hw']
  have hψ0 : ∀ a ∈ H, ψ a = 0 ↔ a ∈ R₂ := by
    intro a ha
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    rw [hψ w hw r hr, ← hA₁u w hw]
    constructor
    · intro hwA
      exact mul_mem (hR.le hwA) hr
    · intro hwr
      have h1 : w ∈ szT₁ L T ⊓ R₂ := mem_inf.mpr ⟨hw, by
        have := mul_mem hwr (inv_mem hr)
        rwa [mul_inv_cancel_right] at this⟩
      rwa [hR.inf] at h1
  have hψR₂ : ∀ a ∈ R₂, ψ a = 0 := fun a ha => (hψ0 a (mem_sup_right ha)).mpr ha
  have hψconj : ∀ v ∈ U, ∀ a ∈ H, ψ (v * a * v⁻¹) = ψ a := by
    intro v hv a ha
    have h1 := htriv v hv a ha
    have e : v * a * v⁻¹ = a * (a⁻¹ * (v * a * v⁻¹)) := by group
    rw [e, hψadd _ ha _ (mem_sup_right h1), hψR₂ _ h1, add_zero]
  have hψd : ∀ a ∈ H, ψ (d * a * d⁻¹) = μ * ψ a := by
    intro a ha
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    have e : d * (w * r) * d⁻¹ = (d * w * d⁻¹) * (d * r * d⁻¹) := by group
    rw [e, hψ _ ((mem_normalizer_iff.mp hdT w).mp hw) _ ((mem_normalizer_iff.mp hdR₂ r).mp hr),
      hψ w hw r hr, hdμ w hw]
  set l : G → K := fun z => ψ (z * t * z⁻¹ * t⁻¹) with hl
  have hcH₁ : ∀ z ∈ U₁, z * t * z⁻¹ * t⁻¹ ∈ H := fun z hz => hcH z (hU₁U hz)
  have hladd : ∀ z ∈ U₁, ∀ z' ∈ U₁, l (z * z') = l z + l z' := by
    intro z hz z' hz'
    have e : z * z' * t * (z * z')⁻¹ * t⁻¹ =
        (z * (z' * t * z'⁻¹ * t⁻¹) * z⁻¹) * (z * t * z⁻¹ * t⁻¹) := by group
    have hmem : z * (z' * t * z'⁻¹ * t⁻¹) * z⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (hUH (hU₁U hz)) _).mp (hcH₁ z' hz')
    simp only [hl]
    rw [e, hψadd _ hmem _ (hcH₁ z hz), hψconj z (hU₁U hz) _ (hcH₁ z' hz'), add_comm]
  have hlsurj : ∀ a : K, ∃ z ∈ U₁, l z = a := by
    intro a
    obtain ⟨w, hw, hwa⟩ := hcoord.u_surj a
    obtain ⟨z, hz, r, hr, hzt⟩ := hcov w hw
    refine ⟨z, hz, ?_⟩
    have e : z * t * z⁻¹ * t⁻¹ = w * r := by
      rw [hzt, mul_inv_cancel_right]
      exact (hR.commT₁ w hw r hr).symm
    simp only [hl]
    rw [e, hψ w hw r hr, hwa]
  have hlker : ∀ z ∈ U₁, l z = 0 → z ∈ H := by
    intro z hz hlz
    refine h.mem_sup_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hz ?_
    have h1 := (hψ0 _ (hcH₁ z hz)).mp hlz
    have e : t * z * t⁻¹ * z⁻¹ = (z * t * z⁻¹ * t⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hld : ∀ z ∈ U₁, l (d * z * d⁻¹) = μ * l z := by
    intro z hz
    have e : d * z * d⁻¹ * t * (d * z * d⁻¹)⁻¹ * t⁻¹ = d * (z * t * z⁻¹ * t⁻¹) * d⁻¹ := by
      have hdt' : d⁻¹ * t = t * d⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hdt, mul_inv_cancel_right]
      calc d * z * d⁻¹ * t * (d * z * d⁻¹)⁻¹ * t⁻¹ = d * z * (d⁻¹ * t) * d * z⁻¹ * d⁻¹ * t⁻¹ := by
            group
        _ = d * z * (t * d⁻¹) * d * z⁻¹ * d⁻¹ * t⁻¹ := by rw [hdt']
        _ = d * z * t * z⁻¹ * (d⁻¹ * t⁻¹) := by group
        _ = d * z * t * z⁻¹ * (t⁻¹ * d⁻¹) := by
            rw [show d⁻¹ * t⁻¹ = t⁻¹ * d⁻¹ by
              rw [← mul_inv_rev, ← mul_inv_rev, hdt]]
        _ = d * (z * t * z⁻¹ * t⁻¹) * d⁻¹ := by group
    simp only [hl]
    rw [e, hψd _ (hcH₁ z hz)]
  have hHsq : ∀ a ∈ H, a ^ 2 ∈ R₂ := by
    intro a ha
    obtain ⟨-, -, -, hsq, -⟩ := h.facts_of_card_sylow hS2
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    have hwr : Commute w r := hR.commT₁ w hw r hr
    rw [hwr.mul_pow]
    exact mul_mem (hR.le (hsq w hw)) (hR.le (hR.sq_mem r hr))
  have hcen : ∀ z ∈ U₁, ∀ r ∈ R₂, r * z = z * r := fun z hz r hr =>
    mem_centralizer_iff.mp (mem_inf.mp hz).2 r hr
  have hsqcomm : ∀ z ∈ U₁, ∀ z' ∈ U₁, z ^ 2 * z' ^ 2 = z' ^ 2 * z ^ 2 := by
    intro z hz z' hz'
    obtain ⟨c, hcdef⟩ : ∃ c : G, c = z * z' * z⁻¹ * z'⁻¹ := ⟨_, rfl⟩
    have hcR : c ∈ R₂ := by rw [hcdef]; exact hcomm hz hz'
    have hcz : Commute c z := hcen z hz c hcR
    have hcz' : Commute c z' := hcen z' hz' c hcR
    have hc4 : c ^ 4 = 1 := by
      have := hR.sq_A₁ _ (hR.sq_mem c hcR)
      rwa [← pow_mul] at this
    have hconj : ∀ g a : G, g * a ^ 2 * g⁻¹ = (g * a * g⁻¹) ^ 2 := fun g a => by
      rw [sq, sq]; group
    have h2 : z * z' * z⁻¹ = c * z' := by rw [hcdef]; group
    have h3 : z * z' ^ 2 * z⁻¹ = c ^ 2 * z' ^ 2 := by rw [hconj, h2, hcz'.mul_pow]
    have hc2z : z * c ^ 2 * z⁻¹ = c ^ 2 := by
      rw [(Commute.pow_right hcz.symm 2).eq, mul_inv_cancel_right]
    have h4 : z ^ 2 * z' ^ 2 * (z ^ 2)⁻¹ = c ^ 4 * z' ^ 2 := by
      calc z ^ 2 * z' ^ 2 * (z ^ 2)⁻¹ = z * (z * z' ^ 2 * z⁻¹) * z⁻¹ := by rw [sq z]; group
        _ = z * (c ^ 2 * z' ^ 2) * z⁻¹ := by rw [h3]
        _ = (z * c ^ 2 * z⁻¹) * (z * z' ^ 2 * z⁻¹) := by group
        _ = c ^ 2 * (c ^ 2 * z' ^ 2) := by rw [hc2z, h3]
        _ = c ^ 4 * z' ^ 2 := by rw [← mul_assoc, ← pow_add]
    calc z ^ 2 * z' ^ 2 = z ^ 2 * z' ^ 2 * (z ^ 2)⁻¹ * z ^ 2 := by group
      _ = c ^ 4 * z' ^ 2 * z ^ 2 := by rw [h4]
      _ = z' ^ 2 * z ^ 2 := by rw [hc4, one_mul]
  set sqm : G → K := fun z => ψ (z ^ 2) with hsqm
  have hsqadd : ∀ z ∈ U₁, ∀ z' ∈ U₁, sqm (z * z') = sqm z + sqm z' := by
    intro z hz z' hz'
    have hc' := hcomm (inv_mem hz) hz'
    have e : (z * z') ^ 2 = z ^ 2 * (z⁻¹ * z' * z⁻¹⁻¹ * z'⁻¹) * z' ^ 2 := by
      rw [sq, sq, sq]; group
    simp only [hsqm]
    rw [e, hψadd _ (mul_mem (hU₁sq z hz) (mem_sup_right hc')) _ (hU₁sq z' hz'),
      hψadd _ (hU₁sq z hz) _ (mem_sup_right hc'), hψR₂ _ hc', add_zero]
  have hsq0 : ∀ z ∈ U₁, l z = 0 → sqm z = 0 := fun z hz hlz =>
    (hψ0 _ (hU₁sq z hz)).mpr (hHsq z (hlker z hz hlz))
  obtain ⟨S, hSadd, hSl⟩ := exists_additive_of_descends hladd hlsurj hsqadd hsq0
  have hSμ : ∀ a, S (μ * a) = μ * S a := by
    intro a
    obtain ⟨z, hz, rfl⟩ := hlsurj a
    have hdz : d * z * d⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hdU₁ z).mp hz
    rw [← hld z hz, ← hSl _ hdz, ← hSl z hz]
    simp only [hsqm]
    rw [show (d * z * d⁻¹) ^ 2 = d * z ^ 2 * d⁻¹ by rw [sq, sq]; group, hψd _ (hU₁sq z hz)]
  have hS00 : S 0 = 0 := by
    have := hSadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hS0 : ∀ a, S a = 0 := by
    by_contra hS
    push Not at hS
    obtain ⟨a₀, ha₀⟩ := hS
    let ker : AddSubgroup K :=
      { carrier := {a | S a = 0}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [hSadd, ha, hb, add_zero]
        zero_mem' := hS00
        neg_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq] at ha ⊢
          have := hSadd (-a) a
          rw [neg_add_cancel, hS00, ha, add_zero] at this
          exact this.symm }
    have hinj : Function.Injective S := by
      intro a b hab
      by_contra hne
      have hab0 : a - b ∈ ker := by
        show S (a - b) = 0
        have := hSadd (a - b) b
        rw [sub_add_cancel, hab] at this
        exact (add_eq_right.mp this.symm)
      have hq4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
      set μu : Kˣ := (Ne.isUnit hμ0).unit with hμu
      have hμuval : (μu : K) = μ := IsUnit.unit_spec _
      have htop := addSubgroup_eq_top_of_scalar_stable (q := 2 ^ f) hKcard (by omega) ker hab0
        (sub_ne_zero.mpr hne) (zpowers μu) (fun s hs y hy => by
          have hy' : S y = 0 := hy
          have hpow : ∀ m : ℕ, S (μ ^ m * y) = 0 := by
            intro m
            induction m with
            | zero => simpa using hy'
            | succ m ih => rw [pow_succ', mul_assoc, hSμ, ih, mul_zero]
          obtain ⟨m, hm⟩ := (isOfFinOrder_of_finite μu).mem_powers_iff_mem_zpowers.mpr hs
          show S ((s : K) * y) = 0
          rw [← hm]
          simp only [Units.val_pow_eq_pow_val, hμuval]
          exact hpow m) (by
          rw [Nat.card_zpowers]
          have h1 : orderOf μu = orderOf μ := by rw [← hμuval]; exact orderOf_units.symm
          rw [h1, hμord]
          obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
          rw [← hq] at hq4 ⊢
          have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
          have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
          have h2 : q ≤ (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
            rw [Nat.le_div_iff_mul_le hgpos]
            have h3 : 3 * q + 1 ≤ q ^ 2 := by nlinarith
            have h4 : q * Nat.gcd 3 (q + 1) ≤ 3 * q := by nlinarith
            omega
          omega)
      have : a₀ ∈ ker := by rw [htop]; exact AddSubgroup.mem_top _
      exact ha₀ this
    have hsurj := Finite.injective_iff_surjective.mp hinj
    have hsqrt : ∀ w ∈ szT₁ L T, ∃ z ∈ U₁, ∃ r ∈ R₂, w = z ^ 2 * r := by
      intro w hw
      obtain ⟨a, ha⟩ := hsurj (u w)
      obtain ⟨z, hz, rfl⟩ := hlsurj a
      refine ⟨z, hz, (z ^ 2)⁻¹ * w, ?_, by group⟩
      have hzH := hU₁sq z hz
      have hwH : w ∈ H := mem_sup_left hw
      refine (hψ0 _ (mul_mem (inv_mem hzH) hwH)).mp ?_
      have h1 : ψ ((z ^ 2)⁻¹ * z ^ 2) = ψ (z ^ 2)⁻¹ + ψ (z ^ 2) :=
        hψadd _ (inv_mem hzH) _ hzH
      rw [inv_mul_cancel, hψR₂ 1 (one_mem _)] at h1
      have h2 : ψ w = u w := by simpa using hψ w hw 1 (one_mem _)
      have h3 : sqm z = u w := by rw [hSl z hz, ha]
      simp only [hsqm] at h3
      rw [hψadd _ (inv_mem hzH) _ hwH, h2, ← h3]
      exact h1.symm
    have hT₁ab : ∀ w ∈ szT₁ L T, ∀ w' ∈ szT₁ L T, w * w' = w' * w := by
      intro w hw w' hw'
      obtain ⟨z, hz, r, hr, rfl⟩ := hsqrt w hw
      obtain ⟨z', hz', r', hr', rfl⟩ := hsqrt w' hw'
      have c1 : r * z' ^ 2 = z' ^ 2 * r := hcen _ (pow_mem hz' 2) r hr
      have c2 : r' * z ^ 2 = z ^ 2 * r' := hcen _ (pow_mem hz 2) r' hr'
      have c3 : r * r' = r' * r := hR.comm r hr r' hr'
      have eL : z ^ 2 * r * (z' ^ 2 * r') = z ^ 2 * z' ^ 2 * (r * r') := by
        calc z ^ 2 * r * (z' ^ 2 * r') = z ^ 2 * (r * z' ^ 2) * r' := by group
          _ = z ^ 2 * (z' ^ 2 * r) * r' := by rw [c1]
          _ = z ^ 2 * z' ^ 2 * (r * r') := by group
      have eR : z' ^ 2 * r' * (z ^ 2 * r) = z' ^ 2 * z ^ 2 * (r' * r) := by
        calc z' ^ 2 * r' * (z ^ 2 * r) = z' ^ 2 * (r' * z ^ 2) * r := by group
          _ = z' ^ 2 * (z ^ 2 * r') * r := by rw [c2]
          _ = z' ^ 2 * z ^ 2 * (r' * r) := by group
      rw [eL, eR, hsqcomm z hz z' hz', c3]
    obtain ⟨-, hA₁card, hA₁eq, -⟩ := h.facts_of_card_sylow hS2
    have hbot : szA₁ (szT₁ L T) = ⊥ := by
      rw [hA₁eq, eq_bot_iff, commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [mem_bot, commutatorElement_def, hT₁ab g₁ hg₁ g₂ hg₂]
      group
    rw [hbot, card_bot] at hA₁card
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
    omega
  have h1 : sqm x = 0 := by rw [hSl x hx, hS0]
  exact (hψ0 _ (hU₁sq x hx)).mp h1

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
