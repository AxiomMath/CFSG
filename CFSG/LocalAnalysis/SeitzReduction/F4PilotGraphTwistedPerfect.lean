module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwistedFamily

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (sigma rho rhoPerm twistSign fixedGroup mem_fixedGroup
  twistedRootGroup xFixed xPair xFixed_val xPair_val xFixed_mem xPair_mem nd nf hHat hHatE
  hFixE hPairE fixedUnits proj orbitMap mem_twistedRootGroup_iff_of_fixed
  mem_twistedRootGroup_iff_of_pair hHat_le_rankOne hHatE_le_fixedGroup commute_xm_rho)
open CFSG.LieType.CurtisTits (rankOne levi)
open scoped commutatorElement

local instance f4PilotGraphTwistedPerfectNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem map_zpow_units_of_fixed {k : Type} [Field k] (θ : k →+* k) {t : kˣ} (htθ : θ t = t)
    (w : ℤ) : θ ((t ^ w : kˣ) : k) = ((t ^ w : kˣ) : k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, htθ]

theorem zpow_neg_two_ne_one {k : Type} [Field k] {t : kˣ} (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ((t ^ (-2 : ℤ) : kˣ) : k) ≠ 1 := by
  intro h
  apply ht
  have h' : t ^ (-2 : ℤ) = 1 := Units.ext h
  rw [zpow_neg, inv_eq_one] at h'
  rw [h', Units.val_one]

theorem toWeight_single_self_E6 :
    ∀ a : Fin (Tag.rank .E6), MinData.toWeight (τ := .E6) (Pi.single a 1) a = 2 := by
  decide

theorem toWeight_neg_single_self_E6 :
    ∀ a : Fin (Tag.rank .E6), MinData.toWeight (τ := .E6) (-Pi.single a 1) a = -2 := by
  decide

section Perfect


variable {k : Type} [Field k] (θ : k →+* k)

theorem commutator_hm_xm {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (a : Fin (Tag.rank .E6)) (t : kˣ) (c : k) :
    ⁅e6Data_valid.hm k a t, e6Data_valid.xm k γ c⁆ =
      e6Data_valid.xm k γ ((((t ^ MinData.toWeight γ a : kˣ) : k) - 1) * c) := by
  rw [commutatorElement_def, e6Data_valid.hm_conj_xm k hγ a t c, e6Data_valid.xm_neg,
    ← e6Data_valid.xm_add]
  congr 1
  ring

theorem twistedRootGroup_fixed_le_commutator_of {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (hργ : rho γ = γ) {R : Subgroup (fixedGroup k θ)}
    {h₀ : fixedGroup k θ} (hh₀R : h₀ ∈ R) {a : Fin (Tag.rank .E6)} {t : kˣ}
    (hh₀ : (h₀ : e6Data_valid.minGroup k) = e6Data_valid.hm k a t) (htθ : θ t = t)
    (hw : ((t ^ MinData.toWeight γ a : kˣ) : k) ≠ 1)
    (hXR : twistedRootGroup k θ (proj γ) ≤ R) :
    twistedRootGroup k θ (proj γ) ≤ ⁅R, R⁆ := by
  intro x hx
  obtain ⟨c, hcθ, hxc⟩ := (mem_twistedRootGroup_iff_of_fixed θ hγ rfl hργ x).1 hx
  set u : k := ((t ^ MinData.toWeight γ a : kˣ) : k) - 1 with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 hw
  have huθ : θ u = u := by rw [hu, map_sub, map_one, map_zpow_units_of_fixed θ htθ]
  have hc' : θ (u⁻¹ * c) = u⁻¹ * c := by rw [map_mul, map_inv₀, huθ, hcθ]
  set y := xFixed θ hγ hργ (u⁻¹ * c) hc' with hy
  have hymem : y ∈ twistedRootGroup k θ (proj γ) := xFixed_mem θ hγ hργ _ hc'
  have e : x = ⁅h₀, y⁆ := by
    apply Subtype.ext
    change (x : e6Data_valid.minGroup k) =
      ⁅(h₀ : e6Data_valid.minGroup k), (y : e6Data_valid.minGroup k)⁆
    rw [hxc, hh₀, hy, xFixed_val, commutator_hm_xm hγ, ← hu, mul_inv_cancel_left₀ hu0]
  rw [e]
  exact commutator_mem_commutator hh₀R (hXR hymem)

theorem twistedRootGroup_pair_le_commutator_of (hθ : ∀ c, θ (θ c) = c)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hργ : rho γ ≠ γ)
    {R : Subgroup (fixedGroup k θ)} {h₀ : fixedGroup k θ} (hh₀R : h₀ ∈ R)
    {a b : Fin (Tag.rank .E6)} {t : kˣ}
    (hh₀ : (h₀ : e6Data_valid.minGroup k) =
      e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map (θ : k →* k) t))
    (hγb : MinData.toWeight γ b = 0) (hργa : MinData.toWeight (rho γ) a = 0)
    (hργb : MinData.toWeight (rho γ) b = MinData.toWeight γ a)
    (hw : ((t ^ MinData.toWeight γ a : kˣ) : k) ≠ 1)
    (hXR : twistedRootGroup k θ (proj γ) ≤ R) :
    twistedRootGroup k θ (proj γ) ≤ ⁅R, R⁆ := by
  have hρroot := CFSG.LieType.Steinberg.TwistedE6.isRoot_rho hγ
  set t' : kˣ := Units.map (θ : k →* k) t with ht'
  set w := MinData.toWeight γ a with hwdef
  have key : ∀ c' d' : k, ⁅e6Data_valid.hm k a t * e6Data_valid.hm k b t',
      e6Data_valid.xm k γ c' * e6Data_valid.xm k (rho γ) d'⁆ =
        e6Data_valid.xm k γ ((((t ^ w : kˣ) : k) - 1) * c') *
          e6Data_valid.xm k (rho γ) ((((t' ^ w : kˣ) : k) - 1) * d') := by
    intro c' d'
    have h1 : e6Data_valid.hm k b t' * e6Data_valid.xm k γ c' * (e6Data_valid.hm k b t')⁻¹ =
        e6Data_valid.xm k γ c' := by
      rw [e6Data_valid.hm_conj_xm k hγ b t' c', hγb, zpow_zero, Units.val_one, one_mul]
    have h2 : e6Data_valid.hm k a t * e6Data_valid.xm k γ c' * (e6Data_valid.hm k a t)⁻¹ =
        e6Data_valid.xm k γ (((t ^ w : kˣ) : k) * c') :=
      e6Data_valid.hm_conj_xm k hγ a t c'
    have h3 : e6Data_valid.hm k b t' * e6Data_valid.xm k (rho γ) d' *
        (e6Data_valid.hm k b t')⁻¹ = e6Data_valid.xm k (rho γ) (((t' ^ w : kˣ) : k) * d') := by
      rw [e6Data_valid.hm_conj_xm k hρroot b t' d', hργb]
    have h4 : ∀ d'', e6Data_valid.hm k a t * e6Data_valid.xm k (rho γ) d'' *
        (e6Data_valid.hm k a t)⁻¹ = e6Data_valid.xm k (rho γ) d'' := by
      intro d''
      rw [e6Data_valid.hm_conj_xm k hρroot a t d'', hργa, zpow_zero, Units.val_one, one_mul]
    have e1 : ⁅e6Data_valid.hm k a t * e6Data_valid.hm k b t',
        e6Data_valid.xm k γ c' * e6Data_valid.xm k (rho γ) d'⁆ =
        (e6Data_valid.hm k a t * (e6Data_valid.hm k b t' * e6Data_valid.xm k γ c' *
          (e6Data_valid.hm k b t')⁻¹) * (e6Data_valid.hm k a t)⁻¹) *
        (e6Data_valid.hm k a t * (e6Data_valid.hm k b t' * e6Data_valid.xm k (rho γ) d' *
          (e6Data_valid.hm k b t')⁻¹) * (e6Data_valid.hm k a t)⁻¹) *
        ((e6Data_valid.xm k (rho γ) d')⁻¹ * (e6Data_valid.xm k γ c')⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e1, h1, h2, h3, h4, e6Data_valid.xm_neg, e6Data_valid.xm_neg, ← mul_assoc,
      mul_assoc (e6Data_valid.xm k γ _), ← e6Data_valid.xm_add k (rho γ),
      mul_assoc (e6Data_valid.xm k γ _) (e6Data_valid.xm k (rho γ) _) (e6Data_valid.xm k γ _),
      ((commute_xm_rho hγ hργ (-c') _).eq).symm, ← mul_assoc, ← e6Data_valid.xm_add k γ]
    congr 2 <;> ring
  intro x hx
  obtain ⟨c, hxc⟩ := (mem_twistedRootGroup_iff_of_pair θ hγ rfl hργ x).1 hx
  set u : k := ((t ^ w : kˣ) : k) - 1 with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 hw
  have hθu : θ u = ((t' ^ w : kˣ) : k) - 1 := by
    rw [hu, map_sub, map_one, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀,
      ht', Units.coe_map]
    rfl
  have hθu0 : θ u ≠ 0 := (map_ne_zero θ).2 hu0
  set y := xPair θ hθ hγ hργ (u⁻¹ * c) with hy
  have hymem : y ∈ twistedRootGroup k θ (proj γ) := xPair_mem θ hθ hγ hργ _
  have e : x = ⁅h₀, y⁆ := by
    apply Subtype.ext
    change (x : e6Data_valid.minGroup k) =
      ⁅(h₀ : e6Data_valid.minGroup k), (y : e6Data_valid.minGroup k)⁆
    rw [hxc, hh₀, hy, xPair_val, key, ← hθu, mul_inv_cancel_left₀ hu0, map_mul, map_inv₀]
    congr 2
    field_simp
  rw [e]
  exact commutator_mem_commutator hh₀R (hXR hymem)

theorem commutator_rankOne_fixed (hθ : ∀ c, θ (θ c) = c) {a : Fin (Tag.rank .E6)}
    (ha : rhoPerm a = a) {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i)
    (hH : ∀ t : fixedUnits θ, ∃ h₀ ∈ hHat k θ i,
      (h₀ : e6Data_valid.minGroup k) = e6Data_valid.hm k a t)
    {t : kˣ} (htθ : θ t = t) (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ⁅rankOne (twistedRootGroup k θ) i, rankOne (twistedRootGroup k θ) i⁆ =
      rankOne (twistedRootGroup k θ) i := by
  refine le_antisymm (commutator_le_self _) ?_
  obtain ⟨h₀, hh₀H, hh₀⟩ := hH ⟨t, (CFSG.LieType.Steinberg.TwistedE6.mem_fixedUnits θ).2 htθ⟩
  have hh₀R := hHat_le_rankOne θ hθ i hh₀H
  have hfix : rho (Pi.single a 1) = Pi.single a 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.rho_single, ha]
  have hfix' : rho (-Pi.single a 1) = -Pi.single a 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.rho_neg_single, ha]
  have hp : proj (Pi.single a 1) = Pi.single i 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.proj_single, hi]
  have hp' : proj (-Pi.single a 1) = -Pi.single i 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.proj_neg_single, hi]
  have hw := toWeight_single_self_E6 a
  have hw' := toWeight_neg_single_self_E6 a
  have hX : twistedRootGroup k θ (proj (Pi.single a 1)) ≤ rankOne (twistedRootGroup k θ) i := by
    rw [hp]
    exact le_sup_left
  have hX' : twistedRootGroup k θ (proj (-Pi.single a 1)) ≤
      rankOne (twistedRootGroup k θ) i := by
    rw [hp']
    exact le_sup_right
  have h1 := twistedRootGroup_fixed_le_commutator_of θ (isRoot_single _ a) hfix hh₀R hh₀ htθ
    (by rw [hw]; exact ht) hX
  have h2 := twistedRootGroup_fixed_le_commutator_of θ (isRoot_neg_single _ a) hfix' hh₀R hh₀ htθ
    (by rw [hw']; exact zpow_neg_two_ne_one ht) hX'
  rw [hp] at h1
  rw [hp'] at h2
  exact sup_le h1 h2

theorem commutator_rankOne_pair (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : rhoPerm a = b) (hba : a ≠ b) {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i)
    (hwt : MinData.toWeight (τ := .E6) (Pi.single a 1) b = 0 ∧
      MinData.toWeight (τ := .E6) (Pi.single b 1) a = 0 ∧
      MinData.toWeight (τ := .E6) (Pi.single a 1) a = 2 ∧
      MinData.toWeight (τ := .E6) (Pi.single b 1) b = 2)
    (hH : ∀ t : kˣ, ∃ h₀ ∈ hHat k θ i, (h₀ : e6Data_valid.minGroup k) =
      e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map (θ : k →* k) t))
    {t : kˣ} (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ⁅rankOne (twistedRootGroup k θ) i, rankOne (twistedRootGroup k θ) i⁆ =
      rankOne (twistedRootGroup k θ) i := by
  refine le_antisymm (commutator_le_self _) ?_
  obtain ⟨h₀, hh₀H, hh₀⟩ := hH t
  have hh₀R := hHat_le_rankOne θ hθ i hh₀H
  obtain ⟨w1, w2, w3, w4⟩ := hwt
  have hρ : rho (Pi.single a 1) = Pi.single b 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.rho_single, hab]
  have hρ' : rho (-Pi.single a 1) = -Pi.single b 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.rho_neg_single, hab]
  have hne : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [hρ]
    intro h
    have := congrFun h b
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hba)] at this
    exact one_ne_zero this
  have hne' : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [hρ']
    intro h
    exact hne (by rw [hρ]; exact neg_injective h)
  have hp : proj (Pi.single a 1) = Pi.single i 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.proj_single, hi]
  have hp' : proj (-Pi.single a 1) = -Pi.single i 1 := by
    rw [CFSG.LieType.Steinberg.TwistedE6.proj_neg_single, hi]
  have hX : twistedRootGroup k θ (proj (Pi.single a 1)) ≤ rankOne (twistedRootGroup k θ) i := by
    rw [hp]
    exact le_sup_left
  have hX' : twistedRootGroup k θ (proj (-Pi.single a 1)) ≤
      rankOne (twistedRootGroup k θ) i := by
    rw [hp']
    exact le_sup_right
  have hneg : ∀ (v : Fin (Tag.rank .E6) → ℤ) (j : Fin (Tag.rank .E6)),
      MinData.toWeight (τ := .E6) (-v) j = -MinData.toWeight (τ := .E6) v j := by
    intro v j
    simp only [MinData.toWeight, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have h1 := twistedRootGroup_pair_le_commutator_of θ hθ (isRoot_single _ a) hne hh₀R hh₀
    w1 (by rw [hρ]; exact w2) (by rw [hρ, w4, w3]) (by rw [w3]; exact ht) hX
  have h2 := twistedRootGroup_pair_le_commutator_of θ hθ (isRoot_neg_single _ a) hne' hh₀R hh₀
    (by rw [hneg, w1, neg_zero]) (by rw [hρ', hneg, w2, neg_zero])
    (by rw [hρ', hneg, hneg, w4, w3]) (by rw [hneg, w3]; exact zpow_neg_two_ne_one ht) hX'
  rw [hp] at h1
  rw [hp'] at h2
  exact sup_le h1 h2

end Perfect

section Nodes


variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

include hθ in
theorem exists_mem_hHat_zero (t : fixedUnits θ) :
    ∃ h₀ ∈ hHat k θ (nf 0), (h₀ : e6Data_valid.minGroup k) = e6Data_valid.hm k (nd 1) t :=
  have hmem : e6Data_valid.hm k (nd 1) t ∈ hHatE k θ (nf 0) :=
    (⟨t, rfl⟩ : e6Data_valid.hm k (nd 1) t ∈ (hFixE θ (nd 1)).range)
  ⟨⟨_, hHatE_le_fixedGroup θ hθ (nf 0) hmem⟩, Subgroup.mem_subgroupOf.2 hmem, rfl⟩

include hθ in
theorem exists_mem_hHat_one (t : fixedUnits θ) :
    ∃ h₀ ∈ hHat k θ (nf 1), (h₀ : e6Data_valid.minGroup k) = e6Data_valid.hm k (nd 3) t :=
  have hmem : e6Data_valid.hm k (nd 3) t ∈ hHatE k θ (nf 1) :=
    (⟨t, rfl⟩ : e6Data_valid.hm k (nd 3) t ∈ (hFixE θ (nd 3)).range)
  ⟨⟨_, hHatE_le_fixedGroup θ hθ (nf 1) hmem⟩, Subgroup.mem_subgroupOf.2 hmem, rfl⟩

include hθ in
theorem exists_mem_hHat_two (t : kˣ) :
    ∃ h₀ ∈ hHat k θ (nf 2), (h₀ : e6Data_valid.minGroup k) =
      e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) t) :=
  have hmem : e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) t) ∈
      hHatE k θ (nf 2) :=
    (⟨t, rfl⟩ : _ ∈ (hPairE θ (nd 2) (nd 4)).range)
  ⟨⟨_, hHatE_le_fixedGroup θ hθ (nf 2) hmem⟩, Subgroup.mem_subgroupOf.2 hmem, rfl⟩

include hθ in
theorem commutator_twLevi_zero {t : kˣ} (htθ : θ t = t) (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ⁅twLevi k θ {0}, twLevi k θ {0}⁆ = twLevi k θ {0} := by
  rw [twLevi, CFSG.LieType.CurtisTits.levi_singleton]
  exact commutator_rankOne_fixed θ hθ (a := nd 1) rfl rfl (exists_mem_hHat_zero θ hθ) htθ ht

include hθ in
theorem commutator_twLevi_one_two {t : kˣ} (htθ : θ t = t)
    (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ⁅twLevi k θ {1, 2}, twLevi k θ {1, 2}⁆ = twLevi k θ {1, 2} := by
  refine le_antisymm (commutator_le_self _) ?_
  refine iSup₂_le fun j hj => ?_
  have hR : ⁅rankOne (twistedRootGroup k θ) j, rankOne (twistedRootGroup k θ) j⁆ =
      rankOne (twistedRootGroup k θ) j := by
    rcases Finset.mem_insert.1 hj with rfl | hj2
    · exact commutator_rankOne_fixed θ hθ (a := nd 3) rfl rfl (exists_mem_hHat_one θ hθ) htθ ht
    · rw [Finset.mem_singleton] at hj2
      subst hj2
      exact commutator_rankOne_pair θ hθ (a := nd 2) (b := nd 4) (by decide) (by decide) rfl
        (by decide) (exists_mem_hHat_two θ hθ) ht
  rw [← hR]
  exact commutator_mono (CFSG.LieType.CurtisTits.rankOne_le_levi _ hj)
    (CFSG.LieType.CurtisTits.rankOne_le_levi _ hj)

end Nodes

theorem exists_barFixed_unit_sq_ne_one {f : ℕ} {F : Type} [Field F] [CharP F 2]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F) (hf : 2 ≤ f) :
    ∃ t : Fˣ, h.barEquiv.toRingHom t = t ∧ ((t ^ (2 : ℤ) : Fˣ) : F) ≠ 1 := by
  have hcard : Nat.card h.fixedField = 2 ^ f :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.card_fixedField h
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨x, hx0, hx1⟩ : ∃ x : h.fixedField, x ≠ 0 ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : h.fixedField) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hcon x hx]⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
    omega
  have hx0' : (x : F) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have hx1' : (x : F) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  refine ⟨Units.mk0 (x : F) hx0', x.2, ?_⟩
  rw [zpow_two, Units.val_mul, Units.val_mk0]
  intro hsq
  apply hx1'
  have hsq' : ((x : F) + 1) * ((x : F) + 1) = 0 := by
    have e : ((x : F) + 1) * ((x : F) + 1) = (x : F) * x + ((x : F) + x) + 1 := by ring
    rw [e, hsq, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h0 := mul_self_eq_zero.1 hsq'
  rw [← CharTwo.sub_eq_add, sub_eq_zero] at h0
  exact h0

end CFSG.SeitzReduction.F4Pilot
