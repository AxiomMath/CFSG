module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeTorus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeD0
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenMain
public import CFSG.RankThree.PartOne.KF.G2Sylow

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (f4i pairedTorusHom pairedTorusHom_apply torusPair)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)
open CFSG.RankThree.PartOne.KLAY (f4S03 isRoot_of_mem_f4S03)
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam weylOne_conj_fam weylTwo_conj_fam)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

theorem mem_map_conj_iff {X : Type*} [Group X] {S : Subgroup X} {g y : X} :
    y ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ S := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem reeLevi :
    ReeLevi := by
  intro m hm K _ _ _ hK ht
  have hq8 : 8 ≤ 2 ^ (2 * m + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ (2 * m + 1) - 1 = N := ⟨_, rfl⟩
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨p, hpdef⟩ : ∃ p, N.minFac = p := ⟨_, rfl⟩
  rw [hpdef] at hp
  have hpN : p ∣ N := hpdef ▸ Nat.minFac_dvd N
  have h2N : ¬ 2 ∣ N := by
    have : 2 ∣ 2 ^ (2 * m + 1) := dvd_pow_self 2 (by omega)
    omega
  have h3N : ¬ 3 ∣ N := by
    have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
      rw [pow_succ, pow_mul]
      norm_num
      ring
    omega
  have h5 : 5 ≤ p := by
    have h2 := hp.two_le
    have hp2 : p ≠ 2 := fun h => h2N (h ▸ hpN)
    have hp3 : p ≠ 3 := fun h => h3N (h ▸ hpN)
    have hp4 : p ≠ 4 := fun h => by
      rw [h] at hp
      exact absurd hp (by decide)
    omega
  have hpq : p ∣ 2 ^ (2 * m + 1) - 1 := hN ▸ hpN
  obtain ⟨s, hs⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot_of_dvd_card_sub_one (K := K) hp
    (by rw [hK]; exact hpq)
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℤ, ((2 ^ m : ℕ) : ℤ) = θ := ⟨_, rfl⟩
  have hθ : (p : ℤ) ∣ 2 * θ ^ 2 - 1 := by
    have h1 : ((2 ^ (2 * m + 1) - 1 : ℕ) : ℤ) = 2 * θ ^ 2 - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow, ← hθdef]
      push_cast
      ring
    rw [← h1]
    exact Int.natCast_dvd_natCast.2 hpq
  have hcop : (1 + 2 * θ).gcd p = 1 := by
    by_contra hne
    have hd : (1 + 2 * θ).gcd p ∣ p := by
      have := Int.gcd_dvd_right (a := 1 + 2 * θ) (b := (p : ℤ))
      exact Int.natCast_dvd_natCast.1 this
    have hdp : (1 + 2 * θ).gcd p = p := (hp.eq_one_or_self_of_dvd _ hd).resolve_left hne
    have hdvd : (p : ℤ) ∣ 1 + 2 * θ := by
      have := Int.gcd_dvd_left (a := 1 + 2 * θ) (b := (p : ℤ))
      rwa [hdp] at this
    have h1 : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = (1 + 2 * θ) * (2 * θ - 1) - 2 * (2 * θ ^ 2 - 1) := by ring
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_right hdvd _) (Dvd.dvd.mul_left hθ _)
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have := hp.one_lt
    omega
  have hw := hs.zpow_of_gcd_eq_one (1 + 2 * θ) hcop
  obtain ⟨w, hwdef⟩ : ∃ w : Kˣ, s ^ (1 + 2 * θ) = w := ⟨_, rfl⟩
  rw [hwdef] at hw
  have hw2 : w ^ 2 = s ^ (2 + 4 * θ) := by
    rw [← hwdef, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hb := gConj_torusOne (a := m) hK s
  rw [hθdef, hwdef, ← hw2] at hb
  obtain ⟨hbR, hbC⟩ := cent_torusPair hK hp h5 hpq hw
  obtain ⟨g, hgdef⟩ : ∃ g, weylTwo K * weylOne K * weylTwo K = g := ⟨_, rfl⟩
  rw [hgdef] at hb
  have hgg : g * g = 1 := by
    have h1 : weylOne K * weylOne K = 1 := canonicalRep_fixedOrbit_mul_self _
    have h2 : weylTwo K * weylTwo K = 1 := canonicalRep_fixedOrbit_mul_self _
    rw [← hgdef]
    calc weylTwo K * weylOne K * weylTwo K * (weylTwo K * weylOne K * weylTwo K) =
        weylTwo K * weylOne K * (weylTwo K * weylTwo K) * weylOne K * weylTwo K := by group
      _ = 1 := by
        rw [h2, mul_one, mul_assoc (weylTwo K), h1, mul_one, h2]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hgΓ : g ∈ F4.reeGamma K m := hgdef ▸ mul_mem (mul_mem weylTwo_mem weylOne_mem) weylTwo_mem
  have hgconj : ∀ y : ModGL F4.tag K, g * (g * y * g) * g = y := fun y => by
    calc g * (g * y * g) * g = (g * g) * y * (g * g) := by group
      _ = y := by rw [hgg, one_mul, mul_one]
  have hgconj' : ∀ y : ModGL F4.tag K, g * y * g⁻¹ = g * y * g := fun y => by rw [hginv]
  have hR₁Γ : rankOneGroupOne K m ≤ F4.reeGamma K m := rankOneGroupOne_le_reeGamma hK
  have hmemR : ∀ (S : Subgroup (ModGL F4.tag K)) (y : ModGL F4.tag K),
      y ∈ S.map (MulAut.conj g).toMonoidHom ↔ g * y * g ∈ S := fun S y => by
    rw [mem_map_conj_iff, hginv]
  have hmapΓ : ∀ S : Subgroup (ModGL F4.tag K), S ≤ F4.reeGamma K m →
      S.map (MulAut.conj g).toMonoidHom ≤ F4.reeGamma K m := fun S hS y hy => by
    have h := mul_mem (mul_mem hgΓ (hS ((hmemR S y).1 hy))) hgΓ
    rwa [hgconj] at h
  set R₁ := rankOneGroupOne K m with hR₁
  set Rg := R₁.map (MulAut.conj g).toMonoidHom with hRg
  set T₀ := F4.reeGamma K m ⊓ torusGroup F4.tag K with hT₀
  set Hg := T₀.map (MulAut.conj g).toMonoidHom with hHg
  have hRgΓ : Rg ≤ F4.reeGamma K m := hmapΓ _ hR₁Γ
  have hHgΓ : Hg ≤ F4.reeGamma K m := hmapΓ _ inf_le_left
  set q₀ := pairedTorusHom (K := K) m (f4i 0) (f4i 3) s with hq₀
  have hq₀R : q₀ ∈ R₁ := subset_closure (Set.mem_union_left _ (Set.mem_union_right _ ⟨s, rfl⟩))
  have hq₀Γ : q₀ ∈ F4.reeGamma K m := hR₁Γ hq₀R
  have hbT₀ : torusPair (K := K) m (w, w ^ 2) ∈ T₀ :=
    ⟨LargeReeCover.torusPair_mem_reeGamma m hK _, by
      rw [LargeReeCover.torusPair_apply]
      exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
        (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))⟩
  have hq₀b : g * q₀ * g = torusPair (K := K) m (w, w ^ 2) := by rw [← hb, hginv]
  have hq₀H : q₀ ∈ Hg := (hmemR _ _).2 (hq₀b ▸ hbT₀)
  have hTcomm : ∀ x ∈ torusGroup F4.tag K, ∀ y ∈ torusGroup F4.tag K, x * y = y * x := by
    intro x hx y hy
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    exact rootDiagUnit_mul_comm_of_mem_torusGroup l hy
  have hHcomm : ∀ x ∈ Hg, ∀ y ∈ Hg, x * y = y * x := by
    intro x hx y hy
    have h := hTcomm _ (mem_inf.1 ((hmemR _ x).1 hx)).2 _ (mem_inf.1 ((hmemR _ y).1 hy)).2
    have e : ∀ u v : ModGL F4.tag K, g * u * g * (g * v * g) = g * (u * v) * g := fun u v => by
      calc g * u * g * (g * v * g) = g * u * (g * g) * v * g := by group
        _ = g * (u * v) * g := by rw [hgg]; group
    rw [e, e] at h
    calc x * y = g * (g * (x * y) * g) * g := (hgconj _).symm
      _ = y * x := by rw [h, hgconj]
  have hTnorm : ∀ x ∈ T₀, ∀ r ∈ R₁, x * r * x⁻¹ ∈ R₁ := by
    intro x hx r hr
    have hR₁eq : F4.reeGamma K m ⊓ rootSpan F4.tag K f4S03 = R₁ :=
      reeGamma_inf_rootSpan_eq_rankOneGroupOne hK
    rw [← hR₁eq] at hr ⊢
    obtain ⟨hxΓ, hxT⟩ := mem_inf.1 hx
    obtain ⟨hrΓ, hrM⟩ := mem_inf.1 hr
    refine mem_inf.2 ⟨mul_mem (mul_mem hxΓ hrΓ) (inv_mem hxΓ), ?_⟩
    exact (mem_normalizer_iff.1 (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
      (fun α hα => isRoot_of_mem_f4S03 hα) hxT) r).1 hrM
  have hHnorm : ∀ x ∈ Hg, ∀ r ∈ Rg, x * r * x⁻¹ ∈ Rg := by
    intro x hx r hr
    rw [hmemR] at hx hr ⊢
    have h := hTnorm _ hx _ hr
    have e : g * (x * r * x⁻¹) * g = g * x * g * (g * r * g) * (g * x * g)⁻¹ := by
      calc g * (x * r * x⁻¹) * g = g * x * (g * g) * r * (g * g) * x⁻¹ * g := by
            rw [hgg]; group
        _ = g * x * g * (g * r * g) * (g * x * g)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, hginv]
            group
    rw [e]
    exact h
  have hpow : ∀ x ∈ torusGroup F4.tag K, x ^ (Nat.card K - 1) = 1 := by
    intro x hx
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    have hl : ∀ n : ℕ, rootDiagUnit F4.tag l ^ n = rootDiagUnit F4.tag (l ^ n) := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
      | succ n ih => rw [pow_succ, ih, pow_succ, rootDiagUnit_mul]
    rw [hl]
    have : l ^ (Nat.card K - 1) = 1 := funext fun i => by
      rw [Pi.pow_apply, CFSG.SectionRank.LargeRee.units_pow_card_sub_one, Pi.one_apply]
    rw [this, rootDiagUnit_one]
  have hHpow : ∀ x ∈ Hg, x ^ (Nat.card K - 1) = 1 := by
    intro x hx
    have h := hpow _ (mem_inf.1 ((hmemR _ x).1 hx)).2
    have e : (g * x * g) ^ (Nat.card K - 1) = g * x ^ (Nat.card K - 1) * g := by
      rw [← hgconj', conj_pow, hgconj']
    rw [e] at h
    calc x ^ (Nat.card K - 1) = g * (g * x ^ (Nat.card K - 1) * g) * g := (hgconj _).symm
      _ = 1 := by rw [h, mul_one, hgg]
  obtain ⟨-, -, -, -, -, ht1, -, -, -, -, -, -, -, -, -, -, -, -, ht19, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  have hR₁t : ∀ r ∈ R₁, ∀ c, r * sylowL m K c = sylowL m K c * r := by
    intro r hr c
    have hrC : r ∈ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
      rw [ht1]
      exact mem_sup_right hr
    exact mem_centralizer_singleton_iff.1 ((ht19 c).2 hrC)
  have htRg : tK m K ≤ Rg := by
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine ⟨sylowA m K c, subset_closure (Set.mem_union_left _
      (Set.mem_union_left _ (sylowA_mem_U1 hK c))), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hgdef]
    calc weylTwo K * weylOne K * weylTwo K * sylowA m K c *
          (weylTwo K * weylOne K * weylTwo K)⁻¹ =
        weylTwo K * (weylOne K * (weylTwo K * fam m K 0 c * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
          (weylTwo K)⁻¹ := by
          show _ = weylTwo K * (weylOne K * (weylTwo K * sylowA m K c * (weylTwo K)⁻¹) *
            (weylOne K)⁻¹) * (weylTwo K)⁻¹
          group
      _ = fam m K 11 c := by
        rw [weylTwo_conj_fam (n := 0) (n' := 9) (by decide) c,
          weylOne_conj_fam (n := 9) (n' := 10) (by decide) c,
          weylTwo_conj_fam (n := 10) (n' := 11) (by decide) c]
  have hRgR₁ : ∀ d ∈ Rg, ∀ r ∈ R₁, d * r = r * d := by
    have h := commute_rankOneGroupOne_conj (K := K) hm hK
    rw [hgdef] at h
    exact h
  have hRgq : ∀ r ∈ Rg, r * q₀ = q₀ * r := by
    intro r hr
    have h := hbR _ ((hmemR _ r).1 hr)
    rw [← hq₀b] at h
    have e : ∀ u v : ModGL F4.tag K, g * u * g * (g * v * g) = g * (u * v) * g := fun u v => by
      calc g * u * g * (g * v * g) = g * u * (g * g) * v * g := by group
        _ = g * (u * v) * g := by rw [hgg]; group
    rw [e, e] at h
    calc r * q₀ = g * (g * (r * q₀) * g) * g := (hgconj _).symm
      _ = q₀ * r := by rw [h, hgconj]
  have hcent : ∀ c ∈ F4.reeGamma K m, c * q₀ = q₀ * c → ∃ h ∈ Hg, h⁻¹ * c ∈ Rg := by
    intro c hc hcq
    have hc' : g * c * g * torusPair (K := K) m (w, w ^ 2) =
        torusPair (K := K) m (w, w ^ 2) * (g * c * g) := by
      rw [← hq₀b]
      calc g * c * g * (g * q₀ * g) = g * (c * q₀) * g := by
            calc g * c * g * (g * q₀ * g) = g * c * (g * g) * q₀ * g := by group
              _ = g * (c * q₀) * g := by rw [hgg]; group
        _ = g * (q₀ * c) * g := by rw [hcq]
        _ = g * q₀ * g * (g * c * g) := by
            calc g * (q₀ * c) * g = g * q₀ * (g * g) * c * g := by rw [hgg]; group
              _ = g * q₀ * g * (g * c * g) := by group
    obtain ⟨h, hh, hhc⟩ := hbC _ (mul_mem (mul_mem hgΓ hc) hgΓ) hc'
    refine ⟨g * h * g, (hmemR _ _).2 (by rwa [hgconj]), (hmemR _ _).2 ?_⟩
    have e : g * ((g * h * g)⁻¹ * c) * g = h⁻¹ * (g * c * g) := by
      rw [mul_inv_rev, mul_inv_rev, hginv]
      calc g * (g * (h⁻¹ * g) * c) * g = (g * g) * h⁻¹ * (g * c * g) := by group
        _ = h⁻¹ * (g * c * g) := by rw [hgg, one_mul]
    rw [e]
    exact hhc
  obtain ⟨hR₁simple, hR₁nc⟩ := isSimpleGroup_rankOneGroupOne hm hK
  set eg := R₁.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective with heg
  have : IsSimpleGroup Rg := eg.symm.isSimpleGroup
  set Ll := Rg.subgroupOf (F4.reeGamma K m) with hLl
  set eL : Ll ≃* Rg := subgroupOfEquivOfLe hRgΓ with heL
  have : IsSimpleGroup Ll := eL.isSimpleGroup
  have hLnc : ∃ a b : Ll, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hR₁nc
    refine ⟨eL.symm (eg x), eL.symm (eg y), fun h => hxy ?_⟩
    have h1 := congrArg (fun z => eg.symm (eL z)) h
    simpa only [MulEquiv.map_mul, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] using h1
  obtain ⟨hLqs, hLZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hLnc
  have hq₀1 : q₀ ≠ 1 := by
    intro h
    have e : q₀ = rootDiagUnit F4.tag ((fun j => s ^ F4.tag.cartan (f4i 0) j) *
        (fun j => (s ^ 2 ^ m) ^ F4.tag.cartan (f4i 3) j)) := by
      rw [hq₀, pairedTorusHom_apply, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
        ← rootDiagUnit_mul]
    have h1 := (root_diagonal_conjugation F4.tag K ((fun j => s ^ F4.tag.cartan (f4i 0) j) *
        (fun j => (s ^ 2 ^ m) ^ F4.tag.cartan (f4i 3) j))).1 (f4i 1) 1
    rw [← e, h, one_mul, inv_one, mul_one] at h1
    have h2 : (1 : K) = (((fun j => s ^ F4.tag.cartan (f4i 0) j) *
        (fun j => (s ^ 2 ^ m) ^ F4.tag.cartan (f4i 3) j)) (f4i 1) : Kˣ) * 1 :=
      pinnedX_injective F4.tag K (Pi.single (f4i 1) 1)
        (by rw [pinnedX_single, pinnedX_single]; exact h1)
    have e01 : F4.tag.cartan (f4i 0) (f4i 1) = -1 := by decide
    have e31 : F4.tag.cartan (f4i 3) (f4i 1) = 0 := by decide
    simp only [Pi.mul_apply, e01, e31, zpow_zero, mul_one, zpow_neg_one] at h2
    have h3 : s⁻¹ = 1 := Units.ext h2.symm
    exact hs.ne_one (by omega) (inv_eq_one.1 h3)
  have hq₀p : q₀ ^ p = 1 := by
    rw [hq₀, ← map_pow, hs.pow_eq_one, map_one]
  set x : F4.reeGamma K m := ⟨q₀, hq₀Γ⟩ with hx
  rw [zx_eq_of_centreData (centreData_t hm hK ht)]
  refine ⟨R₁.subgroupOf (F4.reeGamma K m), zpowers x, Hg.subgroupOf (F4.reeGamma K m), Ll,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨Group.isPerfect_def.1 hLqs.1, hLqs.2.1⟩, ?_, ?_⟩,
    ?_, ?_⟩
  ·
    have : IsSimpleGroup R₁ := hR₁simple
    exact commutator_subgroupOf_of_perfect hR₁Γ (commutator_eq_self_of_simple hR₁nc)
  ·
    intro d hd
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨c, hc⟩ := (mem_tK hK).1 (mem_subgroupOf.1 hz)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hc]
    exact (hR₁t _ (mem_subgroupOf.1 hd) c).symm
  · exact zpowers_le.2 (mem_subgroupOf.2 hq₀R)
  · intro h
    exact hq₀1 (congrArg Subtype.val (zpowers_eq_bot.1 h))
  · rw [Nat.card_zpowers]
    have hxp : x ^ p = 1 := Subtype.ext (by simp [hx, hq₀p])
    exact (hp.odd_of_ne_two (by omega)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hxp)
  · exact zpowers_le.2 (mem_subgroupOf.2 hq₀H)
  · intro a ha b hb
    exact Subtype.ext (hHcomm _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hb))
  · intro y hy
    rw [mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact mem_subgroupOf.2 (hHnorm _ (mem_subgroupOf.1 hy) _ (mem_subgroupOf.1 hn))
    · intro hn
      have h := hHnorm _ (inv_mem (mem_subgroupOf.1 hy)) _ (mem_subgroupOf.1 hn)
      refine mem_subgroupOf.2 ?_
      have e : (y : ModGL F4.tag K)⁻¹ * ((y * n * y⁻¹ : F4.reeGamma K m) : ModGL F4.tag K) *
          (y : ModGL F4.tag K)⁻¹⁻¹ = n := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [e] at h
  · rw [le_centralizer_iff, zpowers_le, mem_centralizer_iff]
    intro l hl
    exact Subtype.ext (hRgq _ (mem_subgroupOf.1 hl))
  · intro c hc
    have hcq : (c : ModGL F4.tag K) * q₀ = q₀ * c :=
      (congrArg Subtype.val (mem_centralizer_iff.1 hc x (mem_zpowers x))).symm
    obtain ⟨h, hh, hhc⟩ := hcent c c.2 hcq
    exact ⟨⟨h, hHgΓ hh⟩, mem_subgroupOf.2 hh, mem_subgroupOf.2 hhc⟩
  · rw [hLZ, Subgroup.card_bot]
    exact odd_one
  · intro z hz
    exact mem_subgroupOf.2 (htRg (mem_subgroupOf.1 hz))
  ·
    intro α ⟨k, hk⟩ hQ hL
    obtain ⟨-, -, -, -, hcard, -⟩ := large_Ree_full_inner_field_automorphism_normal_form m hm K hK
    have hinn : α ∈ inner (F4.reeGamma K m) := by
      have h1 : (QuotientGroup.mk α : Outer (F4.reeGamma K m)) ^ 2 ^ k = 1 := by
        rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      have h3 := orderOf_dvd_natCard (QuotientGroup.mk α : Outer (F4.reeGamma K m))
      rw [hcard] at h3
      have hco : Nat.Coprime (2 ^ k) (2 * m + 1) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.2 ⟨m, rfl⟩)
      have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hco) h3
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
      exact h4
    obtain ⟨c, rfl⟩ := hinn
    have hc2 : c ^ 2 ^ k = 1 := by
      have h1 : MulAut.conj (c ^ 2 ^ k) = 1 := by rw [map_pow, hk]
      have h2 : c ^ 2 ^ k ∈ center (F4.reeGamma K m) := by
        rw [mem_center_iff]
        intro z
        have h3 := congrArg (fun φ : MulAut (F4.reeGamma K m) => φ z) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc z * c ^ 2 ^ k = c ^ 2 ^ k * z * (c ^ 2 ^ k)⁻¹ * c ^ 2 ^ k := by rw [h3]
          _ = c ^ 2 ^ k * z := by group
      rw [large_Ree_fixed_group_center_trivial m K hK, mem_bot] at h2
      exact h2
    have hcq : (c : ModGL F4.tag K) * q₀ = q₀ * c := by
      have h1 := hQ x (mem_zpowers x)
      simp only [MulAut.conj_apply] at h1
      have h2 : c * x = x * c := by
        calc c * x = c * x * c⁻¹ * c := by group
          _ = x * c := by rw [h1]
      exact congrArg Subtype.val h2
    obtain ⟨h, hh, hhc⟩ := hcent c c.2 hcq
    have hpowc : ∀ n : ℕ, ∃ l' ∈ Rg, (c : ModGL F4.tag K) ^ n = h ^ n * l' := by
      intro n
      induction n with
      | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, mul_one]⟩
      | succ n ih =>
        obtain ⟨l', hl', e⟩ := ih
        refine ⟨(h⁻¹ * l' * h⁻¹⁻¹) * (h⁻¹ * c), mul_mem (hHnorm _ (inv_mem hh) _ hl') hhc, ?_⟩
        rw [pow_succ, e, pow_succ]
        group
    obtain ⟨l', hl', e⟩ := hpowc (2 ^ k)
    have hc2' : (c : ModGL F4.tag K) ^ 2 ^ k = 1 := by
      rw [← Subgroup.coe_pow, hc2, Subgroup.coe_one]
    rw [hc2'] at e
    have hh2 : h ^ 2 ^ k ∈ Rg := by
      have : h ^ 2 ^ k = l'⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        exact e.symm
      rw [this]
      exact inv_mem hl'
    have hhq := hHpow _ hh
    have hco : Nat.Coprime (2 ^ k) (Nat.card K - 1) := by
      rw [hK, hN]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega)))
    have hhR : h ∈ Rg := by
      have hb := Nat.gcd_eq_gcd_ab (2 ^ k) (Nat.card K - 1)
      rw [hco.gcd_eq_one, Nat.cast_one] at hb
      have e2 : h = (h ^ 2 ^ k) ^ Nat.gcdA (2 ^ k) (Nat.card K - 1) *
          (h ^ (Nat.card K - 1)) ^ Nat.gcdB (2 ^ k) (Nat.card K - 1) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb, zpow_one]
      rw [e2, hhq, one_zpow, mul_one]
      exact zpow_mem hh2 _
    have hcR : (c : ModGL F4.tag K) ∈ Rg := by
      have h1 := mul_mem hhR hhc
      rwa [mul_inv_cancel_left] at h1
    have hcL : c ∈ Ll := mem_subgroupOf.2 hcR
    have hcZ : (⟨c, hcL⟩ : Ll) ∈ center Ll := by
      rw [mem_center_iff]
      intro z
      have h1 := hL z z.2
      simp only [MulAut.conj_apply] at h1
      apply Subtype.ext
      apply Subtype.ext
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
      calc ((z : F4.reeGamma K m) : ModGL F4.tag K) * (c : ModGL F4.tag K) =
          ((c : ModGL F4.tag K) * ((z : F4.reeGamma K m) : ModGL F4.tag K) *
            (c : ModGL F4.tag K)⁻¹) * (c : ModGL F4.tag K) := by rw [h2]
        _ = (c : ModGL F4.tag K) * ((z : F4.reeGamma K m) : ModGL F4.tag K) := by group
    rw [hLZ, mem_bot] at hcZ
    have hc1 : c = 1 := congrArg Subtype.val hcZ
    rw [hc1, map_one]
  ·
    have : CharP K 2 := ‹CharP K F4.prime›
    exact CFSG.ComponentClassification.RankTwoL3Even.statedClassicalModel_of_mulEquiv_SL2
      (by omega) hK ((QuotientGroup.quotientMulEquivOfEq hLZ).trans
        (QuotientGroup.quotientBot.trans (eL.trans (eg.symm.trans (rankOneEquivSL K m hK).symm))))

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
