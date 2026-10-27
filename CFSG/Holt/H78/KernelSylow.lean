module

public import CFSG.Holt.H78.Kernel
public import CFSG.Holt.H78.DataSylow

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section OrbitGroup

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

variable (G) in
abbrev orbitGroup (α : Ω) : Subgroup (Equiv.Perm (OddOrbits G α)) :=
  (toPermHom G (OddOrbits G α)).range

variable (G) in
abbrev orbitRestrict (α : Ω) : G →* orbitGroup G α :=
  (toPermHom G (OddOrbits G α)).rangeRestrict

variable (G) in
noncomputable abbrev orbitPoint [IsPretransitive G Ω] (α ω : Ω) : OddOrbits G α :=
  blockCoset α (oddOrbitsStabilizer G α) ω

@[simp] theorem orbitRestrict_smul (α : Ω) (g : G) (c : OddOrbits G α) :
    orbitRestrict G α g • c = g • c := rfl

theorem orbitPoint_smul [IsPretransitive G Ω] (α : Ω) (g : G) (ω : Ω) :
    orbitPoint G α (g • ω) = orbitRestrict G α g • orbitPoint G α ω :=
  blockCoset_smul le_sup_left g ω

theorem orbitRestrict_eq_one_iff (α : Ω) {g : G} :
    orbitRestrict G α g = 1 ↔ g ∈ oddOrbitsKernel G α := by
  rw [← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict]

theorem one_lt_index_oddOrbitsStabilizer [Finite G] [IsPretransitive G Ω] {α : Ω}
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) : 1 < (oddOrbitsStabilizer G α).index := by
  have hne : (oddOrbitsStabilizer G α).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine lt_of_le_of_ne (Nat.pos_of_ne_zero hne) fun h1 => hint ⟨fun ω ω' => ?_⟩
  have htop := Subgroup.index_eq_one.mp h1.symm
  have hmem : ∀ γ : Ω, γ ∈ orbit (CFSG.pPrimeCore 2 G) α := fun γ => by
    obtain ⟨g, rfl⟩ := exists_smul_eq G α γ
    exact mem_oddOrbitsStabilizer_iff.mp (htop ▸ Subgroup.mem_top g)
  have h := hmem ω'
  rw [← orbit_eq_iff.mpr (hmem ω)] at h
  exact mem_orbit_iff.mp h

theorem orbitRestrict_smul_orbitPoint_eq_iff [IsPretransitive G Ω] {α β : Ω} {g : G} :
    orbitRestrict G α g • orbitPoint G α β = orbitPoint G α β ↔
      g ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β) := by
  have := CFSG.pPrimeCore_normal (p := 2) (G := G)
  rw [← orbitPoint_smul, eq_comm, blockCoset_eq_blockCoset_iff, mem_stabilizer_iff,
    smul_orbit_eq_orbit_smul, orbit_eq_iff]

variable [Finite G]

theorem orbitRestrict_mem_longInvAt [IsPretransitive G Ω] (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {α β : Ω} {t : G}
    (ht : t ∈ longInvAt G Ω β) :
    orbitRestrict G α t ∈ longInvAt (orbitGroup G α) (OddOrbits G α) (orbitPoint G α β) :=
  rangeRestrict_mem_longInvAt_quotient hG.odd_card le_sup_left
    (one_lt_index_oddOrbitsStabilizer hint) ht

theorem orbitRestrict_mem_longInv (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {α : Ω} {t : G}
    (ht : t ∈ longInv G Ω) : orbitRestrict G α t ∈ longInv (orbitGroup G α) (OddOrbits G α) :=
  have := hG.isPretransitive
  let ⟨_, hβ⟩ := exists_mem_longInvAt ht
  (orbitRestrict_mem_longInvAt hG hint hβ).1

theorem map_jHull_le (hG : IsStarGroup G Ω) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (α : Ω) : (jHull G Ω).map (orbitRestrict G α) ≤ jHull (orbitGroup G α) (OddOrbits G α) := by
  rw [jHull, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨t, ht, rfl⟩
  exact mem_jHull_of_mem_longInv (orbitRestrict_mem_longInv hG hint ht)

end OrbitGroup

section KR1

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem jOddCore_orbitGroup_eq_bot (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (α : Ω) :
    jOddCore (orbitGroup G α) (OddOrbits G α) = ⊥ := by
  have := hG.isPretransitive
  set X := orbitGroup G α
  set π := orbitRestrict G α
  set Q := jOddCore X (OddOrbits G α)
  set HX := (jHull G Ω).map π
  have hHX : HX.Normal := (jHull_normal (G := G) (Ω := Ω)).map π
    (MonoidHom.rangeRestrict_surjective _)
  have hinf : Q ⊓ HX = ⊥ := by
    have h1 : (Q ⊓ HX).subgroupOf HX ≤ CFSG.pPrimeCore 2 HX := by
      refine le_sSup ⟨(inferInstance : (Q ⊓ HX).Normal).subgroupOf HX, ?_⟩
      rw [← Subgroup.card_map_of_injective HX.subtype_injective, Subgroup.subgroupOf_map_subtype,
        Nat.coprime_two_left]
      exact Odd.of_dvd_nat odd_card_jOddCore
        (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left))
    rw [pPrimeCore_map_jHull_eq_bot hG hO α, le_bot_iff, Subgroup.subgroupOf_eq_bot] at h1
    exact h1.eq_bot_of_le inf_le_right
  have hcomm : ∀ q ∈ Q, ∀ x ∈ HX, q * x = x * q := fun q hq x hx => by
    have h := Subgroup.commutator_le_inf Q HX (Subgroup.commutator_mem_commutator hq hx)
    rwa [hinf, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  have htX := orbitRestrict_mem_longInvAt hG hint ht (α := α)
  have htHX : π t ∈ HX := ⟨t, mem_jHull_of_mem_longInv ht.1, rfl⟩
  have hfix : ∀ q ∈ Q, q • orbitPoint G α α = orbitPoint G α α := fun q hq => by
    have h1 : π t • (q • orbitPoint G α α) = q • orbitPoint G α α := by
      rw [smul_smul, ← hcomm q hq _ htHX, mul_smul, htX.2]
    exact (smul_eq_iff_of_mem_longInvAt htX _).mp h1
  refine (Subgroup.eq_bot_iff_forall _).mpr fun q hq => Subtype.ext (Equiv.ext fun b => ?_)
  obtain ⟨ω, rfl⟩ := blockCoset_surjective (le_sup_left : stabilizer G α ≤ _) b
  obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
  change q • orbitPoint G α (g • α) = orbitPoint G α (g • α)
  have hq' : (π g)⁻¹ * q * (π g)⁻¹⁻¹ ∈ Q := jOddCore_normal.conj_mem _ hq _
  rw [orbitPoint_smul, show q • π g • orbitPoint G α α =
      π g • (((π g)⁻¹ * q * (π g)⁻¹⁻¹) • orbitPoint G α α) by
    rw [smul_smul, smul_smul, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul],
    hfix _ hq']

theorem L_le_map_jHull (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {α : Ω}
    (D' : HoltData (orbitGroup G α) (OddOrbits G α)) (i : D'.ι) :
    D'.L i ≤ (jHull G Ω).map (orbitRestrict G α) := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  have hHX : ((jHull G Ω).map (orbitRestrict G α)).Normal :=
    (jHull_normal (G := G) (Ω := Ω)).map _ (MonoidHom.rangeRestrict_surjective _)
  set HX := (jHull G Ω).map (orbitRestrict G α) with hHX_def
  set R := D'.L i ⊓ HX
  set S : Subgroup (Equiv.Perm (D'.Ψc i)) :=
    (R.subgroupOf (jHull (orbitGroup G α) (OddOrbits G α))).map (D'.ρ i)
  have hSM : S ≤ D'.M i := Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_left)
  have hSn : (S.subgroupOf (D'.M i)).Normal := ⟨fun s hs m => by
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    obtain ⟨r, hr, hrs⟩ := hs
    obtain ⟨l, hl, hlm⟩ := HoltData.mem_M.mp m.2
    replace hr : (r : orbitGroup G α) ∈ R := Subgroup.mem_subgroupOf.mp hr
    refine ⟨l * r * l⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (D'.L i).mul_mem ((D'.L i).mul_mem hl hr.1) ((D'.L i).inv_mem hl)
    · exact hHX.conj_mem _ hr.2 _
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, hlm,
        hrs]⟩
  have := D'.isSimpleGroup_M i
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  have htX := orbitRestrict_mem_longInv hG hint (α := α) ht.1
  have htHX : orbitRestrict G α t ∈ HX := ⟨t, mem_jHull_of_mem_longInv ht.1, rfl⟩
  have := hSn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf (D'.M i)) with hbot | htop
  · exfalso
    have hS : S = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hSM
    have hR : ∀ r ∈ R, r = 1 := fun r hr => by
      have hrJ : r ∈ jHull (orbitGroup G α) (OddOrbits G α) := D'.L_le i hr.1
      have h1 : D'.ρ i ⟨r, hrJ⟩ = 1 := by
        have : D'.ρ i ⟨r, hrJ⟩ ∈ S := ⟨⟨r, hrJ⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
        rwa [hS, Subgroup.mem_bot] at this
      have h2 := HoltData.mem_jOddCore_of_mem_L (h := ⟨r, hrJ⟩) hr.1 h1
      rwa [hOX, Subgroup.mem_bot] at h2
    set x : jHull (orbitGroup G α) (OddOrbits G α) :=
      ⟨orbitRestrict G α t, mem_jHull_of_mem_longInv htX⟩
    have hxc : D'.ρ i x ∈ Subgroup.centralizer (D'.M i : Set (Equiv.Perm (D'.Ψc i))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      obtain ⟨l, hl, rfl⟩ := HoltData.mem_M.mp hm
      have hlx : (l : orbitGroup G α) * orbitRestrict G α t = orbitRestrict G α t * l := by
        have hc : (l : orbitGroup G α) * orbitRestrict G α t * (l : orbitGroup G α)⁻¹ *
            (orbitRestrict G α t)⁻¹ ∈ R := by
          refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (hHX.conj_mem _ htHX _) (inv_mem htHX)⟩
          rw [mul_assoc, mul_assoc]
          refine (D'.L i).mul_mem hl ?_
          have h3 := (Subgroup.mem_normalizer_iff.mp (D'.le_normalizer i x.2) _).mp
            ((D'.L i).inv_mem hl)
          simpa only [mul_assoc] using h3
        have h4 := hR _ hc
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
        exact h4
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hlx
    rw [(D'.factor i).centralizer_eq_bot, Subgroup.mem_bot] at hxc
    have h2 := (D'.rho_mem_longInv htX i).1
    rw [show D'.ρ i ⟨orbitRestrict G α t, mem_jHull_of_mem_longInv htX⟩ = D'.ρ i x from rfl, hxc,
      orderOf_one] at h2
    omega
  · intro l hl
    have hlJ : l ∈ jHull (orbitGroup G α) (OddOrbits G α) := D'.L_le i hl
    have h1 : (⟨D'.ρ i ⟨l, hlJ⟩, HoltData.rho_mem_M (h := ⟨l, hlJ⟩) hl⟩ : D'.M i) ∈
        S.subgroupOf (D'.M i) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, hrl⟩ := Subgroup.mem_subgroupOf.mp h1
    replace hr : (r : orbitGroup G α) ∈ R := Subgroup.mem_subgroupOf.mp hr
    rw [← show (r : orbitGroup G α) = l from congrArg Subtype.val
      (HoltData.eq_of_rho_eq_of_mem_L hOX hr.1 hl hrl)]
    exact hr.2

end KR1

section Lift

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] {α : Ω}

variable (D' : HoltData (orbitGroup G α) (OddOrbits G α))

@[expose] def liftL (i : D'.ι) : Subgroup G :=
  jHull G Ω ⊓ (D'.L i).comap (orbitRestrict G α)

variable {D'}

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
theorem mem_liftL {i : D'.ι} {g : G} :
    g ∈ liftL D' i ↔ g ∈ jHull G Ω ∧ orbitRestrict G α g ∈ D'.L i := Iff.rfl

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
theorem liftL_le_jHull (i : D'.ι) : liftL D' i ≤ jHull G Ω := inf_le_left

theorem map_liftL (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    (liftL D' i).map (orbitRestrict G α) = D'.L i := by
  refine le_antisymm ?_ fun l hl => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact hg.2
  · obtain ⟨g, hg, rfl⟩ := L_le_map_jHull hG hO hint D' i hl
    exact ⟨g, ⟨hg, hl⟩, rfl⟩

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem jOrbitKernel_le_liftL (hG : IsStarGroup G Ω) (i : D'.ι) :
    jOrbitKernel G Ω ≤ liftL D' i := by
  rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α]
  intro k hk
  refine ⟨(Subgroup.mem_inf.mp hk).1, ?_⟩
  change orbitRestrict G α k ∈ D'.L i
  rw [(orbitRestrict_eq_one_iff α).mpr (Subgroup.mem_inf.mp hk).2]
  exact one_mem _

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem conj_mem_liftL (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {i : D'.ι} {h g : G}
    (hh : h ∈ jHull G Ω) (hg : g ∈ liftL D' i) : h * g * h⁻¹ ∈ liftL D' i := by
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hh hg.1) (inv_mem hh), ?_⟩
  change orbitRestrict G α (h * g * h⁻¹) ∈ D'.L i
  rw [map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp (D'.le_normalizer i
    (map_jHull_le hG hint α ⟨h, hh, rfl⟩)) _).mp hg.2

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem le_normalizer_liftL (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    jHull G Ω ≤ Subgroup.normalizer (liftL D' i : Set G) := fun h hh =>
  Subgroup.mem_normalizer_iff.mpr fun g => ⟨conj_mem_liftL hG hint hh, fun hg => by
    have h1 := conj_mem_liftL hG hint (inv_mem hh) hg
    rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at h1⟩

end Lift

section KR2

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] {α : Ω} {D' : HoltData (orbitGroup G α) (OddOrbits G α)}

theorem W_le_map_blockEven (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (β : Ω) (i : D'.ι) :
    D'.W (@orbitPoint G _ Ω _ hG.isPretransitive α β) i ≤
      (Subgroup.closure (longInvAt G Ω β) ⊓ blockEven G β).map (orbitRestrict G α) := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  set C := (Subgroup.closure (longInvAt G Ω β) ⊓ blockEven G β).map (orbitRestrict G α) with hC
  obtain ⟨x, hx⟩ := hG.longInvAt_nonempty β
  have hxX := orbitRestrict_mem_longInvAt hG hint hx (α := α)
  set xH : jHull (orbitGroup G α) (OddOrbits G α) :=
    ⟨orbitRestrict G α x, mem_jHull_of_mem_longInv hxX.1⟩
  have hlift : ∀ l : jHull (orbitGroup G α) (OddOrbits G α), (l : orbitGroup G α) ∈ D'.L i →
      (l : orbitGroup G α) • orbitPoint G α β = orbitPoint G α β →
      ∃ g ∈ jHull G Ω, g • β = β ∧ orbitRestrict G α g = l := fun l hl hlB => by
    obtain ⟨g, hg, hgl⟩ := L_le_map_jHull hG hO hint D' i hl
    have hgB : g ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β) :=
      (orbitRestrict_smul_orbitPoint_eq_iff (α := α)).mp (by rw [hgl]; exact hlB)
    have hgβ : β ∈ orbit (jOddCore G Ω) (g • β) := by
      rw [orbit_jOddCore_eq hG, orbit_eq_iff.mpr (mem_stabilizer_iff.mp hgB ▸
        Set.smul_mem_smul_set (mem_orbit_self β))]
      exact mem_orbit_self β
    obtain ⟨⟨o, ho⟩, hoβ⟩ := hgβ
    refine ⟨o * g, mul_mem (jOddCore_le_jHull ho) hg, by rw [mul_smul]; exact hoβ, ?_⟩
    rw [map_mul, (orbitRestrict_eq_one_iff α).mpr
      (pPrimeCore_le_oddOrbitsKernel α (jOddCore_le_pPrimeCore ho)), one_mul, hgl]
  have hT : D'.wModel (orbitPoint G α β) i ≤
      ((D'.L i ⊓ C).subgroupOf (jHull (orbitGroup G α) (OddOrbits G α))).map (D'.ρ i) := by
    rw [HoltData.wModel, mulLongInvClosure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    obtain ⟨l, hlL, hlB, hlu, -⟩ :=
      D'.exists_mem_L_conj_rho_eq hxX (mem_longInvAt_subgroup_perm_iff.mp hu) u.2
    obtain ⟨l', hlL', hlB', hlv, -⟩ :=
      D'.exists_mem_L_conj_rho_eq hxX (mem_longInvAt_subgroup_perm_iff.mp hv) v.2
    obtain ⟨g, hgH, hgB, hgl⟩ := hlift l hlL hlB
    obtain ⟨g', hgH', hgB', hgl'⟩ := hlift l' hlL' hlB'
    refine ⟨(l * xH * l⁻¹) * (l' * xH * l'⁻¹), Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩,
      by rw [map_mul, hlu, hlv]; rfl⟩
    · have e : (((l * xH * l⁻¹) * (l' * xH * l'⁻¹) : jHull (orbitGroup G α) (OddOrbits G α)) :
          orbitGroup G α) = (l : orbitGroup G α) * (orbitRestrict G α x *
            ((l : orbitGroup G α)⁻¹ * l') * (orbitRestrict G α x)⁻¹) * (l' : orbitGroup G α)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, xH]
        rw [inv_eq_self_of_mem_longInv hxX.1]
        group
      rw [e]
      refine (D'.L i).mul_mem ((D'.L i).mul_mem hlL ?_) ((D'.L i).inv_mem hlL')
      exact (Subgroup.mem_normalizer_iff.mp (D'.le_normalizer i
        (mem_jHull_of_mem_longInv hxX.1)) _).mp ((D'.L i).mul_mem ((D'.L i).inv_mem hlL) hlL')
    · have hgx : g * x * g⁻¹ ∈ longInvAt G Ω β := by
        have h1 := conj_mem_longInvAt hx g
        rwa [hgB] at h1
      have hgx' : g' * x * g'⁻¹ ∈ longInvAt G Ω β := by
        have h1 := conj_mem_longInvAt hx g'
        rwa [hgB'] at h1
      refine ⟨(g * x * g⁻¹) * (g' * x * g'⁻¹), Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mul_mem (Subgroup.subset_closure hgx) (Subgroup.subset_closure hgx')
      · exact mul_mem_blockEven hO hgx.1 hgx'.1 (mem_stabilizer_orbit_of_mem_longInvAt hgx)
          (mem_stabilizer_orbit_of_mem_longInvAt hgx')
      · simp only [map_mul, map_inv, hgl, hgl', Subgroup.coe_mul, Subgroup.coe_inv, xH]
  intro w hw
  obtain ⟨hwL, w', rfl, hw'W⟩ := HoltData.mem_W.mp hw
  obtain ⟨c, hcC, hcw⟩ := hT hw'W
  obtain ⟨hcL, hcC⟩ := Subgroup.mem_subgroupOf.mp hcC
  rw [← HoltData.eq_of_rho_eq_of_mem_L hOX hcL hwL hcw]
  exact hcC

theorem exists_isPGroup_map_eq_W (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (β : Ω) (i : D'.ι)
    {U : Subgroup (orbitGroup G α)} (hU : IsPGroup 2 U)
    (hUW : U ≤ D'.W (@orbitPoint G _ Ω _ hG.isPretransitive α β) i) :
    ∃ V : Subgroup G, V ≤ jHull G Ω ⊓ blockEven G β ∧
      V ≤ fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) β) ∧ IsPGroup 2 V ∧
        V.map (orbitRestrict G α) = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcl : Subgroup.closure (longInvAt G Ω β) ≤ jHull G Ω :=
    Subgroup.closure_mono (longInvAt_subset_longInv β)
  obtain ⟨V, -, hVle, hV2, hVU⟩ := exists_isPGroup_map_eq_of_map_le (orbitRestrict G α) hU
    ((hUW.trans (W_le_map_blockEven hG hO hint β i)).trans
      (Subgroup.map_mono (inf_le_inf_right _ hcl))) IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  refine ⟨V, hVle, fun v hv => ?_, hV2, hVU⟩
  obtain ⟨n, hn⟩ := hV2 ⟨v, hv⟩
  exact mem_fixingSubgroup_of_mem_blockEven (Subgroup.mem_inf.mp (hVle hv)).2 (n := n)
    (by simpa using congrArg Subtype.val hn)

theorem exists_mem_blockEven_orbitRestrict_eq (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (hall : ∀ i, ¬ IsOuterFactor (D'.M i)) {β : Ω} {t : G} (ht : t ∈ longInvAt G Ω β) :
    ∃ y ∈ Subgroup.closure (longInvAt G Ω β) ⊓ blockEven G β,
      orbitRestrict G α y = orbitRestrict G α t := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  have htX := orbitRestrict_mem_longInvAt hG hint ht (α := α)
  have h1 := (HoltData.mem_iSup_W_iff_of_mem_longInvAt (D := D') hOX htX).mpr hall
  obtain ⟨y, hy, hyt⟩ := (iSup_le fun i => W_le_map_blockEven hG hO hint β i) h1
  exact ⟨y, hy, hyt⟩

theorem exists_isPGroup_rho_eq (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (β : Ω) (i : D'.ι)
    {U : Subgroup (Equiv.Perm (D'.Ψc i))} (hU : IsPGroup 2 U)
    (hUW : U ≤ D'.wModel (@orbitPoint G _ Ω _ hG.isPretransitive α β) i) :
    ∃ V : Subgroup G, V ≤ liftL D' i ∧ V ≤ fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) β) ∧
      IsPGroup 2 V ∧
      (∀ v ∈ V, ∀ hv : v ∈ jHull G Ω,
        D'.ρ i ⟨orbitRestrict G α v, map_jHull_le hG hint α ⟨v, hv, rfl⟩⟩ ∈ U) ∧
      ∀ u ∈ U, ∃ v ∈ V, ∃ hv : v ∈ jHull G Ω,
        D'.ρ i ⟨orbitRestrict G α v, map_jHull_le hG hint α ⟨v, hv, rfl⟩⟩ = u := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  set B := orbitPoint G α β
  set U' : Subgroup (orbitGroup G α) :=
    D'.W B i ⊓ (U.comap (D'.ρ i)).map (jHull (orbitGroup G α) (OddOrbits G α)).subtype
  have hU'W : U' ≤ D'.W B i := inf_le_left
  have hU'2 : IsPGroup 2 U' := by
    rintro ⟨w, hw⟩
    obtain ⟨hwW, w', hw'U, rfl⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨n, hn⟩ := hU ⟨D'.ρ i w', hw'U⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : D'.ρ i (w' ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have h2 := HoltData.mem_jOddCore_of_mem_L (h := w' ^ 2 ^ n)
      (by rw [Subgroup.coe_pow]; exact pow_mem (D'.W_le_L B i hwW) _) h1
    rw [hOX, Subgroup.mem_bot, Subgroup.coe_pow] at h2
    simpa using h2
  obtain ⟨V, hVle, hVF, hV2, hVU⟩ := exists_isPGroup_map_eq_W hG hO hint β i hU'2 hU'W
  have hVU' : ∀ v ∈ V, orbitRestrict G α v ∈ U' := fun v hv => hVU ▸ Subgroup.mem_map_of_mem _ hv
  refine ⟨V, fun v hv => ⟨(Subgroup.mem_inf.mp (hVle hv)).1, ?_⟩, hVF, hV2, fun v hv hvH => ?_,
    fun u hu => ?_⟩
  · exact D'.W_le_L B i (Subgroup.mem_inf.mp (hVU' v hv)).1
  · obtain ⟨w', hw'U, hw'⟩ := (Subgroup.mem_inf.mp (hVU' v hv)).2
    rw [show (⟨orbitRestrict G α v, map_jHull_le hG hint α ⟨v, hvH, rfl⟩⟩ :
      jHull (orbitGroup G α) (OddOrbits G α)) = w' from Subtype.ext hw'.symm]
    exact hw'U
  · obtain ⟨l, hlL, hlu⟩ := HoltData.mem_M.mp (D'.wModel_le_M B i (hUW hu))
    have hlU' : (l : orbitGroup G α) ∈ U' := Subgroup.mem_inf.mpr
      ⟨HoltData.mem_W.mpr ⟨hlL, l, rfl, hlu ▸ hUW hu⟩, l,
        (Subgroup.mem_comap.mpr (by rw [hlu]; exact hu) : l ∈ U.comap (D'.ρ i)), rfl⟩
    rw [← hVU] at hlU'
    obtain ⟨v, hv, hvl⟩ := hlU'
    refine ⟨v, hv, (Subgroup.mem_inf.mp (hVle hv)).1, ?_⟩
    rw [← hlu]
    congr 1
    exact Subtype.ext hvl

end KR2

section T6

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem HoltData.exists_conj_t_mul_mem_jOddCore (hG : IsStarGroup G Ω) (D : HoltData G Ω)
    {u : G} (hu : u ∈ longInv G Ω) :
    ∃ c ∈ D.socPre, c * D.t * c⁻¹ * u ∈ jOddCore G Ω := by
  have := hG.isPretransitive
  obtain ⟨β, hβ⟩ := exists_mem_longInvAt hu
  obtain ⟨γ, hγ⟩ := exists_mem_longInvAt D.t_mem
  obtain ⟨⟨h, hh⟩, hhγ⟩ := (D.mem_orbit_sup_finsetSup_iff Finset.univ γ β).mpr
    fun j hj => absurd (Finset.mem_univ j) hj
  rw [Finset.sup_univ_eq_iSup] at hh
  change h • γ = β at hhγ
  have ht' : h * D.t * h⁻¹ ∈ longInvAt G Ω β := by
    have h1 := conj_mem_longInvAt hγ h
    rwa [hhγ] at h1
  obtain ⟨l, hl, hlβ, hly⟩ := D.exists_conj_rho_eq ht' Finset.univ
    (fun i => D.ρ i ⟨u, mem_jHull_of_mem_longInv hu⟩) (fun i _ => D.rho_mem_longInvAt hβ i)
    (fun i _ => ⟨_, rfl⟩)
  rw [Finset.sup_univ_eq_iSup] at hl
  refine ⟨l * h, mul_mem hl hh, ?_⟩
  set w := (l : G) * (h * D.t * h⁻¹) * (l : G)⁻¹
  have hw : w ∈ longInvAt G Ω β := by
    have h1 := conj_mem_longInvAt ht' l
    rwa [hlβ] at h1
  have hwH := mem_jHull_of_mem_longInv hw.1
  have huH := mem_jHull_of_mem_longInv hu
  have hk : w * u ∈ jOrbitKernel G Ω := by
    refine (D.mem_jOrbitKernel_iff_rho (h := ⟨w, hwH⟩ * ⟨u, huH⟩)).mpr fun i => ?_
    have h1 := hly i (Finset.mem_univ i)
    rw [map_mul, show (⟨w, hwH⟩ : jHull G Ω) =
      l * ⟨h * D.t * h⁻¹, mem_jHull_of_mem_longInv ht'.1⟩ * l⁻¹ from rfl, h1, ← map_mul,
      show (⟨u, huH⟩ : jHull G Ω) * ⟨u, huH⟩ = 1 from
        Subtype.ext (mul_self_eq_one_of_mem_longInv hu), map_one]
  have e : (l : G) * h * D.t * ((l : G) * h)⁻¹ * u = w * u := by
    simp only [w]
    group
  rw [e]
  by_cases hN : CFSG.pPrimeCore 2 G = ⊥
  · have hO : jOddCore G Ω = ⊥ := le_bot_iff.mp (hN ▸ jOddCore_le_pPrimeCore)
    rw [jOrbitKernel_eq_bot hO] at hk
    rw [Subgroup.mem_bot.mp hk]
    exact one_mem _
  · rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG β] at hk
    rw [jOddCore_eq_jHull_inf_pPrimeCore]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hk).1, blockEven_inf_oddOrbitsKernel_le hG β β
      (Subgroup.mem_inf.mpr ⟨mul_mem_blockEven hN hw.1 hu (mem_stabilizer_orbit_of_mem_longInvAt hw)
        (mem_stabilizer_orbit_of_mem_longInvAt hβ), (Subgroup.mem_inf.mp hk).2⟩)⟩

theorem HoltData.mul_mem_socPre (hG : IsStarGroup G Ω) (D : HoltData G Ω) {u v : G}
    (hu : u ∈ longInv G Ω) (hv : v ∈ longInv G Ω) : u * v ∈ D.socPre := by
  obtain ⟨c, hc, hcu⟩ := D.exists_conj_t_mul_mem_jOddCore hG hu
  obtain ⟨c', hc', hcv⟩ := D.exists_conj_t_mul_mem_jOddCore hG hv
  have htt := mul_self_eq_one_of_mem_longInv D.t_mem
  have hti : D.t⁻¹ = D.t := inv_eq_self_of_mem_longInv D.t_mem
  set o := c * D.t * c⁻¹ * u
  set o' := c' * D.t * c'⁻¹ * v
  have e : u * v = c * (D.t * (c⁻¹ * o * c') * D.t⁻¹) * c'⁻¹ * o' := by
    simp only [o, o', hti]
    calc u * v = c * (D.t * D.t) * c⁻¹ * u * (c' * (D.t * D.t) * c'⁻¹ * v) := by
          rw [htt]
          group
      _ = _ := by group
  rw [e]
  have hcS := D.socPre_le_jHull hc
  refine mul_mem (mul_mem (mul_mem hc (D.conj_mem_socPre (mem_jHull_of_mem_longInv D.t_mem)
    (mul_mem (mul_mem (inv_mem hc) (D.jOddCore_le_socPre hcu)) hc'))) (inv_mem hc'))
    (D.jOddCore_le_socPre hcv)

end T6

end CFSG.Holt.H78
