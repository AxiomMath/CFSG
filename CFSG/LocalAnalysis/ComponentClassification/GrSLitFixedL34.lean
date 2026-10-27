module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitProd
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Adapters.GorensteinWalter
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Sporadic.HeldB.FixedTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

@[expose] def l34X : Equiv.Perm (Fin 42) := g₁ * g₁ * g₂ * g₁ * g₂

@[expose] def l34XT : Tab := comp 42 (comp 42 (comp 42 (comp 42 g₁T g₁T) g₂T) g₁T) g₂T

theorem tabRep_l34X : TabRep l34XT l34X :=
  (((tabRep_g₁.comp tabRep_g₁).comp tabRep_g₂).comp tabRep_g₁).comp tabRep_g₂

theorem l34_tab_facts :
    comp 42 l34XT (comp 42 l34XT (comp 42 l34XT l34XT)) = idTab 42 ∧
      comp 42 l34XT l34XT ≠ idTab 42 ∧
      comp 42 (comp 42 g₂T l34XT) g₂T = comp 42 l34XT (comp 42 l34XT l34XT) ∧
      g₂T ≠ idTab 42 ∧ g₂T ≠ l34XT ∧ g₂T ≠ comp 42 l34XT l34XT ∧
      g₂T ≠ comp 42 l34XT (comp 42 l34XT l34XT) ∧ comp 42 g₂T g₂T = idTab 42 ∧
      comp 42 g₁T g₅T = comp 42 g₅T g₁T ∧ comp 42 g₂T g₅T = comp 42 g₅T g₂T := by
  decide

theorem l34X_mem_C₂ : l34X ∈ C₂ ∧ g₂ ∈ C₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2⟩ := l34_tab_facts
  have hc1 : g₁ * r₂ = r₂ * g₁ :=
    ((tabRep_g₁.comp tabRep_r₂).eq_iff (tabRep_r₂.comp tabRep_g₁)).mp h1
  have hc2 : g₂ * r₂ = r₂ * g₂ :=
    ((tabRep_g₂.comp tabRep_r₂).eq_iff (tabRep_r₂.comp tabRep_g₂)).mp h2
  have hg1 : g₁ ∈ C₂ := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc1, g₁_mem_S⟩
  have hg2 : g₂ ∈ C₂ := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc2, g₂_mem_S⟩
  exact ⟨mul_mem (mul_mem (mul_mem (mul_mem hg1 hg1) hg2) hg1) hg2, hg2⟩

theorem l34X_relations : l34X ^ 4 = 1 ∧ orderOf l34X = 4 ∧ g₂ * g₂ = 1 ∧
    g₂ * l34X * g₂⁻¹ = l34X⁻¹ ∧ g₂ ∉ zpowers l34X := by
  obtain ⟨h4, h2, hinv, h0, h1', h2', h3', hg2, -, -⟩ := l34_tab_facts
  have hx := tabRep_l34X
  have hx2 := hx.comp hx
  have hx3 := hx.comp hx2
  have hx4 := hx.comp hx3
  have hp4 : l34X ^ 4 = 1 := by
    rw [show l34X ^ 4 = l34X * (l34X * (l34X * l34X)) by simp only [pow_succ', pow_zero, mul_one]]
    exact (hx4.eq_iff TabRep.idTab).mp h4
  have hp2 : l34X ^ 2 ≠ 1 := by
    rw [pow_two]
    exact fun h => h2 ((hx2.eq_iff TabRep.idTab).mpr h)
  have hg2' : g₂ * g₂ = 1 := ((tabRep_g₂.comp tabRep_g₂).eq_iff TabRep.idTab).mp hg2
  have hord : orderOf l34X = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := l34X) (by simpa using hp2)
      (by simpa using hp4)
    simpa using this
  have hg2inv : g₂⁻¹ = g₂ := inv_eq_of_mul_eq_one_right hg2'
  have hrel : g₂ * l34X * g₂⁻¹ = l34X⁻¹ := by
    rw [hg2inv]
    have h1 : g₂ * l34X * g₂ = l34X * (l34X * l34X) :=
      (((tabRep_g₂.comp hx).comp tabRep_g₂).eq_iff hx3).mp hinv
    rw [h1, eq_inv_iff_mul_eq_one]
    calc l34X * (l34X * l34X) * l34X = l34X ^ 4 := by
          simp only [pow_succ', pow_zero, mul_one, mul_assoc]
      _ = 1 := hp4
  refine ⟨hp4, hord, hg2', hrel, fun hmem => ?_⟩
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hkx⟩ := hmem
  interval_cases k
  · exact h0 ((tabRep_g₂.eq_iff TabRep.idTab).mpr (by simpa using hkx.symm))
  · exact h1' ((tabRep_g₂.eq_iff hx).mpr (by simpa using hkx.symm))
  · exact h2' ((tabRep_g₂.eq_iff hx2).mpr (by rw [← hkx, pow_two]))
  · exact h3' ((tabRep_g₂.eq_iff hx3).mpr (by rw [← hkx]; simp only [pow_succ', pow_zero, mul_one]))

theorem exists_sylow_C₂_dihedral :
    ∃ P : Sylow 2 ↥C₂, Nonempty ((P : Subgroup ↥C₂) ≃* DihedralGroup (2 ^ (3 - 1))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h4, hord, hg2, hrel, hnot⟩ := l34X_relations
  obtain ⟨hxC, hgC⟩ := l34X_mem_C₂
  have hinj := HSFLit.injective_dihedralLift 4 l34X g₂ h4 hg2 hrel hord hnot
  have hrange := HSFLit.range_dihedralLift 4 l34X g₂ h4 hg2 hrel
  set D := zpowers l34X ⊔ zpowers g₂ with hD
  have hDC : D ≤ C₂ := sup_le (zpowers_le.mpr hxC) (zpowers_le.mpr hgC)
  have hDcard : Nat.card D = 8 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, DihedralGroup.nat_card]
  have hfac : (Nat.card C₂).factorization 2 = 3 := by
    rw [card_C₂, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcard : Nat.card (D.subgroupOf C₂) = 2 ^ (Nat.card C₂).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv, hDcard, hfac]
    norm_num
  refine ⟨Sylow.ofCard _ hcard, ⟨?_⟩⟩
  exact (subgroupOfEquivOfLe hDC).trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm

theorem eq_seven_of_ordA_eq {q : ℕ} (hq : 1 ≤ q) (h : Open.ordA 1 q = 168) : q = 7 := by
  by_cases h9 : 9 ≤ q
  · exfalso
    have hg : Nat.gcd (1 + 1) (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hpos : 0 < Nat.gcd (1 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hprod : q ^ (1 * (1 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (1 + 1), (q ^ i - 1) =
        q * (q ^ 2 - 1) := by
      simp
    have h1 : 720 ≤ q * (q ^ 2 - 1) := by
      have : 80 ≤ q ^ 2 - 1 := by
        have : 81 ≤ q ^ 2 := by nlinarith
        omega
      nlinarith
    unfold Open.ordA at h
    rw [hprod] at h
    have h2 : q * (q ^ 2 - 1) / 2 ≤ q * (q ^ 2 - 1) / Nat.gcd (1 + 1) (q - 1) :=
      Nat.div_le_div_left hg hpos
    omega
  · push Not at h9
    interval_cases q <;> simp_all [Open.ordA]

theorem lieModel_C₂ : Blueprint.LieModel ↥C₂ .PSL 2 7 1 := by
  have : IsSimpleGroup ↥C₂ := isSimpleGroup_C₂
  obtain ⟨P, ⟨e⟩⟩ := exists_sylow_C₂_dihedral
  rcases Adapters.dihedral_simple_recognition ↥C₂ exists_mul_ne_C₂ P 3 (by norm_num) ⟨e⟩ with
    ⟨p, f, hp, hp2, hf, hmodel⟩ | ⟨⟨e7⟩⟩
  · have hcard := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hmodel).1 rfl
    rw [card_C₂] at hcard
    have hq : p ^ f = 7 := eq_seven_of_ordA_eq (Nat.one_le_pow _ _ hp.pos) hcard.symm
    obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq
    exact Or.inl ⟨by decide, hmodel⟩
  · exfalso
    have h1 := Nat.card_congr e7.toEquiv
    rw [card_C₂, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    norm_num [Nat.factorial] at h1

theorem lieModel_C₃ : Blueprint.LieModel ↥C₃ .PSL 2 5 1 := by
  have : IsSimpleGroup ↥C₃ := isSimpleGroup_C₃
  exact Or.inl ⟨by decide,
    LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _
      (QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty card_C₃)⟩

theorem nontrivial_of_isPComponent {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : IsPComponent 2 K) : Nontrivial K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 K).mp hK
  obtain ⟨-, hs, -⟩ := hq
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have : Nontrivial ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K))
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨a'', rfl⟩ := QuotientGroup.mk'_surjective _ a'
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
  obtain ⟨b'', rfl⟩ := QuotientGroup.mk'_surjective _ b'
  exact hab (by rw [Subsingleton.elim a'' b''])

theorem not_isPComponent_of_isSolvable {X : Type*} [Group X] [Finite X] [Group.IsSolvable X]
    (K : Subgroup X) : ¬ IsPComponent 2 K := by
  intro hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect K := CatalogueBHeldSmallCore.pComponent_perfect 2 K hK
  have : Nontrivial K := nontrivial_of_isPComponent hK
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem eq_top_of_isPComponent_of_isSimpleGroup {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] {K : Subgroup X} (hK : IsPComponent 2 K) : K = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, -, -⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 K).mp hK
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hs with h | h
  · have := nontrivial_of_isPComponent hK
    rw [h] at this
    exact absurd this (not_nontrivial_iff_subsingleton.mpr inferInstance)
  · exact h

theorem nonempty_fusionZStar_equiv_of_simple {X Y : Type*} [Group X] [Finite X] [Group Y]
    [IsSimpleGroup Y] {K : Subgroup X} (hK : IsPComponent 2 K) (e : K ≃* Y) :
    Nonempty (K ⧸ Open.fusionZStar K ≃* Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKs : IsSimpleGroup K := e.isSimpleGroup
  have hZ : Open.fusionZStar K = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hKs (Open.fusionZStar K) inferInstance
      with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, hq⟩ :=
        (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 K).mp hK
      obtain ⟨-, hs, -⟩ := hq
      obtain ⟨f⟩ := nonempty_quotient_center_equiv_fusionZStar K
      have : Nontrivial ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := hs.toNontrivial
      have : Nontrivial (K ⧸ Open.fusionZStar K) := f.symm.toEquiv.nontrivial
      have : Subsingleton (K ⧸ Open.fusionZStar K) := QuotientGroup.subsingleton_iff.mpr h
      exact false_of_nontrivial_of_subsingleton (K ⧸ Open.fusionZStar K)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩

theorem nonempty_fusionZStar_equiv_of_mulEquiv' {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (e : A ≃* B) : Nonempty (A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) := by
  refine GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective e.toMonoidHom e.surjective ?_
  rw [show e.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr e.injective, card_bot]
  norm_num

theorem map_conj_centralizer_inf {M : Type*} [Group M] {H : Subgroup M} {c : M}
    (hc : c ∈ normalizer (H : Set M)) (y : M) :
    (centralizer {c * y * c⁻¹} ⊓ H).map (MulAut.conj c⁻¹).toMonoidHom = centralizer {y} ⊓ H := by
  ext z
  rw [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_inf, mem_centralizer_singleton_iff] at hw
    obtain ⟨hwc, hw⟩ := hw
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine ⟨?_, ?_⟩
    · calc c⁻¹ * w * c * y = c⁻¹ * (w * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * w) * c := by rw [hwc]
        _ = y * (c⁻¹ * w * c) := by group
    · have h1 := (mem_normalizer_iff.mp (inv_mem hc) w).mp hw
      rwa [inv_inv] at h1
  · rintro ⟨hzy, hz⟩
    refine ⟨c * z * c⁻¹, mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp hc z).mp hz⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      calc c * z * c⁻¹ * (c * y * c⁻¹) = c * (z * y) * c⁻¹ := by group
        _ = c * (y * z) * c⁻¹ := by rw [hzy]
        _ = c * y * c⁻¹ * (c * z * c⁻¹) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

@[expose] noncomputable def centralizerInfConjEquiv {M : Type*} [Group M] {H : Subgroup M} {c : M}
    (hc : c ∈ normalizer (H : Set M)) (y : M) :
    (centralizer {c * y * c⁻¹} ⊓ H : Subgroup M) ≃* (centralizer {y} ⊓ H : Subgroup M) :=
  ((centralizer {c * y * c⁻¹} ⊓ H).equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective).trans (MulEquiv.subgroupCongr (map_conj_centralizer_inf hc y))

theorem nonempty_fusionZStar_equiv_of_simple_equiv {F C : Type} [Group F] [Finite F] [Group C]
    [Finite C] [IsSimpleGroup C] (ψ : F ≃* C) {P : Subgroup F} (hP : IsPComponent 2 P) :
    Nonempty (P ⧸ Open.fusionZStar P ≃* C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₁ := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 ψ hP
  obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' (P.equivMapOfInjective ψ.toMonoidHom
    ψ.injective)
  have htop := eq_top_of_isPComponent_of_isSimpleGroup hP₁
  obtain ⟨f⟩ := nonempty_fusionZStar_equiv_of_simple hP₁
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
  exact ⟨eZ.trans f⟩

theorem not_isPComponent_of_equiv_solvable {F C : Type} [Group F] [Finite F] [Group C]
    [Group.IsSolvable C] (ψ : F ≃* C) (P : Subgroup F) : ¬ IsPComponent 2 P := by
  have : Group.IsSolvable F :=
    Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
  exact not_isPComponent_of_isSolvable P

theorem simpleFixedComponents_l34 :
    SimpleFixedComponents IsL34Type fun K _ => IsL2Type 5 K ∨ IsL2Type 7 K := by
  intro S' _ _ hS' hnab hτ σ hσ P hPF hP hPne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstated : Assembly.LowTwoRank.StatedClassicalModel S' .PSL 3 2 2 := by
    rcases hτ with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨θ⟩ := nonempty_equiv_of_stated S' hstated
  obtain ⟨e, he, -⟩ := full_automorphism_action
  set σ' := MulAut.congr θ σ with hσ'def
  set r := e.symm σ' with hrdef
  have her : e r = σ' := e.apply_symm_apply σ'
  have hrs : ∀ s : S, ((σ' s : S) : Equiv.Perm (Fin 42)) =
      (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ := by
    intro s
    have h := he r s
    rw [her] at h
    exact h
  have hσ'2 : σ' * σ' = 1 := by
    refine MulEquiv.ext fun t => ?_
    show σ' (σ' t) = t
    rw [hσ'def, Sporadic.HeldB.congr_apply', Sporadic.HeldB.congr_apply',
      MulEquiv.symm_apply_apply, hσ, MulEquiv.apply_symm_apply]
  have hr2 : r * r = 1 := e.injective (by rw [map_mul, her, hσ'2, map_one])
  set F := FixedCommutingProduct.fixedSubgroup σ with hFdef
  set F' := FixedCommutingProduct.fixedSubgroup σ' with hF'def
  have φ₁ : F ≃* F' := Sporadic.HeldB.fixedSubgroupCongr θ σ
  have hF'map : F'.map S.subtype = centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, s.2⟩
      have h1 := congrArg Subtype.val (show σ' s = s from hs)
      rw [hrs] at h1
      change (s : Equiv.Perm (Fin 42)) * r = r * s
      calc (s : Equiv.Perm (Fin 42)) * r =
          (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ * r := by rw [h1]
        _ = r * s := by group
    · intro hx
      obtain ⟨hxr, hxS⟩ := mem_inf.mp hx
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      change σ' ⟨x, hxS⟩ = ⟨x, hxS⟩
      apply Subtype.ext
      rw [hrs]
      have h1 : x * r = r * x := mem_centralizer_singleton_iff.mp hxr
      change (r : Equiv.Perm (Fin 42)) * x * (r : Equiv.Perm (Fin 42))⁻¹ = x
      rw [← h1]
      group
  have φ₂ : F' ≃* ↥(centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S) :=
    (F'.equivMapOfInjective S.subtype S.subtype_injective).trans (MulEquiv.subgroupCongr hF'map)
  have hPF₁ : IsPComponent 2 (P.subgroupOf F) := hP
  obtain ⟨eP⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hPF).symm
  by_cases hr1 : r = 1
  ·
    exfalso
    have hσ'1 : σ' = 1 := by rw [← her, hr1, map_one]
    have hσ1 : σ = 1 := (MulAut.congr θ).injective (by rw [← hσ'def, hσ'1, map_one])
    have hFtop : F = ⊤ := by
      rw [hFdef, hσ1, eq_top_iff]
      intro x _
      rfl
    have : IsSimpleGroup F :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    have h := eq_top_of_isPComponent_of_isSimpleGroup hPF₁
    apply hPne
    rw [eq_top_iff]
    intro x _
    have hx : (⟨x, hFtop ▸ mem_top x⟩ : F) ∈ P.subgroupOf F := h ▸ mem_top _
    exact hx
  · have hro : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
    have key : ∀ (C : Subgroup (Equiv.Perm (Fin 42))) (ri : Equiv.Perm (Fin 42)),
        C = centralizer {ri} ⊓ S → (∃ c ∈ R, (r : Equiv.Perm (Fin 42)) = c * ri * c⁻¹) →
        Nonempty (F ≃* C) := by
      rintro C ri rfl ⟨c, hc, hrc⟩
      exact ⟨φ₁.trans (φ₂.trans ((MulEquiv.subgroupCongr (by rw [hrc])).trans
        (centralizerInfConjEquiv (R_le_normalizer hc) ri)))⟩
    rcases (orderOf_eq_two_iff r).mp hro with h | h | h | h
    · obtain ⟨ψ⟩ := key C₁ r₁ rfl (eq_conj_of_isConj h)
      have : Group.IsSolvable ↥C₁ := isSolvable_C₁
      exact absurd hPF₁ (not_isPComponent_of_equiv_solvable ψ _)
    · obtain ⟨ψ⟩ := key C₂ r₂ rfl (eq_conj_of_isConj h)
      have : IsSimpleGroup ↥C₂ := isSimpleGroup_C₂
      obtain ⟨f⟩ := nonempty_fusionZStar_equiv_of_simple_equiv ψ hPF₁
      exact Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans f).symm lieModel_C₂)
    · obtain ⟨ψ⟩ := key C₃ r₃ rfl (eq_conj_of_isConj h)
      have : IsSimpleGroup ↥C₃ := isSimpleGroup_C₃
      obtain ⟨f⟩ := nonempty_fusionZStar_equiv_of_simple_equiv ψ hPF₁
      exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans f).symm lieModel_C₃)
    · obtain ⟨ψ⟩ := key C₄ r₄ rfl (eq_conj_of_isConj h)
      have : Group.IsSolvable ↥C₄ := isSolvable_C₄
      exact absurd hPF₁ (not_isPComponent_of_equiv_solvable ψ _)

theorem l34FixedInput : L34FixedInput :=
  properFixedComponents_of_simple
    (fun _ _ _ _ e h => LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
    (fun _ _ _ _ e h => h.imp (LieType.CurtisTits.lieModel_of_mulEquiv e.symm)
      (LieType.CurtisTits.lieModel_of_mulEquiv e.symm))
    simpleFixedComponents_l34

end CFSG.ComponentClassification.GrSLit
