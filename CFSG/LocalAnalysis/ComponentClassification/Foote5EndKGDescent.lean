module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKG
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndNP
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCProj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Burgoyne.C

theorem isSubnormal_map_of_range_normal' {A B : Type*} [Group A] [Group B] (γ : A →* B)
    (hnorm : γ.range.Normal) {J : Subgroup A} (hJ : J.IsSubnormal) : (J.map γ).IsSubnormal := by
  have hle : J.map γ ≤ γ.range := map_le_range γ J
  have h1 : (J.map γ.rangeRestrict).IsSubnormal := IsSubnormal.map γ.rangeRestrict_surjective hJ
  have h2 : (J.map γ).subgroupOf γ.range = J.map γ.rangeRestrict := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, h⟩
      exact ⟨j, hj, congrArg Subtype.val h⟩
  exact IsSubnormal.trans hle (h2 ▸ h1) hnorm.isSubnormal

theorem isSolvable_of_commutator_le {X : Type*} [Group X] {H S : Subgroup X}
    (h : ⁅H, H⁆ ≤ S) (hS : Group.IsSolvable ↥S) : Group.IsSolvable ↥H := by
  rw [← Group.isSolvable_commutator_iff]
  have hmap : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have hmem : ∀ x : ↥(commutator ↥H), ((x : ↥H) : X) ∈ S := fun x =>
    h (hmap ▸ mem_map_of_mem H.subtype x.2)
  let f : ↥(commutator ↥H) →* ↥S :=
    (H.subtype.comp (commutator ↥H).subtype).codRestrict S hmem
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : ((a : ↥H) : X) = ((b : ↥H) : X) := congrArg (fun y : ↥S => (y : X)) hab
    exact Subtype.ext (Subtype.ext h1)
  exact Group.isSolvable_of_isSolvable_injective hf

variable {Q : Type} [Group Q]

theorem inf_center_eq_bot_of_center_quotient_eq_bot [Finite Q] (hO : pPrimeCore 2 Q = ⊥)
    {M : Subgroup Q} (hM : center (↥M ⧸ pPrimeCore 2 ↥M) = ⊥) : M ⊓ center Q = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxM, hxZ⟩ := mem_inf.mp hx
  have hc : (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) ∈
      center (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_center_iff.mp hxZ g)
  rw [hM, mem_bot, QuotientGroup.eq_one_iff] at hc
  have hodd : Nat.Coprime 2 (orderOf x) := by
    have h1 := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥M) hc
    rw [Subgroup.orderOf_mk] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hN : (zpowers x).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [(Commute.zpow_right (mem_center_iff.mp hxZ g) k).eq, mul_inv_cancel_right]
    exact zpow_mem_zpowers x k⟩
  have hle : zpowers x ≤ pPrimeCore 2 Q := le_sSup ⟨hN, by rwa [Nat.card_zpowers]⟩
  rw [hO] at hle
  exact hle (mem_zpowers x)

theorem injective_subgroupMap_mk_center {M : Subgroup Q} (hM : M ⊓ center Q = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center Q)).subgroupMap M) := by
  intro a b hab
  have h1 : (QuotientGroup.mk' (center Q) (a : Q)) = QuotientGroup.mk' (center Q) (b : Q) :=
    congrArg Subtype.val hab
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have h2 : (a : Q)⁻¹ * b ∈ M ⊓ center Q := mem_inf.mpr ⟨mul_mem (inv_mem a.2) b.2, h1⟩
  rw [hM, mem_bot, inv_mul_eq_one] at h2
  exact Subtype.ext h2

noncomputable def mapMkCenterEquiv {M : Subgroup Q} (hM : M ⊓ center Q = ⊥) :
    ↥M ≃* ↥(M.map (QuotientGroup.mk' (center Q))) :=
  MulEquiv.ofBijective _ ⟨injective_subgroupMap_mk_center hM,
    (QuotientGroup.mk' (center Q)).subgroupMap_surjective M⟩

theorem orderOf_mk_center_eq_two {b : Q} (hb : orderOf b = 2) (hbZ : b ∉ center Q) :
    orderOf (QuotientGroup.mk' (center Q) b) = 2 := by
  refine orderOf_eq_prime ?_ fun h => hbZ ((QuotientGroup.eq_one_iff b).mp h)
  rw [← map_pow, ← hb, pow_orderOf_eq_one, map_one]

theorem normal_subgroupOf_map_mk_centralizer (b : Q) :
    (((centralizer ({b} : Set Q)).map (QuotientGroup.mk' (center Q))).subgroupOf
      (centralizer ({QuotientGroup.mk' (center Q) b} : Set (Q ⧸ center Q)))).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rw [mem_subgroupOf] at ha ⊢
  obtain ⟨m, hm, hma⟩ := ha
  obtain ⟨B, hB⟩ := QuotientGroup.mk'_surjective (center Q) (g : Q ⧸ center Q)
  obtain ⟨c, hc, hBc⟩ := exists_central_of_commute_mk (le_refl (center Q)) (A := b) (B := B)
    (by rw [hB]; exact mem_centralizer_singleton_iff.1 g.2)
  refine ⟨B * m * B⁻¹, mem_centralizer_singleton_iff.2
    (conj_mem_centralizer_of_central hc hBc (mem_centralizer_singleton_iff.1 hm)), ?_⟩
  rw [map_mul, map_mul, map_inv, hB, hma]
  rfl

theorem isTwoComponentAt_map_mk_center [Finite Q] {b : Q} (hbZ : b ∉ center Q)
    {M : Subgroup Q} (hM : IsTwoComponentAt b M) (hMZ : M ⊓ center Q = ⊥) :
    IsTwoComponentAt (QuotientGroup.mk' (center Q) b) (M.map (QuotientGroup.mk' (center Q))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hb, hMC, hMpc⟩ := hM
  set ρ := QuotientGroup.mk' (center Q) with hρ
  set C := centralizer ({b} : Set Q) with hC
  set C' := centralizer ({ρ b} : Set (Q ⧸ center Q)) with hC'
  have hCC' : C.map ρ ≤ C' := by
    rintro _ ⟨m, hm, rfl⟩
    rw [hC', mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 hm]
  have hMC' : M.map ρ ≤ C' := (map_mono hMC).trans hCC'
  refine ⟨orderOf_mk_center_eq_two hb hbZ, hMC', ?_⟩
  obtain ⟨hsub, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M C hMC).mp hMpc
  refine (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ C' hMC').mpr
    ⟨?_, CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2 (mapMkCenterEquiv hMZ) hres,
      CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (mapMkCenterEquiv hMZ) hq⟩
  let γ : ↥C →* ↥C' := (ρ.comp C.subtype).codRestrict C' fun c => hCC' ⟨c, c.2, rfl⟩
  have hrange : γ.range = (C.map ρ).subgroupOf C' := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      exact ⟨⟨c, hc⟩, Subtype.ext hcx⟩
  have hnorm : γ.range.Normal := hrange ▸ normal_subgroupOf_map_mk_centralizer b
  have h2 : (M.subgroupOf C).map γ = (M.map ρ).subgroupOf C' := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨m, hm, hmx⟩
      exact ⟨⟨m, hMC hm⟩, hm, Subtype.ext hmx⟩
  rw [← h2]
  exact isSubnormal_map_of_range_normal' γ hnorm hsub

theorem map_mk_mem_coreActionKernel {K : Subgroup Q} (hKZ : K ⊓ center Q = ⊥) {d : Q}
    (hd : d ∈ coreActionKernel K) :
    QuotientGroup.mk' (center Q) d ∈ coreActionKernel (K.map (QuotientGroup.mk' (center Q))) := by
  set ρ := QuotientGroup.mk' (center Q) with hρ
  obtain ⟨hdN, hdK⟩ := hd
  refine ⟨?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨d * k * d⁻¹, (mem_normalizer_iff.mp hdN k).mp hk, by
        simp only [map_mul, map_inv]⟩
    · rintro ⟨k, hk, hky⟩
      refine ⟨d⁻¹ * k * d, ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.mp (inv_mem hdN) k).mp hk
        rwa [inv_inv] at h1
      · rw [map_mul, map_mul, map_inv, hky]
        group
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨o, ho, hoe⟩ := hdK k hk
    refine ⟨mapMkCenterEquiv hKZ o, ?_, ?_⟩
    · rw [← pPrimeCore_map_iso 2 (mapMkCenterEquiv hKZ)]
      exact mem_map_of_mem _ ho
    · change ρ (o : Q) = _
      rw [show (o : Q) = k⁻¹ * d⁻¹ * k * d from hoe]
      simp only [map_mul, map_inv]

theorem not_isSolvable_centralizer_of_endKnownGroupsInput [Finite Q] (hKG : EndKnownGroupsInput)
    (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥) (hcat : Blueprint.Catalog (Q ⧸ center Q))
    {z t : Q} {K P D : Subgroup Q} (hzZ : z ∉ center Q) (hDZ : D ⊓ center Q = ⊥)
    (hK : IsTwoComponentAt z K) [IsSimpleGroup (K ⧸ pPrimeCore 2 K)]
    (hKna : ∃ a b : K ⧸ pPrimeCore 2 K, a * b ≠ b * a) (hKt : FooteFamilyType K)
    (hP : IsSylowOf 2 P K) (htP : t ∈ P) (ht : orderOf t = 2) (hzt : z * t = t * z)
    (hzD : z ∈ D) (hD : D ≤ centralizer ({z} : Set Q) ⊓ coreActionKernel K)
    (hPD : P ≤ centralizer (D : Set Q)) (hDd : AschbacherTheorem3.IsDihedralTwoGroup D)
    (hD8 : 8 ≤ Nat.card D)
    (hNP : ∀ b ∈ D, orderOf b = 2 → ∃ Y : Subgroup Q, IsTwoComponentAt b Y ∧ P ≤ Y ∧
      Nonempty (Y ⧸ pPrimeCore 2 Y ≃* K ⧸ pPrimeCore 2 K)) :
    ¬ Group.IsSolvable ↥(centralizer ({z * t} : Set Q)) := by
  intro hsolv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (center Q) with hρ
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  have hKZ : K ⊓ center Q = ⊥ :=
    inf_center_eq_bot_of_center_quotient_eq_bot hO (center_eq_bot_of_isSimpleGroup hKna)
  have hPZ : P ⊓ center Q = ⊥ := eq_bot_iff.mpr fun x hx => by
    rw [← hKZ]
    exact mem_inf.mpr ⟨hP.le (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  set eK := mapMkCenterEquiv hKZ with heK
  have hK' : IsTwoComponentAt (ρ z) (K.map ρ) := isTwoComponentAt_map_mk_center hzZ hK hKZ
  have htK : t ∈ K := hP.le htP
  have htZ : t ∉ center Q := fun h => by
    have h1 : t ∈ K ⊓ center Q := mem_inf.mpr ⟨htK, h⟩
    rw [hKZ, mem_bot] at h1
    rw [h1, orderOf_one] at ht
    omega
  have ht' : orderOf (ρ t) = 2 := orderOf_mk_center_eq_two ht htZ
  have ht'K : ρ t ∈ K.map ρ := mem_map_of_mem ρ htK
  have ht'sq : ρ t * ρ t = 1 := by rw [← sq, ← ht', pow_orderOf_eq_one]
  have hsolvX : Group.IsSolvable ↥(centralizer ({ρ z * ρ t} : Set (Q ⧸ center Q))) := by
    have h1 : Group.IsSolvable ↥((centralizer ({z * t} : Set Q)).map ρ) :=
      Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
    rw [← map_mul]
    exact isSolvable_of_commutator_le (commutator_centralizer_le_mk (le_refl _) (z * t)) h1
  set eKq : K ⧸ pPrimeCore 2 K ≃* ↥(K.map ρ) ⧸ pPrimeCore 2 ↥(K.map ρ) :=
    UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eK with heKq
  have : IsSimpleGroup (↥(K.map ρ) ⧸ pPrimeCore 2 ↥(K.map ρ)) := eKq.symm.isSimpleGroup
  refine hKG (Q ⧸ center Q) inferInstance hcat (ρ z) (ρ t) (K.map ρ) (P.map ρ) (D.map ρ) hK' ?_
    inferInstance (footeFamilyType_of_mulEquiv eK.symm hKt) ?_ ?_ (mem_map_of_mem ρ htP) ht'
    (by rw [← map_mul, ← map_mul, hzt]) (mem_map_of_mem ρ hzD) ?_ ?_
    (Sol78.F514.isDihedralTwoGroup_of_mulEquiv (mapMkCenterEquiv hDZ) hDd)
    (by rw [← Nat.card_congr (mapMkCenterEquiv hDZ).toEquiv]; exact hD8) ?_ ?_ hsolvX
  ·
    intro K₂ hK₂
    by_contra hne
    exact Sol78.F514.not_isSolvable_centralizer_mul_of_ne hK' hK₂ (Ne.symm hne) ht'K ht'sq hsolvX
  ·
    refine ⟨fun e => ?_⟩
    have hX := Nat.card_congr e.toEquiv
    have h1 : Nat.card (↥(K.map ρ) ⧸ pPrimeCore 2 ↥(K.map ρ)) ≤ Nat.card ↥(K.map ρ) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h2 : Nat.card ↥(K.map ρ) ≤ Nat.card ↥(centralizer ({ρ z} : Set (Q ⧸ center Q))) :=
      Subgroup.card_le_of_le hK'.2.1
    have h3 : Nat.card ↥(centralizer ({ρ z} : Set (Q ⧸ center Q))) <
        Nat.card (Q ⧸ center Q) := by
      refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h => ?_
      have htop := (Subgroup.card_eq_iff_eq_top _).mp h
      have hzc : ρ z ∈ center (Q ⧸ center Q) := mem_center_iff.mpr fun g =>
        mem_centralizer_singleton_iff.mp (htop ▸ mem_top g)
      rw [center_eq_bot_of_isSimpleGroup hQ.2.2, mem_bot] at hzc
      have h4 := hK'.1
      rw [hzc, orderOf_one] at h4
      omega
    omega
  ·
    refine isSylowOf_of_card (map_mono hP.le) ?_
    rw [← Nat.card_congr (mapMkCenterEquiv hPZ).toEquiv, ← Nat.card_congr eK.toEquiv]
    exact hP.card_eq
  ·
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hdz, hdK⟩ := mem_inf.mp (hD hd)
    refine mem_inf.mpr ⟨?_, map_mk_mem_coreActionKernel hKZ hdK⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp hdz]
  ·
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hPD hp) d hd]
  ·
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (Sol78.F514.inf_centralizer_le_centralizer_mul ht'K))
  ·
    rintro _ ⟨b, hbD, rfl⟩ hb2
    have hbb : b * b = 1 := by
      have h1 : ρ (b * b) = 1 := by rw [map_mul, ← sq, ← hb2, pow_orderOf_eq_one]
      have h2 : b * b ∈ D ⊓ center Q :=
        mem_inf.mpr ⟨mul_mem hbD hbD, (QuotientGroup.eq_one_iff _).mp h1⟩
      rw [hDZ, mem_bot] at h2
      exact h2
    have hbZ : b ∉ center Q := fun h => by
      have h1 : b ∈ D ⊓ center Q := mem_inf.mpr ⟨hbD, h⟩
      rw [hDZ, mem_bot] at h1
      rw [h1, map_one, orderOf_one] at hb2
      omega
    have hb1 : b ≠ 1 := fun h => hbZ (h ▸ one_mem _)
    obtain ⟨Y, hY, hPY, ⟨eY⟩⟩ := hNP b hbD (orderOf_eq_prime (by rw [sq]; exact hbb) hb1)
    have : IsSimpleGroup (Y ⧸ pPrimeCore 2 Y) := eY.isSimpleGroup
    have hYna : ∃ a c : Y ⧸ pPrimeCore 2 Y, a * c ≠ c * a := by
      obtain ⟨a, c, hac⟩ := hKna
      exact ⟨eY.symm a, eY.symm c, fun h => hac (by simpa using congrArg eY h)⟩
    have hYZ : Y ⊓ center Q = ⊥ :=
      inf_center_eq_bot_of_center_quotient_eq_bot hO (center_eq_bot_of_isSimpleGroup hYna)
    exact ⟨Y.map ρ, isTwoComponentAt_map_mk_center hbZ hY hYZ, map_mono hPY,
      ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
        (mapMkCenterEquiv hYZ)).symm.trans (eY.trans eKq)⟩⟩

end CFSG.ComponentClassification.Foote5
