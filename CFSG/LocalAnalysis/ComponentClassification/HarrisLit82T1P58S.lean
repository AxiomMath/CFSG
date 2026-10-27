module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup

section Core

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem comap_pPrimeCore_eq_of_ker_le (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ pPrimeCore 2 G) : (pPrimeCore 2 H).comap f = pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine CFSG.LocalAnalysis.ComponentInitial.le_pPrimeCore
      ((pPrimeCore_normal (p := 2) (G := H)).comap f) ?_
    rw [Nat.coprime_two_left, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hfw : orderOf (f (w : G)) ∣ 2 := by
      have h1 := orderOf_map_dvd f (w : G)
      rwa [Subgroup.orderOf_coe, hw] at h1
    have hodd := CFSG.LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore
      (p := 2) w.2
    have h1 : f (w : G) = 1 := orderOf_eq_one_iff.mp (hodd.symm.eq_one_of_dvd hfw)
    have hwO : (w : G) ∈ pPrimeCore 2 G := hk h1
    have hodd' := CFSG.LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore
      (p := 2) hwO
    rw [← Subgroup.orderOf_coe w] at hw
    rw [hw] at hodd'
    exact absurd hodd' (by norm_num)
  · intro x hx
    have hmap : (pPrimeCore 2 G).map f ≤ pPrimeCore 2 H :=
      CFSG.LocalAnalysis.ComponentInitial.le_pPrimeCore
        ((pPrimeCore_normal (p := 2) (G := G)).map f hf)
        ((pPrimeCore_coprime_card (p := 2) (G := G)).coprime_dvd_right
          (Subgroup.card_map_dvd _ _))
    exact hmap ⟨x, hx, rfl⟩

theorem nonempty_quotient_pPrimeCore_equiv_of_ker_le (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ pPrimeCore 2 G) : Nonempty (G ⧸ pPrimeCore 2 G ≃* H ⧸ pPrimeCore 2 H) := by
  let g : G →* H ⧸ pPrimeCore 2 H := (QuotientGroup.mk' (pPrimeCore 2 H)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : g.ker = pPrimeCore 2 G := by
    rw [← comap_pPrimeCore_eq_of_ker_le f hf hk]
    ext x
    rw [MonoidHom.mem_ker, mem_comap, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

end Core

section Centralizer

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem pPrimeCore_le_fusionZStar : pPrimeCore 2 K ≤ Open.fusionZStar K := by
  intro o ho
  rw [FooteLit.mem_fusionZStar_iff_forall]
  intro x
  have h1 : x⁻¹ * o * x ∈ pPrimeCore 2 K := by
    have := (pPrimeCore_normal (p := 2) (G := K)).conj_mem _ ho x⁻¹
    simpa [mul_assoc] using this
  have h2 : (x * o)⁻¹ * (o * x) = o⁻¹ * (x⁻¹ * o * x) := by group
  rw [h2]
  exact mul_mem (inv_mem ho) h1

theorem exists_mem_centralizer_of_commute_mod {z : K} (hz : orderOf z = 2) (y : K)
    (hy : (QuotientGroup.mk y : K ⧸ pPrimeCore 2 K) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk y) :
    ∃ c ∈ centralizer ({z} : Set K), c⁻¹ * y ∈ pPrimeCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : Fact (IsPGroup 2 ↥(zpowers z)) :=
    ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])⟩
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (zpowers z) (pPrimeCore 2 K)
    (pPrimeCore_normal (p := 2) (G := K)) (pPrimeCore_coprime_card (p := 2) (G := K))
  dsimp only at h
  have hy' : QuotientGroup.mk' (pPrimeCore 2 K) y ∈
      centralizer (((zpowers z).map (QuotientGroup.mk' (pPrimeCore 2 K)) :
        Subgroup (K ⧸ pPrimeCore 2 K)) : Set (K ⧸ pPrimeCore 2 K)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
    rw [map_zpow]
    exact ((Commute.zpow_left hy.symm k).eq)
  rw [h] at hy'
  obtain ⟨c, hc, hcy⟩ := hy'
  refine ⟨c, ?_, ?_⟩
  · have hc' : c ∈ centralizer ((zpowers z : Subgroup K) : Set K) := hc
    rw [mem_centralizer_iff] at hc' ⊢
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hc' z (mem_zpowers z)
  · rw [← QuotientGroup.eq]
    exact hcy

omit [Finite K] in
theorem map_centralizer_le_centralizer (z : K) :
    (centralizer ({z} : Set K)).map (QuotientGroup.mk' (Open.fusionZStar K)) ≤
      centralizer {QuotientGroup.mk' (Open.fusionZStar K) z} := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ centralizer ({z} : Set K) := hy
  rw [mem_centralizer_singleton_iff] at hy' ⊢
  rw [← map_mul, ← map_mul, hy']

theorem map_centralizer_subgroupOf_normal {z : K} (hz : orderOf z = 2) :
    (((centralizer ({z} : Set K)).map (QuotientGroup.mk' (Open.fusionZStar K))).subgroupOf
      (centralizer {QuotientGroup.mk' (Open.fusionZStar K) z})).Normal := by
  set π := QuotientGroup.mk' (Open.fusionZStar K) with hπ
  constructor
  intro a ha b
  rw [mem_subgroupOf] at ha ⊢
  obtain ⟨y, hy, hya⟩ := ha
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Open.fusionZStar K) (b : K ⧸ _)
  have hb : π x * π z = π z * π x := by
    rw [hx]
    exact mem_centralizer_singleton_iff.mp b.2
  have hb' : π (x * z * x⁻¹) = π z := by
    rw [map_mul, map_mul, hb, map_inv, mul_inv_cancel_right]
  set c := z⁻¹ * (x * z * x⁻¹) with hc
  have hcZ : c ∈ Open.fusionZStar K := by
    rw [hc, ← QuotientGroup.eq]
    exact hb'.symm
  have hcen : (QuotientGroup.mk c : K ⧸ pPrimeCore 2 K) ∈ center (K ⧸ pPrimeCore 2 K) := by
    rw [FooteLit.mk_mem_center_iff]
    exact (FooteLit.mem_fusionZStar_iff_forall c).mp hcZ
  set w := x * y * x⁻¹ with hw
  have hyz : y * z = z * y :=
    mem_centralizer_singleton_iff.mp (show y ∈ centralizer ({z} : Set K) from hy)
  have hxz : x * z * x⁻¹ = z * c := by rw [hc]; group
  have hwz : w * (z * c) = (z * c) * w := by
    rw [← hxz, hw]
    calc x * y * x⁻¹ * (x * z * x⁻¹) = x * (y * z) * x⁻¹ := by group
      _ = x * (z * y) * x⁻¹ := by rw [hyz]
      _ = x * z * x⁻¹ * (x * y * x⁻¹) := by group
  have hmod : (QuotientGroup.mk w : K ⧸ pPrimeCore 2 K) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk w := by
    have h1 := congrArg (QuotientGroup.mk : K → K ⧸ pPrimeCore 2 K) hwz
    simp only [QuotientGroup.mk_mul] at h1
    have hcomm := mem_center_iff.mp hcen (QuotientGroup.mk w)
    apply mul_right_cancel (b := (QuotientGroup.mk c : K ⧸ pPrimeCore 2 K))
    calc (QuotientGroup.mk w : K ⧸ pPrimeCore 2 K) * QuotientGroup.mk z * QuotientGroup.mk c
        = QuotientGroup.mk w * (QuotientGroup.mk z * QuotientGroup.mk c) := mul_assoc _ _ _
      _ = QuotientGroup.mk z * QuotientGroup.mk c * QuotientGroup.mk w := h1
      _ = QuotientGroup.mk z * (QuotientGroup.mk w * QuotientGroup.mk c) := by
          rw [mul_assoc, hcomm]
      _ = QuotientGroup.mk z * QuotientGroup.mk w * QuotientGroup.mk c :=
          (mul_assoc _ _ _).symm
  obtain ⟨c', hc', hc'w⟩ := exists_mem_centralizer_of_commute_mod hz w hmod
  refine ⟨c', hc', ?_⟩
  have hcw : π c' = π w := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact pPrimeCore_le_fusionZStar hc'w
  rw [hcw, hw, map_mul, map_mul, map_inv, hx, hya]
  rfl

end Centralizer

section Image

variable {K : Type} [Group K] [Finite K]

theorem comap_fusionZStar_le_pPrimeCore {L : Subgroup K} {z : K} (hzL : z ∈ L)
    (hLz : L ≤ centralizer {z}) (hz : orderOf z = 2) (hzZ : z ∉ Open.fusionZStar K)
    (hc : Nat.card ↥(center (↥L ⧸ pPrimeCore 2 ↥L)) = 2) :
    (Open.fusionZStar K).comap L.subtype ≤ pPrimeCore 2 ↥L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set zh : ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk ⟨z, hzL⟩ with hzh
  have hzhc : zh ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [mem_center_iff]
    intro u
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    rw [hzh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLz a.2))
  have hzh1 : zh ≠ 1 := by
    intro h
    have hO : (⟨z, hzL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h
    have hodd := CFSG.LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore
      (p := 2) hO
    rw [Subgroup.orderOf_mk, hz] at hodd
    exact absurd hodd (by norm_num)
  have hcen : ∀ u ∈ center (↥L ⧸ pPrimeCore 2 ↥L), u = 1 ∨ u = zh := by
    intro u hu
    by_contra hne
    push Not at hne
    have h3 : 3 ≤ Nat.card ↥(center (↥L ⧸ pPrimeCore 2 ↥L)) := by
      have := Fintype.ofFinite ↥(center (↥L ⧸ pPrimeCore 2 ↥L))
      have hs : ({1, ⟨zh, hzhc⟩, ⟨u, hu⟩} :
          Finset ↥(center (↥L ⧸ pPrimeCore 2 ↥L))).card = 3 := by
        rw [Finset.card_eq_three]
        refine ⟨1, ⟨zh, hzhc⟩, ⟨u, hu⟩, ?_, ?_, ?_, rfl⟩
        · exact fun h => hzh1 (congrArg Subtype.val h).symm
        · exact fun h => hne.1 (congrArg Subtype.val h).symm
        · exact fun h => hne.2 (congrArg Subtype.val h).symm
      rw [Nat.card_eq_fintype_card, ← hs]
      exact Finset.card_le_univ _
    omega
  intro n hn
  rw [mem_comap, Subgroup.coe_subtype] at hn
  have hnc : (QuotientGroup.mk n : ↥L ⧸ pPrimeCore 2 ↥L) ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [FooteLit.mk_mem_center_iff]
    intro a
    have h1 := (FooteLit.mem_fusionZStar_iff_forall (n : K)).mp hn (a : K)
    refine CFSG.LocalAnalysis.ComponentInitial.le_pPrimeCore
      ((pPrimeCore_normal (p := 2) (G := K)).comap L.subtype) ?_ h1
    exact (pPrimeCore_coprime_card (p := 2) (G := K)).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ L.subtype_injective)
  rcases hcen _ hnc with h1 | h1
  · exact (QuotientGroup.eq_one_iff n).mp h1
  · exfalso
    have hzn : n⁻¹ * ⟨z, hzL⟩ ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq).mp (h1.trans hzh)
    set o := n⁻¹ * (⟨z, hzL⟩ : ↥L) with ho
    have hz' : z = (n : K) * (o : K) := by rw [ho]; simp
    set π := QuotientGroup.mk' (Open.fusionZStar K)
    have hn1 : π (n : K) = 1 := (QuotientGroup.eq_one_iff (n : K)).mpr hn
    have hπz : π z = π (o : K) := by
      rw [hz', map_mul, hn1, one_mul]
    have hodd := CFSG.LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore
      (p := 2) hzn
    have hodd' : Nat.Coprime 2 (orderOf (π (o : K))) :=
      hodd.coprime_dvd_right ((orderOf_map_dvd π _).trans (Subgroup.orderOf_coe o).dvd)
    have h2 : orderOf (π z) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
      · intro h
        exact hzZ ((QuotientGroup.eq_one_iff z).mp h)
    rw [hπz] at h2
    rw [h2] at hodd'
    exact absurd hodd' (by norm_num)

end Image

theorem harris82Lemma58Spin7_of_51e (h51e : Harris82Lemma51e) : Harris82Lemma58Spin7 := by
  intro K _ _ hK p hp hp2 hch _ z₂ _ _ hz₂ hz₂c _ L₂ _ hL₂ _ hz₂L _ _ _ r hr hcov
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Open.fusionZStar K) with hπ
  have : IsSimpleGroup (K ⧸ Open.fusionZStar K) := by
    obtain ⟨e⟩ := L35.nonempty_fusionZStar_quotient_equiv K
    have := hK.2.2.1
    exact e.isSimpleGroup
  have hzZ : z₂ ∉ Open.fusionZStar K := by
    intro h
    apply hz₂c
    rw [FooteLit.mk_mem_center_iff]
    exact (FooteLit.mem_fusionZStar_iff_forall z₂).mp h
  have hcov' := hcov
  obtain ⟨-, hc, -⟩ := hcov'
  have hN := comap_fusionZStar_le_pPrimeCore hz₂L hL₂.1 hz₂ hzZ hc
  set ρ := π.subgroupMap L₂ with hρ
  have hρs : Function.Surjective ρ := π.subgroupMap_surjective L₂
  have hker : ρ.ker ≤ pPrimeCore 2 ↥L₂ := by
    intro x hx
    apply hN
    rw [mem_comap, Subgroup.coe_subtype]
    have h1 : π (x : K) = 1 := congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff (x : K)).mp h1
  obtain ⟨e⟩ := nonempty_quotient_pPrimeCore_equiv_of_ker_le ρ hρs hker
  have hJ : IsTwoComponentIn (L₂.map π) (centralizer {π z₂}) := by
    have hle : L₂.map π ≤ (centralizer ({z₂} : Set K)).map π := map_mono hL₂.1
    have hC := map_centralizer_le_centralizer (K := K) z₂
    refine ⟨hle.trans hC, ?_, ?_⟩
    ·
      set ψ : ↥(centralizer ({z₂} : Set K)) →* ↥(centralizer {π z₂}) :=
        (π.domRestrict (centralizer ({z₂} : Set K))).codRestrict _ fun x => hC ⟨x, x.2, rfl⟩
        with hψ
      have hrange : ψ.range = ((centralizer ({z₂} : Set K)).map π).subgroupOf
          (centralizer {π z₂}) := by
        ext y
        rw [MonoidHom.mem_range, mem_subgroupOf]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x, x.2, rfl⟩
        · rintro ⟨x, hx, hxy⟩
          exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
      have hmap : (L₂.subgroupOf (centralizer ({z₂} : Set K))).map ψ =
          (L₂.map π).subgroupOf (centralizer {π z₂}) := by
        ext y
        rw [mem_map, mem_subgroupOf]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, hxy⟩
          exact ⟨⟨x, hL₂.1 hx⟩, hx, Subtype.ext hxy⟩
      have hsub : ((L₂.subgroupOf (centralizer ({z₂} : Set K))).map
          ψ.rangeRestrict).IsSubnormal :=
        hL₂.2.1.map ψ.rangeRestrict_surjective
      have hrn : ψ.range.IsSubnormal := by
        rw [hrange]
        exact (map_centralizer_subgroupOf_normal hz₂).isSubnormal
      have hle' : (L₂.subgroupOf (centralizer ({z₂} : Set K))).map ψ ≤ ψ.range :=
        map_le_range ψ _
      have heq : ((L₂.subgroupOf (centralizer ({z₂} : Set K))).map ψ).subgroupOf ψ.range =
          (L₂.subgroupOf (centralizer ({z₂} : Set K))).map ψ.rangeRestrict := by
        ext y
        rw [mem_subgroupOf, mem_map, mem_map]
        constructor
        · rintro ⟨x, hx, hxy⟩
          exact ⟨x, hx, Subtype.ext hxy⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
      rw [← hmap]
      exact IsSubnormal.trans hle' (heq ▸ hsub) hrn
    · refine ⟨?_, LocalCores.isQuasisimple_of_mulEquiv e hL₂.2.2.2⟩
      have := hL₂.2.2.1
      exact Group.IsPerfect.map π
  have hzJ : π z₂ ∈ L₂.map π := ⟨z₂, hz₂L, rfl⟩
  have hπ2 : orderOf (π z₂) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hz₂, pow_orderOf_eq_one, map_one]
    · intro h
      exact hzZ ((QuotientGroup.eq_one_iff z₂).mp h)
  exact h51e (K ⧸ Open.fusionZStar K) p hp hp2 hch (π z₂) hπ2 (L₂.map π) hJ hzJ r hr
    (isCoverOf_of_mulEquiv e hcov)

end CFSG.ComponentClassification.HarrisLit.T1
