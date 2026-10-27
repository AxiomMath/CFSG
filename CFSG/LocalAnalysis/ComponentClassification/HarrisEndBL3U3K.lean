module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts

theorem EndB.eq_one_of_isSolvable_range {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (f : A →* B) (hs : Group.IsSolvable f.range) (a : A) : f a = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases subsingleton_or_nontrivial f.range with h | h
  · exact congrArg Subtype.val (Subsingleton.elim (⟨f a, a, rfl⟩ : f.range) 1)
  · exact absurd hs (Group.IsPerfect.not_isSolvable f.range)

theorem EndB.eight_mul_card_inf_le
    {G : Type} [Group G]
    [Finite G] {K P : Subgroup G} {w : G} (hK : ⁅K, K⁆ = K)
    (hL : IsL34Type (K ⧸ Open.fusionZStar K)) (hP : IsSylowTwoIn P K)
    (hwN : w ∈ normalizer (K : Set G)) (hw2 : w * w = 1) (hwK : w ∉ withKernel K) :
    8 * Nat.card ↥(P ⊓ centralizer ({w} : Set G)) ≤ Nat.card P := by
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨r, hrR, hr2, hrS, hr⟩ :=
    exists_involution_realization hK hwN hw2 hwK hqS hqsurj hqker
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  set C : Subgroup G := centralizer ({w} : Set G) with hCd
  set φ : ↥(P ⊓ C) →* Equiv.Perm (Fin 42) :=
    (q.comp (jq K)).comp (Subgroup.inclusion (inf_le_left.trans hP.1)) with hφ
  have hφy : ∀ y : ↥(P ⊓ C), φ y = q (jq K ⟨y, hP.1 y.2.1⟩) := fun y => rfl
  have hrange : φ.range ≤ T0 ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42))) := by
    rintro _ ⟨y, rfl⟩
    rw [hφy]
    refine ⟨(hT _).2 ⟨y, y.2.1, _, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have hyw : (y : G) * w = w * y := mem_centralizer_singleton_iff.mp y.2.2
    have hfix : w⁻¹ * y * w = y := by
      calc w⁻¹ * y * w = w⁻¹ * (y * w) := by group
        _ = w⁻¹ * (w * y) := by rw [hyw]
        _ = y := by group
    have h1 := hr (jq K ⟨y, hP.1 y.2.1⟩)
    rw [betaHat_jq, show conjJ K hwN ⟨y, hP.1 y.2.1⟩ = ⟨y, hP.1 y.2.1⟩ from
      Subtype.ext hfix] at h1
    calc q (jq K ⟨y, hP.1 y.2.1⟩) * r = r * q (jq K ⟨y, hP.1 y.2.1⟩) * r⁻¹ * r := by
          rw [← h1]
      _ = r * q (jq K ⟨y, hP.1 y.2.1⟩) := by group
  have hker : Nat.card φ.ker ≤ Nat.card ↥(P ⊓ zStarIn K) := by
    have hmem : ∀ y : φ.ker, ((y : ↥(P ⊓ C)) : G) ∈ P ⊓ zStarIn K := by
      intro y
      refine ⟨y.1.2.1, (mem_zStarIn_iff (hP.1 y.1.2.1)).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker, ← hφy]
      exact y.2
    refine Nat.card_le_card_of_injective (fun y : φ.ker => (⟨_, hmem y⟩ : ↥(P ⊓ zStarIn K)))
      fun a b hab => ?_
    have h1 := congrArg (fun x : ↥(P ⊓ zStarIn K) => (x : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcardPC : Nat.card ↥(P ⊓ C) ≤ Nat.card ↥(P ⊓ zStarIn K) * 8 := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
    exact Nat.mul_le_mul hker ((Subgroup.card_le_of_le hrange).trans
      (card_T0_inf_le_eight hrR hr2 hrS))
  have hcardP : Nat.card P = 64 * Nat.card ↥(P ⊓ zStarIn K) := by
    have hPP : pullP K P hP.1 (T0.comap q) = P := by
      ext y
      rw [mem_pullP]
      exact ⟨fun ⟨hy, _⟩ => hy, fun hy => ⟨hy, (hT _).2 ⟨y, hy, _, rfl⟩⟩⟩
    calc Nat.card P = Nat.card (pullP K P hP.1 (T0.comap q)) := by rw [hPP]
      _ = 64 * Nat.card ↥(P ⊓ zStarIn K) := by
        rw [card_pullP hP2 hT le_rfl,
          card_comap_eq q T0 (fun t ht => hqsurj t (T0_le_S ht)), card_T0,
          Nat.card_congr ζ.toEquiv]
  omega

theorem EndB.not_mem_withKernel {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {w : G} (hL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hq : CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hwN : w ∈ normalizer (K : Set G))
    (hw2 : w * w = 1)
    (hAperf : ⁅GSThmB.layerIn (K ⊓ centralizer ({w} : Set G)),
      GSThmB.layerIn (K ⊓ centralizer ({w} : Set G))⁆ =
        GSThmB.layerIn (K ⊓ centralizer ({w} : Set G)))
    (hAeven : 2 ∣ Nat.card ↥(GSThmB.layerIn (K ⊓ centralizer ({w} : Set G))))
    (hA64 : ¬ 64 ∣ Nat.card ↥(GSThmB.layerIn (K ⊓ centralizer ({w} : Set G)))) :
    w ∉ withKernel K := by
  intro hwK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := K ⊓ centralizer ({w} : Set G) with hCd
  set A : Subgroup G := GSThmB.layerIn C with hAd
  have hAC : A ≤ C := map_subtype_le _
  have hAK : A ≤ K := hAC.trans inf_le_left
  have : Group.IsPerfect ↥A := (Subgroup.isPerfect_iff (H := A)).2 hAperf
  obtain ⟨e₀, he₀⟩ := exists_inner hwK hwN
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL
  have hfixC : ∀ (c : G) (hc : c ∈ C), betaHat K hwN (jq K ⟨c, (mem_inf.mp hc).1⟩) =
      jq K ⟨c, (mem_inf.mp hc).1⟩ := by
    intro c hc
    rw [betaHat_jq]
    congr 1
    apply Subtype.ext
    have hcw : c * w = w * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
    rw [coe_conjJ]
    calc w⁻¹ * c * w = w⁻¹ * (c * w) := by group
      _ = w⁻¹ * (w * c) := by rw [hcw]
      _ = c := by group
  have hAodd : ¬ ∀ a : ↥A, jq K ⟨a, hAK a.2⟩ = 1 := by
    intro hall
    set f : ↥A →* ↥(pPrimeCore 2 ↥K) :=
      { toFun := fun a => ⟨⟨a, hAK a.2⟩, by
          have := hall a
          rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective f := fun a b h => by
      have := congrArg (fun x : ↥(pPrimeCore 2 ↥K) => ((x : ↥K) : G)) h
      exact Subtype.ext this
    have hdvd : Nat.card ↥A ∣ Nat.card ↥(pPrimeCore 2 ↥K) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hodd : ¬ 2 ∣ Nat.card ↥(pPrimeCore 2 ↥K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    exact hodd (hAeven.trans hdvd)
  by_cases hq1 : q e₀ = 1
  ·
    have he₀Z : e₀ ∈ center (Jhat K) := hqker ▸ hq1
    have hid : ∀ e, betaHat K hwN e = e := fun e => by
      rw [he₀, mul_assoc, mem_center_iff.mp he₀Z e, inv_mul_cancel_left]
    set φ : ↥C →* Jhat K := (jq K).comp (Subgroup.inclusion inf_le_left) with hφ
    have hsurj : Function.Surjective φ := by
      intro e
      classical
      obtain ⟨k₀, rfl⟩ := jq_surjective K e
      let F := {k : ↥K // jq K k = jq K k₀}
      have : Fintype F := Fintype.ofFinite F
      have hconj : ∀ k : F, jq K (conjJ K hwN k.1) = jq K k₀ := fun k => by
        rw [← betaHat_jq, hid, k.2]
      have hinvol : ∀ k : ↥K, conjJ K hwN (conjJ K hwN k) = k := fun k => by
        apply Subtype.ext
        rw [coe_conjJ, coe_conjJ]
        have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
        rw [hwi, show w * (w * (k : G) * w) * w = (w * w) * k * (w * w) by group, hw2]
        group
      let σ : Equiv.Perm F :=
        { toFun := fun k => ⟨conjJ K hwN k.1, hconj k⟩
          invFun := fun k => ⟨conjJ K hwN k.1, hconj k⟩
          left_inv := fun k => Subtype.ext (hinvol k.1)
          right_inv := fun k => Subtype.ext (hinvol k.1) }
      have hσ : σ ^ 2 ^ 1 = 1 := by
        ext k
        simp only [pow_one, sq, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one,
          id_eq]
        change ((conjJ K hwN (conjJ K hwN k.1) : ↥K) : G) = ((k.1 : ↥K) : G)
        rw [hinvol]
      have hcardF : Fintype.card F = Nat.card ↥(pPrimeCore 2 ↥K) := by
        rw [← Nat.card_eq_fintype_card]
        have heq : {k : ↥K | jq K k = jq K k₀} = (jq K) ⁻¹' {jq K k₀} := by
          ext k
          simp
        have h1 := (Nat.card_congr (Set.equivOfEq heq)).trans
          (Nat.card_congr ((jq K).fiberEquivKer k₀))
        rw [QuotientGroup.ker_mk'] at h1
        exact h1
      have hodd : ¬ 2 ∣ Fintype.card F := by
        rw [hcardF]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
      obtain ⟨k, hk⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ
      have hk' : conjJ K hwN k.1 = k.1 := congrArg Subtype.val hk
      have hkw : (k.1 : G) ∈ centralizer ({w} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        have h1 := congrArg Subtype.val hk'
        rw [coe_conjJ] at h1
        calc (k.1 : G) * w = w * (w⁻¹ * k.1 * w) := by group
          _ = w * k.1 := by rw [h1]
      exact ⟨⟨k.1, mem_inf.mpr ⟨k.1.2, hkw⟩⟩, k.2⟩
    have hker : ¬ 2 ∣ Nat.card φ.ker := by
      set f : φ.ker →* ↥(pPrimeCore 2 ↥K) :=
        { toFun := fun c => ⟨⟨(c : ↥C).1, (mem_inf.mp (c : ↥C).2).1⟩, by
            have hc1 : φ (c : ↥C) = 1 := c.2
            have hc2 : jq K ⟨(c : ↥C).1, (mem_inf.mp (c : ↥C).2).1⟩ = 1 := hc1
            rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hfinj : Function.Injective f := fun a b h => by
        have := congrArg (fun x : ↥(pPrimeCore 2 ↥K) => ((x : ↥K) : G)) h
        exact Subtype.ext (Subtype.ext this)
      have hdvd : Nat.card φ.ker ∣ Nat.card ↥(pPrimeCore 2 ↥K) := by
        rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv]
        exact Subgroup.card_subgroup_dvd_card _
      intro h2
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
        (h2.trans hdvd)
    have hmap := UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel φ hsurj hker
    rw [LocalAnalysis.ComponentInitial.pLayer_two_eq_top_of_isQuasisimple hq]
      at hmap
    have hdvd : Nat.card (Jhat K) ∣ Nat.card ↥A := by
      have h1 : Nat.card ↥A = Nat.card ↥(pLayer ↥C 2) :=
        Subgroup.card_map_of_injective C.subtype_injective
      rw [h1]
      have h2 : Nat.card ↥((pLayer ↥C 2).map φ) ∣ Nat.card ↥(pLayer ↥C 2) :=
        Subgroup.card_map_dvd _ _
      rw [hmap, card_top] at h2
      exact h2
    have h64 : 64 ∣ Nat.card (Jhat K) := by
      have h1 := Subgroup.card_ker_mul_card_range q
      have hS : Nat.card q.range = 20160 := by
        have : q.range = S := by
          ext s
          exact ⟨fun ⟨e, he⟩ => he ▸ hqS e, fun hs => (hqsurj s hs)⟩
        rw [this, card_S]
      rw [hS] at h1
      rw [← h1]
      exact Dvd.dvd.mul_left (by norm_num) _
    exact hA64 (h64.trans hdvd)
  ·
    have he₀2 : q e₀ * q e₀ = 1 := by
      have hc : e₀ * e₀ ∈ center (Jhat K) := by
        rw [mem_center_iff]
        intro e
        have h1 := betaHat_betaHat K hwN hw2 e
        rw [he₀, he₀] at h1
        calc e * (e₀ * e₀) = e₀ * e₀ * ((e₀ * e₀)⁻¹ * e * (e₀ * e₀)) := by group
          _ = e₀ * e₀ * (e₀⁻¹ * (e₀⁻¹ * e * e₀) * e₀) := by group
          _ = e₀ * e₀ * e := by rw [h1]
      rw [← map_mul, ← MonoidHom.mem_ker, hqker]
      exact hc
    have hrR : q e₀ ∈ R := S_le_R (hqS e₀)
    have hord : orderOf (⟨q e₀, hrR⟩ : R) = 2 := by
      refine orderOf_eq_prime (Subtype.ext ?_) fun h => hq1 (congrArg Subtype.val h)
      simp only [OneMemClass.coe_one, pow_two]
      exact he₀2
    have h64 : Nat.card ↥(centralizer ({q e₀} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 64 := by
      rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
      · rw [card_centralizer_S_of_isConj h]
        exact card_C₁
      · exact absurd (hqS e₀) (not_mem_S_of_isConj h not_mem_S_r₂)
      · exact absurd (hqS e₀) (not_mem_S_of_isConj h not_mem_S_r₃)
      · exact absurd (hqS e₀) (not_mem_S_of_isConj h not_mem_S_r₄)
    set ψ : ↥A →* Equiv.Perm (Fin 42) := (q.comp (jq K)).comp (Subgroup.inclusion hAK)
      with hψ
    have hψle : ψ.range ≤ centralizer ({q e₀} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
      rintro _ ⟨a, rfl⟩
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hqS _⟩
      have h1 := hfixC a (hAC a.2)
      rw [he₀] at h1
      change q (jq K ⟨a, hAK a.2⟩) * q e₀ = q e₀ * q (jq K ⟨a, hAK a.2⟩)
      rw [← map_mul, ← map_mul]
      congr 1
      calc jq K ⟨a, hAK a.2⟩ * e₀ = e₀ * (e₀⁻¹ * jq K ⟨a, hAK a.2⟩ * e₀) := by group
        _ = e₀ * jq K ⟨a, hAK a.2⟩ := by rw [h1]
    have hψ2 : IsPGroup 2 ψ.range := by
      have h2 : IsPGroup 2 ↥(centralizer ({q e₀} : Set (Equiv.Perm (Fin 42))) ⊓ S) :=
        IsPGroup.of_card (n := 6) (by rw [h64]; norm_num)
      exact h2.to_le hψle
    have hψ1 : ∀ a : ↥A, ψ a = 1 := EndB.eq_one_of_isSolvable_range ψ
      (by have := hψ2.isNilpotent; infer_instance)
    set χ : ↥A →* Jhat K := (jq K).comp (Subgroup.inclusion hAK) with hχ
    have hχZ : χ.range ≤ center (Jhat K) := by
      rintro _ ⟨a, rfl⟩
      rw [← hqker, MonoidHom.mem_ker]
      exact hψ1 a
    have hχ1 : ∀ a : ↥A, χ a = 1 := EndB.eq_one_of_isSolvable_range χ (by
      have : IsMulCommutative ↥χ.range := ⟨⟨fun a b => Subtype.ext
        (mem_center_iff.mp (hχZ b.2) a)⟩⟩
      infer_instance)
    exact hAodd hχ1

end CFSG.ComponentClassification.HarrisLit
