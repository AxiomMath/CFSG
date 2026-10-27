module

public import CFSG.GH74.Uniqueness.SU.KI6BFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneAlt
public import CFSG.Walter.TwoRank

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup

namespace Strong

theorem card_ge_four_of_two_le_pRank {G : Type} [Group G] [Finite G] {U : Subgroup G}
    (h : 2 ≤ CFSG.Open.pRank 2 U) : 4 ≤ Nat.card U := by
  obtain ⟨E, hEU, -, hE⟩ := SU1.exists_pRank Nat.prime_two.one_lt U
  have h1 : 2 ^ 2 ≤ 2 ^ (CFSG.Open.pRank 2 U) := Nat.pow_le_pow_right (by norm_num) h
  have h2 : Nat.card E ≤ Nat.card U := Subgroup.card_le_of_le hEU
  rw [hE] at h2
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ _ := h1
    _ ≤ _ := h2

theorem gamma_map_le {K : Type} [Group K] [Finite K] (S : Sylow 2 K) (D : Subgroup K)
    (N : Subgroup K) [N.Normal] (hNS : N ≤ (S : Subgroup K))
    (hN : ∀ W : Subgroup K, W ≤ (S : Subgroup K) → 4 ≤ Nat.card W →
      normalizer (W : Set K) ≤ D) :
    CFSG.Open.properTwoGenCoreGamma ((S : Subgroup K).map (QuotientGroup.mk' N)) 2 ≤
      D.map (QuotientGroup.mk' N) := by
  rw [CFSG.ProperTwoGeneratedCore.gamma_le_iff]
  intro U hUS hrank x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x
  let W := U.comap (QuotientGroup.mk' N)
  have hWS : W ≤ (S : Subgroup K) := by
    intro w hw
    obtain ⟨s, hs, hsw⟩ := hUS hw
    have hn : s⁻¹ * w ∈ N := QuotientGroup.eq.mp hsw
    have : w = s * (s⁻¹ * w) := by group
    rw [this]
    exact (S : Subgroup K).mul_mem hs (hNS hn)
  have hW4 : 4 ≤ Nat.card W := by
    have hsurj : Function.Surjective (fun w : W => (⟨QuotientGroup.mk' N w, w.2⟩ : U)) := by
      rintro ⟨u, hu⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N u
      exact ⟨⟨k, hu⟩, rfl⟩
    exact (card_ge_four_of_two_le_pRank hrank).trans (Nat.card_le_card_of_surjective _ hsurj)
  have hxW : x ∈ normalizer (W : Set K) := by
    rw [← Subgroup.comap_normalizer_eq_of_surjective U (QuotientGroup.mk'_surjective N)]
    exact hx
  exact ⟨x, hN W hWS hW4 hxW, rfl⟩

theorem eq_one_or_eq_of_mem_zpowers_sq {K : Type} [Group K] {z t : K} (hz : z ^ 2 = 1)
    (ht : t ∈ zpowers z) : t = 1 ∨ t = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
  have hz' : z ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    rw [pow_two] at hz
    exact hz
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hpow : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, hz', one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hpow, h, zpow_zero]
  · right
    rw [hpow, h, zpow_one]

theorem sq_eq_of_orderOf_mk {K : Type} [Group K] {z : K}
    (hz2 : orderOf z = 2) (huniq : ∀ y : K, orderOf y = 2 → y = z)
    (hcen : center K = zpowers z) {t : K}
    (ht : orderOf (QuotientGroup.mk' (center K) t) = 2) : t ^ 2 = z := by
  have hz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hsq : t ^ 2 ∈ center K := by
    have h1 : (QuotientGroup.mk' (center K) t) ^ 2 = 1 := by
      rw [← ht]; exact pow_orderOf_eq_one _
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hne : t ∉ center K := by
    intro htc
    have h1 : QuotientGroup.mk' (center K) t = 1 := (QuotientGroup.eq_one_iff t).mpr htc
    rw [h1, orderOf_one] at ht
    omega
  rw [hcen] at hsq hne
  rcases eq_one_or_eq_of_mem_zpowers_sq hz hsq with h | h
  · exfalso
    apply hne
    have ht1 : t ≠ 1 := fun h1 => hne (h1 ▸ one_mem _)
    have : orderOf t = 2 := orderOf_eq_prime h ht1
    rw [huniq t this]
    exact mem_zpowers z
  · exact h

theorem orderOf_eq_four_of_sq_eq {K : Type} [Group K] {z t : K} (hz2 : orderOf z = 2)
    (hts : t ^ 2 = z) : orderOf t = 4 := by
  have hz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := t)
    (by rw [pow_one, hts]; exact hz1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hts]; exact hz)
  rw [h]
  norm_num

theorem mem_normalizer_zpowers_of_conj {K : Type} [Group K] {s y : K}
    (h : y * s * y⁻¹ = s ∨ y * s * y⁻¹ = s⁻¹) : y ∈ normalizer (zpowers s : Set K) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have key : (zpowers s).map (MulAut.conj y).toMonoidHom = zpowers (y * s * y⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have key' : (zpowers s).map (MulAut.conj y : K →* K) = zpowers (y * s * y⁻¹) := key
  rw [key']
  rcases h with h | h
  · rw [h]
  · rw [h, zpowers_inv]

theorem exists_conj_mem_sylow {K : Type} [Group K] [Finite K] (S : Sylow 2 K) (D : Subgroup K)
    (hSD : (S : Subgroup K) ≤ D) {t : K} (htD : t ∈ D) (ht : orderOf t = 4) :
    ∃ g ∈ D, g⁻¹ * t * g ∈ (S : Subgroup K) := by
  let t' : D := ⟨t, htD⟩
  have hp : IsPGroup 2 (zpowers t') := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht]
    norm_num
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D (S.subtype hSD) Q
  refine ⟨g, g.2, ?_⟩
  have h1 : t' ∈ (Q : Subgroup D) := hQ (mem_zpowers t')
  rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : ((MulAut.conj g)⁻¹ • t' : D) ∈ (S.subtype hSD : Subgroup D) := h1
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h2
  simpa [t', MulAut.conj_apply, mul_assoc] using h2

theorem centralizer_map_le {K : Type} [Group K] [Finite K] {z : K}
    (hz2 : orderOf z = 2) (huniq : ∀ y : K, orderOf y = 2 → y = z)
    (hcen : center K = zpowers z) (S : Sylow 2 K) (D : Subgroup K)
    (hSD : (S : Subgroup K) ≤ D)
    (hN : ∀ W : Subgroup K, W ≤ (S : Subgroup K) → 4 ≤ Nat.card W →
      normalizer (W : Set K) ≤ D) :
    ∀ t ∈ D.map (QuotientGroup.mk' (center K)), orderOf t = 2 →
      centralizer ({t} : Set (K ⧸ center K)) ≤ D.map (QuotientGroup.mk' (center K)) := by
  intro tb htb hto xb hxb
  obtain ⟨t, htD, rfl⟩ := htb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ xb
  have hz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hts : t ^ 2 = z := sq_eq_of_orderOf_mk hz2 huniq hcen hto
  have hzc : z ∈ center K := hcen ▸ mem_zpowers z
  have ht4 : orderOf t = 4 := orderOf_eq_four_of_sq_eq hz2 hts
  obtain ⟨g, hgD, hgS⟩ := exists_conj_mem_sylow S D hSD htD ht4
  set s : K := g⁻¹ * t * g with hs
  have hgz : g⁻¹ * z * g = z := by
    have := Subgroup.mem_center_iff.mp hzc g⁻¹
    rw [this]
    group
  have hs2 : s ^ 2 = z := by
    calc s ^ 2 = g⁻¹ * t ^ 2 * g := by rw [hs, pow_two, pow_two]; group
      _ = z := by rw [hts, hgz]
  have hs4 : orderOf s = 4 := orderOf_eq_four_of_sq_eq hz2 hs2
  have hs4' : s ^ 4 = 1 := by rw [← hs4]; exact pow_orderOf_eq_one s
  have hc₀ : t⁻¹ * x * t * x⁻¹ ∈ center K := by
    have h1 : (x : K ⧸ center K) * (t : K ⧸ center K) = (t : K ⧸ center K) * (x : K ⧸ center K) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxb
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc ((t : K ⧸ center K))⁻¹ * (x : K ⧸ center K) * (t : K ⧸ center K) *
          ((x : K ⧸ center K))⁻¹
        = ((t : K ⧸ center K))⁻¹ * ((x : K ⧸ center K) * (t : K ⧸ center K)) *
          ((x : K ⧸ center K))⁻¹ := by group
      _ = ((t : K ⧸ center K))⁻¹ * ((t : K ⧸ center K) * (x : K ⧸ center K)) *
          ((x : K ⧸ center K))⁻¹ := by rw [h1]
      _ = 1 := by group
  set c₀ : K := t⁻¹ * x * t * x⁻¹ with hc₀def
  have hc₀z : c₀ = 1 ∨ c₀ = z := eq_one_or_eq_of_mem_zpowers_sq hz (hcen ▸ hc₀)
  set y : K := g⁻¹ * x * g with hy
  have hysy : y * s * y⁻¹ = s * c₀ := by
    have h1 : y * s * y⁻¹ = g⁻¹ * (x * t * x⁻¹) * g := by rw [hy, hs]; group
    have h2 : x * t * x⁻¹ = t * c₀ := by rw [hc₀def]; group
    have h3 : g⁻¹ * c₀ * g = c₀ := by
      have := Subgroup.mem_center_iff.mp hc₀ g⁻¹
      rw [this]
      group
    calc y * s * y⁻¹ = g⁻¹ * (t * c₀) * g := by rw [h1, h2]
      _ = (g⁻¹ * t * g) * (g⁻¹ * c₀ * g) := by group
      _ = s * c₀ := by rw [h3]
  have hsz : s * z = s⁻¹ := by
    have : s * z * s = 1 := by
      calc s * z * s = s ^ 4 := by rw [← hs2]; group
        _ = 1 := hs4'
    exact eq_inv_of_mul_eq_one_left this
  have hynorm : y ∈ normalizer (zpowers s : Set K) := by
    apply mem_normalizer_zpowers_of_conj
    rcases hc₀z with h | h
    · left; rw [hysy, h, mul_one]
    · right; rw [hysy, h, hsz]
  have hzS : zpowers s ≤ (S : Subgroup K) := (Subgroup.zpowers_le).mpr hgS
  have hcard : 4 ≤ Nat.card (zpowers s) := by rw [Nat.card_zpowers, hs4]
  have hyD : y ∈ D := hN (zpowers s) hzS hcard hynorm
  have hxD : x ∈ D := by
    have : x = g * y * g⁻¹ := by rw [hy]; group
    rw [this]
    exact D.mul_mem (D.mul_mem hgD hyD) (D.inv_mem hgD)
  exact ⟨x, hxD, rfl⟩

open CFSG.ProperTwoGeneratedCore.TheoremC in
theorem card_sylow_eq_four_of_bender_dihedral
    {K : Type} [Group K] [Finite K]
    (hB : CFSG.BenderSuzuki.IsBenderGroup K)
    (hD : CFSG.GorensteinWalter.HasDihedralSylowTwo K) (Q : Sylow 2 K) :
    Nat.card (Q : Subgroup K) = 4 := by
  obtain ⟨m, hm, ⟨d⟩⟩ := hD Q
  have hcard := (benderBorelFactsHold K hB Q).center_card
  by_cases hm1 : m = 1
  · subst hm1
    rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
    norm_num
  · exfalso
    have : NeZero (2 ^ m) := ⟨by positivity⟩
    have heven : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
    have hne : 2 ^ m ≠ 2 := by
      intro h2
      have h3 : m = 1 :=
        Nat.pow_right_injective (le_refl 2) (show 2 ^ m = 2 ^ 1 by rw [h2, pow_one])
      omega
    have hle := CFSG.ProperTwoGeneratedCore.Lemma37.card_center_dihedralGroup_le_two heven hne
    let f : {w : K // InCenterOf (Q : Subgroup K) w} → center (DihedralGroup (2 ^ m)) :=
      fun w => ⟨d ⟨w.1, w.2.1⟩, by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := d.surjective g
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (w.2.2 g' g'.2).eq⟩
    have hf : Function.Injective f := by
      intro w w' hww'
      have := d.injective (congrArg Subtype.val hww')
      exact Subtype.ext (congrArg (fun x : (Q : Subgroup K) => (x : K)) this)
    have := Nat.card_le_card_of_injective f hf
    omega

theorem nonempty_mulEquiv_alt5_of_bender_dihedral
    {K : Type} [Group K] [Finite K]
    (hB : CFSG.BenderSuzuki.IsBenderGroup K)
    (hD : CFSG.GorensteinWalter.HasDihedralSylowTwo K) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  exact CFSG.ProperTwoGeneratedCore.Lemma37.nonempty_mulEquiv_alternatingGroup_five_of_isBenderGroup
    hB Q (card_sylow_eq_four_of_bender_dihedral hB hD Q)

end Strong

theorem rankOne_stronglyEmbedded
    (h1 : RankOneFacts) : RankOneStronglyEmbedded := by
  intro K _ _ hK hr hZ S D hSD hD hN
  obtain ⟨z, hz2, huniq, hcen, -, hsimple, hdih⟩ := h1 K hK hr hZ
  have : IsSimpleGroup (K ⧸ center K) := hsimple
  have hZS : center K ≤ (S : Subgroup K) := hZ.le_sylow_of_normal S
  let Sb : Sylow 2 (K ⧸ center K) := S.mapSurjective (QuotientGroup.mk'_surjective (center K))
  have hSb : (Sb : Subgroup (K ⧸ center K)) =
      (S : Subgroup K).map (QuotientGroup.mk' (center K)) := rfl
  let Db : Subgroup (K ⧸ center K) := D.map (QuotientGroup.mk' (center K))
  have hSbDb : (Sb : Subgroup (K ⧸ center K)) ≤ Db := by
    rw [hSb]
    exact Subgroup.map_mono hSD
  have hDb : Db ≠ ⊤ := by
    intro htop
    apply hD
    rw [eq_top_iff]
    intro k _
    have hk : QuotientGroup.mk' (center K) k ∈ Db := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨d, hdD, hdk⟩ := hk
    have hn : d⁻¹ * k ∈ center K := QuotientGroup.eq.mp hdk
    have : k = d * (d⁻¹ * k) := by group
    rw [this]
    exact D.mul_mem hdD (hSD (hZS hn))
  have hnab : ∃ a b : K ⧸ center K, a * b ≠ b * a := hK.2.2
  have heven : Even (Nat.card (K ⧸ center K)) := by
    obtain ⟨m, -, ⟨e⟩⟩ := hdih Sb
    have h2 : Nat.card (Sb : Subgroup (K ⧸ center K)) = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h3 : Nat.card (Sb : Subgroup (K ⧸ center K)) ∣ Nat.card (K ⧸ center K) :=
      Subgroup.card_subgroup_dvd_card _
    rw [h2] at h3
    exact even_iff_two_dvd.mpr ((dvd_mul_right 2 _).trans h3)
  have hrank : 2 ≤ CFSG.Open.twoRank (K ⧸ center K) :=
    CFSG.Walter.two_le_twoRank (K ⧸ center K) hnab heven
  have hcore : CFSG.Open.properTwoGenCoreGamma (Sb : Subgroup (K ⧸ center K)) 2 ≤ Db := by
    rw [hSb]
    exact Strong.gamma_map_le S D (center K) hZS hN
  have hSE := CFSG.ProperTwoGeneratedCore.strongly_embedded_order_of_full_core_centralizer_closure
    Sb Db hDb hSbDb hrank hcore (Strong.centralizer_map_le hz2 huniq hcen S D hSD hN)
  have hB := CFSG.BenderSuzuki.bender_suzuki Db hSE
  exact Strong.nonempty_mulEquiv_alt5_of_bender_dihedral hB hdih

end CFSG.GH74.Uniqueness.SU.K.R6
