module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39Join
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigQDisc

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem reflTransGen_commFourAdj_subgroupOf {X Y A B : Subgroup G} (hXY : X ≤ Y)
    (h : Relation.ReflTransGen (CommFourIn X) A B) :
    Relation.ReflTransGen (CommFourAdj ↥Y) (A.subgroupOf Y) (B.subgroupOf Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨hb, hc, hbX, hcX, hbc'⟩ := hbc
    refine ih.tail ⟨isKleinFour_subgroupOf hb (hbX.trans hXY),
      isKleinFour_subgroupOf hc (hcX.trans hXY), fun x hx => ?_⟩
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp (hbc' (mem_subgroupOf.mp hx)) y
      (mem_subgroupOf.mp hy))

@[expose] def SolomonQTwoDisconnectedSylowCentFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
      IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') →
      3 ≤ CFSG.Open.pRank 2 K →
      (∃ (S' : Sylow 2 ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'))
          (E F : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')),
          IsKleinFour E ∧ E ≤ S' ∧ IsKleinFour F ∧ F ≤ S' ∧
            ¬ Relation.ReflTransGen
              (CommFourAdj ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')) E F) →
      (∃ D : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'),
          IsKleinFour D ∧ ∀ A : Subgroup G, IsKleinFour A →
            ¬ A ≤ K ⊓ centralizer
              ((D.map ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K').subtype :
                Subgroup G) : Set G)) →
      IsSolomonI (coreQuot K)

section Cent

variable {N K : Subgroup G}

theorem exists_mem_centralizer_of_comm {D : Subgroup G} (hD : IsPGroup 2 D)
    (hDK : D ≤ normalizer (K : Set G)) {a : G} (ha : a ∈ K)
    (hcomm : ∀ d ∈ D, a⁻¹ * d⁻¹ * a * d ∈ oddCoreIn K) :
    ∃ c ∈ K ⊓ centralizer (D : Set G), c⁻¹ * a ∈ oddCoreIn K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := normalizer (K : Set G) with hA
  have hKA : K ≤ A := le_normalizer
  set Nn := (oddCoreIn K).subgroupOf A with hNn
  have hNnn : Nn.Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h1 := map_conj_oddCoreIn (D := K) x.2
    rw [← h1]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hNodd : ¬ 2 ∣ Nat.card Nn := by
    have h1 : Nat.card Nn ∣ Nat.card (oddCoreIn K) := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    intro h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_oddCoreIn K)
      (h2.trans h1)
  set Qd := D.subgroupOf A with hQd
  have hQ2 : IsPGroup 2 Qd := hD.comap_subtype
  have : Fact (IsPGroup 2 Qd) := ⟨hQ2⟩
  set x : ↥A := ⟨a, hKA ha⟩ with hx
  have hxc : QuotientGroup.mk' Nn x ∈ centralizer ((Qd.map (QuotientGroup.mk' Nn) : Subgroup _) :
      Set (↥A ⧸ Nn)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have h1 := hcomm _ (mem_subgroupOf.mp hq)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [mem_subgroupOf]
    have h2 : (((q * x)⁻¹ * (x * q) : ↥A) : G) = a⁻¹ * (q : G)⁻¹ * a * q := by
      simp only [hx, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact h1
  have hcop : Nat.Coprime 2 (Nat.card Nn) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hNodd
  rw [CFSG.centralizer_map_quotient_eq_map_centralizer 2 Qd Nn hNnn hcop] at hxc
  obtain ⟨c, hc, hcx⟩ := hxc
  have hco : c⁻¹ * x ∈ Nn := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
    exact hcx
  have hcD : (c : G) ∈ centralizer (D : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have := (mem_centralizer_iff.mp hc) ⟨s, hDK hs⟩ (mem_subgroupOf.mpr hs)
    exact congrArg Subtype.val this
  have hcoK : ((c⁻¹ * x : ↥A) : G) ∈ oddCoreIn K := mem_subgroupOf.mp hco
  have hcK : (c : G) ∈ K := by
    have h1 : (c : G) = a * ((c⁻¹ * x : ↥A) : G)⁻¹ := by simp [hx]
    rw [h1]
    exact mul_mem ha (inv_mem (map_subtype_le _ hcoK))
  exact ⟨c, ⟨hcK, hcD⟩, hcoK⟩

theorem exists_isKleinFour_map_eq_of_le_range {Y Q : Type} [Group Y] [Finite Y] [Group Q]
    (ψ : Y →* Q) (hker : Odd (Nat.card ψ.ker)) {Eb : Subgroup Q} (hEb : IsKleinFour Eb)
    (hEbr : Eb ≤ ψ.range) : ∃ P : Subgroup Y, IsKleinFour P ∧ P.map ψ = Eb := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEb2 : IsPGroup 2 (Eb.subgroupOf ψ.range) := (isPGroup_of_isKleinFour hEb).comap_subtype
  obtain ⟨P, hP2, -, hPmap⟩ := exists_pSubgroup_lift_of_surjective ψ.rangeRestrict
    (MonoidHom.rangeRestrict_surjective ψ) (A₀ := ⊥) IsPGroup.of_bot hEb2
    (by rw [Subgroup.map_bot]; exact bot_le)
  have hmap : P.map ψ = Eb := by
    have hψ : ψ = ψ.range.subtype.comp ψ.rangeRestrict := by ext; rfl
    rw [hψ, ← Subgroup.map_map, hPmap, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEbr]
  have hinj := CFSG.RankThree.OddKernel.injective_restrict_of_odd ψ hker hP2
  have hinjP : ∀ a ∈ P, ∀ b ∈ P, ψ a = ψ b → a = b := fun a ha b hb hab =>
    congrArg Subtype.val (hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  refine ⟨P, FooteLit.isKleinFour_of_card_eq_four ?_ fun y hy => ?_, hmap⟩
  · have he : P.map ψ = (⊤ : Subgroup P).map (ψ.comp P.subtype) := by
      rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← Subgroup.card_top (G := P), ← Subgroup.card_map_of_injective hinj, ← he, hmap,
      hEb.card_four]
  · refine hinjP _ (pow_mem hy 2) 1 (one_mem P) ?_
    rw [map_pow, map_one]
    exact FooteLit.sq_eq_one_of_isKleinFour hEb (by rw [← hmap]; exact mem_map_of_mem ψ hy)

theorem exists_isKleinFour_le_inf_centralizer {D : Subgroup G} (hD : IsPGroup 2 D)
    (hDK : D ≤ normalizer (K : Set G)) {Ab : Subgroup (coreQuot K)} (hAb : IsKleinFour Ab)
    (hcomm : ∀ a : ↥K, QuotientGroup.mk' (pPrimeCore 2 ↥K) a ∈ Ab →
      ∀ d ∈ D, (a : G)⁻¹ * d⁻¹ * a * d ∈ oddCoreIn K) :
    ∃ A : Subgroup G, IsKleinFour A ∧ A ≤ K ⊓ centralizer (D : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K ⊓ centralizer (D : Set G) with hY
  set ψ : ↥Y →* coreQuot K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left) with hψ
  have hO : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hker : Odd (Nat.card ψ.ker) := by
    have hle : ψ.ker.map Y.subtype ≤ oddCoreIn K := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨(y : G), y.2.1⟩ = 1 := hy
      exact mk_eq_one_iff.mp h1
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective Y.subtype_injective] at hdvd
    exact Odd.of_dvd_nat hO hdvd
  have hrange : Ab ≤ ψ.range := by
    intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) q
    obtain ⟨c, hcY, hca⟩ := exists_mem_centralizer_of_comm hD hDK a.2 (hcomm a hq)
    refine ⟨⟨c, hcY⟩, ?_⟩
    change QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨c, hcY.1⟩ = QuotientGroup.mk' (pPrimeCore 2 ↥K) a
    exact mk_eq_mk_iff.mpr hca
  obtain ⟨P, hP, -⟩ := exists_isKleinFour_map_eq_of_le_range ψ hker hAb hrange
  refine ⟨P.map Y.subtype, FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_, map_subtype_le _⟩
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hP.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hP hv, map_one]

omit [Finite G] in
theorem comm_mul_mem_oddCoreIn_iff {k c a : G} (hk : k ∈ K) (hc : c ∈ coreActionKernel K)
    (ha : a ∈ K) :
    a⁻¹ * (k * c)⁻¹ * a * (k * c) ∈ oddCoreIn K ↔ a⁻¹ * k⁻¹ * a * k ∈ oddCoreIn K := by
  have hy : k⁻¹ * a * k ∈ K := mul_mem (mul_mem (inv_mem hk) ha) hk
  have ho : (k⁻¹ * a * k)⁻¹ * c⁻¹ * (k⁻¹ * a * k) * c ∈ oddCoreIn K :=
    (mem_coreActionKernel.mp hc).2 _ hy
  have e : a⁻¹ * (k * c)⁻¹ * a * (k * c) =
      (a⁻¹ * k⁻¹ * a * k) * ((k⁻¹ * a * k)⁻¹ * c⁻¹ * (k⁻¹ * a * k) * c) := by group
  rw [e]
  exact mul_mem_cancel_right ho

omit [Finite G] in
theorem mk_mem_center_of_mem_coreActionKernel {u : ↥K} (hu : (u : G) ∈ coreActionKernel K) :
    QuotientGroup.mk' (pPrimeCore 2 ↥K) u ∈ center (coreQuot K) := by
  rw [mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) q
  refine (mk_mul_comm_iff x u).mpr ?_
  exact (mem_coreActionKernel.mp hu).2 _ x.2

theorem exists_isKleinFour_le_inf_centralizer_of_center (hK : IsTwoComponentIn K N)
    {D : Subgroup G} (hD : IsPGroup 2 D) (hDK : D ≤ normalizer (K : Set G))
    (hDM : D ≤ oddTwoCoreIn N ⊔ twoLayerIn N) {Z : Subgroup (coreQuot K)} (hZ : IsKleinFour Z)
    (hZc : Z ≤ center (coreQuot K)) :
    ∃ A : Subgroup G, IsKleinFour A ∧ A ≤ K ⊓ centralizer (D : Set G) := by
  refine exists_isKleinFour_le_inf_centralizer hD hDK hZ fun a ha d hd => ?_
  obtain ⟨k, hk, hc⟩ := exists_inv_mul_mem_coreActionKernel hK (hDM hd)
  have e : d = k * (k⁻¹ * d) := by group
  rw [e, comm_mul_mem_oddCoreIn_iff hk hc a.2]
  exact (mk_mul_comm_iff a ⟨k, hk⟩).mp (mem_center_iff.mp (hZc ha) _).symm

theorem exists_isKleinFour_mem_mem {Q : Type} [Group Q] [Finite Q]
    (hr : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q)) {s t : Q} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) : ∃ A : Subgroup Q, IsKleinFour A ∧ s ∈ A ∧ t ∈ A := by
  have hinv2 : ∀ x : Q, x * x = 1 → x ≠ 1 → orderOf x = 2 := fun x hx hx1 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hx) hx1
  by_cases hs1 : s = 1
  · by_cases ht1 : t = 1
    · obtain ⟨b, -, hb2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hr)
      obtain ⟨A, -, hA, -⟩ := exists_isKleinFour_mem hr (mem_top b) hb2
      exact ⟨A, hA, hs1 ▸ one_mem A, ht1 ▸ one_mem A⟩
    · obtain ⟨A, -, hA, htA⟩ := exists_isKleinFour_mem hr (mem_top t) (hinv2 t ht ht1)
      exact ⟨A, hA, hs1 ▸ one_mem A, htA⟩
  · by_cases hts : t = 1 ∨ t = s
    · obtain ⟨A, -, hA, hsA⟩ := exists_isKleinFour_mem hr (mem_top s) (hinv2 s hs hs1)
      refine ⟨A, hA, hsA, ?_⟩
      rcases hts with rfl | rfl
      · exact one_mem A
      · exact hsA
    · push Not at hts
      obtain ⟨A, hA, hsA, htA⟩ := GorensteinWalter.exists_kleinFour_of_commuting_involutions s t
        ⟨hs1, by rw [sq]; exact hs⟩ ⟨hts.1, by rw [sq]; exact ht⟩ (Ne.symm hts.2) hst
      exact ⟨A, hA, hsA, htA⟩

theorem exists_isKleinFour_le_inf_centralizer_of_center_eq_bot (hK : IsTwoComponentIn K N)
    {D : Subgroup G} (hD : IsKleinFour D) (hDK : D ≤ normalizer (K : Set G))
    (hDM : D ≤ oddTwoCoreIn N ⊔ twoLayerIn N) (hZ : center (coreQuot K) = ⊥)
    (hr : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (coreQuot K))) :
    ∃ A : Subgroup G, IsKleinFour A ∧ A ≤ K ⊓ centralizer (D : Set G) := by
  classical
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hQK : coreActionKernel K ≤ normalizer (K : Set G) := fun q hq =>
    (mem_coreActionKernel.mp hq).1
  have htriv : ∀ u : ↥K, (u : G) ∈ coreActionKernel K → π u = 1 := fun u hu => by
    have h1 := mk_mem_center_of_mem_coreActionKernel hu
    rw [hZ, mem_bot] at h1
    exact h1
  have hconj : ∀ k ∈ K, ∀ c ∈ coreActionKernel K, k⁻¹ * c * k ∈ coreActionKernel K :=
    fun k hk c hc => by
      have hn := (normalizer_le_normalizer_coreActionKernel (J := K)) (le_normalizer (inv_mem hk))
      have h1 := (mem_normalizer_iff.mp hn c).mp hc
      rwa [inv_inv] at h1
  obtain ⟨d₁, hd₁, hd₁1⟩ := exists_mem_ne_one_of_isKleinFour hD
  obtain ⟨d₂, hd₂, hd₂z⟩ := exists_not_mem_zpowers_of_isKleinFour hD hd₁
  obtain ⟨k₁, hk₁, hc₁⟩ := exists_inv_mul_mem_coreActionKernel hK (hDM hd₁)
  obtain ⟨k₂, hk₂, hc₂⟩ := exists_inv_mul_mem_coreActionKernel hK (hDM hd₂)
  set c₁ := k₁⁻¹ * d₁ with hc₁def
  set c₂ := k₂⁻¹ * d₂ with hc₂def
  have hd₁e : d₁ = k₁ * c₁ := by rw [hc₁def]; group
  have hd₂e : d₂ = k₂ * c₂ := by rw [hc₂def]; group
  set t₁ := π ⟨k₁, hk₁⟩ with ht₁
  set t₂ := π ⟨k₂, hk₂⟩ with ht₂
  have hsq : ∀ (d : G) (k : G) (hk : k ∈ K), d ∈ D → k⁻¹ * d ∈ coreActionKernel K →
      π ⟨k, hk⟩ * π ⟨k, hk⟩ = 1 := by
    intro d k hk hd hc
    have hd2 : d * d = 1 := by rw [← sq]; exact FooteLit.sq_eq_one_of_isKleinFour hD hd
    have hkk : k * k ∈ coreActionKernel K := by
      have e : (k⁻¹ * (k⁻¹ * d) * k) * (k⁻¹ * d) = (k * k)⁻¹ := by
        calc (k⁻¹ * (k⁻¹ * d) * k) * (k⁻¹ * d) = k⁻¹ * k⁻¹ * (d * d) := by
              simp only [mul_assoc, mul_inv_cancel_left]
          _ = (k * k)⁻¹ := by rw [hd2, mul_one, mul_inv_rev]
      have h2 : (k * k)⁻¹ ∈ coreActionKernel K := by
        rw [← e]
        exact mul_mem (hconj k hk _ hc) hc
      simpa using inv_mem h2
    have h1 := htriv ⟨k * k, mul_mem hk hk⟩ hkk
    rw [← h1, ← map_mul]
    rfl
  have ht₁2 : t₁ * t₁ = 1 := hsq d₁ k₁ hk₁ hd₁ hc₁
  have ht₂2 : t₂ * t₂ = 1 := hsq d₂ k₂ hk₂ hd₂ hc₂
  have hd₁₂ : d₁ * d₂ = d₂ * d₁ := (comm_of_isKleinFour hD _ hd₁ _ hd₂)
  have ht₁₂ : t₁ * t₂ = t₂ * t₁ := by
    have hu : (k₂ * k₁)⁻¹ * (k₁ * k₂) ∈ coreActionKernel K := by
      have e : (k₂ * k₁)⁻¹ * (k₁ * k₂) =
          ((k₁⁻¹ * c₂ * k₁) * c₁) * ((k₂⁻¹ * c₁ * k₂) * c₂)⁻¹ := by
        have e1 : k₁ * k₂ * ((k₂⁻¹ * c₁ * k₂) * c₂) = d₁ * d₂ := by rw [hd₁e, hd₂e]; group
        have e2 : k₂ * k₁ * ((k₁⁻¹ * c₂ * k₁) * c₁) = d₂ * d₁ := by rw [hd₁e, hd₂e]; group
        have e3 : k₁ * k₂ * ((k₂⁻¹ * c₁ * k₂) * c₂) = k₂ * k₁ * ((k₁⁻¹ * c₂ * k₁) * c₁) := by
          rw [e1, e2, hd₁₂]
        calc (k₂ * k₁)⁻¹ * (k₁ * k₂) =
            (k₂ * k₁)⁻¹ * (k₁ * k₂ * ((k₂⁻¹ * c₁ * k₂) * c₂)) *
              ((k₂⁻¹ * c₁ * k₂) * c₂)⁻¹ := by group
          _ = (k₂ * k₁)⁻¹ * (k₂ * k₁ * ((k₁⁻¹ * c₂ * k₁) * c₁)) *
              ((k₂⁻¹ * c₁ * k₂) * c₂)⁻¹ := by rw [e3]
          _ = ((k₁⁻¹ * c₂ * k₁) * c₁) * ((k₂⁻¹ * c₁ * k₂) * c₂)⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (hconj k₁ hk₁ _ hc₂) hc₁)
        (inv_mem (mul_mem (hconj k₂ hk₂ _ hc₁) hc₂))
    have h1 := htriv ⟨(k₂ * k₁)⁻¹ * (k₁ * k₂), mul_mem (inv_mem (mul_mem hk₂ hk₁))
      (mul_mem hk₁ hk₂)⟩ hu
    have h2 : (t₂ * t₁)⁻¹ * (t₁ * t₂) = 1 := by
      rw [ht₁, ht₂, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
      exact h1
    have h3 := congrArg (fun z => (t₂ * t₁) * z) h2
    simp only [mul_inv_cancel_left, mul_one] at h3
    exact h3
  obtain ⟨Ab, hAb, ht₁A, ht₂A⟩ := exists_isKleinFour_mem_mem hr ht₁2 ht₂2 ht₁₂
  refine exists_isKleinFour_le_inf_centralizer (isPGroup_of_isKleinFour hD) hDK hAb
    fun a ha d hd => ?_
  have hcommA : ∀ k (hk : k ∈ K), π ⟨k, hk⟩ ∈ Ab → a⁻¹ * k⁻¹ * a * k ∈ oddCoreIn K :=
    fun k hk hkA => (mk_mul_comm_iff a ⟨k, hk⟩).mp (comm_of_isKleinFour hAb _ ha _ hkA)
  have hDd : d = 1 ∨ d = d₁ ∨ d = d₂ ∨ d = d₁ * d₂ := by
    by_contra hn
    push Not at hn
    obtain ⟨h1, h2, h3, h4⟩ := hn
    have : IsKleinFour D := hD
    have hd₂1 : d₂ ≠ 1 := fun h => hd₂z (h ▸ one_mem _)
    have hd₁₂ne : d₁ ≠ d₂ := fun h => hd₂z (h ▸ mem_zpowers d₁)
    have := IsKleinFour.eq_mul_of_ne_all (x := (⟨d₁, hd₁⟩ : D)) (y := ⟨d₂, hd₂⟩) (z := ⟨d, hd⟩)
      (fun h => hd₁1 (congrArg Subtype.val h)) (fun h => hd₂1 (congrArg Subtype.val h))
      (fun h => hd₁₂ne (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
      (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
    exact h4 (congrArg Subtype.val this)
  rcases hDd with rfl | rfl | rfl | rfl
  · simp only [inv_one, mul_one, inv_mul_cancel]
    exact one_mem _
  · rw [hd₁e, comm_mul_mem_oddCoreIn_iff hk₁ hc₁ a.2]
    exact hcommA k₁ hk₁ ht₁A
  · rw [hd₂e, comm_mul_mem_oddCoreIn_iff hk₂ hc₂ a.2]
    exact hcommA k₂ hk₂ ht₂A
  · have e : d₁ * d₂ = (k₁ * k₂) * ((k₂⁻¹ * c₁ * k₂) * c₂) := by rw [hd₁e, hd₂e]; group
    rw [e, comm_mul_mem_oddCoreIn_iff (mul_mem hk₁ hk₂)
      (mul_mem (hconj k₂ hk₂ _ hc₁) hc₂) a.2]
    refine hcommA _ (mul_mem hk₁ hk₂) ?_
    have e2 : π ⟨k₁ * k₂, mul_mem hk₁ hk₂⟩ = t₁ * t₂ := by
      rw [ht₁, ht₂, ← map_mul]
      rfl
    rw [e2]
    exact mul_mem ht₁A ht₂A

end Cent

@[expose] def SolomonQTwoDisconnectedSylowCycFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
      IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') →
      3 ≤ CFSG.Open.pRank 2 K →
      (∃ (S' : Sylow 2 ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'))
          (E F : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')),
          IsKleinFour E ∧ E ≤ S' ∧ IsKleinFour F ∧ F ≤ S' ∧
            ¬ Relation.ReflTransGen
              (CommFourAdj ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')) E F) →
      (∃ D : Subgroup ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'),
          IsKleinFour D ∧ ∀ A : Subgroup G, IsKleinFour A →
            ¬ A ≤ K ⊓ centralizer
              ((D.map ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K').subtype :
                Subgroup G) : Set G)) →
      center (coreQuot K) ≠ ⊥ →
      (∀ Z : Subgroup (coreQuot K), Z ≤ center (coreQuot K) → ¬ IsKleinFour Z) →
      IsSolomonI (coreQuot K)

theorem solomonQTwoDisconnectedSylowCentFor_of_cyc (h : SolomonQTwoDisconnectedSylowCycFor) :
    SolomonQTwoDisconnectedSylowCentFor := by
  intro G _ _ hG N hN hr K hK K' hK' hne hdisc h3 hS' hD
  set Q' := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' with hQ'
  obtain ⟨D, hD4, hDA⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set DG := D.map Q'.subtype with hDG
  have hDG4 : IsKleinFour DG := by
    refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
    · rw [hDG, Subgroup.card_map_of_injective Q'.subtype_injective, hD4.card_four]
    · obtain ⟨v, hv, rfl⟩ := hx
      rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hD4 hv, map_one]
  have hDQ : DG ≤ Q' := map_subtype_le _
  have hDM : DG ≤ oddTwoCoreIn N ⊔ twoLayerIn N := hDQ.trans inf_le_left
  have hDK : DG ≤ normalizer (K : Set G) := fun g hg => by
    have hgN : g ∈ N := sup_le (map_subtype_le _) (map_subtype_le _) (hDM hg)
    exact mem_normalizer_of_ncard_eq_two hr hK hK' hne hgN
      (mem_coreActionKernel.mp (hDQ hg).2).1
  have hr2 : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (coreQuot K)) := by
    rw [← SectionRank.pRank_eq_open_pRank_top, FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
    omega
  refine h G hG N hN hr K hK K' hK' hne hdisc h3 hS' ⟨D, hD4, hDA⟩ (fun hZ => ?_)
    fun Z hZc hZ4 => ?_
  · obtain ⟨A, hA, hAle⟩ :=
      exists_isKleinFour_le_inf_centralizer_of_center_eq_bot hK.1 hDG4 hDK hDM hZ hr2
    exact hDA A hA hAle
  · obtain ⟨A, hA, hAle⟩ := exists_isKleinFour_le_inf_centralizer_of_center hK.1
      (isPGroup_of_isKleinFour hDG4) hDK hDM hZ4 hZc
    exact hDA A hA hAle

section Certified

theorem solomonQTwoDisconnectedSylowFor_of_cent (hBig : QuasisimpleBigCenterRankThree)
    (hSJ : QuasisimpleSylowFourJoinedSCN) (h : SolomonQTwoDisconnectedSylowCentFor) :
    SolomonQTwoDisconnectedSylowFor := by
  intro G _ _ hG N hN hr K hK K' hK' hne hdisc h3 hS'
  by_contra hI
  set Q' := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' with hQ'
  by_cases hcent : ∃ D : Subgroup ↥Q', IsKleinFour D ∧ ∀ A : Subgroup G, IsKleinFour A →
      ¬ A ≤ K ⊓ centralizer ((D.map Q'.subtype : Subgroup G) : Set G)
  · exact hI (h G hG N hN hr K hK K' hK' hne hdisc h3 hS' hcent)
  obtain ⟨S', E, F, hE, -, hF, -, hEF⟩ := hS'
  have hKQ : K ≤ Q' := le_inf ((le_twoLayerIn_of_isTwoComponentIn hK.1).trans le_sup_right)
    (le_coreActionKernel_of_ne hK' hK hne.symm)
  have hc := not_isTwoDisconnected_coreQuot_of_not_isSolomonI hBig hSJ hG hK h3 hI
  have hK2 : ∀ A B : Subgroup G, IsKleinFour A → A ≤ K → IsKleinFour B → B ≤ K →
      Relation.ReflTransGen (CommFourIn K) A B := by
    intro A B hA hAK hB hBK
    have hbot : K ⊓ centralizer ((⊥ : Subgroup G) : Set G) = K :=
      inf_eq_left.mpr fun k _ => mem_centralizer_iff.mpr fun x hx => by
        rw [show x = 1 from mem_bot.mp hx, one_mul, mul_one]
    have h1 := reflTransGen_commFourIn_of_twoConnected (U := ⊥) IsPGroup.of_bot bot_le hc h3 hA
      (by rw [hbot]; exact hAK) hB (by rw [hbot]; exact hBK)
    rwa [hbot] at h1
  have hadj : ∀ D : Subgroup ↥Q', IsKleinFour D → ∃ A : Subgroup G, IsKleinFour A ∧ A ≤ K ∧
      CommFourAdj ↥Q' D (A.subgroupOf Q') := by
    intro D hD
    have h1 : ∃ A : Subgroup G, IsKleinFour A ∧
        A ≤ K ⊓ centralizer ((D.map Q'.subtype : Subgroup G) : Set G) := by
      by_contra hn
      push Not at hn
      exact hcent ⟨D, hD, fun A hA hAle => hn A hA hAle⟩
    obtain ⟨A, hA, hAle⟩ := h1
    refine ⟨A, hA, hAle.trans inf_le_left, hD, isKleinFour_subgroupOf hA
      ((hAle.trans inf_le_left).trans hKQ), fun d hd => ?_⟩
    rw [mem_centralizer_iff]
    intro a ha
    have h2 := mem_centralizer_iff.mp (hAle (mem_subgroupOf.mp ha)).2 (d : G)
      (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
    exact Subtype.ext h2.symm
  obtain ⟨A, hA, hAK, hEA⟩ := hadj E hE
  obtain ⟨B, hB, hBK, hFB⟩ := hadj F hF
  exact hEF ((Relation.ReflTransGen.single hEA).trans
    ((reflTransGen_commFourAdj_subgroupOf hKQ (hK2 A B hA hAK hB hBK)).trans
      (Relation.ReflTransGen.single (commFourAdj_symm hFB))))

end Certified

end CFSG.ComponentClassification.Sol76.Sig
