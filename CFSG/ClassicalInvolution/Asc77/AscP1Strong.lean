module

public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Goldschmidt
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.StronglyEmbedded.UniqueCosetEnd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]

theorem not_isSolvable_of_mem_mod {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : ¬ Group.IsSolvable ↥K := by
  intro hsolv
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  have hperf : Group.IsPerfect ↥K := hz'.perfect
  have hnt : Nontrivial ↥K := ⟨⟨⟨z, hz.mem⟩, 1, fun h => hz.ne_one (congrArg Subtype.val h)⟩⟩
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)
  rw [hperf.commutator_eq_top] at hlt
  exact lt_irrefl _ hlt

theorem isUniqueInvolution_le_centralizer {G : Type} [Group G] {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) : K ≤ Subgroup.centralizer ({z} : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz.commute_of_mem hw).symm

theorem false_of_bender_of_not_isSolvable {G : Type} [Group G] [Finite G]
    (hB : fusionIsBenderGroup G) {K : Subgroup G} {z : G} (hz2 : orderOf z = 2)
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G)) (hKns : ¬ Group.IsSolvable ↥K) : False := by
  have hz2p : IsPGroup 2 (Subgroup.zpowers z) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  obtain ⟨T, hzT⟩ := hz2p.exists_le_sylow
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hB T
  have hse := hD.se
  set M : Subgroup G := Subgroup.normalizer ((T : Subgroup G) : Set G) with hM
  have hzM : z ∈ M := Subgroup.le_normalizer (hzT (Subgroup.mem_zpowers z))
  have hKM : K ≤ M := by
    intro k hk
    by_contra hkM
    have hodd := hse.2.2 k hkM
    have hkz : z * k = k * z := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk) |>.symm
    have hzM' : z ∈ M.map (MulAut.conj k⁻¹).toMonoidHom := by
      refine ⟨z, hzM, ?_⟩
      show k⁻¹ * z * k⁻¹⁻¹ = z
      calc k⁻¹ * z * k⁻¹⁻¹ = k⁻¹ * (z * k) := by group
        _ = k⁻¹ * (k * z) := by rw [hkz]
        _ = z := by group
    have hmem : z ∈ M ⊓ M.map (MulAut.conj k⁻¹).toMonoidHom := ⟨hzM, hzM'⟩
    have hdvd : 2 ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj k⁻¹).toMonoidHom) := by
      have := Subgroup.orderOf_dvd_natCard (M ⊓ M.map (MulAut.conj k⁻¹).toMonoidHom) hmem
      rwa [hz2] at this
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have : Group.IsSolvable ↥M := CFSG.StronglyEmbedded.UniqueCoset.isSolvable_normalizer_sylow T
  exact hKns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKM)
    (Subgroup.inclusion_injective hKM))

theorem center_eq_bot_of_isSimpleGroup_nonabelian {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

theorem exists_isPGroup_of_mem_mod {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ R : Subgroup G, R ≤ K ∧ IsPGroup 2 R ∧ 8 ≤ Nat.card R ∧ z ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hR : (Q : Subgroup ↥K).map K.subtype ∈ RSet Ω := ⟨K, hK, Q, rfl⟩
  have h8 : 8 ≤ Nat.card ↥((Q : Subgroup ↥K).map K.subtype) := hΩ.eight_le_of_mem_RSet hp hR
  have hR2 : IsPGroup 2 ↥((Q : Subgroup ↥K).map K.subtype) := Q.isPGroup'.map _
  refine ⟨(Q : Subgroup ↥K).map K.subtype, Subgroup.map_subtype_le _, hR2, h8, ?_⟩
  obtain ⟨a, ha⟩ := hR2.exists_card_eq
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at ha
    omega
  have hdvd : 2 ∣ Nat.card ↥((Q : Subgroup ↥K).map K.subtype) := by
    rw [ha]
    exact dvd_pow_self 2 ha0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hyR : (y : G) ∈ (Q : Subgroup ↥K).map K.subtype := y.2
  have hyK : (y : G) ∈ K := Subgroup.map_subtype_le _ hyR
  have hyorder : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hysq : (y : G) * (y : G) = 1 := by
    have h := pow_orderOf_eq_one (y : G)
    rw [hyorder] at h
    rw [← pow_two]
    exact h
  have hy1 : (y : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyorder
    omega
  rcases hz.unique _ hyK hysq with h | h
  · exact absurd h hy1
  · rw [← h]
    exact hyR

theorem false_of_card_eq_eight_mul_odd {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) (hnab : ∃ a b : G, a * b ≠ b * a) {j : ℕ}
    (hj : Odd j) (hcard : Nat.card G = 2 ^ 3 * j) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRK, hR2, h8, hzR⟩ := exists_isPGroup_of_mem_mod hΩ hp hK hz
  obtain ⟨P, hRP⟩ := hR2.exists_le_sylow
  obtain ⟨a, ha⟩ := hR2.exists_card_eq
  obtain ⟨b, hb⟩ := P.isPGroup'.exists_card_eq
  have hbdvd : 2 ^ b ∣ 2 ^ 3 * j := by
    rw [← hb, ← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hb3 : b ≤ 3 := by
    by_contra h
    have h := not_le.mp h
    have h16 : 2 ^ 4 ∣ 2 ^ 3 * j := (Nat.pow_dvd_pow 2 h).trans hbdvd
    have := Nat.odd_iff.mp hj
    omega
  have hle : Nat.card (P : Subgroup G) ≤ Nat.card R := by
    rw [hb, ha]
    calc 2 ^ b ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hb3
      _ = 8 := by norm_num
      _ ≤ 2 ^ a := by rw [← ha]; exact h8
  have hRP' : R = (P : Subgroup G) := Subgroup.eq_of_le_of_card_ge hRP hle
  have hzP : z ∈ (P : Subgroup G) := hRP' ▸ hzR
  have hPK : ∀ y ∈ (P : Subgroup G), y ∈ K := fun y hy => hRK (hRP' ▸ hy)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hzS : (⟨z, hzP⟩ : ↥(P : Subgroup G)) ∈ Subgroup.center ↥(P : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hz.commute_of_mem (hPK y y.2)).symm
  have hzS2 : orderOf (⟨z, hzP⟩ : ↥(P : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz2
  have hwc : ∀ g : G, g⁻¹ * ((⟨z, hzP⟩ : ↥(P : Subgroup G)) : G) * g ∈ (P : Subgroup G) →
      g⁻¹ * ((⟨z, hzP⟩ : ↥(P : Subgroup G)) : G) * g = ((⟨z, hzP⟩ : ↥(P : Subgroup G)) : G) := by
    intro g hg
    have hsq : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
      calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hz.sq]; group
    rcases hz.unique _ (hPK _ hg) hsq with h | h
    · exfalso
      apply hz.ne_one
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · exact h
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar P ⟨z, hzP⟩ hzS hzS2 hwc
  have hbot : CFSG.oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exfalso
      exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz2
        (by rw [h]; exact Subgroup.mem_top z)
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
    have h2 : (QuotientGroup.mk (g * z) : G ⧸ CFSG.oddCore G) = QuotientGroup.mk (z * g) := by
      simpa [QuotientGroup.mk_mul] using h1
    have h3 := QuotientGroup.eq.mp h2
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact h3
  rw [center_eq_bot_of_isSimpleGroup_nonabelian hnab] at hzc
  exact hz.ne_one (Subgroup.mem_bot.mp hzc)

theorem l17_8 : L17_8 p f := by
  intro G _ _ _ Ω K hs S A hAS hA1 hAab hsc
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ := hs.hyp
  have hK := hs.mem
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hKz := isUniqueInvolution_le_centralizer hz
  have hKns := not_isSolvable_of_mem_mod hΩ hK hz
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    have hcon' : ∀ a b : G, a * b = b * a := by
      intro a b
      by_contra h
      exact hcon ⟨a, b, h⟩
    have : Group.IsSolvable G := Group.isSolvable_of_comm hcon'
    exact hKns (Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective)
  have hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A := by
    intro a ha g hg
    have := hsc.2 a ha g⁻¹ (by simpa using hg)
    simpa using this
  have hAab' : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAab a.1 a.2 b.1 b.2)⟩⟩
  have hS := CFSG.ClassicalInvolution.Hat2A7.goldschmidtSimpleType_of_milestone
    (@CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian) hnab S hA1 hAS hAab' hcl
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ |
    ⟨p', f', hp', hodd, hf0, h5, hmod, ⟨e⟩⟩ | ⟨m, hm, hcard⟩ | ⟨⟨e⟩⟩
  · exact false_of_bender_of_not_isSolvable (Or.inl ⟨n, by omega, ⟨e⟩⟩) hz2 hKz hKns
  · exact false_of_bender_of_not_isSolvable (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)) hz2 hKz hKns
  · exact false_of_bender_of_not_isSolvable (Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩)) hz2 hKz hKns
  ·
    have hf0' : f' ≠ 0 := by omega
    have hKcard : Nat.card (GaloisField p' f') = p' ^ f' := GaloisField.card p' f' hf0'
    have hodd' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p' f')) :=
      ⟨p', f', hp'.out, hodd, hf0, hKcard⟩
    have hc := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p' f') hodd'
    rw [hKcard] at hc
    obtain ⟨j, hj, hj4⟩ := CFSG.ClassicalInvolution.Hat2A7.psl2_card_eq_four_mul_odd hmod
    have hcardG : Nat.card G = 2 ^ 2 * j := by
      rw [Nat.card_congr e.toEquiv]
      exact hc.trans (hj4.trans (by norm_num))
    obtain ⟨R, hRK, hR2, h8, -⟩ := exists_isPGroup_of_mem_mod hΩ hp hK hz
    obtain ⟨a, ha⟩ := hR2.exists_card_eq
    have hdvd : 2 ^ a ∣ 2 ^ 2 * j := by
      rw [← ha, ← hcardG]
      exact Subgroup.card_subgroup_dvd_card R
    have ha3 : 3 ≤ a := by
      by_contra h
      have h := not_le.mp h
      have : 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h8dvd : 2 ^ 3 ∣ 2 ^ 2 * j := (Nat.pow_dvd_pow 2 ha3).trans hdvd
    have := Nat.odd_iff.mp hj
    omega
  ·
    obtain ⟨j, hj, hj8⟩ := CFSG.ClassicalInvolution.Hat2A7.ordRee_eq_eight_mul_odd m
    exact false_of_card_eq_eight_mul_odd hΩ hp hK hz hnab hj (by rw [hcard, hj8]; norm_num)
  ·
    have hcardG : Nat.card G = 2 ^ 3 * 21945 := by
      rw [← CFSG.ClassicalInvolution.Hat2A7.card_goldschmidtJ1_eq, Nat.card_congr e.toEquiv]
    exact false_of_card_eq_eight_mul_odd hΩ hp hK hz hnab ⟨10972, by norm_num⟩ hcardG

end CFSG.ClassicalInvolution.Asc77
