module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B1.PilotS3
public import CFSG.GH74.Generic.S3.PumpDiag

public section

namespace CFSG.GH74.Generic.BProg.B2.SD

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

namespace SDRank

theorem sectionalTwoRankLE_of_forall_le {X : Type*} [Group X] (C : Subgroup X) {r : ℕ}
    (h : ∀ P : Subgroup X, P ≤ C → IsPGroup 2 ↥P →
      ∃ s : Finset X, s.card ≤ r ∧ Subgroup.closure (s : Set X) = P) :
    SectionalTwoRankLE ↥C r := by
  classical
  intro Q hQ
  obtain ⟨s, hs, hsP⟩ := h (Q.map C.subtype) (Subgroup.map_subtype_le Q) (hQ.map C.subtype)
  have hsub : (s : Set X) ⊆ C.subtype '' (Q : Set ↥C) := fun y hy => by
    have hy' : y ∈ Q.map C.subtype := hsP ▸ Subgroup.subset_closure hy
    simpa using hy'
  obtain ⟨t, -, hts⟩ := Finset.subset_set_image_iff.mp hsub
  refine ⟨t, ?_, ?_⟩
  · rw [← Finset.card_image_of_injective t C.subtype_injective, hts]
    exact hs
  · apply Subgroup.map_injective C.subtype_injective
    rw [MonoidHom.map_closure, ← Finset.coe_image, hts, hsP]

theorem exists_two_generators_of_commuting {X : Type} [Group X] [Finite X] (hX : Gen4 X)
    {K P : Subgroup X} (hK : RankCertified ↥K 1) (hKP : ∀ k ∈ K, ∀ p ∈ P, k * p = p * k)
    (hinf : K ⊓ P = ⊥) (hP2 : IsPGroup 2 ↥P) :
    ∃ s : Finset X, s.card ≤ 2 ∧ Subgroup.closure (s : Set X) = P := by
  classical
  by_contra hno
  have hP1 : RankCertified ↥P 2 := by
    apply rankCertified_of_not_sectionalTwoRankLE
    intro hle
    obtain ⟨s, hs, hcl⟩ := hle ⊤ (hP2.of_equiv Subgroup.topEquiv.symm)
    refine hno ⟨s.image P.subtype, Finset.card_image_le.trans hs, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure, hcl, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let φ : ↥K × ↥P →* X :=
    MonoidHom.noncommCoprod K.subtype P.subtype (fun k p => hKP _ k.2 _ p.2)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, p⟩ hkp
    have h1 : (k : X) * p = 1 := hkp
    have hk : (k : X) ∈ K ⊓ P := by
      refine ⟨k.2, ?_⟩
      have : (k : X) = (p : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact P.inv_mem p.2
    rw [hinf, Subgroup.mem_bot] at hk
    have hp : (p : X) = 1 := by rw [hk, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hk) (Subtype.ext hp)
  exact ((hK.prod hP1).of_injective φ hφ).not_gen4 (by norm_num) hX

theorem cover_facts {K B C : Type} [Group K] [Finite K] [Group B] [Group C] (φ : K →* B)
    (ρ : K →* C) (hφ : Function.Surjective φ) (hρ : Function.Surjective ρ) (hker : φ.ker ≤ ρ.ker)
    (hodd : ∀ k : K, ρ k = 1 → Odd (orderOf k))
    (hC : ∀ c : C, (∀ c' : C, c' * c = c * c') → c = 1) (h1 : RankCertified C 1) :
    RankCertified B 1 ∧
      ∀ b : B, (∀ b' : B, b' * b = b * b') → ∀ n : ℕ, b ^ (2 ^ n) = 1 → b = 1 := by
  refine ⟨RankCertified.of_hom_ker_le φ ρ hρ hker h1, ?_⟩
  intro b hb n hbn
  obtain ⟨k, rfl⟩ := hφ b
  have hρk : ρ k = 1 := by
    apply hC
    intro c'
    obtain ⟨k', rfl⟩ := hρ c'
    have hcomm : φ k' * φ k = φ k * φ k' := hb (φ k')
    have hmem : k' * k * k'⁻¹ * k⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have h2 := MonoidHom.mem_ker.1 (hker hmem)
    simp only [map_mul, map_inv] at h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hk := hodd k hρk
  have h2 : orderOf (φ k) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hbn
  have h3 : orderOf (φ k) ∣ orderOf k := orderOf_map_dvd φ k
  have h4 : Nat.Coprime (orderOf (φ k)) 2 := Nat.coprime_two_right.2 (Odd.of_dvd_nat hk h3)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (h4.pow_right n) h2)

theorem odd_orderOf_of_mem_pPrimeCore {K : Type} [Group K] [Finite K] {k : K}
    (hk : k ∈ pPrimeCore 2 K) : Odd (orderOf k) :=
  Odd.of_dvd_nat (Nat.coprime_two_left.1 pPrimeCore_coprime_card) (Subgroup.orderOf_dvd_natCard _ hk)

theorem exists_cover {M K : Subgroup G} (hKM : K ≤ M) :
    ∃ φ : ↥K →* ↥(barIn M K), Function.Surjective φ ∧
      φ.ker ≤ (QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker := by
  let ι : ↥K →* ↥M := Subgroup.inclusion hKM
  let φ : ↥K →* ↥(barIn M K) :=
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp ι).codRestrict (barIn M K)
      (fun k => ⟨ι k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩)
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨y, m, hm, rfl⟩
    refine ⟨⟨m.1, hm⟩, ?_⟩
    rfl
  · rw [QuotientGroup.ker_mk']
    have hnormal : φ.ker.Normal := MonoidHom.normal_ker φ
    refine le_pPrimeCore_of_normal_coprime hnormal ?_
    have hinj : Function.Injective ι := Subgroup.inclusion_injective hKM
    have hle : φ.ker.map ι ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' : φ k = 1 := hk
      have := congrArg Subtype.val hk'
      exact (QuotientGroup.eq_one_iff _).1 this
    have hd : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact Subgroup.card_dvd_of_le hle
    exact Nat.Coprime.coprime_dvd_right hd pPrimeCore_coprime_card

end SDRank

theorem sectionalRank_centBarK_le_two {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    SectionalTwoRankLE ↥(centBarK M K) 2 := by
  have hKM : K ≤ M := h1.K_le
  have hgen : Gen4 (Mbar M) := Gen4.quotient (pPrimeCore 2 ↥M) (Gen4.subgroup M hs.hyp.gen4)
  obtain ⟨φ, hφ, hker⟩ := SDRank.exists_cover hKM
  have hC : ∀ c : ↥K ⧸ pPrimeCore 2 ↥K, (∀ c', c' * c = c * c') → c = 1 :=
    B1.PilotS3.center_trivial_of_shape3 hs.pair.1.1.1.2.2 h3
  have hcert : RankCertified (↥K ⧸ pPrimeCore 2 ↥K) 1 := by
    obtain ⟨p, f, -, hp2, -, hmodel⟩ := h3
    rcases hmodel with h | h
    · exact rankCertified_one_of_l3 (t := .PSL) (Or.inl rfl) hp2 (stated_of_lieModel_PSL h)
    · exact rankCertified_one_of_l3 (t := .PSU) (Or.inr rfl) hp2 (stated_of_lieModel_PSU h)
  obtain ⟨hK1, hZ⟩ := SDRank.cover_facts φ (QuotientGroup.mk' (pPrimeCore 2 ↥K)) hφ
    (QuotientGroup.mk'_surjective _) hker
    (fun k hk => SDRank.odd_orderOf_of_mem_pPrimeCore ((QuotientGroup.eq_one_iff k).1 hk)) hC hcert
  refine SDRank.sectionalTwoRankLE_of_forall_le _ (fun P hPC hP2 => ?_)
  refine SDRank.exists_two_generators_of_commuting hgen hK1
    (fun k hk p hp => Subgroup.mem_centralizer_iff.1 (hPC hp) k hk) ?_ hP2
  rw [Subgroup.eq_bot_iff_forall]
  rintro b ⟨hbK, hbP⟩
  obtain ⟨n, hn⟩ := hP2 ⟨b, hbP⟩
  have hcentral : ∀ b' : ↥(barIn M K), b' * (⟨b, hbK⟩ : ↥(barIn M K)) = ⟨b, hbK⟩ * b' :=
    fun b' => Subtype.ext (Subgroup.mem_centralizer_iff.1 (hPC hbP) b' b'.2)
  have hbn : (⟨b, hbK⟩ : ↥(barIn M K)) ^ (2 ^ n) = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hn)
  exact congrArg Subtype.val (hZ ⟨b, hbK⟩ hcentral n hbn)

theorem sectionalRank_le_two_of_le_centBarK {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) {J : Subgroup (Mbar M)} (hJ : J ≤ centBarK M K) :
    SectionalTwoRankLE ↥J 2 :=
  SectionalTwoRankLE.of_injective (Subgroup.inclusion hJ) (Subgroup.inclusion_injective hJ)
    (sectionalRank_centBarK_le_two hs h1 h3)

end CFSG.GH74.Generic.BProg.B2.SD
