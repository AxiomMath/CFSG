module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QCov
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QE4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

namespace P58b3L

@[expose] def E7ThreeNoKlein : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], Blueprint.LieModel X .E7 0 3 1 →
    ∀ z : X, orderOf z = 2 → ∀ R : Subgroup X, R ≤ centralizer {z} →
      (R.subgroupOf (centralizer {z})).IsSubnormal → z ∉ R →
        ¬ IsKleinFour (↥R ⧸ pPrimeCore 2 ↥R)

@[expose] def E7ThreeEvenCentInv : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], Blueprint.LieModel X .E7 0 3 1 →
    ∀ z : X, orderOf z = 2 → P51Q.EvenCentInv X z

theorem false_of_evenCentInv {X : Type} [Group X] [Finite X] {z : X}
    (hinv : P51Q.EvenCentInv X z) (hz : orderOf z = 2) {R : Subgroup X}
    (hRC : R ≤ centralizer {z}) (hRsub : (R.subgroupOf (centralizer {z})).IsSubnormal)
    (hzR : z ∉ R) (hR4 : IsKleinFour (↥R ⧸ pPrimeCore 2 ↥R)) : False := by
  obtain ⟨S, hS4, hSsq⟩ := P51Q.exists_sylow_klein hR4
  set T := S.map R.subtype with hT
  have hTR : T ≤ R := map_subtype_le S
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hcomm : ∀ (t : T) (w : zpowers z), Commute (T.subtype t) ((zpowers z).subtype w) := by
    rintro ⟨t, ht⟩ ⟨w, hw⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    exact Commute.zpow_right (mem_centralizer_singleton_iff.mp (hRC (hTR ht))) i
  set φ := MonoidHom.noncommCoprod T.subtype (zpowers z).subtype hcomm with hφ
  have hzpow : ∀ w ∈ zpowers z, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← zpow_mod_orderOf, hz]
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  have hinj : Function.Injective φ := by
    refine (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr ⟨subtype_injective _,
      subtype_injective _, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff, eq_bot_iff]
    intro w hw
    obtain ⟨hwT, hwz⟩ := mem_inf.mp hw
    rcases hzpow w hwz with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hTR hwT) hzR
  set P := φ.range with hP
  have hφapp : ∀ x : T × zpowers z, φ x = (x.1 : X) * (x.2 : X) := fun x => rfl
  have hPcard : Nat.card P = 8 := by
    rw [hP, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      card_map_of_injective (subtype_injective R), hS4, Nat.card_zpowers, hz]
  have hPC : P ≤ centralizer ({z} : Set X) := by
    rintro _ ⟨x, rfl⟩
    rw [hφapp]
    refine mul_mem (hRC (hTR x.1.2)) ?_
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp x.2.2
    rw [← hi]
    exact zpow_mem (mem_centralizer_singleton_iff.mpr rfl) i
  have hPsq : ∀ q ∈ P, q * q = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [hφapp]
    have h1 : (x.1 : X) * (x.1 : X) = 1 := by
      obtain ⟨s, hs, hsx⟩ := mem_map.mp x.1.2
      rw [← hsx]
      exact congrArg Subtype.val (hSsq s hs)
    have h2 : (x.2 : X) * (x.2 : X) = 1 := by
      rcases hzpow _ x.2.2 with h | h <;> rw [h]
      · exact mul_one 1
      · exact hzz
    have hab : (x.1 : X) * x.2 = x.2 * x.1 := (hcomm x.1 x.2).eq
    calc (x.1 : X) * x.2 * (x.1 * x.2) = x.1 * (x.2 * x.1) * x.2 := by group
      _ = x.1 * (x.1 * x.2) * x.2 := by rw [← hab]
      _ = x.1 * x.1 * (x.2 * x.2) := by group
      _ = 1 := by rw [h1, h2, mul_one]
  have hsolv : Group.IsSolvable (↥R ⧸ pPrimeCore 2 ↥R) :=
    Group.isSolvable_of_comm (mul_comm_of_exponent_two hR4.exponent_two)
  have hPK : ∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
      ∀ k ∈ K, ∀ g ∈ P, (k : X) * g = g * k := by
    rintro K hK hKe k hk _ ⟨x, rfl⟩
    rw [hφapp]
    have h1 := P51Q.commute_of_isComponent hRC hRsub hsolv hK hKe k hk x.1 (hTR x.1.2)
    have h2 : (k : X) * x.2 = x.2 * k := by
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp x.2.2
      rw [← hi]
      exact ((Commute.zpow_right (mem_centralizer_singleton_iff.mp k.2) i)).eq
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  have hsub : (P : Set X) ⊆ {1, z} := fun q hq => by
    rcases hinv q (hPC hq) (fun K h1 h2 k hk => hPK K h1 h2 k hk q hq) (hPsq q hq) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h2 : Nat.card P ≤ 2 :=
    calc Nat.card P = (P : Set X).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, z} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  omega

theorem e7ThreeNoKlein_of_evenCentInv (h : E7ThreeEvenCentInv) : E7ThreeNoKlein :=
  fun X _ _ _ hX z hz _ hRC hRsub hzR hR4 =>
    false_of_evenCentInv (h X hX z hz) hz hRC hRsub hzR hR4

variable {G : Type} [Group G] [Finite G] {z₁ z₂ : G} {L₁ K : Subgroup G}

theorem false_of_kleinFree {τ : StatedLieTag} {n f : ℕ}
    (hfree : ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup Y],
      Blueprint.LieModel Y τ n 3 f → ∀ x : Y, orderOf x = 2 → ∀ R : Subgroup Y,
        R ≤ centralizer {x} → (R.subgroupOf (centralizer {x})).IsSubnormal → x ∉ R →
          ¬ IsKleinFour (↥R ⧸ pPrimeCore 2 ↥R))
    (hz₁ : orderOf z₁ = 2) (hz₂ : orderOf z₂ = 2)
    (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₁L : z₁ ∈ L₁)
    (he₁ : Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)))
    (hKc : IsTwoComponentIn K (centralizer {z₁})) (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K)
    (hz₂K : z₂ ∈ K)
    (hz₂Z : (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K))
    (hm : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) τ n 3 f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he₁
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, -, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hX.2.1
  have hι := odd_card_ker_iota hO₁
  have hψ := odd_card_ker_psi e
  have hψ8 := psi_pow_eight e
  obtain ⟨hsurj, z, -, -, hz₁z, hz, -⟩ := exists_sylow_data hz₁ hz₁L (hL₁.1.trans inf_le_left) e
  obtain ⟨hle, hsub⟩ := range_iota_subnormal hz₂ hL₁ hKc.1 hO₁ hz₂K
  have hzZ : iota hO₁ z ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    have hc : iota hO₁ z = QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ := by
      rw [iota_apply]
      congr 1
      exact Subtype.ext (by rw [coe_toK]; exact hz₁z)
    rw [hc]
    exact mk_mem_center hKc.1 hz₁K
  set t : ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩ with ht_def
  have ht : t * t = 1 := mk_mul_self hz₂ hz₂K
  have htZ : t ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := hz₂Z
  have htM : ∀ m, iota hO₁ m * t = t * iota hO₁ m := fun m =>
    mem_centralizer_singleton_iff.mp (hle ⟨m, rfl⟩)
  set π := QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)) with hπ
  have hR4 := isKleinFour_range (iota hO₁) (psi e) hι hψ hψ8 hsurj hz hzZ
  have htR := not_mem_range (iota hO₁) (psi e) hι hψ hψ8 hsurj hz hzZ ht htZ htM
  have ht2 : orderOf (π t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, ht, map_one]
    · rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htZ
  have hCle : (centralizer {t}).map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hx]
  have hR : (π.comp (iota hO₁)).range = (iota hO₁).range.map π := MonoidHom.range_comp _ _
  have hRC : (π.comp (iota hO₁)).range ≤ centralizer {π t} := by
    rw [hR]
    exact (map_mono hle).trans hCle
  have hRsub : ((π.comp (iota hO₁)).range.subgroupOf (centralizer {π t})).IsSubnormal := by
    have hN := P58b.normal_map_centralizer_of_ker π (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) t
    have h1 : (((iota hO₁).range.map π).subgroupOf ((centralizer {t}).map π)).IsSubnormal := by
      rw [← map_subgroupOf_subgroupMap hle π]
      exact hsub.map (MonoidHom.subgroupMap_surjective _ _)
    rw [hR]
    exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans (map_mono hle) hCle h1 hN.isSubnormal
  exact hfree _ hmX (π t) ht2 _ hRC hRsub htR hR4

end P58b3L

theorem harris82Lemma58bThreeRowAt_E7_of_noKlein (h : P58b3L.E7ThreeNoKlein) :
    P58b3.Harris82Lemma58bThreeRowAt .E7 0 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ he₁ hKc hO₁ _ _ hz₂K hz₂Z hm
  exact (P58b3L.false_of_kleinFree (τ := .E7) (n := 0) (f := 1) h hz₁ hz₂ hL₁ hz₁L he₁ hKc hO₁
    hz₂K hz₂Z hm).elim

end CFSG.ComponentClassification.HarrisLit.T1
