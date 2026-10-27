module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSetting
import CFSG.Quasithin.EmptyFaithful.ModHSolv

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B2F CFSG.Quasithin.E2
  CFSG.AGLEmbeddingD2.GN
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_two_dvd_relIndex_inf_pCoreOf {K S M : Subgroup G} (hmin : MinParabolic K S M)
    {A : Subgroup G} (hAJ : A ≤ kerIn M K) : ¬ 2 ∣ (A ⊓ pCoreOf 2 K).relIndex A := by
  have hsyl := hmin.isSylowTwoOf_pCoreOf_kerIn
  have hQJ : pCoreOf 2 K ≤ kerIn M K := hsyl.1
  have hAK : A ≤ K := hAJ.trans hmin.kerIn_le_H
  have hAQ : A ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hAK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have h1 := B6.relIndex_sup_eq_of_le_normalizer hAQ
  have h2 : (A ⊓ pCoreOf 2 K).relIndex A = (pCoreOf 2 K).relIndex A :=
    Subgroup.inf_relIndex_left A (pCoreOf 2 K)
  have h3 : (pCoreOf 2 K).relIndex (A ⊔ pCoreOf 2 K) ∣ (pCoreOf 2 K).relIndex (kerIn M K) := by
    rw [← Subgroup.relIndex_mul_relIndex (pCoreOf 2 K) (A ⊔ pCoreOf 2 K) (kerIn M K)
      le_sup_right (sup_le hAJ hQJ)]
    exact dvd_mul_right _ _
  rw [h2, ← h1]
  intro hd
  exact hsyl.2.2 (hd.trans h3)

theorem isSolvable_of_autI_card_three {K S M V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hmin : MinParabolic K S M) (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hCK : K ⊓ Subgroup.centralizer (V : Set G) ≤ kerIn M K)
    {C : Subgroup (MulAut (IntMod V hV))} (hC3 : Nat.card C = 3) {Y : Subgroup G}
    (hYK : Y ≤ K) (hYC : autI hV Y = C) : Group.IsSolvable ↥Y := by
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := hYK.trans hKN
  have hker : Y ⊓ Subgroup.centralizer (V : Set G) ≤ kerIn M K :=
    (inf_le_inf_right _ hYK).trans hCK
  haveI hJ : Group.IsSolvable ↥(kerIn M K) := isSolvable_kerIn hmin
  haveI h1 : Group.IsSolvable ↥(Y ⊓ Subgroup.centralizer (V : Set G)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hker)
  have hrange : (convHom hV Y hYN).range = C := by rw [range_convHom, hYC]
  haveI h2 : Group.IsSolvable ↥(convHom hV Y hYN).range := by
    rw [hrange]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic ↥C := isCyclic_of_prime_card hC3
    letI := IsCyclic.commGroup (α := ↥C)
    exact inferInstance
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (inf_le_left : Y ⊓ Subgroup.centralizer (V : Set G) ≤ Y))
    (convHom hV Y hYN).rangeRestrict ?_
  intro y hy
  have hy' : y ∈ (convHom hV Y hYN).ker := by
    simpa [MonoidHom.ker_rangeRestrict] using hy
  rw [ker_convHom] at hy'
  exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy'⟩, rfl⟩

theorem isSylowTwoOf_R₁_sup {K S M V T : Subgroup G} {hV : IsElemAbelian 2 V}
    (hmin : MinParabolic K S M) (hred : IsTwoReducedIn K V)
    (hCK : K ⊓ Subgroup.centralizer (V : Set G) ≤ kerIn M K) (hbS : baum T ≤ S)
    {C : Subgroup (MulAut (IntMod V hV))} (hC3 : Nat.card C = 3) {Y : Subgroup G}
    (hYK : Y ≤ K) (hYC : autI hV Y = C) (hRY : R₁ K T ≤ Subgroup.normalizer (Y : Set G)) :
    IsSylowTwoOf (R₁ K T) (Y ⊔ R₁ K T) := by
  have hQS : pCoreOf 2 K ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hRS : R₁ K T ≤ S := sup_le hQS hbS
  have hR2 : IsPGroup 2 ↥(R₁ K T) := hmin.isSylow.2.1.to_le hRS
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := hYK.trans hred.2.1
  have hQC : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) :=
    MinParabolic.pCoreOf_le_centralizer hred
  refine ⟨le_sup_right, hR2, ?_⟩
  have h1 : (R₁ K T ⊓ Y).relIndex Y = (R₁ K T).relIndex (R₁ K T ⊔ Y) :=
    B6.relIndex_inf_eq_relIndex_sup hRY
  show ¬ 2 ∣ (R₁ K T).relIndex (Y ⊔ R₁ K T)
  rw [sup_comm, ← h1]
  have h2 : Y ⊓ pCoreOf 2 K ≤ R₁ K T ⊓ Y :=
    le_inf (inf_le_right.trans (pCoreOf_le_R₁ K T)) inf_le_left
  have h3 : (R₁ K T ⊓ Y).relIndex Y ∣ (Y ⊓ pCoreOf 2 K).relIndex Y :=
    Subgroup.relIndex_dvd_of_le_left Y h2
  have hYCle : Y ⊓ pCoreOf 2 K ≤ Y ⊓ Subgroup.centralizer (V : Set G) := inf_le_inf_left Y hQC
  have h4 : (Y ⊓ pCoreOf 2 K).relIndex (Y ⊓ Subgroup.centralizer (V : Set G)) *
      (Y ⊓ Subgroup.centralizer (V : Set G)).relIndex Y = (Y ⊓ pCoreOf 2 K).relIndex Y :=
    Subgroup.relIndex_mul_relIndex _ _ _ hYCle inf_le_left
  have h5 : (Y ⊓ Subgroup.centralizer (V : Set G)).relIndex Y = 3 := by
    rw [← card_autI_eq hV hYN, hYC, hC3]
  have h6 : (Y ⊓ pCoreOf 2 K).relIndex (Y ⊓ Subgroup.centralizer (V : Set G)) =
      ((Y ⊓ Subgroup.centralizer (V : Set G)) ⊓ pCoreOf 2 K).relIndex
        (Y ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [inf_assoc, inf_eq_right.2 hQC]
  have h7 : ¬ 2 ∣ ((Y ⊓ Subgroup.centralizer (V : Set G)) ⊓ pCoreOf 2 K).relIndex
      (Y ⊓ Subgroup.centralizer (V : Set G)) :=
    not_two_dvd_relIndex_inf_pCoreOf hmin ((inf_le_inf_right _ hYK).trans hCK)
  intro hd
  have hd' := hd.trans h3
  rw [← h4, h5, h6] at hd'
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd' with h | h
  · exact h7 h
  · omega

theorem not_le_normalizer_R₁_sup {K S M V T : Subgroup G} (hmin : MinParabolic K S M)
    (hred : IsTwoReducedIn K V) (hbS : baum T ≤ S) (hST : S ≤ T)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G)) {Y : Subgroup G}
    (hgen : Y ⊔ S = K) : ¬ Y ⊔ R₁ K T ≤ Subgroup.normalizer (R₁ K T : Set G) := by
  intro h
  have hQS : pCoreOf 2 K ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hRS : R₁ K T ≤ S := sup_le hQS hbS
  have hRT : R₁ K T ≤ T := hRS.trans hST
  have hbR : baum T = baum (R₁ K T) := baum_eq_of_le (baum_le_R₁ K T) hRT
  have hYN : Y ≤ Subgroup.normalizer (baum T : Set G) := fun y hy => by
    have := normalizer_le_normalizer_baum (R₁ K T)
      (h ((le_sup_left : Y ≤ Y ⊔ R₁ K T) hy))
    rwa [← hbR] at this
  have hTN : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hKN : K ≤ Subgroup.normalizer (baum T : Set G) := by
    rw [← hgen]
    exact sup_le hYN (fun s hs => hTN (hST hs))
  have hbK : baum T ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hbS.trans hmin.isSylow.1) hKN
      (hmin.isSylow.2.1.to_le hbS)
  apply hJ
  have hbS' : baum T = baum S := baum_eq_of_le hbS hST
  refine (B6.thompsonJ_le_baum S).trans ?_
  rw [← hbS']
  exact hbK.trans (MinParabolic.pCoreOf_le_centralizer hred)

theorem not_le_centralizer_sup_pGroup {K V R Y : Subgroup G} {hV : IsElemAbelian 2 V}
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hRK : R ≤ K) (hR2 : IsPGroup 2 ↥R)
    {C : Subgroup (MulAut (IntMod V hV))} (hC3 : Nat.card C = 3) (hYK : Y ≤ K)
    (hYC : autI hV Y = C) : ¬ Y ≤ Subgroup.centralizer (V : Set G) ⊔ R := by
  intro hYM
  have hRCv : R ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    fun g hg => B6.le_normalizer_centralizer hKN (hRK hg)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 (by rw [hC3])
  have hφY : (φ : MulAut (IntMod V hV)) ∈ autI hV Y := hYC ▸ φ.2
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hφY
  have hgM := hYM hgY
  have : (g : G) ∈ (Subgroup.centralizer (V : Set G) : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hRCv]
    exact hgM
  obtain ⟨c, hc, r, hr, hcr⟩ := Set.mem_mul.1 this
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := hKN (hRK hr)
  have hcN : c ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer (V : Set G) hc
  have h1 : convI hV g = convI hV ⟨r, hrN⟩ := by
    have : g = ⟨c, hcN⟩ * ⟨r, hrN⟩ := Subtype.ext hcr.symm
    rw [this, map_mul, (convI_eq_one_iff hV ⟨c, hcN⟩).2 hc, one_mul]
  have h2 : (convI hV ⟨r, hrN⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨r, hrN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have h3 : (φ : MulAut (IntMod V hV)) ^ 2 ^ k = 1 := by rw [← hg, h1]; exact h2
  have h4 : orderOf (φ : MulAut (IntMod V hV)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h3
  rw [Subgroup.orderOf_coe, hφ] at h4
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4) (by decide)

theorem isUniqueMaxOver_R₁_sup {K S M V T : Subgroup G} {hV : IsElemAbelian 2 V}
    (hmin : MinParabolic K S M) (hred : IsTwoReducedIn K V) (hbS : baum T ≤ S)
    {C : Subgroup (MulAut (IntMod V hV))} (hC3 : Nat.card C = 3) {Y : Subgroup G}
    (hYK : Y ≤ K) (hYC : autI hV Y = C) (hRY : R₁ K T ≤ Subgroup.normalizer (Y : Set G))
    (hminY : ∀ Z : Subgroup G, Z ≤ Y → R₁ K T ≤ Subgroup.normalizer (Z : Set G) →
      autI hV Z = C → Z = Y) :
    IsUniqueMaxOver (Y ⊔ R₁ K T) (R₁ K T)
      ((Y ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₁ K T) := by
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hQS : pCoreOf 2 K ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hRS : R₁ K T ≤ S := sup_le hQS hbS
  have hRK : R₁ K T ≤ K := hRS.trans hmin.isSylow.1
  have hR2 : IsPGroup 2 ↥(R₁ K T) := hmin.isSylow.2.1.to_le hRS
  have hRCv : R₁ K T ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    fun g hg => B6.le_normalizer_centralizer hKN (hRK hg)
  have hRYC : R₁ K T ≤ Subgroup.normalizer
      ((Y ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hRY hg, hRCv hg⟩
  have hP : ∀ x ∈ Y ⊔ R₁ K T, ∃ y ∈ Y, ∃ r ∈ R₁ K T, y * r = x := by
    intro x hx
    have : x ∈ (Y : Set G) * (R₁ K T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y (R₁ K T) hRY]
      exact hx
    exact Set.mem_mul.1 this
  have hMP : (Y ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₁ K T ≤ Y ⊔ R₁ K T :=
    sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hdich : ∀ X : Subgroup G, R₁ K T ≤ X → X ≤ Y ⊔ R₁ K T →
      X ≤ (Y ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₁ K T ∨ X = Y ⊔ R₁ K T := by
    intro X hRX hXP
    have hdec : ∀ x ∈ X, ∃ y ∈ X ⊓ Y, ∃ r ∈ R₁ K T, y * r = x := by
      intro x hx
      obtain ⟨y, hy, r, hr, rfl⟩ := hP x (hXP hx)
      refine ⟨y, ⟨?_, hy⟩, r, hr, rfl⟩
      have := X.mul_mem hx (X.inv_mem (hRX hr))
      simpa using this
    have hRX' : R₁ K T ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hRX hg), hRY hg⟩
    have hXYK : X ⊓ Y ≤ K := inf_le_right.trans hYK
    have hle : autI hV (X ⊓ Y) ≤ C := hYC ▸ autI_mono hV inf_le_right
    have hcard : Nat.card (autI hV (X ⊓ Y)) ∣ 3 := hC3 ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).1 hcard with h1 | h3
    · left
      have hbot : autI hV (X ⊓ Y) = ⊥ := Subgroup.card_eq_one.1 h1
      have hcent : X ⊓ Y ≤ Subgroup.centralizer (V : Set G) :=
        (autI_eq_bot_iff hV (hXYK.trans hKN)).1 hbot
      intro x hx
      obtain ⟨y, hy, r, hr, rfl⟩ := hdec x hx
      exact Subgroup.mul_mem_sup ⟨hy.2, hcent hy⟩ hr
    · right
      have heq : autI hV (X ⊓ Y) = C := Subgroup.eq_of_le_of_card_ge hle (by rw [hC3, h3])
      have hXY : X ⊓ Y = Y := hminY (X ⊓ Y) inf_le_right hRX' heq
      have hYX : Y ≤ X := hXY ▸ inf_le_left
      exact le_antisymm hXP (sup_le hYX hRX)
  have hMPlt : (Y ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₁ K T < Y ⊔ R₁ K T := by
    refine lt_of_le_of_ne hMP fun heq => ?_
    have hYM : Y ≤ (Y ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₁ K T := le_sup_left.trans heq.ge
    exact not_le_centralizer_sup_pGroup hKN hRK hR2 hC3 hYK hYC
      (hYM.trans (sup_le_sup_right inf_le_right _))
  rw [isUniqueMaxOver_iff]
  refine ⟨⟨hMPlt, fun X hMX hXP => ?_⟩, le_sup_right, fun N hN hRN => ?_⟩
  · rcases hdich X (le_sup_right.trans hMX.le) hXP with h | h
    · exact absurd h (not_le_of_gt hMX)
    · exact h
  · rcases hdich N hRN hN.1.le with h | h
    · by_contra hne
      have hlt : N < (Y ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₁ K T := lt_of_le_of_ne h hne
      exact absurd (hN.2 _ hlt hMP) (ne_of_lt hMPlt)
    · exact absurd h hN.1.ne

theorem exists_solvable_minParabolic_sym {K S M V T : Subgroup G} (hV : IsElemAbelian 2 V)
    (hmin : MinParabolic K S M) (hF : CharTwo K) (hred : IsTwoReducedIn K V)
    (hbS : baum T ≤ S) (hST : S ≤ T)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G))
    {C : Subgroup (MulAut (IntMod V hV))} {Y₀ : Subgroup G}
    (hY₀K : Y₀ ≤ K) (hC3 : Nat.card C = 3) (hY₀C : autI hV Y₀ = C)
    (hY₀N : R₁ K T ≤ Subgroup.normalizer (Y₀ : Set G))
    (hgen : ∀ Y : Subgroup G, Y ≤ K → autI hV Y = C → Y ⊔ S = K) :
    ∃ Y' M' : Subgroup G, Y' ≤ K ∧ autI hV Y' = C ∧
      R₁ K T ≤ Subgroup.normalizer (Y' : Set G) ∧
      MinParabolic (Y' ⊔ R₁ K T) (R₁ K T) M' ∧ Group.IsSolvable ↥(Y' ⊔ R₁ K T) ∧
      CharTwo (Y' ⊔ R₁ K T) ∧ Y' ⊔ S = K := by
  obtain ⟨Y', ⟨hY'K, hY'C, hY'N⟩, hY'min⟩ := WellFounded.has_min
    (wellFounded_lt (α := Subgroup G))
    {Y : Subgroup G | Y ≤ K ∧ autI hV Y = C ∧ R₁ K T ≤ Subgroup.normalizer (Y : Set G)}
    ⟨Y₀, hY₀K, hY₀C, hY₀N⟩
  have hminY : ∀ Z : Subgroup G, Z ≤ Y' → R₁ K T ≤ Subgroup.normalizer (Z : Set G) →
      autI hV Z = C → Z = Y' := by
    intro Z hZY hZN hZC
    by_contra hne
    exact hY'min Z ⟨hZY.trans hY'K, hZC, hZN⟩ (lt_of_le_of_ne hZY hne)
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hHV : ¬ K ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((B6.thompsonJ_le S).trans (hmin.isSylow.1.trans h))
  have hCK := hmin.inf_centralizer_le_kerIn hred hHV
  have hQS : pCoreOf 2 K ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hRS : R₁ K T ≤ S := sup_le hQS hbS
  have hR2 : IsPGroup 2 ↥(R₁ K T) := hmin.isSylow.2.1.to_le hRS
  have hgen' := hgen Y' hY'K hY'C
  have hPK : Y' ⊔ R₁ K T ≤ K := sup_le hY'K (hRS.trans hmin.isSylow.1)
  have hYsol : Group.IsSolvable ↥Y' :=
    isSolvable_of_autI_card_three hmin hKN hCK hC3 hY'K hY'C
  refine ⟨Y', (Y' ⊓ Subgroup.centralizer (V : Set G)) ⊔ R₁ K T, hY'K, hY'C, hY'N,
    ⟨isSylowTwoOf_R₁_sup hmin hred hCK hbS hC3 hY'K hY'C hY'N,
      not_le_normalizer_R₁_sup hmin hred hbS hST hJ hgen',
      isUniqueMaxOver_R₁_sup hmin hred hbS hC3 hY'K hY'C hY'N hminY⟩,
    CFSG.Quasithin.ModH.isSolvable_sup_of_le_normalizer hYsol hR2 hY'N,
    charTwo_of_pCore_le hF ((pCoreOf_le_R₁ K T).trans le_sup_right) hPK, hgen'⟩

end CFSG.AGLEmbeddingD2.Tits.GN516
