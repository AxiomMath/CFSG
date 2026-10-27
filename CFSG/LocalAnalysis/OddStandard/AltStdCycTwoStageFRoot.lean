module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageFBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdWeakTop
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS1
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS2a

public section

namespace CFSG.OddStandard.AltStdCycTwo.StageF

open Subgroup Equiv AltStdBal AltStdSec CFSG.ComponentClassification.RestrictedStd.Spor
open scoped Pointwise

section Parity

theorem four_dvd_card_support {α : Type*} [Fintype α] [DecidableEq α] {t : Perm α}
    (ht : orderOf t = 2) (hs : Perm.sign t = 1) : 4 ∣ t.support.card := by
  have hcyc : ∀ n ∈ t.cycleType, n = 2 := fun n hn => by
    have h1 := Perm.dvd_of_mem_cycleType hn
    have h2 := Perm.two_le_of_mem_cycleType hn
    rw [ht] at h1
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  obtain ⟨c, hrep⟩ : ∃ c, t.cycleType = Multiset.replicate c 2 :=
    ⟨_, Multiset.eq_replicate_card.2 hcyc⟩
  have hsum : t.support.card = 2 * c := by
    rw [← Perm.sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsign := Perm.sign_of_cycleType t
  rw [hrep, hs, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hpow : (-1 : ℤˣ) ^ c = 1 := by
    have h2 : (-1 : ℤˣ) ^ (c * 2 + c) = (-1 : ℤˣ) ^ c := by
      rw [pow_add, pow_mul]; simp
    rw [← h2]; exact hsign.symm
  have heven : Even c := (neg_one_pow_eq_one_iff_even (by decide)).1 hpow
  obtain ⟨k, hk⟩ := heven
  exact ⟨k, by omega⟩

theorem card_fixFin_add_card_support {n : ℕ} (σ : Perm (Fin n)) :
    (fixFin σ).card + σ.support.card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => σ i = i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hs : σ.support = Finset.univ.filter (fun i => ¬ σ i = i) := by
    ext i
    simp [Perm.mem_support]
  rw [hs]
  exact h

theorem odd_card_fixFin {n : ℕ} (hn : Odd n) {σ : Perm (Fin n)} (hσ : orderOf σ = 2)
    (hs : Perm.sign σ = 1) : Odd (fixFin σ).card := by
  obtain ⟨k, hk⟩ := four_dvd_card_support hσ hs
  have h := card_fixFin_add_card_support σ
  obtain ⟨m, hm⟩ := hn
  exact ⟨m - 2 * k, by omega⟩

theorem orderOf_perm_of_mem {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
    (e : L ≃* alternatingGroup (Fin n)) {y : G} (hy : y ∈ L) (hy2 : orderOf y = 2) :
    orderOf ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]

end Parity

section Root

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem Inner.centralizer_ne_top (c : Inner G L Q n z) {R : Subgroup G}
    (hR : ∃ r ∈ R, r ≠ 1) : centralizer (R : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨r, hr, hr1⟩ := hR
  have hc : r ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer (R : Set G) := htop ▸ Subgroup.mem_top g
    exact (mem_centralizer_iff.1 this r hr).symm
  rw [center_eq_bot_of_simple_nonabelian c.std.simple c.std.nonab, Subgroup.mem_bot] at hc
  exact hr1 hc

theorem Inner.centralizer_sec_le (c : Inner G L Q n z) {R B : Subgroup G} {m : ℕ}
    (hRL : R ≤ L) (hBL : B ≤ L) (hRD : RootData L z R B m) :
    centralizer ({(QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R)} : Set (Sec G R)) ≤
      secImage R B ⊔ zpowers (QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R) := by
  intro x hx
  have ht₀2 : (⟨z, hRD.hz⟩ : ↥(centralizer (R : Set G))) * ⟨z, hRD.hz⟩ = 1 :=
    Subtype.ext c.cyc.mul_self
  obtain ⟨w, hw, rfl⟩ := exists_centralizer_preimage
    (P := CFSG.oddCore ↥(centralizer (R : Set G)))
    (fun y hy => orderOf_odd_of_mem_oddCore hy) ht₀2 hx
  have hwz : (w : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hw ⊢
    exact congrArg Subtype.val hw
  have hKN : centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G)) hKN
  have hw' : (w : G) ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hm]
    exact c.hE hwz
  obtain ⟨l, hl, k, hk, hlk⟩ := Set.mem_mul.1 hw'
  have hkR : k ∈ centralizer (R : Set G) := Subgroup.centralizer_le hRL hk
  have hlR : l ∈ centralizer (R : Set G) := by
    have : l = (w : G) * k⁻¹ := by rw [← hlk]; group
    rw [this]
    exact mul_mem w.2 (inv_mem hkR)
  have hkz : k * z = z * k := by
    have hkC : k ∈ centralizer ({z} : Set G) := by
      have : k = l⁻¹ * (w : G) := by rw [← hlk]; group
      rw [this]
      exact mul_mem (inv_mem (c.le_cent hl)) hwz
    exact mem_centralizer_singleton_iff.1 hkC
  have hsplit : (QuotientGroup.mk w : Sec G R) =
      QuotientGroup.mk (⟨l, hlR⟩ : ↥(centralizer (R : Set G))) *
        QuotientGroup.mk (⟨k, hkR⟩ : ↥(centralizer (R : Set G))) := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hlk.symm
  rw [hsplit]
  refine mul_mem (mem_sup_left (hRD.mk_mem ⟨l, hlR⟩ hl)) (mem_sup_right ?_)
  rw [← hRD.shape.cent_cent]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hh
    have hbL : (b : G) ∈ L := hBL (Subgroup.mem_subgroupOf.1 hb)
    have hkb : (b : G) * k = k * b := mem_centralizer_iff.1 hk _ hbL
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkb
  · rw [mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkz

theorem Inner.zstar_or_wreath_of_rootData (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput) (hFour : FourExactOuterInput) (c : Inner G L Q n z)
    {R B : Subgroup G} {m : ℕ} (hRL : R ≤ L) (hBL : B ≤ L) (hRD : RootData L z R B m)
    (hm : 9 ≤ m) (hR1 : ∃ r ∈ R, r ≠ 1) :
    IsZStar R z ∨ WreathOutcome (QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R) (secImage R B) m := by
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G R) :=
    isKGroupCat_sec (isKGroupCat_of_kProper c.std.kProper) (c.centralizer_ne_top hR1)
  have hO : CFSG.oddCore (Sec G R) = ⊥ := oddCore_sec_eq_bot R
  rcases section_dichotomy hO hRD.shape (by omega) with h1 | h2 | h3
  · exact Or.inl (isZStar_iff_mem_center.2 ⟨hRD.hz, h1⟩)
  · exact Or.inr h2
  · exact (false_of_almostSimple_shape_one hlookup hHN hFour hKcat hO hRD.shape hm h3
      (c.centralizer_sec_le hRL hBL hRD)).elim

theorem Inner.wreath_fusion_of_rootData (c : Inner G L Q n z) {R B : Subgroup G} {m : ℕ}
    (hRD : RootData L z R B m) (hm : 5 ≤ m)
    (hW : WreathOutcome (QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R) (secImage R B) m)
    {b : G} (hbL : b ∈ L) (hbC : b ∈ centralizer (R : Set G)) (hb2 : orderOf b = 2) :
    ∃ h' ∈ centralizer (R : Set G), h' * z * h'⁻¹ = z * b := by
  have hbz : b * z = z * b := mem_centralizer_singleton_iff.1 (c.le_cent hbL)
  have hb2' : b * b = 1 := by rw [← sq, ← hb2]; exact pow_orderOf_eq_one b
  obtain ⟨h', hh'⟩ := exists_fusion_of_wreath
    (t := (⟨z, hRD.hz⟩ : ↥(centralizer (R : Set G)))) (β := ⟨b, hbC⟩) hm
    (Subtype.ext c.cyc.mul_self) (Subtype.ext hb2') (Subtype.ext hbz) hW
    (hRD.mk_mem ⟨b, hbC⟩ hbL)
  exact ⟨h', h'.2, congrArg Subtype.val hh'⟩

theorem Inner.rootData (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (c : Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)}
    (hS : S.card = 3 ∨ S.card = 4) (hSc : 9 ≤ n - S.card) :
    RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card) := by
  rcases hS with hS | hS
  · exact rootData_of_weakShape_three hlookup hHN hOut hFour c.std c.cyc c.card e hS hSc
  · exact rootData_of_weakShape hlookup hHN hOut hFour c.std c.cyc c.card e (by omega) hSc

theorem Inner.zstar_or_fusion (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (c : Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n)) {k : ℕ} (hk : 3 ≤ k)
    (hk' : k ≤ 4) (S : Finset (Fin n)) (hS : S.card = k) :
    IsZStar (rootGroup e S) z ∨
      ∀ b ∈ L, b ∈ centralizer (rootGroup e S : Set G) → orderOf b = 2 →
        ∃ h' ∈ centralizer (rootGroup e S : Set G), h' * z * h'⁻¹ = z * b := by
  have hS' : S.card = 3 ∨ S.card = 4 := by omega
  have hm : 9 ≤ n - S.card := by
    have := c.hn
    omega
  have hRD := c.rootData hlookup hHN hOut hFour e hS' hm
  rcases c.zstar_or_wreath_of_rootData hlookup hHN hFour (corr_le e (altSub S))
      (corr_le e (altSub Sᶜ)) hRD hm (exists_ne_one_of_card_ge_three e (by omega)) with h1 | h2
  · exact Or.inl h1
  · right
    intro b hbL hbC hb2
    exact c.wreath_fusion_of_rootData hRD (by omega) h2 hbL hbC hb2

end Root

end CFSG.OddStandard.AltStdCycTwo.StageF
