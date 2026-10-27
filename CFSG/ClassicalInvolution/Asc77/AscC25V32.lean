module

public import CFSG.ClassicalInvolution.Asc77.AscC25V31
public import CFSG.ClassicalInvolution.Asc77.AscC25V23
public import CFSG.ClassicalInvolution.Asc77.AscC25V26
public import CFSG.ClassicalInvolution.Asc77.AscC25V30
public import CFSG.ClassicalInvolution.Asc77.AscC25X13
public import CFSG.ClassicalInvolution.Asc77.AscT7TWire
public import CFSG.ClassicalInvolution.Asc77.AscT7U10
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Nbr

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fs_nbr_twin (d : TwinCtx p f Ω K K' z) {a : G} {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (perfectCoreIn K a) ∈
      omegaNbr (conjFamily (perfectCoreIn K a)) (conjSub c₁ (perfectCoreIn K a))) :
    conjSub (c₂ : G) K ∈ twinSet Ω (conjSub (c₁ : G) K) := by
  by_contra htw
  obtain ⟨-, hne, R₀, hR, hRle, hRN⟩ := h
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSet d.hp2 h5 hL hR
  have hR2 := isPGroup_of_mem_rSet hR
  have hne' : conjSub (c₁ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub (c₂ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
    intro h
    apply hne
    apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
    rw [map_conjSub_perfectCore, map_conjSub_perfectCore, h]
  refine fs_false_of_le_normalizer d hzKa c₁.2 c₂.2 hne' htw
    (hR2.map (Subgroup.centralizer ({a} : Set G)).subtype)
    ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
      fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₀ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    omega
  · rw [← map_conjSub_perfectCore]
    exact Subgroup.map_mono hRle
  · rw [← map_conjSub_perfectCore]
    exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)

theorem conjSub_member_eq {a : G} {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub (c₁ : G) K = conjSub (c₂ : G) K) :
    conjSub c₁ (perfectCoreIn K a) = conjSub c₂ (perfectCoreIn K a) := by
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [map_conjSub_perfectCore, map_conjSub_perfectCore]
  exact conjSub_perfectCore_eq c₁.2 c₂.2 h

theorem fs_nbr_eq (d : TwinCtx p f Ω K K' z) {a : G} {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (perfectCoreIn K a) ∈
      omegaNbr (conjFamily (perfectCoreIn K a)) (conjSub c₁ (perfectCoreIn K a))) :
    conjSub c₂ (perfectCoreIn K a) = conjSub (c₁ * w) (perfectCoreIn K a) := by
  have htw := fs_nbr_twin d h5 hzA hL h
  have h1 := twinSet_conj d.hΩ.conjInvariant htw (c₁ : G)⁻¹
  rw [conjSub_inv_conjSub, d.htw] at h1
  have e1 : conjSub ((c₁ : G)⁻¹) (conjSub (c₂ : G) K) = conjSub ((c₁ : G)⁻¹ * (c₂ : G)) K := by
    rw [conjSub_mul]
  rw [e1] at h1
  rcases h1 with h1 | h1
  · exfalso
    apply h.2.1
    apply conjSub_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left] at h2
    exact h2
  · apply conjSub_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left, ← hw, ← conjSub_mul] at h2
    exact h2

theorem secImg_conjSub_odd {a : G} (L : Subgroup ↥(Subgroup.centralizer ({a} : Set G)))
    {n : ↥(conjGen L)} (hn : n ∈ classicalInvolutionOddCore ↥(conjGen L))
    {M : Subgroup ↥(Subgroup.centralizer ({a} : Set G))} (hM : M ≤ conjGen L) :
    secImg (conjGen L) (conjSub (n : ↥(Subgroup.centralizer ({a} : Set G))) M) =
      secImg (conjGen L) M := by
  have := conjGen_normal L
  have h1 : secAct (conjGen L) (n : ↥(Subgroup.centralizer ({a} : Set G))) = 1 :=
    secAct_eq_one_of_mem (conjGen L)
      (mem_oddCoreOf_iff.mpr ⟨n.2, hn⟩)
  have h2 := secAct_secImg (conjGen L) (n : ↥(Subgroup.centralizer ({a} : Set G))) hM
  rw [← h2, h1]
  ext x
  simp

theorem fs_nbr_quot (d : TwinCtx p f Ω K K' z) {a : G} {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    (hΛ : HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)))
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    (c₀ : ↥(Subgroup.centralizer ({a} : Set G)))
    {M : Subgroup (↥(conjGen (perfectCoreIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))}
    (hM : M ∈ omegaNbr (oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K a))
      (conjGen (perfectCoreIn K a)))) (secImg (conjGen (perfectCoreIn K a))
        (conjSub c₀ (perfectCoreIn K a)))) :
    M = secImg (conjGen (perfectCoreIn K a)) (conjSub (c₀ * w) (perfectCoreIn K a)) := by
  obtain ⟨c, rfl⟩ := (mem_secFamily_iff (perfectCoreIn K a) M).mp hM.1
  set L := perfectCoreIn K a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaMod p e₀ (restrictFamily (conjFamily L) X) := hΛ.restrict X
  have hΛ' : HypOmegaMod p e₀
      (quotFamily (restrictFamily (conjFamily L) X) (classicalInvolutionOddCore ↥X)) :=
    oddQuotHyp p e₀ hp h5 ↥X _ hΛ₁ _ hN
  have hK : (conjSub c₀ L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c₀ L, ⟨c₀, rfl⟩, le_conjGen ⟨c₀, rfl⟩, rfl⟩
  have hJ : (conjSub c L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c L, ⟨c, rfl⟩, le_conjGen ⟨c, rfl⟩, rfl⟩
  obtain ⟨n, hn, hnb⟩ := exists_conj_omegaNbr hp h5 hΛ₁ hΛ' hN hK hJ hM
  rw [conjSub_subgroupOf] at hnb
  have hnL : conjSub (n : ↥(Subgroup.centralizer ({a} : Set G))) (conjSub c₀ L) ≤ X :=
    le_conjGen ⟨(n : ↥(Subgroup.centralizer ({a} : Set G))) * c₀, conjSub_mul _ _ _⟩
  have hcL : conjSub c L ≤ X := le_conjGen ⟨c, rfl⟩
  have hnb' := omegaNbr_of_restrict hnL hcL hnb
  rw [← conjSub_mul] at hnb'
  have heq := fs_nbr_eq d h5 hzA hL hw hnb'
  rw [heq, mul_assoc, conjSub_mul]
  exact secImg_conjSub_odd L hn (le_conjGen ⟨c₀ * w, rfl⟩)

end Nbr

local notation "pRes" => CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual

theorem mem_perfectResidual_of_isPGroup {C Q : Type*} [Group C] [Finite C] [Group Q]
    [Group.IsPerfect Q] (π : C →* Q) (hπ : Function.Surjective π)
    (hN : ∀ n, π n = 1 → Odd (orderOf n)) {x : C} (hx : IsPGroup 2 (Subgroup.zpowers x)) :
    x ∈ pRes C := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := finite_perfectResidual_surjects_to_perfect_image π hπ
  have hpx : π x ∈ Subgroup.map π (pRes C) := by
    rw [hP]
    exact Subgroup.mem_top _
  obtain ⟨p', hp', hpx'⟩ := hpx
  have hn : π (p'⁻¹ * x) = 1 := by rw [map_mul, map_inv, hpx', inv_mul_cancel]
  have hchar : (pRes C).Characteristic := perfectResidual_characteristic
  have hxq : (QuotientGroup.mk x : C ⧸ pRes C) = QuotientGroup.mk (p'⁻¹ * x) := by
    rw [QuotientGroup.eq]
    have h1 : x⁻¹ * (p'⁻¹ * x) = x⁻¹ * p'⁻¹ * x⁻¹⁻¹ := by group
    rw [h1]
    exact (pRes C).normal_of_characteristic.conj_mem _
      ((pRes C).inv_mem hp') _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(Subgroup.zpowers x))).mp hx
  rw [Nat.card_zpowers] at hk
  have hd1 : orderOf (QuotientGroup.mk x : C ⧸ pRes C) ∣ 2 ^ k := by
    rw [← hk]
    exact orderOf_map_dvd (QuotientGroup.mk' (pRes C)) x
  have hd2 : orderOf (QuotientGroup.mk x : C ⧸ pRes C) ∣ orderOf (p'⁻¹ * x) := by
    rw [hxq]
    exact orderOf_map_dvd (QuotientGroup.mk' (pRes C)) (p'⁻¹ * x)
  have hcop : Nat.Coprime (2 ^ k) (orderOf (p'⁻¹ * x)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hN _ hn))
  have h1 : orderOf (QuotientGroup.mk x : C ⧸ pRes C) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h1)

section Nbr2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem mem_perfectResidualOf_of_isPGroup (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    {K : Subgroup G} (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) {x : G} (hxK : x ∈ K)
    (hxb : x ∈ Subgroup.centralizer ({b} : Set G)) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    x ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨e₀, hfe, h5, ⟨φ'⟩⟩ := fs_fix_equiv hp hq h9 e hbN hb2 hσ1
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      simp at h5
    · exact h
  have hcardm : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have : Fintype (GaloisField p e₀) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField p e₀), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField p e₀))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardm]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect SL(2, GaloisField p e₀) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField p e₀) (n := 2) le_rfl (Or.inr h4)
  have hperf : Group.IsPerfect ↥(slFix e ⟨b, hbN⟩) :=
    Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  have hker : ∀ n : ↥(K ⊓ Subgroup.centralizer ({b} : Set G)), fixHom e hbN n = 1 →
      Odd (orderOf n) := by
    intro n hn
    have h1 := mem_oddCoreOf_of_fixHom_eq_one e hbN hn
    have h2 : orderOf (n : G) ∣ Nat.card ↥(oddCoreOf K) := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_coe] at h2
    exact Odd.of_dvd_nat (oddCoreOf_odd_natCard K) h2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(Subgroup.zpowers x))).mp hx2
  have hx2' : IsPGroup 2 (Subgroup.zpowers
      (⟨x, hxK, hxb⟩ : ↥(K ⊓ Subgroup.centralizer ({b} : Set G)))) := by
    rw [IsPGroup.iff_card]
    refine ⟨k, ?_⟩
    have hoe : orderOf (⟨x, hxK, hxb⟩ : ↥(K ⊓ Subgroup.centralizer ({b} : Set G))) = orderOf x :=
      (Subgroup.orderOf_coe (⟨x, hxK, hxb⟩ : ↥(K ⊓ Subgroup.centralizer ({b} : Set G)))).symm
    rw [Nat.card_zpowers, hoe]
    rw [Nat.card_zpowers] at hk
    exact hk
  have hres := mem_perfectResidual_of_isPGroup (fixHom e hbN) (fixHom_surjective e hbN hb2) hker
    hx2'
  exact Subgroup.mem_map.mpr ⟨_, hres, rfl⟩

end Nbr2

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fs_swap_ne (d : TwinCtx p f Ω K K' z) {a : G} (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    {e₀ : ℕ} (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {c : ↥(Subgroup.centralizer ({a} : Set G))} (hcK : conjSub (c : G) K = K') :
    conjSub c (perfectCoreIn K a) ≠ perfectCoreIn K a := by
  have hΩ₀ := fs_hypOmegaMod_conjFamily d.hΩ d.hK d.hI hzA hL
  have hM₁ : perfectCoreIn K a ∈ conjFamily (perfectCoreIn K a) := ⟨1, conjSub_one _⟩
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hmap1 : (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype =
      perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have := map_conjSub_perfectCore (K := K) (a := a) 1
    simpa [conjSub_one] using this
  have hmap2 : (conjSub c (perfectCoreIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub (c : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
    map_conjSub_perfectCore c
  intro h
  obtain ⟨P, hP, hP1, -⟩ := exists_mem_RSet_ge hM₁
    (isPGroup_two_bot' (G := ↥(Subgroup.centralizer ({a} : Set G)))) bot_le
  have h8 := hΩ₀.eight_le_of_mem_RSet d.hp2 hP
  have hP2 : IsPGroup 2 P := hP1.2.1
  have hA2 : IsPGroup 2 (P.map (Subgroup.centralizer ({a} : Set G)).subtype) := hP2.map _
  have hcard : Nat.card ↥(P.map (Subgroup.centralizer ({a} : Set G)).subtype) = Nat.card P :=
    (Nat.card_congr (Subgroup.equivMapOfInjective P _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv).symm
  have hPle : P ≤ perfectCoreIn K a := hP1.1
  have hAK : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K := by
    rw [← hmap1] at hKaK
    exact (Subgroup.map_mono hPle).trans hKaK
  have hAK' : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K' := by
    have h1 : (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype ≤
        conjSub (c : G) K := by
      calc (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype
          = (conjSub c (perfectCoreIn K a)).map
              (Subgroup.centralizer ({a} : Set G)).subtype := by rw [h]
        _ = conjSub (c : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := hmap2
        _ ≤ conjSub (c : G) K := Subgroup.map_mono hKaK
    rw [hcK] at h1
    exact (Subgroup.map_mono hPle).trans h1
  exact d.ne (d.hΩ.eq_of_le_of_le d.hK d.hK' hA2 (by omega) hAK hAK').symm

theorem exists_order_four_mem_perfectCore
    (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a) :
    ∃ y ∈ R', orderOf y = 4 ∧ y * a = a * y ∧
      y ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨y, hyR', hy4, hya⟩ := exists_order_four_of_isFAut hF'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  have hfix := fix_of_isFAut h haS hF'
  have haK' : a ∈ Subgroup.normalizer (K' : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hfix.2.2.2
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK'
  have hσ1 : fieldChar hp hq e ⟨a, haK'⟩ ≠ 1 :=
    fieldChar_ne_one_of_isFAut hp hq e h.hR'syl.1 h.hqR' h.hzR' hF' ha2 haK'
  refine ⟨y, hyR', hy4, hya, ?_⟩
  refine mem_perfectResidualOf_of_isPGroup hp hq h9 e haK' ha2 hσ1 (h.hR'syl.1 hyR')
    (Subgroup.mem_centralizer_singleton_iff.mpr hya) ?_
  rw [IsPGroup.iff_card]
  exact ⟨2, by rw [Nat.card_zpowers, hy4]; norm_num⟩

end Twin

end CFSG.ClassicalInvolution.Asc77.C25V
