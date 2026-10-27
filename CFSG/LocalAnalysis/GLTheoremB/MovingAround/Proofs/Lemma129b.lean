module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129Y
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129W2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma116

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centralizer_barX_eq card_barX_of_isPGroup elemAbelian_barX)

section YLevel

variable {Y : Type} [Group Y] [Finite Y]

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W

theorem kconj_eq_gLBConj (K : Subgroup Y) (a : Y) (i : ℕ) : kconj a K i = GLBConj (a ^ i)⁻¹ K := by
  unfold kconj GLBConj
  rw [inv_inv]

theorem isComponentOf_kconj {K : Subgroup Y} (hK : IsComponentOf K ⊤) (a : Y) (i : ℕ) :
    IsComponentOf (kconj a K i) ⊤ := by
  rw [kconj_eq_gLBConj]
  exact isComponentOf_gLBConj hK _

theorem kconj_ne {K : Subgroup Y} {a : Y} {p : ℕ}
    (hcap : ∀ n : ℕ, 0 < n → n < p → a ^ n ∉ Subgroup.normalizer (K : Set Y))
    {i j : ℕ} (hij : i < j) (hjp : j < p) : kconj a K i ≠ kconj a K j := by
  intro heq
  apply hcap (j - i) (by omega) (by omega)
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 : GLBConj (a ^ i) (kconj a K i) = K := by
    rw [kconj_eq_gLBConj, gLBConj_gLBConj_inv]
  have h2 : GLBConj (a ^ j) (kconj a K j) = K := by
    rw [kconj_eq_gLBConj, gLBConj_gLBConj_inv]
  calc GLBConj (a ^ (j - i)) K = GLBConj (a ^ (j - i)) (GLBConj (a ^ i) (kconj a K i)) := by rw [h1]
    _ = GLBConj (a ^ i * a ^ (j - i)) (kconj a K i) := by rw [gLBConj_gLBConj]
    _ = GLBConj (a ^ j) (kconj a K j) := by rw [← pow_add, Nat.add_sub_cancel' hij.le, heq]
    _ = K := h2

theorem kconj_comm {K : Subgroup Y} {a : Y} {p : ℕ} (hK : IsComponentOf K ⊤)
    (hcap : ∀ n : ℕ, 0 < n → n < p → a ^ n ∉ Subgroup.normalizer (K : Set Y)) :
    ∀ i j : Fin p, i ≠ j → ∀ x ∈ kconj a K i, ∀ y ∈ kconj a K j, x * y = y * x := by
  intro i j hij x hx y hy
  have hne : kconj a K i ≠ kconj a K j := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact kconj_ne hcap h j.2
    · exact (kconj_ne hcap h i.2).symm
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    (isComponentOf_kconj hK a i) (isComponentOf_kconj hK a j) hne
  exact (Subgroup.mem_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx) y hy).symm

theorem center_trivial_of_centralizer_bot {K₁ : Subgroup Y} (hK₁ : IsComponentOf K₁ ⊤)
    {Ab : Subgroup Y}
    (hC : Subgroup.centralizer ((⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y) : Set Y) = ⊥) :
    ∀ z ∈ K₁, (∀ y ∈ K₁, z * y = y * z) → z = 1 := by
  intro z hz hzc
  have hle : (⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y) ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine iSup₂_le fun g hg x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases heq : GLBConj g K₁ = K₁
    · rw [heq] at hx
      exact (hzc x hx).symm
    · have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        (isComponentOf_gLBConj hK₁ g) hK₁ heq
      exact (Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx) z hz).symm
  have hz' : z ∈ Subgroup.centralizer ((⨆ g ∈ Ab, GLBConj g K₁ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  rw [hC, Subgroup.mem_bot] at hz'
  exact hz'

end YLevel

section Basic

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
  {S F K : Subgroup G}

theorem bc_rank (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hr2 : CFSG.Open.pRank p F = 2) :
    CFSG.Open.pRank p A = 3 ∧ F ≠ A ∧ (F.subgroupOf A).index = p := by
  have hp := prime_of h
  have h1 := hs.pRank_A_le hp h
  have h3 := three_le_rank_A h
  have hA3 : CFSG.Open.pRank p A = 3 := by omega
  have hFne : F ≠ A := fun hFA => by rw [hFA] at hr2; omega
  refine ⟨hA3, hFne, ?_⟩
  obtain ⟨B', hB'F, hB'i⟩ := hs.hyp
  have hdvd : (F.subgroupOf A).index ∣ p := hB'i ▸ Subgroup.relIndex_dvd_of_le_left A hB'F
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exfalso
    apply hFne
    have : F.subgroupOf A = ⊤ := Subgroup.index_eq_one.1 h1
    exact le_antisymm hs.F_le_A (Subgroup.subgroupOf_eq_top.1 this)
  · exact h1

theorem bc_not_normalizes (h121 : Prop121_corStatement) (h : Cex127 G m p B M E A N D)
    (hs : Setup2 M A N p S F K) (hFne : F ≠ A)
    (hweak : ∀ B' : Subgroup (MulAut (barOf p K)), IsElemAbelian p B' → p ^ 2 ≤ Nat.card B' →
      IsWeaklyLocallyOTwoBalanced p 2 B') :
    ¬ A ≤ Subgroup.normalizer (K : Set G) := by
  intro hAK
  have hp := prime_of h
  have hnb := not_weakly_balanced h121 h hs.hS hs.hFdef hFne hs.hK (hs.S_le_normalizer hp h) hAK
    hs.hFc hs.hr hs.hKc hs.hW
  refine hnb (hweak _ (isElemAbelian_autBar hAK (A_el h)) ?_)
  have hFA := hs.F_le_A
  calc p ^ 2 ≤ p ^ CFSG.Open.pRank p F := Nat.pow_le_pow_right hp.pos hs.hr
    _ = Nat.card F := (card_eq_pow_pRank hp ((A_el h).mono hFA)).symm
    _ = Nat.card (autBar p F K) := (card_autBar p hs.hFK hs.hFc).symm
    _ ≤ Nat.card (autBar p A K) := Subgroup.card_le_of_le (autBar_mono p hFA)

theorem bc_inf_normalizer (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hA3 : CFSG.Open.pRank p A = 3) (hr2 : CFSG.Open.pRank p F = 2)
    (hAK : ¬ A ≤ Subgroup.normalizer (K : Set G)) :
    A ⊓ Subgroup.normalizer (K : Set G) = F := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hFA := hs.F_le_A
  have hAcard := card_eq_pow_pRank hp (A_el h)
  have hFcard := card_eq_pow_pRank hp ((A_el h).mono hFA)
  rw [hA3] at hAcard
  rw [hr2] at hFcard
  set C := A ⊓ Subgroup.normalizer (K : Set G) with hC
  have hFC : F ≤ C := le_inf hFA hs.hFK
  have hCA : C ≤ A := inf_le_left
  have h1 : Nat.card C ∣ p ^ 3 := hAcard ▸ Subgroup.card_dvd_of_le hCA
  have h2 : p ^ 2 ∣ Nat.card C := hFcard ▸ Subgroup.card_dvd_of_le hFC
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow hp).1 h1
  have hi2 : 2 ≤ i := by
    have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 (hCi ▸ h2)
    exact this
  interval_cases i
  · exact (Subgroup.eq_of_le_of_card_ge hFC (by rw [hCi, hFcard])).symm
  · exfalso
    apply hAK
    have : C = A := Subgroup.eq_of_le_of_card_ge hCA (by rw [hCi, hAcard])
    rw [← this]
    exact inf_le_right

theorem bc_props_of_not_mem (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hA3 : CFSG.Open.pRank p A = 3) (hr2 : CFSG.Open.pRank p F = 2)
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F) {a : G} (haA : a ∈ A)
    (haK : a ∉ Subgroup.normalizer (K : Set G)) :
    a ^ p = 1 ∧ A = F ⊔ Subgroup.zpowers a ∧ F ⊓ Subgroup.zpowers a = ⊥ ∧
      ∀ n : ℕ, 0 < n → n < p → a ^ n ∉ Subgroup.normalizer (K : Set G) := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hFA := hs.F_le_A
  have hAcard := card_eq_pow_pRank hp (A_el h)
  have hFcard := card_eq_pow_pRank hp ((A_el h).mono hFA)
  rw [hA3] at hAcard
  rw [hr2] at hFcard
  have haF : a ∉ F := fun haF => haK (hs.hFK haF)
  have hap : a ^ p = 1 := (A_el h).2 a haA
  have ha1 : a ≠ 1 := fun h1 => haK (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf a = p := orderOf_eq_prime hap ha1
  refine ⟨hap, ?_, ?_, ?_⟩
  ·
    have hle : F ⊔ Subgroup.zpowers a ≤ A :=
      sup_le hFA (Subgroup.zpowers_le.2 haA)
    have h1 : Nat.card (F ⊔ Subgroup.zpowers a : Subgroup G) ∣ p ^ 3 := hAcard ▸ Subgroup.card_dvd_of_le hle
    have h2 : p ^ 2 ∣ Nat.card (F ⊔ Subgroup.zpowers a : Subgroup G) :=
      hFcard ▸ Subgroup.card_dvd_of_le le_sup_left
    obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow hp).1 h1
    have hi2 : 2 ≤ i := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 (hCi ▸ h2)
    interval_cases i
    · exfalso
      have : F = F ⊔ Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hCi, hFcard])
      exact haF (this ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hCi, hAcard])).symm
  ·
    have hcardz : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
    haveI : Fact (Nat.card (Subgroup.zpowers a)).Prime := ⟨hcardz ▸ hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((F ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a)) with h1 | h1
    · ext x
      constructor
      · intro hx
        have : (⟨x, hx.2⟩ : Subgroup.zpowers a) ∈ (F ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a) :=
          Subgroup.mem_subgroupOf.2 hx
        rw [h1, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      · intro hx
        rw [Subgroup.mem_bot] at hx
        rw [hx]; exact Subgroup.one_mem _
    · exfalso
      have : (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) ∈
          (F ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a) := by rw [h1]; exact Subgroup.mem_top _
      exact haF (Subgroup.mem_subgroupOf.1 this).1
  ·
    intro n hn0 hnp hmem
    have hnA : a ^ n ∈ A ⊓ Subgroup.normalizer (K : Set G) := ⟨A.pow_mem haA n, hmem⟩
    rw [hCF] at hnA
    obtain ⟨n', hn'⟩ := exists_pow_eq_self_of_coprime (x := a) (n := n) (by
      rw [hord]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hn0 hnp)).symm)
    exact haF (hn' ▸ F.pow_mem hnA n')

theorem mem_centBar_of_barX_centralizes {p : ℕ} (hp : p.Prime) {N K : Subgroup G}
    (hK : GLAPComponent p N K) {x : G} (hxN : x ∈ N)
    (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hc : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ ∈
      Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N))) :
    x ∈ centBar p ⊤ K := by
  rw [mem_centBar_top_iff hxK]
  refine MulEquiv.ext fun z => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
  show QuotientGroup.mk (K.normalizerMonoidHom ⟨x, hxK⟩ k) = QuotientGroup.mk k
  rw [QuotientGroup.eq]
  have hkN : (k : G) ∈ N := hK.1 k.2
  have hcomm := (Subgroup.mem_centralizer_iff.1 hc _
    ⟨⟨k, hkN⟩, (Subgroup.mem_subgroupOf).2 k.2, rfl⟩).symm
  have hmemN : (K.normalizerMonoidHom ⟨x, hxK⟩ k : G)⁻¹ * (k : G) ∈ GLAPPrimeCoreOf p N := by
    have hxkN : (K.normalizerMonoidHom ⟨x, hxK⟩ k : G) ∈ N := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact N.mul_mem (N.mul_mem hxN hkN) (N.inv_mem hxN)
    refine ⟨⟨(K.normalizerMonoidHom ⟨x, hxK⟩ k : G)⁻¹ * (k : G),
      N.mul_mem (N.inv_mem hxkN) hkN⟩, ?_, rfl⟩
    refine (QuotientGroup.eq_one_iff _).1 ?_
    show QuotientGroup.mk' (GLAPPrimeCore p ↥N) _ = 1
    have e : (⟨(K.normalizerMonoidHom ⟨x, hxK⟩ k : G)⁻¹ * (k : G),
        N.mul_mem (N.inv_mem hxkN) hkN⟩ : ↥N) =
        (⟨x, hxN⟩ * ⟨k, hkN⟩ * ⟨x, hxN⟩⁻¹)⁻¹ * ⟨k, hkN⟩ := by
      apply Subtype.ext
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [e]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hmemK : (K.normalizerMonoidHom ⟨x, hxK⟩ k : G)⁻¹ * (k : G) ∈ GLAPPrimeCoreOf p K := by
    refine glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1 ▸ ⟨?_, hmemN⟩
    exact K.mul_mem (K.inv_mem (K.normalizerMonoidHom ⟨x, hxK⟩ k).2) k.2
  obtain ⟨y, hy, hyeq⟩ := hmemK
  have : y = (K.normalizerMonoidHom ⟨x, hxK⟩ k)⁻¹ * k := Subtype.ext hyeq
  rwa [this] at hy

theorem barX_A_isSCp (h : Cex127 G m p B M E A N D) : IsSCp p ⊤ (barX p N A) := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : IsSCp p ⊤ A := (lemma104_ii_holds h.toSec11.toSec10Fails h.pair).2
  exact isSCp_map_quotient (GLAPPrimeCore p ↥N)
    ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card)
    (isSCp_subgroupOf hA (A_le_N h))

theorem bc_Ystruct (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F) :
    (∀ K' : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N), IsComponentOf K' ⊤ →
        ∃ g ∈ barX p N A, K' = GLBConj g (barX p N K)) ∧
      CFSG.pCore p (↥N ⧸ GLAPPrimeCore p ↥N) = ⊥ ∧
      Subgroup.centralizer ((⨆ g ∈ barX p N A, GLBConj g (barX p N K) :
        Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) : Set (↥N ⧸ GLAPPrimeCore p ↥N)) = ⊥ := by
  have hp := prime_of h
  refine Lemma129Y.scp_centralizer_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp)
    (barX_A_isSCp h) hs.hK.2.2.1 ?_
  intro x hx hxc
  obtain ⟨⟨x₀, hx₀N⟩, hx₀A, rfl⟩ := hx
  have hx₀A' : x₀ ∈ A := (Subgroup.mem_subgroupOf).1 hx₀A
  have hK₁le : barX p N K ≤ (⨆ g ∈ barX p N A, GLBConj g (barX p N K) :
      Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    refine le_iSup₂_of_le (1 : ↥N ⧸ GLAPPrimeCore p ↥N) (Subgroup.one_mem _) ?_
    rw [gLBConj_one]
  have hcent : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x₀, hx₀N⟩ ∈
      Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => (hxc y (hK₁le hy)).symm
  have hxK : x₀ ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_of_barX_normalizes hp le_rfl hs.hK hx₀N (Subgroup.le_normalizer hx₀N)
      (Subgroup.centralizer_le_normalizer _ hcent)
  have hxF : x₀ ∈ F := hCF ▸ ⟨hx₀A', hxK⟩
  have hxcB : x₀ ∈ centBar p ⊤ K := mem_centBar_of_barX_centralizes hp hs.hK hx₀N hxK hcent
  have : x₀ ∈ F ⊓ centBar p ⊤ K := ⟨hxF, hxcB⟩
  rw [hs.hFc, Subgroup.mem_bot] at this
  have h1 : (⟨x₀, hx₀N⟩ : ↥N) = 1 := Subtype.ext this
  rw [h1, map_one]

end Basic

section GToY

variable {G : Type} [Group G] [Finite G]

theorem quotEquivBarX_mk {p : ℕ} (hp : p.Prime) {C L : Subgroup G} (hLC : L ≤ C)
    (hsn : IsSubnormal L C) (t : ↥L) :
    ((quotEquivBarX hp hLC hsn (QuotientGroup.mk t) : ↥(barX p C L)) :
      ↥C ⧸ GLAPPrimeCore p ↥C) = QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨t, hLC t.2⟩ := rfl

theorem mem_normalizer_of_mk {p : ℕ} (hp : p.Prime) {N K : Subgroup G} (hK : GLAPComponent p N K)
    {x : G} (hxN : x ∈ N)
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ ∈
      Subgroup.normalizer ((barX p N K : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
        Set (↥N ⧸ GLAPPrimeCore p ↥N))) :
    x ∈ Subgroup.normalizer (K : Set G) :=
  mem_normalizer_of_barX_normalizes hp le_rfl hK hxN (Subgroup.le_normalizer hxN) h

theorem mk_pow_eq_one {p : ℕ} {N : Subgroup G} {a : G} (haN : a ∈ N) (hap : a ^ p = 1) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) ^ p = 1 := by
  rw [← map_pow]
  have : (⟨a, haN⟩ : ↥N) ^ p = 1 := Subtype.ext hap
  rw [this, map_one]

theorem mk_pow {p : ℕ} {N : Subgroup G} {a : G} (haN : a ∈ N) (n : ℕ) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a ^ n, N.pow_mem haN n⟩ =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) ^ n := by
  rw [← map_pow]; rfl

theorem bc_hcap {p : ℕ} (hp : p.Prime) {N K : Subgroup G} (hK : GLAPComponent p N K) {a : G}
    (haN : a ∈ N)
    (hcapG : ∀ n : ℕ, 0 < n → n < p → a ^ n ∉ Subgroup.normalizer (K : Set G)) :
    ∀ n : ℕ, 0 < n → n < p → (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) ^ n ∉
      Subgroup.normalizer ((barX p N K : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
        Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
  intro n hn0 hnp hmem
  apply hcapG n hn0 hnp
  refine mem_normalizer_of_mk hp hK (N.pow_mem haN n) ?_
  rw [mk_pow haN n]
  exact hmem

theorem quotEquivBarX_barAut {p : ℕ} (hp : p.Prime) {N K : Subgroup G} (hK : GLAPComponent p N K)
    {f : G} (hfN : f ∈ N) (hfK : f ∈ Subgroup.normalizer (K : Set G)) (y : barOf p K) :
    ((quotEquivBarX hp hK.1 hK.2.1 (barAut p K ⟨f, hfK⟩ y) : ↥(barX p N K)) :
        ↥N ⧸ GLAPPrimeCore p ↥N) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f, hfN⟩ *
        ((quotEquivBarX hp hK.1 hK.2.1 y : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f, hfN⟩)⁻¹ := by
  induction y using QuotientGroup.induction_on with
  | H t =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, quotEquivBarX_mk, quotEquivBarX_mk]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem bc_inner {p : ℕ} (hp : p.Prime) {N K F : Subgroup G} (hK : GLAPComponent p N K)
    (hFN : F ≤ N) (hFK : F ≤ Subgroup.normalizer (K : Set G))
    (hinn : autBar p F K ≤ innerAut (barOf p K)) :
    ∀ f ∈ barX p N F, ∃ k ∈ barX p N K, ∀ y ∈ barX p N K, f * y * f⁻¹ = k * y * k⁻¹ := by
  rintro _ ⟨⟨f, hfN⟩, hfF, rfl⟩
  have hfF' : f ∈ F := (Subgroup.mem_subgroupOf).1 hfF
  have hmem := barAut_mem_autBar (p := p) (X := F) (K := K) hfF' (hFK hfF')
  obtain ⟨k', hk'⟩ := hinn hmem
  let e := quotEquivBarX hp hK.1 hK.2.1
  refine ⟨(e k' : ↥N ⧸ GLAPPrimeCore p ↥N), (e k').2, fun y hy => ?_⟩
  obtain ⟨y', hy'⟩ := e.surjective ⟨y, hy⟩
  have h1 := quotEquivBarX_barAut hp hK hfN (hFK hfF') y'
  have h2 : barAut p K ⟨f, hFK hfF'⟩ y' = k' * y' * k'⁻¹ := by
    rw [← hk']; rfl
  rw [h2] at h1
  have h3 : ((e (k' * y' * k'⁻¹) : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N) =
      (e k' : ↥N ⧸ GLAPPrimeCore p ↥N) * (e y' : ↥N ⧸ GLAPPrimeCore p ↥N) *
        (e k' : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹ := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h3] at h1
  have h4 : ((e y' : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N) = y := by rw [hy']
  rw [h4] at h1
  exact h1.symm

end GToY

section Card

variable {G : Type} [Group G] [Finite G]

theorem card_sup_of_commute_disjoint {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a)
    (hd : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hcomm : ∀ (m : ↥H) (n : ↥K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hc m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hcomm) :=
    (MonoidHom.noncommCoprod_injective _ _ _).2 ⟨H.subtype_injective, K.subtype_injective, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype]
      exact disjoint_iff.2 hd⟩
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype hcomm).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(H ⊔ K)
      = Nat.card (MonoidHom.noncommCoprod H.subtype K.subtype hcomm).range := by rw [hrange]
    _ = Nat.card (↥H × ↥K) := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

end Card

section A0Wrap

variable {G : Type} [Group G] [Finite G]

section A0

variable {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem hcap_of_inf_normalizer (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F) {a : G} (haA : a ∈ A)
    (haK : a ∉ Subgroup.normalizer (K : Set G)) :
    ∀ n : ℕ, 0 < n → n < p → a ^ n ∉ Subgroup.normalizer (K : Set G) := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have haF : a ∉ F := fun haF => haK (hs.hFK haF)
  have hap : a ^ p = 1 := (A_el h).2 a haA
  have ha1 : a ≠ 1 := fun h1 => haK (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf a = p := orderOf_eq_prime hap ha1
  intro n hn0 hnp hmem
  have hnA : a ^ n ∈ A ⊓ Subgroup.normalizer (K : Set G) := ⟨A.pow_mem haA n, hmem⟩
  rw [hCF] at hnA
  obtain ⟨n', hn'⟩ := exists_pow_eq_self_of_coprime (x := a) (n := n) (by
    rw [hord]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hn0 hnp)).symm)
  exact haF (hn' ▸ F.pow_mem hnA n')

theorem exists_a_in_A0 (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hAr : CFSG.Open.pRank p A = CFSG.Open.pRank p F + 1)
    (hAK : ¬ A ≤ Subgroup.normalizer (K : Set G))
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F)
    (hFinner : ∀ f ∈ barX p N F, ∃ k ∈ barX p N K, ∀ y ∈ barX p N K,
      f * y * f⁻¹ = k * y * k⁻¹) :
    ∃ a ∈ E ⊓ A, a ∉ Subgroup.normalizer (K : Set G) := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀A, ha₀K⟩ := Set.not_subset.1 hAK
  have hcapG := hcap_of_inf_normalizer h hs hCF ha₀A ha₀K
  have hAN := A_le_N h
  have hFA := hs.F_le_A
  have hFN : F ≤ N := hFA.trans hAN
  have ha₀N : a₀ ∈ N := hAN ha₀A
  obtain ⟨-, -, hC⟩ := bc_Ystruct h hs hCF
  have hKb : IsComponentOf (barX p N K) ⊤ := hs.hK.2.2.1
  have hcenter := center_trivial_of_centralizer_bot hKb hC
  have hcommY := kconj_comm hKb (bc_hcap hp hs.hK ha₀N hcapG)
  have hcomm01 : ∀ x ∈ barX p N K,
      ∀ y ∈ Lemma129W.kconj (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K) 1,
        x * y = y * x := by
    intro x hx y hy
    have hx0 : x ∈ Lemma129W.kconj (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)
        (barX p N K) ((⟨0, hp.pos⟩ : Fin p) : ℕ) :=
      Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
    refine hcommY ⟨0, hp.pos⟩ ⟨1, hp.one_lt⟩ (fun heq => ?_) x hx0 y hy
    have := congrArg Fin.val heq
    simp at this
  have hFa : ∀ f ∈ barX p N F, f * QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ * f := by
    rintro _ ⟨⟨f, hfN⟩, hfF, rfl⟩
    have hfF' : f ∈ F := (Subgroup.mem_subgroupOf).1 hfF
    have hc := elemAbelian_comm (A_el h) (hFA hfF') ha₀A
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  have hFp : IsPGroup p F := ((A_el h).mono hFA).isPGroup
  have hFel : IsElemAbelian p (barX p N F) := elemAbelian_barX hp hFN ((A_el h).mono hFA)
  have hFfaith : ∀ f ∈ barX p N F, (∀ y ∈ barX p N K, f * y = y * f) → f = 1 := by
    rintro _ ⟨⟨f, hfN⟩, hfF, rfl⟩ hc
    have hfF' : f ∈ F := (Subgroup.mem_subgroupOf).1 hfF
    have hcent : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f, hfN⟩ ∈
        Subgroup.centralizer ((barX p N K : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
          Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => (hc y hy).symm
    have hfc : f ∈ centBar p ⊤ K :=
      mem_centBar_of_barX_centralizes hp hs.hK hfN (hs.hFK hfF') hcent
    have hf1 : f ∈ F ⊓ centBar p ⊤ K := ⟨hfF', hfc⟩
    rw [hs.hFc, Subgroup.mem_bot] at hf1
    have : (⟨f, hfN⟩ : ↥N) = 1 := Subtype.ext hf1
    rw [this, map_one]
  obtain ⟨X, hXel, hXcard, hXK, hXF⟩ := Lemma129W2.exists_centralizing_pair (p := p)
    (barX p N K) (barX p N F) (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) hcenter hcomm01 hFa
    hFel hFinner hFfaith
  have hA0N : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hA0el : IsElemAbelian p (E ⊓ A) := (A_el h).mono inf_le_right
  have hA0F : E ⊓ A ≤ F := fun x hx => by
    rw [← hCF]
    exact ⟨hx.2, hcon x hx⟩
  have hXcent : X ≤ Subgroup.centralizer ((barX p N (E ⊓ A) : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
      Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hXF x hx z (barX_mono129 hA0F hz)).symm
  rw [centralizer_barX_eq hp hA0N hA0el.isPGroup] at hXcent
  obtain ⟨P, hPle, hPp, hPbar⟩ := Lemma116.exists_lift hp
    (inf_le_left : N ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤ N) hXcent hXel.isPGroup
  have hPN : P ≤ N := hPle.trans inf_le_left
  have hPc : P ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := hPle.trans inf_le_right
  have hPel : IsElemAbelian p P := Lemma116.elemAbelian_of_barX_elemAbelian hp hPN hPp (hPbar ▸ hXel)
  have hPcard : Nat.card P = p ^ CFSG.Open.pRank p F := by
    have h1 := card_barX_of_isPGroup hp hPN hPp
    have h2 := card_barX_of_isPGroup hp hFN hFp
    rw [hPbar, hXcard, h2] at h1
    rw [← h1, card_eq_pow_pRank hp ((A_el h).mono hFA)]
  have hP2 : 2 ≤ CFSG.Open.pRank p P :=
    hs.hr.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hPel hPcard)
  have hWcomm : ∀ x ∈ E ⊓ A, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hPc hy) x hx
  have hWel : IsElemAbelian p ((E ⊓ A) ⊔ P) := hA0el.sup_of_commute hPel hWcomm
  have hdisj : (E ⊓ A) ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA0, hxP⟩
    have hxN : x ∈ N := hPN hxP
    have hxbar : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ ∈ X :=
      hPbar ▸ ⟨⟨x, hxN⟩, (Subgroup.mem_subgroupOf).2 hxP, rfl⟩
    have hxF : x ∈ F := hA0F hxA0
    have hcent : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ ∈
        Subgroup.centralizer ((barX p N K : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
          Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => (hXK _ hxbar y hy).symm
    have hfc : x ∈ centBar p ⊤ K :=
      mem_centBar_of_barX_centralizes hp hs.hK hxN (hs.hFK hxF) hcent
    have hx1 : x ∈ F ⊓ centBar p ⊤ K := ⟨hxF, hfc⟩
    rw [hs.hFc] at hx1
    exact hx1
  have hrankW : CFSG.Open.pRank p F + 2 ≤ CFSG.Open.pRank p ((E ⊓ A) ⊔ P) := by
    have h1 := card_eq_pow_pRank hp hWel
    have h2 : p ^ (CFSG.Open.pRank p F + 2) ≤ Nat.card ↥((E ⊓ A) ⊔ P) := by
      rw [card_sup_of_commute_disjoint hWcomm hdisj, hPcard, card_eq_pow_pRank hp hA0el]
      calc p ^ (CFSG.Open.pRank p F + 2) = p ^ 2 * p ^ CFSG.Open.pRank p F := by ring
        _ ≤ p ^ CFSG.Open.pRank p (E ⊓ A) * p ^ CFSG.Open.pRank p F :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (two_le_rank_inf h))
    rw [h1] at h2
    exact (pow_le_pow_iff_right₀ hp.one_lt).1 h2
  have hnorm : Subgroup.normalizer (P : Set G) ≤ M :=
    normalizer_le_of_rank_gt h hWel le_sup_left (by omega) le_sup_right hP2
  apply hs.hnc
  have h1 : barX p N K ≤ Subgroup.centralizer ((barX p N P : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
      Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    rw [hPbar]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hXK x hx k hk
  rw [centralizer_barX_eq hp hPN hPp] at h1
  refine h1.trans (barX_mono129 fun x hx => hnorm ?_)
  exact Subgroup.centralizer_le_normalizer _ hx.2

theorem bc_exists_a_in_A0 (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hA3 : CFSG.Open.pRank p A = 3) (hr2 : CFSG.Open.pRank p F = 2)
    (hAK : ¬ A ≤ Subgroup.normalizer (K : Set G))
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F)
    (hinn : autBar p F K ≤ innerAut (barOf p K)) :
    ∃ a ∈ E ⊓ A, a ∉ Subgroup.normalizer (K : Set G) :=
  exists_a_in_A0 h hs (by omega) hAK hCF
    (bc_inner (prime_of h) hs.hK (hs.F_le_A.trans (A_le_N h)) hs.hFK hinn)

end A0

end A0Wrap

section Decomp

variable {G : Type} [Group G]

theorem exists_mul_pow_of_mem_sup {F : Subgroup G} {a : G} {p : ℕ} (hp : 0 < p) (ha : a ^ p = 1)
    (hFa : ∀ f ∈ F, f * a = a * f) {x : G} (hx : x ∈ F ⊔ Subgroup.zpowers a) :
    ∃ f ∈ F, ∃ j : ℕ, x = f * a ^ j := by
  have hcomm : ∀ f ∈ F, ∀ i : ℕ, f * a ^ i = a ^ i * f := fun f hf i =>
    (Commute.pow_right (show Commute f a from hFa f hf) i).eq
  have hinv : ∀ j : ℕ, (a ^ j)⁻¹ = a ^ ((p - 1) * j) := by
    intro j
    have h1 : a ^ j * a ^ ((p - 1) * j) = 1 := by
      rw [← pow_add]
      have : j + (p - 1) * j = p * j := by
        have : p = (p - 1) + 1 := by omega
        conv_rhs => rw [this]
        ring
      rw [this, pow_mul, ha, one_pow]
    exact inv_eq_of_mul_eq_one_right h1
  let H : Subgroup G :=
    { carrier := {x | ∃ f ∈ F, ∃ j : ℕ, x = f * a ^ j}
      one_mem' := ⟨1, F.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, i, rfl⟩ ⟨f', hf', j, rfl⟩
        refine ⟨f * f', F.mul_mem hf hf', i + j, ?_⟩
        calc f * a ^ i * (f' * a ^ j) = f * (a ^ i * f') * a ^ j := by group
          _ = f * (f' * a ^ i) * a ^ j := by rw [← hcomm f' hf' i]
          _ = f * f' * a ^ (i + j) := by rw [pow_add]; group
      inv_mem' := by
        rintro _ ⟨f, hf, j, rfl⟩
        refine ⟨f⁻¹, F.inv_mem hf, (p - 1) * j, ?_⟩
        rw [mul_inv_rev, hinv j]
        have := hcomm f⁻¹ (F.inv_mem hf) ((p - 1) * j)
        rw [← this] }
  have hFH : F ≤ H := fun f hf => ⟨f, hf, 0, by simp⟩
  have haH : a ∈ H := ⟨1, F.one_mem, 1, by simp⟩
  exact (sup_le hFH (Subgroup.zpowers_le.2 haH)) hx

end Decomp

section YKstar

variable {Y : Type} [Group Y] [Finite Y]

theorem inv_pow_eq_pow {a : Y} {p : ℕ} (hp : 0 < p) (ha : a ^ p = 1) (j : ℕ) :
    (a ^ j)⁻¹ = a ^ ((p - 1) * j) := by
  have h1 : a ^ j * a ^ ((p - 1) * j) = 1 := by
    rw [← pow_add]
    have : j + (p - 1) * j = p * j := by
      have : p = (p - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    rw [this, pow_mul, ha, one_pow]
  exact inv_eq_of_mul_eq_one_right h1

theorem gLBConj_pow_le_kstar {p : ℕ} (hp : 0 < p) {K : Subgroup Y} {a : Y} (ha : a ^ p = 1)
    (j : ℕ) : GLBConj (a ^ j) K ≤ Lemma129W.kstar p a K := by
  have hip : ((p - 1) * j) % p < p := Nat.mod_lt _ hp
  have h1 : (a ^ (((p - 1) * j) % p))⁻¹ = a ^ j := by
    rw [← pow_eq_pow_mod _ ha, ← inv_pow_eq_pow hp ha j, inv_inv]
  have hle := le_iSup (fun i : Fin p => Lemma129W.kconj a K i) ⟨((p - 1) * j) % p, hip⟩
  refine le_trans ?_ hle
  show GLBConj (a ^ j) K ≤ Lemma129W.kconj a K (((p - 1) * j) % p)
  rw [kconj_eq_gLBConj, h1]

end YKstar

section BarXGen

variable {G : Type} [Group G]

theorem barX_iSup_eq {p : ℕ} {C : Subgroup G} {ι : Sort*} (X : ι → Subgroup G)
    (hX : ∀ i, X i ≤ C) : barX p C (⨆ i, X i) = ⨆ i, barX p C (X i) := by
  have h1 : (⨆ i, X i).subgroupOf C = ⨆ i, (X i).subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_iSup]
    simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
    rw [inf_eq_right.2 (iSup_le hX)]
    exact iSup_congr fun i => (inf_eq_right.2 (hX i)).symm
  unfold barX
  rw [h1, Subgroup.map_iSup]

theorem barX_zpowers {p : ℕ} {N : Subgroup G} {a : G} (haN : a ∈ N) :
    barX p N (Subgroup.zpowers a) =
      Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) := by
  ext x
  constructor
  · rintro ⟨⟨y, hyN⟩, hy, rfl⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_subgroupOf).1 hy)
    refine Subgroup.mem_zpowers_iff.2 ⟨z, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext hz
  · intro hx
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨⟨a, haN⟩ ^ z, ?_, by rw [map_zpow]⟩
    exact (Subgroup.mem_subgroupOf).2 (Subgroup.zpow_mem_zpowers a z)

end BarXGen

section Transport

theorem isLpType_of_mulEquiv {p Q : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLpType p Q X) : IsLpType p Q Y := by
  obtain ⟨F, hF, hfin, hc, ⟨e'⟩⟩ := h
  exact ⟨F, hF, hfin, hc, ⟨e.symm.trans e'⟩⟩

theorem isSporType_of_mulEquiv {name : TauCeti.SporadicName} {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsSporType name X) : IsSporType name Y := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

theorem isLpType_of_center_bot {p Q : ℕ} {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    (h : IsLpType p Q (X ⧸ Subgroup.center X)) : IsLpType p Q X :=
  isLpType_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) h

end Transport

section CenterBot

variable {G : Type} [Group G] [Finite G]

theorem center_bot_barOf {p : ℕ} (hp : p.Prime) {N K : Subgroup G} (hK : GLAPComponent p N K)
    (hcenter : ∀ z ∈ barX p N K, (∀ y ∈ barX p N K, z * y = y * z) → z = 1) :
    Subgroup.center (barOf p K) = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  let e := quotEquivBarX hp hK.1 hK.2.1
  have hz : ((e u : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N) = 1 := by
    refine hcenter _ (e u).2 fun y hy => ?_
    obtain ⟨y', hy'⟩ := e.surjective ⟨y, hy⟩
    have h1 : e (u * y') = e (y' * u) := by rw [Subgroup.mem_center_iff.1 hu y']
    rw [map_mul, map_mul, hy'] at h1
    exact congrArg Subtype.val h1
  have : e u = 1 := Subtype.ext hz
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [this, map_one])

end CenterBot

section BarXSup

variable {G : Type} [Group G]

theorem barX_sup_eq {p : ℕ} {C X Y : Subgroup G} (hX : X ≤ C) (hY : Y ≤ C) :
    barX p C (X ⊔ Y) = barX p C X ⊔ barX p C Y := by
  unfold barX
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

end BarXSup

section Assembly

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem mk_comm_of_comm {p : ℕ} {N : Subgroup G} {x a : G} (hxN : x ∈ N) (haN : a ∈ N)
    (h : x * a = a * x) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem bc_conj_le_kstar (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    {a : G} (haA : a ∈ A) (hap : a ^ p = 1) (hAeq : A = F ⊔ Subgroup.zpowers a)
    {x : G} (hx : x ∈ A) :
    GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, A_le_N h hx⟩) (barX p N K) ≤
      Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, A_le_N h haA⟩)
        (barX p N K) := by
  have hp := prime_of h
  have hAN := A_le_N h
  have hFa : ∀ f ∈ F, f * a = a * f := fun f hf =>
    elemAbelian_comm (A_el h) (hs.F_le_A hf) haA
  obtain ⟨f, hfF, j, rfl⟩ := exists_mul_pow_of_mem_sup hp.pos hap hFa (hAeq ▸ hx)
  have hxN : f * a ^ j ∈ N := hAN hx
  rw [← barX_gLBConj_eq p hxN K]
  have hconj : GLBConj (f * a ^ j) K = GLBConj (a ^ j) K := by
    rw [← gLBConj_gLBConj (a ^ j) f K, gLBConj_eq_of_mem_normalizer (hs.hFK hfF)]
  rw [hconj]
  have haN : a ^ j ∈ N := N.pow_mem (hAN haA) j
  rw [barX_gLBConj_eq p haN K, mk_pow (hAN haA) j]
  exact gLBConj_pow_le_kstar hp.pos (mk_pow_eq_one (hAN haA) hap) j

theorem bc_centralizer_kstar (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F)
    {a : G} (haA : a ∈ A) (hap : a ^ p = 1) (hAeq : A = F ⊔ Subgroup.zpowers a) :
    Subgroup.centralizer ((Lemma129W.kstar p
      (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, A_le_N h haA⟩) (barX p N K) :
        Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) : Set (↥N ⧸ GLAPPrimeCore p ↥N)) = ⊥ := by
  obtain ⟨-, -, hC⟩ := bc_Ystruct h hs hCF
  have hsub : ((⨆ g ∈ barX p N A, GLBConj g (barX p N K) : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
      Set (↥N ⧸ GLAPPrimeCore p ↥N)) ⊆ (Lemma129W.kstar p
      (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, A_le_N h haA⟩) (barX p N K) :
        Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    refine SetLike.coe_subset_coe.2 (iSup₂_le fun g hg => ?_)
    obtain ⟨⟨x, hxN⟩, hxA, rfl⟩ := hg
    exact bc_conj_le_kstar h hs haA hap hAeq ((Subgroup.mem_subgroupOf).1 hxA)
  exact eq_bot_iff.2 ((Subgroup.centralizer_le hsub).trans hC.le)

theorem bc_barX_layer_eq (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    {a : G} (haA : a ∈ A) (hap : a ^ p = 1) (hAeq : A = F ⊔ Subgroup.zpowers a) :
    barX p N (⨆ g ∈ A, GLBConj g K) =
      Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, A_le_N h haA⟩)
        (barX p N K) := by
  have hAN := A_le_N h
  have hKN : K ≤ N := hs.hK.1
  have hle : ∀ g ∈ A, GLBConj g K ≤ N := fun g hg => by
    have := gLBConj_mono g hKN
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hAN hg))] at this
  apply le_antisymm
  · rw [barX_iSup_eq (fun g => ⨆ (_ : g ∈ A), GLBConj g K) (fun g => iSup_le fun hg => hle g hg)]
    refine iSup_le fun g => ?_
    rw [barX_iSup_eq (fun _ : g ∈ A => GLBConj g K) (fun hg => hle g hg)]
    refine iSup_le fun hg => ?_
    rw [barX_gLBConj_eq p (hAN hg) K]
    exact bc_conj_le_kstar h hs haA hap hAeq hg
  · refine iSup_le fun i => ?_
    have hai : (a ^ (i : ℕ))⁻¹ ∈ A := A.inv_mem (A.pow_mem haA _)
    have haiN : (a ^ (i : ℕ))⁻¹ ∈ N := hAN hai
    have e2 : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨(a ^ (i : ℕ))⁻¹, haiN⟩ =
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, hAN haA⟩) ^ (i : ℕ))⁻¹ := by
      rw [← mk_pow (hAN haA) i, ← map_inv]
      rfl
    have e1 : Lemma129W.kconj (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, hAN haA⟩) (barX p N K) i =
        barX p N (GLBConj (a ^ (i : ℕ))⁻¹ K) := by
      rw [kconj_eq_gLBConj, barX_gLBConj_eq p haiN K, e2]
    rw [e1]
    exact barX_mono129 (le_iSup₂_of_le _ hai le_rfl)

theorem bc_barX_F_le_kstar (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F)
    {a : G} (haA : a ∈ A) (hap : a ^ p = 1) (hAeq : A = F ⊔ Subgroup.zpowers a)
    (hcapG : ∀ n : ℕ, 0 < n → n < p → a ^ n ∉ Subgroup.normalizer (K : Set G))
    (hinn : autBar p F K ≤ innerAut (barOf p K)) :
    barX p N F ≤ Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, A_le_N h haA⟩)
      (barX p N K) := by
  have hp := prime_of h
  have hAN := A_le_N h
  have hFN : F ≤ N := hs.F_le_A.trans hAN
  have hKb : IsComponentOf (barX p N K) ⊤ := hs.hK.2.2.1
  rintro _ ⟨⟨f, hfN⟩, hfF, rfl⟩
  have hfF' : f ∈ F := (Subgroup.mem_subgroupOf).1 hfF
  obtain ⟨k, hk, hgk⟩ := bc_inner hp hs.hK hFN hs.hFK hinn _ ⟨⟨f, hfN⟩, hfF, rfl⟩
  exact Lemma129W2.mem_kstar_of_inner (barX p N K) _
    (kconj_comm hKb (bc_hcap hp hs.hK (hAN haA) hcapG))
    (bc_centralizer_kstar h hs hCF haA hap hAeq)
    (mk_comm_of_comm hfN (hAN haA) (elemAbelian_comm (A_el h) (hs.F_le_A hfF') haA)) hk hgk

theorem bc_layer (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F) :
    GLAPLayer p N = ⨆ g ∈ A, GLBConj g K := by
  have hAN := A_le_N h
  obtain ⟨hcomp, -, -⟩ := bc_Ystruct h hs hCF
  have hconjcomp : ∀ g ∈ A, GLAPComponent p N (GLBConj g K) := fun g hg => by
    have := glaPComponent_gLBConj hs.hK g
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hAN hg))] at this
  unfold GLAPLayer
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    have hL' : GLAPComponent p N L := hL
    have hLc : IsComponentOf (barX p N L) ⊤ := hL'.2.2.1
    obtain ⟨g', hg', hLg⟩ := hcomp (barX p N L) hLc
    obtain ⟨⟨g, hgN⟩, hgA, rfl⟩ := hg'
    have hgA' : g ∈ A := (Subgroup.mem_subgroupOf).1 hgA
    have hL'' : L = GLBConj g K := by
      refine glaPComponent_unique hL' (hconjcomp g hgA') ?_
      rw [barX_gLBConj_eq p hgN K]
      exact hLg
    rw [hL'']
    exact le_iSup₂_of_le g hgA' le_rfl
  · exact iSup₂_le fun g hg => le_sSup (hconjcomp g hg)

theorem lemma129_bc (h121 : Prop121_corStatement) (h : Cex127 G m p B M E A N D)
    (hs : Setup2 M A N p S F K) (hr2 : CFSG.Open.pRank p F = 2)
    (hsl : Spor1916 p 2 (autBar p F K) ∨ Lie1916 p 2 (autBar p F K)) :
    Lemma129Common p M E A N K ∧
      (((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨ (p = 5 ∧ IsSporType .Fi22 (barOf p K))) ∧
        Lemma129IvBData p N K E A) := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hinn : autBar p F K ≤ innerAut (barOf p K) := by
    rcases hsl with ⟨-, -, -, hinn, -⟩ | ⟨-, -, hinn, -⟩ <;> exact hinn
  have hweak : ∀ B' : Subgroup (MulAut (barOf p K)), IsElemAbelian p B' → p ^ 2 ≤ Nat.card B' →
      IsWeaklyLocallyOTwoBalanced p 2 B' := by
    rcases hsl with ⟨-, -, -, -, hw⟩ | ⟨-, -, -, hw⟩ <;> exact hw
  obtain ⟨hA3, hFne, -⟩ := bc_rank h hs hr2
  have hAK := bc_not_normalizes h121 h hs hFne hweak
  have hCF := bc_inf_normalizer h hs hA3 hr2 hAK
  obtain ⟨a, haEA, haK⟩ := bc_exists_a_in_A0 h hs hA3 hr2 hAK hCF hinn
  have haA : a ∈ A := haEA.2
  obtain ⟨hap, hAeq, -, hcapG⟩ := bc_props_of_not_mem h hs hA3 hr2 hCF haA haK
  obtain ⟨-, hpcore, hC⟩ := bc_Ystruct h hs hCF
  have hAN := A_le_N h
  have hFA := hs.F_le_A
  have haN : a ∈ N := hAN haA
  have hKb : IsComponentOf (barX p N K) ⊤ := hs.hK.2.2.1
  have hcenter := center_trivial_of_centralizer_bot hKb hC
  have hcapY := bc_hcap hp hs.hK haN hcapG
  have hcommY := kconj_comm hKb hcapY
  have hā : (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) ^ p = 1 := mk_pow_eq_one haN hap
  obtain ⟨e₀, he₀⟩ := Lemma129W.exists_wreath_equiv p (barX p N K)
    (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) hā hcommY hcenter hcapY
  have hFle := bc_barX_F_le_kstar h hs hCF haA hap hAeq hcapG hinn
  have hlayer := bc_barX_layer_eq h hs haA hap hAeq
  have hZ := center_bot_barOf hp hs.hK hcenter
  have htype : (∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨
      (p = 5 ∧ IsSporType .Fi22 (barOf p K)) := by
    rcases hsl with ⟨hp5, -, hS, -, -⟩ | ⟨-, ⟨q, hq, hLp⟩, -, -⟩
    · exact Or.inr ⟨hp5, hS⟩
    · exact Or.inl ⟨q, hq, isLpType_of_center_bot hZ hLp⟩
  have hD : (∃ q : ℕ, p ∣ q - 1 ∧ IsLpType p q ↥(barX p N K)) ∨
      (p = 5 ∧ IsSporType .Fi22 ↥(barX p N K)) := by
    rcases htype with ⟨q, hq, hL⟩ | ⟨hp5, hS⟩
    · exact Or.inl ⟨q, hq, isLpType_of_mulEquiv (quotEquivBarX hp hs.hK.1 hs.hK.2.1) hL⟩
    · exact Or.inr ⟨hp5, isSporType_of_mulEquiv (quotEquivBarX hp hs.hK.1 hs.hK.2.1) hS⟩
  have hA0 : CFSG.Open.pRank p (E ⊓ A) = 2 :=
    le_antisymm (c104_rank_inf_le_two_of_DD hp h.pair (Or.inr hA3)) (two_le_rank_inf h)
  refine ⟨⟨hs.hK, ⟨hA3, hA0⟩, hs.hnc, ⟨bc_layer h hs hCF, hpcore⟩⟩, htype, ?_⟩
  have hFel : IsElemAbelian p F := (A_el h).mono hFA
  have hEk : IsEkIn p 2 A F := ⟨hFA, hFel, by rw [card_eq_pow_pRank hp hFel, hr2]⟩
  have hza : Subgroup.zpowers a ≤ N := Subgroup.zpowers_le.2 haN
  have hmemA : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩ ∈ barX p N A :=
    ⟨⟨a, haN⟩, (Subgroup.mem_subgroupOf).2 haA, rfl⟩
  have heq : barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A =
      Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) (barX p N K) ⊔
        Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) := by
    rw [hlayer]
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      have : barX p N A = barX p N F ⊔ Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) := by
        conv_lhs => rw [hAeq]
        rw [barX_sup_eq (hFA.trans hAN) hza, barX_zpowers haN]
      rw [this]
      exact sup_le (hFle.trans le_sup_left) le_sup_right
    · exact sup_le le_sup_left (Subgroup.zpowers_le.2 hmemA |>.trans le_sup_right)
  refine ⟨↥(barX p N K), inferInstance, hD, ?_⟩
  generalize hW : barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A = W'
  have hWT : W' = Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) (barX p N K) ⊔
      Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) := hW.symm.trans heq
  subst hWT
  refine ⟨e₀, F, hEk, by rw [hlayer]; exact hFle, a, haEA, hAeq, ?_⟩
  rw [eq_top_iff]
  intro q _
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hāW : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩ ∈
      Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) (barX p N K) ⊔
        Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  let w : ↥(Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩) (barX p N K) ⊔
        Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩)) :=
    ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, haN⟩, hāW⟩
  have hw : RegularWreathProduct.rightHom (e₀ w) = Multiplicative.ofAdd (1 : ZMod p) := he₀
  have hq : q = (Multiplicative.ofAdd (1 : ZMod p)) ^ (Multiplicative.toAdd q).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
    rfl
  refine ⟨w ^ (Multiplicative.toAdd q).val, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, barX_zpowers haN]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · show RegularWreathProduct.rightHom (e₀ (w ^ (Multiplicative.toAdd q).val)) = q
    rw [map_pow, map_pow, hw, ← hq]

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129b

end
