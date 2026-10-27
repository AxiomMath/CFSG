module

public import CFSG.ClassicalInvolution.Asc77.AscC25V32
public import CFSG.ClassicalInvolution.Asc77.AscC25X12

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section TwinSec

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fs_twinSect0 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a)
    (hat : a * t' = t' * a) {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩) :
    ∃ (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
      (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈
        conjGen (perfectCoreIn K' a))
      (a₀ b₀ : ↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))),
      TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a))))
        (secImg (conjGen (perfectCoreIn K' a)) (perfectCoreIn K' a))
        (secImg (conjGen (perfectCoreIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (perfectCoreIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀ := by
  have ht'a : t' ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hat.symm
  refine ⟨ht'a, ?_⟩
  have hp : p ≠ 2 := h.hp
  have d' := twinCtx'_of_hyp25 h
  have hΛ := fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hL
  have hzKa : z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  set w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩ with hwdef
  have hw : conjSub (w : G) K' = K := conjSub_t'_K' h
  set L := perfectCoreIn K' a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hLmem : L ∈ conjFamily L := ⟨1, conjSub_one L⟩
  have hL'mem : conjSub w L ∈ conjFamily L := ⟨w, rfl⟩
  have hLX : L ≤ X := le_conjGen hLmem
  have hL'X : conjSub w L ≤ X := le_conjGen hL'mem
  have hzw : w * ⟨z, hzA⟩ * w⁻¹ = (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
    apply Subtype.ext
    change t' * z * t'⁻¹ = z
    calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [t'_comm_z h]
      _ = z := by group
  have hu₁ : IsUniqueInvolution L ⟨z, hzA⟩ := by
    have := fs_isUniqueInvolution_conjSub h.hz' hzA hzKa 1
    simpa [conjSub_one] using this
  have hu₂ : IsUniqueInvolution (conjSub w L) ⟨z, hzA⟩ := by
    have := fs_isUniqueInvolution_conjSub h.hz' hzA hzKa w
    rwa [hzw] at this
  have hne : conjSub w L ≠ L := fs_swap_ne d' hzA hL hw
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaMod p e₀ (restrictFamily (conjFamily L) X) := hΛ.restrict X
  have hΛ' : HypOmegaMod p e₀
      (quotFamily (restrictFamily (conjFamily L) X) (classicalInvolutionOddCore ↥X)) :=
    oddQuotHyp p e₀ hp h5 ↥X _ hΛ₁ _ hN
  have hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hu₁.mem
  set z₀ : ↥X ⧸ classicalInvolutionOddCore ↥X := QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩ with hz₀
  have hz₀A : IsUniqueInvolution (secImg X L) z₀ := by
    have h1 := fs_isUniqueInvolution_secImg h.hz' hzA hzKa 1
    have e1 : (QuotientGroup.mk' _ ⟨1 * ⟨z, hzA⟩ * 1⁻¹, le_conjGen ⟨1, rfl⟩
        (fs_isUniqueInvolution_conjSub h.hz' hzA hzKa 1).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp
    rw [e1, conjSub_one] at h1
    exact h1
  have hz₀A' : IsUniqueInvolution (secImg X (conjSub w L)) z₀ := by
    have h1 := fs_isUniqueInvolution_secImg h.hz' hzA hzKa w
    have e1 : (QuotientGroup.mk' _ ⟨w * ⟨z, hzA⟩ * w⁻¹, le_conjGen ⟨w, rfl⟩
        (fs_isUniqueInvolution_conjSub h.hz' hzA hzKa w).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      exact hzw
    rw [e1] at h1
    exact h1
  obtain ⟨V₁, V₂, hV₁, hV₂, hc⟩ := T7A.exists_commuting_sylow_twin hΛ hLmem hL'mem hne hu₁ hu₂
  have hcomm : Commutes (V₁.subgroupOf X) (V₂.subgroupOf X) := by
    intro x hx y hy
    apply Subtype.ext
    exact hc (x : ↥(Subgroup.centralizer ({a} : Set G))) (Subgroup.mem_subgroupOf.mp hx) y
      (Subgroup.mem_subgroupOf.mp hy)
  have hne_img : secImg X L ≠ secImg X (conjSub w L) :=
    map_ne_of_commutes_sylow hp hΛ' hN (M₁ := L.subgroupOf X) (M₂ := (conjSub w L).subgroupOf X)
      (V₁ := V₁.subgroupOf X) (V₂ := V₂.subgroupOf X) ⟨L, hLmem, hLX, rfl⟩
      (Hall196.isSylow2In_subgroupOf_of_le hV₁ hLX)
      (Hall196.isSylow2In_subgroupOf_of_le hV₂ hL'X) hcomm
  obtain ⟨y, hyR', hy4, hya, hyP⟩ := exists_order_four_mem_perfectCore h h9 haS ha2 hF'
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hyL : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ L :=
    Subgroup.mem_subgroupOf.mpr hyP
  have hyX : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hyL
  have hysq : y * y = z := C25X.sq_eq_of_orderOf_four h.hz' (h.hR'syl.1 hyR') hy4
  have hbL' : w * ⟨y, hyC⟩ * w⁻¹ ∈ conjSub w L := conj_mem_conjSub hyL
  have hbX : w * ⟨y, hyC⟩ * w⁻¹ ∈ X := hL'X hbL'
  refine ⟨hzX, QuotientGroup.mk ⟨⟨y, hyC⟩, hyX⟩, QuotientGroup.mk ⟨w * ⟨y, hyC⟩ * w⁻¹, hbX⟩,
    ⟨(mem_secFamily_iff L _).mpr ⟨1, by rw [conjSub_one]⟩, (mem_secFamily_iff L _).mpr ⟨w, rfl⟩,
      hne_img, hz₀A, hz₀A',
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbL'), ?_, ?_, ?_, ?_⟩⟩
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    apply Subtype.ext
    exact hysq
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    have e : w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) =
        w * (⟨y, hyC⟩ * ⟨y, hyC⟩) * w⁻¹ := by group
    have e2 : (⟨y, hyC⟩ * ⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = ⟨z, hzA⟩ :=
      Subtype.ext hysq
    change w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) = ⟨z, hzA⟩
    rw [e, e2, hzw]
  · intro M hM hMn
    have := fs_nbr_quot d' hp h5 hzA hL hΛ hw 1 (M := M) (by rwa [conjSub_one])
    simpa using this
  · intro M hM hMn
    have := fs_nbr_quot d' hp h5 hzA hL hΛ hw w (M := M) hMn
    have hww : w * w = 1 := Subtype.ext h.ht'2
    rwa [hww, conjSub_one] at this

end TwinSec

section Generic

variable {Y₀ : Type} [Group Y₀] [Finite Y₀]

theorem nc4_excl_generic (L : Subgroup Y₀) (z₀ : Y₀)
    (hu : ∀ c : Y₀, IsUniqueInvolution (conjSub c L) (c * z₀ * c⁻¹))
    (hNC4 : ∀ c₁ c₂ y₁ : Y₀, y₁ ∈ conjSub c₁ L → orderOf y₁ = 4 →
      y₁ * (c₂ * z₀ * c₂⁻¹) = (c₂ * z₀ * c₂⁻¹) * y₁ → c₂ * z₀ * c₂⁻¹ = c₁ * z₀ * c₁⁻¹) :
    ∀ {J₁ J₂ : Subgroup (↥(conjGen L) ⧸ classicalInvolutionOddCore ↥(conjGen L))},
      J₁ ∈ oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L)) →
      J₂ ∈ oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L)) →
      ∀ {y z₂ : ↥(conjGen L) ⧸ classicalInvolutionOddCore ↥(conjGen L)},
        y ∈ J₁ → y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 →
        z₂ ≠ y * y → z₂ * y = y * z₂ → False := by
  classical
  intro J₁ J₂ hJ₁ hJ₂ y z₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
  obtain ⟨c₁, rfl⟩ := (mem_secFamily_iff L J₁).mp hJ₁
  obtain ⟨c₂, rfl⟩ := (mem_secFamily_iff L J₂).mp hJ₂
  have hXn : (conjGen L).Normal := conjGen_normal L
  have hbar₁ : IsUniqueInvolution (secImg (conjGen L) (conjSub c₁ L))
      (QuotientGroup.mk' _ ⟨c₁ * z₀ * c₁⁻¹, le_conjGen ⟨c₁, rfl⟩ (hu c₁).mem⟩) :=
    isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
      (isUniqueInvolution_subgroupOf (hu c₁) (le_conjGen ⟨c₁, rfl⟩))
  have hbar₂ : IsUniqueInvolution (secImg (conjGen L) (conjSub c₂ L))
      (QuotientGroup.mk' _ ⟨c₂ * z₀ * c₂⁻¹, le_conjGen ⟨c₂, rfl⟩ (hu c₂).mem⟩) :=
    isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
      (isUniqueInvolution_subgroupOf (hu c₂) (le_conjGen ⟨c₂, rfl⟩))
  have hzX₂ : c₂ * z₀ * c₂⁻¹ ∈ conjGen L := le_conjGen ⟨c₂, rfl⟩ (hu c₂).mem
  have hzX₁ : c₁ * z₀ * c₁⁻¹ ∈ conjGen L := le_conjGen ⟨c₁, rfl⟩ (hu c₁).mem
  have hz₂eq : z₂ = QuotientGroup.mk ⟨c₂ * z₀ * c₂⁻¹, hzX₂⟩ :=
    (hbar₂.unique z₂ hz₂ hz₂2).resolve_left hz₂1
  have hyy : y * y = QuotientGroup.mk ⟨c₁ * z₀ * c₁⁻¹, hzX₁⟩ := by
    refine (hbar₁.unique (y * y) ((secImg (conjGen L) (conjSub c₁ L)).mul_mem hy hy)
      ?_).resolve_left hy2
    calc y * y * (y * y) = y * y * y * y := by simp only [mul_assoc]
      _ = 1 := hy4
  obtain ⟨c, hcmem, hcy⟩ := Subgroup.mem_map.mp hy
  have hcM : (c : Y₀) ∈ conjSub c₁ L := Subgroup.mem_subgroupOf.mp hcmem
  have hy_ord : orderOf y = 4 := by
    have h4 : y ^ 2 ^ (1 + 1) = 1 := by
      have : y ^ 2 ^ (1 + 1) = y * y * y * y := by simp [pow_succ, mul_assoc]
      rw [this]
      exact hy4
    have h2 : ¬ y ^ 2 ^ 1 = 1 := by simpa [pow_two] using hy2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
    simpa using this
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen L))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(conjGen L)
  set c' : ↥(conjGen L) := c ^ m with hc'
  have hc'k : c' ^ (2 ^ k) = 1 := by
    rw [hc', ← pow_mul, mul_comm, ← hkm]
    exact pow_orderOf_eq_one c
  have hπc' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen L)) c' = y ^ m := by
    rw [hc', map_pow, hcy]
  have hcop : Nat.Coprime (orderOf y) m := by
    rw [hy_ord]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have hym_ord : orderOf (y ^ m) = 4 := by
    rw [Nat.Coprime.orderOf_pow hcop, hy_ord]
  have hy44 : y ^ 4 = 1 := by
    rw [← hy_ord]
    exact pow_orderOf_eq_one y
  have hc'4 : c' ^ 4 = 1 := by
    have h1 : c' ^ 4 ∈ classicalInvolutionOddCore ↥(conjGen L) := by
      have h0 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen L)) (c' ^ 4) = 1 := by
        rw [map_pow, hπc', ← pow_mul, mul_comm, pow_mul, hy44, one_pow]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : orderOf (⟨c' ^ 4, h1⟩ : classicalInvolutionOddCore ↥(conjGen L)) ∣
        Nat.card (classicalInvolutionOddCore ↥(conjGen L)) := orderOf_dvd_natCard _
    have h3 : orderOf (⟨c' ^ 4, h1⟩ : classicalInvolutionOddCore ↥(conjGen L)) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      refine orderOf_dvd_of_pow_eq_one ?_
      show (c' ^ 4) ^ (2 ^ k) = 1
      rw [← pow_mul, mul_comm, pow_mul, hc'k, one_pow]
    have h4 : Nat.Coprime (2 ^ k) (Nat.card (classicalInvolutionOddCore ↥(conjGen L))) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN₀odd)
    have h5 : orderOf (⟨c' ^ 4, h1⟩ : classicalInvolutionOddCore ↥(conjGen L)) = 1 :=
      Nat.eq_one_of_dvd_coprimes h4 h3 h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
  have hc'2 : ¬ c' ^ 2 ^ 1 = 1 := by
    intro h'
    have h'' : c' ^ 2 = 1 := by simpa using h'
    have h3 : (y ^ m) ^ 2 = 1 := by
      rw [← hπc', ← map_pow, h'', map_one]
    have h4 : orderOf (y ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [hym_ord] at h4
    omega
  have hc'_ord : orderOf c' = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hc'2 (by simpa using hc'4)
    simpa using this
  set y₁ : Y₀ := (c' : Y₀) with hy₁
  have hy₁M : y₁ ∈ conjSub c₁ L := by
    rw [hy₁, hc']
    exact (conjSub c₁ L).pow_mem hcM m
  have hy₁X : y₁ ∈ conjGen L := c'.2
  have hy₁4 : orderOf y₁ = 4 := by rw [hy₁, Subgroup.orderOf_coe]; exact hc'_ord
  have hcom : ⁅c₂ * z₀ * c₂⁻¹, y₁⁆ ∈ oddCoreOf (conjGen L) := by
    have h1 : (⟨c₂ * z₀ * c₂⁻¹, hzX₂⟩ : ↥(conjGen L)) * c' *
        (c' * ⟨c₂ * z₀ * c₂⁻¹, hzX₂⟩)⁻¹ ∈ classicalInvolutionOddCore ↥(conjGen L) := by
      have h2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen L))
          ((⟨c₂ * z₀ * c₂⁻¹, hzX₂⟩ : ↥(conjGen L)) * c' *
            (c' * ⟨c₂ * z₀ * c₂⁻¹, hzX₂⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hπc']
        have h3 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjGen L))
            (⟨c₂ * z₀ * c₂⁻¹, hzX₂⟩ : ↥(conjGen L)) = z₂ := hz₂eq.symm
        rw [h3]
        exact mul_inv_eq_one.mpr ((Commute.pow_right (show Commute z₂ y from hcomm) m).eq)
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [commutatorElement_def, mul_assoc, hy₁]⟩
  have hR2 : IsPGroup 2 (Subgroup.zpowers y₁) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy₁4]; norm_num)
  have hcN : c₂ * z₀ * c₂⁻¹ ∈ Subgroup.normalizer (oddCoreOf (conjGen L) : Set Y₀) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hzX₂)
  have huN : y₁ ∈ Subgroup.normalizer (oddCoreOf (conjGen L) : Set Y₀) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hy₁X)
  obtain ⟨n, hn, hncent⟩ := T7L.exists_conj_centralizes (hu c₂).sq
    (oddCoreOf_odd_natCard (conjGen L)) hR2 (Subgroup.zpowers_le.mpr huN) hcN
    (fun r hr => C25X.comm_mem_of_mem_zpowers huN hcom hr)
  have hyc : (n * y₁ * n⁻¹) * (c₂ * z₀ * c₂⁻¹) = (c₂ * z₀ * c₂⁻¹) * (n * y₁ * n⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hncent (conj_mem_conjSub (Subgroup.mem_zpowers y₁)))
  have hy₁' : n * y₁ * n⁻¹ ∈ conjSub (n * c₁) L := by
    have := conj_mem_conjSub (n := n) hy₁M
    rwa [← conjSub_mul] at this
  have hy₁'4 : orderOf (n * y₁ * n⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) y₁
    simpa [MulAut.conj_apply, hy₁4] using this
  have hconj := hNC4 (n * c₁) c₂ (n * y₁ * n⁻¹) hy₁' hy₁'4 hyc
  have hnX : n ∈ conjGen L := oddCoreOf_le_self _ hn
  have hnN₀ : (⟨n, hnX⟩ : ↥(conjGen L)) ∈ classicalInvolutionOddCore ↥(conjGen L) := by
    obtain ⟨n', hn', hnn'⟩ := Subgroup.mem_map.mp hn
    have : n' = ⟨n, hnX⟩ := Subtype.ext hnn'
    rwa [this] at hn'
  have hmk : (QuotientGroup.mk ⟨n, hnX⟩ : ↥(conjGen L) ⧸ classicalInvolutionOddCore ↥(conjGen L))
      = 1 := (QuotientGroup.eq_one_iff _).mpr hnN₀
  have e1 : (⟨c₂ * z₀ * c₂⁻¹, hzX₂⟩ : ↥(conjGen L)) =
      ⟨n, hnX⟩ * ⟨c₁ * z₀ * c₁⁻¹, hzX₁⟩ * ⟨n, hnX⟩⁻¹ := by
    apply Subtype.ext
    change c₂ * z₀ * c₂⁻¹ = n * (c₁ * z₀ * c₁⁻¹) * n⁻¹
    rw [hconj]
    group
  apply hne
  rw [hz₂eq, hyy, e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk]
  simp

theorem central_of_connected (L : Subgroup Y₀) (z₀ : Y₀)
    (hu : ∀ c : Y₀, IsUniqueInvolution (conjSub c L) (c * z₀ * c⁻¹))
    (hz₀X : z₀ ∈ conjGen L)
    (A' : Subgroup (↥(conjGen L) ⧸ classicalInvolutionOddCore ↥(conjGen L)))
    (hA'u : IsUniqueInvolution A' (QuotientGroup.mk ⟨z₀, hz₀X⟩))
    (hconn : ∀ c : Y₀, secImg (conjGen L) (conjSub c L) = secImg (conjGen L) L ∨
      secImg (conjGen L) (conjSub c L) = A') (c : Y₀) :
    QuotientGroup.mk' (classicalInvolutionOddCore Y₀) z₀ *
        QuotientGroup.mk' (classicalInvolutionOddCore Y₀) c =
      QuotientGroup.mk' (classicalInvolutionOddCore Y₀) c *
        QuotientGroup.mk' (classicalInvolutionOddCore Y₀) z₀ := by
  classical
  have hXn : (conjGen L).Normal := conjGen_normal L
  have hz₀2 : z₀ * z₀ = 1 := by simpa using (hu 1).sq
  have hzinv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz₀2
  have hu1 : IsUniqueInvolution L z₀ := by simpa [conjSub_one] using hu 1
  have hLX : L ≤ conjGen L := le_conjGen ⟨1, conjSub_one L⟩
  have hA1 : IsUniqueInvolution (secImg (conjGen L) L) (QuotientGroup.mk ⟨z₀, hz₀X⟩) :=
    isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
      (isUniqueInvolution_subgroupOf hu1 hLX)
  have key : ∀ d : Y₀, z₀ * (d * z₀ * d⁻¹) ∈ oddCoreOf (conjGen L) := by
    intro d
    have hzd : d * z₀ * d⁻¹ ∈ conjGen L := le_conjGen ⟨d, rfl⟩ (hu d).mem
    have hbar : IsUniqueInvolution (secImg (conjGen L) (conjSub d L))
        (QuotientGroup.mk' _ ⟨d * z₀ * d⁻¹, hzd⟩) :=
      isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
        (isUniqueInvolution_subgroupOf (hu d) (le_conjGen ⟨d, rfl⟩))
    have heq : (QuotientGroup.mk ⟨d * z₀ * d⁻¹, hzd⟩ :
        ↥(conjGen L) ⧸ classicalInvolutionOddCore ↥(conjGen L)) =
          QuotientGroup.mk ⟨z₀, hz₀X⟩ := by
      rcases hconn d with h | h
      · rw [h] at hbar
        exact hbar.eq hA1
      · rw [h] at hbar
        exact hbar.eq hA'u
    have h1 := QuotientGroup.eq.mp heq
    have h2 : (d * z₀ * d⁻¹)⁻¹ * z₀ ∈ oddCoreOf (conjGen L) := Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    have h3 := (oddCoreOf (conjGen L)).inv_mem h2
    have e : ((d * z₀ * d⁻¹)⁻¹ * z₀)⁻¹ = z₀ * (d * z₀ * d⁻¹) := by
      rw [mul_inv_rev, inv_inv, hzinv]
    rwa [e] at h3
  have hnorm : (oddCoreOf (conjGen L)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer ((conjGen L : Subgroup Y₀) : Set Y₀) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact ⟨fun hx => hXn.conj_mem x hx g, fun hx => by
        have := hXn.conj_mem _ hx g⁻¹
        simpa [mul_assoc] using this⟩
    have hg' := T7L.mem_normalizer_oddCoreOf hg
    exact (Subgroup.mem_normalizer_iff.mp hg' n).mp hn
  have hle : oddCoreOf (conjGen L) ≤ classicalInvolutionOddCore Y₀ :=
    CFSG.ComponentClassification.OddCore.maximal Y₀ _ hnorm (oddCoreOf_odd_natCard _)
  have hv := hle (key c)
  have hN : (classicalInvolutionOddCore Y₀).Normal := inferInstance
  have h4 := hN.conj_mem _ hv c⁻¹
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have e2 : (z₀ * c)⁻¹ * (c * z₀) = c⁻¹ * (z₀ * (c * z₀ * c⁻¹)) * c⁻¹⁻¹ := by
    rw [mul_inv_rev, hzinv]
    group
  rw [e2]
  exact h4

end Generic

section TwinSec2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fs_nc4_excl (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {a : G} {e₀ : ℕ}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩) :
    ∀ {J₁ J₂ : Subgroup (↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a)))},
      J₁ ∈ oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a))) →
      J₂ ∈ oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a))) →
      ∀ {y z₂ : ↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))},
        y ∈ J₁ → y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 →
        z₂ ≠ y * y → z₂ * y = y * z₂ → False := by
  have hzKa : z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  intro J₁ J₂ hJ₁ hJ₂ y z₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
  have hNC4 : ∀ c₁ c₂ y₁ : ↥(Subgroup.centralizer ({a} : Set G)),
      y₁ ∈ conjSub c₁ (perfectCoreIn K' a) → orderOf y₁ = 4 →
      y₁ * (c₂ * ⟨z, hzA⟩ * c₂⁻¹) = (c₂ * ⟨z, hzA⟩ * c₂⁻¹) * y₁ →
      c₂ * ⟨z, hzA⟩ * c₂⁻¹ = c₁ * ⟨z, hzA⟩ * c₁⁻¹ := by
    intro c₁ c₂ y₁ hy₁ hy₁4 hcomm
    have hy₁4' : orderOf (y₁ : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hy₁4
    have hcomm' : ((c₂ : G) * z * (c₂ : G)⁻¹) * (y₁ : G) =
        (y₁ : G) * ((c₂ : G) * z * (c₂ : G)⁻¹) := (congrArg Subtype.val hcomm).symm
    have := eq_conj_z_of_commute_order_four h (c := (c₁ : G)) (g := (c₂ : G)) (y₀ := (y₁ : G))
      (le_conjSub_of_mem c₁ hy₁) hy₁4' hcomm'
    exact Subtype.ext this
  exact nc4_excl_generic (perfectCoreIn K' a) ⟨z, hzA⟩
    (fun c => fs_isUniqueInvolution_conjSub h.hz' hzA hzKa c) hNC4 hJ₁ hJ₂ hy hy4 hy2 hz₂ hz₂2
    hz₂1 hne hcomm

theorem fs_typed (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a) (hat : a * t' = t' * a) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩ ∧
      (z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨
        SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
          5 true ∨
        SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
          6 (!piSign p e₀)) := by
  classical
  obtain ⟨e₀, hfe, h5, hzA, hL, hlt, hIH⟩ := mixed_section_data h h9 haS ha2 hF'
  refine ⟨e₀, hfe, h5, hzA, hL, ?_⟩
  have hp : p ≠ 2 := h.hp
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := fs_twinSect0 h h9 haS ha2 hF' hat h5 hzA hL
  have hΛ := fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hL
  have hS := genSection_conjFamily hp h5 hL hΛ (aEmpty_conjFamily_perfectCore h hp hzA hL)
  have hlt' : Nat.card (↥(conjGen (perfectCoreIn K' a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))) < Nat.card G := by
    have h1 : Nat.card (↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))) ≤
          Nat.card ↥(conjGen (perfectCoreIn K' a)) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    have h2 : Nat.card ↥(conjGen (perfectCoreIn K' a)) ≤
        Nat.card ↥(Subgroup.centralizer ({a} : Set G)) := Subgroup.card_le_card_group _
    omega
  rcases C25X.twinSection_cases0 hp h5 hIH hlt' hS T with hconn | ⟨D, hcard, i, hsix⟩
  · left
    have hzKa : z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
      Subgroup.mem_subgroupOf.mp hL.mem
    have hu : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        IsUniqueInvolution (conjSub c (perfectCoreIn K' a)) (c * ⟨z, hzA⟩ * c⁻¹) :=
      fun c => fs_isUniqueInvolution_conjSub h.hz' hzA hzKa c
    have hconn' : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        secImg (conjGen (perfectCoreIn K' a)) (conjSub c (perfectCoreIn K' a)) =
          secImg (conjGen (perfectCoreIn K' a)) (perfectCoreIn K' a) ∨
        secImg (conjGen (perfectCoreIn K' a)) (conjSub c (perfectCoreIn K' a)) =
          secImg (conjGen (perfectCoreIn K' a)) (conjSub (⟨t', ht'a⟩ :
            ↥(Subgroup.centralizer ({a} : Set G))) (perfectCoreIn K' a)) :=
      fun c => hconn _ ((mem_secFamily_iff (perfectCoreIn K' a) _).mpr ⟨c, rfl⟩)
    unfold zStarOf
    refine Subgroup.mem_map.mpr ⟨⟨z, hzA⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    exact (central_of_connected (perfectCoreIn K' a) ⟨z, hzA⟩ hu hzX _ T.hzA' hconn' c).symm
  · right
    have hmf : C25X.NC4Fact p := C25X.nc4Fact_proved p
    let M := T7L.toModelOfGen hS.hyp D hcard hS.gen i
    have hodd : Odd (p ^ e₀) := (Nat.Prime.odd_of_ne_two Fact.out hp).pow
    have hmod : p ^ e₀ % 4 = 1 ∨ p ^ e₀ % 4 = 3 := by
      obtain ⟨j, hj⟩ := hodd
      omega
    have key : ((D.tag i = .PSL ∧ D.rank i = 4 ∧ p ^ e₀ % 4 = 1) ∨
        (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ e₀ % 4 = 3) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4)) →
        False := by
      intro hS4
      obtain ⟨J₁, hJ₁, J₂, hJ₂, y, hy, z₂, hz₂, hy4, hy2, hz₂2, hz₂1, hne, hcomm⟩ :=
        C25X.s4_excl hmf hp h5 M ⟨_, T.hA⟩ hS4
      exact fs_nc4_excl h hzA hL hJ₁ hJ₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
    rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inl ⟨rfl, h1, h2⟩, D, hcard, i, rfl, rfl⟩
    · rcases hmod with h3 | h3
      · exact (key (Or.inl ⟨h1, h2, h3⟩)).elim
      · right
        have hπ : piSign p e₀ = false := by
          unfold piSign
          simp [h3]
        rw [hπ]
        exact sectionOrthType_of_hasOrthType hS.gen
          ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩), D, hcard, i, rfl, rfl⟩
    · rcases hmod with h3 | h3
      · right
        have hπ : piSign p e₀ = true := by
          unfold piSign
          simp [h3]
        rw [hπ]
        exact sectionOrthType_of_hasOrthType hS.gen
          ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩)), D, hcard, i, rfl, rfl⟩
      · exact (key (Or.inr (Or.inl ⟨h1, h2, h3⟩))).elim
    · exact (key (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))).elim
    · exact (key (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))).elim
    · exact (key (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))).elim

end TwinSec2

end CFSG.ClassicalInvolution.Asc77.C25V
