module

public import CFSG.GH74.Generic.BProg.B3.S3T3B
public import CFSG.GH74.Generic.BProg.B3.S3Rk2Conj
public import CFSG.GH74.Generic.BProg.B3.S3Sec29BNTrans
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Basic

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3T3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_mul (H : Subgroup G) (g k : G) :
    H.map (MulAut.conj (g * k)).toMonoidHom =
      (H.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext h
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem mem_map_conj_self {H : Subgroup G} {k h : G} (hk : k * h = h * k) (hh : h ∈ H) :
    h ∈ H.map (MulAut.conj k).toMonoidHom :=
  ⟨h, hh, by simp [MulAut.conj_apply, hk]⟩

theorem isSylowOf_of_le_of_isSylowOf {S D C Q : Subgroup G} (hDC : D ≤ C) (hQD : Q ≤ D)
    (hQ : IsSylowOf 2 Q C) (hS : IsSylowOf 2 S D) : IsSylowOf 2 S C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSD, hSp, hS2⟩ := isSylowOf_iff.1 hS
  obtain ⟨-, -, hQ2⟩ := isSylowOf_iff.1 hQ
  refine isSylowOf_iff.2 ⟨hSD.trans hDC, hSp, fun h2 => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex S D C hSD hDC] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · exact hS2 h
  · exact hQ2 (h.trans (Subgroup.relIndex_dvd_of_le_left C hQD))

end S3T3

theorem lemma2912_proved (G : Type) [Group G] [Finite G] : Lemma2912 G := by
  intro x a y K A D J₀ B Q J hc hB hnoG hJ hJA7 huniq hall
  classical
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBN, e, F₀, F₁, hF⟩ := hall B Q hB
  obtain ⟨Bs, hBsel, hBs16, hxBs, hyBs, hBsx, hBsy, hBsN, hBsKC, hBs0, hnoR⟩ :=
    S3T3.exists_Bstar hB hJ hJA7 hBN e hF
  obtain ⟨hBsc, hBssq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBsel
  have hx2 : orderOf x = 2 := hB.circ.1.1.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hB.circ.1.1.1.2.2
  have hKx : K ≤ centralizer ({x} : Set G) := hKc.1
  have h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) := hB.shape.qShape3
  have hZ := B1.PilotS3.center_trivial_of_shape3 hKc h3
  have hxK : x ∉ K := B1.PilotS5.not_mem_of_center_trivial hx2 hKx hZ
  obtain ⟨E, hEK, hAE, -, hEel, hE4, hyE⟩ := S3T3.H29.exists_E hB
  obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.1 hB.y_mem
  have hy1 : y ≠ 1 := by
    intro h1
    have := hB.y_ord
    rw [h1, orderOf_one] at this
    omega
  have hAK : A ⊓ K = E := S3T3.inf_eq_of_exists_E hKx hx2 hxK hEK hAE
  have hB0C : Bs ⊓ cSec K ≤ CxK x K := le_inf (inf_le_left.trans hBsx) inf_le_right
  have hB0el : CFSG.IsElementaryAbelian 2 ↥(Bs ⊓ cSec K) :=
    Th2Sig6.isElementaryAbelian_of_le hBsel inf_le_left
  have hB04 : Nat.card ↥(Bs ⊓ cSec K) = 4 := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hB0el
    have h2 := (C3.Layer1.Back.pRank_mono' hB0C).trans hB.C_rank.le
    have h3 : 2 ^ pRank 2 ↥(Bs ⊓ cSec K) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  set E' : Subgroup G := Bs ⊓ K with hE'
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' := Th2Sig6.isElementaryAbelian_of_le hBsel inf_le_left
  have hE'4 : Nat.card ↥E' = 4 := by
    have h1 : Nat.card ↥Bs ≤ 4 * Nat.card ↥E' :=
      S3T3.card_le_four_mul_inf hZ hB.C_rank.le hBsel hBsKC
    have h2 : Nat.card ↥E' ≤ 4 := S3Rk2Rank.card_le_four_of_le h3 (inf_le_right : E' ≤ K) hE'el
    omega
  have hyE' : y ∈ E' := Subgroup.mem_inf.2 ⟨hyBs, hyK⟩
  have hEB0 : E' ⊓ (Bs ⊓ cSec K) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgE, hgC⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_bot.2 (S3Ctx29.eq_one_of_mem_cSec hZ (inf_le_right : E' ≤ K)
      (CFSG.IsElementaryAbelian.isPGroup 2 ↥E') hgE (Subgroup.mem_inf.1 hgC).2)
  have hBsdec : Bs = E' ⊔ (Bs ⊓ cSec K) := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_).symm
    rw [S3Theta52.card_sup_of_commute (fun a ha c hc => hBsc a (Subgroup.mem_inf.1 ha).1 c
      (Subgroup.mem_inf.1 hc).1) hEB0, hE'4, hB04, hBs16]
  obtain ⟨k₁, hk₁K, hk₁⟩ := S3Rk2Conj.exists_conj_four h3 hEK (inf_le_right : E' ≤ K) hEel hE4
    hE'el hE'4
  have hwE : k₁ * y * k₁⁻¹ ∈ E := by
    rw [← hk₁]
    exact ⟨y, hyE', rfl⟩
  have hw1 : k₁ * y * k₁⁻¹ ≠ 1 := by
    intro h
    apply hy1
    have : y = k₁⁻¹ * (k₁ * y * k₁⁻¹) * k₁ := by group
    rw [this, h]
    group
  obtain ⟨g, hg, hgw⟩ := ntrans_proved G x K A B E y (k₁ * y * k₁⁻¹) hB.circ.1.2.2 h3 hB.src hB.ext
    hB.rankB hEK hAE hEel hE4 hyE hy1 hwE hw1
  obtain ⟨⟨hgK, hgA⟩, -⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
  set k : G := g * k₁ with hkdef
  have hkK : k ∈ K := K.mul_mem hgK hk₁K
  have hky : k * y * k⁻¹ = y := by
    rw [hkdef]
    calc g * k₁ * y * (g * k₁)⁻¹ = g * (k₁ * y * k₁⁻¹) * g⁻¹ := by group
      _ = y := hgw
  have hkyc : k * y = y * k := by
    calc k * y = k * y * k⁻¹ * k := by group
      _ = y * k := by rw [hky]
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hgE : E.map (MulAut.conj g).toMonoidHom = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨f, hf, rfl⟩
      show g * f * g⁻¹ ∈ E
      rw [← hAK]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hgA f).1 (hEA hf),
        K.mul_mem (K.mul_mem hgK (hEK hf)) (K.inv_mem hgK)⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hkE : E'.map (MulAut.conj k).toMonoidHom = E := by
    rw [hkdef, S3T3.map_conj_mul, hk₁, hgE]
  have hkC : k ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hkyc
  have hkJ : k ∈ normalizer (J : Set G) := by
    have hX : (centralizer ({y} : Set G)).map (MulAut.conj k).toMonoidHom =
        centralizer ({y} : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkC)
    have hJ' : IsPCompIn 2 (centralizer ({y} : Set G)) (J.map (MulAut.conj k).toMonoidHom) := by
      have := Stage1.Thm2.Recip.isPCompIn_map_conj hJ k
      rwa [hX] at this
    obtain ⟨eA⟩ := hJA7
    obtain ⟨e₁⟩ := S3Boot293.nonempty_quot_map_conj k J
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ hJ' ⟨e₁.trans eA⟩)
  set Bss : Subgroup G := Bs.map (MulAut.conj k).toMonoidHom with hBss
  have hkxc : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.1 (hKx hkK)
  have hEB : E ≤ Bss := by
    rw [← hkE]
    exact Subgroup.map_mono inf_le_left
  have hxBss : x ∈ Bss := S3T3.mem_map_conj_self hkxc hxBs
  have hBssx : Bss ≤ centralizer ({x} : Set G) := by
    have hX : (centralizer ({x} : Set G)).map (MulAut.conj k).toMonoidHom =
        centralizer ({x} : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hKx hkK))
    rw [hBss, ← hX]
    exact Subgroup.map_mono hBsx
  have hBssel : CFSG.IsElementaryAbelian 2 ↥Bss := CFSG.IsElementaryAbelian.map _
  have hBss16 : Nat.card ↥Bss = 16 := by
    rw [hBss, Subgroup.card_map_of_injective (MulAut.conj k).injective, hBs16]
  have hBssr : pRank 2 ↥Bss = 4 := by
    have := hBssel
    exact CFSG.pRank_eq_of_card_eq_pow one_lt_two (by rw [hBss16]; norm_num)
  have hAB : A ≤ Bss := by
    rw [hAE]
    exact sup_le hEB (zpowers_le.2 hxBss)
  have hB0k : (Bs ⊓ cSec K).map (MulAut.conj k).toMonoidHom ≤ Bss ⊓ cSec K := by
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_inf.2 ⟨⟨b, (Subgroup.mem_inf.1 hb).1, rfl⟩,
      Stage1.Thm2.Recip.cSec_conj K (Subgroup.le_normalizer hkK) (Subgroup.mem_inf.1 hb).2⟩
  have hBsseq : Bss = A ⊔ (Bss ⊓ cSec K) := by
    refine le_antisymm ?_ (sup_le hAB inf_le_left)
    calc Bss = E ⊔ (Bs ⊓ cSec K).map (MulAut.conj k).toMonoidHom := by
          rw [hBss, ← hkE, ← Subgroup.map_sup, ← hBsdec]
      _ ≤ A ⊔ (Bss ⊓ cSec K) := sup_le_sup (hAE ▸ le_sup_left) hB0k
  have hext : IsExtSource2 x K A Bss :=
    ⟨hAB, hxBss, hBssx, hBssel, by omega, by omega, hBsseq⟩
  have hBssc : ∀ a ∈ Bss, ∀ c ∈ Bss, a * c = c * a :=
    (C3.Layer1.Back.forall_of_isElementaryAbelian hBssel).1
  have hB0D : Bss ⊓ cSec K ≤ CxK x K ⊓ centralizer (A : Set G) := by
    intro b hb
    obtain ⟨hbB, hbK⟩ := Subgroup.mem_inf.1 hb
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hBssx hbB, hbK⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hBssc a (hAB ha) b hbB
  have hBss0el : CFSG.IsElementaryAbelian 2 ↥(Bss ⊓ cSec K) :=
    Th2Sig6.isElementaryAbelian_of_le hBssel inf_le_left
  have hB0p : IsPGroup 2 ↥(Bss ⊓ cSec K) := CFSG.IsElementaryAbelian.isPGroup 2 ↥(Bss ⊓ cSec K)
  obtain ⟨Q', hQ'D, hB0Q'⟩ := S3Theta52.exists_isSylowOf_ge hB0D hB0p
  have hQ'C : IsSylowOf 2 Q' (CxK x K) :=
    S3T3.isSylowOf_of_le_of_isSylowOf inf_le_left (le_inf hB.Q_syl.le hB.Q_cent) hB.Q_syl hQ'D
  have h29 : H29 G x K A Bss Q' y :=
    ⟨hB.hyp, hB.noAlt, hB.circ, hB.shape, hB.src, hext, hBssr, hB.C_rank,
      le_inf (inf_le_left.trans hBssx) inf_le_right, hQ'C, hQ'D.le.trans inf_le_right, hB0Q',
      hB.y_mem, hB.y_ord, hnoG Bss hext hBssr⟩
  obtain ⟨-, e', F₀', F₁', hF'⟩ := hall Bss Q' h29
  obtain ⟨hF₀', -, hF'eq⟩ := hF'
  obtain ⟨τ, hτ⟩ := S3Sec29H.exists_a7Act_conj e e'
  set φk := GLS.Th2.Obs.a7Act J e ⟨k, hkJ⟩ with hφk
  refine hnoR ((F₀'.map (MulAut.conj τ⁻¹).toMonoidHom).map (MulAut.conj φk⁻¹).toMonoidHom) ?_
    (S3T3.isRootFour_map_conj (S3T3.isRootFour_map_conj hF₀' τ⁻¹) φk⁻¹)
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hfm : f ∈ (Bss.subgroupOf (normalizer (J : Set G))).map (GLS.Th2.Obs.a7Act J e') := by
    rw [hF'eq]
    exact Subgroup.mem_sup_left hf
  obtain ⟨m, hm, rfl⟩ := hfm
  obtain ⟨b, hb, hbm⟩ := Subgroup.mem_subgroupOf.1 hm
  have hbN : b ∈ normalizer (J : Set G) := hBsN hb
  have hmeq : m = ⟨k, hkJ⟩ * ⟨b, hbN⟩ * (⟨k, hkJ⟩ : ↥(normalizer (J : Set G)))⁻¹ := by
    apply Subtype.ext
    rw [← hbm]
    rfl
  refine ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.2 hb, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hτ, hmeq, map_mul, map_mul, map_inv, ← hφk]
  group

end CFSG.GH74.Generic.BProg.B3
