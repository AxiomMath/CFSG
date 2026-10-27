module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29Tail
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29F

variable {G : Type} [Group G] [Finite G]

theorem exists_Q_syl {x : G} {K A E : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q (CxK x K) ∧ ∀ e ∈ E, ∀ q ∈ Q, e * q = q * e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hAN : A ≤ centralizer ({x} : Set G) ⊓ normalizer (K : Set G) := by
    rw [hAE]
    refine sup_le (fun e he => Subgroup.mem_inf.2
      ⟨hKC (hEK he), Subgroup.le_normalizer (hEK he)⟩) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
      S3Theta52.mem_normalizer_of_le_centralizer hKC⟩
  have hAnorm : A ≤ normalizer ((CxK x K : Subgroup G) : Set G) := by
    intro a ha
    obtain ⟨hax, haK⟩ := Subgroup.mem_inf.1 (hAN ha)
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => S3Theta52.conj_mem_CxK hax haK hc, fun hc => ?_⟩
    have hax' : a⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem hax
    have haK' : a⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem haK
    have := S3Theta52.conj_mem_CxK hax' haK' hc
    rwa [show a⁻¹ * (a * c * a⁻¹) * a⁻¹⁻¹ = c by group] at this
  obtain ⟨T, hT, hAT⟩ := S3Theta52.exists_isSylowOf_ge (le_sup_left : A ≤ A ⊔ CxK x K)
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥A)
  have hMN : A ⊔ CxK x K ≤ normalizer ((CxK x K : Subgroup G) : Set G) :=
    sup_le hAnorm Subgroup.le_normalizer
  have hQ : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) := hT.inf_of_le_normalizer le_sup_right hMN
  have hTp : IsPGroup 2 ↥T := hT.isPGroup
  have hEA : E ≤ A := hAE ▸ le_sup_left
  refine ⟨T ⊓ CxK x K, hQ, fun e he q hq => ?_⟩
  obtain ⟨hqT, hqC⟩ := Subgroup.mem_inf.1 hq
  have hmemO : ⁅e, q⁆ ∈ pPrimeCoreOf 2 K := (Subgroup.mem_inf.1 hqC).2.2.2 e (hEK he)
  have hmemT : ⁅e, q⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem (hAT (hEA he)) hqT) (T.inv_mem (hAT (hEA he))))
      (T.inv_mem hqT)
  exact commutatorElement_eq_one_iff_mul_comm.1
    (S3Theta52.eq_one_of_mem_of_mem_pPrimeCoreOf hTp hmemT hmemO)

theorem ext_decomp {x : G} {K A B E : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1) (hEK : E ≤ K)
    (hAE : A = E ⊔ zpowers x) (hEel : CFSG.IsElementaryAbelian 2 ↥E)
    (hext : IsExtSource2 x K A B) :
    x ∈ B ⊓ cSec K ∧ B = E ⊔ (B ⊓ cSec K) ∧ E ⊓ (B ⊓ cSec K) = ⊥ := by
  obtain ⟨-, hxB, -, -, -, -, hBeq⟩ := hext
  have hxB0 : x ∈ B ⊓ cSec K :=
    Subgroup.mem_inf.2 ⟨hxB, S3Ctx29.mem_cSec_of_le_centralizer hK.1⟩
  refine ⟨hxB0, ?_, ?_⟩
  · calc B = A ⊔ (B ⊓ cSec K) := hBeq
      _ = E ⊔ zpowers x ⊔ (B ⊓ cSec K) := by rw [← hAE]
      _ = E ⊔ (B ⊓ cSec K) := by
        rw [sup_assoc, sup_eq_right.2 (Subgroup.zpowers_le.2 hxB0)]
  · rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heB0⟩ := Subgroup.mem_inf.1 he
    exact Subgroup.mem_bot.2 (S3Ctx29.eq_one_of_mem_cSec hZ hEK
      (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) heE (Subgroup.mem_inf.1 heB0).2)

theorem exists_involution_of_card_four {E : Subgroup G}
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : Nat.card ↥E = 4) :
    ∃ y ∈ E, orderOf y = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE4]; norm_num)
  obtain ⟨e, he⟩ := exists_ne (1 : ↥E)
  have hy1 : (e : G) ≠ 1 := fun h => he (Subtype.ext h)
  have hy2 : (e : G) ^ 2 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e e.2
  exact ⟨e, e.2, orderOf_eq_prime hy2 hy1⟩

theorem exists_B_Q {x : G} {K A E B₁ : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1) (hEK : E ≤ K)
    (hAE : A = E ⊔ zpowers x) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hext₁ : IsExtSource2 x K A B₁) (hr₁ : pRank 2 ↥B₁ = 4) (hB₁C : B₁ ⊓ cSec K ≤ CxK x K) :
    ∃ B Q : Subgroup G, IsExtSource2 x K A B ∧ pRank 2 ↥B = 4 ∧ B ⊓ cSec K ≤ CxK x K ∧
      IsSylowOf 2 Q (CxK x K) ∧ Q ≤ centralizer (A : Set G) ∧ B ⊓ cSec K ≤ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := Th2Sig6.isElementaryAbelian_of_le hAel hEA
  obtain ⟨Q, hQs, hQE⟩ := exists_Q_syl hK hEK hAE hAel
  obtain ⟨hxF₁, hB₁eq, hEF₁⟩ := ext_decomp hK hZ hEK hAE hEel hext₁
  have hB₁el : CFSG.IsElementaryAbelian 2 ↥B₁ := hext₁.2.2.2.1
  have hF₁el : CFSG.IsElementaryAbelian 2 ↥(B₁ ⊓ cSec K) :=
    Th2Sig6.isElementaryAbelian_of_le hB₁el inf_le_left
  obtain ⟨S, hS, hF₁S⟩ := S3Theta52.exists_isSylowOf_ge hB₁C
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥(B₁ ⊓ cSec K))
  obtain ⟨k, hkC, hk⟩ := hQs.exists_mem_conj hS
  set F' : Subgroup G := (B₁ ⊓ cSec K).map (MulAut.conj k⁻¹).toMonoidHom with hF'
  have hF'Q : F' ≤ Q := by
    rintro _ ⟨f, hf, rfl⟩
    have := (hk f).1 (hF₁S hf)
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hF'el : CFSG.IsElementaryAbelian 2 ↥F' :=
    CFSG.IsElementaryAbelian.map (p := 2) (A := B₁ ⊓ cSec K) (MulAut.conj k⁻¹).toMonoidHom
  have hF'card : Nat.card ↥F' = Nat.card ↥(B₁ ⊓ cSec K) :=
    Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  have hF'C : F' ≤ CxK x K := hF'Q.trans hQs.le
  have hxF' : x ∈ F' := by
    refine ⟨x, hxF₁, ?_⟩
    have hkx : k * x = x * k :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hkC).1
    show k⁻¹ * x * k⁻¹⁻¹ = x
    rw [inv_inv, mul_assoc, ← hkx, ← mul_assoc, inv_mul_cancel, one_mul]
  have hEF'c : ∀ e ∈ E, ∀ f ∈ F', e * f = f * e := fun e he f hf => hQE e he f (hF'Q hf)
  have hEF'1 : E ⊓ F' = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heF⟩ := Subgroup.mem_inf.1 he
    exact Subgroup.mem_bot.2 (S3Ctx29.eq_one_of_mem_cSec hZ hEK
      (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) heE (Subgroup.mem_inf.1 (hF'C heF)).2)
  have hBel : CFSG.IsElementaryAbelian 2 ↥(E ⊔ F') :=
    S3Theta52.isElementaryAbelian_sup hEel hF'el hEF'c
  have hB₁c : ∀ a ∈ B₁, ∀ c ∈ B₁, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B₁) ⟨c, hc⟩)
  have hEB₁ : E ≤ B₁ := hEA.trans hext₁.1
  have hcard₁ := S3Theta52.card_sup_of_commute
    (fun e he c hc => hB₁c e (hEB₁ he) c (Subgroup.mem_inf.1 hc).1) hEF₁
  rw [← hB₁eq] at hcard₁
  have hcard' := S3Theta52.card_sup_of_commute hEF'c hEF'1
  have hBcard : Nat.card ↥(E ⊔ F') = 2 ^ 4 := by
    rw [hcard', hF'card, ← hcard₁, C3.Layer1.Back.card_eq_two_pow_pRank hB₁el, hr₁]
  have hBr : pRank 2 ↥(E ⊔ F') = 4 := by
    have := hBel
    exact CFSG.pRank_eq_of_card_eq_pow one_lt_two hBcard
  have hBF' : (E ⊔ F') ⊓ cSec K = F' := by
    apply le_antisymm
    · intro b hb
      obtain ⟨hbB, hbS⟩ := Subgroup.mem_inf.1 hb
      obtain ⟨e, he, f, hf, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hEF'c hbB
      have hfS : f ∈ cSec K := (Subgroup.mem_inf.1 (hF'C hf)).2
      have heS : e ∈ cSec K := by
        have := (cSec K).mul_mem hbS ((cSec K).inv_mem hfS)
        simpa using this
      rw [S3Ctx29.eq_one_of_mem_cSec hZ hEK (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) he heS,
        one_mul]
      exact hf
    · exact le_inf le_sup_right fun f hf => (Subgroup.mem_inf.1 (hF'C hf)).2
  have hAB : A ≤ E ⊔ F' := by
    rw [hAE]
    exact sup_le le_sup_left ((Subgroup.zpowers_le.2 hxF').trans le_sup_right)
  have hxQ' : ∀ q ∈ Q, x * q = q * x := fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hQs.le hq)).1).symm
  have hQA : Q ≤ centralizer (A : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hAq : A ≤ centralizer ({q} : Set G) := by
      rw [hAE]
      exact sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.2 (hQE e he q hq))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hxQ' q hq)))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hAq ha)
  refine ⟨E ⊔ F', Q, ⟨hAB, Subgroup.mem_sup_right hxF', ?_, hBel, by omega, by omega, ?_⟩, hBr,
    hBF'.le.trans hF'C, hQs, hQA, hBF'.le.trans hF'Q⟩
  · exact sup_le (fun e he => hKC (hEK he)) fun f hf => (Subgroup.mem_inf.1 (hF'C hf)).1
  · rw [hBF', hAE, sup_assoc, sup_eq_right.2 (Subgroup.zpowers_le.2 hxF')]

end S3Sec29F

variable {G : Type} [Group G] [Finite G]

theorem exists_H29 : Exists29H G := by
  intro x a K A D J hc hSD hC hnoG
  obtain ⟨hC2, B₁, hext₁, hr₁, hB₁C⟩ := exists_B29H hc hSD hC
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK hSD.qShape3
  obtain ⟨E, hEK, hAE, -, hEel, hE4⟩ := S3Theta52.exists_E_of_src hc.src hZ
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hc.src.2.1
  obtain ⟨B, Q, hext, hrB, hBC, hQs, hQA, hBQ⟩ :=
    S3Sec29F.exists_B_Q hK hZ hEK hAE hAel hext₁ hr₁ hB₁C
  obtain ⟨y, hyE, hy2⟩ := S3Sec29F.exists_involution_of_card_four hEel hE4
  have hEA : E ≤ A := hAE ▸ le_sup_left
  exact ⟨y, B, Q, hc.hyp, hc.noAlt, hc.circ, hSD, hc.src, hext, hrB, hC2, hBC, hQs, hQA, hBQ,
    Subgroup.mem_inf.2 ⟨hEA hyE, hEK hyE⟩, hy2, hnoG B hext hrB⟩

end CFSG.GH74.Generic.BProg.B3
