module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29
public import CFSG.GH74.Generic.BProg.B3.S3Sec29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

namespace S3Sec29BNTrans

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_subgroupOf_of_le {A Y : Subgroup G} (h : A ≤ Y) :
    Nat.card (A.subgroupOf Y) = Nat.card A := by
  have h1 := Subgroup.card_map_of_injective (K := A.subgroupOf Y) (f := Y.subtype)
    Y.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h] at h1
  exact h1.symm

theorem eq_one_of_pGroup_of_odd {Y : Type} [Group Y] [Finite Y] {P O : Subgroup Y}
    (hP : IsPGroup 2 P) (hO : Odd (Nat.card O)) {o : Y} (hoP : o ∈ P) (hoO : o ∈ O) : o = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨o, hoP⟩
  have h1 : o ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have h2 : orderOf o ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hoO
  have hcop : Nat.Coprime (2 ^ n) (Nat.card O) :=
    (Nat.coprime_two_left.2 hO).pow_left n
  have h4 : orderOf o ∣ Nat.gcd (2 ^ n) (Nat.card O) := Nat.dvd_gcd h2 h3
  rw [hcop] at h4
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

theorem exists_o_normalizing {O B : Subgroup G} (hOB : B ≤ normalizer (O : Set G))
    (hOodd : Odd (Nat.card O)) (hB2 : IsPGroup 2 B) {g : G}
    (hg : B.map (MulAut.conj g).toMonoidHom ≤ B ⊔ O) :
    ∃ o ∈ O, B.map (MulAut.conj (o⁻¹ * g)).toMonoidHom = B := by
  classical
  set Y : Subgroup G := B ⊔ O with hY
  have hOY : O ≤ Y := le_sup_right
  have hBY : B ≤ Y := le_sup_left
  have hYN : Y ≤ normalizer (O : Set G) := sup_le hOB Subgroup.le_normalizer
  let B' : Subgroup Y := B.subgroupOf Y
  let O' : Subgroup Y := O.subgroupOf Y
  let Q' : Subgroup Y := (B.map (MulAut.conj g).toMonoidHom).subgroupOf Y
  have hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).2 hYN
  have hO'odd : Odd (Nat.card O') := by
    rw [show Nat.card O' = Nat.card O from card_subgroupOf_of_le hOY]
    exact hOodd
  have hB'2 : IsPGroup 2 B' := hB2.comap_subtype
  have hQ'2 : IsPGroup 2 Q' := (hB2.map (MulAut.conj g).toMonoidHom).comap_subtype
  have hsup : B' ⊔ O' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBY hOY]
    exact Subgroup.subgroupOf_self _
  have hdec : ∀ y : Y, ∃ o ∈ O', ∃ b ∈ B', y = o * b := by
    intro y
    have hy : y ∈ O' ⊔ B' := by rw [sup_comm, hsup]; exact Subgroup.mem_top y
    rw [Subgroup.mem_sup_of_normal_left] at hy
    obtain ⟨o, ho, b, hb, rfl⟩ := hy
    exact ⟨o, ho, b, hb, rfl⟩
  have hmax : ∀ {P : Subgroup Y}, IsPGroup 2 P → B' ≤ P → P = B' := by
    intro P hP hle
    apply le_antisymm _ hle
    intro p hp
    obtain ⟨o, ho, b, hb, rfl⟩ := hdec p
    have hbP : b ∈ P := hle hb
    have hoP : o ∈ P := by
      have := P.mul_mem hp (P.inv_mem hbP)
      simpa using this
    have := eq_one_of_pGroup_of_odd hP hO'odd hoP ho
    rw [this, one_mul]
    exact hb
  let SB : Sylow 2 Y := ⟨B', hB'2, fun {P} hP hle => hmax hP hle⟩
  obtain ⟨S, hQS⟩ := hQ'2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq Y SB S
  have hScoe : (S : Subgroup Y) = MulAut.conj h • (B' : Subgroup Y) := by
    rw [← hh, Sylow.coe_subgroup_smul]
  have hcardQ : Nat.card Q' = Nat.card B' := by
    rw [show Nat.card Q' = Nat.card ↥(B.map (MulAut.conj g).toMonoidHom) from
      card_subgroupOf_of_le hg, show Nat.card B' = Nat.card B from card_subgroupOf_of_le hBY]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hSc : Nat.card (S : Subgroup Y) = Nat.card B' := by
    rw [hScoe]
    exact Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hQeq : Q' = (S : Subgroup Y) := by
    refine Subgroup.eq_of_le_of_card_ge hQS ?_
    rw [hSc, hcardQ]
  obtain ⟨o, ho, b, hb, hhob⟩ := hdec h
  have ho' : (o : G) ∈ O := Subgroup.mem_subgroupOf.1 ho
  have hb' : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb
  have hhG : (h : G) = (o : G) * (b : G) := congrArg Subtype.val hhob
  have hle : B.map (MulAut.conj ((o : G)⁻¹ * g)).toMonoidHom ≤ B := by
    rintro _ ⟨z, hz, rfl⟩
    have hw : g * z * g⁻¹ ∈ Y := hg ⟨z, hz, by simp [MulAut.conj_apply]⟩
    have hw' : (⟨g * z * g⁻¹, hw⟩ : Y) ∈ Q' :=
      Subgroup.mem_subgroupOf.2 ⟨z, hz, by simp [MulAut.conj_apply]⟩
    rw [hQeq, hScoe, Subgroup.mem_smul_pointwise_iff_exists] at hw'
    obtain ⟨s, hs, hsw⟩ := hw'
    have hs' : (s : G) ∈ B := Subgroup.mem_subgroupOf.1 hs
    have hsw' : (h : G) * (s : G) * (h : G)⁻¹ = g * z * g⁻¹ := by
      have := congrArg Subtype.val hsw
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have key : ((o : G)⁻¹ * g) * z * ((o : G)⁻¹ * g)⁻¹ = (b : G) * (s : G) * (b : G)⁻¹ := by
      calc ((o : G)⁻¹ * g) * z * ((o : G)⁻¹ * g)⁻¹ = (o : G)⁻¹ * (g * z * g⁻¹) * (o : G) := by
            group
        _ = (o : G)⁻¹ * ((h : G) * (s : G) * (h : G)⁻¹) * (o : G) := by rw [hsw']
        _ = (b : G) * (s : G) * (b : G)⁻¹ := by rw [hhG]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [key]
    exact B.mul_mem (B.mul_mem hb' hs') (B.inv_mem hb')
  exact ⟨o, ho', Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj _).injective).ge⟩

end Sylow

theorem comm_of_isElementaryAbelian {G : Type} [Group G] {B : Subgroup G}
    (hB : CFSG.IsElementaryAbelian 2 ↥B) : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
  congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)

theorem cycFour_of_qShape3 {Kt : Type} [Group Kt] (h : QShape3 Kt) : S3.CycFour Kt := by
  obtain ⟨p, f, hp, hp2, hq, hL | hL⟩ := h
  · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data hL
    exact S3.CycFour.of_mulEquiv e.symm
      (S3.cycFour_psl (Ring.two_ne_zero (S3.ringChar_ne_two_of_card_pow hp hp2 hF)))
  · obtain ⟨-, hf, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data hL
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
      ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
    exact S3.CycFour.of_mulEquiv e.symm (S3.cycFour_psu hU hp2)

theorem mem_four_of_card {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE4 : Nat.card ↥E = 4) {a₀ y : G}
    (haE : a₀ ∈ E) (hyE : y ∈ E) (ha1 : a₀ ≠ 1) (hy1 : y ≠ 1) (hay : a₀ ≠ y)
    (hsq : ∀ e ∈ E, e * e = 1) {e : G} (he : e ∈ E) :
    e = 1 ∨ e = a₀ ∨ e = y ∨ e = a₀ * y := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨he1, hea, hey, heay⟩ := hne
  have hay1 : a₀ * y ≠ 1 := by
    intro h
    have h1 : y = a₀⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right (hsq a₀ haE)
    exact hay (h1.trans h2).symm
  have hay2 : a₀ * y ≠ a₀ := fun h => hy1 (mul_eq_left.1 h)
  have hay3 : a₀ * y ≠ y := fun h => ha1 (mul_eq_right.1 h)
  have hmul : a₀ * y ∈ E := E.mul_mem haE hyE
  let f : Fin 5 → ↥E := ![1, ⟨a₀, haE⟩, ⟨y, hyE⟩, ⟨a₀ * y, hmul⟩, ⟨e, he⟩]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, Subtype.ext_iff, eq_comm]
  have h5 : 5 ≤ Nat.card ↥E := by
    simpa using Nat.card_le_card_of_injective f hinj
  omega

end S3Sec29BNTrans

theorem ntrans_proved (G : Type) [Group G] [Finite G] : NTrans G := by
  classical
  intro x K A B E y a₀ hterm hQ3 hsrc hext hrank hEK hAE hEel hE4 hyE hy1 haE ha1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hterm.1.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK hQ3
  obtain ⟨hAB, hxB, hBC, hBel, -, -, hBeq⟩ := hext
  have hEp : IsPGroup 2 ↥E := CFSG.IsElementaryAbelian.isPGroup 2 ↥E
  have hBp : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := S3Sec29BNTrans.comm_of_isElementaryAbelian hBel
  have hEc : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a := S3Sec29BNTrans.comm_of_isElementaryAbelian hEel
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEB : E ≤ B := hEA.trans hAB
  have hxB0 : x ∈ B ⊓ cSec K := Subgroup.mem_inf.2 ⟨hxB, S3Ctx29.mem_cSec_of_le_centralizer hKC⟩
  have hBsup : B = E ⊔ (B ⊓ cSec K) := by
    calc B = A ⊔ (B ⊓ cSec K) := hBeq
      _ = E ⊔ zpowers x ⊔ (B ⊓ cSec K) := by rw [← hAE]
      _ = E ⊔ (B ⊓ cSec K) := by
        rw [sup_assoc, sup_eq_right.2 (Subgroup.zpowers_le.2 hxB0)]
  have hcomm : ∀ e ∈ E, ∀ c ∈ B ⊓ cSec K, e * c = c * e := fun e he c hc =>
    hBc e (hEB he) c (Subgroup.mem_inf.1 hc).1
  have hsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e he
    rwa [sq] at this
  have hBK : B ⊓ K = E := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzB, hzK⟩ := Subgroup.mem_inf.1 hz
      have hzm : z ∈ E ⊔ (B ⊓ cSec K) := hBsup ▸ hzB
      obtain ⟨e, he, c, hc, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hcomm hzm
      have hcK : c ∈ K := by
        have := K.mul_mem (K.inv_mem (hEK he)) hzK
        simpa using this
      have hc1 : c = 1 := S3Ctx29.eq_one_of_mem_cSec hZ (inf_le_right : B ⊓ K ≤ K)
        (hBp.to_le inf_le_left) (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc).1, hcK⟩)
        (Subgroup.mem_inf.1 hc).2
      rw [hc1, mul_one]
      exact he
    · exact le_inf hEB hEK
  by_cases hay : a₀ = y
  · exact ⟨1, ⟨⟨one_mem _, one_mem _⟩, one_mem _⟩, by simp [hay]⟩
  set π : ↥K →* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hπE : ∀ (e : G) (he : e ∈ E) (e' : G) (he' : e' ∈ E),
      π ⟨e, hEK he⟩ = π ⟨e', hEK he'⟩ → e = e' := by
    intro e he e' he' h
    have h1 : (⟨e, hEK he⟩ : ↥K)⁻¹ * ⟨e', hEK he'⟩ ∈ pPrimeCore 2 ↥K := QuotientGroup.eq.1 h
    have h2 : e⁻¹ * e' ∈ pPrimeCoreOf 2 K := ⟨_, h1, rfl⟩
    have h3 : e⁻¹ * e' = 1 :=
      S3Theta52.eq_one_of_mem_of_mem_pPrimeCoreOf hEp (mul_mem (inv_mem he) he') h2
    exact inv_mul_eq_one.1 h3
  set a' : ↥K := ⟨a₀, hEK haE⟩ with ha'
  set y' : ↥K := ⟨y, hEK hyE⟩ with hy'
  have ha2 : a' * a' = 1 := Subtype.ext (hsq a₀ haE)
  have hy2 : y' * y' = 1 := Subtype.ext (hsq y hyE)
  have hay' : a' * y' = y' * a' := Subtype.ext (hEc a₀ haE y hyE)
  have hπ1 : ∀ (e : G) (he : e ∈ E), π ⟨e, hEK he⟩ = 1 → e = 1 := by
    intro e he h
    have h1 : (⟨e, hEK he⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h
    exact S3Theta52.eq_one_of_mem_of_mem_pPrimeCoreOf hEp he ⟨_, h1, rfl⟩
  set ua : ↥K ⧸ pPrimeCore 2 ↥K := π a' with hua
  set ub : ↥K ⧸ pPrimeCore 2 ↥K := π y' with hub
  have hua2 : ua * ua = 1 := by rw [hua, ← map_mul, ha2, map_one]
  have hub2 : ub * ub = 1 := by rw [hub, ← map_mul, hy2, map_one]
  have huab : ua * ub = ub * ua := by rw [hua, hub, ← map_mul, ← map_mul, hay']
  have hua1 : ua ≠ 1 := fun h => ha1 (hπ1 a₀ haE h)
  have hub1 : ub ≠ 1 := fun h => hy1 (hπ1 y hyE h)
  have huab' : ua ≠ ub := fun h => hay (hπE a₀ haE y hyE h)
  obtain ⟨c, hc1, hc2⟩ := S3Sec29BNTrans.cycFour_of_qShape3 hQ3 ua ub hua2 hub2 huab hua1 hub1 huab'
  have hcb : c⁻¹ * ua * c = ub := by rw [← hc2]; group
  have hcabab : c⁻¹ * (ua * ub) * c = ua := by rw [← hc1]; group
  have hcab : c⁻¹ * ub * c = ua * ub := by
    have h2 : c⁻¹ * (ua * ub) * c = (c⁻¹ * ua * c) * (c⁻¹ * ub * c) := by group
    rw [h2, hcb] at hcabab
    have hubinv : ub⁻¹ = ub := inv_eq_of_mul_eq_one_right hub2
    calc c⁻¹ * ub * c = ub⁻¹ * (ub * (c⁻¹ * ub * c)) := by group
      _ = ub⁻¹ * ua := by rw [hcabab]
      _ = ua * ub := by rw [hubinv, huab.symm]
  obtain ⟨g₀', hg₀'⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) c⁻¹
  have hg₀'π : π g₀' = c⁻¹ := hg₀'
  set g₀ : G := (g₀' : G) with hg₀
  have hg₀K : g₀ ∈ K := g₀'.2
  have hπconj : ∀ k : ↥K, π (g₀' * k * g₀'⁻¹) = c⁻¹ * π k * c := by
    intro k
    rw [map_mul, map_mul, map_inv, hg₀'π, inv_inv]
  have hconjE : ∀ (e : G) (he : e ∈ E), ∃ (e' : G) (he' : e' ∈ E),
      π (g₀' * ⟨e, hEK he⟩ * g₀'⁻¹) = π ⟨e', hEK he'⟩ := by
    intro e he
    have hk1 : (⟨1, hEK (one_mem E)⟩ : ↥K) = 1 := rfl
    have hyy : (⟨a₀ * y, hEK (E.mul_mem haE hyE)⟩ : ↥K) = a' * y' := rfl
    rcases S3Sec29BNTrans.mem_four_of_card hE4 haE hyE ha1 hy1 hay hsq he with
      h1 | h1 | h1 | h1
    · have hk : (⟨e, hEK he⟩ : ↥K) = 1 := Subtype.ext h1
      refine ⟨1, one_mem E, ?_⟩
      rw [hk, hk1]
      simp
    · have hk : (⟨e, hEK he⟩ : ↥K) = a' := Subtype.ext h1
      refine ⟨y, hyE, ?_⟩
      rw [hk, hπconj]
      exact hcb
    · have hk : (⟨e, hEK he⟩ : ↥K) = y' := Subtype.ext h1
      refine ⟨a₀ * y, E.mul_mem haE hyE, ?_⟩
      rw [hk, hπconj, hyy, map_mul]
      exact hcab
    · have hk : (⟨e, hEK he⟩ : ↥K) = a' * y' := Subtype.ext h1
      refine ⟨a₀, haE, ?_⟩
      rw [hk, hπconj, map_mul]
      exact hcabab
  have hgE : ∀ e ∈ E, g₀ * e * g₀⁻¹ ∈ B ⊔ pPrimeCoreOf 2 K := by
    intro e he
    obtain ⟨e', he', h⟩ := hconjE e he
    have h1 : (⟨e', hEK he'⟩ : ↥K)⁻¹ * (g₀' * ⟨e, hEK he⟩ * g₀'⁻¹) ∈ pPrimeCore 2 ↥K :=
      QuotientGroup.eq.1 h.symm
    have h2 : e'⁻¹ * (g₀ * e * g₀⁻¹) ∈ pPrimeCoreOf 2 K := ⟨_, h1, rfl⟩
    have h3 : g₀ * e * g₀⁻¹ = e' * (e'⁻¹ * (g₀ * e * g₀⁻¹)) := by group
    rw [h3]
    exact mul_mem (Subgroup.mem_sup_left (hEB he')) (Subgroup.mem_sup_right h2)
  have hgB0 : ∀ c ∈ B ⊓ cSec K, g₀ * c * g₀⁻¹ ∈ B ⊔ pPrimeCoreOf 2 K := by
    intro c hc
    have h1 : ⁅g₀, c⁆ ∈ pPrimeCoreOf 2 K := (Subgroup.mem_inf.1 hc).2.2.2 g₀ hg₀K
    have h3 : g₀ * c * g₀⁻¹ = ⁅g₀, c⁆ * c := by
      simp only [commutatorElement_def]
      group
    rw [h3]
    exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left (Subgroup.mem_inf.1 hc).1)
  have hmapBO : B.map (MulAut.conj g₀).toMonoidHom ≤ B ⊔ pPrimeCoreOf 2 K := by
    rw [Subgroup.map_le_iff_le_comap]
    calc B = E ⊔ (B ⊓ cSec K) := hBsup
      _ ≤ (B ⊔ pPrimeCoreOf 2 K).comap (MulAut.conj g₀).toMonoidHom :=
        sup_le (fun e he => by simpa [MulAut.conj_apply] using hgE e he)
          (fun c hc => by simpa [MulAut.conj_apply] using hgB0 c hc)
  have hBNK : B ≤ normalizer (K : Set G) := by
    calc B = E ⊔ (B ⊓ cSec K) := hBsup
      _ ≤ normalizer (K : Set G) :=
        sup_le (fun e he => Subgroup.le_normalizer (hEK he))
          (fun c hc => (Subgroup.mem_inf.1 hc).2.1)
  have hBN : B ≤ normalizer (pPrimeCoreOf 2 K : Set G) := fun b hb =>
    TwoThin.mem_normalizer_pPrimeCoreOf (hBNK hb)
  obtain ⟨o, hoO, hnB⟩ := S3Sec29BNTrans.exists_o_normalizing hBN
    (TwoThin.card_pPrimeCoreOf_odd K) hBp hmapBO
  obtain ⟨o', ho', hoo'⟩ := hoO
  set g' : ↥K := o'⁻¹ * g₀' with hg'
  have hgg' : (g' : G) = o⁻¹ * g₀ := by
    rw [hg', ← hoo']
    rfl
  set g : G := o⁻¹ * g₀ with hg
  have hgK : g ∈ K := by rw [← hgg']; exact g'.2
  have hgNB : g ∈ normalizer (B : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.2 hnB
  have hgNE : g ∈ normalizer (E : Set G) := by
    have h1 : g ∈ normalizer (B : Set G) ⊓ normalizer (K : Set G) :=
      Subgroup.mem_inf.2 ⟨hgNB, Subgroup.le_normalizer hgK⟩
    have h2 := Subgroup.inf_normalizer_le_normalizer_inf h1
    rwa [hBK] at h2
  have hgx : g * x * g⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKC hgK)
    rw [this]
    group
  have hgNA : g ∈ normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    rw [hAE, Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.1 hgNE,
      MonoidHom.map_zpowers]
    show E ⊔ zpowers (g * x * g⁻¹) = E ⊔ zpowers x
    rw [hgx]
  refine ⟨g, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgK, hgNA⟩, hgNB⟩, ?_⟩
  have hE' : g * a₀ * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hgNE a₀).1 haE
  have hπg : π g' = c⁻¹ := by
    have hπo : π o' = 1 := (QuotientGroup.eq_one_iff o').2 ho'
    rw [hg', map_mul, map_inv, hπo, inv_one, one_mul, hg₀'π]
  have h1 : π ⟨g * a₀ * g⁻¹, hEK hE'⟩ = π y' := by
    have : (⟨g * a₀ * g⁻¹, hEK hE'⟩ : ↥K) = g' * a' * g'⁻¹ := by
      apply Subtype.ext
      simp [hgg', ha']
    rw [this, map_mul, map_mul, map_inv, hπg, inv_inv, ← hua]
    exact hcb
  exact hπE _ hE' y hyE h1

end CFSG.GH74.Generic.BProg.B3
