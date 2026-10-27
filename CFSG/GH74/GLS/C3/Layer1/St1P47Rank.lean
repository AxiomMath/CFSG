module

public import CFSG.GH74.GLS.C3.Layer1.BkGen4L34
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GH74.GLS.C3.Layer1.St1P89Tools
public import CFSG.GH74.GLS.IVK.Proofs2.C3RankAdd
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.GH74.GLS.C3.Layer1.P47

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.ABGLocalTools CFSG.GH74.Uniqueness.SU.SU1 CFSG.GH74.GLS.IVK.Proofs2

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_klein (K : Subgroup G) (V : Subgroup (kBar K))
    (hVsq : ∀ v ∈ V, v * v = 1) (hV4 : 4 ∣ Nat.card ↥V) :
    ∃ P : Subgroup G, P ≤ K ∧ (∀ e ∈ P, e * e = 1) ∧ 4 ∣ Nat.card ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set YK : Subgroup ↥K := pPrimeCore 2 ↥K with hYK
  set π : ↥K →* kBar K := QuotientGroup.mk' YK with hπ
  set Y : Subgroup G := pPrimeCoreOf 2 K with hY
  set EK : Subgroup ↥K := V.comap π with hEK
  set E : Subgroup G := EK.map K.subtype with hE
  have hπker : ∀ k : ↥K, π k = 1 ↔ k ∈ YK := fun k => QuotientGroup.eq_one_iff k
  have hYmem : ∀ z : ↥K, (z : G) ∈ Y ↔ z ∈ YK := fun z =>
    Subgroup.mem_map_iff_mem K.subtype_injective
  have hYcop : Nat.Coprime 2 (Nat.card ↥Y) := by
    have h1 : Nat.card ↥Y = Nat.card ↥YK := Subgroup.card_map_of_injective K.subtype_injective
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := ↥K)
  have hEK_mem : ∀ k : ↥K, k ∈ EK ↔ π k ∈ V := fun k => Iff.rfl
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨P, hPE, hPp, hPcard, -⟩ := exists_normalized_sylow_two E ⊥ hbot bot_le
  have hEK_le : E ≤ K := Subgroup.map_subtype_le _
  have hPK : P ≤ K := hPE.trans hEK_le
  have h4E : 2 ^ 2 ∣ Nat.card ↥E := by
    have h1 : Nat.card ↥E = Nat.card ↥EK := Subgroup.card_map_of_injective K.subtype_injective
    have h2 : EK.map π = V :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) V
    have h3 : Nat.card ↥(EK.map π) ∣ Nat.card ↥EK := Subgroup.card_map_dvd EK π
    rw [h2] at h3
    rw [h1]
    exact (by norm_num : 2 ^ 2 ∣ 4).trans (hV4.trans h3)
  have hm2 : 2 ≤ (Nat.card ↥E).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h4E
  refine ⟨P, hPK, ?_, ?_⟩
  · intro e he
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 (hPE he)
    have hk2 : π (k * k) = 1 := by
      rw [map_mul]
      exact hVsq _ ((hEK_mem k).1 hk)
    have hkk : ((k * k : ↥K) : G) ∈ Y := (hYmem _).2 ((hπker _).1 hk2)
    exact eq_one_of_mem_of_coprime hYcop hPp (by simpa using hkk) (P.mul_mem he he)
  · rw [← hPcard]
    exact (by norm_num : (4 : ℕ) = 2 ^ 2) ▸ pow_dvd_pow 2 hm2

end Lift

section Main

variable {G : Type} [Group G] [Finite G]

theorem x_not_mem_of_le {x : G} {K P : Subgroup G} (hpair : IsIL2Pair x K)
    (hZ : ∀ z : kBar K, (∀ w : kBar K, z * w = w * z) → z = 1) (hPK : P ≤ K) : x ∉ P := by
  intro hxP
  have hx2 : orderOf x = 2 := hpair.1
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  have hKX : K ≤ centralizer ({x} : Set G) := hpair.2.1
  have hxK : x ∈ K := hPK hxP
  have hcentral : ∀ w : kBar K, (QuotientGroup.mk ⟨x, hxK⟩ : kBar K) * w =
      w * QuotientGroup.mk ⟨x, hxK⟩ := by
    intro w
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.1 (hKX k'.2)).symm
  have h1 : (QuotientGroup.mk ⟨x, hxK⟩ : kBar K) = 1 := hZ _ hcentral
  have h2 : (⟨x, hxK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : x ∈ pPrimeCoreOf 2 K := ⟨⟨x, hxK⟩, h2, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 ↥(zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx2]; norm_num)
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCoreOf 2 K)) :=
    Nat.coprime_two_left.mpr (TwoThin.card_pPrimeCoreOf_odd K)
  exact hx1 (eq_one_of_mem_of_coprime hcop hxp h3 (Subgroup.mem_zpowers x))

omit [Finite G] in
theorem zpowers_sup_facts {x : G} {P : Subgroup G} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hPX : P ≤ centralizer ({x} : Set G)) (hPsq : ∀ e ∈ P, e * e = 1) (hxP : x ∉ P) :
    (∀ u ∈ zpowers x, ∀ v ∈ P, u * v = v * u) ∧ (∀ q ∈ zpowers x ⊔ P, q * q = 1) ∧
      Nat.card ↥(zpowers x ⊔ P) = 2 * Nat.card ↥P := by
  have hsq : x ^ 2 = 1 := by rw [sq]; exact hx
  have hcomm : ∀ u ∈ zpowers x, ∀ v ∈ P, u * v = v * u := by
    intro u hu v hv
    have hxv : x * v = v * x := (mem_centralizer_singleton_iff.1 (hPX hv)).symm
    rcases P89.mem_zpowers_of_sq hsq hu with h | h
    · rw [h]; simp
    · rw [h]; exact hxv
  refine ⟨hcomm, ?_, ?_⟩
  · intro q hq
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_commute hcomm hq
    have huu : u * u = 1 := by
      rcases P89.mem_zpowers_of_sq hsq hu with h | h
      · rw [h]; simp
      · rw [h]; exact hx
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← hcomm u hu v hv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [huu, hPsq v hv, one_mul]
  · have hinf : zpowers x ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨hg1, hg2⟩
      rcases P89.mem_zpowers_of_sq hsq hg1 with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h] at hg2; exact absurd hg2 hxP
    rw [P89.card_sup_of_commute hcomm hinf, P89.card_zpowers_two hsq hx1]

theorem center_kBar_eq_bot
    (hL34 : B_gen4_noL34_elem) (hG : Gen4 G) {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (hU2 : InU2 (kBar K)) : center (kBar K) = ⊥ := by
  obtain ⟨hq, hcls⟩ := hU2
  rcases hcls with hA | hB | hC
  · obtain ⟨p, f, hp, hf, hodd, hL⟩ := hA
    have hs : IsSimpleGroup (kBar K) :=
      (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
    exact center_eq_bot_of_simple_quasisimple hs hq
  · have hs : IsSimpleGroup (kBar K) := by
      obtain ⟨e⟩ := hB
      have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    exact center_eq_bot_of_simple_quasisimple hs hq
  · exact (hL34 G hG x K hpair.1 hpair.2 hC).elim

theorem mem_normalizer_of_mem_centralizer
    (hL34 : B_gen4_noL34_elem) (hG : C3Hyp G) {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (hU2 : InU2 (kBar K)) {a : G} (haX : a ∈ centralizer ({x} : Set G)) :
    a ∈ normalizer (K : Set G) := by
  by_contra haN
  have hx2 : orderOf x = 2 := hpair.1
  have hxsq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  have hKX : K ≤ centralizer ({x} : Set G) := hpair.2.1
  have hax : a * x = x * a := mem_centralizer_singleton_iff.1 haX
  have hK' : cmap a K ≠ K := fun h => haN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hcX' : cmap a (centralizer ({x} : Set G)) = centralizer ({x} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer haX)
  have hK'c : IsPCompIn 2 (centralizer ({x} : Set G)) (cmap a K) := by
    have := isPCompIn_cmap hpair.2 a
    rwa [hcX'] at this
  have hsec : cmap a K ≤ cSec K := le_cSec_of_ne hK'c hpair.2 hK'
  have hq : CFSG.IsQuasisimple (kBar K) := hU2.1
  have hcen : center (kBar K) = ⊥ := center_kBar_eq_bot hL34 hG.gen4 hpair hU2
  have hZ : ∀ z : kBar K, (∀ w : kBar K, z * w = w * z) → z = 1 := by
    intro z hz
    have : z ∈ center (kBar K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hz g).symm
    rw [hcen, Subgroup.mem_bot] at this
    exact this
  obtain ⟨V, hVel, hV4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
      (by rw [hcen, Subgroup.card_bot]; exact odd_one))
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := (isElemAbelian_iff.1 hVel).2 v hv
    rwa [sq] at this
  obtain ⟨P, hPK, hPsq, hP4⟩ := exists_lift_klein K V hVsq (by rw [hV4])
  set P' : Subgroup G := cmap a P with hP'
  have hP'K' : P' ≤ cmap a K := Subgroup.map_mono hPK
  have hP'X : P' ≤ centralizer ({x} : Set G) := hP'K'.trans ((Subgroup.map_mono hKX).trans hcX'.le)
  have hP'sq : ∀ e ∈ P', e * e = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    have := hPsq p hp
    show a * p * a⁻¹ * (a * p * a⁻¹) = 1
    calc a * p * a⁻¹ * (a * p * a⁻¹) = a * (p * p) * a⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hP'card : 4 ∣ Nat.card ↥P' := by
    rw [hP', cmap, Subgroup.card_map_of_injective (MulAut.conj a).injective]
    exact hP4
  have hxP' : x ∉ P' := by
    intro hxP'
    have hxP : x ∈ P := by
      have h1 : a⁻¹ * x * a ∈ P := mem_cmap.1 hxP'
      have e : a⁻¹ * x * a = x := by
        calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
          _ = a⁻¹ * (a * x) := by rw [hax]
          _ = x := by group
      rwa [e] at h1
    exact x_not_mem_of_le hpair hZ hPK hxP
  obtain ⟨hcommB, hBsq, hBcard⟩ := zpowers_sup_facts hxsq hx1 hP'X hP'sq hxP'
  set B : Subgroup G := zpowers x ⊔ P' with hB
  have hBea : CFSG.IsElementaryAbelian 2 ↥B := isElementaryAbelian_two_of_mul_self B hBsq
  have hxsecK : x ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    Back.mem_centralizerSection_of_centralizes
      (fun k hk => (mem_centralizer_singleton_iff.1 (hKX hk)).symm) (TwoThin.pPrimeCoreOf_le K)
  have hBsec : B ≤ centralizerSection K (pPrimeCoreOf 2 K) :=
    sup_le ((Subgroup.zpowers_le).2 hxsecK) (hP'K'.trans hsec)
  obtain ⟨m, Q, hm2, hQsq, hQcard⟩ := exists_big_elemAbelian K B hBea hBsec V hVsq
    (by rw [hV4]) hZ
  have hQea : CFSG.IsElementaryAbelian 2 ↥Q := isElementaryAbelian_two_of_mul_self Q hQsq
  have hBpg : IsPGroup 2 ↥B := by
    have := hBea
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  obtain ⟨j, hj⟩ := hBpg.exists_card_eq
  have hP'ge : 4 ≤ Nat.card ↥P' := Nat.le_of_dvd Nat.card_pos hP'card
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have hlt' : j < 3 := not_le.mp hlt
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrank := le_pRank_group_of_elem hQea (k := j + m) (by rw [hQcard, hj, pow_add])
  have h4 := hG.pRank_eq_four
  omega

theorem b_iv2_4_7_of
    (hL34 : B_gen4_noL34_elem) : B_iv2_4_7 := by
  intro G _ _ hG x K hpair hU2 A hA hxA a haA
  exact mem_normalizer_of_mem_centralizer hL34 hG hpair hU2
    (mem_centralizer_singleton_iff.2 (hA.commute haA hxA))

theorem b_iv2_4_7_proved :
    B_iv2_4_7 :=
  b_iv2_4_7_of C3.Layer1.Bk.b_gen4_noL34_elem_proof

end Main

end CFSG.GH74.GLS.C3.Layer1.P47
