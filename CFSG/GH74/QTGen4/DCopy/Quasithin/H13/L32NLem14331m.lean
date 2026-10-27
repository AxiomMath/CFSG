module

public import CFSG.Quasithin.H13.L32NLem14331m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem caseI_oTwoUpper_le_F4 (Xc : CaseI_F4 T L V g D e) {X : Subgroup G}
    (hXI : X ≤ iKP T L V l e) (eX : Nonempty (↥X ⧸ CFSG.Open.pCore 2 ↥X ≃* Equiv.Perm (Fin 3)))
    {K₀ : Subgroup ↥(iKP T L V l e)} (hK₀ : K₀ ∈ cComp (⊤ : Subgroup ↥(iKP T L V l e)))
    (hK₀O : K₀.map (piQ T L V l e) = oTwoUpper (⊤ : Subgroup (dQ T L V l e))) :
    oTwoUpper X ≤ K₀.map (iKP T L V l e).subtype := by
  obtain ⟨eX⟩ := eX
  have htriple := C.caseI_triple_F4 D Xc
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxX, hxo⟩
  have hx3 := pow_three_of_odd_sub eX hxX hxo
  have hxI := hXI hxX
  have hx3' : (⟨x, hxI⟩ : ↥(iKP T L V l e)) ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hx3)
  have hπ : piQ T L V l e ⟨x, hxI⟩ ∈ K₀.map (piQ T L V l e) := by
    rw [hK₀O]
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top _)
      (Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ?_))
    rw [← map_pow, show (⟨x, hxI⟩ : ↥(iKP T L V l e)) ^ 3 = 1 by simpa using hx3', map_one]
  exact ⟨⟨x, hxI⟩, A5.mem_of_pow_three_of_mem_map htriple.isSolvable_pPrimeCore hK₀ hx3' hπ, rfl⟩

theorem caseI_index_F4 (h1434 : Lemma1434One_F4) (Xc : CaseI_F4 T L V g D e)
    (hq : CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup (dQ T L V l e))))
    (hAm : IsGoldschmidtAmalgam (g1bar T L V l e) (g2bar T L V l e)) :
    ∃ m : ℕ, (m = 15 ∨ m = 21) ∧
      3 * Nat.card ↥(iKP T L V l e) = m * Nat.card ↥(kT T V l e) ∧
      3 * Nat.card ↥(iKP T L V l e) = m * Nat.card ↥(p128 T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := iKP T L V l e with hI
  set π := piQ T L V l e with hπ
  set Y := CFSG.pPrimeCore 3 ↥I with hY
  have htriple := C.caseI_triple_F4 D Xc
  have hO2n : (oTwoUpper (⊤ : Subgroup (dQ T L V l e))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_oTwoUpper ⊤))
  have hKbc : oTwoUpper (⊤ : Subgroup (dQ T L V l e)) ∈ cComp (⊤ : Subgroup (dQ T L V l e)) :=
    mem_cComp_top_of_isComponent ⟨hq, hO2n.isSubnormal⟩
  obtain ⟨K₀, hK₀, hK₀O⟩ := (cComp_quotient_bijOn Y htriple.isSolvable_pPrimeCore).2.2 hKbc
  have hK₀n : K₀.Normal := normal_of_mem_cComp htriple.isSolvable_pPrimeCore hK₀ (hK₀O ▸ hO2n)
  set K₀G := K₀.map I.subtype with hK₀G
  have hKTI : kT T V l e ≤ I := le_sup_left
  have hPI : p128 T L V ≤ I := le_sup_right
  have hKT0 := C.caseI_oTwoUpper_le_F4 D Xc hKTI (C.caseI_quotient_KT_F4 D Xc) hK₀ hK₀O
  have hP0 := C.caseI_oTwoUpper_le_F4 D Xc hPI (C.quotient_P_F4 Xc.h1222) hK₀ hK₀O

  have hZ : ⁅quasithinOmegaOneCenter T, K₀G⁆ ≠ ⊥ := by
    obtain ⟨k, hk, hkz, -, -⟩ := L128P.exists_rotation_mem_F4 Xc.h1222 C.setting.hyp C.setting.v1
      C.setting.v2 C.setting.le C.z_mem C.z_ne C.a_mem_F4 C.a_nmem_F4
    intro hb
    have hzZ : z ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.mp C.z_mem).2
    have h1 := Subgroup.commutator_mem_commutator hzZ (hP0 hk)
    rw [hb, Subgroup.mem_bot, commutatorElement_def] at h1
    apply C.a_nmem_F4
    have h2 : k * z * k⁻¹ = z := by
      calc k * z * k⁻¹ = (z * k * z⁻¹ * k⁻¹)⁻¹ * z := by group
        _ = z := by rw [h1, inv_one, one_mul]
    rw [← hkz, h2]
    exact C.z_mem
  obtain ⟨hs, hcard⟩ := C.caseI_K0_simple_F4 D h1434 Xc hK₀ hZ
  have h3dvd : 3 ∣ Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) := by
    rcases hcard with h | h <;> rw [h] <;> norm_num

  have hT2 : IsPGroup 2 ↥T := C.S.hH.sylow.1
  have hTN : T ≤ Subgroup.normalizer (K₀G : Set G) := by
    intro t ht
    have htI : t ∈ I := (le_sup_right.trans le_sup_left : T ≤ I) ht
    refine mem_normalizer_of_maps fun w hw => ?_
    obtain ⟨w', hw', rfl⟩ := hw
    exact ⟨⟨t, htI⟩ * w' * ⟨t, htI⟩⁻¹, hK₀n.conj_mem w' hw' _, rfl⟩
  have hIle : I ≤ K₀G ⊔ T := by
    have hKT' : kT T V l e = oTwoUpper (kT T V l e) ⊔ T :=
      eq_oTwoUpper_sup_of_isSylowTwoOf' (A5.isSylowTwoOf_of_le C.S.hH.sylow le_sup_right)
    have hP' : p128 T L V = oTwoUpper (p128 T L V) ⊔ T :=
      eq_oTwoUpper_sup_of_isSylowTwoOf' (A5.isSylowTwoOf_of_le C.S.hH.sylow L128P.le_p128)
    refine sup_le ?_ ?_
    · rw [hKT']
      exact sup_le_sup_right hKT0 T
    · rw [hP']
      exact sup_le_sup_right hP0 T

  have hle := subgroupOf_le_pCore_of_simple CFSG.pPrimeCore_coprime_card K₀ hs h3dvd
  have hY2 : IsPGroup 2 ↥Y := by
    have hodd : ∀ y' ∈ Y, Odd (orderOf y') → y' = 1 := by
      intro y' hy' hyo
      have hyo' : Odd (orderOf (y' : G)) := by rwa [Subgroup.orderOf_coe]
      obtain ⟨y'', hy'', hy''e⟩ :=
        mem_of_odd_of_mem_sup hT2 hTN (hIle y'.2) hyo' (pow_orderOf_eq_one _)
      have hyy : y'' = y' := Subtype.ext hy''e
      subst hyy
      have hmem : (⟨y'', hy''⟩ : ↥K₀) ∈ Y.subgroupOf K₀ := hy'
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K₀) 2 ⟨_, hle hmem⟩
      have hn' : y'' ^ 2 ^ n = 1 := by
        have := congrArg (fun x => ((x : ↥K₀) : ↥I)) (congrArg Subtype.val hn)
        simpa using this
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hyo)) (orderOf_dvd_of_pow_eq_one hn')
        dvd_rfl)
    intro y'
    obtain ⟨n, hn⟩ := exists_two_pow_of_odd hodd y'.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

  have hYO : Y ≤ CFSG.Open.pCore 2 ↥I := CFSG.LieType.BorelTits.le_pCore 2 inferInstance hY2
  have hYKT : Y ≤ (kT T V l e).subgroupOf I := by
    intro y hy
    have := hYO hy
    rw [← F6.inf_pPrimeCore_eq_pCore_left htriple.subgroupOf] at this
    exact this.1
  have hYP : Y ≤ (p128 T L V).subgroupOf I := by
    intro y hy
    have := hYO hy
    rw [← F6.inf_pPrimeCore_eq_pCore_right htriple.subgroupOf] at this
    exact this.1

  obtain ⟨b', hb'⟩ := card_map_of_simple CFSG.pPrimeCore_coprime_card K₀ hs h3dvd
  rw [hK₀O] at hb'
  obtain ⟨m, c, hm, hmo, hO⟩ : ∃ m c : ℕ, (m = 15 ∨ m = 21) ∧ Odd m ∧
      Nat.card ↥(oTwoUpper (⊤ : Subgroup (dQ T L V l e))) = m * 2 ^ c := by
    rcases hcard with h | h
    · exact ⟨15, b' + 2, Or.inl rfl, by decide, by rw [hb', h, pow_add]; ring⟩
    · exact ⟨21, b' + 3, Or.inr rfl, by decide, by rw [hb', h, pow_add]; ring⟩

  obtain ⟨S, hS⟩ := hAm.sylow
  have hS2 : IsPGroup 2 ↥(g1bar T L V l e ⊓ g2bar T L V l e) := hS ▸ S.isPGroup'
  have hSi : ¬ 2 ∣ (g1bar T L V l e ⊓ g2bar T L V l e).index := hS ▸ S.not_dvd_index
  have hsyl : IsSylowTwoOf (g1bar T L V l e ⊓ g2bar T L V l e) ⊤ :=
    ⟨le_top, hS2, by rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right]⟩
  have hDsup : oTwoUpper (⊤ : Subgroup (dQ T L V l e)) ⊔ (g1bar T L V l e ⊓ g2bar T L V l e) = ⊤ :=
    (eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl).symm
  have hD := card_eq_odd_mul hO2n hS2 hSi hDsup hmo hO

  have hG1 : Nat.card ↥(g1bar T L V l e) = 3 * Nat.card ↥(g1bar T L V l e ⊓ g2bar T L V l e) := by
    have h1 := hAm.toIsGoldschmidtTriple.relIndex_inf_left
    have h2 := Subgroup.relIndex_mul_card (g1bar T L V l e ⊓ g2bar T L V l e) (g1bar T L V l e)
    rw [h1, inf_of_le_left inf_le_left] at h2
    exact h2.symm
  have hG2 : Nat.card ↥(g2bar T L V l e) = 3 * Nat.card ↥(g1bar T L V l e ⊓ g2bar T L V l e) := by
    have h1 := hAm.toIsGoldschmidtTriple.relIndex_inf_right
    have h2 := Subgroup.relIndex_mul_card (g1bar T L V l e ⊓ g2bar T L V l e) (g2bar T L V l e)
    rw [h1, inf_of_le_left inf_le_right] at h2
    exact h2.symm

  have hIc : Nat.card ↥I = Nat.card (dQ T L V l e) * Nat.card ↥Y :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Y
  have hX : ∀ {X : Subgroup G} (hXI : X ≤ I), Y ≤ X.subgroupOf I →
      Nat.card ↥X = Nat.card ↥((X.subgroupOf I).map π) * Nat.card ↥Y := by
    intro X hXI hYX
    rw [F6.card_map_mk, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXI).toEquiv,
      ← Subgroup.relIndex_mul_card Y (X.subgroupOf I), inf_of_le_left hYX]
  have hKTc := hX hKTI hYKT
  have hPc := hX hPI hYP
  refine ⟨m, hm, ?_, ?_⟩
  · rw [hKTc, hIc, hD]
    change 3 * (m * Nat.card ↥(g1bar T L V l e ⊓ g2bar T L V l e) * Nat.card ↥Y) =
      m * (Nat.card ↥(g1bar T L V l e) * Nat.card ↥Y)
    rw [hG1]
    ring
  · rw [hPc, hIc, hD]
    change 3 * (m * Nat.card ↥(g1bar T L V l e ⊓ g2bar T L V l e) * Nat.card ↥Y) =
      m * (Nat.card ↥(g2bar T L V l e) * Nat.card ↥Y)
    rw [hG2]
    ring

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
