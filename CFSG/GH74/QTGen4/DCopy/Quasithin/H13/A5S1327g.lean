module

public import CFSG.Quasithin.H13.A5S1327g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327dS331

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Final1327CaseThree_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 (S.H0 H) ≠ ⊥ →
    ¬ ThreeTop (S.H0 H) → F6.IsF618CaseThree (S.G1bar H) (S.G2bar H) → False

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem false_of_caseOne_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) (hQ1 : pCoreOf 2 (S.G1bar H) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have htriple := S.triple_of_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer_F4 h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  set I := S.H0 H with hI
  set N3 := CFSG.pPrimeCore 3 ↥I with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hTI : T ≤ I := hTH.trans le_sup_right
  have hR1G1 : S.R1 ≤ S.L1 ⊔ T := S.R1_le_T.trans le_sup_right
  set R1b := (S.R1.subgroupOf I).map π with hR1b
  have hR1b_le : R1b ≤ S.G1bar H := Subgroup.map_mono (Subgroup.comap_mono hR1G1)
  have hG1R1b : S.G1bar H ≤ Subgroup.normalizer (R1b : Set (↥I ⧸ N3)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine A4.mem_normalizer_of_conj_mem ?_
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨g * r * g⁻¹, ?_, by simp only [map_mul, map_inv]; rfl⟩
    show ((g * r * g⁻¹ : ↥I) : G) ∈ S.R1
    have := (Subgroup.mem_normalizer_iff.mp (S.L1T_le_normalizer_R1 hg) r).mp hr
    simpa using this
  have hR1b2 : IsPGroup 2 ↥R1b :=
    (A4.isPGroup_subgroupOf_of_le (S.R1_le_T.trans hTI) (S.isPGroup_T.to_le S.R1_le_T)).map _
  have hR1b_bot : R1b = ⊥ := by
    have := le_pCoreOf_of_le_normalizer hR1b_le hG1R1b hR1b2
    rw [hQ1] at this
    exact le_bot_iff.mp this

  have hR1O2 : S.R1 ≤ pCoreOf 2 I := by
    intro r hr
    have hrI : r ∈ I := hTI (S.R1_le_T hr)
    have hrN3 : (⟨r, hrI⟩ : ↥I) ∈ N3 := by
      have : π ⟨r, hrI⟩ ∈ R1b := ⟨⟨r, hrI⟩, hr, rfl⟩
      rw [hR1b_bot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    exact S.mem_pCoreOf_H0_of_mem_pPrimeCore hTH htriple (S.R1_le_T hr) hrI hrN3
  have heq : S.R1 = pCoreOf 2 I := le_antisymm hR1O2 (S.pCoreOf_H0_le_R1 hTH hjT hjN hj)

  obtain ⟨-, hJR1, -⟩ := S.lemma_13_2_4_one
  have hHN : H ≤ Subgroup.normalizer (S.R1 : Set G) := by
    rw [heq]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 I)
  have hNJ : Subgroup.normalizer (thompsonJ S.R1 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [hJR1]
    exact S.normalizer_thompsonJ_Q_le
  exact hH.2.1 ((hHN.trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)).trans hNJ)

theorem P_le_R1_of_dihedral_F4 (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) (e : ↥(S.G2bar H) ≃* DihedralGroup 12) :
    pCoreOf 2 H ⊓ oTwoUpper H ≤ S.R1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have htriple := S.triple_of_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer_F4 h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  set I := S.H0 H with hI
  set N3 := CFSG.pPrimeCore 3 ↥I with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hHI : H ≤ I := le_sup_right

  set ψ : ↥H →* ↥(S.G2bar H) :=
    (π.comp (Subgroup.inclusion hHI)).codRestrict (S.G2bar H)
      (fun h => ⟨Subgroup.inclusion hHI h, h.2, rfl⟩) with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  intro x hx
  have hxT : x ∈ T := pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH) hx.1
  have hxH : x ∈ H := hTH hxT

  have hxO : (⟨x, hxH⟩ : ↥H) ∈ oTwoUpper (⊤ : Subgroup ↥H) := by
    have h1 : x ∈ (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := by
      rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hx.2
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = ⟨x, hxH⟩ := Subtype.ext hyx
    rwa [this] at hy

  have hψO : ψ ⟨x, hxH⟩ ∈ oTwoUpper (⊤ : Subgroup ↥(S.G2bar H)) := by
    rw [← Subgroup.map_top_of_surjective ψ hψs, oTwoUpper_map]
    exact ⟨_, hxO, rfl⟩
  have heO : e (ψ ⟨x, hxH⟩) ∈ oTwoUpper (⊤ : Subgroup (DihedralGroup 12)) := by
    rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, oTwoUpper_map]
    exact ⟨_, hψO, rfl⟩
  have h3' : ψ ⟨x, hxH⟩ ^ 3 = 1 := by
    have h1 : e (ψ ⟨x, hxH⟩ ^ 3) = 1 := by rw [map_pow]; exact oTwoUpper_dih12 _ heO
    exact (map_eq_one_iff e e.injective).mp h1
  obtain ⟨b, hb⟩ := S.isPGroup_T ⟨x, hxT⟩
  have hb' : (⟨x, hxH⟩ : ↥H) ^ 2 ^ b = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
  have h2' : ψ ⟨x, hxH⟩ ^ 2 ^ b = 1 := by rw [← map_pow, hb', map_one]
  have h1 : ψ ⟨x, hxH⟩ = 1 :=
    eq_one_of_pow_coprime h2' h3' (Nat.Coprime.pow_left b (by norm_num))

  have hxN3 : (⟨x, hHI hxH⟩ : ↥I) ∈ N3 := by
    have h2 : π ⟨x, hHI hxH⟩ = 1 := congrArg Subtype.val h1
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact S.pCoreOf_H0_le_R1 hTH hjT hjN hj
    (S.mem_pCoreOf_H0_of_mem_pPrimeCore hTH htriple hxT (hHI hxH) hxN3)

theorem false_of_caseThree_two_F4 (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h5172 : Stmt5_1_7_two_F4) (h311 : Theorem311Stmt) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) (hcase : F6.IsF618CaseThree (S.G2bar H) (S.G1bar H)) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨e⟩, -, -⟩ := hcase
  exact S.false_of_P_le_R1_F4 h331 h311 hH hHZ hsolv hS3
    (S.P_le_R1_of_dihedral_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3 e)

theorem oTwoUpper_le_of_le_image_F4 (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) {L' : Subgroup ↥(S.H0 H)}
    (hL' : L' ∈ cComp (⊤ : Subgroup ↥(S.H0 H)))
    (himg : oTwoUpper (⊤ : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))) ≤
      L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) :
    oTwoUpper H ≤ L'.map (S.H0 H).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htriple := S.triple_of_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3
  have hpow3 := S.pow_three_pow_mem_F4 h331 hH hHZ hsolv hS3
  refine (Subgroup.closure_le _).mpr ?_
  rintro k ⟨hkH, hko⟩
  have hkI : k ∈ S.H0 H := Subgroup.mem_sup_right hkH

  obtain ⟨a, ha⟩ := hpow3 k (mem_oTwoUpper_of_odd hkH hko)
  have hka : k ^ 3 ^ a = 1 := by
    obtain ⟨c, hc⟩ := pCoreOf_isPGroup 2 H ⟨_, ha⟩
    have hc' : (k ^ 3 ^ a) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
    have hco : (k ^ 3 ^ a) ^ orderOf k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    exact eq_one_of_pow_coprime hc' hco (Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr hko))
  have hk'a : (⟨k, hkI⟩ : ↥(S.H0 H)) ^ 3 ^ a = 1 := Subtype.ext (by simpa using hka)

  have hπk : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) ⟨k, hkI⟩ ∈
      L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) := by
    refine himg (mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_)
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) ⟨k, hkI⟩
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hko h1
  exact ⟨⟨k, hkI⟩, mem_of_pow_three_of_mem_map htriple.isSolvable_pPrimeCore hL' hk'a hπk, rfl⟩

theorem false_of_caseBig_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) (h3 : ¬ ThreeTop (S.H0 H))
    (hq : CFSG.IsQuasisimple ↥(oTwoUpper
      (⊤ : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H)))))
    (hcard : ∀ b : ℕ, Nat.card ↥(oTwoUpper
      (⊤ : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H)))) ≠ 60 * 2 ^ b) : False := by
  have htriple := S.triple_of_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3
  set I := S.H0 H with hI
  set N3 := CFSG.pPrimeCore 3 ↥I with hN3
  set π := QuotientGroup.mk' N3 with hπ
  set Kb := oTwoUpper (⊤ : Subgroup (↥I ⧸ N3)) with hKb
  have hKbn : Kb.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_oTwoUpper ⊤))
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥I ⧸ N3)) :=
    mem_cComp_top_of_isComponent ⟨hq, hKbn.isSubnormal⟩
  obtain ⟨L', hL', hL'K⟩ := (cComp_quotient_bijOn N3 htriple.isSolvable_pPrimeCore).2.2 hKbc
  have hZL : ⁅quasithinOmegaOneCenter T, L'.map I.subtype⁆ = ⊥ := by
    by_contra hne
    obtain ⟨b, hb⟩ := S.card_image_of_comm_ne hH hO2 hL' hne
    rw [hL'K] at hb
    exact hcard b hb
  have hLH := S.oTwoUpper_le_of_le_image_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3 hL' hL'K.ge
  apply hHZ
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_le S.h13.sylow hH.1.1)]
  refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
  refine hLH.trans ?_
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZL)

end Setting

theorem final1327_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) (h311 : Theorem311Stmt) (hF618 : F6.TheoremF618Cat)
    (hBig : FactF618Big) (hThree : Final1327CaseThree_F4) : Final1327_F4 := by
  intro G _ _ T L V S H hH hHZ hsolv hS3 hO2 h3
  obtain ⟨hAm, hconc⟩ := S.f618_of_F4 h331 h1222 h5172 hF618 hH hHZ hsolv hS3 hO2 h3
  have hAm' : IsGoldschmidtAmalgam (S.G2bar H) (S.G1bar H) :=
    { toIsGoldschmidtTriple := hAm.toIsGoldschmidtTriple.symm
      pCore_eq_bot := hAm.pCore_eq_bot }
  rcases hconc with h | h
  · rcases h with h1 | h2 | h3' | hrest
    · exact S.false_of_caseOne_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3 h1.2.1
    · exact h3 (isPGroup_oTwoUpper_of_caseTwo h2)
    · exact hThree G T L V S H hH hHZ hsolv hS3 hO2 h3 h3'
    · obtain ⟨hq, hc⟩ := hBig _ _ _ hAm hrest
      exact S.false_of_caseBig_F4 h331 h1222 h5172 hH hHZ hsolv hS3 hO2 h3 hq hc
  · rcases h with h1 | h2 | h3' | hrest
    · exact S.false_of_caseOne_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3 h1.2.2.1
    · exact h3 (isPGroup_oTwoUpper_of_caseTwo h2)
    · exact S.false_of_caseThree_two_F4 h331 h1222 h5172 h311 hH hHZ hsolv hS3 h3 h3'
    · obtain ⟨hq, hc⟩ := hBig _ _ _ hAm' hrest
      exact S.false_of_caseBig_F4 h331 h1222 h5172 hH hHZ hsolv hS3 hO2 h3 hq hc

end CFSG.Quasithin.H13.A5
