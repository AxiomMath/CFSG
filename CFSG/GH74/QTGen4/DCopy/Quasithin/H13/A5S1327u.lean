module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327t

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem false_of_caseS2B_F4 (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h5172 : Stmt5_1_7_two_F4) (h1332 : Stmt13_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h137 : EmptyFaithfulMultiple.Input137) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ : S.UH H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (S.UH H) ∧ IsTwoReducedIn H (S.UH H) :=
    conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  obtain ⟨-, hO2X, hidx⟩ := S.isXi_oTwoUpper_F4 h331 h1222 h5172 hH hHZ hsolv hS3
  have hH0L := S.H0_le_normalizer_oTwoUpper_F4 h331 h1222 h5172 h1332 h137 hH hHZ hsolv hS3 hO2
  have hL1U := S.L1_le_centralizer_UH_F4 h331 h1222 h5172 h1332 h512 h137 hH hHZ hsolv hS3 hO2
  have hH0 : S.L1 ≤ S.H0 H := by
    rw [S.H0_eq_sup hTH]; exact le_sup_left.trans le_sup_left
  have hHH0 : H ≤ S.H0 H := le_sup_right

  have hrank : CFSG.Open.pRank 3 (S.H0 H) ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian
      (⟨hTH.trans hHH0, hO2⟩ : InH T (S.H0 H))
    have h1 := hq 3 Nat.prime_three (by norm_num)
    rwa [← pRank_top_subtype]
  set U := S.UH H with hUdef
  set X := oTwoUpper H with hXdef
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hXH : X ≤ H := oTwoUpper_le H
  have hXN : X ≤ Subgroup.normalizer (U : Set G) := hXH.trans hHN

  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  obtain ⟨hMP, -⟩ := S.hyp501.minParabolic_of_isHStar_F4 h331 hH
  have hJT := S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ
  obtain ⟨K₁, K₂, B⟩ := exists_twoBlocks hUel hMP hsolv hSQT hUred hJT hS3
  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨t, -, ht⟩ := B.swap
  have hy₂ : t * y₁ * t⁻¹ ∈ K₂ := by
    rw [← ht, B1.mem_conjAut]
    simpa [mul_assoc] using hy₁
  have hy₂3 : (t * y₁ * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hy₁3]; group
  have hy₂1 : t * y₁ * t⁻¹ ≠ 1 := fun h => hy₁1 (by
    have e : y₁ = t⁻¹ * (t * y₁ * t⁻¹) * t := by group
    rw [e, h]; group)
  obtain ⟨hLcomm, hLcube⟩ := B.autI_twoResidual_comm_cube hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  rw [twoResidual_eq_oTwoUpper'] at hLcomm hLcube

  obtain ⟨g, hgL₁, hg⟩ := S.exists_L1_c3p
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  set l := (g : G) ^ 2 ^ k with hldef
  have hl1 : l ∈ S.L1 := S.L1.pow_mem hgL₁ _
  have hlodd : Odd (orderOf l) := by
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    rw [hldef, orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ g.2 _
  have hρl : S.frame.ρ ⟨l, hlN⟩ = c3p ^ 2 ^ k := by
    rw [show (⟨l, hlN⟩ : ↥(Subgroup.normalizer (V : Set G))) = g ^ 2 ^ k from rfl, map_pow, hg]
  have hρl1 : S.frame.ρ ⟨l, hlN⟩ ≠ 1 := by
    rw [hρl]
    intro h
    have h3 : orderOf c3p = 3 := orderOf_eq_prime c3p_cube (by decide)
    have hdvd : orderOf c3p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
    rw [h3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hl1' : l ≠ 1 := by
    intro h
    apply hρl1
    have : (⟨l, hlN⟩ : ↥(Subgroup.normalizer (V : Set G))) = 1 := Subtype.ext h
    rw [this, map_one]

  have hl3 : l ^ 3 = 1 := by
    have hρ3 : S.frame.ρ ⟨l ^ 3, Subgroup.pow_mem _ hlN 3⟩ = 1 := by
      rw [show (⟨l ^ 3, Subgroup.pow_mem _ hlN 3⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨l, hlN⟩ ^ 3 from rfl, map_pow, hρl, ← pow_mul, mul_comm, pow_mul, c3p_cube, one_pow]
    have hC := S.frame.mem_centralizer_of_rho _ hρ3
    have hlL : l ^ 3 ∈ L := L.pow_mem (S.L1_le_L hl1) 3
    have hT3 : l ^ 3 ∈ T := by
      refine S.pCoreOf_LT_le_T ?_
      rw [← S.cLT]
      exact ⟨Subgroup.mem_sup_left hlL, hC⟩
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨l ^ 3, hT3⟩
    have hb' : (l ^ 3) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hodd3 : (l ^ 3) ^ orderOf l = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    exact eq_one_of_pow_coprime hb' hodd3
      (Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hlodd))
  have hlU : l ∈ Subgroup.centralizer (U : Set G) := hL1U hl1
  have hlX : l ∈ Subgroup.normalizer (X : Set G) := hH0L (hH0 hl1)
  have hlUN : l ∈ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _ hlU

  by_cases hlXm : l ∈ X
  · have hlO : l ∈ pCoreOf 2 X := by rw [hO2X]; exact ⟨hlXm, hlU⟩
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 X ⟨l, hlO⟩
    have hb' : l ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    exact hl1' (eq_one_of_pow_coprime hb' hl3 (Nat.Coprime.pow_left b (by norm_num)))

  set Y := X ⊔ Subgroup.zpowers l with hY
  have hlXN : Subgroup.zpowers l ≤ Subgroup.normalizer (X : Set G) := (Subgroup.zpowers_le).2 hlX
  have hYset : (Y : Set G) = (X : Set G) * (Subgroup.zpowers l : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left X (Subgroup.zpowers l) hlXN
  have hYH0 : Y ≤ S.H0 H :=
    sup_le (hXH.trans hHH0) ((Subgroup.zpowers_le).2 (hH0 hl1))
  have hconjX : ∀ (i : ℤ), ∀ x ∈ X, l ^ i * x * (l ^ i)⁻¹ ∈ X := fun i x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hlX i) x).mp hx
  have hconvl : ∀ (i : ℤ) (hi : l ^ i ∈ Subgroup.normalizer (U : Set G)),
      convI hUel ⟨l ^ i, hi⟩ = 1 := fun i hi =>
    (convI_eq_one_iff hUel _).2 (Subgroup.zpow_mem _ hlU i)

  have hconvY : ∀ (x : G) (hx : x ∈ X) (i : ℤ),
      convI hUel ⟨x * l ^ i, Subgroup.mul_mem _ (hXN hx) (Subgroup.zpow_mem _ hlUN i)⟩ =
        convI hUel ⟨x, hXN hx⟩ := by
    intro x hx i
    have e : (⟨x * l ^ i, Subgroup.mul_mem _ (hXN hx) (Subgroup.zpow_mem _ hlUN i)⟩ :
        ↥(Subgroup.normalizer (U : Set G))) = ⟨x, hXN hx⟩ * ⟨l ^ i, Subgroup.zpow_mem _ hlUN i⟩ :=
      rfl
    rw [e, map_mul, hconvl, mul_one]
  have hcommY : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' * y⁻¹ * y'⁻¹ ∈ (pCoreOf 2 X) := by
    intro y hy y' hy'
    have hy1 : y ∈ (Y : Set G) := hy
    have hy1' : y' ∈ (Y : Set G) := hy'
    rw [hYset] at hy1 hy1'
    obtain ⟨x, hx, _, ⟨i, rfl⟩, rfl⟩ := hy1
    obtain ⟨x', hx', _, ⟨j, rfl⟩, rfl⟩ := hy1'
    simp only
    rw [hO2X]
    refine ⟨?_, ?_⟩
    · have e : x * l ^ i * (x' * l ^ j) * (x * l ^ i)⁻¹ * (x' * l ^ j)⁻¹ =
          x * (l ^ i * x' * (l ^ i)⁻¹) * (l ^ j * x⁻¹ * (l ^ j)⁻¹) * x'⁻¹ := by group
      rw [e]
      exact X.mul_mem (X.mul_mem (X.mul_mem hx (hconjX i x' hx'))
        (hconjX j _ (X.inv_mem hx))) (X.inv_mem hx')
    · have hmemN : x * l ^ i * (x' * l ^ j) * (x * l ^ i)⁻¹ * (x' * l ^ j)⁻¹ ∈
          Subgroup.normalizer (U : Set G) := by
        have a1 := Subgroup.mul_mem _ (hXN hx) (Subgroup.zpow_mem _ hlUN i)
        have a2 := Subgroup.mul_mem _ (hXN hx') (Subgroup.zpow_mem _ hlUN j)
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ a1 a2)
          (Subgroup.inv_mem _ a1)) (Subgroup.inv_mem _ a2)
      refine (convI_eq_one_iff hUel ⟨_, hmemN⟩).1 ?_
      have e : (⟨_, hmemN⟩ : ↥(Subgroup.normalizer (U : Set G))) =
          ⟨x * l ^ i, Subgroup.mul_mem _ (hXN hx) (Subgroup.zpow_mem _ hlUN i)⟩ *
            ⟨x' * l ^ j, Subgroup.mul_mem _ (hXN hx') (Subgroup.zpow_mem _ hlUN j)⟩ *
            (⟨x * l ^ i, Subgroup.mul_mem _ (hXN hx) (Subgroup.zpow_mem _ hlUN i)⟩)⁻¹ *
            (⟨x' * l ^ j, Subgroup.mul_mem _ (hXN hx') (Subgroup.zpow_mem _ hlUN j)⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hconvY x hx i, hconvY x' hx' j,
        hLcomm _ (convI_mem_autI hUel hx (hXN hx)) _ (convI_mem_autI hUel hx' (hXN hx'))]
      group
  have hcubeY : ∀ y ∈ Y, y ^ 3 ∈ (pCoreOf 2 X) := by
    intro y hy
    have hy1 : y ∈ (Y : Set G) := hy
    rw [hYset] at hy1
    obtain ⟨x, hx, _, ⟨i, rfl⟩, rfl⟩ := hy1
    simp only
    rw [hO2X]
    have hli3 : (l ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hl3, one_zpow]
    refine ⟨?_, ?_⟩
    · have e : (x * l ^ i) ^ 3 = x * (l ^ i * x * (l ^ i)⁻¹) *
          ((l ^ i) ^ 2 * x * ((l ^ i) ^ 2)⁻¹) * (l ^ i) ^ 3 := by
        rw [pow_three, pow_three, sq]; group
      rw [e, hli3, mul_one]
      refine X.mul_mem (X.mul_mem hx (hconjX i x hx)) ?_
      have := hconjX (2 * i) x hx
      rwa [zpow_mul', zpow_two, ← sq] at this
    · have hmemN : (x * l ^ i) ^ 3 ∈ Subgroup.normalizer (U : Set G) :=
        Subgroup.pow_mem _ (Subgroup.mul_mem _ (hXN hx) (Subgroup.zpow_mem _ hlUN i)) 3
      refine (convI_eq_one_iff hUel ⟨_, hmemN⟩).1 ?_
      have e : (⟨_, hmemN⟩ : ↥(Subgroup.normalizer (U : Set G))) =
          ⟨x * l ^ i, Subgroup.mul_mem _ (hXN hx) (Subgroup.zpow_mem _ hlUN i)⟩ ^ 3 := rfl
      rw [e, map_pow, hconvY x hx i]
      exact hLcube _ (convI_mem_autI hUel hx (hXN hx))

  have hinf : X ⊓ Subgroup.zpowers l = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨hyX, ⟨i, rfl⟩⟩ := hy
    by_contra hne
    apply hlXm
    have hgen : Subgroup.zpowers (l ^ i) = Subgroup.zpowers l := by
      have h3 : (l ^ i) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hl3, one_zpow]
      have hne' : l ^ i ≠ 1 := fun h => hne (by rw [Subgroup.mem_bot]; exact h)
      have hox : orderOf (l ^ i) = 3 := orderOf_eq_prime h3 hne'
      have hol : orderOf l = 3 := orderOf_eq_prime hl3 hl1'
      exact Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 (Subgroup.zpow_mem_zpowers l i))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hol])
    have : l ∈ Subgroup.zpowers (l ^ i) := hgen ▸ Subgroup.mem_zpowers l
    exact (Subgroup.zpowers_le).2 hyX this
  have hcardY : Nat.card Y = 27 * Nat.card (pCoreOf 2 X) := by
    have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hlXN
    have h2 : X.relIndex (Subgroup.zpowers l) = 3 := by
      rw [Subgroup.relIndex, show X.subgroupOf (Subgroup.zpowers l) = ⊥ from ?_,
        Subgroup.index_bot, Nat.card_zpowers, orderOf_eq_prime hl3 hl1']
      rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, hinf]
    have h3 := Subgroup.relIndex_mul_card X (Subgroup.zpowers l ⊔ X)
    rw [inf_of_le_left le_sup_right, h1, h2, sup_comm] at h3
    have h4 := Subgroup.relIndex_mul_card (pCoreOf 2 X) X
    rw [inf_of_le_left (pCoreOf_le 2 X), hidx] at h4
    rw [← h3, ← h4]
    ring

  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y) 3 (n := 3)
    (by rw [hcardY]; exact Dvd.intro _ rfl)
  set E := E'.map Y.subtype with hE
  have hcardE : Nat.card E = 3 ^ 3 := by
    rw [hE, Subgroup.card_map_of_injective Y.subtype_injective, hE']
  have hEY : E ≤ Y := Subgroup.map_subtype_le E'
  have hEP : ∀ e ∈ E, e ∈ (pCoreOf 2 X) → e = 1 := by
    intro e he heP
    have h27 : e ^ 27 = 1 := by
      have := pow_card_eq_one' (G := ↥E) (x := ⟨e, he⟩)
      rw [hcardE] at this
      simpa using congrArg Subtype.val this
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 X ⟨e, heP⟩
    have hb' : e ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    exact eq_one_of_pow_coprime hb' h27 (Nat.Coprime.pow_left b (by norm_num))
  have hEel : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => hEP _ (E.pow_mem he 3) (hcubeY e (hEY he))⟩
    have h1 := hEP _ (E.mul_mem (E.mul_mem (E.mul_mem a.2 b.2) (E.inv_mem a.2)) (E.inv_mem b.2))
      (hcommY _ (hEY a.2) _ (hEY b.2))
    show (a : G) * b = b * a
    calc (a : G) * b = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have h3 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (hEY.trans hYH0) hEel hcardE
  omega

end Setting

end CFSG.Quasithin.H13.A5
