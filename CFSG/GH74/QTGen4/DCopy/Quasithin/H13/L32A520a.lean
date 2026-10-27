module

public import CFSG.Quasithin.H13.L32A520a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Setting

variable {T L V H : Subgroup G}

theorem normalizer_le_of_le_cSec_F4 (h1332 : Stmt13_3_2_F4) (S : Setting147 G T L V H)
    {X : Subgroup G} (hXH : X ≤ H) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXo : oTwoUpper X = X) (hX1 : X ≠ ⊥)
    (hXC : X ≤ centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L)) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL13 := h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hL13.2.1.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hT := S.hyp.fsu.sylow
  have hchar : CharTwo H := by
    refine charTwo_of_inH S.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2) ⟨?_, S.hz.1.2⟩
    rw [IsPGroup.toSylow_coe]
    exact hTH

  have hRT : pCoreOf 2 L ≤ T := by
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 L)).trans (pCoreOf_le_of_le S.hyp le_sup_right)
    exact sup_le (le_normalizer_pCoreOf 2 L) (F7.le_normalizer_pCoreOf_of_le_normalizer hTL)

  have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
    refine C1Pack.le_normalizer_of_commutator_mem_s1461 hXo (pCoreOf_isPGroup 2 L) (hRT.trans hTX)
      (le_normalizer_pCoreOf 2 L) fun x hx l hl => ?_
    have h1 := (mem_centralizerSection.mp (hXC hx)).2.2.2 l hl
    rw [show x * l * x⁻¹ * l⁻¹ = (l * x * l⁻¹ * x⁻¹)⁻¹ by group]
    exact inv_mem h1

  have hQX : pCoreOf 2 H ≤ Subgroup.normalizer (X : Set G) :=
    (pCoreOf_le_of_le S.hyp hTH).trans hTX
  have hX2 := C1Pack.pCoreOf_ne_bot_of_eq_oTwoUpper hchar hXH hQX hXo hX1
  have hK : pCoreOf 2 (Subgroup.normalizer (X : Set G)) ≠ ⊥ := by
    intro h
    apply hX2
    have := le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 X).trans Subgroup.le_normalizer)
      (normalizer_le_normalizer_pCoreOf 2 X) (pCoreOf_isPGroup 2 X)
    rw [h] at this
    exact le_bot_iff.mp this
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hK
  have hMeq := hL13.2.1.2.2.2 M' hM'.1 ((sup_le hLX hTX).trans hM'.2)
  rw [← hMeq]
  exact hM'.2

theorem lemma14_5_20A_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) {Y : Subgroup G} {p : ℕ} (hp : p.Prime) (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hYp : ∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y) :
    Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y ∨ (p = 3 ∧ l1 T L V ≤ Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hHV1 : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := S.hz.2.1
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := S14.TL_F4
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp hTH

  have hOY : pCoreOf 2 Y ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH)
      (hHY.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
  have hOK : pCoreOf 2 Y ≤ Y ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf (pCoreOf_le 2 Y) (hOY.trans (hQT.trans hTM))
  by_cases h1 : Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y
  · exact Or.inl h1
  right
  have hK : ¬ Y ⊓ Subgroup.normalizer (L : Set G) ≤ pCoreOf 2 Y :=
    fun h => h1 (le_antisymm h hOK)

  have hp2 : p ≠ 2 := by
    rintro rfl
    apply hK
    have hY2 : IsPGroup 2 Y := by
      rintro ⟨y, hy⟩
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Y ⟨_, hYp y hy⟩
      refine ⟨k + 1, Subtype.ext ?_⟩
      have h2 : (y ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_succ', pow_mul]
      exact h2
    exact inf_le_left.trans (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hY2)

  have hYM1 : oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) ≠ ⊥ :=
    oTwoUpper_ne_bot_of_not_le hp hp2 hYp inf_le_left hK
  have hYO : ¬ Y ≤ pCoreOf 2 Y := fun h => hK (inf_le_left.trans h)
  have hZ : ¬ o2z Y ≤ pCoreOf 2 Y := by
    have : Fact p.Prime := ⟨hp⟩
    have hPQ : IsPGroup p (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((pCoreOf 2 Y).subgroupOf Y) q
      refine ⟨1, ?_⟩
      rw [pow_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hYp y y.2)
    obtain ⟨y₀, hy₀, hy₀O⟩ := IsConcreteLE.not_le_iff_exists.mp hYO
    have : Nontrivial (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) :=
      ⟨⟨QuotientGroup.mk' ((pCoreOf 2 Y).subgroupOf Y) ⟨y₀, hy₀⟩, 1, fun h => hy₀O (by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
        exact Subgroup.mem_subgroupOf.mp h)⟩⟩
    have := hPQ.center_nontrivial
    obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Subgroup.center (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)))
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective ((pCoreOf 2 Y).subgroupOf Y) (c : _)
    intro hle
    apply hc
    have hyZ : (y : G) ∈ o2z Y := ⟨y, Subgroup.mem_comap.mpr (by rw [hy]; exact c.2), rfl⟩
    have h2 : y ∈ (pCoreOf 2 Y).subgroupOf Y := Subgroup.mem_subgroupOf.mpr (hle hyZ)
    have h3 : QuotientGroup.mk' ((pCoreOf 2 Y).subgroupOf Y) y = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
    exact Subtype.ext (hy.symm.trans h3)
  have hYZ1 : oTwoUpper (o2z Y) ≠ ⊥ := oTwoUpper_ne_bot_of_not_le hp hp2 hYp (o2z_le Y) hZ

  have hTK : T ≤ Subgroup.normalizer
      ((Y ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHY (hTH ht), Subgroup.le_normalizer (hTM ht)⟩
  have hTYM : T ≤ Subgroup.normalizer
      (oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) : Set G) :=
    hTK.trans (normalizer_le_normalizer_oTwoUpper _)
  have hHYZ : H ≤ Subgroup.normalizer (oTwoUpper (o2z Y) : Set G) :=
    (hHY.trans (normalizer_le_normalizer_o2z Y)).trans (normalizer_le_normalizer_oTwoUpper _)
  have hYMH : oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) ≤ H :=
    (oTwoUpper_le _).trans (inf_le_left.trans hYH)

  have hA : ¬ oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) ≤
      centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L) := by
    intro hYMC
    have hN := normalizer_le_of_le_cSec_F4 h1332 S hYMH hTYM (oTwoUpper_oTwoUpper _) hYM1 hYMC
    have hZN : oTwoUpper (o2z Y) ≤ Subgroup.normalizer (L : Set G) :=
      ((oTwoUpper_le _).trans ((o2z_le_normalizer hOK inf_le_left).trans
        (normalizer_le_normalizer_oTwoUpper _))).trans hN
    have hZM : oTwoUpper (o2z Y) ≤ oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) :=
      calc oTwoUpper (o2z Y) = oTwoUpper (oTwoUpper (o2z Y)) := (oTwoUpper_oTwoUpper _).symm
        _ ≤ oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) :=
          oTwoUpper_mono (le_inf ((oTwoUpper_le _).trans (o2z_le Y)) hZN)
    have hN' := normalizer_le_of_le_cSec_F4 h1332 S (hZM.trans hYMH) (hTH.trans hHYZ)
      (oTwoUpper_oTwoUpper _) hYZ1 (hZM.trans hYMC)
    exact S.hz.2.2 (hHYZ.trans hN')

  have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
    have := S14.card_V1_F4
    rw [h, Subgroup.card_bot] at this
    exact absurd this (by norm_num)
  have h6 := lemma1433Six_of_inputs_F4 h1332 h1334 h1222 G T L V S.hyp.hyp S.hyp.fsu (fsuV1 T V) H
    inf_le_left hV1 hHV1
  have hKX : ∀ y ∈ Y ⊓ Subgroup.normalizer (L : Set G), y ∈ L32NSet14.nX T V := by
    intro y hy
    have h2 : y ∈ H ⊓ Subgroup.normalizer (L : Set G) := ⟨hYH hy.1, hy.2⟩
    rw [h6] at h2
    exact ⟨h2.2, hHV1 h2.1⟩
  obtain ⟨ψ, hψ⟩ := S14.exists_rep_F4

  have hB2 : ∀ y (hy : y ∈ Y ⊓ Subgroup.normalizer (L : Set G)), Odd (orderOf y) →
      ψ ⟨y, hKX y hy⟩ = 1 →
        y ∈ centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L) := by
    intro y hy hodd hψy
    have hsq := S14.sq_mem_cent_F4 ((hψ _).mp hψy)
    have hyV : y ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.zpowers_le.mpr hsq) (A4.mem_zpowers_pow_of_coprime (Nat.coprime_two_left.mpr hodd))
    have hyL : y ∈ Subgroup.normalizer (L : Set G) := hy.2
    refine mem_centralizerSection.mpr ⟨hyL, hyL, normalizer_le_normalizer_pCoreOf 2 L hyL,
      fun l hl => ?_⟩
    rw [← S14.cent_eq_F4]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h2 : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL _).mp (inv_mem hl)
      rw [show l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) by group]
      exact mul_mem hl h2
    · have h2 : l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer _ (S14.LV_F4 hl))
          y).mp hyV
      exact mul_mem h2 (inv_mem hyV)

  obtain ⟨y, hyK, hyodd, hyC⟩ : ∃ y ∈ Y ⊓ Subgroup.normalizer (L : Set G), Odd (orderOf y) ∧
      y ∉ centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L) := by
    by_contra hall
    push Not at hall
    exact hA ((Subgroup.closure_le _).mpr fun x hx => hall x hx.1 hx.2)
  have hψy : ψ ⟨y, hKX y hyK⟩ ≠ 1 := fun h => hyC (hB2 y hyK hyodd h)

  have hp3 : p = 3 := by
    by_contra hp3
    apply hψy
    have hyp1 : y ^ p = 1 := by
      obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 Y ⟨_, hYp y hyK.1⟩
      have hb' : y ^ (p * 2 ^ b) = 1 := by
        rw [pow_mul]
        simpa using congrArg Subtype.val hb
      have hd := orderOf_dvd_of_pow_eq_one hb'
      have hcop : Nat.Coprime (orderOf y) (2 ^ b) :=
        Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hyodd)
      exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hd)
    have h2 : ψ ⟨y, hKX y hyK⟩ ^ p = 1 := by
      rw [← map_pow]
      have e : (⟨y, hKX y hyK⟩ : ↥(L32NSet14.nX T V)) ^ p = 1 := Subtype.ext (by simpa using hyp1)
      rw [e, map_one]
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one (L32NSet14.sl2_pow_six (ψ ⟨y, hKX y hyK⟩)))
    have hcop : Nat.Coprime p 6 := Nat.Coprime.mul_right
      ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
    rw [hcop.gcd_eq_one] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  refine ⟨hp3, ?_⟩
  subst hp3

  obtain ⟨t₀, ht₀T, ht₀⟩ := S14.exists_T_not_triv_F4
  have hα : conjAct V ⟨t₀, S14.TV_F4 ht₀T⟩ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One S14.h1281_F4]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hα
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.mp hlL
  have hlv : ∀ v ∈ V, l * v * l⁻¹ = t₀ * v * t₀⁻¹ := fun v hv =>
    congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hlα
  have hcent : t₀⁻¹ * l ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h2 := hlv v hv
    calc v * (t₀⁻¹ * l) = t₀⁻¹ * (t₀ * v * t₀⁻¹) * l := by group
      _ = t₀⁻¹ * (l * v * l⁻¹) * l := by rw [h2]
      _ = t₀⁻¹ * l * v := by group
  have hLTC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S14.LV_F4 S14.TV_F4
    refine (le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_)
      S14.isPGroup_cent_sup_F4).trans (pCoreOf_le_of_le S.hyp le_sup_right)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
      normalizer_le_normalizer_centralizer _ (hLTV hg)⟩
  have hlT : l ∈ T := by
    have h2 : t₀⁻¹ * l ∈ T := hLTC ⟨mul_mem (Subgroup.mem_sup_right (inv_mem ht₀T))
      (Subgroup.mem_sup_left hlL'), hcent⟩
    rw [show l = t₀ * (t₀⁻¹ * l) by group]
    exact mul_mem ht₀T h2
  have hlX : l ∈ L32NSet14.nX T V := S14.T_le_X_F4 hlT
  have hψl : ψ ⟨l, hlX⟩ ≠ 1 := by
    intro h
    apply ht₀
    have htX : t₀ ∈ L32NSet14.nX T V := S14.T_le_X_F4 ht₀T
    have h2 : ψ (⟨t₀, htX⟩⁻¹ * ⟨l, hlX⟩) = 1 := by
      refine (hψ _).mpr (L32NSet14.mem_trivSub.mpr ⟨?_, ?_, fun v hv => ?_⟩)
      · exact mul_mem (inv_mem htX.1) hlX.1
      · exact mul_mem (inv_mem htX.2) hlX.2
      · have := Subgroup.mem_centralizer_iff.mp hcent v hv
        have e : t₀⁻¹ * l * v * (t₀⁻¹ * l)⁻¹ * v⁻¹ = 1 := by
          rw [show t₀⁻¹ * l * v = v * (t₀⁻¹ * l) from this.symm]
          group
        show t₀⁻¹ * l * v * (t₀⁻¹ * l)⁻¹ * v⁻¹ ∈ fsuV1 T V
        rw [e]
        exact one_mem _
    rw [map_mul, map_inv, h, mul_one, inv_eq_one] at h2
    exact (hψ _).mp h2
  have hτ2 : ψ ⟨l, hlX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨l, hlT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have e : (⟨l, hlX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [e, map_one]
  have hσ3 : ψ ⟨y, hKX y hyK⟩ ^ 3 = 1 := by
    refine L32NSet14.sl2_cube_of_odd hyodd ?_
    rw [← map_pow]
    have e : (⟨y, hKX y hyK⟩ : ↥(L32NSet14.nX T V)) ^ orderOf y = 1 :=
      Subtype.ext (by simp)
    rw [e, map_one]

  obtain ⟨hw3, hw1⟩ := sl2_comm_cube _ _ hσ3 hψy hτ2 hψl
  have hyY : y ∈ Y := hyK.1
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hyK.2
  have hwY : y * l * y⁻¹ * l⁻¹ ∈ Y := by
    have h2 : l * y⁻¹ * l⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hHY (hTH hlT)) _).mp (inv_mem hyY)
    rw [show y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) by group]
    exact mul_mem hyY h2
  have hwL : y * l * y⁻¹ * l⁻¹ ∈ L :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hyN l).mp hlL') (inv_mem hlL')
  have hwX : y * l * y⁻¹ * l⁻¹ ∈ L32NSet14.nX T V :=
    mul_mem (mul_mem (mul_mem (hKX y hyK) hlX) (inv_mem (hKX y hyK))) (inv_mem hlX)
  have hψw : ψ ⟨y * l * y⁻¹ * l⁻¹, hwX⟩ =
      ψ ⟨y, hKX y hyK⟩ * ψ ⟨l, hlX⟩ * (ψ ⟨y, hKX y hyK⟩)⁻¹ * (ψ ⟨l, hlX⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl

  obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 Y ⟨_, hYp _ hwY⟩
  have hb' : ((y * l * y⁻¹ * l⁻¹) ^ 3) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hw'3 : ((y * l * y⁻¹ * l⁻¹) ^ 2 ^ b) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hb']
  have hw'X : (y * l * y⁻¹ * l⁻¹) ^ 2 ^ b ∈ L32NSet14.nX T V := pow_mem hwX _
  have hψw' : ψ ⟨(y * l * y⁻¹ * l⁻¹) ^ 2 ^ b, hw'X⟩ ≠ 1 := by
    intro h
    apply hw1
    rw [← hψw]
    have e : ψ ⟨(y * l * y⁻¹ * l⁻¹) ^ 2 ^ b, hw'X⟩ = ψ ⟨y * l * y⁻¹ * l⁻¹, hwX⟩ ^ 2 ^ b := by
      rw [← map_pow]
      rfl
    rw [e, hψw] at h
    rw [hψw]
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one h)
    rw [(Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hw'L₁ : (y * l * y⁻¹ * l⁻¹) ^ 2 ^ b ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨pow_mem hwL _, hw'X.2⟩, 3, by decide, hw'3⟩
  have hw'O : (y * l * y⁻¹ * l⁻¹) ^ 2 ^ b ∉ pCoreOf 2 (L₁Of L (fsuV1 T V)) := fun h =>
    hψw' ((hψ _).mpr (S14.pCoreOf_L1_le_F4 h))

  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hL₁H : L₁Of L (fsuV1 T V) ≤ H := hl1eq ▸ hL1H
  set L₁ := L₁Of L (fsuV1 T V) with hL₁def
  have hKO : ¬ L₁ ⊓ Y ≤ pCoreOf 2 L₁ := fun h => hw'O (h ⟨hw'L₁, pow_mem hwY _⟩)
  have hle : L₁ ⊓ Y ⊔ pCoreOf 2 L₁ ≤ L₁ := sup_le inf_le_left (pCoreOf_le 2 L₁)
  have hJ : L₁ ⊓ Y ⊔ pCoreOf 2 L₁ = L₁ := by
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hle
    rw [S14.Lp3_F4] at hmul
    have hne1 : (pCoreOf 2 L₁).relIndex (L₁ ⊓ Y ⊔ pCoreOf 2 L₁) ≠ 1 := by
      intro h
      rw [Subgroup.relIndex_eq_one] at h
      exact hKO (le_sup_left.trans h)
    have hd : (pCoreOf 2 L₁).relIndex (L₁ ⊓ Y ⊔ pCoreOf 2 L₁) ∣ 3 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd h hne1
    · rw [h] at hmul
      have h2 : (L₁ ⊓ Y ⊔ pCoreOf 2 L₁).relIndex L₁ = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
  have hKn : pCoreOf 2 L₁ ≤ Subgroup.normalizer ((L₁ ⊓ Y : Subgroup G) : Set G) := fun q hq =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (pCoreOf_le 2 L₁ hq),
      hHY (hL₁H (pCoreOf_le 2 L₁ hq))⟩

  have hO2 : oTwoUpper (L₁ ⊓ Y ⊔ pCoreOf 2 L₁) ≤ L₁ ⊓ Y := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    have hmulN := Subgroup.coe_mul_of_right_le_normalizer_left (L₁ ⊓ Y) (pCoreOf 2 L₁) hKn
    have hx' : x ∈ ((L₁ ⊓ Y : Subgroup G) : Set G) * (pCoreOf 2 L₁ : Set G) := by
      rw [← hmulN]
      exact hx
    obtain ⟨n, hn, q, hq, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 L₁ ⟨q, hq⟩
    obtain ⟨n', hn', hnq⟩ := A4.exists_pow_mul_eq hn (hKn hq) (2 ^ j)
    refine ⟨j, ?_⟩
    have hq1 : q ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [hnq, hq1, mul_one]
    exact hn'
  rw [hJ] at hO2
  rw [← hl1eq]
  calc L₁ = oTwoUpper L₁ := (L32NSet14.oTwoUpper_oTwoRes _).symm
    _ ≤ L₁ ⊓ Y := hO2
    _ ≤ Y := inf_le_right

end Setting

end CFSG.Quasithin.H13.L32A
