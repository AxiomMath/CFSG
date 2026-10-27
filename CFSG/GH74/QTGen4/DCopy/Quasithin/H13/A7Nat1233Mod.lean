module

public import CFSG.Quasithin.H13.A7Nat1233Mod
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1233FourInputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238Ke

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem facts1233Four_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} (hyp : Hyp1223 G T L V) :
    V ≤ T ∧ T ≤ normalizer (V : Set G) ∧ IsMulCommutative ↥V ∧ ∀ v ∈ V, v ^ 2 = 1 := by
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hab, -⟩ := hall V hyp.irrPlus
  refine ⟨hVT, hTV, hab, ?_⟩
  obtain ⟨-, hEA, -⟩ := hred
  intro v hv
  have hv' : (⟨v, le_sup_right (b := T) (a := L) (hVT hv)⟩ : ↥(L ⊔ T)) ∈
      V.subgroupOf (L ⊔ T) := hv
  have h1 := (BlueprintB2.isElementaryAbelian_iff.1 hEA).2 _ hv'
  exact congrArg Subtype.val h1

theorem insp1233Mod_of_F4
    (h1222 : Stmt12_2_2_F4) (h1225 : Stmt12_2_5_F4) : Insp1233Mod_F4 := by
  intro G _ _ T L V hyp hS z hzV hz1 hzZ
  classical
  obtain ⟨-, hcard, φ, hφs, hφk⟩ := hS
  obtain ⟨hVT, hTV, hab, hsq⟩ := facts1233Four_F4 h1222 hyp
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hΓ : Nat.card (autOn L V) = 2520 := card_autOn_of_ker hLV hφs hφk
  have hW2 : ∀ w : ↥V, w * w = 1 := fun w => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hsq w w.2)
  have hz' : (⟨z, hzV⟩ : ↥V) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hSs := isSimpleGroup_fourStab hW2 hcard hΓ hz'

  have htrans : ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, v = l * z * l⁻¹ := by
    intro v hv hv1
    obtain ⟨γ, hγ, hγz⟩ := exists_apply_eq_four hcard hΓ hz'
      (show (⟨v, hv⟩ : ↥V) ≠ 1 from fun h => hv1 (congrArg Subtype.val h))
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).1 hγ
    exact ⟨l, l.2, (congrArg Subtype.val hγz).symm⟩

  have hCzV : L ⊓ centralizer ({z} : Set G) ≤ normalizer (V : Set G) := inf_le_left.trans hLV
  have hLzV : hyp.Lv z ≤ normalizer (V : Set G) := (oTwoUpper_le _).trans hCzV
  have hLz : autOn (hyp.Lv z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    change autOn (oTwoUpper (L ⊓ centralizer ({z} : Set G))) V = _
    rw [autOn_oTwoUpper_eq hCzV, autOn_inf_centralizer_eq hLV hzV,
      oTwoUpper_fourStab hW2 hcard hΓ hz']
  have hSperf := commutator_fourStab hW2 hcard hΓ hz'
  have hKz : autOn (Kv hyp z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    change autOn (perfectCore (hyp.Lv z)) V = _
    rw [autOn_perfectCore_eq hLzV, hLz, perfectCore_eq_self_of_perfect hSperf]

  have hTzV : hyp.Tv z ≤ normalizer (V : Set G) := inf_le_left.trans hTV
  have hTz : autOn (hyp.Tv z) V ≤ fourStab (autOn L V) ⟨z, hzV⟩ := by
    intro a ha
    obtain ⟨t, rfl⟩ := (A4.mem_autOn_iff hTzV).1 ha
    refine ⟨mem_of_mem_normalizer_four hW2 hcard hΓ
      (autOn_le_normalizer_autOn hLV hTV hyp.normalizes
        ((A4.mem_autOn_iff hTV).2 ⟨⟨t, t.2.1⟩, rfl⟩)), MulAction.mem_stabilizer_iff.2 ?_⟩
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.1 t.2.2, mul_inv_cancel_right]
  have hLTz : autOn (hyp.Lv z ⊔ hyp.Tv z) V = fourStab (autOn L V) ⟨z, hzV⟩ := by
    rw [autOn_sup_eq_sup_autOn hLzV hTzV, hLz]
    exact sup_eq_left.2 hTz
  have hcomm := commV_fourStab_eq_top hW2 hcard hΓ hz'
  have hSp := pCoreOf_fourStab hW2 hcard hΓ hz'
  refine ⟨htrans, by rw [hLTz]; exact hSp, by rw [hLz, perfectCore_eq_self_of_perfect hSperf],
    eq_commutator_of_commV_eq_top hLzV (by rw [hLz]; exact hcomm), ?_⟩

  have hTK : T ≤ normalizer (Kv hyp z : Set G) := T_le_normalizer_Kv_F4 hyp h1225 hzV hz1 hzZ
  have hKV : Kv hyp z ≤ normalizer (V : Set G) := (Kv_le_L hyp z).trans hLV
  have hq := Kv_quasisimple_four hyp hLV hφs hφk hKz (fourStab_noncomm hW2 hcard hΓ hz') hSp
  have hmemL : Kv hyp z ∈ lFamily T := by
    show Kv hyp z ∈ cComp (Kv hyp z ⊔ T)
    refine mem_cComp_of_quasisimple_quotient
      (fun N _ hN => eq_top_of_perfect_of_isPGroup (Kv_perfect hyp z) N hN) hq
      (A3.subnormal_of_normal le_sup_left ?_)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hTK)
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ centralizer ({z} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hzZ) t ht))
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hsq z hzV) hz1
  have hloc : quasithinIsLocal T (Kv hyp z) :=
    ⟨hyp.sylow.1, hmemL, (isSylowTwoOf_of_le hyp.sylow le_sup_right).2.2,
      pCoreOf_ne_bot_of_le_centralizer hz2 ((le_sup_right : T ≤ Kv hyp z ⊔ T) (hVT hzV))
        (sup_le (Kv_le_centralizer hyp z) hTe)⟩

  have hVY : VY (Kv hyp z) ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hVc : V = ⁅V, Kv hyp z⁆ :=
      eq_commutator_of_commV_eq_top hKV (by rw [hKz]; exact hcomm)
    have hVle : V ≤ Kv hyp z :=
      hVc.le.trans ((Subgroup.le_normalizer_iff_commutator_le_right).1 (hVT.trans hTK))
    have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hsq x x.2)⟩
    have hVP : V ≤ pCoreOf 2 (Kv hyp z) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVle hKV hV2
    have hPV := pCoreOf_le_centralizer_of_autOn hKV hKz hSp
    have hVZ : V ≤ omegaOneCenterOf (pCoreOf 2 (Kv hyp z)) := fun v hv =>
      Subgroup.subset_closure ⟨⟨hVP hv, (Subgroup.le_centralizer_iff.1 hPV) hv⟩, hsq v hv⟩
    intro hbot
    have h1 : ⁅V, Kv hyp z⁆ ≤ VY (Kv hyp z) := Subgroup.commutator_mono hVZ le_rfl
    rw [hbot, ← hVc] at h1
    exact hyp.irrPlus.2.1 (le_bot_iff.1 h1)
  exact isFaithfulLocal_iff_isXf.2 ⟨hloc, isXClass_of_isLocal hyp.qtke hyp.sylow hloc, hVY⟩

end CFSG.Quasithin.H13.A7
