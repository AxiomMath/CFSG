module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6U42
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171U42Red
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem card_le_of_mulAut_rank {Ω : Type} [Group Ω] [Finite Ω] {B K D : Subgroup Ω}
    (m : ℕ) (hB : IsElemAbelian 3 B) (hBK : B ≤ Subgroup.normalizer (K : Set Ω))
    (hD : D = B ⊓ Subgroup.centralizer (K : Set Ω)) (hDcard : Nat.card D = 9)
    (hAut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) ≤ m) :
    Nat.card B ≤ 9 * 3 ^ m := by
  classical
  let α : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBK)
  have hDleB : D ≤ B := hD ▸ inf_le_left
  have hker : α.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : α b = 1 ↔ (b : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
      have hker1 : α b = 1 ↔
          Subgroup.inclusion hBK b ∈ K.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact Iff.rfl
      rw [hker1, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion]
    rw [hD, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h1.1 h⟩, fun h => h1.2 h.2⟩
  have hker_card : Nat.card α.ker = 9 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleB).toEquiv, hDcard]
  have hBtop : IsElemAbelian 3 (⊤ : Subgroup ↥B) := by
    haveI : IsMulCommutative ↥B := hB.1
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : ↥B) (b : ↥B))⟩⟩, fun a _ => ?_⟩
    exact Subtype.ext (by simpa using hB.2 (a : ↥B) a.2)
  have hrange_el : IsElemAbelian 3 α.range := by
    rw [MonoidHom.range_eq_map]
    exact hBtop.map α
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_card_eq_pow_of_isElemAbelian
    (p := 3) Nat.prime_three hrange_el
  have hk3 : k ≤ m := by
    have h := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hrange_el hk
    exact h.trans hAut
  have hrange_le : Nat.card α.range ≤ 3 ^ m := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk3
  have h := Subgroup.card_ker_mul_card_range α
  rw [hker_card] at h
  calc Nat.card B = 9 * Nat.card α.range := h.symm
    _ ≤ 9 * 3 ^ m := Nat.mul_le_mul_left _ hrange_le

theorem card_le_nine_of_alt_six {Ω : Type} [Group Ω] [Finite Ω] {B K D : Subgroup Ω}
    (hB : IsElemAbelian 3 B) (hBK : B ≤ Subgroup.normalizer (K : Set Ω))
    (hD : D = B ⊓ Subgroup.centralizer (K : Set Ω)) (hDcard : Nat.card D = 9)
    (e : ↥K ≃* alternatingGroup (Fin 6)) : Nat.card B ≤ 81 := by
  have hZ : Subgroup.center ↥K = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot (by norm_num)] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
  have hAut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) ≤ 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_alt (Or.inl rfl) hZ e
  exact (card_le_of_mulAut_rank 2 hB hBK hD hDcard hAut).trans (by norm_num)

theorem pRank_three_mulAut_u42 {Ω : Type} [Group Ω] [Finite Ω] {K : Subgroup Ω}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hU42 : CFSG.Assembly.LargeEvenIsU42 ↥K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) ≤ 3 := by
  have hcatK : catalogIs ↥K S9.isU4two := (S171.catalog_pSimple_u42 hKq hU42).1
  have hKcard : Nat.card ↥K = 25920 := CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU42
  have hKsimple : IsSimpleGroup ↥K := by
    obtain ⟨F, hF, hfin, hcard, ⟨eK⟩⟩ := hU42
    exact eK.isSimpleGroup_congr.mpr
      (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 1
        (by rw [hcard]; norm_num) 4 (by norm_num) (by decide))
  have hZ : Subgroup.center ↥K = ⊥ := by
    haveI : IsSimpleGroup ↥K := hKsimple
    have hnc : ¬ IsMulCommutative ↥K := by
      intro hc
      haveI : IsMulCommutative ↥K := hc
      have hp : Nat.Prime (Nat.card ↥K) := (Group.is_simple_iff_prime_card).1 hKsimple
      rw [hKcard] at hp
      exact (by norm_num : ¬ Nat.Prime 25920) hp
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥K) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc
  have hKrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 :=
    CFSG.SectionRank.pRank_le (by norm_num : 1 < 3)
      (fun E _ hE => T171U6.u42Rank_holds ↥K hcatK E hE)
  have hOut : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)) ≤ 0 :=
    CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 0
      (CFSG.LocalAnalysis.GLTheoremA.CatB.not_three_dvd_outer_u4two hcatK)
  exact (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer
    Nat.prime_three hZ).trans (by omega)

theorem bCardLe_holds : BCardLe := by
  intro Ω _ _ B x L hcfg hex hsmall
  obtain ⟨D, K, hpre⟩ := hex
  have hKq : CFSG.Open.IsQuasisimple ↥K := hpre.2.2.2.2.2.1.2.2
  have hBK : B ≤ Subgroup.normalizer (K : Set Ω) := S171.B_norm_K hcfg.elem hcfg.norm hpre
  have hDcard : Nat.card D = 9 := by
    rw [hpre.2.2.1]; norm_num
  have hDeq : D = B ⊓ Subgroup.centralizer (K : Set Ω) := hpre.2.2.2.2.2.2
  rcases hsmall D K hpre with hU42 | hA6
  · exact (card_le_of_mulAut_rank 3 hcfg.elem hBK hDeq hDcard
      (pRank_three_mulAut_u42 hKq hU42)).trans (by norm_num)
  · obtain ⟨e⟩ := hA6
    exact (card_le_nine_of_alt_six hcfg.elem hBK hDeq hDcard e).trans (by norm_num)

theorem wit5False_holds : Wit5False := by
  intro Ω _ _ B x L hcfg hmax hBcard hWit
  classical
  obtain ⟨E, hEel, hEcard, hEbot, hTwoLocal⟩ := hWit
  obtain ⟨P, hP2, hP1, hEP⟩ := hTwoLocal
  have htest : Nat.card (Subgroup.zpowers x : Subgroup Ω) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one]
  set E' : Subgroup Ω := E.map L.subtype with hE'def
  set P' : Subgroup Ω := P.map L.subtype with hP'def
  have hE'el : IsElemAbelian 3 E' := hEel.map L.subtype
  have hE'card : Nat.card E' = 3 ^ 5 := by
    rw [hE'def, Subgroup.card_map_of_injective L.subtype_injective, hEcard]
  have hxL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hxE : x ∉ E' := by
    rintro ⟨e, he, hex⟩
    have hee : (e : Ω) = x := hex
    have hec : e ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have hxg : x * (g : Ω) = (g : Ω) * x :=
        (Subgroup.mem_centralizer_iff.1 hxL (g : Ω) g.2).symm
      calc (g : Ω) * (e : Ω) = (g : Ω) * x := by rw [hee]
        _ = x * (g : Ω) := hxg.symm
        _ = (e : Ω) * (g : Ω) := by rw [hee]
    have h1 : e ∈ E ⊓ Subgroup.center ↥L := ⟨he, hec⟩
    rw [hEbot] at h1
    have he1 : e = 1 := by simpa using h1
    exact hcfg.ne_one (by rw [← hex]; simpa using congrArg L.subtype he1)
  set Zx : Subgroup Ω := Subgroup.zpowers x with hZxdef
  have hxel : IsElemAbelian 3 Zx := by
    rw [hZxdef, Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a rfl b rfl
      rfl
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hcfg.elem.2 x hcfg.mem
  have hcomm : ∀ a ∈ E', ∀ b ∈ Zx, a * b = b * a := by
    rintro _ ⟨e, -, rfl⟩ _ hb
    rw [hZxdef] at hb
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.zpowers_le.2 hxL hb) (e : Ω) e.2
  have hinf : E' ⊓ Zx = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨⟨e, he, rfl⟩, ha⟩
    rw [hZxdef] at ha
    have haC : (e : Ω) ∈ Subgroup.centralizer (L : Set Ω) := (Subgroup.zpowers_le.2 hxL) ha
    have hec : e ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 haC (g : Ω) g.2
    have h1 : e ∈ E ⊓ Subgroup.center ↥L := ⟨he, hec⟩
    rw [hEbot] at h1
    have he1 : e = 1 := by simpa using h1
    show L.subtype e = 1
    rw [he1]
    rfl
  have hx3 : Nat.card ↥Zx = 3 := htest
  have hFcard : Nat.card ↥(E' ⊔ Zx) = 3 ^ 6 := by
    have hnorm : Zx ≤ Subgroup.normalizer (E' : Set Ω) := by
      refine (Subgroup.zpowers_le.2 ?_).trans
        (Subgroup.centralizer_le_normalizer (E' : Set Ω))
      exact Subgroup.mem_centralizer_iff.2 fun a ha =>
        hcomm a ha x (Subgroup.mem_zpowers x)
    have hdisj : Disjoint E' Zx := disjoint_iff.mpr hinf
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E'
      Zx hnorm hdisj, hE'card, hx3]
    norm_num
  have hFel : IsElemAbelian 3 (E' ⊔ Zx) := hE'el.sup_of_commute hxel hcomm
  have hP'2 : IsPGroup 2 P' := hP2.map L.subtype
  have hP'1 : P' ≠ ⊥ := by
    intro h
    have h' : Subgroup.map L.subtype P = ⊥ := hP'def ▸ h
    exact hP1 (Subgroup.map_injective L.subtype_injective (by rw [h', Subgroup.map_bot]))
  have hP'L : P' ≤ L := hP'def ▸ Subgroup.map_subtype_le (H := L) P
  have hFN : E' ⊔ Zx ≤ Subgroup.normalizer (P' : Set Ω) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map L.subtype)
    · refine (Subgroup.zpowers_le.2 ?_).trans
        (Subgroup.centralizer_le_normalizer (P' : Set Ω))
      exact Subgroup.centralizer_le hP'L hxL
  have hle := hmax _ P' hFel hP'2 hP'1 hFN
  rw [hFcard] at hle
  have : (3 : ℕ) ^ 6 ≤ 3 ^ 5 := hle.trans hBcard
  norm_num at this

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
