module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

theorem stepBound_holds : StepBound := by
  intro hU42 Ω _ _ B x L hsetup D K hpre hcat hKsimple hKcard
  classical
  obtain ⟨hcfg, -, -⟩ := hsetup
  have hDleB : D ≤ B := hpre.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hKcomp : IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set Ω)) := hpre.2.2.2.2.2.1
  have hDeq : D = B ⊓ Subgroup.centralizer (K : Set Ω) := hpre.2.2.2.2.2.2
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  have hB_elem : IsElemAbelian 3 B := hcfg.elem
  have hBL : B ≤ Subgroup.normalizer (L : Set Ω) := hcfg.norm
  have hBN : B ≤ Subgroup.normalizer (K : Set Ω) := S171.B_norm_K hB_elem hBL hpre
  have hxL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hD9 : Nat.card D = 9 := by rw [hDcard]; norm_num
  have hcenter : Subgroup.center ↥K = ⊥ := by
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
  have hconj_inj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  let α : B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hOut : ¬ 3 ∣ Nat.card (Outer ↥K) :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.not_three_dvd_outer_u4two hcat
  have hinner : ∀ b : B, α b ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    intro b
    have h := CFSG.LocalAnalysis.GLTheoremA.CatB.forall_cube_inner_of_card_outer hOut (α b) ?_
    · rwa [CFSG.ComponentClassification.OuterAutomorphisms.inner] at h
    · have hb3 : b ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hB_elem.2 (b : Ω) b.2
      rw [← map_pow, hb3, map_one]
  let kb : B → ↥K := fun b => Classical.choose (MonoidHom.mem_range.1 (hinner b))
  have hkb : ∀ b : B, α b = MulAut.conj (kb b) := fun b =>
    (Classical.choose_spec (MonoidHom.mem_range.1 (hinner b))).symm
  let φ : B →* ↥K :=
    { toFun := kb
      map_one' := hconj_inj (by rw [← hkb 1, map_one, map_one])
      map_mul' := fun a b => hconj_inj (by
        rw [← hkb (a * b), map_mul, hkb a, hkb b, ← map_mul]) }
  have hker_alpha : ∀ b : B, α b = 1 ↔ (b : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
    intro b
    have hker : α b = 1 ↔ Subgroup.inclusion hBN b ∈ K.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      exact Iff.rfl
    rw [hker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion]
  have hkerD : φ.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hb
      have hb1 : kb b = 1 := hb
      have hα1 : α b = 1 := by rw [hkb b, hb1, map_one]
      have hbc : (b : Ω) ∈ Subgroup.centralizer (K : Set Ω) := (hker_alpha b).1 hα1
      rw [hDeq]
      exact ⟨b.2, hbc⟩
    · intro hbD
      have hbc : (b : Ω) ∈ Subgroup.centralizer (K : Set Ω) := by
        have hmem : (b : Ω) ∈ B ⊓ Subgroup.centralizer (K : Set Ω) := by
          rw [← hDeq]
          exact hbD
        exact hmem.2
      have hα1 : α b = 1 := (hker_alpha b).2 hbc
      show kb b = 1
      exact hconj_inj (by rw [← hkb b, hα1, map_one])
  have hBtop : IsElemAbelian 3 (⊤ : Subgroup ↥B) := by
    haveI : IsMulCommutative ↥B := hB_elem.1
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : ↥B) (b : ↥B))⟩⟩, fun a _ => ?_⟩
    exact Subtype.ext (by simpa using hB_elem.2 (a : ↥B) a.2)
  have hrange_el : IsElemAbelian 3 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact hBtop.map φ
  have hrange_le : Nat.card φ.range ≤ 27 := hU42 ↥K hcat φ.range hrange_el
  have hker_card : Nat.card φ.ker = 9 := by
    rw [hkerD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleB).toEquiv, hD9]
  have hcardB : Nat.card B ≤ 243 := by
    have h := Subgroup.card_ker_mul_card_range φ
    calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := h.symm
      _ ≤ 9 * 27 := Nat.mul_le_mul (le_of_eq hker_card) hrange_le
      _ = 243 := by norm_num
  refine ⟨hcardB, ?_⟩
  have hcentral : ∀ b : B,
      ((b : Ω) * ((kb b : ↥K) : Ω)⁻¹) ∈ Subgroup.centralizer (K : Set Ω) := by
    intro b
    have heq : α b = K.normalizerMonoidHom
        ⟨((kb b : ↥K) : Ω), K.le_normalizer (kb b).2⟩ := by
      rw [hkb b]
      ext y
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      simp
    have hker : Subgroup.inclusion hBN b *
        ⟨((kb b : ↥K) : Ω), K.le_normalizer (kb b).2⟩⁻¹ ∈ K.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [show K.normalizerMonoidHom (Subgroup.inclusion hBN b) = α b from rfl, heq,
        mul_inv_cancel]
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    simpa using hker
  let ψ : B →* Ω :=
    { toFun := fun b => (b : Ω) * ((kb b : ↥K) : Ω)⁻¹
      map_one' := by
        have hk1 : kb 1 = 1 := map_one φ
        simp [hk1]
      map_mul' := fun a b => by
        have hkmul : kb (a * b) = kb a * kb b := map_mul φ a b
        have hcomm : ((b : Ω) * ((kb b : ↥K) : Ω)⁻¹) * ((kb a : ↥K) : Ω)⁻¹ =
            ((kb a : ↥K) : Ω)⁻¹ * ((b : Ω) * ((kb b : ↥K) : Ω)⁻¹) :=
          (Subgroup.mem_centralizer_iff.1 (hcentral b) _
            (K.inv_mem (kb a).2)).symm
        show (a : Ω) * (b : Ω) * (((kb (a * b) : ↥K) : Ω))⁻¹ =
          ((a : Ω) * (((kb a : ↥K) : Ω))⁻¹) * ((b : Ω) * (((kb b : ↥K) : Ω))⁻¹)
        rw [hkmul, Subgroup.coe_mul, mul_inv_rev]
        calc (a : Ω) * (b : Ω) * ((((kb b : ↥K) : Ω))⁻¹ * (((kb a : ↥K) : Ω))⁻¹)
            = (a : Ω) * (((b : Ω) * ((kb b : ↥K) : Ω)⁻¹) * ((kb a : ↥K) : Ω)⁻¹) := by
              group
          _ = (a : Ω) * (((kb a : ↥K) : Ω)⁻¹ * ((b : Ω) * ((kb b : ↥K) : Ω)⁻¹)) := by
              rw [hcomm]
          _ = ((a : Ω) * (((kb a : ↥K) : Ω))⁻¹) *
              ((b : Ω) * (((kb b : ↥K) : Ω))⁻¹) := by group }
  set E : Subgroup Ω := ψ.range with hEdef
  have hE_el : IsElemAbelian 3 E := by
    rw [hEdef, MonoidHom.range_eq_map]
    exact hBtop.map ψ
  have hE_cent : E ≤ Subgroup.centralizer (K : Set Ω) := by
    rintro _ ⟨b, rfl⟩
    exact hcentral b
  have hE_NL : E ≤ Subgroup.normalizer (L : Set Ω) := by
    rintro _ ⟨b, rfl⟩
    exact Subgroup.mul_mem _ (hBL b.2) (Subgroup.inv_mem _ (Subgroup.le_normalizer (hKL (kb b).2)))
  have hE_Cx : E ≤ Subgroup.centralizer ({x} : Set Ω) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxb : (b : Ω) * x = x * (b : Ω) := hB_elem.comm b.2 hcfg.mem
    have hxq : ((kb b : ↥K) : Ω) * x = x * ((kb b : ↥K) : Ω) :=
      Subgroup.mem_centralizer_iff.1 hxL (kb b : Ω) (hKL (kb b).2)
    have hxqinv : x * (((kb b : ↥K) : Ω))⁻¹ = (((kb b : ↥K) : Ω))⁻¹ * x := by
      calc x * (((kb b : ↥K) : Ω))⁻¹
          = (((kb b : ↥K) : Ω))⁻¹ * (((kb b : ↥K) : Ω) * x) *
              (((kb b : ↥K) : Ω))⁻¹ := by group
        _ = (((kb b : ↥K) : Ω))⁻¹ * (x * ((kb b : ↥K) : Ω)) *
              (((kb b : ↥K) : Ω))⁻¹ := by rw [hxq]
        _ = (((kb b : ↥K) : Ω))⁻¹ * x := by group
    calc ((b : Ω) * (((kb b : ↥K) : Ω))⁻¹) * x
        = (b : Ω) * ((((kb b : ↥K) : Ω))⁻¹ * x) := by group
      _ = (b : Ω) * (x * (((kb b : ↥K) : Ω))⁻¹) := by rw [← hxqinv]
      _ = ((b : Ω) * x) * (((kb b : ↥K) : Ω))⁻¹ := by group
      _ = (x * (b : Ω)) * (((kb b : ↥K) : Ω))⁻¹ := by rw [← hxb]
      _ = x * ((b : Ω) * (((kb b : ↥K) : Ω))⁻¹) := by group
  have hDE : D ≤ E := by
    intro d hd
    have hdB : d ∈ B := hDleB hd
    have hdc : d ∈ Subgroup.centralizer (K : Set Ω) := by
      rw [hDeq] at hd
      exact hd.2
    have hα1 : α ⟨d, hdB⟩ = 1 := (hker_alpha ⟨d, hdB⟩).2 hdc
    have hk1 : kb ⟨d, hdB⟩ = 1 := hconj_inj (by rw [← hkb ⟨d, hdB⟩, hα1, map_one])
    refine MonoidHom.mem_range.2 ⟨⟨d, hdB⟩, ?_⟩
    show (d : Ω) * ((kb ⟨d, hdB⟩ : ↥K) : Ω)⁻¹ = d
    rw [hk1, Subgroup.coe_one, inv_one, mul_one]
  have hEge9 : 9 ≤ Nat.card E := by
    have h := Subgroup.card_le_of_le hDE
    rwa [hD9] at h
  obtain ⟨e, he⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_card_eq_pow_of_isElemAbelian
    (p := 3) Nat.prime_three hE_el
  by_cases hbig : 27 ≤ Nat.card E
  · exact Or.inl ⟨E, hE_el, hE_cent, hE_NL, hE_Cx, hbig⟩
  · push Not at hbig
    have hE9 : Nat.card E = 9 := by
      rw [he] at hEge9 hbig
      have hge : 2 ≤ e := by
        refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 ?_
        calc 3 ^ 2 = 9 := by norm_num
          _ ≤ 3 ^ e := hEge9
      have hlt : e < 3 := by
        refine (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 ?_
        calc 3 ^ e < 27 := hbig
          _ = 3 ^ 3 := by norm_num
      have he2 : e = 2 := by omega
      rw [he, he2]
      norm_num
    have hED : E = D := (Subgroup.eq_of_le_of_card_ge hDE (by rw [hE9, hD9])).symm
    refine Or.inr ?_
    intro b hb
    refine ⟨ψ ⟨b, hb⟩, ?_, ((kb ⟨b, hb⟩ : ↥K) : Ω), (kb ⟨b, hb⟩).2, ?_⟩
    · have hmem : ψ ⟨b, hb⟩ ∈ E := MonoidHom.mem_range.2 ⟨⟨b, hb⟩, rfl⟩
      rwa [hED] at hmem
    · show b = ((b : Ω) * (((kb ⟨b, hb⟩ : ↥K) : Ω))⁻¹) * ((kb ⟨b, hb⟩ : ↥K) : Ω)
      group

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
