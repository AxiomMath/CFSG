module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5L4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wr
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private lemma sec8t84_f7_zpowers_eq_one_or {u x : G} (hu : u * u = 1)
    (hx : x ∈ zpowers u) : x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hu, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hu, one_zpow, one_mul, zpow_one]

private lemma sec8t84_f7_mem_sup_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hconj : ∀ a ∈ H, ∀ b ∈ K, a * b * a⁻¹ ∈ K :=
    Subgroup.le_normalizer_iff.mp hHK
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, a * b = x}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
          exact ⟨a * c, H.mul_mem ha hc, (c⁻¹ * b * c) * d,
            K.mul_mem (by simpa using hconj c⁻¹ (H.inv_mem hc) b hb) hd, by group⟩
        inv_mem' := by
          rintro x ⟨a, ha, b, hb, rfl⟩
          exact ⟨a⁻¹, H.inv_mem ha, a * b⁻¹ * a⁻¹, hconj a ha b⁻¹ (K.inv_mem hb),
            by group⟩ }
    have hHP : H ≤ P := fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩
    have hKP : K ≤ P := fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩
    exact SetLike.le_def.mp (sup_le hHP hKP) hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

private lemma sec8t84_f7_mem_normalizer_inf {A B : Subgroup G} {x : G}
    (hA : x ∈ normalizer (A : Set G)) (hB : x ∈ normalizer (B : Set G)) :
    x ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  simp only [Subgroup.mem_inf]
  rw [hA y, hB y]

private lemma sec8t84_f7_isElemAb2_map_conj {E : Subgroup G} (u : G)
    (hE : IsElemAb2 E 4) : IsElemAb2 (E.map (MulAut.conj u).toMonoidHom) 4 := by
  haveI : IsMulCommutative E := hE.1.1
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rintro x hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [← map_pow, hE.1.2 e he, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective, hE.2]

theorem sec8t84_inv_L_le_T0 (F : Sec8T84Base) {t : G} {L S : Subgroup G} {z g : G}
    {B E T T1 T2 V1 V2 F1 F2 : Subgroup G} (hE : Sec8E G t L S z g B E)
    (hgood : S ⊓ L ≤ normalizer (E : Set G)) (hST : S ⊓ normalizer (E : Set G) ≤ T)
    (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (hrk : ∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → ¬ IsElemAb2 R 8) :
    ∀ x ∈ S ⊓ L, x * x = 1 → x ∈ T1 ⊔ T2 := by
  intro x hx hxsq
  by_cases hx1 : x = 1
  · rw [hx1]; exact (T1 ⊔ T2).one_mem
  have hxS : x ∈ S := hx.1
  have hxL : x ∈ L := hx.2
  have hxT : x ∈ T := hST ⟨hxS, hgood hx⟩
  rw [D.T_eq] at hxT
  have htN : t ∈ normalizer ((T1 ⊔ T2 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => sec8t84_wr_conj_mem D.wr hy
    · intro hy
      have h := sec8t84_wr_conj_mem D.wr hy
      have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
        have hsinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right D.t_sq
        calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t) := by
              rw [hsinv]; group
          _ = y := by rw [D.t_sq]; group
      rwa [h2] at h
  have hzpN : zpowers t ≤ Subgroup.normalizer ((T1 ⊔ T2 : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr htN
  obtain ⟨a, ha, b, hb, hab⟩ := (sec8t84_f7_mem_sup_of_le_normalizer hzpN).mp hxT
  rcases sec8t84_f7_zpowers_eq_one_or D.t_sq ha with ha1 | hat
  · rw [← hab, ha1, one_mul]; exact hb
  · have hsb : t * x = b := by
      rw [← hab, hat, ← mul_assoc, D.t_sq, one_mul]
    have hs : t * x ∈ T1 ⊔ T2 := by rw [hsb]; exact hb
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hE.ctx.sylow.1 hxS)
    have hssq : (t * x) * (t * x) = 1 := by
      have h1 : t * x * (t * x) = (t * t) * (x * x) := by
        calc t * x * (t * x) = t * (x * t) * x := by group
          _ = t * (t * x) * x := by rw [hxt]
          _ = (t * t) * (x * x) := by group
      rw [h1, D.t_sq, hxsq, mul_one]
    have hsne : t * x ≠ 1 := by
      intro h
      have hxeq : x = t := by
        calc x = t⁻¹ * (t * x) := by group
          _ = t⁻¹ * 1 := by rw [h]
          _ = t⁻¹ := by rw [mul_one]
          _ = t := inv_eq_of_mul_eq_one_right D.t_sq
      exact sec8t84_t_not_mem_L F hE.ctx (hxeq ▸ hxL)
    have hxord : orderOf x = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hxsq) hx1
    have hconj : IsConj t (t * x) :=
      F.h83 G t L hE.ctx.toSec3SettingLB hE.ctx.omega6m x hxord hxL
    exact (sec8t84_conj_not_mem D hrk (t * x) hs hsne hssq hconj).elim

theorem sec8t84_B_swap (F : Sec8T84Base) (hI : Asc82Step84IK) (hSw : Sec8T84OuterSwaps)
    (hKP : CFSG.Assembly.KProper Catalog G) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    ∃ γ ∈ S, ∃ B' : Subgroup G, B' ≤ S ⊓ L ∧ IsElemAb2 B' 4 ∧ B' ≠ B ∧
      B' = B.map (MulAut.conj γ).toMonoidHom := by
  obtain ⟨γ, hγS, hγout, -, -, -⟩ := sec8t84_gamma0 F hI hKP hctx
  obtain ⟨B', hB'le, hB'e, hB'ne, -, -, honly⟩ := sec8t84_SL_E16 F hctx
  refine ⟨γ, hγS, B', hB'le, hB'e, hB'ne, ?_⟩
  have hL : IsOm6M L := ⟨hctx.component.isQuasisimple, hctx.omega6m⟩
  have hγcent : γ ∈ centralizer ({t} : Set G) := hctx.sylow.1 hγS
  have hγNL : γ ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer F.h36 hctx.toSec3SettingLB γ hγcent
  have hγNS : γ ∈ normalizer (S : Set G) := Subgroup.le_normalizer hγS
  have hγN : γ ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    sec8t84_f7_mem_normalizer_inf hγNS hγNL
  have hBmap : B.map (MulAut.conj γ).toMonoidHom ≤ S ⊓ L := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hbSL : b ∈ S ⊓ L := by
      have h1 := hctx.B_le hb
      exact ⟨h1.2, h1.1⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hγN b).mp hbSL
  have hBme : IsElemAb2 (B.map (MulAut.conj γ).toMonoidHom) 4 :=
    sec8t84_f7_isElemAb2_map_conj γ hctx.B_e16
  rcases honly (B.map (MulAut.conj γ).toMonoidHom) hBmap hBme with hEqB | hEqB'
  · exfalso
    have hγNB : γ ∈ normalizer (B : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa using hEqB
    exact hSw G L hL γ hγNL hγout B (hctx.B_le.trans inf_le_left) hctx.B_e16 hγNB
  · exact hEqB'.symm

end CFSG.OddStandard.SmallF3.Omega
