module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Br
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Yb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Gl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_tdata_of (hP : Sec8T84FactP) {t : G} {E Y1 Y2 T : Subgroup G}
    (ht : t * t = 1) (hE8 : IsElemAb2 E 8) (hXO : Sec8XO G t E Y1 Y2)
    (hT : IsSylow2Of T (normalizer (E : Set G))) (htT : t ∈ T) :
    ∃ F1 : Subgroup G, Sec8T84TData G t E T (T ⊓ Y1) (T ⊓ Y2) (E ⊓ Y1) (E ⊓ Y2) F1
      (F1.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨_, -, hTeq, hS1, hS2, hT0, hcomm, hinf, hsw1, hsw2, _, hV1T, hV2T, hconjE1, hconjE2⟩ :=
    sec8t84_tstruct ht hE8 hXO.core hT htT
  obtain ⟨H1, hY1⟩ := sec8t84_ydata1 hE8 hXO
  obtain ⟨H2, hY2⟩ := sec8t84_ydata2 hE8 hXO
  have hVn : ((E ⊓ Y1).subgroupOf (T ⊓ Y1)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hV1T, Subgroup.le_normalizer_iff]
    exact hconjE1
  obtain ⟨F1, hmod1⟩ := sec8t84_pmod_of hP hY1 hS1 hV1T hVn
  have hwr : Sec8T84Wr G t (T ⊓ Y1) (T ⊓ Y2) := ⟨ht, hcomm, hinf, hsw1, hsw2⟩
  have hsup_le : (T ⊓ Y1) ⊔ (T ⊓ Y2) ≤ Y1 ⊔ Y2 :=
    sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
  have ht_not : t ∉ (T ⊓ Y1) ⊔ (T ⊓ Y2) := fun h => hXO.t_not (hsup_le h)
  have htN : t ∈ Subgroup.normalizer (E : Set G) := hT.1 htT
  have hV2_eq : E ⊓ Y2 = (E ⊓ Y1).map (MulAut.conj t).toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨t * x * t⁻¹, ⟨?_, hXO.swap2 x hx.2⟩, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp htN x).mp hx.1
      · change t * (t * x * t⁻¹) * t⁻¹ = x
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
        rw [htinv]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [ht]; simp
    · rintro ⟨y, hy, rfl⟩
      change t * y * t⁻¹ ∈ E ⊓ Y2
      exact ⟨(Subgroup.mem_normalizer_iff.mp htN y).mp hy.1, hXO.swap1 y hy.2⟩
  have hrank8 : ∀ s ∈ (T ⊓ Y1) ⊔ (T ⊓ Y2), s * s = 1 → s ≠ 1 →
      ∃ R : Subgroup G, R ≤ centralizer ({s} : Set G) ∧ IsElemAb2 R 8 := by
    intro s hsT hs2 _
    obtain ⟨a, ha, b, hb, rfl⟩ := sec8t84_wr_decomp hwr hsT
    have haY1 : a ∈ Y1 := ha.2
    have hbY2 : b ∈ Y2 := hb.2
    have hab : a * b = b * a := hcomm a ha b hb
    have ha2b2 : a * a * (b * b) = 1 := by
      have heq : (a * b) * (a * b) = a * a * (b * b) := by
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = a * a * (b * b) := by group
      rwa [heq] at hs2
    have ha2 : a * a = 1 := by
      have ha2eq : a * a = (b * b)⁻¹ := mul_eq_one_iff_eq_inv.mp ha2b2
      have hmem : a * a ∈ (T ⊓ Y1) ⊓ (T ⊓ Y2) := by
        refine ⟨(T ⊓ Y1).mul_mem ha ha, ?_⟩
        rw [ha2eq]
        exact (T ⊓ Y2).inv_mem ((T ⊓ Y2).mul_mem hb hb)
      exact Subgroup.mem_bot.mp (hinf ▸ hmem)
    have hb2 : b * b = 1 := by
      have h := ha2b2
      rw [ha2, one_mul] at h
      exact h
    obtain ⟨D1, hO1, hD1Y1, haD1, hsq1, hc1, hcard1⟩ :=
      sec8t84_rank_piece hP hY1 haY1 ha2
    obtain ⟨D2, hO2, hD2Y2, hbD2, hsq2, hc2, hcard2⟩ :=
      sec8t84_rank_piece hP hY2 hbY2 hb2
    have hOodd : Odd (Nat.card (oddCoreIn (normalizer (E : Set G)))) :=
      CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (normalizer (E : Set G))
    have h12 : D1 ⊓ D2 ≤ oddCoreIn (normalizer (E : Set G)) :=
      (inf_le_inf hD1Y1 hD2Y2).trans hXO.inf
    have hc12 : ∀ x ∈ D1, ∀ y ∈ D2,
        x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      fun x hx y hy => hXO.comm x (hD1Y1 hx) y (hD2Y2 hy)
    have hn1 : ∀ x ∈ D1, ∀ o ∈ oddCoreIn (normalizer (E : Set G)),
        x * o * x⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      fun x hx o ho => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn
        (hXO.le1 (hD1Y1 hx)) ho
    have hn2 : ∀ x ∈ D2, ∀ o ∈ oddCoreIn (normalizer (E : Set G)),
        x * o * x⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      fun x hx o ho => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn
        (hXO.le2 (hD2Y2 hx)) ho
    exact sec8t84_rank_glue hOodd hO1 hO2 h12 hsq1 hsq2 hc1 hc2 hc12 hn1 hn2 hcard1 hcard2
      (Subgroup.mul_mem_sup haD1 hbD2) hs2
  refine ⟨F1, ?_⟩
  refine ⟨ht, ?_, ht_not, hcomm, hinf, hsw1, hsw2, hXO.E_sup, hV2_eq, rfl, hmod1, hrank8⟩
  calc T = zpowers t ⊔ (T ⊓ (Y1 ⊔ Y2)) := hTeq
    _ = zpowers t ⊔ ((T ⊓ Y1) ⊔ (T ⊓ Y2)) := by rw [hT0]

end CFSG.OddStandard.SmallF3.Omega
