module

public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_sylow_of_not_exists_mul_eq [IsSimpleGroup G]
    (hnonab : ∃ g h : G, g * h ≠ h * g) {J : Subgroup G} (hst : IsStandardSubgroup J)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G))
    (hnotJ : ∀ g : G, g⁻¹ * t * g ∉ J)
    (S : Sylow 2 G) (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (htS : t ∈ (S : Subgroup G)) {z : G} (hzJ : z ∈ J)
    (hZ : ∀ w ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), s * w = w * s) → orderOf w = 2 →
      w = z ∨ w = t ∨ w = z * t)
    {s : G} (hsS : s ∈ (S : Subgroup G)) (hs : orderOf s = 2)
    (hsout : ¬ ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), s = j * c)
    (hprod : ∀ b ∈ (S : Subgroup G), (¬ ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), b = j * c) →
      ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), b * s = j * c)
    (hinner : ∀ b ∈ (S : Subgroup G), (∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), b = j * c) →
      b ∈ J ∨ b * t ∈ J) : False := by
  classical
  have hs2 : s * s = 1 := by
    rw [← pow_two, ← hs]
    exact pow_orderOf_eq_one s
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcomm_st : s * t = t * s := mem_centralizer_singleton_iff.1 (hSt hsS)
  have hsN : s ∈ Subgroup.normalizer (J : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hst.assembly htJ ht).1 (hSt hsS)
  have hconjJ : ∀ j ∈ J, s * j * s⁻¹ ∈ J := fun j hj =>
    (Subgroup.mem_normalizer_iff.1 hsN j).1 hj
  let M : Subgroup G :=
    { carrier := {x | x ∈ J ∨ x * s ∈ J}
      one_mem' := Or.inl J.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (J.mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact J.mul_mem hx hy)
        · refine Or.inr ?_
          have h2 : (x * s) * (s * y * s⁻¹) ∈ J := J.mul_mem hx (hconjJ y hy)
          have e : (x * y) * s = (x * s) * (s * y * s⁻¹) := by
            have h1 : (x * s) * (s * y * s⁻¹) = x * ((s * s) * (y * s⁻¹)) := by group
            rw [h1, hs2, one_mul, hsinv, ← mul_assoc]
          rw [e]
          exact h2
        · refine Or.inl ?_
          have h2 : (x * s) * (s * (y * s) * s⁻¹) ∈ J := J.mul_mem hx (hconjJ (y * s) hy)
          have e : x * y = (x * s) * (s * (y * s) * s⁻¹) := by
            have h1 : (x * s) * (s * (y * s) * s⁻¹) = x * ((s * s) * ((y * s) * s⁻¹)) := by
              group
            rw [h1, hs2, one_mul]
            have hy' : (y * s) * s⁻¹ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]
            rw [hy']
          rw [e]
          exact h2
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (J.inv_mem hx)
        · refine Or.inr ?_
          have h2 : s * (x * s)⁻¹ * s⁻¹ ∈ J := hconjJ _ (J.inv_mem hx)
          have e : x⁻¹ * s = s * (x * s)⁻¹ * s⁻¹ := by
            rw [hsinv]
            group
          rw [e]
          exact h2 }
  have hzM : z ∈ M := Or.inl hzJ
  have htM : t ∉ M := by
    rintro (h1 | h2)
    · exact hnotJ 1 (by simpa using h1)
    · refine hsout ⟨t * s, h2, t⁻¹, Subgroup.inv_mem _ htJ, ?_⟩
      rw [htinv]
      symm
      calc (t * s) * t = t * (s * t) := by rw [mul_assoc]
        _ = t * (t * s) := by rw [hcomm_st]
        _ = (t * t) * s := by rw [mul_assoc]
        _ = s := by rw [ht2, one_mul]
  have hztM : z * t ∉ M := by
    rintro (h1 | h2)
    · refine hnotJ 1 ?_
      have e : (1 : G)⁻¹ * t * 1 = z⁻¹ * (z * t) := by group
      rw [e]
      exact J.mul_mem (J.inv_mem hzJ) h1
    · exact htM (Or.inr (by
        have e : t * s = z⁻¹ * ((z * t) * s) := by group
        rw [e]
        exact J.mul_mem (J.inv_mem hzJ) h2))
  set S₀ : Subgroup G := (S : Subgroup G) ⊓ M with hS₀
  have htS₀ : t ∉ S₀ := fun h => htM h.2
  have hztS₀ : z * t ∉ S₀ := fun h => hztM h.2
  have hrel : S₀.relIndex (S : Subgroup G) = 2 := by
    refine (Subgroup.index_eq_two_iff_exists_notMem_and).2 ⟨⟨t, htS⟩, ?_, ?_⟩
    · intro hmem
      exact htS₀ (Subgroup.mem_subgroupOf.1 hmem)
    · intro b
      show (b * ⟨t, htS⟩ : ↥(S : Subgroup G)) ∈ S₀.subgroupOf (S : Subgroup G) ∨
        b ∈ S₀.subgroupOf (S : Subgroup G)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      show ((b : G) * t) ∈ S₀ ∨ (b : G) ∈ S₀
      by_cases hb : ∃ j ∈ J, ∃ c ∈ centralizer (J : Set G), (b : G) = j * c
      · rcases hinner (b : G) b.2 hb with hbJ | hbtJ
        · exact Or.inr ⟨b.2, Or.inl hbJ⟩
        · exact Or.inl ⟨(S : Subgroup G).mul_mem b.2 htS, Or.inl hbtJ⟩
      · obtain ⟨j, hj, c, hc, hbc⟩ := hprod (b : G) b.2 hb
        have hbsS : (b : G) * s ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem b.2 hsS
        rcases hinner ((b : G) * s) hbsS ⟨j, hj, c, hc, hbc⟩ with hJ | hJ
        · exact Or.inr ⟨b.2, Or.inr hJ⟩
        · refine Or.inl ⟨(S : Subgroup G).mul_mem b.2 htS, Or.inr ?_⟩
          have e : ((b : G) * t) * s = ((b : G) * s) * t := by
            rw [mul_assoc, ← hcomm_st, ← mul_assoc]
          rw [e]
          exact hJ
  have hmin : ∀ y ∈ (S : Subgroup G), y ∉ S₀ → orderOf t ≤ orderOf y := by
    intro y hyS hyS₀
    have hy1 : y ≠ 1 := fun h1 => hyS₀ (by rw [h1]; exact S₀.one_mem)
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    have h2 : 0 < orderOf y := orderOf_pos y
    rw [ht]
    omega
  have hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hNn hNidx
    rcases Subgroup.Normal.eq_bot_or_eq_top N with hbot | htop
    · have hcard : Nat.card G = 2 := by
        rw [hbot, Subgroup.index_bot] at hNidx
        exact hNidx
      obtain ⟨x, y, hxy⟩ := hnonab
      refine hxy ?_
      have h2 : ∀ g : G, orderOf g ∣ 2 := by
        intro g
        rw [← hcard]
        exact orderOf_dvd_natCard g
      exact Commute.of_orderOf_dvd_two h2 x y
    · rw [htop, Subgroup.index_top] at hNidx
      exact absurd hNidx (by norm_num)
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hSidx : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
  obtain ⟨g, hgS₀, hext⟩ :=
    CFSG.EvenSporTransfer.exists_extremal_conj_of_thompson (T := (S : Subgroup G)) (U := S₀)
      hSp hSidx inf_le_left hrel htS htS₀ hmin hno
  set v : G := g⁻¹ * t * g with hvdef
  have hvS : v ∈ (S : Subgroup G) := hgS₀.1
  have hv2 : orderOf v = 2 := by
    have hsc : SemiconjBy g⁻¹ t v := by
      rw [hvdef]
      show g⁻¹ * t = (g⁻¹ * t * g) * g⁻¹
      group
    rw [← SemiconjBy.orderOf_eq g⁻¹ hsc, ht]
  have hCt' : centralizer ({v} : Set G) =
      (centralizer ({t} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    ext y
    constructor
    · intro hy
      rw [mem_centralizer_singleton_iff] at hy
      refine ⟨g * y * g⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        calc g * y * g⁻¹ * t = g * (y * v) * g⁻¹ := by rw [hvdef]; group
          _ = g * (v * y) * g⁻¹ := by rw [hy]
          _ = t * (g * y * g⁻¹) := by rw [hvdef]; group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
    · rintro ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * c * g * v = g⁻¹ * (c * t) * g := by rw [hvdef]; group
        _ = g⁻¹ * (t * c) * g := by rw [hc]
        _ = g⁻¹ * t * g * (g⁻¹ * c * g) := by group
  set C : Subgroup G := centralizer ({v} : Set G) with hC
  have hCt : C = (centralizer ({t} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hC]
    exact hCt'
  set Q : Subgroup G := (S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom with hQdef
  have hQle : Q ≤ C := by
    rw [hCt, hQdef]
    exact Subgroup.map_mono hSt
  have hQp : IsPGroup 2 Q := hSp.map (MulAut.conj g⁻¹).toMonoidHom
  have hQcard : Nat.card ↥Q = Nat.card ↥(S : Subgroup G) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective
  have hA_p : IsPGroup 2 ↥(((S : Subgroup G) ⊓ C).subgroupOf C) :=
    hext.2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (S : Subgroup G) ⊓ C ≤ C)).symm
  have hP2 : ¬ 2 ∣ (((S : Subgroup G) ⊓ C).subgroupOf C).index := hext.2.2
  set A : Sylow 2 ↥C := hA_p.toSylow hP2 with hAdef
  have hAcoe : ((A : Subgroup ↥C)) = ((S : Subgroup G) ⊓ C).subgroupOf C := by
    rw [hAdef]
    exact IsPGroup.toSylow_coe hA_p hP2
  have hQsub_p : IsPGroup 2 ↥(Q.subgroupOf C) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQle).symm
  obtain ⟨R, hQR⟩ := hQsub_p.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) A R
  have hRcard : Nat.card ↥R = Nat.card ↥((S : Subgroup G) ⊓ C) := by
    calc Nat.card ↥R = Nat.card ↥(c • A) := by rw [hc]
      _ = Nat.card ↥A := (Nat.card_congr (Sylow.equivSMul A c).toEquiv).symm
      _ = Nat.card ↥((A : Subgroup ↥C)) := rfl
      _ = Nat.card ↥(((S : Subgroup G) ⊓ C).subgroupOf C) := by rw [hAcoe]
      _ = Nat.card ↥((S : Subgroup G) ⊓ C) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcard_le : Nat.card ↥(S : Subgroup G) ≤ Nat.card ↥((S : Subgroup G) ⊓ C) := by
    rw [← hQcard]
    calc Nat.card ↥Q = Nat.card ↥(Q.subgroupOf C) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle)).symm
      _ ≤ Nat.card ↥R := Subgroup.card_le_of_le hQR
      _ = Nat.card ↥((S : Subgroup G) ⊓ C) := hRcard
  have hSeq : (S : Subgroup G) ⊓ C = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left hcard_le
  have hSleC : (S : Subgroup G) ≤ C := hSeq ▸ inf_le_right
  rcases hZ v hvS (fun b hb => mem_centralizer_singleton_iff.1 (hSleC hb)) hv2 with hvz | hvt | hvzt
  · refine hnotJ g ?_
    rw [← hvdef, hvz]
    exact hzJ
  · exact htS₀ (hvt ▸ hgS₀)
  · exact hztS₀ (hvzt ▸ hgS₀)

end CFSG.ComponentClassification.GrSLit.L34Sec5S

