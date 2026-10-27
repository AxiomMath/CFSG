module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NJf1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

private theorem pCoreOf_top_eq (X : Type) [Group X] :
    pCoreOf 2 (⊤ : Subgroup X) = pCore 2 X := by
  rw [pCoreOf,
    show (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom from rfl]
  exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := X))

private theorem pCoreOf_top_normal (X : Type) [Group X] :
    (pCoreOf 2 (⊤ : Subgroup X)).Normal := by
  rw [pCoreOf_top_eq X]
  exact CFSG.LieType.BorelTits.pCore_normal 2

private theorem pCoreOf_top_map_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (pCoreOf 2 (⊤ : Subgroup X)).map e.toMonoidHom = pCoreOf 2 (⊤ : Subgroup Y) := by
  rw [pCoreOf_top_eq X, pCoreOf_top_eq Y]
  exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e

private theorem map_centralizer_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (S : Subgroup X) :
    (centralizer (S : Set X)).map e.toMonoidHom =
      centralizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  apply le_antisymm
  · rw [Subgroup.coe_map e.toMonoidHom S]
    exact map_centralizer_le_centralizer_image (S : Set X) e.toMonoidHom
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    rw [Subgroup.mem_centralizer_iff] at hy
    exact hy (e s) (Subgroup.mem_map_of_mem e.toMonoidHom hs)

private theorem centralizer_map_eq {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {S : Subgroup X} {T : Subgroup Y} (hST : S.map e.toMonoidHom = T)
    (hS : centralizer (S : Set X) = S) : centralizer (T : Set Y) = T := by
  rw [← hST, ← map_centralizer_mulEquiv e S, hS]

private noncomputable def topQuotEquiv {X : Type} [Group X] (N : Subgroup X) [N.Normal] :
    (↥(⊤ : Subgroup X) ⧸ N.subgroupOf ⊤) ≃* (X ⧸ N) :=
  QuotientGroup.congr (N.subgroupOf ⊤) N (Subgroup.topEquiv (G := X))
    (Subgroup.map_subgroupOf_eq_of_le le_top)

private theorem quotEquiv_of_secProp_top {X : Type} [Group X] [Finite X] (N : Subgroup X)
    [N.Normal]
    (h : SecProp (⊤ : Subgroup X) N (fun Z _ _ _ => Nonempty (Z ≃* GL (Fin 3) (ZMod 2)))) :
    Nonempty (X ⧸ N ≃* GL (Fin 3) (ZMod 2)) := by
  unfold SecProp at h
  obtain ⟨_, hP⟩ := h
  obtain ⟨f⟩ := hP
  exact ⟨(topQuotEquiv N).symm.trans f⟩

private theorem secProp_top_of_quotEquiv {X : Type} [Group X] [Finite X] (N : Subgroup X)
    [N.Normal]
    (h : Nonempty (X ⧸ N ≃* GL (Fin 3) (ZMod 2))) :
    SecProp (⊤ : Subgroup X) N (fun Z _ _ _ => Nonempty (Z ≃* GL (Fin 3) (ZMod 2))) := by
  refine ⟨inferInstance, ?_⟩
  obtain ⟨f⟩ := h
  exact ⟨(topQuotEquiv N).trans f⟩

theorem y7n_ext26_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : Sec2.IsExt26 1 X) : Sec2.IsExt26 1 Y := by
  obtain ⟨h1, h2, h3⟩ := h
  have hmap := pCoreOf_top_map_mulEquiv e
  haveI := pCoreOf_top_normal X
  haveI := pCoreOf_top_normal Y
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨f⟩ := h1
    exact ⟨((Subgroup.equivMapOfInjective (pCoreOf 2 (⊤ : Subgroup X)) e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmap)).symm.trans f⟩
  · refine secProp_top_of_quotEquiv (pCoreOf 2 (⊤ : Subgroup Y)) ?_
    obtain ⟨f⟩ := quotEquiv_of_secProp_top (pCoreOf 2 (⊤ : Subgroup X)) h2
    exact ⟨(QuotientGroup.congr (pCoreOf 2 (⊤ : Subgroup X))
      (pCoreOf 2 (⊤ : Subgroup Y)) e hmap).symm.trans f⟩
  · have h3' : centralizer ((pCore 2 X : Subgroup X) : Set X) = pCore 2 X := by
      rwa [pCoreOf_top_eq X] at h3
    have hmap' : (pCore 2 X).map e.toMonoidHom = pCore 2 Y := by
      rwa [pCoreOf_top_eq X, pCoreOf_top_eq Y] at hmap
    rw [pCoreOf_top_eq Y]
    exact centralizer_map_eq e hmap' h3'

theorem y7n_nonsplit_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : ¬ SplitsOver (⊤ : Subgroup X) (pCoreOf 2 (⊤ : Subgroup X))) :
    ¬ SplitsOver (⊤ : Subgroup Y) (pCoreOf 2 (⊤ : Subgroup Y)) := by
  intro hY
  apply h
  have hcomap : pCoreOf 2 (⊤ : Subgroup X) =
      (pCoreOf 2 (⊤ : Subgroup Y)).comap e.toMonoidHom := by
    rw [← pCoreOf_top_map_mulEquiv e, Subgroup.comap_map_eq_self_of_injective e.injective]
  unfold SplitsOver at hY ⊢
  obtain ⟨C, _hCtop, hCinf, hCsup⟩ := hY
  refine ⟨C.comap e.toMonoidHom, le_top, ?_, ?_⟩
  · rw [hcomap, ← Subgroup.comap_inf, hCinf, MonoidHom.comap_bot]
    exact MonoidHom.ker_eq_bot e.toMonoidHom e.injective
  · rw [hcomap, Subgroup.comap_sup_eq e.toMonoidHom (pCoreOf 2 (⊤ : Subgroup Y)) C
      e.surjective, hCsup, Subgroup.comap_top]

theorem y7n_card_of_ext26 {X : Type} [Group X] [Finite X] (h : Sec2.IsExt26 1 X) :
    Nat.card X = 1344 := by
  obtain ⟨h1, h2, _h3⟩ := h
  haveI := pCoreOf_top_normal X
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCoreOf 2 (⊤ : Subgroup X))]
  have hcore : Nat.card (pCoreOf 2 (⊤ : Subgroup X)) = 8 := by
    obtain ⟨f⟩ := h1
    rw [Nat.card_congr f.toEquiv, Nat.card_fun]
    have hz : Nat.card (Multiplicative (ZMod (2 ^ 1))) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      norm_num
    rw [hz, Nat.card_fin]
    norm_num
  have hquot : Nat.card (X ⧸ pCoreOf 2 (⊤ : Subgroup X)) = 168 := by
    obtain ⟨f⟩ := quotEquiv_of_secProp_top (pCoreOf 2 (⊤ : Subgroup X)) h2
    rw [← CFSG.ComponentClassification.GHarris.card_GL32_gh]
    exact Nat.card_congr f.toEquiv
  rw [hquot, hcore]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7n_Lam_facts {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (h79 : c.Fact79) {L1 : Subgroup G}
    (hL1 : IsCompPre c.s L1) :
    Sec2.IsExt26 1 ↥⁅L1, L1⁆ ∧
      ¬ SplitsOver (⊤ : Subgroup ↥⁅L1, L1⁆) (pCoreOf 2 (⊤ : Subgroup ↥⁅L1, L1⁆)) ∧
      Nat.card ↥⁅L1, L1⁆ = 1344 ∧
      ∀ x ∈ ⁅L1, L1⁆, (∀ y ∈ ⁅L1, L1⁆, y * x = x * y) → x = 1 := by
  obtain ⟨_, ⟨e⟩, hcent⟩ := h79 L1 hL1
  obtain ⟨hExt, hNs⟩ := y7n_jf_ext26 hH
  let e' : ↥⁅L1, L1⁆ ≃* ↥(JF c.s) := e.trans (MulEquiv.subgroupCongr hcent)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact y7n_ext26_of_mulEquiv e'.symm hExt
  · exact y7n_nonsplit_of_mulEquiv e'.symm hNs
  · exact (Nat.card_congr e'.toEquiv).trans (y7n_card_of_ext26 hExt)
  · intro x hx hxc
    have hmem : (e' ⟨x, hx⟩ : G) ∈ JF c.s := (e' ⟨x, hx⟩).2
    have hcomm : ∀ y ∈ JF c.s, y * (e' ⟨x, hx⟩ : G) = (e' ⟨x, hx⟩ : G) * y := by
      intro y hy
      obtain ⟨z, hz⟩ := e'.surjective ⟨y, hy⟩
      have hyz : (e' z : G) = y := congrArg Subtype.val hz
      rw [← hyz]
      have hz' : z * ⟨x, hx⟩ = ⟨x, hx⟩ * z := Subtype.ext (hxc (z : G) z.2)
      have hz'' : e' z * e' ⟨x, hx⟩ = e' ⟨x, hx⟩ * e' z := by
        rw [← map_mul, ← map_mul, hz']
      exact congrArg Subtype.val hz''
    have h1 : (e' ⟨x, hx⟩ : G) = 1 := y7n_jf_center hH _ hmem hcomm
    have h2 : e' ⟨x, hx⟩ = 1 := Subtype.ext h1
    have h3 : (⟨x, hx⟩ : ↥⁅L1, L1⁆) = 1 := e'.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3

end CFSG.OddStandard.HigherRank.YamadaG23
