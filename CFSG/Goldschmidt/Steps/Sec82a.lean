module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec83a
import CFSG.Goldschmidt.Steps.Sec84a
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec8Comp
import CFSG.Goldschmidt.Steps.G52
import CFSG.Walter.Bender1970.S3.FStar
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open CFSG.GorensteinWalter

structure Ctx {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G) (a : G)
    (H : Subgroup G) (p : ℕ) (M L : Subgroup G) : Prop where
  hset : GoldSetting G S A
  h4 : Nat.card A = 4
  ha : a ∈ A
  ha1 : a ≠ 1
  hH : H ∈ Walter.benderM a
  hHa : H = Subgroup.centralizer ({a} : Set G)
  hp : p.Prime
  hp2 : p ≠ 2
  hP1 : qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥
  hM : IsCoatom M
  hPM : Subgroup.normalizer
    ((qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ≤ M
  hMH : M ≠ H
  hCM : Subgroup.centralizer (A : Set G) ≤ M
  hS : IsSStarIn M A
  hL : GorensteinWalter.IsComponentOf L M
  hLQ : GorensteinWalter.IsComponentOf L (normalClosureIn M A)
  hQL : normalClosureIn M A = L
  hML : M ≤ Subgroup.normalizer (L : Set G)
  hAL : A ≤ L
  haL : a ∉ Subgroup.centralizer (L : Set G)
  hLH : ¬ L ≤ H
  hL2 : IsGoldL2 L

namespace Ctx

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G} {a : G}
  {H : Subgroup G} {p : ℕ} {M L : Subgroup G}

theorem hsimple (c : Ctx S A a H p M L) : IsSimpleGroup G := c.hset.isSimpleGroup

theorem hHco (c : Ctx S A a H p M L) : IsCoatom H := Walter.isCoatom_of_mem_benderM c.hH

theorem hAC (c : Ctx S A a H p M L) : A ≤ Subgroup.centralizer (A : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ hy => Sec8.comm c.hset.elem hy hx

theorem hAM (c : Ctx S A a H p M L) : A ≤ M := c.hAC.trans c.hCM

theorem hLM (c : Ctx S A a H p M L) : L ≤ M := c.hL.1

theorem hCH (c : Ctx S A a H p M L) : Subgroup.centralizer (A : Set G) ≤ H :=
  (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr c.ha)).trans
    (Walter.centralizer_le_of_mem_benderM c.hH)

theorem hAH (c : Ctx S A a H p M L) : A ≤ H := c.hAC.trans c.hCH

theorem hHO (c : Ctx S A a H p M L) :
    H = oddCoreOf H ⊔ Subgroup.centralizer (A : Set G) :=
  (Sec8.eq_oddCoreOf_sup c.hset c.h4 c.ha c.ha1 c.hH).2

theorem hLtop (c : Ctx S A a H p M L) : L ≠ ⊤ := fun h => c.hM.1 (top_le_iff.mp (h ▸ c.hLM))

theorem hCPM (c : Ctx S A a H p M L) :
    Subgroup.centralizer
      ((qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ≤ M :=
  (Subgroup.centralizer_le_normalizer _).trans c.hPM

theorem hCOM (c : Ctx S A a H p M L) :
    Subgroup.centralizer (qCoreOf H p : Set G) ≤ M :=
  (Subgroup.centralizer_le inf_le_left).trans c.hCPM

theorem hMaH (c : Ctx S A a H p M L) : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ H :=
  fun _ hy => c.hHa ▸ hy.2

end Ctx

theorem exists_ctx (h64 : S_G64) (h31 : S_G31) (h37 : S_G37) {G : Type} [Group G] [Finite G]
    {S : Sylow 2 G} {A : Subgroup G} (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) {p : ℕ}
    (hp : p.Prime) (hP1 : qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥) {M : Subgroup G}
    (hM : IsCoatom M) (hPM : Subgroup.normalizer
      ((qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ≤ M)
    (hMH : M ≠ H) (haF : a ∈ generalizedFittingSubgroupOf M) :
    ∃ L : Subgroup G, Ctx S A a H p M L := by
  have hsimple := hset.isSimpleGroup
  have hHco := Walter.isCoatom_of_mem_benderM hH
  obtain ⟨-, hHa⟩ := Sec8.mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have hAH : A ≤ H := hset.le.trans (Sec8.le_of_mem_benderM hset h4 ha hH)
  have hCH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans
      (Walter.centralizer_le_of_mem_benderM hH)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR : IsPGroup 2 (A ⊔ qCoreOf H 2 : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (S.isPGroup'.to_le hset.le) (qCoreOf_isPGroup H 2)
        (hAH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H 2)))
    have hOA : qCoreOf H 2 ≤ Subgroup.centralizer (A : Set G) := fun x hx =>
      Sec8.pGroup_le_centralizer hset h4 hR le_sup_left (Subgroup.mem_sup_right hx)
    rw [inf_eq_left.mpr hOA] at hPM
    have hHM := (le_normalizer_of_isNormalIn (qCoreOf_normal_in H 2)).trans hPM
    exact hMH ((hHco.le_iff.mp hHM).resolve_left hM.1)
  have hCM : Subgroup.centralizer (A : Set G) ≤ M :=
    (Sec8.centralizer_le_normalizer_inf hCH p).trans hPM
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := fun _ hx =>
    Subgroup.mem_centralizer_iff.mpr fun _ hy => Sec8.comm hset.elem hy hx
  have hAM : A ≤ M := hAC.trans hCM
  have hS := Sec8.sstar_of_le hset hM.1 hAM
  have haFM : a ∉ CFSG.fittingSubgroupOf M := fun h => hMH (Sec8.eq_of_le_centralizer h64 hset h4
    ha ha1 hH hp inf_le_left hM hPM haF (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Walter.fittingSubgroupOf_le_centralizer_layer M h) e he)))
  obtain ⟨L, hL, haL⟩ := Sec8.exists_component_of_not_mem_fitting haF haFM
  have hLQ := Sec8.isComponentOf_normalClosureIn hL (Sec8.le_normalClosureIn hAM ha) haL
  have hAL := Sec8.le_of_isComponentOf h31 hS hset.elem h4 hLQ
  obtain ⟨hQL, hML⟩ := Sec8.normalClosureIn_eq_of_isComponentOf h31 hset h4 hS hLQ
  have hLH : ¬ L ≤ H := Sec8.false_of_isComponentOf_le h31 hset h4 ha ha1 hH hS hLQ
  have : Fact p.Prime := ⟨hp⟩
  set X := qCoreOf H p with hX
  have hX1 : X ≠ ⊥ := fun h => hP1 (le_bot_iff.mp (h ▸ inf_le_left))
  set Z := X ⊓ Subgroup.centralizer (X : Set G) with hZ
  have hZ1 := Sec8.qCoreOf_inf_centralizer_ne_bot hp hX1
  have hXp : IsPGroup p X := qCoreOf_isPGroup H p
  have hodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hZM : Z ≤ M := fun z hz =>
    hPM (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le inf_le_left hz.2))
  have hHX : H ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hZH : Z ≤ H := inf_le_left.trans (qCoreOf_le H p)
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := fun h hh =>
    Sec8.mem_normalizer_inf (hHX hh) (Sec8.normalizer_le_normalizer_centralizer _ (hHX hh))
  have hZn : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    fun y hy => hHZ (hHa ▸ hy.2)
  have hZp : IsPGroup p Z := hXp.to_le inf_le_left
  have hZodd : Odd (Nat.card Z) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hZeq := G52.eq_componentLayerOf_sup_of_isPGroup hp hZp hZodd
  have hOFZ : oddCoreOf (CFSG.fittingSubgroupOf Z) = Z := by
    rw [Walter.fittingSubgroupOf_eq_self_of_isNilpotent hZp.isNilpotent,
      G52.oddCoreOf_eq_self_of_odd hZodd]
  obtain ⟨-, -, -, h3⟩ := h37 G M A hS hset.elem a ha ha1 Z hZM hZn hZeq
  rw [hOFZ] at h3
  have hZL : ¬ Z ≤ Subgroup.centralizer (L : Set G) := by
    intro hZL
    have hNZ : Subgroup.normalizer (Z : Set G) = H :=
      normalizer_eq_of_nontrivial_normal_in_coatom hsimple hHco hZH hZ1
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mpr hHZ)
    exact hLH (hNZ ▸ (Subgroup.le_centralizer_iff.mp hZL).trans
      (Subgroup.centralizer_le_normalizer _))
  obtain ⟨-, hL2, -⟩ := h3 L hL hZL
  exact ⟨L, hset, h4, ha, ha1, hH, hHa, hp, hp2, hP1, hM, hPM, hMH, hCM, hS, hL, hLQ, hQL, hML,
    hAL, haL, hLH, hL2⟩

end CFSG.Goldschmidt.Sec82
