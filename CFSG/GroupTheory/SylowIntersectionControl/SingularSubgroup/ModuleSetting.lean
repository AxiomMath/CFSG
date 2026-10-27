module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Centralizer
import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (O2Trivial)
open scoped IsMulCommutative

namespace GomiThm45Counterexample

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

theorem isSylowIn_autOn (h : GomiThm45Counterexample c G S) :
    IsSylowIn 2 (autOn S (gomiV G)) (autOn G (gomiV G)) :=
  AutOn.isSylowTwoOf_autOn h.isSylowTwoOf (gomiV_moduleSetting G).2

section Preimage

omit [Finite Ω]

private noncomputable def preimage_g45t (hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω))
    (P : Subgroup (MulAut ↥(gomiV G))) : Subgroup Ω :=
  Subgroup.map G.subtype (Subgroup.comap (A4.actionOn (gomiV G) G hG) P)

private theorem mem_preimage_g45t {hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    {P : Subgroup (MulAut ↥(gomiV G))} {x : Ω} :
    x ∈ preimage_g45t (G := G) hG P ↔
      ∃ hx : x ∈ G, A4.actionOn (gomiV G) G hG ⟨x, hx⟩ ∈ P := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨y.2, Subgroup.mem_comap.1 hy⟩
  · rintro ⟨hx, hxP⟩
    exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, Subgroup.mem_comap.2 hxP, rfl⟩

private theorem actionOn_eq_conjAct {hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    {x : Ω} (hx : x ∈ G) :
    A4.actionOn (gomiV G) G hG ⟨x, hx⟩ = conjAct (gomiV G) ⟨x, hG hx⟩ := by
  show conjAct (gomiV G) (Subgroup.inclusion hG ⟨x, hx⟩) =
    conjAct (gomiV G) ⟨x, hG hx⟩
  congr 1

private theorem preimage_g45t_le (hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω))
    (P : Subgroup (MulAut ↥(gomiV G))) : preimage_g45t (G := G) hG P ≤ G :=
  Subgroup.map_subtype_le _

private theorem centralizer_le_preimage_g45t (hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω))
    (P : Subgroup (MulAut ↥(gomiV G))) :
    G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ preimage_g45t (G := G) hG P := by
  intro x hx
  rw [mem_preimage_g45t]
  refine ⟨hx.1, ?_⟩
  have h1 : A4.actionOn (gomiV G) G hG ⟨x, hx.1⟩ = 1 :=
    (A4.actionOn_eq_one_iff hG ⟨x, hx.1⟩).mpr hx.2
  rw [h1]
  exact one_mem P

private theorem le_normalizer_preimage_g45t (hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω))
    {P : Subgroup (MulAut ↥(gomiV G))} (hPle : P ≤ autOn G (gomiV G))
    (hPN : (P.subgroupOf (autOn G (gomiV G))).Normal) :
    G ≤ Subgroup.normalizer (preimage_g45t (G := G) hG P : Set Ω) := by
  have hPnorm : autOn G (gomiV G) ≤
      Subgroup.normalizer (P : Set (MulAut ↥(gomiV G))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mp hPN
  rw [Subgroup.le_normalizer_iff]
  intro g hg k hk
  obtain ⟨hkG, hkP⟩ := (mem_preimage_g45t (G := G)).1 hk
  rw [mem_preimage_g45t]
  refine ⟨G.mul_mem (G.mul_mem hg hkG) (G.inv_mem hg), ?_⟩
  have hfg : A4.actionOn (gomiV G) G hG ⟨g, hg⟩ ∈ autOn G (gomiV G) :=
    (A4.mem_autOn_iff hG).2 ⟨⟨g, hg⟩, rfl⟩
  have hconj := (Subgroup.mem_normalizer_iff.mp (hPnorm hfg))
    (A4.actionOn (gomiV G) G hG ⟨k, hkG⟩)
  have harg : (⟨g * k * g⁻¹, G.mul_mem (G.mul_mem hg hkG) (G.inv_mem hg)⟩ : ↥G) =
      ⟨g, hg⟩ * ⟨k, hkG⟩ * ⟨g, hg⟩⁻¹ := by
    ext
    simp [mul_assoc]
  rw [harg, map_mul, map_mul, map_inv]
  exact hconj.mp hkP

private theorem autOn_preimage_g45t (hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω))
    {P : Subgroup (MulAut ↥(gomiV G))} (hPle : P ≤ autOn G (gomiV G)) :
    autOn (preimage_g45t (G := G) hG P) (gomiV G) = P := by
  refine le_antisymm ?_ ?_
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.1 ha
    obtain ⟨hnG, hnP⟩ := (mem_preimage_g45t (G := G)).1 hn
    rw [actionOn_eq_conjAct hnG] at hnP
    rwa [show (⟨n.1, hG hnG⟩ : Subgroup.normalizer (gomiV G : Set Ω)) = n from
      Subtype.ext rfl] at hnP
  · intro p hp
    obtain ⟨n, -, rfl⟩ := (A4.mem_autOn_iff hG).1 (hPle hp)
    have hpn : (n : Ω) ∈ preimage_g45t (G := G) hG P := by
      rw [mem_preimage_g45t]
      exact ⟨n.2, hp⟩
    have hn_eq : A4.actionOn (gomiV G) G hG n =
        conjAct (gomiV G) ⟨n.1, hG n.2⟩ := by
      simpa using actionOn_eq_conjAct (G := G) (hG := hG) (x := (n : Ω)) n.2
    rw [hn_eq]
    exact AutOn.conjAct_mem_autOn ⟨n.1, hG n.2⟩ hpn

end Preimage

theorem o2Trivial_autOn (h : GomiThm45Counterexample c G S) :
    O2Trivial (autOn G (gomiV G)) := by
  intro P hPle hPN hP2
  have hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hCN : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤
      preimage_g45t (G := G) hG P :=
    centralizer_le_preimage_g45t hG P
  have hNG : preimage_g45t (G := G) hG P ≤ G := preimage_g45t_le hG P
  have hNnorm : G ≤ Subgroup.normalizer (preimage_g45t (G := G) hG P : Set Ω) :=
    le_normalizer_preimage_g45t hG hPle hPN
  have h2 : ∀ x ∈ preimage_g45t (G := G) hG P, ∃ k : ℕ,
      x ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω) := by
    intro x hx
    obtain ⟨hxG, hxP⟩ := (mem_preimage_g45t (G := G)).1 hx
    obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hP2
      (⟨A4.actionOn (gomiV G) G hG ⟨x, hxG⟩, hxP⟩ : ↥P)
    refine ⟨k, ?_⟩
    have hxpowG : x ^ 2 ^ k ∈ G := G.pow_mem hxG _
    have hk' : A4.actionOn (gomiV G) G hG ⟨x, hxG⟩ ^ 2 ^ k = 1 := by
      have h1 := congrArg (fun y : ↥P => (y : MulAut ↥(gomiV G))) hk
      simpa using h1
    have hpow : A4.actionOn (gomiV G) G hG ⟨x ^ 2 ^ k, hxpowG⟩ =
        A4.actionOn (gomiV G) G hG ⟨x, hxG⟩ ^ 2 ^ k := by
      rw [show (⟨x ^ 2 ^ k, hxpowG⟩ : ↥G) = ⟨x, hxG⟩ ^ 2 ^ k by
        ext
        simp]
      rw [map_pow]
    rw [← A4.actionOn_eq_one_iff hG ⟨x ^ 2 ^ k, hxpowG⟩, hpow]
    exact hk'
  have hN_eq : preimage_g45t (G := G) hG P =
      G ⊓ Subgroup.centralizer (gomiV G : Set Ω) :=
    eq_centralizer_of_isPGroup_quotient h hCN hNG hNnorm h2
  have hPbot : autOn (preimage_g45t (G := G) hG P) (gomiV G) = ⊥ := by
    rw [hN_eq]
    exact AutOn.autOn_eq_bot_of_le_centralizer inf_le_right
  rw [← autOn_preimage_g45t hG hPle]
  exact hPbot

theorem sup_autOn_eq (h : GomiThm45Counterexample c G S)
    {N : Subgroup (MulAut ↥(gomiV G))} (hNG : N ≤ autOn G (gomiV G))
    (hN : (N.subgroupOf (autOn G (gomiV G))).Normal) (h2 : 2 ∣ Nat.card N) :
    N ⊔ autOn S (gomiV G) = autOn G (gomiV G) := by
  have hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hS : S ≤ Subgroup.normalizer (gomiV G : Set Ω) := h.isSylowTwoOf.1.trans hG
  have hN₀G : preimage_g45t (G := G) hG N ≤ G := preimage_g45t_le hG N
  have hN₀norm : G ≤ Subgroup.normalizer (preimage_g45t (G := G) hG N : Set Ω) :=
    le_normalizer_preimage_g45t hG hNG hN
  have hN₀aut : autOn (preimage_g45t (G := G) hG N) (gomiV G) = N :=
    autOn_preimage_g45t hG hNG
  have hsup : preimage_g45t (G := G) hG N ⊔ S = G := by
    by_contra hne
    have hQ_sylow : IsSylowTwoOf (pCoreOf 2 (preimage_g45t (G := G) hG N))
        (preimage_g45t (G := G) hG N) :=
      isSylowTwoOf_pCoreOf_of_sup_ne h hN₀G hN₀norm hne
    have hQnorm : G ≤
        Subgroup.normalizer (pCoreOf 2 (preimage_g45t (G := G) hG N) : Set Ω) :=
      hN₀norm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    have hQle : autOn (pCoreOf 2 (preimage_g45t (G := G) hG N)) (gomiV G) ≤
        autOn G (gomiV G) :=
      AutOn.autOn_mono ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hN₀G)
    have hQaut_normal :
        ((autOn (pCoreOf 2 (preimage_g45t (G := G) hG N)) (gomiV G)).subgroupOf
          (autOn G (gomiV G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr
        (AutOn.autOn_le_normalizer_autOn hQnorm)
    have hQaut_2 : IsPGroup 2
        (autOn (pCoreOf 2 (preimage_g45t (G := G) hG N)) (gomiV G)) :=
      AutOn.isPGroup_autOn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    have hQaut_bot : autOn (pCoreOf 2 (preimage_g45t (G := G) hG N)) (gomiV G) = ⊥ :=
      o2Trivial_autOn h _ hQle hQaut_normal hQaut_2
    have hN_sylow : IsSylowTwoOf
        (autOn (pCoreOf 2 (preimage_g45t (G := G) hG N)) (gomiV G))
        (autOn (preimage_g45t (G := G) hG N) (gomiV G)) :=
      AutOn.isSylowTwoOf_autOn hQ_sylow (hN₀G.trans hG)
    rw [hQaut_bot, hN₀aut] at hN_sylow
    have hodd : ¬ 2 ∣ Nat.card N := by
      simpa [Subgroup.bot_subgroupOf, Subgroup.index_bot] using hN_sylow.2.2
    exact hodd h2
  have hsupAut : autOn G (gomiV G) =
      autOn (preimage_g45t (G := G) hG N ⊔ S) (gomiV G) := by
    rw [hsup]
  rw [hsupAut, AutOn.autOn_sup_eq (hN₀G.trans hG) hS, hN₀aut]

end GomiThm45Counterexample

end CFSG.GroupTheory
