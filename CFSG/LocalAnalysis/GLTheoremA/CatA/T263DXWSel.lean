module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXModel
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116b
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DXW

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


private theorem le_of_isPGroup_two {G : Type*} [Group G] {C N P : Subgroup G} (hPC : P ≤ C)
    (hP2 : IsPGroup 2 ↥P) (hN : ∀ g ∈ C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) : P ≤ N := by
  intro g hg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨g, hg⟩
  exact hN g (hPC hg) ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩

private theorem ne_bot_of_le {G : Type*} [Group G] {N P : Subgroup G} (hPN : P ≤ N)
    (hP : P ≠ ⊥) : N ≠ ⊥ := by
  intro h
  exact hP (le_bot_iff.1 (hPN.trans (le_of_eq h)))

private theorem not_isSolvable_of_isComponentOf {G : Type} [Group G] {C N : Subgroup G}
    (h : CFSG.RankThree.PartOne.IsComponentOf C N) (hsolv : Group.IsSolvable ↥C) (hne : N ≠ ⊥) :
    False := by
  haveI : Group.IsPerfect ↥N := h.2.1.1
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  haveI := hsolv
  haveI : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h.1)
      (Subgroup.inclusion_injective h.1)
  exact Group.IsPerfect.not_isSolvable ↥N inferInstance

private theorem commutator_ne_bot_of_center_eq_bot {G : Type*} [Group G] {P N : Subgroup G}
    (hPN : P ≤ N) (hP : P ≠ ⊥) (hZ : Subgroup.center ↥N = ⊥) : ⁅P, N⁆ ≠ ⊥ := by
  intro hbot
  have hPcent : P ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hinf : N ⊓ Subgroup.centralizer (N : Set G) = ⊥ := by
    refine le_bot_iff.1 ?_
    rintro x ⟨hxN, hxc⟩
    have hxcen : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc y y.2)
    rw [hZ, Subgroup.mem_bot] at hxcen
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hxcen)
  exact hP (le_bot_iff.1 ((le_inf hPN hPcent).trans (le_of_eq hinf)))

private theorem dvd_card_centerQuot_of_center_eq_bot {N : Type*} [Group N] {p : ℕ}
    (hZ : Subgroup.center N = ⊥) (hp : p ∣ Nat.card N) :
    p ∣ Nat.card (N ⧸ Subgroup.center N) := by
  rw [hZ, Nat.card_congr (QuotientGroup.quotientBot (G := N)).toEquiv]
  exact hp

private theorem isComponentOf_of_commutator_le {G : Type} [Group G] {C N : Subgroup G}
    (hNC : N ≤ C) (hCN : ⁅C, C⁆ ≤ N) (hNq : CFSG.IsQuasisimple ↥N) :
    CFSG.RankThree.PartOne.IsComponentOf C N :=
  ⟨hNC, hNq,
    (K155X.l154_normal_subgroupOf_of_commutator_le hNC hCN).isSubnormal⟩

theorem modelSel_reeGamma {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) [Finite ↥(ReeTag.F4.reeGamma K a)] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ (2 * a + 1) - 1) :
    DX.ModelSel p ↥(ReeTag.F4.reeGamma K a) := by
  classical
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  intro r hrp hr1 P hPC hP2 hPne
  haveI : Fact p.Prime := ⟨hp⟩
  have hr : orderOf r = p := orderOf_eq_prime hrp hr1
  obtain ⟨N₁, hN₁C, hN₁two, hN₁uniq, hN₁comp⟩ :=
    CFSG.RankThree.PartOne.TCF.largeRee_component_data ha hK hp hp3 r hr
  have hPN₁ : P ≤ N₁ := le_of_isPGroup_two hPC hP2 hN₁two
  have hN₁ne : N₁ ≠ ⊥ := ne_bot_of_le hPN₁ hPne
  have hN₁IsComp : CFSG.RankThree.PartOne.IsComponentOf
      (Subgroup.centralizer ({r} : Set (ReeTag.F4.reeGamma K a))) N₁ := hN₁comp hN₁ne
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116b.largeRee_layer_typed ha hK hp hp3 r
    hr with hsolv | ⟨N, hNC, hCN, -, hty⟩
  · exact (not_isSolvable_of_isComponentOf hN₁IsComp hsolv hN₁ne).elim
  · have hty' : Nonempty (↥N ≃* CFSG.Blueprint.suzukiGroup a K) ∨
        Nonempty (↥N ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
      hty.symm.imp (fun ⟨e⟩ => ⟨e.symm⟩) (fun ⟨e⟩ => ⟨e.symm⟩)
    obtain ⟨hNq, hZ, hdvd⟩ :=
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.layerType_props ha hK hty'
    have hNIsComp : CFSG.RankThree.PartOne.IsComponentOf
        (Subgroup.centralizer ({r} : Set (ReeTag.F4.reeGamma K a))) N :=
      isComponentOf_of_commutator_le hNC hCN hNq
    have hNeq : N = N₁ := hN₁uniq N hNIsComp
    have hPN : P ≤ N := by rw [hNeq]; exact hPN₁
    refine ⟨N, ?_, ?_, ?_, ?_⟩
    · exact ⟨hNC, (CFSG.Open.IsSubnormal.iff_subgroupOf hNC).2 hNIsComp.2.2,
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hNq⟩
    · exact dvd_card_centerQuot_of_center_eq_bot hZ (hpq.trans hdvd)
    · exact commutator_ne_bot_of_center_eq_bot hPN hPne hZ
    · exact hPN.trans le_sup_left

end CFSG.LocalAnalysis.GLTheoremA.T263.DXW
