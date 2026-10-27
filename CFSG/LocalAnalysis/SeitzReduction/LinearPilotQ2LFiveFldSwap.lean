module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveHRoot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSGen

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section WZero

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem wZero_le_centralizerPerfectCore_of_wOne (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b c : Fin 5} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) {W₁ : Subgroup G} (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW₁ : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G)) :
    W₁ ⊓ centralizer (modelToG e X₀ : Set G) ≤ centralizerPerfectCore (modelToG e X₀) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  have hcsub : ({a, b} : Finset (Fin 5)) ⊆ {c}ᶜ := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton]
    intro hjc
    rcases Finset.mem_insert.1 hj with h | h
    · exact hca (hjc ▸ h)
    · exact hcb (hjc ▸ Finset.mem_singleton.1 h)
  obtain ⟨x, hxX, -, -, -, hx1, hxm, -⟩ := exists_lift_torusQ1 hX₀ hX₀c
  rw [hK] at hxm
  have hX₀z : X₀ = zpowers x :=
    eq_zpowers_of_card_eq_prime (p := 3) (by rw [hX₀c, hK]) hxX hx1 hxm
  set xG : G := ((e.symm x : L) : G) with hxG
  have hXz : modelToG e X₀ = zpowers xG := by
    rw [hX₀z, modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hCX : centralizer (modelToG e X₀ : Set G) = centralizer ({xG} : Set G) := by
    rw [hXz, centralizer_zpowers_eq]
  have hxt : xG * t = t * xG := hLt xG (e.symm x).2
  set S₀ : Finset (Fin 5) := ({c}ᶜ : Finset (Fin 5)) \ {a, b} with hS₀
  have hS₀card : S₀.card = 2 := by
    rw [hS₀, Finset.card_sdiff_of_subset hcsub, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin, Finset.card_pair hab]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  have hcS₀ : c ∉ S₀ := fun h => hcc (Finset.mem_sdiff.1 h).1
  have hV₀ : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({xG} : Set G) =
      modelToG e (pointRadOn c S₀) := by
    rw [hW₁t, ← hCX, modelToG_inf_centralizer_eq, pointRadical,
      pointRadOn_inf_centralizer hab hca hcb _ hX₀ hX₀c]
  have hS₀sub : insert c S₀ ⊆ ({a, b} : Finset (Fin 5))ᶜ := by
    intro j hj
    rw [Finset.mem_compl]
    rcases Finset.mem_insert.1 hj with rfl | hj
    · intro hjab
      rcases Finset.mem_insert.1 hjab with h | h
      · exact hca h
      · exact hcb (Finset.mem_singleton.1 h)
    · exact (Finset.mem_sdiff.1 hj).2
  obtain ⟨d, d', hdd', hS₀dd'⟩ := Finset.card_eq_two.1 hS₀card
  have hdS₀ : d ∈ S₀ := by rw [hS₀dd']; simp
  have hd'S₀ : d' ∈ S₀ := by rw [hS₀dd']; simp
  have hcd : c ≠ d := fun h => hcS₀ (h ▸ hdS₀)
  have hcd' : c ≠ d' := fun h => hcS₀ (h ▸ hd'S₀)
  obtain ⟨Y₀, hY₀, -, hY₀c⟩ := exists_torusQ1 (K := K) (n := 5) hdd'
  obtain ⟨y, hyY, -, -, -, hy1, hym, -⟩ := exists_lift_torusQ1 hY₀ hY₀c
  rw [hK] at hym
  have hY₀z : Y₀ = zpowers y :=
    eq_zpowers_of_card_eq_prime (p := 3) (by rw [hY₀c, hK]) hyY hy1 hym
  set yG : G := ((e.symm y : L) : G) with hyG
  have hYz : modelToG e Y₀ = zpowers yG := by
    rw [hY₀z, modelToG, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hCY : centralizer (modelToG e Y₀ : Set G) = centralizer ({yG} : Set G) := by
    rw [hYz, centralizer_zpowers_eq]
  have hyS₀ : y ∈ blockSL (K := K) S₀ := by
    rw [hS₀dd', ← rootSL2_eq]
    exact hY₀ hyY
  have hyD : yG ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ)) :=
    symm_mem_modelToG e (blockSL_mono ((Finset.subset_insert c S₀).trans hS₀sub) hyS₀)
  have hyN : yG ∈ normalizer (W₁ : Set G) :=
    hLW₁ (symm_mem_modelToG e (blockSL_mono (fun j hj => (Finset.mem_sdiff.1 hj).1) hyS₀))
  have hyt : yG * t = t * yG := hLt yG (e.symm y).2
  have hW₀y : W₁ ⊓ centralizer ({xG} : Set G) ⊓ centralizer ({yG} : Set G) = ⊥ := by
    refine inf_centralizer_inf_eq_bot hW₁2 ht2 htW₁ hxt hyt ?_
    rw [hV₀, ← hCY, modelToG_inf_centralizer_eq, pointRadOn_inf_centralizer hdd' hcd hcd' S₀ hY₀
      hY₀c, hS₀dd', Finset.sdiff_self, pointRadOn_empty, modelToG, Subgroup.map_bot,
      Subgroup.map_bot]
  have htX : t ∈ centralizer (modelToG e X₀ : Set G) := centralizer_le (modelToG_le e X₀) htC
  obtain ⟨-, hDX, hDq, -⟩ := neighbour_hyps_linear_two hset hK e (by norm_num) htC ht hab hX₀
    hX₀c rfl htX rfl
  have hDE : modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ)) ≤
      centralizerPerfectCore (modelToG e X₀) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDX (Subgroup.isPerfect_iff.mp hDq.1)
  have hWc : ∀ v ∈ W₁ ⊓ centralizer (modelToG e X₀ : Set G),
      ∀ w ∈ W₁ ⊓ centralizer (modelToG e X₀ : Set G), v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 (Subgroup.mem_inf.1 hv).1 (Subgroup.mem_inf.1 hw).1
  have hyW₀ : yG ∈ normalizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) :
      Set G) :=
    mem_normalizer_inf_of_mem hyN (le_normalizer (hDX hyD))
  refine le_centralizerPerfectCore_of_inf_centralizer_eq_bot hWc inf_le_right (hDE hyD) hyW₀ ?_
  rw [hCX]
  exact hW₀y

end WZero

end CFSG.SeitzReduction.LinearPilot
