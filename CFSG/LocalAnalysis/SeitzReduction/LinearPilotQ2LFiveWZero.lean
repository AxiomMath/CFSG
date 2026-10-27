module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  (e : L ≃* LinearFlag.projectiveSL n K)

theorem natCard_modelToG_eq (A : Subgroup (LinearFlag.projectiveSL n K)) :
    Nat.card (modelToG e A) = Nat.card A := by
  rw [modelToG, Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective]

theorem modelToG_inf_centralizer_eq (A B : Subgroup (LinearFlag.projectiveSL n K)) :
    modelToG e A ⊓ centralizer (modelToG e B : Set G) =
      modelToG e (A ⊓ centralizer (B : Set (LinearFlag.projectiveSL n K))) := by
  ext g
  constructor
  · rintro ⟨hgA, hgB⟩
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hgA
    refine (mem_modelToG e).2 ⟨a, Subgroup.mem_inf.2 ⟨ha, ?_⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro b hb
    have h := (mem_centralizer_iff.1 hgB) _ (symm_mem_modelToG e hb)
    have h' : e.symm b * e.symm a = e.symm a * e.symm b := Subtype.ext h
    have h'' := congrArg e h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h''
  · intro hg
    obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hg
    obtain ⟨haA, haB⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨symm_mem_modelToG e haA, ?_⟩
    rw [mem_centralizer_iff]
    intro g' hg'
    obtain ⟨b, hb, rfl⟩ := (mem_modelToG e).1 hg'
    have h := (mem_centralizer_iff.1 haB) b hb
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, h]

end Transport

section Basic

variable {G : Type*} [Group G]

theorem centralizer_zpowers_eq (g : G) :
    centralizer (zpowers g : Set G) = centralizer ({g} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem conj_mem_centralizer_singleton {g x : G} (hgx : g * x = x * g) {k : G}
    (hk : k ∈ centralizer ({x} : Set G)) : g * k * g⁻¹ ∈ centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hk ⊢
  have hgx' : g⁻¹ * x = x * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgx, mul_inv_cancel_right]
  calc g * k * g⁻¹ * x = g * k * (g⁻¹ * x) := by group
    _ = g * k * (x * g⁻¹) := by rw [hgx']
    _ = g * (k * x) * g⁻¹ := by group
    _ = g * (x * k) * g⁻¹ := by rw [hk]
    _ = (g * x) * k * g⁻¹ := by group
    _ = (x * g) * k * g⁻¹ := by rw [hgx]
    _ = x * (g * k * g⁻¹) := by group

theorem mem_normalizer_inf_centralizer {W : Subgroup G} {g x : G}
    (hgW : g ∈ normalizer (W : Set G)) (hgx : g * x = x * g) :
    g ∈ normalizer ((W ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have hgx' : g⁻¹ * x = x * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgx, mul_inv_cancel_right]
  rw [mem_normalizer_iff]
  intro h
  have hx : h ∈ centralizer ({x} : Set G) ↔ g * h * g⁻¹ ∈ centralizer ({x} : Set G) := by
    refine ⟨conj_mem_centralizer_singleton hgx, fun hk => ?_⟩
    have := conj_mem_centralizer_singleton hgx' hk
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← (mem_normalizer_iff.1 hgW h), ← hx]

theorem eq_zpowers_of_card_eq_prime {X : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hX : Nat.card X = p) {x : G} (hxX : x ∈ X) (hx1 : x ≠ 1) (hxp : x ^ p = 1) :
    X = zpowers x := by
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hle : zpowers x ≤ X := (zpowers_le).2 hxX
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; exact hp.out.ne_zero)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hX, Nat.card_zpowers, hord]

end Basic

@[expose] def LFiveWOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ c : Fin 5, ∃ W₁ : Subgroup G, Nat.card W₁ = 2 ^ 8 ∧ (∀ w ∈ W₁, w * w = 1) ∧
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) ∧
      t ∈ normalizer (W₁ : Set G) ∧
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_wZero_lFive (hW : LFiveWOneInput) (hset : SeitzSetting G L) {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin 5} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1) :
    ∃ W₀ : Subgroup G, Nat.card W₀ = 2 ^ 4 ∧ (∀ w ∈ W₀, w * w = 1) ∧
      W₀ ≤ centralizer (modelToG e X₀ : Set G) ∧ t ∈ normalizer (W₀ : Set G) ∧
      W₀ ⊓ centralizer ({t} : Set G) ≤
        modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ)) ∧
      Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 2 ∧
      ∃ y ∈ modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5))ᶜ)),
        y ∈ normalizer (W₀ : Set G) ∧ W₀ ⊓ centralizer ({y} : Set G) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard3 : (({a, b} : Finset (Fin 5))ᶜ).card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨c, hc⟩ : (({a, b} : Finset (Fin 5))ᶜ).Nonempty := Finset.card_pos.1 (by omega)
  have hca : c ≠ a := fun h => by simp [h] at hc
  have hcb : c ≠ b := fun h => by simp [h] at hc
  obtain ⟨W₁, hW₁c, hW₁2, hW₁t, htW₁, hLW₁⟩ := hW G L hset K hK e t ht hKt c
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (Subgroup.mem_inf.1 h).1
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  have hcsub : ({a, b} : Finset (Fin 5)) ⊆ {c}ᶜ := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    exact (Finset.mem_compl.1 hc) hj
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
  have hxB : x ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
    blockSL_mono hcsub (by rw [← rootSL2_eq]; exact hX₀ hxX)
  have hxN : xG ∈ normalizer (W₁ : Set G) := hLW₁ (symm_mem_modelToG e hxB)
  have hxt : xG * t = t * xG := hLt xG (e.symm x).2
  have hx3G : xG ^ 3 = 1 := by
    rw [hxG, ← Subgroup.coe_pow, ← map_pow, hxm, map_one, Subgroup.coe_one]
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  have hV₁card : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 := by
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htW₁ (by rw [hW₁c, hV₁card]; norm_num)
  set S₀ : Finset (Fin 5) := ({c}ᶜ : Finset (Fin 5)) \ {a, b} with hS₀
  have hS₀card : S₀.card = 2 := by
    rw [hS₀, Finset.card_sdiff_of_subset hcsub, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin, Finset.card_pair hab]
  have hcS₀ : c ∉ S₀ := fun h => hcc (Finset.mem_sdiff.1 h).1
  have hV₀ : W₁ ⊓ centralizer ({t} : Set G) ⊓ centralizer ({xG} : Set G) =
      modelToG e (pointRadOn c S₀) := by
    rw [hW₁t, ← hCX, modelToG_inf_centralizer_eq, pointRadical,
      pointRadOn_inf_centralizer hab hca hcb _ hX₀ hX₀c]
  have hV₀card : Nat.card (modelToG e (pointRadOn (K := K) c S₀)) = 2 ^ 2 := by
    rw [natCard_modelToG_eq, card_pointRadOn hK c hcS₀, hS₀card]
  have hS₀sub : insert c S₀ ⊆ ({a, b} : Finset (Fin 5))ᶜ := by
    intro j hj
    rw [Finset.mem_compl]
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact Finset.mem_compl.1 hc
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
  have hyx : yG * xG = xG * yG := by
    have hdisj : Disjoint S₀ ({a, b} : Finset (Fin 5)) := Finset.sdiff_disjoint
    have h := (commute_blockSL_of_disjoint hdisj y hyS₀ x (by rw [← rootSL2_eq]; exact hX₀ hxX)).eq
    have h' : e.symm y * e.symm x = e.symm x * e.symm y := by rw [← map_mul, h, map_mul]
    exact congrArg Subtype.val h'
  refine ⟨W₁ ⊓ centralizer ({xG} : Set G), ?_, fun w hw => hW₁2 w (Subgroup.mem_inf.1 hw).1,
    hCX ▸ inf_le_right, mem_normalizer_inf_centralizer htW₁ hxt.symm, ?_, ?_, yG, hyD,
    mem_normalizer_inf_centralizer hyN hyx, ?_⟩
  · rw [card_inf_centralizer_eq_sq hW₁2 ht2 htW₁ hsurj hxN hxt hx3G, hV₀, hV₀card]
    norm_num
  · rw [inf_right_comm, hV₀]
    exact modelToG_mono e ((pointRadOn_le_blockSL c S₀).trans (blockSL_mono hS₀sub))
  · rw [inf_right_comm, hV₀, hV₀card]
  · refine inf_centralizer_inf_eq_bot hW₁2 ht2 htW₁ hxt hyt ?_
    rw [hV₀, ← hCY, modelToG_inf_centralizer_eq, pointRadOn_inf_centralizer hdd' hcd hcd' S₀ hY₀ hY₀c,
      hS₀dd', Finset.sdiff_self, pointRadOn_empty, modelToG, Subgroup.map_bot, Subgroup.map_bot]

end CFSG.SeitzReduction.LinearPilot
