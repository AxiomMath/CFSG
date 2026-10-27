module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFivePRoot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFivePEmb
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSFive

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Basic

variable {G : Type*} [Group G]

theorem card_inf_centralizer_conj_le [Finite G] {W : Subgroup G} {g : G}
    (hg : g ∈ normalizer (W : Set G)) (k : G) :
    Nat.card (W ⊓ centralizer ({g * k * g⁻¹} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({k} : Set G) : Subgroup G) := by
  have hg' : g⁻¹ ∈ normalizer (W : Set G) := inv_mem hg
  let f : (W ⊓ centralizer ({g * k * g⁻¹} : Set G) : Subgroup G) →
      (W ⊓ centralizer ({k} : Set G) : Subgroup G) := fun w =>
    ⟨g⁻¹ * w * g, by
      obtain ⟨hwW, hwk⟩ := Subgroup.mem_inf.1 w.2
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h1 := (mem_normalizer_iff.1 hg' (w : G)).1 hwW
        rwa [inv_inv] at h1
      · rw [mem_centralizer_singleton_iff] at hwk ⊢
        calc g⁻¹ * (w : G) * g * k = g⁻¹ * ((w : G) * (g * k * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * k * g⁻¹) * (w : G)) * g := by rw [hwk]
          _ = k * (g⁻¹ * (w : G) * g) := by group⟩
  have hf : Function.Injective f := by
    intro w w' h
    have h1 : g⁻¹ * (w : G) * g = g⁻¹ * (w' : G) * g := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  exact Nat.card_le_card_of_injective f hf

end Basic

theorem xab_commutator {n : ℕ} {K : Type*} [Field K] {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) (a b : K) :
    xab hij a * xab hjl b * (xab hij a)⁻¹ * (xab hjl b)⁻¹ = xab hil (a * b) := by
  have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil a b
  rw [commutatorElement_def] at h
  rw [xab, xab, xab, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h]

theorem compl_sdiff_pair_eq_of_equiv {c : Fin 5} (σ : Fin 4 ≃ ({c}ᶜ : Finset (Fin 5)))
    {i j k l : Fin 4} (hcov : ∀ m : Fin 4, m = i ∨ m = j ∨ m = k ∨ m = l) (hki : k ≠ i)
    (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    ({c}ᶜ : Finset (Fin 5)) \ {(σ i : Fin 5), (σ j : Fin 5)} = {(σ k : Fin 5), (σ l : Fin 5)} := by
  have hne : ∀ {m m' : Fin 4}, m ≠ m' → (σ m : Fin 5) ≠ σ m' := fun h h' =>
    h (σ.injective (Subtype.ext h'))
  have hc : ∀ m : Fin 4, (σ m : Fin 5) ≠ c := fun m h =>
    Finset.mem_compl.1 (σ m).2 (Finset.mem_singleton.2 h)
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨hxc, hxi, hxj⟩
    obtain ⟨m, hm⟩ := σ.surjective ⟨x, by simpa using hxc⟩
    have hx : x = σ m := by rw [hm]
    rcases hcov m with rfl | rfl | rfl | rfl
    · exact absurd hx hxi
    · exact absurd hx hxj
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (rfl | rfl)
    · exact ⟨hc k, hne hki, hne hkj⟩
    · exact ⟨hc l, hne hli, hne hlj⟩

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  (e : L ≃* LinearFlag.projectiveSL n K)

theorem modelToG_le_centralizer_singleton {A : Subgroup (LinearFlag.projectiveSL n K)}
    {x : LinearFlag.projectiveSL n K}
    (h : A ≤ centralizer ({x} : Set (LinearFlag.projectiveSL n K))) :
    modelToG e A ≤ centralizer ({((e.symm x : L) : G)} : Set G) := by
  rw [← centralizer_zpowers_eq, ← modelToG_zpowers]
  refine modelToG_le_centralizer e ?_
  rwa [centralizer_zpowers_eq]

theorem mem_centralizer_of_symm_mem_centralizer {A : Subgroup (LinearFlag.projectiveSL n K)}
    {z : LinearFlag.projectiveSL n K}
    (h : ((e.symm z : L) : G) ∈ centralizer (modelToG e A : Set G)) :
    z ∈ centralizer (A : Set (LinearFlag.projectiveSL n K)) := by
  rw [mem_centralizer_iff] at h ⊢
  intro v hv
  have h1 := h _ (symm_mem_modelToG e hv)
  have h2 : e.symm v * e.symm z = e.symm z * e.symm v := Subtype.ext h1
  have h3 := congrArg e h2
  simpa only [map_mul, MulEquiv.apply_symm_apply] using h3

end Transport

section Normalize

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_normalizer_wZero_of_root {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht2 : t * t = 1)
    (htC : t ∈ centralizer (L : Set G)) {c : Fin 5} {W₁ : Subgroup G}
    (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    (hWV : Nat.card W₁ = Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    {yG : G} (hyt : yG * t = t * yG) {S : Finset (Fin 5)}
    (hV₀ : W₁ ⊓ centralizer ({yG} : Set G) ⊓ centralizer ({t} : Set G) =
      modelToG e (pointRadOn c S))
    {i j : Fin 5} (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c) (hiS : i ∉ S) (hjS : j ∈ S)
    (hroot : Nat.card W₁ ≤
      4 * Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hij (1 : K)) : L) : G)} : Set G) :
        Subgroup G)) :
    ((e.symm (xab hij (1 : K)) : L) : G) ∈
      normalizer ((W₁ ⊓ centralizer ({yG} : Set G) : Subgroup G) : Set G) := by
  set x : G := ((e.symm (xab hij (1 : K)) : L) : G) with hx
  have hxB : xab hij (1 : K) ∈ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
    xab_mem_blockSL hij (by simpa using hic) (by simpa using hjc) 1
  have hxN : x ∈ normalizer (W₁ : Set G) := hLW (symm_mem_modelToG e hxB)
  have hxt : x * t = t * x := (mem_centralizer_iff.1 htC) x (e.symm _).2
  have hx2 : x * x = 1 := by
    rw [hx, ← Subgroup.coe_mul, ← map_mul, ← xab_add, CharTwo.add_self_eq_zero, xab_zero,
      map_one, Subgroup.coe_one]
  have hxV : x ∉ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    rw [hW₁t]
    exact fun h => xab_not_mem_centralizer_pointRadical hK hij hic hjc
      (mem_centralizer_of_symm_mem_centralizer e h)
  have hxV₀ : modelToG e (pointRadOn c S) ≤ centralizer ({x} : Set G) :=
    modelToG_le_centralizer_singleton e (pointRadOn_le_centralizer_xab hij hic hjc hiS 1)
  have hVx : ∀ v ∈ W₁ ⊓ centralizer ({t} : Set G),
      x * v * x⁻¹ * v⁻¹ ∈ modelToG e (pointRadOn c S) := by
    intro v hv
    rw [hW₁t] at hv
    obtain ⟨v', hv', rfl⟩ := (mem_modelToG e).1 hv
    have h1 := xab_commutator_mem_pointRadOn hij hic hjc (1 : K) hv'
    have h2 : ((e.symm (xab hij (1 : K) * v' * (xab hij 1)⁻¹ * v'⁻¹) : L) : G) =
        x * ((e.symm v' : L) : G) * x⁻¹ * ((e.symm v' : L) : G)⁻¹ := by
      simp only [hx, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h2]
    exact symm_mem_modelToG e (pointRadOn_mono c (Finset.singleton_subset_iff.2 hjS) h1)
  have hW₀t : ∀ w ∈ W₁ ⊓ centralizer ({yG} : Set G),
      t * w * t⁻¹ * w⁻¹ ∈ modelToG e (pointRadOn c S) := by
    intro w hw
    obtain ⟨hwW, hwy⟩ := Subgroup.mem_inf.1 hw
    rw [← hV₀]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨tcomm_mem htW₁ hwW,
      tcomm_mem_centralizer_of_commute hyt hwy⟩, tcomm_mem_centralizer hW₁2 ht2 htW₁ hwW⟩
  have hV₀W₀ : modelToG e (pointRadOn c S) ≤ W₁ ⊓ centralizer ({yG} : Set G) := by
    rw [← hV₀]; exact inf_le_left
  exact mem_normalizer_of_root hW₁2 ht2 htW₁ hWV hV₀W₀ inf_le_left hW₀t hxN hxt hx2 hroot hxV
    hxV₀ hVx

end Normalize

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem sylowPartAt_five {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b c d d' : Fin 5} (hab : a ≠ b) (hdd' : d ≠ d') (hca : c ≠ a) (hcb : c ≠ b)
    (hS : ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'})
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    (hj : ((e.symm (xab hab 1) : L) : G) ∈
      centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G)) :
    ∃ C S₀ : Subgroup G, Nat.card C = 2 ^ 6 ∧ IsPGroup 2 C ∧
      C ≤ normalizer (W₁ : Set G) ∧ C ≤ centralizer ({t} : Set G) ∧
      C ⊓ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ ∧
      W₁ ≤ S₀ ∧ S₀ ≤ W₁ ⊔ C ∧
      S₀ ≤ centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
      C ≤ S₀ ⊔ zpowers ((e.symm (xab hdd' 1) : L) : G) ∧
      2 ^ 15 ≤ 4 * Nat.card S₀ ∧
      ∀ h ∈ C, h * h = 1 → Nat.card (W₁ ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
        Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  have hdS : d ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hd'S : d' ∈ ({c}ᶜ : Finset (Fin 5)) \ {a, b} := by rw [hS]; simp
  have hcd : c ≠ d := fun h => by simp [← h] at hdS
  have hcd' : c ≠ d' := fun h => by simp [← h] at hd'S
  have had : a ≠ d := fun h => by simp [← h] at hdS
  have hbd : b ≠ d := fun h => by simp [← h] at hdS
  have had' : a ≠ d' := fun h => by simp [← h] at hd'S
  have hbd' : b ≠ d' := fun h => by simp [← h] at hd'S
  have hfmem : ∀ i : Fin 4, ![a, b, d, d'] i ∈ ({c}ᶜ : Finset (Fin 5)) := by
    intro i
    rw [Finset.mem_compl, Finset.mem_singleton]
    fin_cases i
    · exact Ne.symm hca
    · exact Ne.symm hcb
    · exact Ne.symm hcd
    · exact Ne.symm hcd'
  let f : Fin 4 → ({c}ᶜ : Finset (Fin 5)) := fun i => ⟨![a, b, d, d'] i, hfmem i⟩
  have hfinj : Function.Injective f := by
    intro i j h
    have h1 : ![a, b, d, d'] i = ![a, b, d, d'] j := congrArg Subtype.val h
    revert h1
    fin_cases i <;> fin_cases j <;>
      simp [hab, had, had', hbd, hbd', hdd', Ne.symm hab, Ne.symm had, Ne.symm had', Ne.symm hbd,
        Ne.symm hbd', Ne.symm hdd']
  have hfbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_coe, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin]
  let σ : Fin 4 ≃ ({c}ᶜ : Finset (Fin 5)) := Equiv.ofBijective f hfbij
  have hσne : ∀ {i j : Fin 4}, i ≠ j → (σ i : Fin 5) ≠ σ j := fun h h' =>
    h (σ.injective (Subtype.ext h'))
  have hS_ad : ({c}ᶜ : Finset (Fin 5)) \ {a, d} = {b, d'} :=
    compl_sdiff_pair_eq_of_equiv σ (i := 0) (j := 2) (k := 1) (l := 3) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hX₀y := eq_zpowers_xab_mul_xab_symm hK (by norm_num) hab hX₀ hX₀c
  subst hX₀y
  set yG : G := ((e.symm (xab hab (1 : K) * xab hab.symm 1) : L) : G) with hyG
  have hX₀G : centralizer (modelToG e (zpowers (xab hab (1 : K) * xab hab.symm 1)) : Set G) =
      centralizer ({yG} : Set G) := by
    rw [modelToG_zpowers, centralizer_zpowers_eq]
  rw [hX₀G] at hj
  rw [hX₀G]
  set W₀ : Subgroup G := W₁ ⊓ centralizer ({yG} : Set G) with hW₀def
  obtain ⟨-, hV₀, hroot⟩ := wZero_data_five hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hab hdd' hca hcb
    hS
  have hrab := hroot hj
  have hyt : yG * t = t * yG := hLt yG (e.symm _).2
  have hcc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  have hV₁card : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4 := by
    rw [hW₁t, natCard_modelToG_eq, pointRadical, card_pointRadOn hK c hcc, Finset.card_compl,
      Finset.card_singleton, Fintype.card_fin]
  have hWV : Nat.card W₁ = Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hW₁c, hV₁card]; norm_num
  have hWc : ∀ v ∈ W₁, ∀ w ∈ W₁, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW₁2 hv hw
  set ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* G :=
    L.subtype.comp (e.symm.toMonoidHom.comp (embTwo (K := K) ({c}ᶜ : Finset (Fin 5)) σ))
    with hψdef
  have hψ : ∀ g, ψ g = ((e.symm (embTwo (K := K) ({c}ᶜ : Finset (Fin 5)) σ g) : L) : G) :=
    fun g => rfl
  have hI5 : ({c}ᶜ : Finset (Fin 5)).card < 5 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    norm_num
  have hψinj : Function.Injective ψ :=
    L.subtype_injective.comp (e.symm.injective.comp (embTwo_injective σ hI5))
  have hψB : ∀ g, ψ g ∈ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) := fun g =>
    symm_mem_modelToG e (embTwo_mem_blockSL σ g)
  have hψN : ∀ g, ψ g ∈ normalizer (W₁ : Set G) := fun g => hLW (hψB g)
  have hψt : ∀ g, ψ g * t = t * ψ g := fun g => hLt _ (e.symm _).2
  have hψroot : ∀ k : Fin 6, ψ (uRoot k) =
      ((e.symm (xab (hσne (uRow_ne_uCol k)) (1 : K)) : L) : G) := fun k => by
    rw [hψ, embTwo_uRoot]
  have hψ0 : ψ (uRoot 0) = ((e.symm (xab hab (1 : K)) : L) : G) := hψroot 0
  have hψ1 : ψ (uRoot 1) = ((e.symm (xab had (1 : K)) : L) : G) := hψroot 1
  have hψ2 : ψ (uRoot 2) = ((e.symm (xab had' (1 : K)) : L) : G) := hψroot 2
  have hψ3 : ψ (uRoot 3) = ((e.symm (xab hbd (1 : K)) : L) : G) := hψroot 3
  have hψ4 : ψ (uRoot 4) = ((e.symm (xab hbd' (1 : K)) : L) : G) := hψroot 4
  have hψ5 : ψ (uRoot 5) = ((e.symm (xab hdd' (1 : K)) : L) : G) := hψroot 5
  have hfaith : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ⊓
      centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ := by
    rw [hW₁t, modelToG_inf_centralizer_eq, blockSL_compl_inf_centralizer_pointRadical hK c,
      modelToG, Subgroup.map_bot, Subgroup.map_bot]
  have hψV : ∀ g, g ≠ 1 →
      ψ g ∉ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    intro g hg hC
    have h1 : ψ g ∈ (⊥ : Subgroup G) := hfaith ▸ Subgroup.mem_inf.2 ⟨hψB g, hC⟩
    exact hg (hψinj (by rw [Subgroup.mem_bot.1 h1, map_one]))
  have hrootAll : ∀ m : Fin 6, Nat.card W₁ ≤
      4 * Nat.card (W₁ ⊓ centralizer ({ψ (uRoot m)} : Set G) : Subgroup G) := by
    intro m
    obtain ⟨l, hl⟩ := exists_mul_uRoot_zero_eq m
    have h1 : ψ (uRoot 0) = (ψ l)⁻¹ * ψ (uRoot m) * (ψ l)⁻¹⁻¹ := by
      rw [inv_inv, ← map_inv, ← map_mul, ← map_mul, mul_assoc, ← hl, ← mul_assoc, inv_mul_cancel,
        one_mul]
    have h2 := card_inf_centralizer_conj_le (inv_mem (hψN l)) (ψ (uRoot m))
    rw [← h1, hψ0] at h2
    exact hrab.trans (Nat.mul_le_mul_left _ h2)
  set C : Subgroup G := (uGroup (ZMod 2)).map ψ with hCdef
  have hCc : Nat.card C = 2 ^ 6 := by
    rw [hCdef, Subgroup.card_map_of_injective hψinj, card_uGroup, Nat.card_zmod]
  have hCB : C ≤ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) := by
    rintro _ ⟨g, -, rfl⟩
    exact hψB g
  have hCN : C ≤ normalizer (W₁ : Set G) := hCB.trans hLW
  have hCt : C ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨g, -, rfl⟩
    exact mem_centralizer_singleton_iff.2 (hψt g)
  have hCV : C ⊓ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ hCB).trans hfaith.le)
  set Q : Subgroup G := uQuot.map ψ with hQdef
  set S₀ : Subgroup G := W₁ ⊔ Q with hS₀def
  have hQC : Q ≤ C := Subgroup.map_mono uQuot_le_uGroup
  have hQc : 2 ^ 5 ≤ Nat.card Q := by
    rw [hQdef, Subgroup.card_map_of_injective hψinj]
    exact card_uQuot
  have hWQ : W₁ ⊓ Q = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    intro w hw
    obtain ⟨hwW, hwQ⟩ := Subgroup.mem_inf.1 hw
    refine Subgroup.mem_inf.2 ⟨hQC hwQ, ?_⟩
    rw [mem_centralizer_iff]
    intro v hv
    exact hWc v (Subgroup.mem_inf.1 hv).1 w hwW
  have hS₀c : 2 ^ 13 ≤ Nat.card S₀ := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne (hQC.trans hCN)
    rw [hWQ, Subgroup.card_bot, mul_one, hW₁c] at h1
    rw [hS₀def, h1]
    calc 2 ^ 13 = 2 ^ 8 * 2 ^ 5 := by norm_num
      _ ≤ 2 ^ 8 * Nat.card Q := Nat.mul_le_mul_left _ hQc
  have hW₀C : W₁ ≤ centralizer (W₀ : Set G) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro v hv
    exact hWc v (Subgroup.mem_inf.1 hv).1 w hw
  have hyC : yG ∈ centralizer (W₀ : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hw).2
  have hXab : ((e.symm (xab hab (1 : K)) : L) : G) ∈ centralizer (W₀ : Set G) := hj
  have hXba : ((e.symm (xab hab.symm (1 : K)) : L) : G) ∈ centralizer (W₀ : Set G) := by
    have hx2 : ((e.symm (xab hab (1 : K)) : L) : G) * ((e.symm (xab hab (1 : K)) : L) : G) =
        1 := by
      rw [← Subgroup.coe_mul, ← map_mul, ← xab_add, CharTwo.add_self_eq_zero, xab_zero, map_one,
        Subgroup.coe_one]
    have h1 : ((e.symm (xab hab.symm (1 : K)) : L) : G) =
        ((e.symm (xab hab (1 : K)) : L) : G) * yG := by
      rw [hyG, coe_symm_mul, ← mul_assoc, hx2, one_mul]
    rw [h1]
    exact mul_mem hXab hyC
  have hN : ∀ {i j : Fin 5} (hij : i ≠ j), c ≠ i → c ≠ j →
      i ∉ ({d, d'} : Finset (Fin 5)) → j ∈ ({d, d'} : Finset (Fin 5)) →
      Nat.card W₁ ≤ 4 * Nat.card (W₁ ⊓ centralizer ({((e.symm (xab hij (1 : K)) : L) : G)} :
        Set G) : Subgroup G) →
      ((e.symm (xab hij (1 : K)) : L) : G) ∈ normalizer (W₀ : Set G) :=
    fun hij hci hcj hiS hjS hr => mem_normalizer_wZero_of_root hK e ht2 htC hW₁2 hW₁t htW₁ hLW
      hWV hyt hV₀ hij (Ne.symm hci) (Ne.symm hcj) hiS hjS hr
  have hr1 := hrootAll 1
  have hr2 := hrootAll 2
  have hr3 := hrootAll 3
  have hr4 := hrootAll 4
  rw [hψ1] at hr1
  rw [hψ2] at hr2
  rw [hψ3] at hr3
  rw [hψ4] at hr4
  have hNad := hN had hca hcd (by simp [had, had']) (by simp) hr1
  have hNad' := hN had' hca hcd' (by simp [had, had']) (by simp) hr2
  have hNbd := hN hbd hcb hcd (by simp [hbd, hbd']) (by simp) hr3
  have hNbd' := hN hbd' hcb hcd' (by simp [hbd, hbd']) (by simp) hr4
  have hcomm : ∀ {i j l : Fin 5} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l),
      ((e.symm (xab hij (1 : K)) : L) : G) * ((e.symm (xab hjl (1 : K)) : L) : G) *
        ((e.symm (xab hij (1 : K)) : L) : G)⁻¹ * ((e.symm (xab hjl (1 : K)) : L) : G)⁻¹ =
      ((e.symm (xab hil (1 : K)) : L) : G) := by
    intro i j l hij hjl hil
    have h := xab_commutator hij hjl hil (1 : K) 1
    rw [mul_one] at h
    rw [← h, map_mul, map_mul, map_mul, map_inv, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hXab0 : ψ (uRoot 0) ∈ centralizer (W₀ : Set G) := by
    rw [hψ0]
    exact hXab
  have hXad : ψ (uRoot 1) ∈ centralizer (W₀ : Set G) := by
    rw [hψ1, ← hcomm hab hbd had]
    exact commutator_mem_centralizer hXab hNbd
  have hXad' : ψ (uRoot 2) ∈ centralizer (W₀ : Set G) := by
    rw [hψ2, ← hcomm hab hbd' had']
    exact commutator_mem_centralizer hXab hNbd'
  have hXbd : ψ (uRoot 3) ∈ centralizer (W₀ : Set G) := by
    rw [hψ3, ← hcomm hab.symm had hbd]
    exact commutator_mem_centralizer hXba hNad
  have hXbd' : ψ (uRoot 4) ∈ centralizer (W₀ : Set G) := by
    rw [hψ4, ← hcomm hab.symm had' hbd']
    exact commutator_mem_centralizer hXba hNad'
  have hQW₀ : Q ≤ centralizer (W₀ : Set G) := by
    rw [hQdef, Subgroup.map_le_iff_le_comap, uQuot, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact hXab0
    · exact hXad
    · exact hXad'
    · exact hXbd
    · exact hXbd'
  have hS₀W₀ : S₀ ≤ centralizer (W₀ : Set G) := sup_le hW₀C hQW₀
  have hCu : C ≤ S₀ ⊔ zpowers ((e.symm (xab hdd' (1 : K)) : L) : G) := by
    have h1 := Subgroup.map_mono (f := ψ) uGroup_le_sup
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hψ5] at h1
    exact h1.trans (sup_le_sup_right le_sup_right _)
  have hsq : ∀ {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l), i ≠ c → j ≠ c → k ≠ c → l ≠ c →
      l ≠ i → j ≠ l → (({c}ᶜ : Finset (Fin 5)) \ {i, k}).card = 2 →
      Nat.card (W₁ ⊓ centralizer ({t} : Set G) ⊓
        centralizer ({((e.symm (xab hij (1 : K)) : L) : G) *
          ((e.symm (xab hkl (1 : K)) : L) : G)} : Set G) : Subgroup G) ^ 2 ≤
        Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    intro i j k l hij hkl hic hjc hkc hlc hli hjl hcard
    rw [← coe_symm_mul, hV₁card, hW₁t, modelToG_inf_centralizer_singleton]
    have hle := pointRadical_inf_centralizer_xab_mul_xab_le hK hij hkl hic hjc hkc hlc hli hjl
    have h4 : Nat.card (modelToG e (pointRadical (K := K) c ⊓
        centralizer ({xab hij (1 : K) * xab hkl 1} : Set (LinearFlag.projectiveSL 5 K)))) ≤
        4 := by
      refine (Subgroup.card_le_of_le (modelToG_mono e hle)).trans ?_
      rw [natCard_modelToG_eq, card_pointRadOn hK c (by simp), hcard]
      norm_num
    calc _ ≤ 4 ^ 2 := Nat.pow_le_pow_left h4 2
      _ = 2 ^ 4 := by norm_num
  have hkeyRep : ∀ k : Fin 9, Nat.card (W₁ ⊓ centralizer ({ψ (uElem (uRep k)) * t} : Set G) :
      Subgroup G) ≤ Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    intro k
    have hR2 : ψ (uElem (uRep k)) * ψ (uElem (uRep k)) = 1 := by
      rw [← map_mul, uElem_uRep_mul_self, map_one]
    rcases uElem_uRep_cases k with ⟨m, hm⟩ | h6 | h7 | h8
    · rw [hm] at hR2 ⊢
      have hm1 : uRoot (R := ZMod 2) m ≠ 1 := by
        rw [uRoot, Ne, uElem_eq_one_iff]
        intro h
        have h1 := congrFun h m
        simp at h1
      exact card_inf_centralizer_mul_le_of_root hW₁2 ht2 htW₁ hWV (hψN _) (hψt _) hR2
        (hrootAll m) (hψV _ hm1)
    · refine card_inf_centralizer_mul_le_of_sq hW₁2 ht2 htW₁ (hψN _) hR2 ?_
      rw [h6, map_mul, hψ1, hψ4]
      exact hsq had hbd' (Ne.symm hca) (Ne.symm hcd) (Ne.symm hcb) (Ne.symm hcd')
        (Ne.symm had') hdd' (by rw [hS, Finset.card_pair hdd'])
    · refine card_inf_centralizer_mul_le_of_sq hW₁2 ht2 htW₁ (hψN _) hR2 ?_
      rw [h7, map_mul, hψ2, hψ3]
      exact hsq had' hbd (Ne.symm hca) (Ne.symm hcd') (Ne.symm hcb) (Ne.symm hcd)
        (Ne.symm had) (Ne.symm hdd') (by rw [hS, Finset.card_pair hdd'])
    · refine card_inf_centralizer_mul_le_of_sq hW₁2 ht2 htW₁ (hψN _) hR2 ?_
      rw [h8, map_mul, hψ0, hψ5]
      exact hsq hab hdd' (Ne.symm hca) (Ne.symm hcb) (Ne.symm hcd) (Ne.symm hcd')
        (Ne.symm had') hbd' (by rw [hS_ad, Finset.card_pair hbd'])
  have hkey : ∀ h ∈ C, h * h = 1 →
      Nat.card (W₁ ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
        Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ hh2
    have hx : uMulF x x = 0 := by
      have h1 : ψ (uElem x * uElem x) = ψ 1 := by rw [map_mul, map_one]; exact hh2
      rw [uElem_mul] at h1
      exact uElem_eq_one_iff.1 (hψinj h1)
    by_cases hx0 : x = 0
    · rw [hx0, uElem_zero, map_one, one_mul]
    obtain ⟨i, k, hik⟩ := exists_conj_eq_uRep hx hx0
    have hxu : uElem x = uElem (uConj i) * uElem (uRep k) * (uElem (uConj i))⁻¹ := by
      rw [← hik, mul_inv_cancel_right]
    set g : G := ψ (uElem (uConj i)) with hg
    have hgt : g⁻¹ * t = t * g⁻¹ := by
      have h1 : g * t = t * g := hψt (uElem (uConj i))
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [h1]
        _ = t * g⁻¹ := by group
    have hconj : ψ (uElem x) * t = g * (ψ (uElem (uRep k)) * t) * g⁻¹ := by
      rw [hxu, map_mul, map_mul, map_inv]
      calc g * ψ (uElem (uRep k)) * g⁻¹ * t = g * ψ (uElem (uRep k)) * (g⁻¹ * t) := by group
        _ = g * ψ (uElem (uRep k)) * (t * g⁻¹) := by rw [hgt]
        _ = g * (ψ (uElem (uRep k)) * t) * g⁻¹ := by group
    rw [hconj]
    exact (card_inf_centralizer_conj_le (hψN _) _).trans (hkeyRep k)
  exact ⟨C, S₀, hCc, IsPGroup.of_card hCc, hCN, hCt, hCV, le_sup_left, sup_le_sup_left hQC _,
    hS₀W₀, hCu, by omega, hkey⟩

theorem sylowPart_five (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcore : ∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      modelToG e (rootSL2 (K := K) a b) ≤
        centralizer (centralizerPerfectCore (modelToG e X₀) : Set G))
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G)) :
    ∃ (a b d d' : Fin 5) (_ : a ≠ b) (hdd' : d ≠ d'), c ≠ a ∧ c ≠ b ∧
      ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'} ∧
      ∃ X₀ : Subgroup (LinearFlag.projectiveSL 5 K), X₀ ≤ rootSL2 a b ∧
        Nat.card X₀ = Nat.card K + 1 ∧
      ∃ C S₀ : Subgroup G, Nat.card C = 2 ^ 6 ∧ IsPGroup 2 C ∧
        C ≤ normalizer (W₁ : Set G) ∧ C ≤ centralizer ({t} : Set G) ∧
        C ⊓ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ ∧
        W₁ ≤ S₀ ∧ S₀ ≤ W₁ ⊔ C ∧
        S₀ ≤ centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
        C ≤ S₀ ⊔ zpowers ((e.symm (xab hdd' 1) : L) : G) ∧
        2 ^ 15 ≤ 4 * Nat.card S₀ ∧
        ∀ h ∈ C, h * h = 1 → Nat.card (W₁ ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
          Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hI4 : 4 = ({c}ᶜ : Finset (Fin 5)).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  set σ : Fin 4 ≃ ({c}ᶜ : Finset (Fin 5)) :=
    (finCongr hI4).trans ({c}ᶜ : Finset (Fin 5)).equivFin.symm with hσ
  have hσne : ∀ {i j : Fin 4}, i ≠ j → (σ i : Fin 5) ≠ σ j := fun h h' =>
    h (σ.injective (Subtype.ext h'))
  have hσc : ∀ i : Fin 4, c ≠ σ i := fun i h =>
    Finset.mem_compl.1 (σ i).2 (Finset.mem_singleton.2 h.symm)
  have hab : (σ 0 : Fin 5) ≠ σ 1 := hσne (by decide)
  have hdd' : (σ 2 : Fin 5) ≠ σ 3 := hσne (by decide)
  have hS_ab : ({c}ᶜ : Finset (Fin 5)) \ {(σ 0 : Fin 5), (σ 1 : Fin 5)} =
      {(σ 2 : Fin 5), (σ 3 : Fin 5)} :=
    compl_sdiff_pair_eq_of_equiv σ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hJab, -, -, -⟩ := root_data_five hset hK e ht htC hcore hW₁c hW₁2 hW₁t htW₁ hLW
    hab hdd' (hσc 0) (hσc 1) hS_ab
  have hX₀ : zpowers (xab hab (1 : K) * xab hab.symm 1) ≤ rootSL2 (σ 0 : Fin 5) (σ 1) :=
    (zpowers_le).2 (xab_mul_xab_symm_mem_rootSL2 hab 1 1)
  have hX₀c : Nat.card (zpowers (xab hab (1 : K) * xab hab.symm 1)) = Nat.card K + 1 := by
    rw [Nat.card_zpowers, orderOf_xab_mul_xab_symm (by norm_num) hab, hK]
  have hj : ((e.symm (xab hab (1 : K)) : L) : G) ∈ centralizer ((W₁ ⊓
      centralizer (modelToG e (zpowers (xab hab (1 : K) * xab hab.symm 1)) : Set G) :
        Subgroup G) : Set G) := by
    rw [modelToG_zpowers, centralizer_zpowers_eq]
    exact hJab (symm_mem_modelToG e (xab_mem_rootSL2 hab 1))
  obtain ⟨C, S₀, h⟩ := sylowPartAt_five hK e ht hKt hab hdd' (hσc 0) (hσc 1) hS_ab hX₀ hX₀c
    hW₁c hW₁2 hW₁t htW₁ hLW hj
  exact ⟨σ 0, σ 1, σ 2, σ 3, hab, hdd', hσc 0, hσc 1, hS_ab, _, hX₀, hX₀c, C, S₀, h⟩

end Main

theorem lFiveSOneSylowPartInput : LFiveSOneSylowPartInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt _ hcore c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  exact sylowPart_five hset hK e ht hKt hcore c hW₁c hW₁2 hW₁t htW₁ hLW

end CFSG.SeitzReduction.LinearPilot
