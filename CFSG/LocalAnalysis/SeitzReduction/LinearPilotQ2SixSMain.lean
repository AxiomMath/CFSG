module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSJ
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSUni
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

variable {G : Type} [Group G] {L : Subgroup G}

theorem le_range_swapDiagHom_sixS {A D : Subgroup G} {t : G} (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hD : D ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hDt : D ≤ centralizer ({t} : Set G)) :
    D ≤ (swapDiagHom hc).range := by
  intro d hd
  obtain ⟨y, hyA, hy⟩ := exists_eq_mul_conj_of_mem_sup ht hinf hc (hD hd)
    (mem_centralizer_singleton_iff.1 (hDt hd))
  exact ⟨⟨y, hyA⟩, hy.symm⟩

theorem fin_six_shift_facts_sixS : ∀ c : Fin 6,
    (c + 1 ≠ c + 2 ∧ c + 3 ≠ c + 4 ∧ c + 3 ≠ c + 5 ∧ c + 4 ≠ c + 5 ∧ c ≠ c + 1 ∧ c ≠ c + 2 ∧
      c ≠ c + 3 ∧ c ≠ c + 4 ∧ c ≠ c + 5 ∧ c + 1 ≠ c + 3 ∧ c + 1 ≠ c + 4 ∧ c + 1 ≠ c + 5 ∧
      c + 2 ≠ c + 3 ∧ c + 2 ≠ c + 4 ∧ c + 2 ≠ c + 5) ∧
    ∀ x : Fin 6, x = c ∨ x = c + 1 ∨ x = c + 2 ∨ x = c + 3 ∨ x = c + 4 ∨ x = c + 5 := by
  decide

variable [Finite G]

theorem exists_sOneSwapData_six
    (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hall : ∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX)
    {c : Fin 6} {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 10) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htW₁ : t ∈ normalizer (W₁ : Set G))
    (hLW : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G))
    {a b d₁ d₂ d₃ : Fin 6} (hab : a ≠ b) (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃)
    (hca : c ≠ a) (hcb : c ≠ b) (hc1 : c ≠ d₁) (hc2 : c ≠ d₂) (hc3 : c ≠ d₃)
    (ha1 : a ≠ d₁) (ha2 : a ≠ d₂) (ha3 : a ≠ d₃) (hb1 : b ≠ d₁) (hb2 : b ≠ d₂) (hb3 : b ≠ d₃)
    (h6 : ∀ x : Fin 6, x = c ∨ x = a ∨ x = b ∨ x = d₁ ∨ x = d₂ ∨ x = d₃) :
    ∃ (C S₀ F W₀ A X : Subgroup G) (k : ℕ), Nat.card C = 2 ^ 10 ∧
      SOneSwapData W₁ C S₀ F W₀ A X t k := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : ∀ g ∈ L, g * t = t * g := fun g hg => (mem_centralizer_iff.1 htC) g hg
  set S : Finset (Fin 6) := {d₁, d₂, d₃} with hSdef
  have hS : ({c}ᶜ : Finset (Fin 6)) \ {a, b} = S := by
    ext x
    rcases h6 x with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hSdef, hab, hab.symm, h12, h13, h23, h12.symm, h13.symm, h23.symm, hca, hcb, hc1, hc2,
        hc3, hca.symm, hcb.symm, hc1.symm, hc2.symm, hc3.symm, ha1, ha2, ha3, hb1, hb2, hb3,
        ha1.symm, ha2.symm, ha3.symm, hb1.symm, hb2.symm, hb3.symm]
  have hcompl : ({a, b} : Finset (Fin 6))ᶜ = insert c S := by
    ext x
    rcases h6 x with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hSdef, hab, hab.symm, h12, h13, h23, h12.symm, h13.symm, h23.symm, hca, hcb, hc1, hc2,
        hc3, hca.symm, hcb.symm, hc1.symm, hc2.symm, hc3.symm, ha1, ha2, ha3, hb1, hb2, hb3,
        ha1.symm, ha2.symm, ha3.symm, hb1.symm, hb2.symm, hb3.symm]
  have hcS : c ∉ S := by simp [hSdef, hc1, hc2, hc3]
  have haS : a ∉ S := by simp [hSdef, ha1, ha2, ha3]
  have hbS : b ∉ S := by simp [hSdef, hb1, hb2, hb3]
  have hScard : S.card = 3 := by
    rw [hSdef, Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hSc : S ⊆ ({c}ᶜ : Finset (Fin 6)) := by
    rw [← hS]
    exact Finset.sdiff_subset
  have hSab : S ⊆ ({a, b} : Finset (Fin 6))ᶜ := by
    rw [hcompl]
    exact Finset.subset_insert c S
  have hdisj : Disjoint S ({a, b} : Finset (Fin 6)) := by
    rw [← hS]
    exact Finset.sdiff_disjoint
  have hall' : ∀ (i j : Fin 6) (hij : i ≠ j) (htX : t ∈ centralizer (modelToG e
      (zpowers (xab hij (1 : K) * xab hij.symm 1)) : Set G)),
      LinearTwoSwapKindAt e t i j (zpowers (xab hij (1 : K) * xab hij.symm 1)) htX :=
    fun i j hij htX => hall i j hij _ (rootTorus_le_and_card_sixS hK hij).1
      (rootTorus_le_and_card_sixS hK hij).2 htX
  obtain ⟨hX₀, hX₀c⟩ := rootTorus_le_and_card_sixS hK hab
  have htX : t ∈ centralizer (modelToG e (zpowers (xab hab (1 : K) * xab hab.symm 1)) :
      Set G) := centralizer_le (modelToG_le e _) htC
  obtain ⟨A, hEX, hinf, hc, hAc, hDE⟩ :=
    exists_swap_factor_of_swap hset hK e (by norm_num) htC ht hab hX₀ hX₀c htX (hall' a b hab htX)
  obtain ⟨hW₀c, hV₀, -⟩ := wZero_facts_sixS hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hab hca hcb
  rw [hS] at hV₀
  obtain ⟨hW₀E, -⟩ := wZero_le_and_rootSL2_le_centralizer_sixS hset hK e ht htC hW₁c hW₁2 hW₁t
    htW₁ hLW hab hca hcb (hall' a b hab)
  obtain ⟨hJ1, hJ2⟩ := pointRadOn_le_centralizer_wZero_sixS hset hK e ht htC hW₁c hW₁2 hW₁t
    htW₁ hLW hab hca hcb hS hall'
  set xG : G := rootTorusSixG e hab with hxG
  set W₀ : Subgroup G := W₁ ⊓ centralizer ({xG} : Set G) with hW₀
  have hW₀2 : ∀ w ∈ W₀, w * w = 1 := fun w hw => hW₁2 w hw.1
  have hxt : xG * t = t * xG := hLt _ (e.symm _).2
  have htW₀ : t ∈ normalizer (W₀ : Set G) := mem_normalizer_inf_centralizer htW₁ hxt.symm
  rw [hEX] at hW₀E hDE
  set D : Subgroup G := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 6))ᶜ)) with hD
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hLt d (modelToG_le e _ hd))
  have hcard4 : (({a, b} : Finset (Fin 6))ᶜ).card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  have hDcard : Nat.card A ≤ Nat.card D := by
    obtain ⟨φ⟩ := blockSL_mulEquiv (K := K) (I := (({a, b} : Finset (Fin 6))ᶜ)) (by omega)
    rw [hAc, hD, natCard_modelToG_eq, Nat.card_congr φ.toEquiv, hcard4]
  have hδD := swapDiagHom_mem_of_card_le ht2 hinf hc hDE hDt hDcard
  have hDV : D ⊓ centralizer ((W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤ W₀ := by
    rintro _ ⟨⟨_, ⟨d', hd'B, rfl⟩, rfl⟩, hdC⟩
    have hd'' : d' ∈ pointRadOn (K := K) c S := by
      refine mem_pointRadOn_of_mem_blockSL_of_forall_commute_sixS hK hcS ⟨d₁, by simp [hSdef]⟩
        (by rwa [hcompl] at hd'B) fun v hv => ?_
      have hv' : ((e.symm v : L) : G) ∈ W₀ ⊓ centralizer ({t} : Set G) := by
        rw [hV₀]
        exact symm_mem_modelToG e hv
      have h1 := (mem_centralizer_iff.1 hdC) _ hv'
      exact ((symm_commute_iff_sixS e v d').1 h1).symm
    have h2 : ((e.symm d' : L) : G) ∈ W₀ ⊓ centralizer ({t} : Set G) := by
      rw [hV₀]
      exact symm_mem_modelToG e hd''
    exact h2.1
  have hWV : Nat.card W₀ = Nat.card (W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hW₀c, hV₀, natCard_modelToG_eq, card_pointRadOn hK c hcS, hScard]
    norm_num
  obtain ⟨hdecomp, hVE⟩ := eq_sup_and_card_le_of_swap_sixS ht2 hinf hc hW₀E hW₀2 htW₀ hδD hDV hWV
  have hE1 : W₀ ⊓ A ≠ ⊥ := by
    intro h
    have h1 : Nat.card (W₀ ⊓ A : Subgroup G) = 1 := by rw [h, Subgroup.card_bot]
    rw [h1, hV₀, natCard_modelToG_eq, card_pointRadOn hK c hcS, hScard] at hVE
    norm_num at hVE
  have hy0B : xab hab (1 : K) * xab hab.symm 1 ∈ blockSL (K := K) ({a, b} : Finset (Fin 6)) := by
    rw [← rootSL2_eq]
    exact hX₀ (mem_zpowers _)
  have hnorm : ∀ x ∈ blockSL (K := K) S, ((e.symm x : L) : G) ∈ normalizer (W₀ : Set G) := by
    intro x hx
    have hxW : ((e.symm x : L) : G) ∈ normalizer (W₁ : Set G) :=
      hLW (symm_mem_modelToG e (blockSL_mono hSc hx))
    have hcomm := (commute_blockSL_of_disjoint hdisj x hx _ hy0B).eq
    exact mem_normalizer_inf_centralizer hxW ((symm_commute_iff_sixS e _ _).2 hcomm)
  have hT₀ : insert d₁ ({d₂, d₃} : Finset (Fin 6)) = S := rfl
  set F₀ : Subgroup G := modelToG e (pointRadOn (K := K) d₁ {d₂, d₃}) with hF₀
  have hF₀S : pointRadOn (K := K) d₁ {d₂, d₃} ≤ blockSL S := hT₀ ▸ pointRadOn_le_blockSL d₁ _
  have hF₀D : F₀ ≤ D := modelToG_mono e (hF₀S.trans (blockSL_mono hSab))
  have hF₀δ := hF₀D.trans (le_range_swapDiagHom_sixS ht2 hinf hc hDE hDt)
  have hF₀W : F₀ ≤ normalizer (W₀ : Set G) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hnorm x (hF₀S hx)
  have hF₀2 : ∀ f ∈ F₀, f * f = 1 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change ((e.symm x : L) : G) * ((e.symm x : L) : G) = 1
    rw [← Subgroup.coe_mul, ← map_mul, pointRadOn_mul_self d₁ _ hx, map_one, Subgroup.coe_one]
  have hF₀V : F₀ ⊓ centralizer ((W₀ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨_, ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hfC⟩
    have hv : ((e.symm (LinearFlag.proj 6 K (pointRadElem c (Pi.single d₁ (1 : K))))
        : L) : G) ∈ W₀ ⊓ centralizer ({t} : Set G) := by
      rw [hV₀]
      refine symm_mem_modelToG e ⟨_, ⟨Pi.single d₁ 1, fun j hj => ?_, rfl⟩, rfl⟩
      exact Pi.single_eq_of_ne (by rintro rfl; exact hj (by simp [hSdef])) 1
    have h1 : ((e.symm (LinearFlag.proj 6 K (pointRadElem c (Pi.single d₁ (1 : K)))) : L) : G) *
        ((e.symm (LinearFlag.proj 6 K (pointRadElem d₁ r)) : L) : G) =
        ((e.symm (LinearFlag.proj 6 K (pointRadElem d₁ r)) : L) : G) *
          ((e.symm (LinearFlag.proj 6 K (pointRadElem c (Pi.single d₁ (1 : K)))) : L) : G) :=
      (mem_centralizer_iff.1 hfC) _ hv
    rw [symm_commute_iff_sixS] at h1
    have hr0 := eq_zero_of_proj_pointRadElem_commute_sixS hK hc1 (hr c (by simp [hc2, hc3]))
      (hr d₁ (by simp [h12, h13])) h1.symm
    rw [Subgroup.mem_bot]
    change ((e.symm (LinearFlag.proj 6 K (pointRadElem d₁ r)) : L) : G) = 1
    rw [hr0, pointRadElem_zero, map_one, map_one, Subgroup.coe_one]
  obtain ⟨X, hX2, hXA, hXW₀, hXE, hXc⟩ :=
    exists_faithful_factor_of_swap_sixS ht2 hinf hc hdecomp htW₀ hF₀δ hF₀W hF₀2 hF₀V
  have hXc4 : Nat.card X = 2 ^ 2 := by
    rw [hXc, hF₀, natCard_modelToG_eq, card_pointRadOn hK d₁ (by simp [h12, h13]),
      Finset.card_pair h23]
  set F : Subgroup G := modelToG e (blockSL (K := K) S) with hF
  have hFA : F ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom :=
    (modelToG_mono e (blockSL_mono hSab)).trans hDE
  have hFW₀ : F ≤ normalizer (W₀ : Set G) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hnorm x hx
  set Q₁ : Subgroup (LinearFlag.projectiveSL 6 K) :=
    pointRadOn (K := K) a (insert b S) ⊔ pointRadOn b S with hQ₁
  set Q₂ : Subgroup (LinearFlag.projectiveSL 6 K) :=
    pointRadOn (K := K) d₁ {d₂, d₃} ⊔ pointRadOn d₂ {d₃} with hQ₂
  set C : Subgroup G := modelToG e (Q₁ ⊔ Q₂) with hC
  set S₀ : Subgroup G := W₁ ⊔ modelToG e Q₁ with hS₀
  have hCc : Nat.card C = 2 ^ 10 := by
    rw [hC, natCard_modelToG_eq]
    exact card_unitriangular_sixS hK hab h12 h13 h23 ha1 ha2 ha3 hb1 hb2 hb3
  have hQ₂S : Q₂ ≤ blockSL S := fGroup_le_blockSL_sixS d₁ d₂ d₃
  have hQL₁ : Q₁ ⊔ Q₂ ≤ blockSL (K := K) ({c}ᶜ : Finset (Fin 6)) := by
    refine sup_le (sup_le ?_ ?_) (hQ₂S.trans (blockSL_mono hSc))
    · refine (pointRadOn_le_blockSL a _).trans (blockSL_mono fun x hx => ?_)
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · simpa using hca.symm
      · simpa using hcb.symm
      · exact hSc hx
    · refine (pointRadOn_le_blockSL b _).trans (blockSL_mono fun x hx => ?_)
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simpa using hcb.symm
      · exact hSc hx
  have hCL₁ : C ≤ modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) := modelToG_mono e hQL₁
  have hCW : C ≤ normalizer (W₁ : Set G) := hCL₁.trans hLW
  have hCt : C ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (hLt x (modelToG_le e _ hx))
  have hCV : C ⊓ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨_, ⟨x', hx', rfl⟩, rfl⟩, hxC⟩
    have h1 : x' = 1 := by
      refine eq_one_of_mem_blockSL_of_forall_conj_pointRadical hK c (hQL₁ hx') fun v hv => ?_
      have hv' : ((e.symm v : L) : G) ∈ W₁ ⊓ centralizer ({t} : Set G) := by
        rw [hW₁t]
        exact symm_mem_modelToG e hv
      have h2 : ((e.symm v : L) : G) * ((e.symm x' : L) : G) =
          ((e.symm x' : L) : G) * ((e.symm v : L) : G) := (mem_centralizer_iff.1 hxC) _ hv'
      rw [symm_commute_iff_sixS] at h2
      rw [← h2, mul_inv_cancel_right]
    rw [Subgroup.mem_bot]
    change ((e.symm x' : L) : G) = 1
    rw [h1, map_one, Subgroup.coe_one]
  have hQ₁G : modelToG e Q₁ ≤ centralizer (W₀ : Set G) := by
    have h1 : modelToG e Q₁ = modelToG e (pointRadOn (K := K) a (insert b S)) ⊔
        modelToG e (pointRadOn (K := K) b S) := by
      simp only [hQ₁, modelToG, Subgroup.map_sup]
    rw [h1]
    exact sup_le hJ1 hJ2
  have hWV₁ : W₁ ≤ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
    fun w hw => mem_centralizer_iff.2 fun v hv =>
      mul_comm_of_forall_mul_self_eq_one hW₁2 hv.1 hw
  have hS₀card : Nat.card S₀ = 2 ^ 10 * 2 ^ 7 := by
    have hN : modelToG e Q₁ ≤ normalizer (W₁ : Set G) :=
      (modelToG_mono e (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂)).trans hCW
    have hinf' : W₁ ⊓ modelToG e Q₁ = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : z ∈ C ⊓ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
        ⟨modelToG_mono e (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂) hz.2, hWV₁ hz.1⟩
      rwa [hCV] at h1
    rw [hS₀, card_sup_eq_mul_of_le_normalizer_sixS hN hinf', hW₁c, natCard_modelToG_eq, hQ₁,
      card_jGroup_sixS hK hab haS hbS, hScard]
    norm_num
  refine ⟨C, S₀, F, W₀, A, X, 16, hCc, IsPGroup.of_card hCc, hCW, hCt, hCV, le_sup_left,
    sup_le_sup_left (modelToG_mono e le_sup_left) _, ?_, ?_, ?_, hinf, hc, htW₀, hE1, hFA, hFW₀,
    hX2, hXA, hXW₀, hXE, by rw [hXc4]; norm_num, fun x hx hx2 =>
      key_sixS hset hK e ht htC hW₁c hW₁2 hW₁t htW₁ hLW hall (hCL₁ hx) hx2⟩
  · exact sup_le (fun w hw => mem_centralizer_iff.2 fun v hv =>
      mul_comm_of_forall_mul_self_eq_one hW₁2 hv.1 hw) hQ₁G
  · rw [hC, modelToG, Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le (le_sup_right.trans le_sup_left)
      ((Subgroup.map_mono (Subgroup.map_mono hQ₂S)).trans le_sup_right)
  · rw [hW₁c, hCc, hS₀card]
    norm_num

theorem lSixSOneSwapDataInput_holds :
    LSixSOneSwapDataInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, hall6⟩ :=
    fin_six_shift_facts_sixS c
  exact exists_sOneSwapData_six hset hK e ht hKt hall hW₁c hW₁2 hW₁t htW₁ hLW h1 h2 h3 h4 h5 h6
    h7 h8 h9 h10 h11 h12 h13 h14 h15 hall6

theorem lSixSOneNotSylowInput_holds :
    LSixSOneNotSylowInput :=
  lSixSOneNotSylowInput_of_swapData lSixSOneSwapDataInput_holds

end CFSG.SeitzReduction.LinearPilot
