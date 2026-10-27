module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeInter

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Model

variable {K : Type} [Field K]

@[expose] def blockRowStab (c : Fin 5) (v : Fin 5 → K) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 5) K) where
  carrier := {X | X ∈ blockSpecialLinear ({c}ᶜ : Finset (Fin 5)) ∧
    v ᵥ* (X : Matrix (Fin 5) (Fin 5) K) = v}
  one_mem' := ⟨one_mem _, by rw [Matrix.SpecialLinearGroup.coe_one, vecMul_one]⟩
  mul_mem' := fun {X Y} hX hY => ⟨mul_mem hX.1 hY.1, by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← vecMul_vecMul, hX.2, hY.2]⟩
  inv_mem' := fun {X} hX => ⟨inv_mem hX.1, by
    conv_lhs => rw [← hX.2]
    rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]⟩

theorem card_blockSpecialLinear_compl (hK : Nat.card K = 2) (c : Fin 5) :
    Nat.card (blockSpecialLinear (K := K) ({c}ᶜ : Finset (Fin 5))) = 20160 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h4 : (({c}ᶜ : Finset (Fin 5))).card = 4 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  obtain ⟨eB⟩ := blockSL_mulEquiv (K := K) (I := ({c}ᶜ : Finset (Fin 5))) (by rw [h4]; norm_num)
  rw [← Subgroup.card_map_of_injective (proj_injective_of_natCard_eq_two (n := 5) hK)]
  change Nat.card (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) = 20160
  rw [Nat.card_congr eB.toEquiv, card_SL_eq (by rw [h4]; norm_num), h4, hK]
  decide

theorem vecMul_apply_self_of_mem_blockSpecialLinear {c : Fin 5}
    {X : Matrix.SpecialLinearGroup (Fin 5) K}
    (hX : X ∈ blockSpecialLinear ({c}ᶜ : Finset (Fin 5))) (w : Fin 5 → K) :
    (w ᵥ* (X : Matrix (Fin 5) (Fin 5) K)) c = w c := by
  have hc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  simp only [vecMul, dotProduct]
  rw [Finset.sum_eq_single c]
  · rw [hX c c (Or.inl hc), one_apply_eq, mul_one]
  · intro k _ hk
    rw [hX k c (Or.inr hc), one_apply_ne hk, mul_zero]
  · simp

theorem single_vecMul_of_mem_blockSpecialLinear {c : Fin 5}
    {X : Matrix.SpecialLinearGroup (Fin 5) K}
    (hX : X ∈ blockSpecialLinear ({c}ᶜ : Finset (Fin 5))) (a : K) :
    Pi.single c a ᵥ* (X : Matrix (Fin 5) (Fin 5) K) = Pi.single c a := by
  have hc : c ∉ ({c}ᶜ : Finset (Fin 5)) := by simp
  funext j
  have h1 : (X : Matrix (Fin 5) (Fin 5) K) c j = (1 : Matrix (Fin 5) (Fin 5) K) c j :=
    hX c j (Or.inl hc)
  rw [single_vecMul, Pi.smul_apply, Matrix.row_apply, h1, one_apply, Pi.single_apply, smul_eq_mul]
  by_cases hj : j = c
  · subst hj
    simp
  · simp [hj, Ne.symm hj]

theorem card_blockRowStab_ge (hK : Nat.card K = 2) (c : Fin 5) (v : Fin 5 → K) :
    1344 ≤ Nat.card (blockRowStab c v) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  set Γ := blockSpecialLinear (K := K) ({c}ᶜ : Finset (Fin 5)) with hΓ
  have hinv : ∀ (X : Matrix.SpecialLinearGroup (Fin 5) K) (w : Fin 5 → K),
      w ᵥ* ((X⁻¹ : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ᵥ*
        (X : Matrix (Fin 5) (Fin 5) K) = w := fun X w => by
    rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  have hext : ∀ w w' : Fin 5 → K, w c = w' c →
      (fun i : Fin 4 => w (c.succAbove i)) = (fun i => w' (c.succAbove i)) → w = w' := by
    intro w w' hc hoff
    funext j
    rcases Fin.eq_self_or_eq_succAbove c j with rfl | ⟨i, rfl⟩
    · exact hc
    · exact congrFun hoff i
  have hsingle : ∀ w : Fin 5 → K, (fun i : Fin 4 => w (c.succAbove i)) = 0 →
      w = Pi.single c (w c) := by
    intro w h0
    refine hext _ _ (by simp) ?_
    rw [h0]
    funext i
    rw [Pi.single_eq_of_ne (Fin.succAbove_ne c i)]
    rfl
  set O : Set (Fin 5 → K) := Set.range fun X : Γ => v ᵥ*
    ((((X : Matrix.SpecialLinearGroup (Fin 5) K))⁻¹ : Matrix.SpecialLinearGroup (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) with hO
  have hw : ∀ w ∈ O, w c = v c ∧
      ((fun i : Fin 4 => w (c.succAbove i)) = 0 → (fun i : Fin 4 => v (c.succAbove i)) = 0) := by
    rintro _ ⟨X, rfl⟩
    have hc1 := vecMul_apply_self_of_mem_blockSpecialLinear (inv_mem X.2) v
    refine ⟨hc1, fun h0 => ?_⟩
    have h1 := hsingle _ h0
    rw [hc1] at h1
    have h2 : v = Pi.single c (v c) := by
      calc v = v ᵥ* ((((X : Matrix.SpecialLinearGroup (Fin 5) K))⁻¹ :
            Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ᵥ*
              ((X : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
            (hinv _ v).symm
        _ = Pi.single c (v c) := by rw [h1, single_vecMul_of_mem_blockSpecialLinear X.2]
    funext i
    rw [h2, Pi.single_eq_of_ne (Fin.succAbove_ne c i)]
    rfl
  have horb : Nat.card O ≤ 15 := by
    by_cases hv0 : (fun i : Fin 4 => v (c.succAbove i)) = 0
    · have hv := hsingle v hv0
      have hsub : O ⊆ {v} := by
        rintro _ ⟨X, rfl⟩
        rw [Set.mem_singleton_iff]
        have h1 := single_vecMul_of_mem_blockSpecialLinear (inv_mem X.2) (v c)
        rw [← hv] at h1
        exact h1
      rw [Nat.card_coe_set_eq]
      calc O.ncard ≤ ({v} : Set (Fin 5 → K)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton v
        _ ≤ 15 := by norm_num
    · let f : O → {u : Fin 4 → K // u ≠ 0} := fun w =>
        ⟨fun i => (w : Fin 5 → K) (c.succAbove i), fun h => hv0 ((hw _ w.2).2 h)⟩
      have hf : Function.Injective f := by
        intro w w' hww
        apply Subtype.ext
        refine hext _ _ ((hw _ w.2).1.trans (hw _ w'.2).1.symm) ?_
        exact congrArg Subtype.val hww
      have h16 : Nat.card {u : Fin 4 → K // u ≠ 0} = 15 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
          Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hK]
        norm_num
      rw [← h16]
      exact Nat.card_le_card_of_injective f hf
  have hsec : ∀ w : O, ∃ X : Γ, v ᵥ* ((((X : Matrix.SpecialLinearGroup (Fin 5) K))⁻¹ :
      Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = w := fun w => w.2
  choose sc hsc using hsec
  let orbitMap : Γ → O := fun X => ⟨_, X, rfl⟩
  have hstab : ∀ X : Γ, ((X : Matrix.SpecialLinearGroup (Fin 5) K))⁻¹ *
      ((sc (orbitMap X) : Γ) : Matrix.SpecialLinearGroup (Fin 5) K) ∈ blockRowStab c v := by
    intro X
    refine ⟨mul_mem (inv_mem X.2) (sc (orbitMap X)).2, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, ← vecMul_vecMul]
    change (orbitMap X : Fin 5 → K) ᵥ* _ = v
    rw [← hsc (orbitMap X), hinv]
  let Φ : Γ → O × blockRowStab c v := fun X => (orbitMap X, ⟨_, hstab X⟩)
  have hΦ : Function.Injective Φ := by
    intro X X' hXX
    have h1 : orbitMap X = orbitMap X' := congrArg Prod.fst hXX
    have h2 := congrArg (fun q : O × blockRowStab c v =>
      ((q.2 : blockRowStab c v) : Matrix.SpecialLinearGroup (Fin 5) K)) hXX
    simp only [Φ] at h2
    rw [h1] at h2
    have h3 := mul_right_cancel h2
    apply Subtype.ext
    exact inv_injective h3
  have h4 : Nat.card Γ ≤ Nat.card O * Nat.card (blockRowStab c v) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective Φ hΦ
  rw [card_blockSpecialLinear_compl hK c] at h4
  have h5 : Nat.card O * Nat.card (blockRowStab c v) ≤ 15 * Nat.card (blockRowStab c v) :=
    Nat.mul_le_mul_right _ horb
  omega

end Model

section InG

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_leviStab_le_normalizer (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {d : G} (hdC : d ∈ centralizer ({t} : Set G))
    (hdo : ∀ l ∈ L, ∃ x ∈ L, d * x * d⁻¹ ≠ l * x * l⁻¹) :
    ∃ F₀ : Subgroup G, F₀ ≤ seitzTilde W₁ Kc ∧
      F₀ ≤ normalizer ((W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) ∧
      (∀ x ∈ F₀, t * x * t⁻¹ = x) ∧ (∀ x ∈ F₀, x ∈ W₁ → x = 1) ∧ 1344 ≤ Nat.card F₀ := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hdL : d ∈ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
      hdC
  obtain ⟨p, hp⟩ := exists_conj_dualAut_of_outer hset hK e ht hKt hdC hdo
  obtain ⟨P, rfl⟩ := proj_surjective 5 K p
  set v : Fin 5 → K := Pi.single c 1 ᵥ*
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hv
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set F₀ := modelToG e ((blockRowStab c v).map (proj 5 K)) with hF₀
  have hF₀L₁ : F₀ ≤ L₁ := modelToG_mono e (map_mono fun X hX => hX.1)
  have hL₁N : L₁ ≤ seitzTilde W₁ Kc := blockSL_le_seitzTilde hK e htC c hW₁c htN hLN hfield
  have hF₀L : F₀ ≤ L := hF₀L₁.trans (modelToG_le e _)
  have hV₁W₁ : modelToG e (pointRadical (K := K) c) ≤ W₁ := by
    rw [← hW₁t]
    exact inf_le_left
  refine ⟨F₀, hF₀L₁.trans hL₁N, ?_, fun x hx => ?_, fun x hx hxW => ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨_, ⟨X, hX, rfl⟩, rfl⟩ := (mem_modelToG e).1 hx
    set x := ((e.symm (proj 5 K X) : L) : G) with hxdef
    have hxL : x ∈ L := (e.symm (proj 5 K X)).2
    have hyL : d⁻¹ * x * d ∈ L := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hdL) x).1 hxL
      rwa [inv_inv] at h1
    obtain ⟨Y₀, hY₀⟩ := proj_surjective 5 K (e ⟨d⁻¹ * x * d, hyL⟩)
    have h1 := hp ⟨d⁻¹ * x * d, hyL⟩
    rw [show d * (d⁻¹ * x * d) * d⁻¹ = x by group, ← hY₀, MulAut.mul_apply, dualAut_proj,
      MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h1
    have h2 : X = P * (Y₀⁻¹).transpose * P⁻¹ := by
      apply proj_injective_of_natCard_eq_two hK
      apply e.symm.injective
      exact Subtype.ext h1
    have hQ : (Y₀⁻¹).transpose = P⁻¹ * X * P := by rw [h2]; group
    have hrow : ∀ i, ((Y₀⁻¹ : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i c =
        (1 : Matrix (Fin 5) (Fin 5) K) i c := by
      intro i
      have h3 : ((Y₀⁻¹ : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i c =
          (((Y₀⁻¹).transpose : Matrix.SpecialLinearGroup (Fin 5) K) :
            Matrix (Fin 5) (Fin 5) K) c i := by
        rw [Matrix.SpecialLinearGroup.coe_transpose, transpose_apply]
      have h4 : (Pi.single c 1 : Fin 5 → K) ᵥ*
          (((Y₀⁻¹).transpose : Matrix.SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
            Pi.single c 1 := by
        rw [hQ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          ← vecMul_vecMul, ← vecMul_vecMul, ← hv, hX.2, hv, vecMul_vecMul,
          ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
          vecMul_one]
      have h5 := congrFun h4 i
      rw [single_one_vecMul, Matrix.row_apply] at h5
      rw [h3, h5, Pi.single_apply, one_apply]
    obtain ⟨A, hA, r, hAr⟩ := exists_mem_blockSpecialLinear_mul_pointRadElem hrow
    have hmem : e ⟨d⁻¹ * x * d, hyL⟩ ∈ pointRadical (K := K) c ⊔
        blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) := by
      rw [← hY₀, ← inv_inv Y₀, map_inv, hAr, map_mul]
      exact inv_mem (mul_mem (mem_sup_right (proj_mem_blockSL hA))
        (mem_sup_left (proj_pointRadElem_mem_pointRadical c r)))
    have hyN : d⁻¹ * x * d ∈ normalizer (W₁ : Set G) := by
      have h6 : d⁻¹ * x * d ∈ modelToG e (pointRadical (K := K) c ⊔
          blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) := by
        refine (mem_modelToG e).2 ⟨_, hmem, ?_⟩
        rw [MulEquiv.symm_apply_apply]
      rw [modelToG, Subgroup.map_sup, Subgroup.map_sup] at h6
      exact (sup_le (hV₁W₁.trans le_normalizer) hLN) h6
    have h7 := conj_mem_normalizer_of_conj_subset (g := d)
      (W' := W₁.map (MulAut.conj d).toMonoidHom)
      (fun w hw => ⟨w, hw, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩)
      (fun w hw => by
        obtain ⟨w₁, hw₁, rfl⟩ := hw
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          show d⁻¹ * (d * w₁ * d⁻¹) * d = w₁ by group]
        exact hw₁) hyN
    rwa [show d * (d⁻¹ * x * d) * d⁻¹ = x by group] at h7
  ·
    have h1 := (mem_centralizer_iff.1 htC) x (hF₀L hx)
    calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [h1]
      _ = x := by group
  ·
    have hxt : x ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 htC) x (hF₀L hx)
    have hxV : x ∈ modelToG e (pointRadical (K := K) c) := by
      rw [← hW₁t]
      exact mem_inf.2 ⟨hxW, hxt⟩
    obtain ⟨a, ha, hax⟩ := (mem_modelToG e).1 hxV
    obtain ⟨b, hb, hbx⟩ := (mem_modelToG e).1 (hF₀L₁ hx)
    have hab : a = b := e.symm.injective (Subtype.ext (hax.trans hbx.symm))
    have hbot : a ∈ pointRadical (K := K) c ⊓ blockSL (K := K) ({c}ᶜ : Finset (Fin 5)) :=
      mem_inf.2 ⟨ha, hab ▸ hb⟩
    rw [pointRadical_inf_blockSL_compl_eq_bot hK c, mem_bot] at hbot
    rw [← hax, hbot, map_one]
    rfl
  ·
    rw [hF₀, modelToG, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective,
      Subgroup.card_map_of_injective (proj_injective_of_natCard_eq_two hK)]
    exact card_blockRowStab_ge hK c v

end InG

end CFSG.SeitzReduction.LinearPilot
