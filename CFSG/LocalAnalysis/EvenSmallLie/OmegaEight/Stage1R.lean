module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Wsub
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

theorem prod_map_mul_of_comm {H : Subgroup G} (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    {ι : Type*} (l : List ι) (f g : ι → G) (hf : ∀ i, f i ∈ H) (hg : ∀ i, g i ∈ H) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hF : (l.map f).prod ∈ H := list_prod_mem fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact hf j
    simp only [List.map_cons, List.prod_cons, ih]
    have hc := hH (g i) (hg i) _ hF
    calc f i * g i * ((l.map f).prod * (l.map g).prod)
        = f i * (g i * (l.map f).prod) * (l.map g).prod := by group
      _ = f i * ((l.map f).prod * g i) * (l.map g).prod := by rw [hc]
      _ = f i * (l.map f).prod * (g i * (l.map g).prod) := by group

theorem prod_map_mem {H : Subgroup G} {ι : Type*} (l : List ι) (f : ι → G) (hf : ∀ i, f i ∈ H) :
    (l.map f).prod ∈ H :=
  list_prod_mem fun x hx => by obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact hf j

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
  (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS hZ

@[expose] noncomputable def wY [Finite G] (y : V6) : G :=
  ((List.finRange 6).map fun j => if y j = 1 then hS.dW hZ j else 1).prod

theorem wY_mem [Finite G] (y : V6) : hS.wY hZ y ∈ hS.Wsub hZ :=
  prod_map_mem _ _ fun j => by
    split_ifs
    · exact hS.dW_mem_Wsub hZ j
    · exact one_mem _

theorem tauD_wY [Finite G] (y : V6) : tauD t ψ (hS.wY hZ y) = y := by
  rw [wY, (hS.tauD_list_prod hZ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    split_ifs
    · exact hS.dW_mem hZ j
    · exact one_mem _).2, List.map_map, ← Fin.sum_univ_def]
  conv_rhs => rw [eq_sum_basisVec y]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (y j) with h | h
  · simp only [h, zero_smul, show ¬ (0 : ZMod 2) = 1 by decide, ite_false]
    exact (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)
  · simp only [h, one_smul, ite_true, hS.tauD_dW hZ]

theorem wY_add [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (y y' : V6) :
    hS.wY hZ (y + y') = hS.wY hZ y * hS.wY hZ y' := by
  rw [wY, wY, wY, ← prod_map_mul_of_comm (fun x hx y hy => hS.Wsub_comm hZ hx hy)]
  · congr 1
    refine List.map_congr_left fun j _ => ?_
    have hd := hW2 _ (hS.dW_mem_Wsub hZ j)
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (y j) with h | h <;>
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (y' j) with h' | h' <;>
      simp [h, h', hd]
  · intro j; split_ifs
    · exact hS.dW_mem_Wsub hZ j
    · exact one_mem _
  · intro j; split_ifs
    · exact hS.dW_mem_Wsub hZ j
    · exact one_mem _

theorem conj_dW_mem_Wsub [Finite G] {x : G} (hx : x ∈ P) (j : Fin 6) :
    x * hS.dW hZ j * x⁻¹ ∈ hS.Wsub hZ :=
  (mem_normalizer_iff.1 (hS.P_le_normalizer_Wsub hZ hx) _).1 (hS.dW_mem_Wsub hZ j)

theorem inv_wY_mem [Finite G] (y : V6) : (hS.wY hZ y)⁻¹ ∈ hS.Wsub hZ :=
  inv_mem (hS.wY_mem hZ y)

theorem mem_Q_of_mem_Wsub [Finite G] {w : G} (hw : w ∈ hS.Wsub hZ) (h0 : tauD t ψ w = 0) :
    w ∈ Q := by
  have hE := (hS.tauD_eq_zero_iff hZ (hS.Wsub_le_D hZ hw)).1 h0
  obtain ⟨v, h | h⟩ := hS.mem_E_iff.1 hE
  · exact h ▸ hS.rad.ψ_mem v
  · exfalso
    apply hS.t_not_mem_Wsub hZ
    have := mul_mem hw (inv_mem (hS.Q_le_Wsub hZ (hS.rad.ψ_mem v)))
    rwa [h, mul_inv_cancel_right] at this

@[expose] noncomputable def kapG [Finite G] (i : Fin 6) : Mat6 :=
  Matrix.of fun r c => coord ψ (p i * hS.dW hZ c * (p i)⁻¹ *
    (hS.wY hZ (genMat ε i *ᵥ basisVec c))⁻¹) r

theorem conj_dW_eq [Finite G] (i : Fin 6) (c : Fin 6) :
    p i * hS.dW hZ c * (p i)⁻¹ = ψ (fun r => hS.kapG hZ i r c) *
      hS.wY hZ (genMat ε i *ᵥ basisVec c) := by
  have hW := mul_mem (hS.conj_dW_mem_Wsub hZ (hS.rad.p_mem i) c)
    (hS.inv_wY_mem hZ (genMat ε i *ᵥ basisVec c))
  have hτ : tauD t ψ (p i * hS.dW hZ c * (p i)⁻¹ * (hS.wY hZ (genMat ε i *ᵥ basisVec c))⁻¹) = 0 := by
    have h1 := hS.Wsub_le_D hZ (hS.conj_dW_mem_Wsub hZ (hS.rad.p_mem i) c)
    have h2 := hS.Wsub_le_D hZ (hS.inv_wY_mem hZ (genMat ε i *ᵥ basisVec c))
    rw [hS.tauD_mul hZ h1 h2, hS.tauD_conj hZ (hS.rad.p_mem i) (hS.dW_mem hZ c), hS.tauD_dW hZ,
      hS.rad.lin_p]
    have h3 := hS.tauD_mul hZ (hS.Wsub_le_D hZ (hS.wY_mem hZ (genMat ε i *ᵥ basisVec c))) h2
    rw [mul_inv_cancel, (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _), hS.tauD_wY] at h3
    exact h3.symm
  have hQ := hS.mem_Q_of_mem_Wsub hZ hW hτ
  have : ψ (fun r => hS.kapG hZ i r c) = p i * hS.dW hZ c * (p i)⁻¹ *
      (hS.wY hZ (genMat ε i *ᵥ basisVec c))⁻¹ := by
    rw [← hS.rad.ψ_coord hQ]
    rfl
  rw [this, inv_mul_cancel_right]

omit hZ in
theorem ψ_list_sum {ι : Type*} (l : List ι) (f : ι → V6) :
    ψ (l.map f).sum = (l.map fun i => ψ (f i)).prod := by
  induction l with
  | nil => simp [hS.rad.ψ_zero]
  | cons i l ih => simp only [List.map_cons, List.sum_cons, List.prod_cons, hS.rad.ψ_add, ih]

theorem wY_zero [Finite G] : hS.wY hZ 0 = 1 := by
  simp [wY, show ¬ (0 : ZMod 2) = 1 by decide]

theorem wY_list_sum [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {ι : Type*} (l : List ι)
    (f : ι → V6) : hS.wY hZ (l.map f).sum = (l.map fun i => hS.wY hZ (f i)).prod := by
  induction l with
  | nil => simp [hS.wY_zero hZ]
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, hS.wY_add hZ hW2, ih]

omit hS hZ in
theorem mulVec_eq_sum (M : Mat6) (y : V6) :
    M *ᵥ y = ((List.finRange 6).map fun j => y j • fun r => M r j).sum := by
  rw [← Fin.sum_univ_def]
  ext r
  simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem conj_wY [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (i : Fin 6) (y : V6) :
    p i * hS.wY hZ y * (p i)⁻¹ = ψ (hS.kapG hZ i *ᵥ y) * hS.wY hZ (genMat ε i *ᵥ y) := by
  have hconj : p i * hS.wY hZ y * (p i)⁻¹ =
      ((List.finRange 6).map fun j => p i * (if y j = 1 then hS.dW hZ j else 1) * (p i)⁻¹).prod := by
    rw [wY]
    have := map_list_prod (MulAut.conj (p i)).toMonoidHom
      ((List.finRange 6).map fun j => if y j = 1 then hS.dW hZ j else 1)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.map_map] at this
    rw [this]
    rfl
  have hsplit : ∀ j, p i * (if y j = 1 then hS.dW hZ j else 1) * (p i)⁻¹ =
      (if y j = 1 then ψ (fun r => hS.kapG hZ i r j) else 1) *
        (if y j = 1 then hS.wY hZ (genMat ε i *ᵥ basisVec j) else 1) := by
    intro j
    split_ifs
    · exact hS.conj_dW_eq hZ i j
    · group
  rw [hconj, List.map_congr_left fun j _ => hsplit j,
    prod_map_mul_of_comm (fun x hx y hy => hS.Wsub_comm hZ hx hy)]
  · congr 1
    · rw [mulVec_eq_sum, hS.ψ_list_sum]
      refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (y j) with h | h
      · simp [h, hS.rad.ψ_zero, show ¬ (0 : ZMod 2) = 1 by decide]
      · simp [h]
    · rw [mulVec_eq_sum (genMat ε i), hS.wY_list_sum hZ hW2]
      refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (y j) with h | h
      · simp [h, hS.wY_zero hZ, show ¬ (0 : ZMod 2) = 1 by decide]
      · simp only [h, ite_true, one_smul]
        congr 1
        ext r
        rw [mulVec_basisVec]
  · intro j
    split_ifs
    · exact hS.Q_le_Wsub hZ (hS.rad.ψ_mem _)
    · exact one_mem _
  · intro j
    split_ifs
    · exact hS.wY_mem hZ _
    · exact one_mem _

theorem conj_wY_word [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (w : List ℕ)
    (hw : ∀ s ∈ w, s < 6) (y : V6) :
    wordElt p w * hS.wY hZ y * (wordElt p w)⁻¹ =
      ψ ((urMat6 ε (extC (hS.kapG hZ)) w).2 *ᵥ y) *
        hS.wY hZ ((urMat6 ε (extC (hS.kapG hZ)) w).1 *ᵥ y) := by
  induction w generalizing y with
  | nil => simp [wordElt, urMat6, hS.rad.ψ_zero]
  | cons s w ih =>
    have hs : s < 6 := hw s List.mem_cons_self
    have ih' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) y
    have hp : pAt p s = p ⟨s, hs⟩ := by simp [pAt, hs]
    have hW : wordElt p (s :: w) = p ⟨s, hs⟩ * wordElt p w := by
      rw [wordElt, List.map_cons, List.prod_cons, hp]; rfl
    rw [hW]
    calc p ⟨s, hs⟩ * wordElt p w * hS.wY hZ y * (p ⟨s, hs⟩ * wordElt p w)⁻¹
        = p ⟨s, hs⟩ * (wordElt p w * hS.wY hZ y * (wordElt p w)⁻¹) * (p ⟨s, hs⟩)⁻¹ := by group
      _ = (p ⟨s, hs⟩ * ψ ((urMat6 ε (extC (hS.kapG hZ)) w).2 *ᵥ y) * (p ⟨s, hs⟩)⁻¹) *
          (p ⟨s, hs⟩ * hS.wY hZ ((urMat6 ε (extC (hS.kapG hZ)) w).1 *ᵥ y) * (p ⟨s, hs⟩)⁻¹) := by
          rw [ih']; group
      _ = _ := by
          rw [hS.rad.p_act, hS.conj_wY hZ hW2, ← mul_assoc, ← hS.rad.ψ_add]
          simp only [urMat6, extC, hs, dite_true, add_mulVec, mulVec_mulVec]

omit hS hZ in
theorem urMat6_fst_eq (C : ℕ → Mat6) (w : List ℕ) :
    (urMat6 ε C w).1 = toMat 6 6 (wordRows ε w) := by
  induction w with
  | nil => exact toMat_id6'.symm
  | cons s w ih => rw [urMat6, wordRows, toMat_bmul, ih]; rfl

theorem lin_wordElt_mat [Finite G] (w : List ℕ) (v : V6) :
    lin ψ (wordElt p w) v = (urMat6 ε (extC (hS.kapG hZ)) w).1 *ᵥ v := by
  induction w generalizing v with
  | nil => simp [wordElt, urMat6, hS.rad.lin_one]
  | cons s w ih =>
    have h : wordElt p (s :: w) = pAt p s * wordElt p w := by
      rw [wordElt, List.map_cons, List.prod_cons]; rfl
    rw [h, hS.rad.lin_mul (hS.rad.P_le_normalizer (hS.rad.pAt_mem s))
      (hS.rad.P_le_normalizer (hS.rad.wordElt_mem w)), ih, hS.rad.lin_pAt]
    simp only [urMat6, mulVec_mulVec]

theorem urMat6_rel [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {r : List ℕ}
    (hr : r ∈ extRels ε) : (urMat6 ε (extC (hS.kapG hZ)) r).2 = 0 := by
  have hlt : ∀ s ∈ r, s < 6 := fun s hs => by
    obtain ⟨k, hk, hkr⟩ := List.getElem_of_mem hr
    exact extRels_lt ε (k := k) (by rw [List.getD_eq_getElem _ _ hk, hkr]; exact hs)
  have hM : (urMat6 ε (extC (hS.kapG hZ)) r).1 = 1 := by
    rw [urMat6_fst_eq]
    have h := (cohChecks ε).1
    simp only [relCheck6, Bool.and_eq_true, List.all_eq_true] at h
    exact toMat_eq_one_of_bIsId (h.2 r hr)
  have hwQ : wordElt p r ∈ Q := by
    refine hS.mem_Q_of_mem_P (hS.rad.wordElt_mem r) (mem_centralizer_iff.2 fun q hq => ?_)
    obtain ⟨v, rfl⟩ := hS.rad.mem_ψ q hq
    have h1 := hS.lin_wordElt_mat hZ r v
    rw [hM, one_mulVec, hS.rad.lin_eq_iff (hS.rad.P_le_normalizer (hS.rad.wordElt_mem r))] at h1
    calc ψ v * wordElt p r = wordElt p r * ψ v * (wordElt p r)⁻¹ * wordElt p r := by rw [h1]
      _ = wordElt p r * ψ v := by group
  ext i j
  have h1 := hS.conj_wY_word hZ hW2 r hlt (basisVec j)
  rw [hM, one_mulVec] at h1
  have hc : wordElt p r * hS.wY hZ (basisVec j) * (wordElt p r)⁻¹ = hS.wY hZ (basisVec j) := by
    rw [hS.Wsub_comm hZ (hS.Q_le_Wsub hZ hwQ) (hS.wY_mem hZ _), mul_inv_cancel_right]
  rw [hc] at h1
  have h2 : ψ ((urMat6 ε (extC (hS.kapG hZ)) r).2 *ᵥ basisVec j) = ψ 0 := by
    rw [hS.rad.ψ_zero]
    exact (mul_eq_right.1 h1.symm)
  have h3 := congrFun (hS.rad.ψ_inj h2) i
  rw [mulVec_basisVec] at h3
  exact h3

theorem exists_X [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) :
    ∃ X : Mat6, ∀ i : Fin 6, hS.kapG hZ i = genMat ε i * X + X * genMat ε i :=
  exists_coboundary6 ε (hS.kapG hZ) fun _ hr => hS.urMat6_rel hZ hW2 hr

@[expose] noncomputable def rY [Finite G] (X : Mat6) (u : V6) : G := ψ (X *ᵥ u) * hS.wY hZ u

theorem rY_mem [Finite G] (X : Mat6) (u : V6) : hS.rY hZ X u ∈ hS.Wsub hZ :=
  mul_mem (hS.Q_le_Wsub hZ (hS.rad.ψ_mem _)) (hS.wY_mem hZ u)

theorem rY_add [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (X : Mat6) (u u' : V6) :
    hS.rY hZ X (u + u') = hS.rY hZ X u * hS.rY hZ X u' := by
  rw [rY, rY, rY, mulVec_add, hS.rad.ψ_add, hS.wY_add hZ hW2]
  have hc := hS.Wsub_comm hZ (hS.Q_le_Wsub hZ (hS.rad.ψ_mem (X *ᵥ u'))) (hS.wY_mem hZ u)
  calc ψ (X *ᵥ u) * ψ (X *ᵥ u') * (hS.wY hZ u * hS.wY hZ u')
      = ψ (X *ᵥ u) * (ψ (X *ᵥ u') * hS.wY hZ u) * hS.wY hZ u' := by group
    _ = ψ (X *ᵥ u) * (hS.wY hZ u * ψ (X *ᵥ u')) * hS.wY hZ u' := by rw [hc]
    _ = ψ (X *ᵥ u) * hS.wY hZ u * (ψ (X *ᵥ u') * hS.wY hZ u') := by group

theorem tauD_rY [Finite G] (X : Mat6) (u : V6) : tauD t ψ (hS.rY hZ X u) = u := by
  rw [rY, hS.tauD_mul hZ (hS.Q_le_D (hS.rad.ψ_mem _)) (hS.Wsub_le_D hZ (hS.wY_mem hZ u)),
    (hS.tauD_eq_zero_iff hZ (hS.Q_le_D (hS.rad.ψ_mem _))).2 (mem_sup_left (hS.rad.ψ_mem _)),
    zero_add, hS.tauD_wY]

@[expose] noncomputable def rHom [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (X : Mat6) :
    Multiplicative V6 →* G where
  toFun u := hS.rY hZ X (Multiplicative.toAdd u)
  map_one' := by
    simp only [toAdd_one, rY, mulVec_zero, hS.rad.ψ_zero, hS.wY_zero hZ, mul_one]
  map_mul' u u' := by
    simp only [toAdd_mul]
    exact hS.rY_add hZ hW2 X _ _

@[expose] noncomputable def Rsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (X : Mat6) :
    Subgroup G :=
  (hS.rHom hZ hW2 X).range

theorem mem_Rsub [Finite G] {hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1} {X : Mat6} {r : G} :
    r ∈ hS.Rsub hZ hW2 X ↔ ∃ u, hS.rY hZ X u = r :=
  ⟨fun ⟨u, hu⟩ => ⟨Multiplicative.toAdd u, hu⟩, fun ⟨u, hu⟩ => ⟨Multiplicative.ofAdd u, hu⟩⟩

theorem Rsub_le_Wsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (X : Mat6) :
    hS.Rsub hZ hW2 X ≤ hS.Wsub hZ := by
  rintro r ⟨u, rfl⟩
  exact hS.rY_mem hZ X _

theorem inf_Rsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (X : Mat6) :
    Q ⊓ hS.Rsub hZ hW2 X = ⊥ := by
  rw [eq_bot_iff]
  rintro r ⟨hrQ, hrR⟩
  obtain ⟨u, rfl⟩ := (hS.mem_Rsub hZ).1 hrR
  have h0 : u = 0 := by
    rw [← hS.tauD_rY hZ X u]
    exact (hS.tauD_eq_zero_iff hZ (hS.Q_le_D hrQ)).2 (mem_sup_left hrQ)
  rw [h0, rY, mulVec_zero, hS.rad.ψ_zero, hS.wY_zero hZ, mul_one]
  exact one_mem _

theorem sup_Rsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) (X : Mat6) :
    Q ⊔ hS.Rsub hZ hW2 X = hS.Wsub hZ := by
  refine le_antisymm (sup_le (hS.Q_le_Wsub hZ) (hS.Rsub_le_Wsub hZ hW2 X)) fun w hw => ?_
  set r := hS.rY hZ X (tauD t ψ w)
  have hrR : r ∈ hS.Rsub hZ hW2 X := (hS.mem_Rsub hZ).2 ⟨_, rfl⟩
  have hq : w * r⁻¹ ∈ Q := by
    refine hS.mem_Q_of_mem_Wsub hZ (mul_mem hw (inv_mem (hS.rY_mem hZ X _))) ?_
    have hrD := hS.Wsub_le_D hZ (hS.rY_mem hZ X (tauD t ψ w))
    have h1 := hS.tauD_mul hZ (hS.Wsub_le_D hZ hw) (inv_mem hrD)
    have h2 := hS.tauD_mul hZ hrD (inv_mem hrD)
    rw [mul_inv_cancel, (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _), hS.tauD_rY] at h2
    rw [h1]
    exact h2.symm
  have : w = w * r⁻¹ * r := by group
  rw [this]
  exact mul_mem (mem_sup_left hq) (mem_sup_right hrR)

theorem conj_rY_gen [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {X : Mat6}
    (hX : ∀ i : Fin 6, hS.kapG hZ i = genMat ε i * X + X * genMat ε i) (i : Fin 6) (u : V6) :
    p i * hS.rY hZ X u * (p i)⁻¹ = hS.rY hZ X (genMat ε i *ᵥ u) := by
  have h1 : p i * hS.rY hZ X u * (p i)⁻¹ =
      (p i * ψ (X *ᵥ u) * (p i)⁻¹) * (p i * hS.wY hZ u * (p i)⁻¹) := by
    rw [rY]; group
  rw [h1, hS.rad.p_act, hS.conj_wY hZ hW2, ← mul_assoc, ← hS.rad.ψ_add, rY, hX i]
  congr 2
  rw [add_mulVec, mulVec_mulVec, mulVec_mulVec, ← add_assoc]
  have h2 : ∀ v w : V6, v + v + w = w := fun v w => by
    ext r
    simp only [Pi.add_apply]
    exact (by decide : ∀ a b : ZMod 2, a + a + b = b) _ _
  rw [h2]

theorem P_le_normalizer_Rsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {X : Mat6}
    (hX : ∀ i : Fin 6, hS.kapG hZ i = genMat ε i * X + X * genMat ε i) :
    P ≤ normalizer (hS.Rsub hZ hW2 X : Set G) := by
  refine hS.rad.P_le.trans ((closure_le _).2 ?_)
  rintro x (hx | ⟨i, rfl⟩)
  · refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun r hr => ?_)
    exact hS.Wsub_comm hZ (hS.Rsub_le_Wsub hZ hW2 X hr) (hS.Q_le_Wsub hZ hx)
  · change p i ∈ normalizer (hS.Rsub hZ hW2 X : Set G)
    rw [mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [Subgroup.card_map_of_injective (MulAut.conj (p i)).injective])
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨u, rfl⟩ := (hS.mem_Rsub hZ).1 hr
    change p i * hS.rY hZ X u * (p i)⁻¹ ∈ hS.Rsub hZ hW2 X
    rw [hS.conj_rY_gen hZ hW2 hX]
    exact (hS.mem_Rsub hZ).2 ⟨_, rfl⟩

theorem commutator_mem_Rsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {X : Mat6} {r : G}
    (hr : r ∈ hS.Rsub hZ hW2 X) : r * t * r⁻¹ * t⁻¹ ∈ Q := by
  have := hS.kap_t_right hZ (hS.Wsub_le_D hZ (hS.Rsub_le_Wsub hZ hW2 X hr))
  rw [kap] at this
  rw [this]
  exact hS.rad.ψ_mem _

theorem commutator_eq_one_Rsub [Finite G] (hW2 : ∀ w ∈ hS.Wsub hZ, w * w = 1) {X : Mat6}
    {r : G} (hr : r ∈ hS.Rsub hZ hW2 X) (h1 : r * t * r⁻¹ * t⁻¹ = 1) : r = 1 := by
  have hrD := hS.Wsub_le_D hZ (hS.Rsub_le_Wsub hZ hW2 X hr)
  have h2 := hS.kap_t_right hZ hrD
  rw [kap, h1, ← hS.rad.ψ_zero] at h2
  have h3 := (hS.tauD_eq_zero_iff hZ hrD).1 (hS.rad.ψ_inj h2).symm
  have hrQ : r ∈ Q := by
    obtain ⟨v, h | h⟩ := hS.mem_E_iff.1 h3
    · exact h ▸ hS.rad.ψ_mem v
    · exfalso
      apply hS.t_not_mem_Wsub hZ
      have := mul_mem (hS.Rsub_le_Wsub hZ hW2 X hr) (inv_mem (hS.Q_le_Wsub hZ (hS.rad.ψ_mem v)))
      rwa [h, mul_inv_cancel_right] at this
  have := hS.inf_Rsub hZ hW2 X
  have hmem : r ∈ Q ⊓ hS.Rsub hZ hW2 X := ⟨hrQ, hr⟩
  rw [this, mem_bot] at hmem
  exact hmem

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
