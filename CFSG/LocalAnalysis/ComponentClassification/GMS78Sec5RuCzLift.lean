module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzSign
public import Certificates.Data.GMS78RuCzRigidCheck

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Subgroup CFSG.CosetTable

namespace Lift

open Sign

variable {H : Type*} [Group H]

theorem map_evalC {K : Type*} [Group K] (φ : H →* K) (y : ℕ → H) (w : List ℕ) :
    φ (evalC y w) = evalC (fun i => φ (y i)) w := by
  induction w with
  | nil => rw [evalC_nil, evalC_nil, map_one]
  | cons c w ih =>
    rw [evalC_cons, evalC_cons, map_mul, ih]
    split_ifs <;> simp

theorem evalC_mem_closure (y : ℕ → H) {n : ℕ} {w : List ℕ} (hw : ∀ c ∈ w, c < 2 * n) :
    evalC y w ∈ closure (y '' {i | i < n}) := by
  induction w with
  | nil => rw [evalC_nil]; exact one_mem _
  | cons c w ih =>
    have hcn : c / 2 < n := by have := hw c List.mem_cons_self; omega
    have hc : y (c / 2) ∈ closure (y '' {i | i < n}) := subset_closure ⟨c / 2, hcn, rfl⟩
    rw [evalC_cons]
    refine mul_mem ?_ (ih fun c' h => hw c' (List.mem_cons_of_mem _ h))
    split_ifs
    exacts [hc, inv_mem hc]

theorem commute_evalC {y : ℕ → H} {t : H} {w : List ℕ} (h : ∀ c ∈ w, Commute (y (c / 2)) t) :
    Commute (evalC y w) t := by
  induction w with
  | nil => rw [evalC_nil]; exact Commute.one_left t
  | cons c w ih =>
    rw [evalC_cons]
    refine Commute.mul_left ?_ (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    split_ifs
    exacts [h c List.mem_cons_self, (h c List.mem_cons_self).inv_left]

theorem xor_one_codes : ∀ c < 20, (c ^^^ 1) / 2 = c / 2 ∧ ((c ^^^ 1) % 2 = 0 ↔ ¬ c % 2 = 0) := by
  decide

theorem evalC_invCodes (y : ℕ → H) {w : List ℕ} (hw : ∀ c ∈ w, c < 20) :
    evalC y (invCodes w) = (evalC y w)⁻¹ := by
  induction w with
  | nil => simp [invCodes]
  | cons c w ih =>
    have e : invCodes (c :: w) = invCodes w ++ [c ^^^ 1] := by
      simp [invCodes]
    obtain ⟨h1, h2⟩ := xor_one_codes c (hw c List.mem_cons_self)
    rw [e, evalC_append, ih fun c' h => hw c' (List.mem_cons_of_mem _ h), evalC_cons,
      evalC_cons, evalC_nil, h1, mul_one, mul_inv_rev]
    congr 1
    by_cases hc : c % 2 = 0
    · rw [ite_eq_right (fun h => h2.1 h hc), ite_eq_left hc]
    · rw [ite_eq_left (h2.2 hc), ite_eq_right hc, inv_inv]

theorem czRelsJ_lt : ∀ r ∈ czRelsJ, ∀ c ∈ r, c < 12 := by decide +kernel

theorem czW_lt : ∀ i < 6, (∀ c ∈ czWq.getD i [], c < 12) ∧ (∀ c ∈ czWv.getD i [], c < 12) ∧
    ∀ c ∈ czWw.getD i [], c < 12 := by decide +kernel

theorem czSols_lt : ∀ s < 8, ∀ i < 6, ∀ c ∈ (czSols.getD s []).getD i [], c < 12 := by
  decide +kernel

theorem czNormX_lt : ∀ s < 4, ∀ c ∈ czNormX.getD s [], c < 4 := by decide +kernel

theorem czP12Codes_lt : ∀ r ∈ czP12Codes, ∀ c ∈ r, c < 18 := by decide +kernel

theorem czHCodes_lt : ∀ r ∈ czHCodes, ∀ c ∈ r, c < 20 := by decide +kernel

theorem czHCodes_getD_lt : ∀ i < 10, ∀ c ∈ czHCodes.getD i [], c < 20 := by decide +kernel

theorem czHTarget_lt : ∀ i < 6, ∀ c ∈ czHTarget i, c < 12 := by decide +kernel

theorem czHCodes_conj : ∀ i < 6, (czHCodes.getD i []).take 3 = [19, 2 * i, 18] ∧
    ∀ c ∈ (czHCodes.getD i []).drop 3, c < 12 := by decide +kernel

theorem czHCodes_six : czHCodes.getD 6 [] = [19, 12, 18, 13] := by decide +kernel

theorem czHCodes_take : czHCodes.take 7 = (List.range 7).map fun i => czHCodes.getD i [] := by
  decide +kernel

theorem czP12Codes_comm : [0, 12, 1, 13] ∈ czP12Codes ∧ [2, 12, 3, 13] ∈ czP12Codes := by
  decide +kernel

@[expose] def sigmaVal (i : ℕ) : Equiv.Perm (Fin 5) :=
  if i < 6 then 1 else if i = 6 then Equiv.swap 2 3 * Equiv.swap 3 4
  else if i = 7 then Equiv.swap 2 3 else if i = 8 then Equiv.swap 1 2 else Equiv.swap 0 1

theorem sigmaVal_drop : ∀ r ∈ czHCodes.drop 7, evalC sigmaVal r = 1 := by decide +kernel

theorem sigma_cube : (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 0 1) ^ 3 = 1 := by decide

theorem eq_top_of_mem {K : Subgroup (Equiv.Perm (Fin 5))}
    (h1 : Equiv.swap 2 3 * Equiv.swap 3 4 ∈ K) (h2 : Equiv.swap (2 : Fin 5) 3 ∈ K)
    (h3 : Equiv.swap (1 : Fin 5) 2 ∈ K) (h4 : Equiv.swap (0 : Fin 5) 1 ∈ K) : K = ⊤ := by
  have h5 : Equiv.swap (3 : Fin 5) 4 ∈ K := by
    have e : Equiv.swap (3 : Fin 5) 4 = Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 2 3 *
        (Equiv.swap 2 3 * Equiv.swap 3 4)⁻¹ := by decide
    rw [e]
    exact K.mul_mem (K.mul_mem h1 h2) (K.inv_mem h1)
  rw [eq_top_iff]
  intro g _
  have hg : g ∈ Submonoid.closure (Set.range fun i : Fin 4 => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  refine (Submonoid.closure_le (S := K.toSubmonoid)).2 ?_ hg
  rintro _ ⟨i, rfl⟩
  fin_cases i
  exacts [h4, h3, h2, h5]

structure IsLetters (σ : H →* Equiv.Perm (Fin 5)) (y : ℕ → H) : Prop where
  rels : ∀ r ∈ czRelsJ, evalC y r = 1
  card : Nat.card (closure (y '' {i | i < 6})) = 2048
  ker : σ.ker = closure (y '' {i | i < 6})
  conjQ : ∀ i < 6, (y 6)⁻¹ * y i * y 6 = evalC y (czWq.getD i [])
  conjV : ∀ i < 6, (y 7)⁻¹ * y i * y 7 = evalC y (czWv.getD i [])
  conjW : ∀ i < 6, (y 8)⁻¹ * y i * y 8 = evalC y (czWw.getD i [])
  p12 : ∀ r ∈ czP12Codes, evalC y r = 1
  sq_mem : y 0 ^ 2 ∈ center H
  sigmaQ : σ (y 6) = Equiv.swap 2 3 * Equiv.swap 3 4
  sigmaV : σ (y 7) = Equiv.swap 2 3
  sigmaW : σ (y 8) = Equiv.swap 1 2

namespace IsLetters

variable {σ : H →* Equiv.Perm (Fin 5)} {y : ℕ → H}

theorem sigma_j (hy : IsLetters σ y) {i : ℕ} (hi : i < 6) : σ (y i) = 1 := by
  rw [← MonoidHom.mem_ker, hy.ker]
  exact subset_closure ⟨i, hi, rfl⟩

theorem commute_q (hy : IsLetters σ y) {i : ℕ} (hi : i < 2) : Commute (y i) (y 6) := by
  have key : ∀ j : ℕ, y j * (y 6 * ((y j)⁻¹ * ((y 6)⁻¹ * 1))) = 1 → Commute (y j) (y 6) := by
    intro j e
    calc y j * y 6 = y j * (y 6 * ((y j)⁻¹ * ((y 6)⁻¹ * 1))) * (y 6 * y j) := by group
      _ = y 6 * y j := by rw [e, one_mul]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact key 0 (hy.p12 _ czP12Codes_comm.1)
  · exact key 1 (hy.p12 _ czP12Codes_comm.2)

end IsLetters

@[expose] def RigidHyp (H : Type*) [Group H] : Prop :=
  ∀ y : ℕ → H, (∀ r ∈ czRelsJ, evalC y r = 1) →
    Nat.card (closure (y '' {i | i < 6})) = 2048 → ∀ yq yw g : H,
    (∀ i < 6, yq⁻¹ * y i * yq = evalC y (czWq.getD i [])) →
    (∀ i < 6, yw⁻¹ * y i * yw = evalC y (czWw.getD i [])) →
    (∀ i < 6, g⁻¹ * y i * g ∈ closure (y '' {i | i < 6})) → g * yq = yq * g →
    (yw * g) ^ 3 ∈ closure (y '' {i | i < 6}) →
    ∃ s < 8, ∀ i < 6, g⁻¹ * y i * g = evalC y ((czSols.getD s []).getD i [])

@[expose] def NormHyp (H : Type*) [Group H] : Prop :=
  ∀ y : ℕ → H, (∀ r ∈ czRelsJ, evalC y r = 1) →
    Nat.card (closure (y '' {i | i < 6})) = 2048 → ∀ (g : H) (s : ℕ), s < 4 →
    (∀ i < 6, g⁻¹ * y i * g = evalC y ((czSols.getD s []).getD i [])) →
    ∀ i < 6, (g * evalC y (czNormX.getD s []))⁻¹ * y i * (g * evalC y (czNormX.getD s [])) =
      evalC y (czHTarget i)

@[expose] def Class2Hyp (H : Type*) [Group H] : Prop :=
  ∀ y : ℕ → H, (∀ r ∈ czRelsJ, evalC y r = 1) →
    Nat.card (closure (y '' {i | i < 6})) = 2048 → ∀ (g : H) (s : ℕ), 4 ≤ s → s < 8 →
    (∀ i < 6, g⁻¹ * y i * g = evalC y ((czSols.getD s []).getD i [])) →
    czClass2To1.getD (s - 4) 0 < 4 ∧ ∀ i < 6, g⁻¹ * evalC y (c2JCodes.getD i []) * g =
      evalC (fun j => evalC y (c2JCodes.getD j []))
        ((czSols.getD (czClass2To1.getD (s - 4) 0) []).getD i [])

@[expose] def SignHyp (H : Type*) [Group H] : Prop :=
  ∀ y : ℕ → H, (∀ r ∈ czRelsJ, evalC y r = 1) →
    Nat.card (closure (y '' {i | i < 6})) = 2048 →
    (∀ i < 6, (y 6)⁻¹ * y i * y 6 = evalC y (czWq.getD i [])) →
    (∀ i < 6, (y 7)⁻¹ * y i * y 7 = evalC y (czWv.getD i [])) →
    (∀ i < 6, (y 8)⁻¹ * y i * y 8 = evalC y (czWw.getD i [])) →
    (∀ i < 6, (y 9)⁻¹ * y i * y 9 = evalC y (czHTarget i)) →
    ∀ r ∈ czHCodes.drop 7, evalC y r ∈ closure (y '' {i | i < 6}) →
      evalC y r = 1 ∨ evalC y r = y 0 ^ 2

variable {σ : H →* Equiv.Perm (Fin 5)} {y : ℕ → H}

theorem exists_norm (hy : IsLetters σ y) (hN : NormHyp H) {h : H}
    (hσh : σ h = Equiv.swap 0 1) (hhq : h * y 6 = y 6 * h) {s : ℕ} (hs : s < 4)
    (hsol : ∀ i < 6, h⁻¹ * y i * h = evalC y ((czSols.getD s []).getD i [])) :
    ∃ g : H, σ g = Equiv.swap 0 1 ∧ g * y 6 = y 6 * g ∧
      ∀ i < 6, g⁻¹ * y i * g = evalC y (czHTarget i) := by
  refine ⟨h * evalC y (czNormX.getD s []), ?_, ?_, hN y hy.rels hy.card h s hs hsol⟩
  · have hu : σ (evalC y (czNormX.getD s [])) = 1 := by
      rw [← MonoidHom.mem_ker, hy.ker]
      exact evalC_mem_closure y fun c hc => by have := czNormX_lt s hs c hc; omega
    rw [map_mul, hσh, hu, mul_one]
  · have hc : Commute (evalC y (czNormX.getD s [])) (y 6) :=
      commute_evalC fun c hc => hy.commute_q (by have := czNormX_lt s hs c hc; omega)
    calc h * evalC y (czNormX.getD s []) * y 6 = h * (y 6 * evalC y (czNormX.getD s [])) := by
          rw [mul_assoc, hc.eq]
      _ = y 6 * (h * evalC y (czNormX.getD s [])) := by rw [← mul_assoc, hhq, mul_assoc]

theorem exists_letters_of_norm (hy : IsLetters σ y) (hS : SignHyp H) {g : H}
    (hσg : σ g = Equiv.swap 0 1) (hgq : g * y 6 = y 6 * g)
    (hgj : ∀ i < 6, g⁻¹ * y i * g = evalC y (czHTarget i))
    (hb1 : ∀ x : Fin 10 → H, (∀ r ∈ czEps1Rels, FreeGroup.lift x (FreeGroup.mk r) = 1) →
      closure (Set.range x) = ⊤ → Nat.card H ≤ 122880)
    (hb2 : ∀ x : Fin 10 → H, (∀ r ∈ czEps2Rels, FreeGroup.lift x (FreeGroup.mk r) = 1) →
      closure (Set.range x) = ⊤ → Nat.card H ≤ 122880)
    (hb3 : ∀ x : Fin 10 → H, (∀ r ∈ czEps3Rels, FreeGroup.lift x (FreeGroup.mk r) = 1) →
      closure (Set.range x) = ⊤ → Nat.card H ≤ 122880)
    (hH : Nat.card H = 245760) :
    ∃ x : Fin 10 → H, (∀ i : Fin 10, i.val < 9 → x i = y i.val) ∧ closure (Set.range x) = ⊤ ∧
      ∀ r ∈ czRels, FreeGroup.lift x (FreeGroup.mk r) = 1 := by
  obtain ⟨z, hz9, hzi⟩ : ∃ z : ℕ → H, z 9 = g ∧ ∀ i, i ≠ 9 → z i = y i :=
    ⟨fun i => if i = 9 then g else y i, ite_eq_left rfl, fun i hi => ite_eq_right hi⟩
  have hzc : ∀ {w : List ℕ}, (∀ c ∈ w, c < 18) → evalC z w = evalC y w := fun hw =>
    evalC_congr fun c hc => hzi _ (by have := hw c hc; omega)
  have hQ : closure (z '' {i | i < 6}) = closure (y '' {i | i < 6}) :=
    congrArg Subgroup.closure (Set.image_congr fun i hi => hzi i (by
      have hi' : i < 6 := hi
      omega))
  have hτ : ∀ i < 10, σ (z i) = sigmaVal i := by
    intro i hi
    rcases (by omega : i < 6 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with h6 | rfl | rfl | rfl | rfl
    · rw [hzi i (by omega), hy.sigma_j h6, sigmaVal, ite_eq_left h6]
    · rw [hzi 6 (by decide), hy.sigmaQ]; rfl
    · rw [hzi 7 (by decide), hy.sigmaV]; rfl
    · rw [hzi 8 (by decide), hy.sigmaW]; rfl
    · rw [hz9, hσg]; rfl
  obtain ⟨X, hX⟩ : ∃ X : Fin 10 → H, X = fun i => z i.val := ⟨_, rfl⟩
  have hXw : ∀ {w : List ℕ}, (∀ c ∈ w, c < 20) →
      FreeGroup.lift X (FreeGroup.mk (wordOfCodes 10 w)) = evalC z w := by
    intro w hw
    rw [lift_mk_wordOfCodes X hw]
    refine evalC_congr fun c hc => ?_
    have hc' : c / 2 < 10 := by have := hw c hc; omega
    rw [hX, ofNat_eq_mk hc']
  have hX0 : X 0 = y 0 := by rw [hX]; exact hzi 0 (by decide)
  have hP12 : ∀ r ∈ czP12Codes, FreeGroup.lift X (FreeGroup.mk (wordOfCodes 10 r)) = 1 := by
    intro r hr
    rw [hXw fun c hc => by have := czP12Codes_lt r hr c hc; omega,
      hzc (czP12Codes_lt r hr), hy.p12 r hr]
  have hH7 : ∀ r ∈ czHCodes.take 7, FreeGroup.lift X (FreeGroup.mk (wordOfCodes 10 r)) = 1 := by
    intro r hr
    rw [czHCodes_take] at hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    rw [List.mem_range] at hi
    rw [hXw (czHCodes_getD_lt i (by omega))]
    rcases (by omega : i < 6 ∨ i = 6) with h6 | rfl
    · obtain ⟨ht, hd⟩ := czHCodes_conj i h6
      rw [← List.take_append_drop 3 (czHCodes.getD i []), evalC_append, ht,
        hzc (w := (czHCodes.getD i []).drop 3) fun c hc => by have := hd c hc; omega]
      have h2m : 2 * i % 2 = 0 := by omega
      have h2i : 2 * i / 2 = i := by omega
      have e : evalC z [19, 2 * i, 18] = g⁻¹ * y i * g := by
        rw [evalC_cons, evalC_cons, h2m, h2i, ite_eq_left rfl]
        change (z 9)⁻¹ * (z i * (z 9 * 1)) = _
        rw [hz9, hzi i (by omega), mul_one, mul_assoc]
      rw [e, hgj i h6, czHTarget, evalC_invCodes y fun c hc => by have := hd c hc; omega,
        inv_mul_cancel]
    · rw [czHCodes_six]
      change (z 9)⁻¹ * (z 6 * (z 9 * ((z 6)⁻¹ * 1))) = 1
      rw [hz9, hzi 6 (by decide)]
      calc g⁻¹ * (y 6 * (g * ((y 6)⁻¹ * 1))) = g⁻¹ * (y 6 * g) * (y 6)⁻¹ := by group
        _ = 1 := by rw [← hgq]; group
  have hsgn : ∀ r ∈ czHCodes.drop 7, FreeGroup.lift X (FreeGroup.mk (wordOfCodes 10 r)) = 1 ∨
      FreeGroup.lift X (FreeGroup.mk (wordOfCodes 10 r)) = X 0 ^ 2 := by
    intro r hr
    have hr20 : ∀ c ∈ r, c < 20 := czHCodes_lt r (List.mem_of_mem_drop hr)
    rw [hXw hr20, hX0, ← hzi 0 (by decide)]
    refine hS z (fun r' hr' => ?_) (by rw [hQ]; exact hy.card) (fun i hi => ?_) (fun i hi => ?_)
      (fun i hi => ?_) (fun i hi => ?_) r hr ?_
    · rw [hzc fun c hc => by have := czRelsJ_lt r' hr' c hc; omega]
      exact hy.rels r' hr'
    · rw [hzi 6 (by decide), hzi i (by omega),
        hzc fun c hc => by have := (czW_lt i hi).1 c hc; omega]
      exact hy.conjQ i hi
    · rw [hzi 7 (by decide), hzi i (by omega),
        hzc fun c hc => by have := (czW_lt i hi).2.1 c hc; omega]
      exact hy.conjV i hi
    · rw [hzi 8 (by decide), hzi i (by omega),
        hzc fun c hc => by have := (czW_lt i hi).2.2 c hc; omega]
      exact hy.conjW i hi
    · rw [hz9, hzi i (by omega), hzc fun c hc => by have := czHTarget_lt i hi c hc; omega]
      exact hgj i hi
    · rw [hQ, ← hy.ker, MonoidHom.mem_ker, map_evalC,
        evalC_congr (g₂ := sigmaVal) fun c hc => hτ _ (by have := hr20 c hc; omega)]
      exact sigmaVal_drop r hr
  have hgen : closure (Set.range X) = ⊤ := by
    have hXz : ∀ i (hi : i < 10), z i ∈ closure (Set.range X) := fun i hi =>
      subset_closure ⟨⟨i, hi⟩, by rw [hX]⟩
    have hker : σ.ker ≤ closure (Set.range X) := by
      rw [hy.ker, closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < 6 := hi
      rw [← hzi i (by omega)]
      exact hXz i (by omega)
    have himg : (closure (Set.range X)).map σ = ⊤ :=
      eq_top_of_mem ⟨z 6, hXz 6 (by decide), (hτ 6 (by decide)).trans rfl⟩
        ⟨z 7, hXz 7 (by decide), (hτ 7 (by decide)).trans rfl⟩
        ⟨z 8, hXz 8 (by decide), (hτ 8 (by decide)).trans rfl⟩
        ⟨z 9, hXz 9 (by decide), (hτ 9 (by decide)).trans rfl⟩
    rw [eq_top_iff]
    intro a _
    have ha : σ a ∈ (closure (Set.range X)).map σ := by
      rw [himg]
      exact mem_top _
    obtain ⟨c, hc, hca⟩ := mem_map.1 ha
    have hac : a * c⁻¹ ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hca, mul_inv_cancel]
    simpa using mul_mem (hker hac) hc
  have hz0 : X 0 ^ 2 ∈ center H := by
    rw [hX0]
    exact hy.sq_mem
  obtain ⟨x, hx, -, hxgen, hxrel⟩ := czSign_of hb1 hb2 hb3 hH X hz0 hP12 hH7 hsgn hgen
  refine ⟨x, fun i hi => ?_, hxgen, hxrel⟩
  rw [hx i hi, hX]
  exact hzi _ (by omega)

theorem exists_letters {k k' : ℕ → H} (hk : IsLetters σ k) (hk' : IsLetters σ k')
    (hk'j : ∀ i < 6, k' i = evalC k (c2JCodes.getD i [])) (hk'q : k' 6 = k 6) {h : H}
    (hσh : σ h = Equiv.swap 0 1) (hhq : h * k 6 = k 6 * h) (hR : RigidHyp H) (hN : NormHyp H)
    (hC : Class2Hyp H) (hS : SignHyp H)
    (hb1 : ∀ x : Fin 10 → H, (∀ r ∈ czEps1Rels, FreeGroup.lift x (FreeGroup.mk r) = 1) →
      closure (Set.range x) = ⊤ → Nat.card H ≤ 122880)
    (hb2 : ∀ x : Fin 10 → H, (∀ r ∈ czEps2Rels, FreeGroup.lift x (FreeGroup.mk r) = 1) →
      closure (Set.range x) = ⊤ → Nat.card H ≤ 122880)
    (hb3 : ∀ x : Fin 10 → H, (∀ r ∈ czEps3Rels, FreeGroup.lift x (FreeGroup.mk r) = 1) →
      closure (Set.range x) = ⊤ → Nat.card H ≤ 122880)
    (hH : Nat.card H = 245760) :
    ∃ x : Fin 10 → H, ((∀ i : Fin 10, i.val < 9 → x i = k i.val) ∨
      ∀ i : Fin 10, i.val < 9 → x i = k' i.val) ∧ closure (Set.range x) = ⊤ ∧
      ∀ r ∈ czRels, FreeGroup.lift x (FreeGroup.mk r) = 1 := by
  have hn : ∀ i < 6, h⁻¹ * k i * h ∈ closure (k '' {i | i < 6}) := by
    intro i hi
    rw [← hk.ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, hk.sigma_j hi, mul_one,
      inv_mul_cancel]
  have h3 : (k 8 * h) ^ 3 ∈ closure (k '' {i | i < 6}) := by
    rw [← hk.ker, MonoidHom.mem_ker, map_pow, map_mul, hk.sigmaW, hσh]
    exact sigma_cube
  obtain ⟨s, hs8, hs⟩ := hR k hk.rels hk.card (k 6) (k 8) h hk.conjQ hk.conjW hn hhq h3
  rcases Nat.lt_or_ge s 4 with hs4 | hs4
  · obtain ⟨g, hσg, hgq, hgj⟩ := exists_norm hk hN hσh hhq hs4 hs
    obtain ⟨x, hx, hgen, hrel⟩ := exists_letters_of_norm hk hS hσg hgq hgj hb1 hb2 hb3 hH
    exact ⟨x, Or.inl hx, hgen, hrel⟩
  · obtain ⟨hs', hs2⟩ := hC k hk.rels hk.card h s hs4 hs8 hs
    have hsol : ∀ i < 6, h⁻¹ * k' i * h =
        evalC k' ((czSols.getD (czClass2To1.getD (s - 4) 0) []).getD i []) := by
      intro i hi
      rw [hk'j i hi, hs2 i hi]
      refine evalC_congr fun c hc => (hk'j _ ?_).symm
      have := czSols_lt _ (by omega) i hi c hc
      omega
    have hhq' : h * k' 6 = k' 6 * h := by rw [hk'q]; exact hhq
    obtain ⟨g, hσg, hgq, hgj⟩ := exists_norm hk' hN hσh hhq' hs' hsol
    obtain ⟨x, hx, hgen, hrel⟩ := exists_letters_of_norm hk' hS hσg hgq hgj hb1 hb2 hb3 hH
    exact ⟨x, Or.inr hx, hgen, hrel⟩

end Lift

end CFSG.ComponentClassification.GMS78.RuCz
