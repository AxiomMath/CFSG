module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainShapeBCore
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainShapeBCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainPlus

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G] {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G}

theorem dig4_641 : toVec4 (dig4 641) = Pi.single 0 1 + toVec4 (twoV 24) := by
  ext j
  fin_cases j <;> simp [toVec4, dig4, twoV] <;> decide

theorem red_dig4_641 : (fun j => red4 (toVec4 (dig4 641) j)) = (Pi.single 0 1 : V6) := by
  ext j
  fin_cases j <;> simp [toVec4, dig4] <;> decide

theorem homocyclic_false_shapeB [Finite G]
    (hK : Stage0.StepK t L)
    (hS : Setup .plus t L U Q P a ψ p) (hu : UData .plus U Q ψ u)
    (hU6 : closure (Set.range u) ⊓ Q = ⊥) (hNL : ∀ x ∈ L, x ∈ normalizer (U : Set G) → x ∈ U)
    (hNQ : ∀ x ∈ centralizer ({t} : Set G),
      x ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → x ∈ L ⊔ zpowers t)
    (h3 : ∀ x ∈ centralizer ({t} : Set G), x ^ 3 ∈ L ⊔ zpowers t)
    (hrel3 : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 3)
    (hn3 : ∃ n ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a ∧
      n * n ∈ U ∧ ∀ y ∈ closure ({ψ (Pi.single 0 1), ψ (Pi.single 1 1), ψ (Pi.single 2 1),
        u 3, u 4, u 5} : Set G), n * y = y * n)
    {W : Subgroup G} (hW : Premises t Q W) (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) : False := by
  have hR := hS.rad
  have hL := hW.level_two hS hinv
  obtain ⟨Φ, hΦ, hrepW⟩ := exists_coord_lift (ε := .plus) hS hL
    fun x hx y hy => hW.P_conj_mem hS hx hy
  have hUle : closure (Set.range u) ≤ U := (closure_le U).2 (Set.range_subset_iff.2 hu.u_mem)
  choose ℓ' hℓ'U hℓ'l using fun i : Fin 64 => hu.exists_mem_closure hR i.isLt
  let ℓ : ℕ → G := fun i => if h : i < 64 then ℓ' ⟨i, h⟩ else 1
  have hℓU : ∀ i, ℓ i ∈ closure (Set.range u) := fun i => by
    by_cases h : i < 64
    · simp only [ℓ, dite_eq_left h]; exact hℓ'U _
    · simp only [ℓ, dite_eq_right h]; exact one_mem _
  have hℓl : ∀ i < 64, ∀ v, lin ψ (ℓ i) v = s0Mat .plus i *ᵥ v := fun i hi v => by
    simp only [ℓ, dite_eq_left hi]; exact hℓ'l _ v
  have hℓP : ∀ i, ℓ i ∈ P := fun i => hR.U_le_P (hUle (hℓU i))
  have hℓN : ∀ i, ℓ i ∈ normalizer (Q : Set G) := fun i => hR.P_le_normalizer (hℓP i)
  have hℓuniq : ∀ i < 64, ∀ x ∈ closure (Set.range u),
      (∀ v, lin ψ x v = s0Mat .plus i *ᵥ v) → x = ℓ i :=
    fun i hi x hx h => eq_of_lin_eq_closure hS hu hU6 hx (hℓU i) fun v => by rw [h, hℓl i hi]
  have hℓ0 : ℓ 0 = 1 := (hℓuniq 0 (by norm_num) 1 (one_mem _) fun v => by
    rw [hR.lin_one, s0Mat_zero, one_mulVec]).symm
  have htN : t ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem fun q hq => by
    rw [← hS.shape.commute_of_mem (hR.Q_le_L hq), mul_inv_cancel_right]
    exact hq
  have htl : ∀ v, lin ψ t v = v := fun v => by
    rw [hR.lin_eq_iff htN, ← hS.shape.commute_of_mem (hR.Q_le_L (hR.ψ_mem v)),
      mul_inv_cancel_right]
  have hWN : ∀ x ∈ W, x ∈ normalizer (Q : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun q hq => by
      rw [hW.comm x hx q (hW.Q_le hq), mul_inv_cancel_right]
      exact hq
  have hWl : ∀ x ∈ W, ∀ v, lin ψ x v = v := fun x hx v => by
    rw [hR.lin_eq_iff (hWN x hx), hW.comm x hx _ (hW.Q_le (hR.ψ_mem v)), mul_inv_cancel_right]
  have hℓmul : ∀ i < 64, ∀ j < 64, ℓ i * ℓ j = ℓ (tabGet (mulTab .plus) i j) :=
    fun i hi j hj => hℓuniq _ (tab_lt .plus hi hj) _ (mul_mem (hℓU i) (hℓU j)) fun v => by
      rw [hR.lin_mul (hℓN i) (hℓN j), hℓl j hj, hℓl i hi, mulVec_mulVec, s0Mat_mul .plus hi hj]
  have hwords : ∀ i < 64, wordRows .plus (s0Words.getD i []) = s0Get .plus i := by
    have h := wordsCheck_spec
    simp only [wordsCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    exact h
  have hℓrep : ∀ i < 64, Rep Φ (ℓ i) (toMat4 (liftTab.getD i #[])) := by
    intro i hi
    have hlt : liftTab.getD i #[] = prod4 .plus (s0Words.getD i []) := by
      simp [liftTab, Array.getD_eq_getD_getElem?, hi]
    rw [hlt, toMat4_prod4]
    have hq := mul_inv_mem_Q_of_lin_eq hS (hℓP i) (hR.wordElt_mem (s0Words.getD i []))
      fun v => by rw [hℓl i hi, lin_wordElt_eq hR, hwords i hi, s0Mat]
    have h1 := Coord4.rep_mul (hΦ.rep_of_mem_A hL.comm (hL.Q_le hq))
      (hrepW (s0Words.getD i []))
    rwa [one_mul, inv_mul_cancel_right] at h1
  have hD : T0Data hR W t Φ ℓ := ⟨hΦ, hinv, hW.t_not_mem, hS.shape.mul_self, hWN, hWl, htN, htl,
    hℓN, hℓl, hℓmul, fun i => hS.shape.commute_of_mem (hR.P_le_L (hℓP i)), hℓrep⟩
  have haQ : a ∈ Q := hR.a_eq ▸ hR.ψ_mem _
  have hat : a * t = t * a := hS.shape.commute_of_mem (hR.Q_le_L haQ)
  have ha2 : a * a = 1 := hR.Q_mul_self haQ
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have ha1 : a ≠ 1 := fun h => by
    rw [hR.a_eq, ← hR.ψ_zero] at h
    have := congrFun (hR.ψ_inj h) 0
    simp at this
  have haU : ∀ z ∈ U, a * z = z * a := fun z hz => by
    have h := a_central hS hu hz
    calc a * z = z * (z⁻¹ * a * z) := by group
      _ = z * a := by
        rw [show z⁻¹ * a * z = a by
          calc z⁻¹ * a * z = z⁻¹ * (z * a * z⁻¹) * z := by rw [h]
            _ = a := by group]
  have hacT : ∀ g ∈ U ⊔ zpowers t, g * a = a * g := by
    intro g hg
    obtain ⟨z, hz, e | e⟩ := (hS.shape.mem_sup_iff hR.U_le_L).1 hg <;> rw [e]
    · exact (haU z hz).symm
    · rw [mul_assoc, ← hat, ← mul_assoc, ← haU z hz, mul_assoc]
  have hQn : ∀ y ∈ U ⊔ zpowers t, ∀ g ∈ Q, y * g * y⁻¹ ∈ Q := by
    intro y hy g hg
    have hgt : g * t = t * g := hS.shape.commute_of_mem (hR.Q_le_L hg)
    obtain ⟨z, hz, e | e⟩ := (hS.shape.mem_sup_iff hR.U_le_L).1 hy <;> rw [e]
    · exact (mem_normalizer_iff.1 (hR.P_le_normalizer (hR.U_le_P hz)) g).1 hg
    · rw [show z * t * g * (z * t)⁻¹ = z * (t * g * t⁻¹) * z⁻¹ by group, ← hgt,
        mul_inv_cancel_right]
      exact (mem_normalizer_iff.1 (hR.P_le_normalizer (hR.U_le_P hz)) g).1 hg
  have hKL : ∀ x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G), x ∈ L ⊔ zpowers t →
      x ∈ U ⊔ zpowers t := fun x hxN hxK => mem_TH_of_mem_K hK hR.U_le_L hNL hxK hxN
  have hTL : U ⊔ zpowers t ≤ L ⊔ zpowers t := sup_le_sup_right hR.U_le_L _
  have haK : ∀ x ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G),
      x ∈ centralizer ({t} : Set G) → x * a * x⁻¹ = a := by
    intro x hxN hxC
    have hxL := hK.le_normalizer hxC
    have hUU : ∀ y ∈ U, x * y * x⁻¹ ∈ U := fun y hy => by
      have h1 : x * y * x⁻¹ ∈ U ⊔ zpowers t := (mem_normalizer_iff.1 hxN y).1 (mem_sup_left hy)
      have h2 : x * y * x⁻¹ ∈ L := (mem_normalizer_iff.1 hxL y).1 (hR.U_le_L hy)
      obtain ⟨z, hz, e | e⟩ := mem_sup_zpowers_of_le hK hR.U_le_L h1
      · rw [e]; exact hz
      · exfalso
        apply hK.not_mem
        rw [e] at h2
        have := mul_mem (inv_mem (hR.U_le_L hz)) h2
        rwa [inv_mul_cancel_left] at this
    have hxU : x ∈ normalizer (U : Set G) := mem_normalizer_of_conj_mem hUU
    have hcen : ∀ y ∈ U, x * a * x⁻¹ * y = y * (x * a * x⁻¹) := by
      intro y hy
      have hy' : x⁻¹ * y * x ∈ U := by
        have := (mem_normalizer_iff.1 (inv_mem hxU) y).1 hy
        rwa [inv_inv] at this
      have hc := haU _ hy'
      calc x * a * x⁻¹ * y = x * (a * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * y * x) * a) * x⁻¹ := by rw [hc]
        _ = y * (x * a * x⁻¹) := by group
    rcases hR.center_U _ (hUU a (hR.Q_le_U haQ)) hcen with h1 | h1
    · exfalso
      apply ha1
      calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hdec : ∀ g ∈ U ⊔ zpowers t, ∃ (q : ℕ) (e : Bool) (s : ℕ), q < 64 ∧ s < 64 ∧
      g = muT Φ t ℓ (twoV q, e, s) := by
    intro g hg
    obtain ⟨y, hy, hxy⟩ := (hS.shape.mem_sup_iff hR.U_le_L).1 hg
    obtain ⟨s, hs, hys⟩ := hu.exists_s0 hR hy
    have hyq := mul_inv_mem_Q_of_lin_eq hS (hR.U_le_P hy) (hℓP s) fun v => by rw [hys, hℓl s hs]
    obtain ⟨r, hr⟩ := hR.mem_ψ _ hyq
    have hy' : y = Φ (toVec4 (twoV (vecBits r))) * ℓ s := by
      rw [hΦ.phi_two, hr]; group
    rcases hxy with hxy | hxy
    · exact ⟨vecBits r, false, s, vecBits_lt r, hs, by rw [hxy, hy']; simp [muT]⟩
    · refine ⟨vecBits r, true, s, vecBits_lt r, hs, ?_⟩
      rw [hxy, hy']
      simp only [muT, ite_true]
      rw [mul_assoc, hS.shape.commute_of_mem (hR.P_le_L (hℓP s)), ← mul_assoc]
  have hidx : ∀ k, (k = 3 ∨ k = 4 ∨ k = 5) → ∀ hk : k < 6,
      s0Get .plus (k + 1) = uRows .plus k := by
    have h := uIdxCheck_spec
    simp only [uIdxCheck, Bool.and_eq_true, beq_iff_eq] at h
    rintro k (rfl | rfl | rfl) _
    · exact h.1.1
    · exact h.1.2
    · exact h.2
  have hgens : ∀ y ∈ t0Gens, y.2.2 < 64 ∧ muT Φ t ℓ y ∈ closure ({ψ (Pi.single 0 1),
      ψ (Pi.single 1 1), ψ (Pi.single 2 1), u 3, u 4, u 5} : Set G) := by
    have hψj : ∀ j : Fin 6, muT Φ t ℓ (twoV (2 ^ (j : ℕ)), false, 0) = ψ (Pi.single j 1) := by
      intro j
      simp only [muT, Bool.false_eq_true, ite_false, mul_one, hℓ0]
      rw [← vecBits_single j, hΦ.phi_two]
    have huk : ∀ k : Fin 6, (k = 3 ∨ k = 4 ∨ k = 5) →
        muT Φ t ℓ (dig4 0, false, (k : ℕ) + 1) = u k := by
      intro k hk
      simp only [muT, Bool.false_eq_true, ite_false, mul_one, toVec4_dig4_zero, hΦ.zero,
        one_mul]
      refine (hℓuniq _ (by omega) _ (subset_closure ⟨k, rfl⟩) fun v => ?_).symm
      rw [hR.lin_eq_iff (hR.P_le_normalizer (hR.U_le_P (hu.u_mem k))), hu.u_act, s0Mat,
        hidx k (by rcases hk with rfl | rfl | rfl <;> simp) k.isLt]
    intro y hy
    simp only [t0Gens, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (twoV (2 ^ ((0 : Fin 6) : ℕ)), false, 0) ∈ _
      rw [hψj]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (twoV (2 ^ ((1 : Fin 6) : ℕ)), false, 0) ∈ _
      rw [hψj]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (twoV (2 ^ ((2 : Fin 6) : ℕ)), false, 0) ∈ _
      rw [hψj]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (dig4 0, false, ((3 : Fin 6) : ℕ) + 1) ∈ _
      rw [huk 3 (by decide)]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (dig4 0, false, ((4 : Fin 6) : ℕ) + 1) ∈ _
      rw [huk 4 (by decide)]
      exact subset_closure (by simp)
    · refine ⟨by norm_num, ?_⟩
      change muT Φ t ℓ (dig4 0, false, ((5 : Fin 6) : ℕ) + 1) ∈ _
      rw [huk 5 (by decide)]
      exact subset_closure (by simp)
  have hT0 : ∀ x ∈ U ⊔ zpowers t, (∀ y ∈ closure ({ψ (Pi.single 0 1), ψ (Pi.single 1 1),
      ψ (Pi.single 2 1), u 3, u 4, u 5} : Set G),
        Φ (Pi.single 0 1) * x * y = y * (Φ (Pi.single 0 1) * x)) → False := by
    intro x hx hcx
    obtain ⟨q, e, s, hq, hs, hxμ⟩ := hdec x hx
    have hn₁μ : muT Φ t ℓ (dig4 1, false, 0) = Φ (Pi.single 0 1) := by
      simp [muT, toVec4_dig4_one, hℓ0]
    have hZ : Φ (Pi.single 0 1) * x =
        muT Φ t ℓ (tmul (mulTab .plus) liftTab (dig4 1, false, 0) (twoV q, e, s)) := by
      rw [← hD.muT_mul _ _ (by norm_num) hs, hn₁μ, ← hxμ]
    have hc := t0Check_spec
    simp only [t0Check, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at hc
    obtain ⟨y, hy, hne⟩ := hc q hq e (by cases e <;> simp) s hs
    apply hne
    obtain ⟨hy64, hyQ⟩ := hgens y hy
    have hZ64 : (tmul (mulTab .plus) liftTab (dig4 1, false, 0) (twoV q, e, s)).2.2 < 64 :=
      tab_lt .plus (by norm_num) hs
    have hcomm := hcx _ hyQ
    rw [hZ, hD.muT_mul _ _ hZ64 hy64, hD.muT_mul _ _ hy64 hZ64] at hcomm
    exact hD.muT_inj (tab_lt .plus hZ64 hy64) (tab_lt .plus hy64 hZ64) (addV4_size _ _)
      (addV4_size _ _) (addV4_lt _ _) (addV4_lt _ _) hcomm
  set ν : Fin 6 → ZMod 4 := toVec4 (dig4 641) with hν
  have hn₁W : Φ ν ∈ W := hΦ.mem ν
  have hn₁sq : Φ ν * Φ ν = a := by rw [hΦ.sq, hν, red_dig4_641, hR.a_eq]
  have hn₁μ : muT Φ t ℓ (dig4 641, false, 0) = Φ ν := by simp [muT, hℓ0, hν]
  have haμ : muT Φ t ℓ (twoV 1, false, 0) = a := by
    rw [hR.a_eq]
    simp only [muT, Bool.false_eq_true, ite_false, mul_one, hℓ0]
    rw [show (1 : ℕ) = vecBits (Pi.single (0 : Fin 6) 1 : V6) by rw [vecBits_single]; rfl,
      hΦ.phi_two]
  have hn₁a : Φ ν * a = a * Φ ν := hW.comm _ hn₁W a (hW.Q_le haQ)
  have hcomm' : ∀ g ∈ U ⊔ zpowers t, Φ ν * g * (Φ ν)⁻¹ = g ∨ Φ ν * g * (Φ ν)⁻¹ = g * a := by
    intro g hg
    obtain ⟨q, e, s, hq, hs, rfl⟩ := hdec g hg
    have hc := commCheck_spec
    simp only [commCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hc
    have h := hc q hq e (by cases e <;> simp) s hs
    have e1 := hD.muT_mul (dig4 641, false, 0) (twoV q, e, s) (by norm_num) hs
    have e2 := hD.muT_mul (twoV q, e, s) (dig4 641, false, 0) hs (by norm_num)
    rw [hn₁μ] at e1 e2
    rcases h with h | h
    · left
      rw [show Φ ν * muT Φ t ℓ (twoV q, e, s) = muT Φ t ℓ (twoV q, e, s) * Φ ν by
        rw [e1, e2, h], mul_inv_cancel_right]
    · right
      have h64 : (tmul (mulTab .plus) liftTab (twoV q, e, s) (dig4 641, false, 0)).2.2 < 64 :=
        tab_lt .plus hs (by norm_num)
      have e3 := hD.muT_mul _ (twoV 1, false, 0) h64 (by norm_num)
      rw [haμ, ← e2, ← h] at e3
      rw [e1, ← e3]
      calc muT Φ t ℓ (twoV q, e, s) * Φ ν * a * (Φ ν)⁻¹ =
          muT Φ t ℓ (twoV q, e, s) * (Φ ν * a * (Φ ν)⁻¹) := by group
        _ = muT Φ t ℓ (twoV q, e, s) * a := by rw [hn₁a, mul_inv_cancel_right]
  have hn₁N : Φ ν ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun g hg => by
      rcases hcomm' g hg with h | h <;> rw [h]
      · exact hg
      · exact mul_mem hg (mem_sup_left (hR.Q_le_U haQ))
  have hn₁t : Φ ν * t * (Φ ν)⁻¹ = t * a := by
    have h1 : t * (Φ ν)⁻¹ * t⁻¹ = Φ ν := by rw [hinv _ (inv_mem hn₁W), inv_inv]
    calc Φ ν * t * (Φ ν)⁻¹ = Φ ν * (t * (Φ ν)⁻¹ * t⁻¹) * t := by group
      _ = t * a := by rw [h1, hn₁sq, hat]
  have hn₁e0 : Φ ν = Φ (Pi.single 0 1) * ψ (toVec 6 24) := by
    rw [hν, dig4_641, hΦ.add, ← hΦ.phi_two (toVec 6 24), vecBits_toVec (by norm_num)]
  have hn₁inv : (Φ ν)⁻¹ * t * Φ ν = t * a := by
    calc (Φ ν)⁻¹ * t * Φ ν = (Φ ν)⁻¹ * (t * Φ ν * t⁻¹) * t := by group
      _ = (Φ ν * Φ ν)⁻¹ * t := by rw [hinv _ hn₁W]; group
      _ = t * a := by rw [hn₁sq, hainv, hat]
  obtain ⟨n₃, hn₃N, hn₃t, hn₃sq, hn₃c⟩ := hn3
  set h := (Φ ν)⁻¹ * n₃ with hhdef
  have hn3e : n₃ = Φ ν * h := by rw [hhdef, mul_inv_cancel_left]
  have hhN : h ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) := mul_mem (inv_mem hn₁N) hn₃N
  have hht : h * t = t * h := by
    have h3' : n₃ * t = t * a * n₃ := by rw [← hn₃t]; group
    calc h * t = (Φ ν)⁻¹ * (n₃ * t) := by rw [hhdef, mul_assoc]
      _ = (Φ ν)⁻¹ * (t * a * n₃) := by rw [h3']
      _ = ((Φ ν)⁻¹ * t * Φ ν) * ((Φ ν)⁻¹ * a * Φ ν) * ((Φ ν)⁻¹ * n₃) := by group
      _ = t * a * a * h := by
        rw [hn₁inv, show (Φ ν)⁻¹ * a * Φ ν = a by rw [mul_assoc, ← hn₁a, inv_mul_cancel_left],
          ← hhdef]
      _ = t * h := by rw [mul_assoc t a a, ha2, mul_one]
  have hhC : h ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hht
  by_cases hhL : h ∈ L ⊔ zpowers t
  ·
    have hhT := hKL h hhN hhL
    refine hT0 (ψ (toVec 6 24) * h)
      (mul_mem (mem_sup_left (hR.Q_le_U (hR.ψ_mem _))) hhT) fun y hy => ?_
    have e : Φ (Pi.single 0 1) * (ψ (toVec 6 24) * h) = n₃ := by
      rw [← mul_assoc, ← hn₁e0, hn3e]
    rw [e]
    exact hn₃c y hy
  ·
    have haK' := haK h hhN hhC
    set y := Φ ν * h * (Φ ν)⁻¹ with hydef
    have hyN : y ∈ normalizer ((U ⊔ zpowers t : Subgroup G) : Set G) :=
      mul_mem (mul_mem hn₁N hhN) (inv_mem hn₁N)
    have hyt : y * t = t * y := by
      have hht' : h * t * h⁻¹ = t := by rw [hht, mul_inv_cancel_right]
      calc y * t = Φ ν * h * ((Φ ν)⁻¹ * t * Φ ν) * (Φ ν)⁻¹ := by rw [hydef]; group
        _ = Φ ν * h * (t * a) * (Φ ν)⁻¹ := by rw [hn₁inv]
        _ = Φ ν * (h * t * h⁻¹) * (h * a * h⁻¹) * h * (Φ ν)⁻¹ := by group
        _ = (Φ ν * t * (Φ ν)⁻¹) * (Φ ν * a * (Φ ν)⁻¹) * (Φ ν * h * (Φ ν)⁻¹) := by
          rw [hht', haK']; group
        _ = t * a * a * y := by rw [hn₁t, hn₁a, mul_inv_cancel_right, hydef]
        _ = t * y := by rw [mul_assoc t a a, ha2, mul_one]
    have hyC : y ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hyt
    have hyL : y ∉ L ⊔ zpowers t := fun hyL => hhL (hTL (by
      have hyT := hKL y hyN hyL
      have e : h = (Φ ν)⁻¹ * y * (Φ ν)⁻¹⁻¹ := by rw [hydef]; group
      rw [e]
      exact (mem_normalizer_iff.1 (inv_mem hn₁N) y).1 hyT))
    by_cases hhy : h⁻¹ * y ∈ L ⊔ zpowers t
    ·
      have hg := hKL _ (mul_mem (inv_mem hhN) hyN) hhy
      have hsq : h * h = n₃ * n₃ * (h⁻¹ * ((h⁻¹ * y) * a) * h)⁻¹ := by
        rw [hn3e, hydef, ← hn₁sq]; group; exact (_root_.zpow_two h).symm
      have hc : h⁻¹ * ((h⁻¹ * y) * a) * h ∈ U ⊔ zpowers t := by
        have := (mem_normalizer_iff.1 (inv_mem hhN) _).1
          (mul_mem hg (mem_sup_left (hR.Q_le_U haQ)))
        rwa [inv_inv] at this
      have hh2 : h * h ∈ U ⊔ zpowers t := by
        rw [hsq]
        exact mul_mem (mem_sup_left hn₃sq) (inv_mem hc)
      apply hhL
      have := mul_mem (h3 h hhC) (inv_mem (hTL hh2))
      rwa [show h ^ 3 * (h * h)⁻¹ = h by group] at this
    ·
      have hx2 := mem_of_relIndex_three (fun c hc x hx => hK.conj_mem_sup hc hx) hrel3 hhC hyC
        hhL hyL hhy
      have hx2T := hKL _ (mul_mem (mul_mem (inv_mem hhN) (inv_mem hhN)) hyN) hx2
      have hh3T := hKL _ (pow_mem hhN 3) (h3 h hhC)
      obtain ⟨y₀, hy₀, hy₀g⟩ := exists_inner_of_inv (T := U ⊔ zpowers t) ha2 hacT hcomm'
        (fun g hg => (mem_normalizer_iff.1 hhN g).1 hg)
        (fun g hg => by
          have := (mem_normalizer_iff.1 (inv_mem hhN) g).1 hg
          rwa [inv_inv] at this)
        haK' hh3T (mul_mem hh3T hx2T) (by rw [hydef]; group)
      have hhQ : h ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem fun g hg => by
        rcases hy₀g g (mem_sup_left (hR.Q_le_U hg)) with e | e <;> rw [e]
        · exact hQn y₀ hy₀ g hg
        · exact mul_mem (hQn y₀ hy₀ g hg) haQ
      exact hhL (hNQ h hhC (mem_normalizer_sup hhQ (mem_normalizer_zpowers hht)))

end CFSG.EvenSmallLie.OmegaEight.Chain
