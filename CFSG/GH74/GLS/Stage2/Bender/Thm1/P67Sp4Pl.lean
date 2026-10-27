module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4A

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.Stage2.OddAut

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

variable {K : Type} [Field K]

theorem fixSp_inf_range_eq_bot {x : StatedSp 2 K} {m : ℕ} (hx : x ^ m = 1) (hm : (m : K) ≠ 0)
    {w u : Fin 2 ⊕ Fin 2 → K} (hu : act x u - u = w) (hw : w ∈ fixSp x) : w = 0 := by
  have hfix : ∀ i : ℕ, act (x ^ i) w = w := by
    intro i
    induction i with
    | zero => rw [pow_zero, act_one]
    | succ i ih => rw [pow_succ', act_mul, ih]; exact mem_fixSp.mp hw
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n, act (x ^ i) (act x u - u)) =
      act (x ^ n) u - u := by
    intro n
    induction n with
    | zero => simp [act_one]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, act_sub, ← act_mul, ← pow_succ]
      abel
  have h1 := hsum m
  rw [hx, act_one, sub_self, hu] at h1
  have h2 : (∑ i ∈ Finset.range m, act (x ^ i) w) = (m : K) • w := by
    simp only [hfix, Finset.sum_const, Finset.card_range]
    exact (Nat.cast_smul_eq_nsmul K m w).symm
  rw [h2] at h1
  exact (smul_eq_zero.mp h1).resolve_left hm


theorem inf_orth_ne_bot_of_finrank_one {Q : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hQ : Module.finrank K Q = 1) : Q ⊓ orth Q ≠ ⊥ := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hQ
  intro hbot
  have hvQ : (v : Fin 2 ⊕ Fin 2 → K) ∈ orth Q := by
    rw [mem_orth]
    intro u hu
    obtain ⟨c, hc⟩ := hv ⟨u, hu⟩
    have : (u : Fin 2 ⊕ Fin 2 → K) = c • (v : Fin 2 ⊕ Fin 2 → K) := (congrArg Subtype.val hc).symm
    rw [this, map_smul, LinearMap.smul_apply, spForm_self, smul_zero]
  have : (v : Fin 2 ⊕ Fin 2 → K) ∈ Q ⊓ orth Q := ⟨v.2, hvQ⟩
  rw [hbot, Submodule.mem_bot] at this
  exact hv0 (Subtype.ext this)

theorem fixSp_plane [Finite K] {x : StatedSp 2 K} {m : ℕ} (hx : x ^ m = 1) (hm : (m : K) ≠ 0)
    (hx1 : x ≠ 1) (hne : fixSp x ≠ ⊥) :
    Module.finrank K (fixSp x) = 2 ∧ fixSp x ⊓ orth (fixSp x) = ⊥ := by
  set P := fixSp x with hP
  set Rg : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    LinearMap.range (Matrix.mulVecLin (mx (x : GL _ K) - 1)) with hRg
  have hRgle : Rg ≤ orth P := by
    rintro _ ⟨u, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact act_sub_mem_orth_fixSp x u
  have hdim : Module.finrank K Rg + Module.finrank K P = 4 := by
    have := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (mx (x : GL _ K) - 1))
    have h4 : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card]; simp
    rw [h4] at this
    exact this
  have hdimo : Module.finrank K (orth P) = 4 - Module.finrank K P := by
    rw [finrank_orth]
  have hRgeq : Rg = orth P := by
    apply Submodule.eq_of_le_of_finrank_eq hRgle
    omega
  have hinf : P ⊓ orth P = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hwP, hwo⟩
    rw [← hRgeq] at hwo
    obtain ⟨u, hu⟩ := hwo
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec] at hu
    exact fixSp_inf_range_eq_bot hx hm hu hwP
  refine ⟨?_, hinf⟩
  have hne0 : Module.finrank K P ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.mp h0)
  have hne4 : Module.finrank K P ≠ 4 := by
    intro h4
    have htop : P = ⊤ := Submodule.eq_top_of_finrank_eq (by
      rw [h4, Module.finrank_fintype_fun_eq_card]; simp)
    apply hx1
    apply act_ext
    intro v
    rw [act_one]
    have hv : v ∈ P := by rw [htop]; exact Submodule.mem_top
    exact mem_fixSp.mp hv
  have hle4 : Module.finrank K P ≤ 4 := by
    have := Submodule.finrank_le P
    rw [Module.finrank_fintype_fun_eq_card] at this
    simpa using this
  have hne1 : Module.finrank K P ≠ 1 := by
    intro h1
    exact inf_orth_ne_bot_of_finrank_one h1 hinf
  have hne3 : Module.finrank K P ≠ 3 := by
    intro h3
    have h1 : Module.finrank K (orth P) = 1 := by omega
    have := inf_orth_ne_bot_of_finrank_one h1
    rw [orth_orth, inf_comm, hinf] at this
    exact this rfl
  omega


theorem eq_id_on_plane [Finite K] {Q : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hQ : Module.finrank K Q = 2) (hQo : Q ⊓ orth Q = ⊥) {y : StatedSp 2 K} {m : ℕ}
    (hy : y ^ m = 1) (hm : (m : K) ≠ 0) (hinv : ∀ v ∈ Q, act y v ∈ Q)
    {w0 : Fin 2 ⊕ Fin 2 → K} (hw0 : w0 ∈ Q) (hw00 : w0 ≠ 0) (hfix : act y w0 = w0) :
    ∀ v ∈ Q, act y v = v := by
  obtain ⟨u0, hu0Q, hu0⟩ : ∃ u ∈ Q, spForm 2 K w0 u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : w0 ∈ Q ⊓ orth Q :=
      ⟨hw0, mem_orth.mpr fun a ha => spForm_isRefl _ _ (hcon a ha)⟩
    rw [hQo, Submodule.mem_bot] at this
    exact hw00 this
  set c0 := spForm 2 K w0 u0 with hc0
  set u := c0⁻¹ • u0 with hu
  have huQ : u ∈ Q := Q.smul_mem _ hu0Q
  have hwu : spForm 2 K w0 u = 1 := by
    rw [hu, map_smul, smul_eq_mul, inv_mul_cancel₀ hu0]
  have hindep : LinearIndependent K ![w0, u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (spForm 2 K w0) hst
    simp only [map_add, map_smul, smul_eq_mul, spForm_self, mul_zero, zero_add, hwu, mul_one,
      map_zero] at h1
    refine ⟨?_, h1⟩
    rw [h1, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right hw00
  have hspan : Submodule.span K {w0, u} = Q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro a ha
      rcases ha with rfl | rfl
      · exact hw0
      · exact huQ
    · rw [hQ]
      have h1 := finrank_span_eq_card hindep
      have h2 : Set.range ![w0, u] = {w0, u} := by
        ext a; simp [or_comm, eq_comm]
      rw [h2] at h1
      simpa using h1
  obtain ⟨α, hα⟩ : ∃ α : K, act y u = u + α • w0 := by
    have hdQ : act y u - u ∈ Q := Q.sub_mem (hinv u huQ) huQ
    rw [← hspan] at hdQ
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hdQ
    have hB : spForm 2 K w0 (act y u - u) = 0 := by
      have h1 : spForm 2 K w0 (act y u) = spForm 2 K w0 u := by
        calc spForm 2 K w0 (act y u) = spForm 2 K (act y w0) (act y u) := by rw [hfix]
          _ = spForm 2 K w0 u := spForm_act y w0 u
      rw [map_sub, h1, sub_self]
    rw [← hαβ] at hB
    simp only [map_add, map_smul, smul_eq_mul, spForm_self, mul_zero, zero_add, hwu, mul_one] at hB
    refine ⟨α, ?_⟩
    rw [hB, zero_smul, add_zero] at hαβ
    rw [← sub_eq_iff_eq_add', ← hαβ]
  intro v hv
  rw [← hspan] at hv
  obtain ⟨c1, c2, rfl⟩ := Submodule.mem_span_pair.mp hv
  have hy1 : act y (c1 • w0 + c2 • u) = (c1 • w0 + c2 • u) + (c2 * α) • w0 := by
    rw [act_add, act_smul, act_smul, hfix, hα]
    module
  have hiter : ∀ k : ℕ, act (y ^ k) (c1 • w0 + c2 • u) =
      (c1 • w0 + c2 • u) + ((k : K) * (c2 * α)) • w0 := by
    intro k
    induction k with
    | zero => simp [act_one]
    | succ k ih =>
      rw [pow_succ', act_mul, ih, act_add, act_smul, hfix, hy1]
      push_cast
      module
  have h1 := hiter m
  rw [hy, act_one] at h1
  have h2 : ((m : K) * (c2 * α)) • w0 = 0 := by
    have := congrArg (fun t => t - (c1 • w0 + c2 • u)) h1
    simpa using this.symm
  have h3 : (m : K) * (c2 * α) = 0 := (smul_eq_zero.mp h2).resolve_right hw00
  have h4 : c2 * α = 0 := (mul_eq_zero.mp h3).resolve_left hm
  rw [hy1, h4, zero_smul, add_zero]


section HPlane

variable {P : Submodule K (Fin 2 ⊕ Fin 2 → K)}

theorem act_mem_of_mem_HP {h : StatedSp 2 K} (hh : h ∈ HP P) {p : Fin 2 ⊕ Fin 2 → K} (hp : p ∈ P) :
    act h p ∈ P := by
  rw [← orth_orth P, mem_orth]
  intro q hq
  have h1 : spForm 2 K q (act h p) = spForm 2 K q p := by
    calc spForm 2 K q (act h p) = spForm 2 K (act h q) (act h p) := by rw [mem_HP.mp hh q hq]
      _ = spForm 2 K q p := spForm_act h q p
  rw [h1]
  exact spForm_isRefl _ _ ((mem_orth.mp hq) p hp)

theorem act_mem_orth_of_fix {x : StatedSp 2 K} (hx : ∀ p ∈ P, act x p = p)
    {q : Fin 2 ⊕ Fin 2 → K} (hq : q ∈ orth P) : act x q ∈ orth P := by
  rw [mem_orth]
  intro p hp
  have h1 : spForm 2 K p (act x q) = spForm 2 K p q := by
    calc spForm 2 K p (act x q) = spForm 2 K (act x p) (act x q) := by rw [hx p hp]
      _ = spForm 2 K p q := spForm_act x p q
  rw [h1]
  exact (mem_orth.mp hq) p hp

theorem commute_of_fix_HP (hPo : P ⊓ orth P = ⊥) {x h : StatedSp 2 K} (hx : ∀ p ∈ P, act x p = p)
    (hh : h ∈ HP P) : h * x = x * h := by
  apply act_ext
  intro v
  have hv : v ∈ P ⊔ orth P := by rw [sup_orth_eq_top hPo]; exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
  have hxq : act x q ∈ orth P := act_mem_orth_of_fix hx hq
  have hhp : act h p ∈ P := act_mem_of_mem_HP hh hp
  have e1 : act (h * x) (p + q) = act h p + act x q := by
    rw [act_mul, act_add, hx p hp, act_add, mem_HP.mp hh _ hxq]
  have e2 : act (x * h) (p + q) = act h p + act x q := by
    rw [act_mul, act_add, mem_HP.mp hh q hq, act_add, hx _ hhp]
  rw [e1, e2]

theorem tvS_mem_HP {w : Fin 2 ⊕ Fin 2 → K} (hw : w ∈ P) (t : K) : tvS w t ∈ HP P := by
  intro v hv
  show mx ((tvS w t : StatedSp 2 K) : GL _ K) *ᵥ v = v
  rw [mx_tvS_mulVec]
  have : spForm 2 K v w = 0 := spForm_isRefl _ _ ((mem_orth.mp hv) w hw)
  rw [this, mul_zero, zero_smul, add_zero]

theorem cf_mem_HP [Finite K] (A : gsp 2 K) (σ : K ≃+* K) (hΦ : ∀ v ∈ P, semi A σ v ∈ P)
    {h : StatedSp 2 K} (hh : h ∈ HP P) : cf A σ h ∈ HP P := by
  intro v hv
  obtain ⟨v', hv', rfl⟩ := exists_semi_mem A σ (semi_mem_orth A σ hΦ) v hv
  show mx ((cf A σ h : StatedSp 2 K) : GL _ K) *ᵥ semi A σ v' = semi A σ v'
  rw [cf_mulVec_semi]
  show semi A σ (act h v') = semi A σ v'
  rw [mem_HP.mp hh v' hv']

end HPlane

theorem exists_scalar_of_forall_eigen {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (P : Submodule K (ι → K))
    (h : ∀ w ∈ P, w ≠ 0 → ∃ l : K, M *ᵥ w = l • w) : ∃ c : K, ∀ w ∈ P, M *ᵥ w = c • w := by
  by_cases hP : P = ⊥
  · exact ⟨0, fun w hw => by rw [hP, Submodule.mem_bot] at hw; subst hw; simp⟩
  obtain ⟨w0, hw0P, hw00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨c, hc⟩ := h w0 hw0P hw00
  refine ⟨c, fun w hw => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0; simp
  obtain ⟨l, hl⟩ := h w hw hw0
  by_cases hdep : ∃ a : K, w = a • w0
  · obtain ⟨a, rfl⟩ := hdep
    rw [Matrix.mulVec_smul, hc, smul_comm]
  · push Not at hdep
    obtain ⟨l', hl'⟩ := h (w + w0) (P.add_mem hw hw0P) (by
      intro h0
      apply hdep (-1)
      rw [neg_one_smul]
      exact eq_neg_of_add_eq_zero_left h0)
    rw [Matrix.mulVec_add, hl, hc] at hl'
    have h1 : (l - l') • w + (c - l') • w0 = 0 := by
      have : l • w + c • w0 = l' • (w + w0) := hl'
      rw [smul_add] at this
      rw [sub_smul, sub_smul]
      linear_combination (exp := 1) this
    have hl1 : l = l' := by
      by_contra hne
      have hne' : l - l' ≠ 0 := sub_ne_zero.mpr hne
      apply hdep (-((c - l') / (l - l')))
      have : w = (-((c - l') / (l - l'))) • w0 := by
        have h2 : (l - l') • w = -((c - l') • w0) := eq_neg_of_add_eq_zero_left h1
        calc w = (l - l')⁻¹ • ((l - l') • w) := by rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
          _ = (l - l')⁻¹ • (-((c - l') • w0)) := by rw [h2]
          _ = _ := by
            rw [smul_neg, smul_smul, ← neg_smul]
            congr 1
            field_simp
      exact this
    rw [hl1, sub_self, zero_smul, zero_add] at h1
    have hcl : c = l' := sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hw00)
    rw [hl, hl1, hcl]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
