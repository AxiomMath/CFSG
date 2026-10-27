module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2ChiefSp4

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.Quasithin.B42Sp4 (spM)

private theorem exists_covBy_of_lt_of_le {α : Type*} [PartialOrder α] [Finite α] {x y : α}
    (h : x < y) : ∃ z : α, x ⋖ z ∧ z ≤ y := by
  have hfin : (Set.Ioc x y).Finite := Set.toFinite _
  obtain ⟨z, hz, hmin⟩ := Set.Finite.exists_minimal hfin ⟨y, h, le_rfl⟩
  rw [Set.mem_Ioc] at hz
  refine ⟨z, ⟨hz.1, ?_⟩, hz.2⟩
  intro c hxc hcz
  have hcy : c ≤ y := le_of_lt (lt_of_lt_of_le hcz hz.2)
  have hcs : c ∈ Set.Ioc x y := ⟨hxc, hcy⟩
  exact not_le_of_gt hcz (hmin hcs (le_of_lt hcz))

private theorem covBy_cons {n : ℕ} {α : Type*} [LT α] {x : α} {Ws : Fin (n + 1) → α}
    (hxz : x ⋖ Ws 0) (hcov : ∀ i : Fin n, Ws i.castSucc ⋖ Ws i.succ) :
    ∀ i : Fin (n + 1), (Fin.cons (α := fun _ => α) x Ws) i.castSucc ⋖
      (Fin.cons (α := fun _ => α) x Ws) i.succ := by
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
    exact hxz
  | succ j =>
    simp only [Fin.castSucc_succ, Fin.cons_succ]
    exact hcov j

private theorem exists_chain_to_top {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) K V)
    (x : Subrepresentation ρ) :
    ∃ (r : ℕ) (Ws : Fin (r + 1) → Subrepresentation ρ),
      Ws 0 = x ∧ Ws (Fin.last r) = ⊤ ∧ ∀ i : Fin r, Ws i.castSucc ⋖ Ws i.succ := by
  have : Finite (Subrepresentation ρ) :=
    Finite.of_injective (Subrepresentation.toSubmodule (ρ := ρ))
      Subrepresentation.toSubmodule_injective
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    by_cases hx : x = ⊤
    · subst hx
      exact ⟨0, fun _ => ⊤, rfl, rfl, fun i => i.elim0⟩
    · have hlt : x < ⊤ := lt_of_le_of_ne le_top hx
      obtain ⟨z, hxz, -⟩ := exists_covBy_of_lt_of_le (y := ⊤) hlt
      obtain ⟨r, Ws, hW0, hWl, hWs⟩ := ih z hxz.1
      exact ⟨r + 1, Fin.cons x Ws, by rw [Fin.cons_zero],
        by rw [show Fin.last (r + 1) = (Fin.last r).succ from rfl, Fin.cons_succ, hWl],
        covBy_cons (by rw [hW0]; exact hxz) hWs⟩

private theorem exists_chain_through {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) K V)
    (S : Subrepresentation ρ) :
    ∀ x : Subrepresentation ρ, x ≤ S →
      ∃ (r : ℕ) (Ws : Fin (r + 1) → Subrepresentation ρ) (a : Fin (r + 1)),
        Ws 0 = x ∧ Ws (Fin.last r) = ⊤ ∧
        (∀ i : Fin r, Ws i.castSucc ⋖ Ws i.succ) ∧ Ws a = S := by
  have : Finite (Subrepresentation ρ) :=
    Finite.of_injective (Subrepresentation.toSubmodule (ρ := ρ))
      Subrepresentation.toSubmodule_injective
  intro x
  induction x using WellFoundedGT.induction with
  | ind x ih =>
    intro hxS
    by_cases hx : x = S
    · obtain ⟨r, Ws, h0, hl, hcov⟩ := exists_chain_to_top ρ x
      exact ⟨r, Ws, 0, h0, hl, hcov, by rw [h0, hx]⟩
    · have hxlt : x < S := lt_of_le_of_ne hxS hx
      obtain ⟨z, hxz, hzS⟩ := exists_covBy_of_lt_of_le hxlt
      obtain ⟨r, Ws, a, h0, hl, hcov, ha⟩ := ih z hxz.1 hzS
      exact ⟨r + 1, Fin.cons x Ws, a.succ, by rw [Fin.cons_zero],
        by rw [show Fin.last (r + 1) = (Fin.last r).succ from rfl, Fin.cons_succ, hl],
        covBy_cons (by rw [h0]; exact hxz) hcov, by rw [Fin.cons_succ, ha]⟩

private theorem exists_isCompositionSeries_through {K : Type} [Group K] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) K V)
    (S : Subrepresentation ρ) :
    ∃ (r : ℕ) (Vs : Fin (r + 1) → Subrepresentation ρ) (a : Fin (r + 1)),
      IsCompositionSeries r Vs ∧ Vs a = S := by
  obtain ⟨r, Ws, a, h0, hl, hcov, ha⟩ := exists_chain_through ρ S ⊥ bot_le
  exact ⟨r, Ws, a, ⟨h0, hl, hcov⟩, ha⟩

private theorem sum_factorCodim_lt_le {K : Type} [Group K] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V} {r : ℕ}
    (Vs : Fin (r + 1) → Subrepresentation ρ) (hmono : ∀ i : Fin r, Vs i.castSucc ≤ Vs i.succ)
    (h0 : Vs 0 = ⊥) (a : Fin (r + 1)) (A : Subgroup K) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < a.val), factorCodim Vs A i ≤
      finrank (ZMod 2) (Vs a).toSubmodule -
        finrank (ZMod 2) ↥((Vs a).toSubmodule ⊓ fixSub ρ A) := by
  let c : Fin (r + 1) → ℕ := fun j =>
    finrank (ZMod 2) (Vs j).toSubmodule - finrank (ZMod 2) ↥((Vs j).toSubmodule ⊓ fixSub ρ A)
  have hstep : ∀ i : Fin r, c i.castSucc + factorCodim Vs A i ≤ c i.succ := by
    intro i
    have hle := hmono i
    have e1 := finrank_factor_add hle
    have e2 := finrank_inf_fixSub_le A hle
    have e3 : finrank (ZMod 2) ↥((Vs i.castSucc).toSubmodule ⊓ fixSub ρ A) ≤
        finrank (ZMod 2) (Vs i.castSucc).toSubmodule := Submodule.finrank_mono inf_le_left
    have e4 : finrank (ZMod 2) ↥((Vs i.succ).toSubmodule ⊓ fixSub ρ A) ≤
        finrank (ZMod 2) (Vs i.succ).toSubmodule := Submodule.finrank_mono inf_le_left
    have e5 : finrank (ZMod 2) ↥(fixSub (factorRep (Vs i.castSucc) (Vs i.succ)) A) ≤
        finrank (ZMod 2) ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) :=
      Submodule.finrank_le _
    unfold factorCodim
    simp only [c]
    omega
  have hc0 : c 0 = 0 := by
    have hb : (Vs 0).toSubmodule = ⊥ := by rw [h0]; rfl
    have key : ∀ S : Submodule (ZMod 2) V, S = ⊥ →
        finrank (ZMod 2) ↥S - finrank (ZMod 2) ↥(S ⊓ fixSub ρ A) = 0 := by
      rintro S rfl
      simp
    exact key _ hb
  have key : ∀ m (hm : m ≤ r),
      ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < m), factorCodim Vs A i + c 0 ≤
        c ⟨m, Nat.lt_succ_of_le hm⟩ := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hempty : Finset.univ.filter (fun i : Fin r => i.val < 0) = ∅ := by
        ext i; simp
      rw [hempty, Finset.sum_empty, zero_add]
      have h0eq : (⟨0, Nat.lt_succ_of_le hm⟩ : Fin (r + 1)) = 0 := Fin.ext rfl
      rw [h0eq, hc0]
    | succ m ih =>
      intro hm
      have hmr : m < r := Nat.lt_of_succ_le hm
      have ih' := ih (Nat.le_of_succ_le hm)
      have hfilter : Finset.univ.filter (fun i : Fin r => i.val < m + 1) =
          insert ⟨m, hmr⟩ (Finset.univ.filter (fun i : Fin r => i.val < m)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (h | h)
          · rw [h]; exact Nat.lt_succ_self m
          · exact Nat.lt_succ_of_lt h
      have hnot : ⟨m, hmr⟩ ∉ Finset.univ.filter (fun i : Fin r => i.val < m) := by simp
      rw [hfilter, Finset.sum_insert hnot]
      have hcast : Fin.castSucc (⟨m, hmr⟩ : Fin r) =
          (⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩ : Fin (r + 1)) := Fin.ext rfl
      have hsucc : Fin.succ (⟨m, hmr⟩ : Fin r) =
          (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (r + 1)) := Fin.ext rfl
      have hs := hstep ⟨m, hmr⟩
      rw [hcast, hsucc] at hs
      rw [show factorCodim Vs A ⟨m, hmr⟩ +
            (∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < m), factorCodim Vs A i) + c 0 =
          (∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < m), factorCodim Vs A i) + c 0 +
            factorCodim Vs A ⟨m, hmr⟩ from by ring]
      exact le_trans (Nat.add_le_add_right ih' _) hs
  have hfin := key a.val (Nat.lt_succ_iff.mp a.isLt)
  rw [hc0, add_zero] at hfin
  have haeq : (⟨a.val, Nat.lt_succ_of_le (Nat.lt_succ_iff.mp a.isLt)⟩ : Fin (r + 1)) = a :=
    Fin.ext rfl
  rw [haeq] at hfin
  exact hfin

private theorem covBy_comp_of_factor_surj {K L : Type*} [Group K] [Group L] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] {ρK : Representation (ZMod 2) K V}
    {ρL : Representation (ZMod 2) L V} (α : L →* K) (hα : ∀ l : L, ρK (α l) = ρL l)
    {r : ℕ} {Ws : Fin (r + 1) → Subrepresentation ρK} {Vs : Fin (r + 1) → Subrepresentation ρL}
    {i : Fin r} (h : Ws i.castSucc ⋖ Ws i.succ)
    (hsurj : ∀ k : K, ∃ l : L, factorRep (Ws i.castSucc) (Ws i.succ) k =
      factorRep (Ws i.castSucc) (Ws i.succ) (α l))
    (hVs : ∀ j, (Vs j).toSubmodule = (Ws j).toSubmodule) :
    Vs i.castSucc ⋖ Vs i.succ := by
  refine ⟨?_, ?_⟩
  · change (Vs i.castSucc).toSubmodule < (Vs i.succ).toSubmodule
    rw [hVs i.castSucc, hVs i.succ]
    exact h.1
  · intro c hc1 hc2
    let cK : Subrepresentation ρK :=
      { toSubmodule := c.toSubmodule
        apply_mem_toSubmodule := fun k x hx => by
          have hxsucc : x ∈ (Ws i.succ).toSubmodule := by
            have hle : c.toSubmodule ≤ (Vs i.succ).toSubmodule := hc2.le
            rw [hVs i.succ] at hle
            exact hle hx
          obtain ⟨l, hkl⟩ := hsurj k
          have hdiff : ρK k x - ρK (α l) x ∈ (Ws i.castSucc).toSubmodule := by
            have hcong := LinearMap.congr_fun hkl
              (Submodule.Quotient.mk (⟨x, hxsucc⟩ : ↥(Ws i.succ).toSubmodule))
            rw [factorRep_mk, factorRep_mk] at hcong
            have hmem := (Submodule.Quotient.eq
              (factorSub (Ws i.castSucc) (Ws i.succ))).mp hcong
            have hvalk : (((Ws i.succ).toRepresentation k) ⟨x, hxsucc⟩ : V) = ρK k x :=
              congrArg Subtype.val ((Subrepresentation.toRepresentation_apply_mk
                (hv := hxsucc)
                (hw := (Ws i.succ).apply_mem_toSubmodule k hxsucc)).mpr rfl)
            have hvall : (((Ws i.succ).toRepresentation (α l)) ⟨x, hxsucc⟩ : V) =
                ρK (α l) x :=
              congrArg Subtype.val ((Subrepresentation.toRepresentation_apply_mk
                (hv := hxsucc)
                (hw := (Ws i.succ).apply_mem_toSubmodule (α l) hxsucc)).mpr rfl)
            have hsub := Submodule.mem_comap.mp hmem
            simp only [map_sub, Submodule.subtype_apply] at hsub
            rw [hvalk, hvall] at hsub
            exact hsub
          have hleft : ρK (α l) x ∈ c.toSubmodule := by
            rw [hα l]
            exact c.apply_mem_toSubmodule l hx
          have hle_ic : (Ws i.castSucc).toSubmodule ≤ c.toSubmodule := by
            rw [← hVs i.castSucc]
            exact hc1.le
          rw [← sub_add_cancel (ρK k x) (ρK (α l) x)]
          exact c.toSubmodule.add_mem (hle_ic hdiff) hleft }
    have hc1' : Ws i.castSucc < cK := by
      change (Ws i.castSucc).toSubmodule < c.toSubmodule
      rw [← hVs i.castSucc]
      exact hc1
    have hc2' : cK < Ws i.succ := by
      change c.toSubmodule < (Ws i.succ).toSubmodule
      rw [← hVs i.succ]
      exact hc2
    exact (h.2 hc1') hc2'

theorem exists_series_natural_factor_sp4 {G : Type} [Group G]
    [Finite G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) (L B : Subgroup G) {F : Type} [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* StatedSp 2 F)
    (hperf : commutator ↥L = ⊤) (hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L))
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hinner : ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l) {U : Submodule (ZMod 2) W}
    (hUL : commOn ρ L ⊤ ≤ U) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U)
    (hbest : IsBestOffenderOn ρ B U)
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u))
    (hnt : ¬ B ≤ cenOn ρ B U) :
    ∃ (r : ℕ) (Vs : Fin (r + 1) → Subrepresentation (ρ.comp L.subtype)) (i₀ : Fin r)
      (α : MulAut (StatedSp 2 F))
      (φ : ((Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)) ≃+
        (Fin 2 ⊕ Fin 2 → F)),
      IsCompositionSeries r Vs ∧
      (∀ i : Fin r, i ≠ i₀ → ∀ l : ↥L, factorRep (Vs i.castSucc) (Vs i.succ) l = 1) ∧
      ∀ (g : StatedSp 2 F)
        (x : (Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)),
        φ (factorRep (Vs i₀.castSucc) (Vs i₀.succ) (e.symm g) x) = (spM (α g)).mulVec (φ x) := by
  classical
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hZsub : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 :=
    pow_three_eq_one_of_central_sp4 (K := G) e
  have hZcenter : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 := by
    intro z hz
    have hzc : ∀ k ∈ L, k * (z : G) = (z : G) * k := by
      intro k hk
      have h1 := Subgroup.mem_center_iff.mp hz ⟨k, hk⟩
      exact congrArg Subtype.val h1
    have h2 := hZsub (z : G) z.2 hzc
    exact Subtype.ext (by simpa using h2)
  obtain ⟨lB, hlB⟩ := exists_lift_hom hB2 hBc hZsub hinner
  obtain ⟨π, hπ⟩ := exists_split_hom lB hlB
  have hLsub : ∀ l : ↥L, π (l, 1) = (l : G) := fun l => by rw [hπ]; simp
  have hπinl : ∀ l : ↥L, (ρ.comp π) (MonoidHom.inl ↥L ↥B l) = ρ (l : G) := fun l => by
    show ρ (π (l, 1)) = ρ (l : G)
    rw [hLsub]
  have hgr : ∀ b : ↥B, π (lB b, b) = (b : G) := fun b => by rw [hπ]; simp
  have hπmem : ∀ k : ↥L × ↥B, π k ∈ L ⊔ B := by
    rintro ⟨l, b⟩
    rw [hπ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (lB b).2))) (Subgroup.mem_sup_right b.2)
  have hBp : IsPGroup 2 ↥B := fun b => ⟨1, by
    apply Subtype.ext
    show (b : G) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact hB2 b b.2⟩
  have hLp : CFSG.pCore 2 ↥L = ⊥ := pCore_two_eq_bot_of_quasisimple hperf hsimple hZcenter
  obtain ⟨e1, he1⟩ := exists_quotientEquiv_fst hBp hLp
  let ψ : (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) ≃* StatedSp 2 F := e1.trans e
  have hq : CFSG.Open.IsQuasisimple (StatedSp 2 F) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e.symm (by
      change commutator ↥L = ⊤ ∧ IsSimpleGroup (↥L ⧸ Subgroup.center ↥L)
      exact ⟨hperf, hsimple⟩)
  have hAea : CFSG.IsElementaryAbelian 2 (graphSub lB) := graphSub_isElementaryAbelian lB
    (fun b c => Subtype.ext (hBc b b.2 c c.2)) (fun b => Subtype.ext (hB2 b b.2))
  have hex : ∃ b : ↥B, lB b ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hnt fun b hb => mem_cenOn_of_lift_eq_one lB hlB hmove ⟨b, hb⟩ (hall ⟨b, hb⟩)
  have hnotle : ¬ graphSub lB ≤ CFSG.pCore 2 (↥L × ↥B) :=
    not_graphSub_le_pCore hBp hLp lB hex
  let SU : Subrepresentation (ρ.comp π) := ⟨U, fun g w hw => hinv (π g) (hπmem g) w hw⟩
  have : Finite ↥SU.toSubmodule := inferInstanceAs (Finite ↥U)
  obtain ⟨r, Ws, a, hWs, hWsa⟩ := exists_isCompositionSeries_through (ρ.comp π) SU
  have hntL : ∃ l : ↥L, (ρ.comp π) (MonoidHom.inl ↥L ↥B l) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hbB, hbnot⟩ := Set.not_subset.mp hnt
    obtain ⟨k, hk, u, hu, hne⟩ := hmove b hbB hbnot
    apply hne
    have hfix : ∀ l : ↥L, ρ (l : G) = 1 := fun l => by
      have h1 : ρ (π (l, 1)) = 1 := hcon l
      rwa [hLsub l] at h1
    have h1 : ρ k u = u := by
      simpa using LinearMap.congr_fun (hfix ⟨k, hk⟩) u
    have h2 : ρ k (ρ b u) = ρ b u := by
      simpa using LinearMap.congr_fun (hfix ⟨k, hk⟩) (ρ b u)
    calc ρ b (ρ k u) = ρ b u := by rw [h1]
      _ = ρ k (ρ b u) := h2.symm
  have hker : ∀ b : ↥B, ((1 : ↥L), b) ∈ CFSG.pCore 2 (↥L × ↥B) := fun b => by
    rw [pCore_prod_eq_ker_fst hBp hLp]
    exact MonoidHom.mem_ker.mpr rfl
  have hsurj : ∀ (i : Fin r) (k : ↥L × ↥B), ∃ l : ↥L,
      factorRep (Ws i.castSucc) (Ws i.succ) k =
        factorRep (Ws i.castSucc) (Ws i.succ) (MonoidHom.inl ↥L ↥B l) := by
    rintro i ⟨l, b⟩
    refine ⟨l, ?_⟩
    have hk : ((l, b) : ↥L × ↥B) = MonoidHom.inl ↥L ↥B l * ((1 : ↥L), b) := by
      ext <;> simp
    have h1 : factorRep (Ws i.castSucc) (Ws i.succ) ((1 : ↥L), b) = 1 :=
      LinearMap.ext fun x => factor_trivial_pCore (hWs.covBy i) (hker b) x
    rw [hk, map_mul, h1, mul_one]
  have hWsmono : Monotone Ws := Fin.monotone_iff_le_succ.mpr fun i => (hWs.covBy i).le
  have hUa : (Ws a).toSubmodule = U := by rw [hWsa]
  have hpt : ∀ (i : Fin r), a.val ≤ i.val → ∀ k : ↥L × ↥B,
      factorRep (Ws i.castSucc) (Ws i.succ) k = 1 := by
    intro i hai k
    obtain ⟨l, b⟩ := k
    have hk : ((l, b) : ↥L × ↥B) = MonoidHom.inl ↥L ↥B l * ((1 : ↥L), b) := by
      ext <;> simp
    have hle_i : (Ws a).toSubmodule ≤ (Ws i.castSucc).toSubmodule :=
      hWsmono (Fin.le_def.mpr hai)
    have h1 : factorRep (Ws i.castSucc) (Ws i.succ) (MonoidHom.inl ↥L ↥B l) = 1 := by
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
        (factorSub (Ws i.castSucc) (Ws i.succ)) x
      rw [factorRep_mk]
      apply (Submodule.Quotient.eq (factorSub (Ws i.castSucc) (Ws i.succ))).mpr
      have hcoe : (((Ws i.succ).toRepresentation (MonoidHom.inl ↥L ↥B l)) y : W) =
          ρ (l : G) (y : W) := by
        show (ρ.comp π) (MonoidHom.inl ↥L ↥B l) (y : W) = ρ (l : G) (y : W)
        rw [hπinl]
      change ((((Ws i.succ).toRepresentation (MonoidHom.inl ↥L ↥B l)) y : W) -
        (y : W)) ∈ (Ws i.castSucc).toSubmodule
      rw [hcoe]
      exact (hUL.trans (hUa ▸ hle_i))
        (Submodule.subset_span ⟨(l : G), l.2, (y : W), Submodule.mem_top, rfl⟩)
    have h2 : factorRep (Ws i.castSucc) (Ws i.succ) ((1 : ↥L), b) = 1 :=
      LinearMap.ext fun x => factor_trivial_pCore (hWs.covBy i) (hker b) x
    rw [hk, map_mul, h1, h2, mul_one]
  let φB : ↥B →* (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B) :=
    (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))).comp (lB.prod (MonoidHom.id ↥B))
  have hrange : φB.range = (graphSub lB).map
      (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))) :=
    (MonoidHom.map_range _ _).symm
  have hφ : ∀ b : ↥B, φB b = 1 → (b : G) ∈ cenOn ρ B U := by
    intro b hb
    have h1 : (lB b, b) ∈ CFSG.pCore 2 (↥L × ↥B) := (QuotientGroup.eq_one_iff _).mp hb
    rw [pCore_prod_eq_ker_fst hBp hLp] at h1
    exact mem_cenOn_of_lift_eq_one lB hlB hmove b (MonoidHom.mem_ker.mp h1)
  have hlog := finrank_sub_le_log_card_range hbest φB hφ
  have hfixU : (Ws a).toSubmodule ⊓ fixSub (ρ.comp π) (graphSub lB) = fixOn ρ B U := by
    have hmap : (fixSub SU.toRepresentation (graphSub lB)).map SU.toSubmodule.subtype =
        SU.toSubmodule ⊓ fixSub (ρ.comp π) (graphSub lB) := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.2, ?_⟩
        intro a ha
        exact congrArg Subtype.val ((mem_fixSub.mp hx) a ha)
      · rintro ⟨hw, hfix⟩
        exact ⟨⟨w, hw⟩, mem_fixSub.mpr fun a ha => Subtype.ext (hfix a ha), rfl⟩
    have hWsa' : (Ws a).toSubmodule = SU.toSubmodule := by rw [hWsa]
    rw [hWsa', ← hmap]
    exact map_subtype_fixSub_graph lB π hgr SU
  have hsum : ∑ i ∈ nontrivialFactors Ws, factorCodim Ws (graphSub lB) i ≤
      Nat.log 2 (Nat.card ((graphSub lB).map
        (QuotientGroup.mk' (CFSG.pCore 2 (↥L × ↥B))))) := by
    have hsub : nontrivialFactors Ws ⊆
        Finset.univ.filter (fun i : Fin r => i.val < a.val) := by
      intro i hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hlt
      push Not at hlt
      obtain ⟨k, hk⟩ := mem_nontrivialFactors.mp hi
      exact hk (hpt i hlt k)
    refine (Finset.sum_le_sum_of_subset hsub).trans ?_
    refine (sum_factorCodim_lt_le Ws (fun i => (hWs.covBy i).le) hWs.zero a
      (graphSub lB)).trans ?_
    rw [hfixU, hUa, ← hrange]
    exact hlog
  obtain ⟨hcard, hNat⟩ := chief_factors_sp4 hn hF hq ψ hWs (graphSub lB) hnotle hsum
  obtain ⟨i₀, l₀, hl₀⟩ := exists_nontriv_series_factor (MonoidHom.inl ↥L ↥B) hperf hWs hntL
  have hi₀ : i₀ ∈ nontrivialFactors Ws :=
    mem_nontrivialFactors.mpr ⟨MonoidHom.inl ↥L ↥B l₀, hl₀⟩
  have hsingle : nontrivialFactors Ws = {i₀} := by
    refine (Finset.eq_singleton_iff_unique_mem).mpr ⟨hi₀, ?_⟩
    intro j hj
    exact ((Finset.card_le_one.mp hcard) i₀ hi₀ j hj).symm
  have htrivK : ∀ i : Fin r, i ≠ i₀ → ∀ k : ↥L × ↥B,
      factorRep (Ws i.castSucc) (Ws i.succ) k = 1 := by
    intro i hi k
    by_contra hk
    have himem : i ∈ nontrivialFactors Ws := mem_nontrivialFactors.mpr ⟨k, hk⟩
    rw [hsingle, Finset.mem_singleton] at himem
    exact hi himem
  let Vs : Fin (r + 1) → Subrepresentation (ρ.comp L.subtype) := fun i =>
    ⟨(Ws i).toSubmodule, fun l w hw => by
      have h1 := (Ws i).apply_mem_toSubmodule (MonoidHom.inl ↥L ↥B l) hw
      rw [hπinl l] at h1
      exact h1⟩
  have hVs0 : Vs 0 = ⊥ := by
    refine Subrepresentation.toSubmodule_injective ?_
    change (Ws 0).toSubmodule = (⊥ : Subrepresentation (ρ.comp L.subtype)).toSubmodule
    rw [hWs.zero]
    rfl
  have hVsLast : Vs (Fin.last r) = ⊤ := by
    refine Subrepresentation.toSubmodule_injective ?_
    change (Ws (Fin.last r)).toSubmodule =
      (⊤ : Subrepresentation (ρ.comp L.subtype)).toSubmodule
    rw [hWs.last]
    rfl
  have hVsCov : ∀ i : Fin r, Vs i.castSucc ⋖ Vs i.succ := fun i =>
    covBy_comp_of_factor_surj (α := MonoidHom.inl ↥L ↥B) (hα := hπinl) (Vs := Vs)
      (h := hWs.covBy i) (hsurj := hsurj i) (hVs := fun _ => rfl)
  have hfactor : ∀ (i : Fin r) (l : ↥L),
      factorRep (Vs i.castSucc) (Vs i.succ) l =
        factorRep (Ws i.castSucc) (Ws i.succ) (MonoidHom.inl ↥L ↥B l) := by
    intro i l
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
      (factorSub (Vs i.castSucc) (Vs i.succ)) x
    rw [factorRep_mk]
    change Submodule.Quotient.mk (((Vs i.succ).toRepresentation l) y) =
      Submodule.Quotient.mk (((Ws i.succ).toRepresentation (MonoidHom.inl ↥L ↥B l)) y)
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    show ρ (l : G) (y : W) = ρ (π (l, 1)) (y : W)
    rw [hLsub]
  have hcomp : IsCompositionSeries r Vs := ⟨hVs0, hVsLast, hVsCov⟩
  have htriv : ∀ i : Fin r, i ≠ i₀ → ∀ l : ↥L,
      factorRep (Vs i.castSucc) (Vs i.succ) l = 1 := by
    intro i hi l
    rw [hfactor i l]
    exact htrivK i hi (MonoidHom.inl ↥L ↥B l)
  obtain ⟨α, φ, hφ₀⟩ := hNat i₀ hi₀
  refine ⟨r, Vs, i₀, α, φ, hcomp, htriv, ?_⟩
  intro g x
  have hpsi : ψ (MonoidHom.inl ↥L ↥B (e.symm g) :
      (↥L × ↥B) ⧸ CFSG.pCore 2 (↥L × ↥B)) = g := by
    show e (e1 (QuotientGroup.mk (MonoidHom.inl ↥L ↥B (e.symm g)))) = g
    rw [he1]
    simp
  rw [hfactor i₀ (e.symm g)]
  have hg := hφ₀ (MonoidHom.inl ↥L ↥B (e.symm g)) x
  rw [hpsi] at hg
  exact hg

end CFSG.LocalAnalysis.RankThreeUC.S15

end
