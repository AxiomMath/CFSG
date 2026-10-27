module

public import CFSG.HardMathSupport.Timmesfeld.DFour.OrderThree
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.RankThree.OddD4Centralizer

variable {K : Type} [Field K]

theorem finrank_V8 : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem quadPlus_one_apply (c : Fin 1 ⊕ Fin 1 → K) :
    quadPlus 1 K c = c (Sum.inl 0) * c (Sum.inr 0) := by
  rw [quadPlus_apply, Fin.sum_univ_one]

theorem exists_singular_line_of_finrank_pos {Q : QuadraticForm K (Fin 4 ⊕ Fin 4 → K)}
    {S : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hS : 0 < finrank K S) (hSs : ∀ x ∈ S, Q x = 0) :
    ∃ L : Submodule K (Fin 4 ⊕ Fin 4 → K), L ∈ singularSubspaces Q 1 ∧ L ≤ S := by
  have hS0 : S ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hS
    exact lt_irrefl 0 hS
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  refine ⟨K ∙ v, ⟨finrank_span_singleton hv0, fun x hx => ?_⟩,
    (Submodule.span_singleton_le_iff_mem _ _).mpr hvS⟩
  exact hSs x ((Submodule.span_singleton_le_iff_mem _ _).mpr hvS hx)

section Main

set_option linter.unusedSectionVars false

variable [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
  {g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
  (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)) (hg3 : ∀ v, g (g (g v)) = v)
  (hd : finrank K (fixSp g) = 6)
include h2 h3 hg hg3 hd

theorem finrank_movSp_eq_two : finrank K (movSp g) = 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSp g) (movSp g)
  rw [fixSp_sup_movSp h3 hg3, fixSp_inf_movSp h3 hg3, finrank_top, finrank_bot, finrank_V8] at h
  omega

theorem exists_singular_line_le_fixSp :
    ∃ L : Submodule K (Fin 4 ⊕ Fin 4 → K), L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
      L ≤ fixSp g := by
  obtain ⟨hF4, hFs⟩ := flag_mem_singularSubspaces (K := K) (r := 4) (le_rfl : 4 ≤ 4)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSp g) (flag 4 K 4)
  have hle := Submodule.finrank_le (fixSp g ⊔ flag 4 K 4)
  rw [finrank_V8] at hle
  obtain ⟨L, hL, hLle⟩ := exists_singular_line_of_finrank_pos (S := fixSp g ⊓ flag 4 K 4)
    (by omega) fun x hx => hFs x hx.2
  exact ⟨L, hL, hLle.trans inf_le_left⟩

theorem exists_hyperbolic_pair {e : Fin 4 ⊕ Fin 4 → K} (heW : e ∈ movSp g) (he0 : e ≠ 0)
    (hQe : quadPlus 4 K e = 0) :
    ∃ f ∈ movSp g, quadPlus 4 K f = 0 ∧ polar (quadPlus 4 K) e f = 1 := by
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  obtain ⟨w, hwW, hc⟩ : ∃ w ∈ movSp g, polar (quadPlus 4 K) e w ≠ 0 := by
    by_contra hall
    push Not at hall
    apply he0
    refine hQ.1 e fun v => ?_
    rw [polarBilin_apply_apply]
    have e1 : v = fix3 g v + (v - fix3 g v) := by abel
    rw [e1, polar_add_right, hall _ (sub_fix3_mem h3 hg3 v), add_zero, polar_comm]
    exact polar_fixSp_movSp h3 hg3 hg (fix3_mem h3 hg3 v) heW
  set c := polar (quadPlus 4 K) e w with hcdef
  refine ⟨c⁻¹ • w - (quadPlus 4 K w * c⁻¹ ^ 2) • e,
    (movSp g).sub_mem ((movSp g).smul_mem _ hwW) ((movSp g).smul_mem _ heW), ?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add (quadPlus 4 K), QuadraticMap.map_smul,
      QuadraticMap.map_smul, hQe, polar_smul_left, polar_smul_right, polar_comm, ← hcdef]
    have hcc : c * c⁻¹ ^ 3 = c⁻¹ ^ 2 := by
      rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    linear_combination (-(quadPlus 4 K w)) * hcc
  · rw [polar_sub_right, polar_smul_right, polar_smul_right, ← hcdef, polar_self, hQe]
    simp [inv_mul_cancel₀ hc]

@[expose] noncomputable def hypEmb (e f : Fin 4 ⊕ Fin 4 → K) :
    (Fin 1 ⊕ Fin 1 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  (LinearMap.proj (Sum.inl 0)).smulRight e + (LinearMap.proj (Sum.inr 0)).smulRight f

omit h2 h3 hg hg3 hd in
theorem hypEmb_apply (e f : Fin 4 ⊕ Fin 4 → K) (c : Fin 1 ⊕ Fin 1 → K) :
    hypEmb e f c = c (Sum.inl 0) • e + c (Sum.inr 0) • f := by
  simp [hypEmb]

omit h2 h3 hg hg3 hd in
theorem quadPlus_hypEmb {e f : Fin 4 ⊕ Fin 4 → K} (hQe : quadPlus 4 K e = 0)
    (hQf : quadPlus 4 K f = 0) (hef : polar (quadPlus 4 K) e f = 1) (c : Fin 1 ⊕ Fin 1 → K) :
    quadPlus 4 K (hypEmb e f c) = quadPlus 1 K c := by
  rw [hypEmb_apply, QuadraticMap.map_add (quadPlus 4 K), QuadraticMap.map_smul,
    QuadraticMap.map_smul, hQe, hQf, polar_smul_left, polar_smul_right, hef, quadPlus_one_apply]
  ring

theorem range_hypEmb {e f : Fin 4 ⊕ Fin 4 → K} (heW : e ∈ movSp g) (hfW : f ∈ movSp g)
    (hQe : quadPlus 4 K e = 0) (hQf : quadPlus 4 K f = 0)
    (hef : polar (quadPlus 4 K) e f = 1) : LinearMap.range (hypEmb e f) = movSp g := by
  have hle : LinearMap.range (hypEmb e f) ≤ movSp g := by
    rintro _ ⟨c, rfl⟩
    rw [hypEmb_apply]
    exact (movSp g).add_mem ((movSp g).smul_mem _ heW) ((movSp g).smul_mem _ hfW)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearMap.finrank_range_of_inj (injective_of_linearIsometry
    (quadPlus_hypEmb hQe hQf hef)), finrank_movSp_eq_two h2 h3 hg hg3 hd,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem exists_singular_three_le_fixSp {e f : Fin 4 ⊕ Fin 4 → K} (heW : e ∈ movSp g)
    (he0 : e ≠ 0) (hfW : f ∈ movSp g) (hQe : quadPlus 4 K e = 0) (hQf : quadPlus 4 K f = 0)
    (hef : polar (quadPlus 4 K) e f = 1) :
    ∃ N : Submodule K (Fin 4 ⊕ Fin 4 → K), N ∈ singularSubspaces (quadPlus 4 K) 3 ∧
      N ≤ fixSp g := by
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  obtain ⟨hF4, hFs⟩ := flag_mem_singularSubspaces (K := K) (r := 4) (le_rfl : 4 ≤ 4)
  set e₀ : Fin 4 ⊕ Fin 4 → K := Pi.single (Sum.inl 0) 1 with he₀def
  have he₀F : e₀ ∈ flag 4 K 4 := Submodule.subset_span ⟨0, by simp, rfl⟩
  have he₀0 : e₀ ≠ 0 := fun h => by
    have := congrFun h (Sum.inl 0)
    simp [he₀def] at this
  obtain ⟨h, hh, hhe⟩ := (orthogonal_norm_shell_transitive hQ
    ⟨flag 4 K 2, (flag_mem_singularSubspaces (K := K) (r := 4) (by norm_num)).1,
      (flag_mem_singularSubspaces (K := K) (r := 4) (by norm_num)).2⟩).1 e₀ e he₀0 he0
    (by rw [hFs e₀ he₀F, hQe])
  have hhO : ∀ v, quadPlus 4 K (h v) = quadPlus 4 K v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (orthElementaryGroup_le _ hh)
  set M₁ := (flag 4 K 4).map (h : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) with hM₁
  have hM₁s : ∀ x ∈ M₁, quadPlus 4 K x = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [LinearEquiv.coe_coe, hhO]
    exact hFs y hy
  have hM₁d : finrank K M₁ = 4 := by
    rw [hM₁, LinearEquiv.finrank_map_eq, hF4]
  have heM₁ : e ∈ M₁ := ⟨e₀, he₀F, hhe⟩
  set φ := (polarBilin (quadPlus 4 K)).flip f with hφ
  have hφe : φ e = 1 := by
    rw [hφ, LinearMap.flip_apply, polarBilin_apply_apply, hef]
  have hker : finrank K (LinearMap.ker φ) = 7 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hr1 : finrank K (LinearMap.range φ) = 1 := by
      have hle := Submodule.finrank_le (LinearMap.range φ)
      rw [Module.finrank_self] at hle
      have hne : LinearMap.range φ ≠ ⊥ := fun h0 => by
        have : φ e ∈ LinearMap.range φ := LinearMap.mem_range_self φ e
        rw [h0, Submodule.mem_bot, hφe] at this
        exact one_ne_zero this
      have hpos : 0 < finrank K (LinearMap.range φ) :=
        Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
      omega
    rw [hr1, finrank_V8] at hrn
    omega
  set N := M₁ ⊓ LinearMap.ker φ with hN
  have hNs : ∀ x ∈ N, quadPlus 4 K x = 0 := fun x hx => hM₁s x hx.1
  have hNB : N ≤ fixSp g := by
    intro v hv
    have hve : polar (quadPlus 4 K) v e = 0 := polar_eq_zero_of_singular hM₁s hv.1 heM₁
    have hvf : polar (quadPlus 4 K) v f = 0 := by
      have : φ v = 0 := hv.2
      rw [hφ, LinearMap.flip_apply, polarBilin_apply_apply] at this
      exact this
    have hwW := sub_fix3_mem h3 hg3 v
    rw [← range_hypEmb h2 h3 hg hg3 hd heW hfW hQe hQf hef] at hwW
    obtain ⟨c, hc⟩ := hwW
    rw [hypEmb_apply] at hc
    have hPe : polar (quadPlus 4 K) (fix3 g v) e = 0 :=
      polar_fixSp_movSp h3 hg3 hg (fix3_mem h3 hg3 v) heW
    have hPf : polar (quadPlus 4 K) (fix3 g v) f = 0 :=
      polar_fixSp_movSp h3 hg3 hg (fix3_mem h3 hg3 v) hfW
    have hee : polar (quadPlus 4 K) e e = 0 := by rw [polar_self, hQe, smul_zero]
    have hff : polar (quadPlus 4 K) f f = 0 := by rw [polar_self, hQf, smul_zero]
    have hfe : polar (quadPlus 4 K) f e = 1 := by rw [polar_comm, hef]
    have h1 : polar (quadPlus 4 K) (v - fix3 g v) e = 0 := by
      rw [polar_sub_left, hve, hPe, sub_zero]
    have h2' : polar (quadPlus 4 K) (v - fix3 g v) f = 0 := by
      rw [polar_sub_left, hvf, hPf, sub_zero]
    rw [← hc, polar_add_left, polar_smul_left, polar_smul_left, hee, hfe] at h1
    rw [← hc, polar_add_left, polar_smul_left, polar_smul_left, hef, hff] at h2'
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at h1 h2'
    have hw0 : v - fix3 g v = 0 := by rw [← hc, h1, h2', zero_smul, zero_smul, add_zero]
    have : v = fix3 g v := sub_eq_zero.mp hw0
    rw [this]
    exact fix3_mem h3 hg3 v
  have hN3 : finrank K N = 3 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq M₁ (LinearMap.ker φ)
    rw [← hN] at h1
    have h2'' := Submodule.finrank_le (M₁ ⊔ LinearMap.ker φ)
    rw [finrank_V8] at h2''
    have hup := two_mul_finrank_le_fixSp h3 hg3 hg hQ hNB hNs
    rw [finrank_movSp_eq_two h2 h3 hg hg3 hd, finrank_V8] at hup
    rw [hM₁d, hker] at h1
    omega
  exact ⟨N, ⟨hN3, hNs⟩, hNB⟩

theorem exists_emb_fixSp {e f : Fin 4 ⊕ Fin 4 → K} (heW : e ∈ movSp g) (he0 : e ≠ 0)
    (hfW : f ∈ movSp g) (hQe : quadPlus 4 K e = 0) (hQf : quadPlus 4 K f = 0)
    (hef : polar (quadPlus 4 K) e f = 1) :
    ∃ ι : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      (∀ c, quadPlus 4 K (ι c) = quadPlus 3 K c) ∧ LinearMap.range ι = fixSp g := by
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  obtain ⟨N, ⟨hN3, hNs⟩, hNB⟩ := exists_singular_three_le_fixSp h2 h3 hg hg3 hd heW he0 hfW hQe
    hQf hef
  set QB := (quadPlus 4 K).comp (fixSp g).subtype with hQB
  have hpolB : ∀ x y : fixSp g, polar QB x y = polar (quadPlus 4 K) x y := fun x y => by
    simp only [polar, hQB, QuadraticMap.comp_apply, map_add, Submodule.subtype_apply]
  have hnd : (polarBilin QB).Nondegenerate := by
    refine nondegenerate_polarBilin_of_forall fun x hx => ?_
    apply Subtype.ext
    refine hQ.1 (x : Fin 4 ⊕ Fin 4 → K) fun v => ?_
    rw [polarBilin_apply_apply]
    have e1 : v = fix3 g v + (v - fix3 g v) := by abel
    rw [e1, polar_add_right, polar_fixSp_movSp h3 hg3 hg x.2 (sub_fix3_mem h3 hg3 v), add_zero]
    have := hx ⟨fix3 g v, fix3_mem h3 hg3 v⟩
    rw [hpolB] at this
    exact this
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType QB := by
    refine ⟨N.comap (fixSp g).subtype, ?_, fun x hx => ?_⟩
    · rw [(Submodule.comapSubtypeEquivOfLe hNB).finrank_eq, hN3, hd]
    · rw [hQB, QuadraticMap.comp_apply]
      exact hNs _ hx
  obtain ⟨φ⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hnd (n := 3)
    (by rw [hd]) hplus
  refine ⟨(fixSp g).subtype ∘ₗ φ.symm.toLinearEquiv.toLinearMap, fun c => ?_, ?_⟩
  · change QB (φ.symm c) = quadPlus 3 K c
    exact φ.symm.map_app c
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

theorem card_maximal_ne_two_mul_card_lines :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} ≠
      2 * Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} := by
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  have hB : finrank K (Fin 4 ⊕ Fin 4 → K) < finrank K (fixSp g) + 4 := by
    rw [finrank_V8, hd]
    norm_num
  have hA : ∀ x ∈ movSp g, inv2 h3 hg3 x = -x := fun x hx => inv2_of_movSp h3 hg3 hx
  have hBf : ∀ x ∈ fixSp g, inv2 h3 hg3 x = x := fun x hx => inv2_of_fixSp h3 hg3 hx
  have hAB : movSp g ⊔ fixSp g = ⊤ := movSp_sup_fixSp h3 hg3
  have hlines : Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
      Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ movSp g} +
        Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ fixSp g} := by
    rw [← card_fixed_lines h2 hA hBf hAB]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun L =>
      and_congr_right fun hL => map_eq_iff_map_inv2_eq h3 hg3 hg hQ hB h2 hL.2)
  have ha : ∀ S : Submodule K (Fin 4 ⊕ Fin 4 → K), S ≤ movSp g →
      (∀ x ∈ S, quadPlus 4 K x = 0) → finrank K S ≤ 1 := by
    intro S hS hSs
    have := two_mul_finrank_le_movSp h3 hg3 hg hQ hS hSs
    rw [finrank_V8, hd] at this
    omega
  have hb : ∀ S : Submodule K (Fin 4 ⊕ Fin 4 → K), S ≤ fixSp g →
      (∀ x ∈ S, quadPlus 4 K x = 0) → finrank K S ≤ 3 := by
    intro S hS hSs
    have := two_mul_finrank_le_fixSp h3 hg3 hg hQ hS hSs
    rw [finrank_V8, finrank_movSp_eq_two h2 h3 hg hg3 hd] at this
    omega
  have hmax : Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
      Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ movSp g} *
        Nat.card {N // N ∈ singularSubspaces (quadPlus 4 K) 3 ∧ N ≤ fixSp g} := by
    rw [← card_fixed_sum h2 hA hBf hAB (inv2_mem_orthogonalGroup h3 hg3 hg) ha hb]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun M =>
      and_congr_right fun hM => map_eq_iff_map_inv2_eq h3 hg3 hg hQ hB h2 hM.2)
  rw [hmax, hlines]
  by_cases hiso : ∃ e ∈ movSp g, e ≠ 0 ∧ quadPlus 4 K e = 0
  · obtain ⟨e, heW, he0, hQe⟩ := hiso
    obtain ⟨f, hfW, hQf, hef⟩ := exists_hyperbolic_pair h2 h3 hg hg3 hd heW he0 hQe
    have hιW := quadPlus_hypEmb hQe hQf hef
    have hx : Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ movSp g} = 2 := by
      rw [← range_hypEmb h2 h3 hg hg3 hd heW hfW hQe hQf hef, card_singular_le_range hιW 1,
        card_singular_one_one]
    obtain ⟨ι, hι, hιr⟩ := exists_emb_fixSp h2 h3 hg hg3 hd heW he0 hfW hQe hQf hef
    have hy : Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ fixSp g} =
        (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
      rw [← hιr, card_singular_le_range hι 1, card_singular_three_one]
    have hz : Nat.card {N // N ∈ singularSubspaces (quadPlus 4 K) 3 ∧ N ≤ fixSp g} =
        2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
      rw [← hιr, card_singular_le_range hι 3, card_singular_three_three]
    rw [hx, hy, hz]
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    intro hc
    have h1 : ((2 * (2 + (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1)) : ℕ) : ℤ) -
        ((2 * (2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1)) : ℕ) : ℤ) =
          4 + 2 * ((Nat.card K : ℤ) ^ 2 + 1) * ((Nat.card K : ℤ) ^ 2 - Nat.card K - 1) := by
      push_cast
      ring
    rw [hc, sub_self] at h1
    have hq' : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq
    nlinarith
  · push Not at hiso
    have hx : Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ movSp g} = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun L => ?_⟩
      obtain ⟨L, ⟨hL1, hLs⟩, hLW⟩ := L
      have hL0 : L ≠ ⊥ := fun h => by
        rw [h, finrank_bot] at hL1
        exact zero_ne_one hL1
      obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
      exact hiso v (hLW hvL) hv0 (hLs v hvL)
    obtain ⟨L, hL, hLB⟩ := exists_singular_line_le_fixSp h2 h3 hg hg3 hd
    have hy : 0 < Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L ≤ fixSp g} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨L, hL, hLB⟩⟩, inferInstance⟩
    rw [hx]
    omega

end Main

end CFSG.HardMathSupport.Timmesfeld.DFour
