module

public import CFSG.Assembly.E6FourCentRoots

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.E6FourCentChk

private def qvec (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℚ := fun i => (γ i : ℚ)

private noncomputable def dualLin (u : List ℤ) : (Fin Tag.E6.rank → ℚ) →ₗ[ℚ] ℚ :=
  ∑ i : Fin Tag.E6.rank, (u.getD (i : ℕ) 0 : ℚ) • LinearMap.proj i

private lemma dualLin_apply (u : List ℤ) (x : Fin Tag.E6.rank → ℚ) :
    dualLin u x = ∑ i : Fin Tag.E6.rank, x i * (u.getD (i : ℕ) 0 : ℚ) := by
  simp only [dualLin, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, mul_comm]

private lemma dualLin_single (u : List ℤ) (p : Fin Tag.E6.rank) :
    dualLin u (Pi.single p 1) = (u.getD (p : ℕ) 0 : ℚ) := by
  rw [dualLin_apply]
  rw [Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg hb, zero_mul]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

private lemma e6rank_eq : Tag.E6.rank = 6 := by decide

private lemma dualLin_ne_zero (u : List ℤ) (hlen : u.length = 6)
    (h : u.any (fun z => z != 0) = true) : dualLin u ≠ 0 := by
  intro hzero
  rw [List.any_eq_true] at h
  obtain ⟨z, hz, hz0⟩ := h
  obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
  have hi6 : i < 6 := by omega
  have hval : dualLin u (Pi.single ⟨i, hi6⟩ 1) = (u.getD i 0 : ℚ) := dualLin_single u _
  have hz' : dualLin u (Pi.single ⟨i, hi6⟩ 1) = 0 := by rw [hzero]; rfl
  rw [hval] at hz'
  have hui : u[i] = 0 := by
    have : u.getD i 0 = 0 := by exact_mod_cast hz'
    rwa [List.getD_eq_getElem _ _ hi] at this
  exact bne_iff_ne.mp hz0 (by rw [← hzi]; exact hui)

private lemma dualLin_ne_zero_of_minor (u v : List ℤ) (p q : Fin Tag.E6.rank)
    (h : u.getD (p : ℕ) 0 * v.getD (q : ℕ) 0 - u.getD (q : ℕ) 0 * v.getD (p : ℕ) 0 ≠ 0) :
    dualLin u ≠ 0 := by
  intro hzero
  have hp' : dualLin u (Pi.single p 1) = 0 := by rw [hzero]; rfl
  rw [dualLin_single] at hp'
  have hpu : u.getD (p : ℕ) 0 = 0 := by exact_mod_cast hp'
  have hq' : dualLin u (Pi.single q 1) = 0 := by rw [hzero]; rfl
  rw [dualLin_single] at hq'
  have hqu : u.getD (q : ℕ) 0 = 0 := by exact_mod_cast hq'
  exact h (by rw [hpu, hqu]; ring)

private lemma dualLin_qvec (u : List ℤ) {k : ℕ} (hk : k < 72) :
    dualLin u (qvec (e6RootVec k)) = (dotI (rt k) u : ℚ) := by
  rw [dualLin_apply]
  simp only [qvec]
  rw [rt_eq_ofFn hk, dotI_ofFn]
  push_cast
  rfl

private lemma mem_e6MaskRoots {c k : ℕ} (hk : k < 72) (h : c.testBit k = true) :
    e6RootVec k ∈ e6MaskRoots c := ⟨k, hk, h, rfl⟩

private lemma finrank_ker_dual {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (φ : V →ₗ[ℚ] ℚ) (hφ : φ ≠ 0) :
    Module.finrank ℚ (LinearMap.ker φ) + 1 = Module.finrank ℚ V := by
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [Module.Dual.range_eq_top_of_ne_zero hφ, finrank_top, Module.finrank_self] at h
  omega

private lemma finrank_ker_dual_six (φ : (Fin Tag.E6.rank → ℚ) →ₗ[ℚ] ℚ) (hφ : φ ≠ 0) :
    Module.finrank ℚ (LinearMap.ker φ) = 5 := by
  have h := finrank_ker_dual φ hφ
  have hV : Module.finrank ℚ (Fin Tag.E6.rank → ℚ) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, e6rank_eq]
  omega

private lemma finrank_ker_inf_add_one {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (φ ψ : V →ₗ[ℚ] ℚ)
    (hψ : ψ.domRestrict (LinearMap.ker φ) ≠ 0) :
    Module.finrank ℚ ↥(LinearMap.ker φ ⊓ LinearMap.ker ψ) + 1 =
      Module.finrank ℚ (LinearMap.ker φ) := by
  let ψ' := ψ.domRestrict (LinearMap.ker φ)
  have hker : LinearMap.ker ψ' = (LinearMap.ker ψ).comap (LinearMap.ker φ).subtype := by
    rw [LinearMap.ker_domRestrict]
  have hfin : Module.finrank ℚ (LinearMap.ker ψ') =
      Module.finrank ℚ ↥(LinearMap.ker φ ⊓ LinearMap.ker ψ) := by
    rw [hker, ← Submodule.finrank_map_subtype_eq (LinearMap.ker φ)
      ((LinearMap.ker ψ).comap (LinearMap.ker φ).subtype), Submodule.map_comap_subtype]
  have hrn : 1 + Module.finrank ℚ (LinearMap.ker ψ') = Module.finrank ℚ (LinearMap.ker φ) := by
    have h := LinearMap.finrank_range_add_finrank_ker ψ'
    rw [Module.Dual.range_eq_top_of_ne_zero hψ, finrank_top, Module.finrank_self] at h
    exact h
  rw [hfin] at hrn
  omega

private lemma linearIndependent_of_dual {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : Fin n → V) (f : Fin n → V →ₗ[ℚ] ℚ)
    (hdiag : ∀ i, f i (v i) ≠ 0) (hoff : ∀ i j, i ≠ j → f i (v j) = 0) :
    LinearIndependent ℚ v := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hi : ∑ j, a j * f i (v j) = 0 := by
    have := congrArg (f i) ha
    simpa [map_sum, map_smul, smul_eq_mul] using this
  have hsum : ∑ j, a j * f i (v j) = a i * f i (v i) := by
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [hoff i j (Ne.symm hj), mul_zero]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  rw [hsum] at hi
  exact (mul_eq_zero.mp hi).resolve_right (hdiag i)

private lemma le_compRank_of_dual {c n : ℕ} (g : Fin n → ℕ)
    (hg : ∀ i, g i < 72) (hmem : ∀ i, c.testBit (g i) = true) (d : Fin n → List ℤ)
    (hdual : ∀ i j, (i = j → dotI (rt (g i)) (d j) ≠ 0) ∧
      (i ≠ j → dotI (rt (g i)) (d j) = 0)) :
    n ≤ compRank (τ := Tag.E6) (e6MaskRoots c) := by
  let v : Fin n → (Fin Tag.E6.rank → ℚ) := fun i => qvec (e6RootVec (g i))
  have hli : LinearIndependent ℚ v := by
    apply linearIndependent_of_dual v (fun i => dualLin (d i))
    · intro i
      rw [dualLin_qvec (d i) (hg i)]
      exact_mod_cast (hdual i i).1 rfl
    · intro i j hij
      rw [dualLin_qvec (d i) (hg j)]
      exact_mod_cast (hdual j i).2 (Ne.symm hij)
  have hspan : Module.finrank ℚ (Submodule.span ℚ (Set.range v)) = n := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hle : Submodule.span ℚ (Set.range v) ≤
      Submodule.span ℚ (qvec '' e6MaskRoots c) := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨e6RootVec (g i), mem_e6MaskRoots (hg i) (hmem i), rfl⟩
  have hmono := Submodule.finrank_mono hle
  rw [hspan] at hmono
  exact hmono

private lemma compRank_le_of_ker {c : ℕ} (φ : (Fin Tag.E6.rank → ℚ) →ₗ[ℚ] ℚ)
    (hφ : φ ≠ 0)
    (hvan : ∀ k, k < 72 → c.testBit k = true → φ (qvec (e6RootVec k)) = 0) :
    compRank (τ := Tag.E6) (e6MaskRoots c) ≤ 5 := by
  have hle : Submodule.span ℚ (qvec '' e6MaskRoots c) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro x ⟨γ, hγ, rfl⟩
    obtain ⟨k, hk, hbit, heq⟩ := hγ
    rw [← heq]
    exact LinearMap.mem_ker.mpr (hvan k hk hbit)
  have hmono := Submodule.finrank_mono hle
  have hker := finrank_ker_dual_six φ hφ
  rw [hker] at hmono
  exact hmono

private lemma compRank_le_of_ker_inf {c : ℕ} (φ ψ : (Fin Tag.E6.rank → ℚ) →ₗ[ℚ] ℚ)
    (hφ : φ ≠ 0) (hψ : ψ.domRestrict (LinearMap.ker φ) ≠ 0)
    (hvan1 : ∀ k, k < 72 → c.testBit k = true → φ (qvec (e6RootVec k)) = 0)
    (hvan2 : ∀ k, k < 72 → c.testBit k = true → ψ (qvec (e6RootVec k)) = 0) :
    compRank (τ := Tag.E6) (e6MaskRoots c) ≤ 4 := by
  have hle : Submodule.span ℚ (qvec '' e6MaskRoots c) ≤
      LinearMap.ker φ ⊓ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro x ⟨γ, hγ, rfl⟩
    obtain ⟨k, hk, hbit, heq⟩ := hγ
    rw [← heq]
    exact Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (hvan1 k hk hbit),
      LinearMap.mem_ker.mpr (hvan2 k hk hbit)⟩
  have hmono := Submodule.finrank_mono hle
  have hker := finrank_ker_inf_add_one φ ψ hψ
  have hkerφ := finrank_ker_dual_six φ hφ
  rw [hkerφ] at hker
  have h4 : Module.finrank ℚ ↥(LinearMap.ker φ ⊓ LinearMap.ker ψ) = 4 := by
    omega
  rw [h4] at hmono
  exact hmono

private lemma e6MaskRoots_ncard (c : ℕ) : (e6MaskRoots c).ncard = popc c := by
  have hset : e6MaskRoots c =
      (↑(((Finset.range 72).filter (fun k => c.testBit k = true)).image e6RootVec) :
        Set (Fin Tag.E6.rank → ℤ)) := by
    ext γ
    constructor
    · rintro ⟨k, hk, hbit, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hbit⟩, rfl⟩)
    · intro hγ
      obtain ⟨k, hk, hflt⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hγ)
      rcases Finset.mem_filter.mp hk with ⟨hkrange, hbit⟩
      exact ⟨k, Finset.mem_range.mp hkrange, hbit, hflt⟩
  have hinj : Set.InjOn e6RootVec
      (↑((Finset.range 72).filter (fun k => c.testBit k = true)) : Set ℕ) := by
    intro k hk k' hk' heq
    exact e6RootVec_injOn (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hk').1) heq
  have hcard : ((Finset.range 72).filter (fun k => c.testBit k = true)).card = popc c := by
    rw [popc_eq]
    rw [← List.toFinset_card_of_nodup
      (List.Nodup.filter (fun k => c.testBit k = true) List.nodup_range)]
    congr 1
    ext x
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_filter,
      Finset.mem_range, decide_eq_true_eq]
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hcard]

private lemma lt_of_testBit {c k : ℕ} (hc : c < 2 ^ 72) (h : c.testBit k = true) : k < 72 := by
  by_contra hk
  have hk' : 72 ≤ k := by omega
  have h1 : 2 ^ k ≤ c := Nat.ge_two_pow_of_testBit h
  have h2 : 2 ^ 72 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk'
  omega

private lemma dualOK_spec {gs ds : List (List ℤ)} (h : dualOK gs ds = true)
    {i j : ℕ} (hi : i < gs.length) (hj : j < ds.length) :
    (i = j → dotI (gs.getD i []) (ds.getD j []) ≠ 0) ∧
    (i ≠ j → dotI (gs.getD i []) (ds.getD j []) = 0) := by
  have h' := h
  simp only [dualOK] at h'
  have h1 : ((List.range ds.length).all fun j =>
      bif Nat.beq i j then dotI (gs.getD i []) (ds.getD j []) != 0
      else dotI (gs.getD i []) (ds.getD j []) == 0) = true :=
    (List.all_eq_true.mp h') i (List.mem_range.mpr hi)
  have h2 := (List.all_eq_true.mp h1) j (List.mem_range.mpr hj)
  constructor
  · intro hij
    have hbij : Nat.beq i j = true := by rw [Nat.beq_eq]; exact hij
    rw [hbij] at h2
    simp only [Bool.cond_true] at h2
    exact bne_iff_ne.mp h2
  · intro hij
    have hbij : Nat.beq i j = false := beq_eq_false_iff_ne.mpr hij
    rw [hbij] at h2
    simp only [Bool.cond_false] at h2
    exact beq_iff_eq.mp h2

private lemma a5Valid_facts {e : A5Cert} (h : a5Valid e = true) :
    Nat.testBit e.c e.g1 = true ∧ Nat.testBit e.c e.g2 = true ∧
    Nat.testBit e.c e.g3 = true ∧ Nat.testBit e.c e.g4 = true ∧
    Nat.testBit e.c e.g5 = true ∧
    dualOK [rt e.g1, rt e.g2, rt e.g3, rt e.g4, rt e.g5]
      [e.d1, e.d2, e.d3, e.d4, e.d5] = true ∧
    e.u.any (fun z => z != 0) = true ∧
    (rootsOf e.c).all (fun g => dotI g e.u == 0) = true := by
  have h' : _ := h
  simp only [a5Valid, Bool.and_eq_true, and_assoc] at h'
  obtain ⟨_, _, _, hg1, hg2, hg3, hg4, hg5, _, _, _, _, hdual, huany, hrs⟩ := h'
  exact ⟨hg1, hg2, hg3, hg4, hg5, hdual, huany, hrs⟩

private lemma d4Valid_facts {e : D4Cert} (h : d4Valid e = true) :
    Nat.testBit e.c e.g1 = true ∧ Nat.testBit e.c e.g2 = true ∧
    Nat.testBit e.c e.g3 = true ∧ Nat.testBit e.c e.g4 = true ∧
    dualOK [rt e.g1, rt e.g2, rt e.g3, rt e.g4] [e.d1, e.d2, e.d3, e.d4] = true ∧
    (rootsOf e.c).all (fun g => dotI g e.u1 == 0 && dotI g e.u2 == 0) = true ∧
    (e.u1.getD e.p 0 * e.u2.getD e.q 0 - e.u1.getD e.q 0 * e.u2.getD e.p 0) ≠ 0 := by
  have h' : _ := h
  simp only [d4Valid, Bool.and_eq_true, and_assoc] at h'
  obtain ⟨_, _, hg1, hg2, hg3, hg4, _, _, _, hdual, hru, hminor⟩ := h'
  exact ⟨hg1, hg2, hg3, hg4, hdual, hru, bne_iff_ne.mp hminor⟩

private lemma dotI_rt_eq_zero_of_all {c : ℕ} {u : List ℤ}
    (h : (rootsOf c).all (fun g => dotI g u == 0) = true)
    {k : ℕ} (hk : k < 72) (hbit : c.testBit k = true) : dotI (rt k) u = 0 := by
  have hmem : rt k ∈ rootsOf c := by
    rw [rootsOf]
    exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk, hbit⟩, rfl⟩
  exact beq_iff_eq.mp ((List.all_eq_true.mp h) (rt k) hmem)

private lemma dotI_rt_eq_zero_of_all2 {c : ℕ} {u v : List ℤ}
    (h : (rootsOf c).all (fun g => dotI g u == 0 && dotI g v == 0) = true)
    {k : ℕ} (hk : k < 72) (hbit : c.testBit k = true) :
    dotI (rt k) u = 0 ∧ dotI (rt k) v = 0 := by
  have hmem : rt k ∈ rootsOf c := by
    rw [rootsOf]
    exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk, hbit⟩, rfl⟩
  have hh := (List.all_eq_true.mp h) (rt k) hmem
  rw [Bool.and_eq_true] at hh
  exact ⟨beq_iff_eq.mp hh.1, beq_iff_eq.mp hh.2⟩

private lemma typedOK_extract {c : ℕ} (h : typedOK c c = true) :
    (popc c = 30 ∧ ∃ e ∈ a5Tab, e.c = c ∧ a5Valid e = true) ∨
    (popc c = 24 ∧ ∃ e ∈ d4Tab, e.c = c ∧ d4Valid e = true) := by
  have h' := h
  simp only [typedOK] at h'
  rw [Bool.and_eq_true] at h'
  rw [Nat.beq_eq] at h'
  have hrest := h'.2
  rw [Bool.or_eq_true] at hrest
  rcases hrest with h30 | h24
  · left
    rw [Bool.and_eq_true] at h30
    refine ⟨beq_iff_eq.mp h30.1, ?_⟩
    rw [List.any_eq_true] at h30
    obtain ⟨e, he, hval⟩ := h30.2
    rw [Bool.and_eq_true] at hval
    exact ⟨e, he, beq_iff_eq.mp hval.1, hval.2⟩
  · right
    rw [Bool.and_eq_true] at h24
    refine ⟨beq_iff_eq.mp h24.1, ?_⟩
    rw [List.any_eq_true] at h24
    obtain ⟨e, he, hval⟩ := h24.2
    rw [Bool.and_eq_true] at hval
    exact ⟨e, he, beq_iff_eq.mp hval.1, hval.2⟩

private theorem a5Tab_u_length : a5Tab.all (fun e => decide (e.u.length = 6)) = true := by
  decide +kernel

private theorem d4Tab_pq_bound : d4Tab.all (fun e => decide (e.p < 6 ∧ e.q < 6)) = true := by
  decide +kernel

theorem typedOK_popc {c : ℕ} (h : typedOK c c = true) : popc c = 30 ∨ popc c = 24 := by
  rcases typedOK_extract h with hA | hD
  · exact Or.inl hA.1
  · exact Or.inr hD.1

theorem e6Four_a5_rank_card {c : ℕ} (hc : c < 2 ^ 72) (hp : popc c = 30)
    (h : typedOK c c = true) :
    compRank (τ := Tag.E6) (e6MaskRoots c) = 5 ∧ (e6MaskRoots c).ncard = 30 := by
  have hcard : (e6MaskRoots c).ncard = popc c := e6MaskRoots_ncard c
  rw [hp] at hcard
  rcases typedOK_extract h with hA | hD
  · obtain ⟨_, e, he, hec, hval⟩ := hA
    obtain ⟨hg1, hg2, hg3, hg4, hg5, hdual, huany, hrs⟩ := a5Valid_facts hval
    have hlen : e.u.length = 6 := by
      have := (List.all_eq_true.mp a5Tab_u_length) e he
      exact of_decide_eq_true this
    have hφ : dualLin e.u ≠ 0 := dualLin_ne_zero e.u hlen huany
    have hrs' : (rootsOf c).all (fun g => dotI g e.u == 0) = true := by
      rw [← hec]; exact hrs
    have hvan : ∀ k, k < 72 → c.testBit k = true →
        dualLin e.u (qvec (e6RootVec k)) = 0 := by
      intro k hk hbit
      rw [dualLin_qvec e.u hk]
      exact_mod_cast (dotI_rt_eq_zero_of_all hrs' hk hbit)
    have hle : compRank (τ := Tag.E6) (e6MaskRoots c) ≤ 5 := compRank_le_of_ker _ hφ hvan
    have hgb : ∀ i : Fin 5, c.testBit (![e.g1, e.g2, e.g3, e.g4, e.g5] i) = true := by
      intro i
      fin_cases i
      · simpa [hec] using hg1
      · simpa [hec] using hg2
      · simpa [hec] using hg3
      · simpa [hec] using hg4
      · simpa [hec] using hg5
    have hdual5 : ∀ i j : Fin 5,
        (i = j → dotI (rt (![e.g1, e.g2, e.g3, e.g4, e.g5] i))
            (![e.d1, e.d2, e.d3, e.d4, e.d5] j) ≠ 0) ∧
        (i ≠ j → dotI (rt (![e.g1, e.g2, e.g3, e.g4, e.g5] i))
            (![e.d1, e.d2, e.d3, e.d4, e.d5] j) = 0) := by
      intro i j
      have hs := dualOK_spec hdual (i := (i : ℕ)) (j := (j : ℕ)) (by simp) (by simp)
      have hgi : ([rt e.g1, rt e.g2, rt e.g3, rt e.g4, rt e.g5].getD (i : ℕ) [])
          = rt (![e.g1, e.g2, e.g3, e.g4, e.g5] i) := by fin_cases i <;> rfl
      have hdj : ([e.d1, e.d2, e.d3, e.d4, e.d5].getD (j : ℕ) [])
          = ![e.d1, e.d2, e.d3, e.d4, e.d5] j := by fin_cases j <;> rfl
      rw [hgi, hdj] at hs
      exact ⟨fun hij => hs.1 (congrArg Fin.val hij),
        fun hij => hs.2 (fun hh => hij (Fin.ext hh))⟩
    have hge : 5 ≤ compRank (τ := Tag.E6) (e6MaskRoots c) :=
      le_compRank_of_dual (c := c)
        (g := ![e.g1, e.g2, e.g3, e.g4, e.g5])
        (d := ![e.d1, e.d2, e.d3, e.d4, e.d5])
        (fun i => lt_of_testBit hc (hgb i)) hgb hdual5
    exact ⟨le_antisymm hle hge, hcard⟩
  · omega

theorem e6Four_d4_rank_card {c : ℕ} (hc : c < 2 ^ 72) (hp : popc c = 24)
    (h : typedOK c c = true) :
    compRank (τ := Tag.E6) (e6MaskRoots c) = 4 ∧ (e6MaskRoots c).ncard = 24 := by
  have hcard : (e6MaskRoots c).ncard = popc c := e6MaskRoots_ncard c
  rw [hp] at hcard
  rcases typedOK_extract h with hA | hD
  · omega
  · obtain ⟨_, e, he, hec, hval⟩ := hD
    obtain ⟨hg1, hg2, hg3, hg4, hdual, hru, hminor⟩ := d4Valid_facts hval
    have hpq : e.p < 6 ∧ e.q < 6 := by
      have := (List.all_eq_true.mp d4Tab_pq_bound) e he
      exact of_decide_eq_true this
    have hp6 : e.p < Tag.E6.rank := by rw [e6rank_eq]; exact hpq.1
    have hq6 : e.q < Tag.E6.rank := by rw [e6rank_eq]; exact hpq.2
    have hφ : dualLin e.u1 ≠ 0 :=
      dualLin_ne_zero_of_minor e.u1 e.u2 ⟨e.p, hp6⟩ ⟨e.q, hq6⟩ hminor
    let x : Fin Tag.E6.rank → ℚ :=
      (e.u1.getD e.q 0 : ℚ) • Pi.single ⟨e.p, hp6⟩ 1 +
        (-(e.u1.getD e.p 0 : ℚ)) • Pi.single ⟨e.q, hq6⟩ 1
    have hx1 : dualLin e.u1 x = 0 := by
      simp only [x, map_add, map_smul, dualLin_single, smul_eq_mul]
      ring
    have hx2val : dualLin e.u2 x =
        -((e.u1.getD e.p 0 * e.u2.getD e.q 0 - e.u1.getD e.q 0 * e.u2.getD e.p 0 : ℤ) : ℚ) := by
      simp only [x, map_add, map_smul, dualLin_single, smul_eq_mul]
      push_cast
      ring
    have hx2 : dualLin e.u2 x ≠ 0 := by
      rw [hx2val]
      intro hz
      exact hminor (by exact_mod_cast (neg_eq_zero.mp hz))
    have hψ : (dualLin e.u2).domRestrict (LinearMap.ker (dualLin e.u1)) ≠ 0 := by
      intro hzero
      have hxmem : x ∈ LinearMap.ker (dualLin e.u1) := LinearMap.mem_ker.mpr hx1
      have : (dualLin e.u2).domRestrict (LinearMap.ker (dualLin e.u1)) ⟨x, hxmem⟩ = 0 := by
        rw [hzero]; rfl
      exact hx2 (by simpa [LinearMap.domRestrict] using this)
    have hru' : (rootsOf c).all (fun g => dotI g e.u1 == 0 && dotI g e.u2 == 0) = true := by
      rw [← hec]; exact hru
    have hvan1 : ∀ k, k < 72 → c.testBit k = true →
        dualLin e.u1 (qvec (e6RootVec k)) = 0 := by
      intro k hk hbit
      rw [dualLin_qvec e.u1 hk]
      exact_mod_cast (dotI_rt_eq_zero_of_all2 hru' hk hbit).1
    have hvan2 : ∀ k, k < 72 → c.testBit k = true →
        dualLin e.u2 (qvec (e6RootVec k)) = 0 := by
      intro k hk hbit
      rw [dualLin_qvec e.u2 hk]
      exact_mod_cast (dotI_rt_eq_zero_of_all2 hru' hk hbit).2
    have hle : compRank (τ := Tag.E6) (e6MaskRoots c) ≤ 4 :=
      compRank_le_of_ker_inf _ _ hφ hψ hvan1 hvan2
    have hgb : ∀ i : Fin 4, c.testBit (![e.g1, e.g2, e.g3, e.g4] i) = true := by
      intro i
      fin_cases i
      · simpa [hec] using hg1
      · simpa [hec] using hg2
      · simpa [hec] using hg3
      · simpa [hec] using hg4
    have hdual4 : ∀ i j : Fin 4,
        (i = j → dotI (rt (![e.g1, e.g2, e.g3, e.g4] i))
            (![e.d1, e.d2, e.d3, e.d4] j) ≠ 0) ∧
        (i ≠ j → dotI (rt (![e.g1, e.g2, e.g3, e.g4] i))
            (![e.d1, e.d2, e.d3, e.d4] j) = 0) := by
      intro i j
      have hs := dualOK_spec hdual (i := (i : ℕ)) (j := (j : ℕ)) (by simp) (by simp)
      have hgi : ([rt e.g1, rt e.g2, rt e.g3, rt e.g4].getD (i : ℕ) [])
          = rt (![e.g1, e.g2, e.g3, e.g4] i) := by fin_cases i <;> rfl
      have hdj : ([e.d1, e.d2, e.d3, e.d4].getD (j : ℕ) [])
          = ![e.d1, e.d2, e.d3, e.d4] j := by fin_cases j <;> rfl
      rw [hgi, hdj] at hs
      exact ⟨fun hij => hs.1 (congrArg Fin.val hij),
        fun hij => hs.2 (fun hh => hij (Fin.ext hh))⟩
    have hge : 4 ≤ compRank (τ := Tag.E6) (e6MaskRoots c) :=
      le_compRank_of_dual (c := c)
        (g := ![e.g1, e.g2, e.g3, e.g4])
        (d := ![e.d1, e.d2, e.d3, e.d4])
        (fun i => lt_of_testBit hc (hgb i)) hgb hdual4
    exact ⟨le_antisymm hle hge, hcard⟩

end CFSG.Assembly

end
