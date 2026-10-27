module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank

section Helpers

variable {r : ℕ} {K : Type} [Field K]

theorem spEnd_comp_apply (g h : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    spEnd (g * h) v = spEnd g (spEnd h v) := by
  rw [spEnd_mul, Module.End.mul_apply]

theorem spEnd_one_apply (v : Fin r ⊕ Fin r → K) : spEnd (1 : StatedSp r K) v = v := by
  rw [spEnd_one]
  rfl

theorem spEnd_cube_apply {g : StatedSp r K} (hg : g ^ 3 = 1) (v : Fin r ⊕ Fin r → K) :
    spEnd g (spEnd g (spEnd g v)) = v := by
  have h : g * g * g = 1 := by rw [← pow_three']; exact hg
  rw [← spEnd_comp_apply, ← spEnd_comp_apply, h, spEnd_one_apply]

theorem spEnd_norm_fixed {g : StatedSp r K} (hg : g ^ 3 = 1) (v : Fin r ⊕ Fin r → K) :
    spEnd g (v + spEnd g v + spEnd g (spEnd g v)) = v + spEnd g v + spEnd g (spEnd g v) := by
  rw [map_add, map_add, spEnd_cube_apply hg]
  abel

end Helpers

theorem exists_generators_of_plane {G : Type*} [Group G] {E : Subgroup G}
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ 1 ∧ y ≠ 1 ∧ x * y ≠ 1 ∧ x * (y * y) ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨x, hx1⟩ := exists_ne (1 : E)
  have hxE : (x : G) ∈ E := x.2
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hord : orderOf (x : G) = 3 := orderOf_eq_prime (hexp x x.2) hx1'
  have hzp : Nat.card (Subgroup.zpowers (x : G)) = 3 := by rw [Nat.card_zpowers, hord]
  have hny : ¬ E ≤ Subgroup.zpowers (x : G) := by
    intro hle
    have := Subgroup.card_dvd_of_le hle
    rw [hcard, hzp] at this
    norm_num at this
  obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers (x : G) := by
    by_contra h
    push Not at h
    exact hny h
  refine ⟨x, hxE, y, hyE, hx1', ?_, ?_, ?_⟩
  · rintro rfl
    exact hy (Subgroup.one_mem _)
  · intro h
    apply hy
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · intro h
    apply hy
    have h2 : y * y = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right h
    have h3 : y = y * y * (y * y) := by
      have h4 := hexp y hyE
      calc y = y * (y * (y * y)) := by rw [← pow_three, h4, mul_one]
        _ = y * y * (y * y) := by group
    rw [h3, h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers _))

section Fixed

variable {r : ℕ} {K : Type} [Field K]

theorem exists_fixed_of_plane {E : Subgroup (StatedSp r K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9) (h3 : (3 : K) ≠ 0) {U : Submodule K (Fin r ⊕ Fin r → K)}
    (hU : ∀ e ∈ E, ∀ u ∈ U, spEnd e u ∈ U) (hU0 : U ≠ ⊥) :
    ∃ z ∈ E, z ≠ 1 ∧ ∃ u ∈ U, u ≠ 0 ∧ spEnd z u = u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy1, hxy21⟩ := exists_generators_of_plane hexp hcard
  have hN : ∀ g ∈ E, g ≠ 1 → ∀ u ∈ U, u + spEnd g u + spEnd g (spEnd g u) = 0 := by
    intro g hg hg1 u hu
    by_contra h0
    have hgu : spEnd g u ∈ U := hU g hg u hu
    exact hcon g hg hg1 _ (U.add_mem (U.add_mem hu hgu) (hU g hg _ hgu)) h0
      (spEnd_norm_fixed (hexp g hg) u)
  have hxy : ∀ v, spEnd y (spEnd x v) = spEnd x (spEnd y v) := fun v => by
    rw [← spEnd_comp_apply, ← spEnd_comp_apply, hcomm y hy x hx]
  have hyc : ∀ v, spEnd y (spEnd y (spEnd y v)) = v := spEnd_cube_apply (hexp y hy)
  have hxy2 : ∀ v, spEnd y (spEnd y (spEnd x v)) = spEnd x (spEnd y (spEnd y v)) := fun v => by
    rw [hxy, hxy]
  have hzero : ∀ u ∈ U, u = 0 := by
    intro u hu
    have hYu : spEnd y u ∈ U := hU y hy u hu
    have hYYu : spEnd y (spEnd y u) ∈ U := hU y hy _ hYu
    have b := hN y hy hy1 u hu
    have c := hN (x * y) (E.mul_mem hx hy) hxy1 u hu
    have d := hN (x * (y * y)) (E.mul_mem hx (E.mul_mem hy hy)) hxy21 u hu
    have e1 := hN x hx hx1 (spEnd y u) hYu
    have e2 := hN x hx hx1 (spEnd y (spEnd y u)) hYYu
    simp only [spEnd_comp_apply] at c d
    rw [hxy (spEnd y u)] at c
    rw [hxy2 (spEnd y (spEnd y u)), hyc (spEnd y u)] at d
    have h3u : (3 : K) • u = 0 := by
      linear_combination (norm := module) b + c + d - e1 - e2
    exact (smul_eq_zero.mp h3u).resolve_left h3
  exact hU0 ((Submodule.eq_bot_iff U).2 hzero)

end Fixed

section Decomp

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def fixSub (g : StatedSp r K) : Submodule K (Fin r ⊕ Fin r → K) :=
  LinearMap.ker (spEnd g - 1)

@[expose] noncomputable def normKer (g : StatedSp r K) : Submodule K (Fin r ⊕ Fin r → K) :=
  LinearMap.ker (1 + spEnd g + spEnd g * spEnd g)

theorem mem_fixSub {g : StatedSp r K} {v : Fin r ⊕ Fin r → K} :
    v ∈ fixSub g ↔ spEnd g v = v := by
  simp [fixSub, LinearMap.mem_ker, sub_eq_zero]

theorem mem_normKer {g : StatedSp r K} {v : Fin r ⊕ Fin r → K} :
    v ∈ normKer g ↔ v + spEnd g v + spEnd g (spEnd g v) = 0 := by
  simp [normKer, LinearMap.mem_ker]

theorem spForm_fixSub_normKer (h3 : (3 : K) ≠ 0) (g : StatedSp r K) {f w : Fin r ⊕ Fin r → K}
    (hf : f ∈ fixSub g) (hw : w ∈ normKer g) : spForm r K f w = 0 := by
  rw [mem_fixSub] at hf
  rw [mem_normKer] at hw
  have h1 : spForm r K f (spEnd g w) = spForm r K f w := by
    have := spEnd_isometry g f w
    rwa [hf] at this
  have h2 : spForm r K f (spEnd g (spEnd g w)) = spForm r K f w := by
    have := spEnd_isometry g f (spEnd g w)
    rw [hf] at this
    rw [this, h1]
  have h0 : spForm r K f (w + spEnd g w + spEnd g (spEnd g w)) = 0 := by rw [hw, map_zero]
  rw [map_add, map_add, h1, h2] at h0
  have : (3 : K) * spForm r K f w = 0 := by linear_combination h0
  exact (mul_eq_zero.mp this).resolve_left h3

theorem fixSub_inf_normKer (h3 : (3 : K) ≠ 0) (g : StatedSp r K) : fixSub g ⊓ normKer g = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hf : v ∈ fixSub g := hv.1
  have hn : v ∈ normKer g := hv.2
  rw [mem_fixSub] at hf
  rw [mem_normKer, hf, hf] at hn
  have h3v : (3 : K) • v = 0 := by linear_combination (norm := module) hn
  exact (Submodule.mem_bot K).2 ((smul_eq_zero.mp h3v).resolve_left h3)

theorem fixSub_sup_normKer (h3 : (3 : K) ≠ 0) {g : StatedSp r K} (hg : g ^ 3 = 1) :
    fixSub g ⊔ normKer g = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨n, hn⟩ : ∃ n : Fin r ⊕ Fin r → K, n = v + spEnd g v + spEnd g (spEnd g v) :=
    ⟨_, rfl⟩
  have hnf : spEnd g n = n := by rw [hn]; exact spEnd_norm_fixed hg v
  have h33 : (3 : K) * 3⁻¹ = 1 := mul_inv_cancel₀ h3
  refine Submodule.mem_sup.2 ⟨(3 : K)⁻¹ • n, ?_, v - (3 : K)⁻¹ • n, ?_, by abel⟩
  · rw [mem_fixSub, map_smul, hnf]
  · rw [mem_normKer]
    simp only [map_sub, map_smul]
    rw [hnf, hnf]
    have key : v - (3 : K)⁻¹ • n + (spEnd g v - (3 : K)⁻¹ • n) +
        (spEnd g (spEnd g v) - (3 : K)⁻¹ • n) = n - ((3 : K) * 3⁻¹) • n := by
      rw [hn]
      module
    rw [key, h33, one_smul, sub_self]

theorem nondegenerate_restrict_of_orth {P P' : Submodule K (Fin r ⊕ Fin r → K)}
    (hsup : P ⊔ P' = ⊤) (horth : ∀ u ∈ P, ∀ v ∈ P', spForm r K u v = 0) :
    ((spForm r K).restrict P).Nondegenerate := by
  have key : ∀ x ∈ P, (∀ y ∈ P, spForm r K x y = 0) → x = 0 := by
    intro x hx hxy
    refine (spForm_nondegenerate (r := r) (K := K)).1 x fun v => ?_
    have hv : v ∈ P ⊔ P' := by rw [hsup]; trivial
    obtain ⟨p, hp, p', hp', rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hxy p hp, horth x hx p' hp', add_zero]
  constructor
  · intro x hx
    exact Subtype.ext (key x x.2 fun y hy => hx ⟨y, hy⟩)
  · intro x hx
    refine Subtype.ext (key x x.2 fun y hy => ?_)
    have h : spForm r K y x = 0 := hx ⟨y, hy⟩
    rw [← spForm_isAlt.neg_eq y x, h, neg_zero]

theorem nondegenerate_fixSub (h3 : (3 : K) ≠ 0) {g : StatedSp r K} (hg : g ^ 3 = 1) :
    ((spForm r K).restrict (fixSub g)).Nondegenerate :=
  nondegenerate_restrict_of_orth (fixSub_sup_normKer h3 hg)
    fun _ hu _ hv => spForm_fixSub_normKer h3 g hu hv

theorem nondegenerate_normKer (h3 : (3 : K) ≠ 0) {g : StatedSp r K} (hg : g ^ 3 = 1) :
    ((spForm r K).restrict (normKer g)).Nondegenerate :=
  nondegenerate_restrict_of_orth (by rw [sup_comm]; exact fixSub_sup_normKer h3 hg)
    fun u hu v hv => by
      rw [← spForm_isAlt.neg_eq v u, spForm_fixSub_normKer h3 g hv hu, neg_zero]

theorem two_le_finrank_of_nondegenerate {P : Submodule K (Fin r ⊕ Fin r → K)}
    (hnd : ((spForm r K).restrict P).Nondegenerate) (hP : P ≠ ⊥) : 2 ≤ Module.finrank K P := by
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨y, hyP, hxy⟩ : ∃ y ∈ P, spForm r K x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (congrArg Subtype.val (hnd.1 ⟨x, hxP⟩ fun z => h z z.2))
  have hli : LinearIndependent K ![(⟨x, hxP⟩ : P), ⟨y, hyP⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • x + t • y = 0 := by simpa using congrArg Subtype.val hst
    have h2 : spForm r K x (s • x + t • y) = 0 := by rw [h1, map_zero]
    rw [map_add, map_smul, map_smul, spForm_isAlt x, smul_eq_mul, smul_eq_mul, mul_zero,
      zero_add] at h2
    have ht : t = 0 := (mul_eq_zero.mp h2).resolve_right hxy
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at h1
    exact (smul_eq_zero.mp h1).resolve_right hx0
  simpa using hli.fintype_card_le_finrank

end Decomp

theorem finrank_eq_two_of_orth_sup {K : Type} [Field K] {P P' : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hsup : P ⊔ P' = ⊤) (horth : ∀ u ∈ P, ∀ v ∈ P', spForm 2 K u v = 0) (hP : P ≠ ⊥)
    (hP' : P' ≠ ⊥) : Module.finrank K P = 2 ∧ Module.finrank K P' = 2 := by
  have hnd := nondegenerate_restrict_of_orth hsup horth
  have horth' : ∀ u ∈ P', ∀ v ∈ P, spForm 2 K u v = 0 := fun u hu v hv => by
    rw [← spForm_isAlt.neg_eq v u, horth v hv u hu, neg_zero]
  have hnd' := nondegenerate_restrict_of_orth (by rw [sup_comm]; exact hsup) horth'
  have hinf : P ⊓ P' = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ P := hv.1
    have h2 : v ∈ P' := hv.2
    exact (Submodule.mem_bot K).2 (congrArg Subtype.val
      (hnd.1 ⟨v, h1⟩ fun y => horth' v h2 y y.2))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P P'
  rw [hsup, hinf, finrank_top, finrank_bot] at hdim
  have h4 : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  have := two_le_finrank_of_nondegenerate hnd hP
  have := two_le_finrank_of_nondegenerate hnd' hP'
  omega

end CFSG.LieType.SeitzGeneration
