module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotPositionB

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt elt E)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] {n : ℕ}

section Row

variable (n) in
@[expose] noncomputable def wRowT (i : Fin (n + 3)) (Z : StatedSp (n + 3) K) :
    Fin (n + 1) ⊕ Fin (n + 1) → K :=
  fun x => mat (n + 3) K Z (Sum.inl i) (Sum.map (planes12 n) (planes12 n) x)

theorem offPQ_sumMap_planes12 (x : Fin (n + 1) ⊕ Fin (n + 1)) :
    OffPQ (1 : Fin (n + 3)) 2 (Sum.map (planes12 n) (planes12 n) x) := by
  rcases x with x | x <;>
    exact ⟨by simp [mem_coords, planes12_ne_one], by simp [mem_coords, planes12_ne_two]⟩

theorem inl_ne_of_offPQ {i : Fin (n + 3)} (hi : i = 1 ∨ i = 2) {t : Fin (n + 3) ⊕ Fin (n + 3)}
    (ht : OffPQ 1 2 t) : t ≠ Sum.inl i := by
  rintro rfl
  rcases hi with rfl | rfl
  exacts [ht.1 (inl_mem_coords _), ht.2 (inl_mem_coords _)]

theorem mat_inl_inl_of_mem_wRadical {Z : StatedSp (n + 3) K}
    (hZ : Z ∈ wRadical K (1 : Fin (n + 3)) 2) {i j : Fin (n + 3)} (hj : j = 1 ∨ j = 2) :
    mat (n + 3) K Z (Sum.inl i) (Sum.inl j) =
      (1 : Matrix (Fin (n + 3) ⊕ Fin (n + 3)) (Fin (n + 3) ⊕ Fin (n + 3)) K)
        (Sum.inl i) (Sum.inl j) := by
  rcases hj with rfl | rfl
  exacts [hZ.1 _, hZ.2.1 _]

theorem wRowT_mul {Z Z' : StatedSp (n + 3) K} (hZ : Z ∈ wRadical K (1 : Fin (n + 3)) 2)
    (hZ' : Z' ∈ wRadical K (1 : Fin (n + 3)) 2) {i : Fin (n + 3)} (hi : i = 1 ∨ i = 2)
    (x : Fin (n + 1) ⊕ Fin (n + 1)) :
    wRowT n i (Z * Z') x = wRowT n i Z x + wRowT n i Z' x := by
  set t := Sum.map (planes12 n) (planes12 n) x with htdef
  have ht : OffPQ (1 : Fin (n + 3)) 2 t := offPQ_sumMap_planes12 x
  have hti : t ≠ Sum.inl i := inl_ne_of_offPQ hi ht
  have ht1 : t ≠ Sum.inl 1 := inl_ne_of_offPQ (Or.inl rfl) ht
  have ht2 : t ≠ Sum.inl 2 := inl_ne_of_offPQ (Or.inr rfl) ht
  simp only [wRowT, ← htdef]
  rw [map_mul, Matrix.mul_apply, Fintype.sum_eq_add t (Sum.inl i) hti]
  · rw [hZ'.2.2 t ht t ht1 ht2, Matrix.one_apply_eq, mul_one,
      mat_inl_inl_of_mem_wRadical hZ hi, Matrix.one_apply_eq, one_mul]
  · rintro b ⟨hbt, hbi⟩
    by_cases hb : b = Sum.inl 1 ∨ b = Sum.inl 2
    · obtain ⟨j, hj, rfl⟩ : ∃ j : Fin (n + 3), (j = 1 ∨ j = 2) ∧ b = Sum.inl j := by
        rcases hb with h | h
        exacts [⟨1, Or.inl rfl, h⟩, ⟨2, Or.inr rfl, h⟩]
      rw [mat_inl_inl_of_mem_wRadical hZ hj, Matrix.one_apply_ne (Ne.symm hbi), zero_mul]
    · push Not at hb
      rw [hZ'.2.2 t ht b hb.1 hb.2, Matrix.one_apply_ne hbt, mul_zero]

theorem wRowT_one {i : Fin (n + 3)} (hi : i = 1 ∨ i = 2) :
    wRowT n i (1 : StatedSp (n + 3) K) = 0 := by
  funext x
  simp only [wRowT, map_one, Pi.zero_apply]
  exact Matrix.one_apply_ne (inl_ne_of_offPQ hi (offPQ_sumMap_planes12 x)).symm

theorem wRowT_conj {A B : StatedSp (n + 3) K} (hA : A ∈ wRadical K (1 : Fin (n + 3)) 2)
    (hB : B ∈ wRadical K (1 : Fin (n + 3)) 2) {i : Fin (n + 3)} (hi : i = 1 ∨ i = 2) :
    wRowT n i (A * B * A⁻¹) = wRowT n i B := by
  funext x
  have hAi : A⁻¹ ∈ wRadical K (1 : Fin (n + 3)) 2 := inv_mem hA
  have h1 := wRowT_mul (mul_mem hA hB) hAi hi x
  have h2 := wRowT_mul hA hB hi x
  have h3 := wRowT_mul hA hAi hi x
  rw [mul_inv_cancel, wRowT_one hi] at h3
  simp only [Pi.zero_apply] at h3
  rw [h1, h2]
  linear_combination -h3

theorem wRowT_mul_left {h : StatedSp (n + 3) K} (hh : h ∈ spCompl12 K n)
    (Z : StatedSp (n + 3) K) {i : Fin (n + 3)} (hi : i = 1 ∨ i = 2) :
    wRowT n i (h * Z) = wRowT n i Z := by
  rw [spCompl12_eq_suppGroup] at hh
  have hrow : ∀ b, mat (n + 3) K h (Sum.inl i) b =
      (1 : Matrix (Fin (n + 3) ⊕ Fin (n + 3)) (Fin (n + 3) ⊕ Fin (n + 3)) K) (Sum.inl i) b := by
    intro b
    refine hh (Sum.inl i) b ?_
    rintro ⟨h1, -⟩
    have h1' : OffPQ (1 : Fin (n + 3)) 2 (Sum.inl i) := h1
    rcases hi with rfl | rfl
    exacts [h1'.1 (inl_mem_coords _), h1'.2 (inl_mem_coords _)]
  funext x
  simp only [wRowT]
  rw [map_mul, Matrix.mul_apply]
  simp_rw [hrow]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem coe_spCompl12Equiv_apply (g : StatedSp (n + 1) K) :
    (spCompl12Equiv K n g : StatedSp (n + 3) K) =
      spEmbed (planes12 n) (planes12_injective n) g :=
  MonoidHom.ofInjective_apply _

theorem wRowT_mul_spEmbed (Z : StatedSp (n + 3) K) (g : StatedSp (n + 1) K) (i : Fin (n + 3)) :
    wRowT n i (Z * spEmbed (planes12 n) (planes12_injective n) g) =
      Matrix.vecMul (wRowT n i Z) (mat (n + 1) K g) := by
  have hinj : Function.Injective (Sum.map (planes12 n) (planes12 n)) :=
    Sum.map_injective.2 ⟨planes12_injective n, planes12_injective n⟩
  funext y
  simp only [wRowT, Matrix.vecMul, dotProduct]
  rw [map_mul, mat_spEmbed, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => ?_) (fun x => ?_)
  · rw [spEmbedMat_apply_of_not_mem _ (fun h => hb h.1),
      Matrix.one_apply_ne (fun h => hb ⟨y, h.symm⟩), mul_zero]
  · rw [spEmbedMat_apply_image (planes12_injective n)]

theorem mem_wCenter_of_wRowT_eq_zero {Z : StatedSp (n + 3) K}
    (hZ : Z ∈ wRadical K (1 : Fin (n + 3)) 2) (h1 : wRowT n 1 Z = 0) (h2 : wRowT n 2 Z = 0) :
    Z ∈ wCenter K n := by
  have hrows : ∀ t, OffPQ (1 : Fin (n + 3)) 2 t →
      mat (n + 3) K Z (Sum.inl 1) t = 0 ∧ mat (n + 3) K Z (Sum.inl 2) t = 0 := by
    intro t ht
    obtain ⟨x, rfl⟩ : ∃ x, Sum.map (planes12 n) (planes12 n) x = t := by
      rcases t with j | j
      · have hj1 : j ≠ 1 := fun h => ht.1 (h ▸ inl_mem_coords _)
        have hj2 : j ≠ 2 := fun h => ht.2 (h ▸ inl_mem_coords _)
        obtain ⟨x, hx⟩ := exists_planes12_eq hj1 hj2
        exact ⟨Sum.inl x, by simp [hx]⟩
      · have hj1 : j ≠ 1 := fun h => ht.1 (h ▸ inr_mem_coords _)
        have hj2 : j ≠ 2 := fun h => ht.2 (h ▸ inr_mem_coords _)
        obtain ⟨x, hx⟩ := exists_planes12_eq hj1 hj2
        exact ⟨Sum.inr x, by simp [hx]⟩
    exact ⟨congrFun h1 x, congrFun h2 x⟩
  rw [eq_siegel_of_mem_wRadical one_ne_two_fin hZ hrows]
  exact mul_mem (mul_mem (siegDiag_mem_wCenter (Or.inl rfl) _)
    (siegDiag_mem_wCenter (Or.inr rfl) _)) (siegPair_mem_wCenter _)

end Row

section Short

theorem eq_zero_of_vecMul_elt_sum {v : Fin 2 ⊕ Fin 2 → K}
    (h1 : Matrix.vecMul v (mat 2 K (elt (.positiveSum 0 1 (by decide)) 1)) = v)
    (h2 : Matrix.vecMul v (mat 2 K (elt (.negativeSum 0 1 (by decide)) 1)) = v) : v = 0 := by
  rw [mat_elt, one_smul, Matrix.vecMul_add, Matrix.vecMul_one, add_eq_left] at h1 h2
  have a1 := congrFun h1 (Sum.inr 1)
  have a2 := congrFun h1 (Sum.inr 0)
  have a3 := congrFun h2 (Sum.inl 1)
  have a4 := congrFun h2 (Sum.inl 0)
  simp [Matrix.vecMul, dotProduct, E, Matrix.single_apply] at a1 a2 a3 a4
  funext x
  rcases x with x | x <;> fin_cases x <;> simp_all

end Short

section QZero

theorem elt_positiveLong_mem_longRootSp2 {m : ℕ} (k : Fin m) (c : K) :
    elt (.positiveLong k) c ∈ longRootSp2 K m k := by
  rw [longRootSp2_eq_suppGroup, mem_suppGroup]
  intro r t hrt
  have h0 : E K (.positiveLong k) r t = 0 := by
    simp only [E, Matrix.single_apply]
    refine ite_eq_right_iff.2 ?_
    rintro ⟨rfl, rfl⟩
    exact absurd ⟨inl_mem_coords k, inr_mem_coords k⟩ hrt
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply, h0, smul_zero, add_zero]

theorem elt_negativeLong_mem_longRootSp2 {m : ℕ} (k : Fin m) (c : K) :
    elt (.negativeLong k) c ∈ longRootSp2 K m k := by
  rw [longRootSp2_eq_suppGroup, mem_suppGroup]
  intro r t hrt
  have h0 : E K (.negativeLong k) r t = 0 := by
    simp only [E, Matrix.single_apply]
    refine ite_eq_right_iff.2 ?_
    rintro ⟨rfl, rfl⟩
    exact absurd ⟨inr_mem_coords k, inl_mem_coords k⟩ hrt
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply, h0, smul_zero, add_zero]

theorem siegPair_one_three_mem_wRadical :
    siegPair K (1 : Fin (1 + 3)) 3 1 ∈ wRadical K (1 : Fin (1 + 3)) 2 :=
  siegPair_mem_wRadical (Or.inl rfl) 1

theorem commute_siegPair_one_three {j : StatedSp (1 + 3) K}
    (hj : j ∈ longRootSp2 K (1 + 3) 0) :
    j * siegPair K (1 : Fin (1 + 3)) 3 1 = siegPair K (1 : Fin (1 + 3)) 3 1 * j := by
  rw [longRootSp2_eq_suppGroup] at hj
  refine (commute_suppGroup_compl hj ?_).eq
  rw [mem_suppGroup]
  intro r t hrt
  have h0 : (∃ a, r = Sum.inl a ∧ (a = 0 ∨ ∃ b, t = Sum.inr b ∧ b = 0)) ∨
      ¬ (∃ a b, r = Sum.inl a ∧ t = Sum.inr b) := by
    by_cases h : ∃ a b, r = Sum.inl a ∧ t = Sum.inr b
    · obtain ⟨a, b, rfl, rfl⟩ := h
      left
      refine ⟨a, rfl, ?_⟩
      by_contra hab
      push Not at hab
      apply hrt
      refine ⟨?_, ?_⟩ <;> simp [mem_coords, hab.1, hab.2 b rfl]
    · exact Or.inr h
  rw [mat_siegPair]
  rcases h0 with ⟨a, rfl, ha | ⟨b, rfl, rfl⟩⟩ | h0
  · rcases t with b | b
    · simp [Matrix.one_apply]
    · subst ha
      simp
  · simp
  · rcases r with a | a <;> rcases t with b | b
    · simp [Matrix.one_apply]
    · exact absurd ⟨a, b, rfl, rfl⟩ h0
    · simp
    · simp [Matrix.one_apply]

theorem siegPair_one_three_not_mem_wCenter :
    siegPair K (1 : Fin (1 + 3)) 3 1 ∉ wCenter K 1 := by
  intro h
  have ht : OffPQ (1 : Fin (1 + 3)) 2 (Sum.inr 3) :=
    ⟨by simp [mem_coords], by simp [mem_coords]⟩
  have h0 := (rows_eq_zero_of_mem_wCenter h (Sum.inr 3) ht).1
  rw [mat_siegPair, fromBlocks_apply₁₂] at h0
  simp at h0

end QZero

section F5

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem vecMul_mat_conj {m : ℕ} {v : Fin m ⊕ Fin m → K} {s g : StatedSp m K}
    (h : v = Matrix.vecMul v (mat m K (s * g * s⁻¹))) :
    Matrix.vecMul (Matrix.vecMul v (mat m K s)) (mat m K g) = Matrix.vecMul v (mat m K s) := by
  have hs1 : mat m K s⁻¹ * mat m K s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, map_mul] at h
  calc Matrix.vecMul (Matrix.vecMul v (mat m K s)) (mat m K g)
      = Matrix.vecMul v (mat m K s * mat m K g * (mat m K s⁻¹ * mat m K s)) := by
        rw [hs1, Matrix.mul_one, Matrix.vecMul_vecMul]
    _ = Matrix.vecMul (Matrix.vecMul v (mat m K s * mat m K g * mat m K s⁻¹)) (mat m K s) := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_assoc (mat m K s * mat m K g)]
    _ = Matrix.vecMul v (mat m K s) := by rw [← h]

theorem exists_conj_of_leviAutOfAut_wRadical_one {M : Subgroup (StatedSp (1 + 3) K)}
    (hSM : spCompl12 K 1 ≤ M) (hQM : Disjoint (wRadical K (1 : Fin (1 + 3)) 2) M)
    (hMN : M ≤ normalizer (wRadical K (1 : Fin (1 + 3)) 2 : Set (StatedSp (1 + 3) K)))
    (β : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)) ≃*
      (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)))
    (hβ : ((wRadical K (1 : Fin (1 + 3)) 2).subgroupOf
      (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M)).map β.toMonoidHom =
        (wRadical K (1 : Fin (1 + 3)) 2).subgroupOf (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M))
    (hι : ((spCompl12 K 1).subgroupOf M).map
      (EPilot.leviAutOfAut _ M hQM hMN β hβ).toMonoidHom = (spCompl12 K 1).subgroupOf M) :
    ∃ c : StatedSp (1 + 3) K,
      (((longRootSp2 K (1 + 3) 0).subgroupOf M).map
        (EPilot.leviAutOfAut _ M hQM hMN β hβ).toMonoidHom).map M.subtype =
        (longRootSp2 K (1 + 3) 0).map (MulAut.conj c).toMonoidHom := by
  generalize hιdef : EPilot.leviAutOfAut _ M hQM hMN β hβ = ι at hι ⊢
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (StatedSp 2 K),
      α = ((spCompl12Equiv K 1).trans (restrictMulEquiv hSM ι hι)).trans
        (spCompl12Equiv K 1).symm :=
    ⟨_, rfl⟩
  have hιE : ∀ (m : M) (g : StatedSp 2 K),
      (m : StatedSp (1 + 3) K) = (spCompl12Equiv K 1 g : StatedSp (1 + 3) K) →
      (ι m : StatedSp (1 + 3) K) = (spCompl12Equiv K 1 (α g) : StatedSp (1 + 3) K) := by
    intro m g hmg
    have hm : m = ⟨spCompl12Equiv K 1 g, hSM (spCompl12Equiv K 1 g).2⟩ := Subtype.ext hmg
    subst hm
    have h1 : spCompl12Equiv K 1 (α g) = restrictMulEquiv hSM ι hι (spCompl12Equiv K 1 g) := by
      rw [hαdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [h1, coe_restrictMulEquiv_apply]
  have hJE : ∀ x : StatedSp (1 + 3) K, x ∈ longRootSp2 K (1 + 3) 0 ↔
      ∃ g ∈ longRootSp2 K 2 0, (spCompl12Equiv K 1 g : StatedSp (1 + 3) K) = x := by
    intro x
    rw [← map_spCompl12Equiv_longRootSp2 (K := K) 1]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨s, σ, h | h⟩ := F4Pilot.exists_eq_conj_mul_fieldSp_tauSp α
  ·
    refine ⟨(spCompl12Equiv K 1 s : StatedSp (1 + 3) K), ?_⟩
    have hfJ := map_fieldSp_longRootSp2 (K := K) (n := 2) σ 0
    have hconj : ∀ g : StatedSp 2 K, (spCompl12Equiv K 1 (α g) : StatedSp (1 + 3) K) =
        (spCompl12Equiv K 1 s : StatedSp (1 + 3) K) *
          (spCompl12Equiv K 1 (fieldSp 2 K σ g) : StatedSp (1 + 3) K) *
          (spCompl12Equiv K 1 s : StatedSp (1 + 3) K)⁻¹ := by
      intro g
      rw [h g, map_mul, map_mul, map_inv]
      rfl
    ext x
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      obtain ⟨g, hg, hgm⟩ := (hJE _).1 (mem_subgroupOf.1 hm)
      refine ⟨(spCompl12Equiv K 1 (fieldSp 2 K σ g) : StatedSp (1 + 3) K),
        (hJE _).2 ⟨_, hfJ ▸ mem_map_of_mem _ hg, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype]
      rw [hιE m g hgm.symm, hconj g]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g', hg', rfl⟩ := (hJE _).1 hy
      rw [← hfJ] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      refine ⟨_, ⟨⟨spCompl12Equiv K 1 g, hSM (spCompl12Equiv K 1 g).2⟩,
        mem_subgroupOf.2 ((hJE _).2 ⟨g, hg, rfl⟩), rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_subtype]
      rw [hιE ⟨spCompl12Equiv K 1 g, hSM (spCompl12Equiv K 1 g).2⟩ g rfl, hconj g]
  ·
    exfalso
    have hq₀Q : siegPair K (1 : Fin (1 + 3)) 3 1 ∈ wRadical K (1 : Fin (1 + 3)) 2 :=
      siegPair_one_three_mem_wRadical
    obtain ⟨qq, hqq⟩ : ∃ qq : (wRadical K (1 : Fin (1 + 3)) 2 ⊔ M : Subgroup (StatedSp (1 + 3) K)),
        (qq : StatedSp (1 + 3) K) = siegPair K (1 : Fin (1 + 3)) 3 1 :=
      ⟨⟨_, mem_sup_left hq₀Q⟩, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X : StatedSp (1 + 3) K, X = (β qq : StatedSp (1 + 3) K) := ⟨_, rfl⟩
    have hXQ : X ∈ wRadical K (1 : Fin (1 + 3)) 2 := by
      rw [hX]
      exact (EPilot.coe_mem_iff_of_map_eq hβ qq).2 (by rw [hqq]; exact hq₀Q)
    have key : ∀ g ∈ longRootSp2 K 2 0, ∀ i : Fin (1 + 3), (i = 1 ∨ i = 2) →
        wRowT 1 i X = Matrix.vecMul (wRowT 1 i X) (mat 2 K (α g)) := by
      intro g hg i hi
      have hEgM : (spCompl12Equiv K 1 g : StatedSp (1 + 3) K) ∈ M := hSM (spCompl12Equiv K 1 g).2
      obtain ⟨jm, hjm⟩ : ∃ jm : M,
          (jm : StatedSp (1 + 3) K) = (spCompl12Equiv K 1 g : StatedSp (1 + 3) K) :=
        ⟨⟨_, hEgM⟩, rfl⟩
      have hjJ : (jm : StatedSp (1 + 3) K) ∈ longRootSp2 K (1 + 3) 0 :=
        (hJE _).2 ⟨g, hg, hjm.symm⟩
      obtain ⟨B, hB⟩ : ∃ B : StatedSp (1 + 3) K,
          B = (β (inclusion le_sup_right jm) : StatedSp (1 + 3) K) := ⟨_, rfl⟩
      have hβc : B * X = X * B := by
        have hcomm : inclusion le_sup_right jm * qq = qq * inclusion le_sup_right jm := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inclusion, hqq]
          exact commute_siegPair_one_three hjJ
        rw [hB, hX, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm]
      obtain ⟨A, hA⟩ : ∃ A : StatedSp (1 + 3) K, A = (ι jm : StatedSp (1 + 3) K) := ⟨_, rfl⟩
      have hdQ : A⁻¹ * B ∈ wRadical K (1 : Fin (1 + 3)) 2 := by
        have h0 := EPilot.leviAutOfAut_inv_mul_mem hQM hMN hβ jm
        rw [hιdef] at h0
        rw [hA, hB]
        exact h0
      have hrel : A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) = X * A := by
        calc A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) = (B * X) * B⁻¹ * A := by group
          _ = X * A := by rw [hβc]; group
      have hAS : A ∈ spCompl12 K 1 := by
        rw [hA]
        exact (coe_apply_mem_iff_of_map_eq hι jm).2 (by rw [hjm]; exact (spCompl12Equiv K 1 g).2)
      have h1 := wRowT_mul_left hAS ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) hi
      have h2 := wRowT_conj hdQ hXQ hi
      have h3 : wRowT 1 i (X * A) = Matrix.vecMul (wRowT 1 i X) (mat 2 K (α g)) := by
        rw [hA, hιE jm g hjm, coe_spCompl12Equiv_apply]
        exact wRowT_mul_spEmbed X (α g) i
      calc wRowT 1 i X = wRowT 1 i ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) := h2.symm
        _ = wRowT 1 i (A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹)) := h1.symm
        _ = wRowT 1 i (X * A) := by rw [hrel]
        _ = Matrix.vecMul (wRowT 1 i X) (mat 2 K (α g)) := h3
    have hfix : ∀ i : Fin (1 + 3), (i = 1 ∨ i = 2) → wRowT 1 i X = 0 := by
      intro i hi
      have hA := key _ (elt_positiveLong_mem_longRootSp2 0 1) i hi
      have hB := key _ (elt_negativeLong_mem_longRootSp2 0 1) i hi
      rw [h, F4Pilot.tauSp_elt, F4Pilot.fieldSp_elt, one_pow, map_one] at hA hB
      have hτA : F4Pilot.tauIdx (.positiveLong (0 : Fin 2)) = .positiveSum 0 1 (by decide) := rfl
      have hτB : F4Pilot.tauIdx (.negativeLong (0 : Fin 2)) = .negativeSum 0 1 (by decide) := rfl
      rw [hτA] at hA
      rw [hτB] at hB
      have hw0 := eq_zero_of_vecMul_elt_sum (vecMul_mat_conj hA) (vecMul_mat_conj hB)
      have hs2 : mat 2 K s * mat 2 K s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      calc wRowT 1 i X = Matrix.vecMul (wRowT 1 i X) (mat 2 K s * mat 2 K s⁻¹) := by
            rw [hs2, Matrix.vecMul_one]
        _ = Matrix.vecMul (Matrix.vecMul (wRowT 1 i X) (mat 2 K s)) (mat 2 K s⁻¹) := by
            rw [Matrix.vecMul_vecMul]
        _ = 0 := by rw [hw0, Matrix.zero_vecMul]
    have hXY : X ∈ wCenter K 1 :=
      mem_wCenter_of_wRowT_eq_zero hXQ (hfix 1 (Or.inl rfl)) (hfix 2 (Or.inr rfl))
    rw [hX] at hXY
    have hq₀Y := coe_symm_mem_spIntrinsic hβ .a2 (β qq) hXY
    rw [MulEquiv.symm_apply_apply, hqq] at hq₀Y
    exact siegPair_one_three_not_mem_wCenter hq₀Y

theorem spLongRootF5_a2_one (hK : 4 ≤ Nat.card K) : SpLongRootF5 K 1 .a2 := fun β hβ =>
  exists_conj_of_leviAutOfAut_wRadical_one (M := a2Levi K 1) le_sup_right
    (disjoint_spCoreRadical_spCoreLevi (n := 1) .a2)
    (spCoreLevi_le_normalizer_spCoreRadical (n := 1) .a2) β hβ
    (map_leviAutOfAut_spCoreFactor hK .a2 β hβ)

theorem spLongRootF5_c2_one (hK : 4 ≤ Nat.card K) : SpLongRootF5 K 1 .c2 := fun β hβ =>
  exists_conj_of_leviAutOfAut_wRadical_one (M := spCompl12 K 1) le_rfl
    (disjoint_spCoreRadical_spCoreLevi (n := 1) .c2)
    (spCoreLevi_le_normalizer_spCoreRadical (n := 1) .c2) β hβ
    (map_leviAutOfAut_spCoreFactor hK .c2 β hβ)

theorem spLongRootF5_one_of_four_le (hK : 4 ≤ Nat.card K) (κ : SpTwoCentral) :
    SpLongRootF5 K 1 κ :=
  spLongRootF5_one hK (spLongRootF5_a2_one hK) (spLongRootF5_c2_one hK) κ

theorem spLongRootF5_of_one_le {n : ℕ} (hK : 4 ≤ Nat.card K) (hn : 1 ≤ n) (κ : SpTwoCentral) :
    SpLongRootF5 K n κ := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · exact spLongRootF5_one_of_four_le hK κ
  · exact spLongRootF5_of_two_le hK hn2 κ

end F5

end CFSG.SeitzReduction.SymplecticPilot
