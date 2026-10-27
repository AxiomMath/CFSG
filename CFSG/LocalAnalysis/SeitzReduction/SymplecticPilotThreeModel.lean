module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotPositionBSp4B1

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n : ℕ}

theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {q₁ q₂ m₁ m₂ : G}
    (h₁ : Commute q₁ m₁) (h₂ : Commute q₁ m₂) (h₃ : Commute q₁ q₂) (h₄ : Commute q₂ m₁)
    (h₅ : Commute q₂ m₂) : ⁅q₁ * m₁, q₂ * m₂⁆ = ⁅m₁, m₂⁆ := by
  have hX : Commute q₁ (m₁ * q₂ * m₂ * m₁⁻¹) :=
    ((h₁.mul_right h₃).mul_right h₂).mul_right h₁.inv_right
  have hY : Commute q₂ (m₂ * m₁⁻¹ * m₂⁻¹) := (h₅.mul_right h₄.inv_right).mul_right h₅.inv_right
  calc ⁅q₁ * m₁, q₂ * m₂⁆ = (q₁ * (m₁ * q₂ * m₂ * m₁⁻¹) * q₁⁻¹) * (m₂⁻¹ * q₂⁻¹) := by
        rw [commutatorElement_def]; group
    _ = m₁ * (q₂ * (m₂ * m₁⁻¹ * m₂⁻¹) * q₂⁻¹) := by rw [hX.eq, mul_inv_cancel_right]; group
    _ = ⁅m₁, m₂⁆ := by rw [hY.eq, mul_inv_cancel_right, commutatorElement_def]; group

theorem mem_longRootSp2_sup_complSp_of_block {k : Fin n} {x : StatedSp n K}
    (hx : ∀ a b, a ∈ coords k → b ∉ coords k → mat n K x a b = 0 ∧ mat n K x b a = 0) :
    x ∈ longRootSp2 K n k ⊔ complSp K k := by
  have hdet := det_stdBlock_eq_one x k fun c hc => (hx (Sum.inl k) c (inl_mem_coords k) hc).2
  set A : SL(2, K) := mkSL (stdBlock k (mat n K x)) hdet with hA
  set a := longBlock K n k A with ha
  have hblk : stdBlock k (mat n K a) = stdBlock k (mat n K x) := by
    rw [ha, mat_longBlock, stdBlock_blockMat, hA, coe_mkSL]
  have hent : ∀ u ∈ coords k, ∀ t ∈ coords k, mat n K a u t = mat n K x u t := by
    intro u hu t ht
    have e00 := congrFun (congrFun hblk 0) 0
    have e01 := congrFun (congrFun hblk 0) 1
    have e10 := congrFun (congrFun hblk 1) 0
    have e11 := congrFun (congrFun hblk 1) 1
    simp only [stdBlock, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one] at e00 e01 e10 e11
    rcases mem_coords.1 hu with rfl | rfl <;> rcases mem_coords.1 ht with rfl | rfl
    · exact e00
    · exact e01
    · exact e10
    · exact e11
  have hcol : ∀ t ∈ coords k, ∀ u, mat n K a u t = mat n K x u t := by
    intro t ht u
    by_cases hu : u ∈ coords k
    · exact hent u hu t ht
    · rw [ha, mat_longBlock, blockMat_apply_of_not_mem k _ (fun h => hu h.1),
        Matrix.one_apply_ne (fun (h : u = t) => hu (h ▸ ht)), (hx t u ht hu).2]
  have hy : a⁻¹ * x ∈ complSp K k := by
    rw [complSp, mem_suppGroup_iff (parClosed_coords k).compl]
    intro t ht r
    have htk : t ∈ coords k := by simpa using ht
    have e : mat n K (a⁻¹ * x) r t = mat n K (a⁻¹ * a) r t := by
      rw [map_mul, map_mul, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hcol t htk u]
    rw [e, inv_mul_cancel, map_one]
  have hxa : x = a * (a⁻¹ * x) := by group
  rw [hxa]
  exact mul_mem (mem_sup_left ⟨A, rfl⟩) (mem_sup_right hy)

theorem spEmbed_succAbove_one_diagSp (t : Fin 2 → Kˣ) :
    spEmbed (Fin.succAbove (1 : Fin 3)) Fin.succAbove_right_injective (diagSp K 2 t) =
      diagSp K 3 ![t 0, 1, t 1] := by
  have hσ : Function.Injective (Fin.succAbove (1 : Fin 3)) := Fin.succAbove_right_injective
  have hinj : Function.Injective (Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove 1)) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  apply mat_injective
  rw [mat_spEmbed, mat_diagSp, mat_diagSp]
  ext a b
  by_cases h : a ∈ Set.range (Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove 1)) ∧
      b ∈ Set.range (Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove 1))
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [spEmbedMat_apply_image hσ]
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq, diagonal_apply_eq]
      rcases x with i | i <;> fin_cases i <;> rfl
    · rw [diagonal_apply_ne _ hxy, diagonal_apply_ne _ (fun e => hxy (hinj e))]
  · rw [spEmbedMat_apply_of_not_mem _ h]
    by_cases hab : a = b
    · subst hab
      have ha : a ∈ coords (1 : Fin 3) := by
        have h' : a ∉ Set.range (Sum.map (Fin.succAbove (1 : Fin 3)) (Fin.succAbove 1)) :=
          fun h' => h ⟨h', h'⟩
        rw [range_succAbove] at h'
        simpa using h'
      rw [one_apply_eq, diagonal_apply_eq]
      rcases mem_coords.1 ha with rfl | rfl <;> simp [diagSpEntry]
    · rw [one_apply_ne hab, diagonal_apply_ne _ hab]

variable (K) in
@[expose] noncomputable def threeTorus : Subgroup (StatedSp 3 K) :=
  ((siegelTorus K 2).map (complSpEquiv (K := K) (m := 2) 1).toMonoidHom).map
    (complSp K (1 : Fin 3)).subtype

theorem coe_complSpEquiv_diagSp_const (r : Kˣ) :
    ((complSpEquiv (K := K) (m := 2) 1 (diagSp K 2 fun _ => r) : complSp K (1 : Fin 3)) :
      StatedSp 3 K) = diagSp K 3 ![r, 1, r] := by
  rw [coe_complSpEquiv_apply, spEmbed_succAbove_one_diagSp]

theorem mem_threeTorus {x : StatedSp 3 K} :
    x ∈ threeTorus K ↔ ∃ r : Kˣ, diagSp K 3 ![r, 1, r] = x := by
  constructor
  · rintro ⟨_, ⟨d, ⟨r, rfl⟩, rfl⟩, rfl⟩
    exact ⟨r, (coe_complSpEquiv_diagSp_const r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨_, ⟨diagSp K 2 fun _ => r, ⟨r, rfl⟩, rfl⟩, coe_complSpEquiv_diagSp_const r⟩

theorem threeTorus_le_complSp : threeTorus K ≤ complSp K (1 : Fin 3) :=
  map_subtype_le _

theorem diagSp_mem_threeTorus (κ : Kˣ) : diagSp K 3 ![κ, 1, κ] ∈ threeTorus K :=
  mem_threeTorus.2 ⟨κ, rfl⟩

theorem card_threeTorus [Finite K] : Nat.card (threeTorus K) = Nat.card Kˣ := by
  have hinj : Function.Injective ((complSp K (1 : Fin 3)).subtype.comp
      ((complSpEquiv (K := K) (m := 2) 1).toMonoidHom.comp
        ((diagSp K 2).comp (Pi.constMonoidHom (Fin 2) Kˣ)))) := by
    refine (complSp K (1 : Fin 3)).subtype_injective.comp
      ((complSpEquiv (K := K) (m := 2) 1).injective.comp (diagSp_injective.comp ?_))
    intro r s h
    exact congrFun h 0
  have hrange : ((complSp K (1 : Fin 3)).subtype.comp
      ((complSpEquiv (K := K) (m := 2) 1).toMonoidHom.comp
        ((diagSp K 2).comp (Pi.constMonoidHom (Fin 2) Kˣ)))).range = threeTorus K := by
    rw [threeTorus, siegelTorus, MonoidHom.range_comp, MonoidHom.range_comp]
  rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem not_two_dvd_card_threeTorus [Finite K] [CharP K 2] : ¬ 2 ∣ Nat.card (threeTorus K) := by
  rw [card_threeTorus, Nat.card_congr (rootTorusSpEquiv (K := K) (n := 1) 0).toEquiv]
  exact fun h => (Nat.not_even_iff_odd.2 (odd_card_rootTorusSp 0)) (even_iff_two_dvd.2 h)

theorem diagSpEntry_three_ne {κ : Kˣ} (hκ : κ ≠ 1) {a b : Fin 3 ⊕ Fin 3}
    (ha : a ∈ coords (1 : Fin 3)) (hb : b ∉ coords (1 : Fin 3)) :
    diagSpEntry ![κ, 1, κ] a ≠ diagSpEntry ![κ, 1, κ] b := by
  have hκ' : (κ : K) ≠ 1 := fun h => hκ (Units.ext h)
  rcases mem_coords.1 ha with rfl | rfl <;> rcases b with i | i <;> fin_cases i <;>
    simp_all [mem_coords, diagSpEntry, eq_comm]

section FixedPlaneCentralizer

open scoped Pointwise

private theorem diagSpEntry_fixed_ne {K : Type} [Field K] {n : ℕ}
    {t : Fin n → Kˣ} {k : Fin n} (hk : t k = 1) (ht : ∀ i, i ≠ k → t i ≠ 1)
    {a b : Fin n ⊕ Fin n} (ha : a ∈ coords k) (hb : b ∉ coords k) :
    diagSpEntry t a ≠ diagSpEntry t b := by
  rcases mem_coords.1 ha with rfl | rfl <;> rcases b with i | i
  all_goals
    have hi : i ≠ k := by
      intro h
      subst i
      exact hb (by simp [mem_coords])
    simp only [diagSpEntry_inl, diagSpEntry_inr, hk, inv_one, Units.val_one]
    intro h
    apply ht i hi
    first
    | exact Units.ext h.symm
    | have hinv : (t i)⁻¹ = 1 := Units.ext h.symm
      exact inv_eq_one.mp hinv

theorem centralizer_diagSp_le_longRootSp2_sup_complSp {K : Type} [Field K] {n : ℕ}
    (t : Fin n → Kˣ) (k : Fin n) (hk : t k = 1) (ht : ∀ i, i ≠ k → t i ≠ 1) :
    Subgroup.centralizer ({diagSp K n t} : Set (StatedSp n K)) ≤
      longRootSp2 K n k ⊔ complSp K k := by
  intro x hx
  have hc : Commute x (diagSp K n t) := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hz := (commute_diagSp_iff x t).1 hc
  exact mem_longRootSp2_sup_complSp_of_block fun a b ha hb =>
    ⟨hz a b (diagSpEntry_fixed_ne hk ht ha hb),
      hz b a (diagSpEntry_fixed_ne hk ht ha hb).symm⟩

private theorem diagSp_mem_complSp {K : Type} [Field K] {n : ℕ}
    (t : Fin n → Kˣ) (k : Fin n) (hk : t k = 1) :
    diagSp K n t ∈ complSp K k := by
  rw [mem_complSp]
  intro a b hab
  rw [mat_diagSp_apply, Matrix.one_apply]
  by_cases heq : a = b
  · subst b
    rw [if_pos rfl, if_pos rfl]
    have ha : a ∈ coords k := by
      by_contra h
      exact hab ⟨h, h⟩
    rcases mem_coords.1 ha with rfl | rfl
    · simp only [diagSpEntry_inl, hk, Units.val_one]
    · simp only [diagSpEntry_inr, hk, inv_one, Units.val_one]
  · rw [if_neg heq, if_neg heq]

theorem longRootSp2_le_centralizer_diagSp {K : Type} [Field K] {n : ℕ}
    (t : Fin n → Kˣ) (k : Fin n) (hk : t k = 1) :
    longRootSp2 K n k ≤ Subgroup.centralizer ({diagSp K n t} : Set (StatedSp n K)) := by
  intro q hq
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_mem_longRootSp2_of_mem_complSp hq (diagSp_mem_complSp t k hk)).eq

theorem longRootSp2_normal_subgroupOf_centralizer_diagSp
    {K : Type} [Field K] {n : ℕ} (t : Fin n → Kˣ) (k : Fin n)
    (hk : t k = 1) (ht : ∀ i, i ≠ k → t i ≠ 1) :
    ((longRootSp2 K n k).subgroupOf
      (Subgroup.centralizer ({diagSp K n t} : Set (StatedSp n K)))).Normal := by
  have hQC := longRootSp2_le_centralizer_diagSp t k hk
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr
  exact (centralizer_diagSp_le_longRootSp2_sup_complSp t k hk ht).trans
    (sup_le Subgroup.le_normalizer
      ((complSp_le_centralizer_longRootSp2 k).trans (Subgroup.centralizer_le_normalizer _)))

end FixedPlaneCentralizer

theorem centralizer_threeTorus_le {κ : Kˣ} (hκ : κ ≠ 1) :
    centralizer (threeTorus K : Set (StatedSp 3 K)) ≤
      longRootSp2 K 3 (1 : Fin 3) ⊔ complSp K (1 : Fin 3) := by
  intro x hx
  have hc : Commute x (diagSp K 3 ![κ, 1, κ]) :=
    ((mem_centralizer_iff.1 hx) _ (diagSp_mem_threeTorus κ)).symm
  have hz := (commute_diagSp_iff x _).1 hc
  exact mem_longRootSp2_sup_complSp_of_block fun a b ha hb =>
    ⟨hz a b (diagSpEntry_three_ne hκ ha hb), hz b a (diagSpEntry_three_ne hκ ha hb).symm⟩

theorem eq_siegDiag_of_mem_transvRadical_of_commute {κ : Kˣ} (hκ : κ ≠ 1) {q : StatedSp 3 K}
    (hq : q ∈ transvRadical K (1 : Fin 3)) (hc : Commute q (diagSp K 3 ![κ, 1, κ])) :
    q = siegDiag K 1 (mat 3 K q (Sum.inl 1) (Sum.inr 1)) :=
  eq_siegDiag_of_mem_transvRadical hq fun _ ht =>
    (commute_diagSp_iff q _).1 hc _ _ (diagSpEntry_three_ne hκ (inl_mem_coords 1) ht)

section Perfect

variable [CharP K 2]

theorem exists_eq_siegDiag_mul_of_commute {κ : Kˣ} (hκ : κ ≠ 1) {p : StatedSp 3 K}
    (hp : p ∈ transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3))
    (hc : Commute p (diagSp K 3 ![κ, 1, κ])) :
    ∃ (c : K) (m : StatedSp 3 K), m ∈ complSp K (1 : Fin 3) ∧ p = siegDiag K 1 c * m := by
  have hpC : p ∈ centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)) := by
    rw [centralizer_siegDiag_eq_sup]
    exact hp
  set p' : centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)) := ⟨p, hpC⟩ with hp'
  set m := comprHom K (1 : Fin 3) p' with hm
  have hmM : m ∈ complSp K (1 : Fin 3) := comprHom_mem_complSp p'
  set m' : centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)) :=
    ⟨m, complSp_le_centralizer_siegDiag hmM⟩ with hm'def
  have hm' : comprHom K (1 : Fin 3) m' = m := comprHom_of_mem_complSp hmM
  have hq : p * m⁻¹ ∈ transvRadical K (1 : Fin 3) := by
    have h := (mem_transvRadical_iff_comprHom_eq_one (g := p' * m'⁻¹)).2 (by
      rw [map_mul, map_inv, hm', ← hm, mul_inv_cancel])
    simpa [hp', hm'def] using h
  set w := diagSp K 3 ![κ, 1, κ] with hw
  have hwM : w ∈ complSp K (1 : Fin 3) := threeTorus_le_complSp (diagSp_mem_threeTorus κ)
  set w' : centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)) :=
    ⟨w, complSp_le_centralizer_siegDiag hwM⟩ with hw'def
  have hw' : comprHom K (1 : Fin 3) w' = w := comprHom_of_mem_complSp hwM
  have hmw : Commute m w := by
    have h : p' * w' = w' * p' := Subtype.ext hc
    have h' := congrArg (comprHom K (1 : Fin 3)) h
    rw [map_mul, map_mul, hw', ← hm] at h'
    exact h'
  have hqw : Commute (p * m⁻¹) w := hc.mul_left hmw.inv_left
  refine ⟨mat 3 K (p * m⁻¹) (Sum.inl 1) (Sum.inr 1), m, hmM, ?_⟩
  rw [← eq_siegDiag_of_mem_transvRadical_of_commute hκ hq hqw]
  group

theorem le_complSp_of_perfect_of_le_centralizer_threeTorus {κ : Kˣ} (hκ : κ ≠ 1)
    {P : Subgroup (StatedSp 3 K)} (hP : ⁅P, P⁆ = P)
    (hPΛ : P ≤ transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3))
    (hPT : P ≤ centralizer (threeTorus K : Set (StatedSp 3 K))) :
    P ≤ complSp K (1 : Fin 3) := by
  have hdec : ∀ p ∈ P, ∃ (c : K) (m : StatedSp 3 K), m ∈ complSp K (1 : Fin 3) ∧
      p = siegDiag K 1 c * m := fun p hp =>
    exists_eq_siegDiag_mul_of_commute hκ (hPΛ hp)
      ((mem_centralizer_iff.1 (hPT hp)) _ (diagSp_mem_threeTorus κ)).symm
  have hC : ∀ c : K, ∀ g ∈ centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)),
      Commute (siegDiag K 1 c) g := fun c g hg =>
    (commute_siegDiag_of_mem_centralizer hg c).symm
  have hsC : ∀ c : K, siegDiag K (1 : Fin 3) c ∈
      centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)) := fun c =>
    mem_centralizer_singleton_iff.2 (by rw [siegDiag_mul, siegDiag_mul, add_comm])
  rw [← hP, Subgroup.commutator_le]
  intro p₁ hp₁ p₂ hp₂
  obtain ⟨c₁, m₁, hm₁, rfl⟩ := hdec p₁ hp₁
  obtain ⟨c₂, m₂, hm₂, rfl⟩ := hdec p₂ hp₂
  have hm₁C := complSp_le_centralizer_siegDiag hm₁
  have hm₂C := complSp_le_centralizer_siegDiag hm₂
  rw [commutatorElement_mul_mul_of_commute (hC c₁ _ hm₁C) (hC c₁ _ hm₂C) (hC c₁ _ (hsC c₂))
    (hC c₂ _ hm₁C) (hC c₂ _ hm₂C), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hm₁ hm₂) (inv_mem hm₁)) (inv_mem hm₂)

end Perfect

end CFSG.SeitzReduction.SymplecticPilot
