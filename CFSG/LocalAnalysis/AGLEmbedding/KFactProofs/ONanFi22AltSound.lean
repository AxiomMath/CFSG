module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22AltData
public import CFSG.Sporadic.SchreierLemmas.MoorePresentation

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Alt

open scoped Pointwise

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.AGLEmbedding.KFactProofs.Fi22Guest
  CFSG.Sporadic.SchreierLemmas

variable {G : Type*} [Group G]

structure AltData (X Y : G) (q : ℕ → G) (x : ℕ → G) : Prop where
  X_pow : X ^ 5 = 1
  Y_pow : Y ^ 5 = 1
  XY_comm : X * Y = Y * X
  q_mem : ∀ j, q j ∈ Subgroup.closure ({X, Y} : Set G)
  x_mem : ∀ i, 1 ≤ i → i ≤ 7 → x i ∈ Subgroup.closure
    {m : G | ∃ j c : ℕ, q j ≠ 1 ∧ m * q j * m⁻¹ = q j ^ c}
  moore : IsMooreFamily 7 x
  ne_one : x 1 ≠ 1

theorem AltData.map {H : Type*} [Group H] {X Y : G} {q x : ℕ → G} (D : AltData X Y q x)
    (ψ : G ≃* H) : AltData (ψ X) (ψ Y) (fun j => ψ (q j)) (fun i => ψ (x i)) where
  X_pow := by rw [← map_pow, D.X_pow, map_one]
  Y_pow := by rw [← map_pow, D.Y_pow, map_one]
  XY_comm := by rw [← map_mul, ← map_mul, D.XY_comm]
  q_mem j := by
    have := Subgroup.mem_map_of_mem ψ.toMonoidHom (D.q_mem j)
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  x_mem i h1 h7 := by
    have := Subgroup.mem_map_of_mem ψ.toMonoidHom (D.x_mem i h1 h7)
    rw [MonoidHom.map_closure] at this
    refine Subgroup.closure_mono ?_ this
    rintro _ ⟨m, ⟨j, c, hq, hm⟩, rfl⟩
    refine ⟨j, c, fun h => hq (ψ.injective (by simpa using h)), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hm, map_pow]
  moore :=
    { cube_one := by rw [← map_pow, D.moore.cube_one, map_one]
      sq_eq_one := fun j h2 hj => by rw [← map_pow, D.moore.sq_eq_one j h2 hj, map_one]
      cube_adjacent := fun j h2 hj => by
        rw [← map_mul, ← map_pow, D.moore.cube_adjacent j h2 hj, map_one]
      sq_distant := fun i j hi hij hj => by
        rw [← map_mul, ← map_pow, D.moore.sq_distant i j hi hij hj, map_one] }
  ne_one h := D.ne_one (ψ.injective (by rw [map_one]; exact h))

theorem AltData.pow_five {X Y : G} {q x : ℕ → G} (D : AltData X Y q x) :
    ∀ g ∈ Subgroup.closure ({X, Y} : Set G), g ^ 5 = 1 :=
  pow_eq_one_of_mem_closure (GuestData.pairwise_commute D.XY_comm) <| by
    rintro s (rfl | rfl)
    exacts [D.X_pow, D.Y_pow]

theorem AltData.nonempty_alt9 {X Y : G} {q x : ℕ → G} (D : AltData X Y q x) :
    Nonempty (Subgroup.closure (x '' Set.Icc 1 7) ≃* alternatingGroup (Fin 9)) := by
  have hM : IsMooreFamily (9 - 2) x := D.moore
  obtain ⟨e⟩ := ((moore_alternating_presentation (by norm_num : 3 ≤ 9) x hM).2.2.2.2.2
    (by norm_num) ⟨1, ⟨le_refl _, by norm_num⟩, D.ne_one⟩).2
  exact ⟨e.symm⟩

theorem AltData.closure_le_join [Finite G] {X Y : G} {q x : ℕ → G} (D : AltData X Y q x)
    (A : Subgroup G) (hA : Subgroup.closure ({X, Y} : Set G) ≤ A) :
    Subgroup.closure (x '' Set.Icc 1 7) ≤
      ⨆ (Z : Subgroup G) (_ : Z ≤ A) (_ : Z ≠ ⊥), Subgroup.normalizer (Z : Set G) := by
  have hS : {m : G | ∃ j c : ℕ, q j ≠ 1 ∧ m * q j * m⁻¹ = q j ^ c} ⊆
      ((⨆ (Z : Subgroup G) (_ : Z ≤ A) (_ : Z ≠ ⊥), Subgroup.normalizer (Z : Set G) :
        Subgroup G) : Set G) := by
    rintro m ⟨j, c, hq1, hm⟩
    have hZ : Subgroup.zpowers (q j) ≤ A := (Subgroup.zpowers_le).2 (hA (D.q_mem j))
    have hZne : Subgroup.zpowers (q j) ≠ ⊥ := by rwa [Ne, Subgroup.zpowers_eq_bot]
    have hN : m ∈ Subgroup.normalizer ((Subgroup.zpowers (q j) : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      refine Subgroup.mem_zpowers_iff.2 ⟨c * k, ?_⟩
      have h' : q j ^ (c : ℤ) = m * q j * m⁻¹ := by rw [zpow_natCast, hm]
      rw [zpow_mul, h', conj_zpow]
    exact Subgroup.mem_iSup_of_mem (Subgroup.zpowers (q j))
      (Subgroup.mem_iSup_of_mem hZ (Subgroup.mem_iSup_of_mem hZne hN))
  rw [Subgroup.closure_le]
  rintro _ ⟨i, ⟨hi1, hi7⟩, rfl⟩
  exact ((Subgroup.closure_le _).2 hS) (D.x_mem i hi1 hi7)

theorem AltData.exists_alt_join [Finite G] {X Y : G} {q x : ℕ → G} (D : AltData X Y q x)
    (A : Sylow 5 G) :
    ∃ J : Subgroup G, Nonempty (J ≃* alternatingGroup (Fin 9)) ∧
      J ≤ ⨆ (Z : Subgroup G) (_ : Z ≤ (A : Subgroup G)) (_ : Z ≠ ⊥),
        Subgroup.normalizer (Z : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.closure ({X, Y} : Set G)) := fun g =>
    ⟨1, Subtype.ext (by simpa using D.pow_five g.1 g.2)⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S A
  have D' := D.map (MulAut.conj g)
  refine ⟨_, D'.nonempty_alt9, D'.closure_le_join (A : Subgroup G) ?_⟩
  rw [Subgroup.closure_le]
  have hT : (A : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  rintro _ (rfl | rfl)
  all_goals
    rw [hT]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS (Subgroup.subset_closure (by simp)))

section Soundness

variable {n : ℕ} [MulAction G (Fin n)]

theorem rep_xTab (hn : n < 2 ^ 32) {x y : G} {α αi β βi : Table} (hx : Rep n α x)
    (hxi : Rep n αi x⁻¹) (hy : Rep n β y) (hyi : Rep n βi y⁻¹) (i : ℕ) :
    Rep n (xTab n α αi β βi i)
      ((xData.getD i []).map fun s => wordProd (img2 x y) (eLetterWord s)).prod := by
  unfold xTab
  generalize xData.getD i [] = l
  induction l with
  | nil => exact Rep.idT hn
  | cons s l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    exact Rep.compT (rep_wordTab hn hx hxi hy hyi _) ih

theorem mooreChecks_spec [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32) {X : ℕ → Table}
    {xs : ℕ → G} (hX : ∀ i, 1 ≤ i → i ≤ 7 → Rep n (X i) (xs i))
    (h : mooreChecks n X = true) : IsMooreFamily 7 xs ∧ xs 1 ≠ 1 := by
  unfold mooreChecks at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hone : ∀ {g : G} {T : Table}, Rep n T g → T = idT n → g = 1 := fun hT hid =>
    eq_one_of_rep_idT hn (hid ▸ hT)
  refine ⟨⟨?_, fun j hj2 hj7 => ?_, fun j hj2 hj7 => ?_, fun i j hi hij hj => ?_⟩, ?_⟩
  · exact hone (Rep.powT hn (hX 1 le_rfl (by norm_num)) 3) h1
  · rcases h2 j (by omega) with h | ⟨h, -⟩
    · omega
    · exact hone (Rep.powT hn (hX j (by omega) hj7) 2) h
  · rcases h2 j (by omega) with h | ⟨-, h⟩
    · omega
    · exact hone (Rep.powT hn (Rep.compT (hX (j - 1) (by omega) (by omega)) (hX j (by omega) hj7))
        3) h
  · rcases h3 i (by omega) j (by omega) with h | h
    · omega
    · exact hone (Rep.powT hn (Rep.compT (hX i hi (by omega)) (hX j (by omega) hj)) 2) h
  · exact ne_one_of_movesPt h4 (hX 1 le_rfl (by norm_num))

theorem altData_of_check [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32) {x y : G}
    {α αi β βi : Table} (hx : Rep n α x) (hxi : Rep n αi x⁻¹) (hy : Rep n β y)
    (hyi : Rep n βi y⁻¹) (h1 : relCheck n α αi β βi wordRels = true)
    (h2 : nData.all (fun t => movesPt n (wordTab n α αi β βi (qWord t.1))) = true)
    (h : altCheck n α αi β βi = true) :
    ∃ (X Y : G) (q : ℕ → G) (xs : ℕ → G), AltData X Y q xs := by
  have hrels := wordProd_eq_one_of_relCheck hn hx hxi hy hyi h1
  let g := img2 x y
  let q : ℕ → G := fun j => wordProd g (qWord j)
  let S : Set G := {m : G | ∃ j c : ℕ, q j ≠ 1 ∧ m * q j * m⁻¹ = q j ^ c}
  let F : ℤ → G := fun s => wordProd g (eLetterWord s)
  let xs : ℕ → G := fun i => ((xData.getD (i - 1) []).map F).prod
  have hX : wordProd g wx ^ 5 = 1 := by
    have := hrels (wpow wx 5) (by simp [wordRels])
    rwa [wordProd_wpow] at this
  have hY : wordProd g wy ^ 5 = 1 := by
    have := hrels (wpow wy 5) (by simp [wordRels])
    rwa [wordProd_wpow] at this
  have hXY : wordProd g wx * wordProd g wy = wordProd g wy * wordProd g wx := by
    have := hrels (wx ++ wy ++ winv wx ++ winv wy) (by simp [wordRels])
    simp only [wordProd_append, wordProd_winv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hq : ∀ j, q j ∈ Subgroup.closure ({wordProd g wx, wordProd g wy} : Set G) := by
    have hXm : wordProd g wx ∈ Subgroup.closure ({wordProd g wx, wordProd g wy} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hYm : wordProd g wy ∈ Subgroup.closure ({wordProd g wx, wordProd g wy} : Set G) :=
      Subgroup.subset_closure (by simp)
    intro j
    rcases j with _ | _ | k
    · exact hXm
    · exact hYm
    · show wordProd g (wx ++ wpow wy (k + 1)) ∈ _
      rw [wordProd_append, wordProd_wpow]
      exact Subgroup.mul_mem _ hXm (Subgroup.pow_mem _ hYm _)
  have hnt : ∀ t ∈ nData, q t.1 ≠ 1 := fun t ht =>
    ne_one_of_movesPt ((List.all_eq_true.1 h2) t ht) (rep_wordTab hn hx hxi hy hyi (qWord t.1))
  have hm : ∀ k, wordProd g (nWord k) ∈ Subgroup.closure S := by
    intro k
    by_cases hk : k < nData.length
    · have hd : nData.getD k (0, 0, []) = nData[k] := List.getD_eq_getElem _ _ hk
      have hnw : nWord k = nData[k].2.2 := by
        unfold nWord
        rw [hd]
      have hmem : nData[k] ∈ nData := List.getElem_mem hk
      have hrel := hrels (nRel nData[k]) (by
        simp only [wordRels, List.mem_append, List.mem_map]
        exact Or.inr ⟨_, hmem, rfl⟩)
      simp only [nRel, wordProd_append, wordProd_winv, wordProd_wpow] at hrel
      rw [hnw]
      exact Subgroup.subset_closure ⟨nData[k].1, nData[k].2.1, hnt _ hmem, mul_inv_eq_one.1 hrel⟩
    · have : nWord k = [] := by
        unfold nWord
        rw [List.getD_eq_default _ _ (not_lt.1 hk)]
      rw [this]
      exact Subgroup.one_mem _
  have hF : ∀ s, F s ∈ Subgroup.closure S := by
    intro s
    show wordProd g (eLetterWord s) ∈ _
    unfold eLetterWord
    split_ifs
    · exact hm _
    · rw [wordProd_winv]
      exact Subgroup.inv_mem _ (hm _)
  have hxs : ∀ i, 1 ≤ i → i ≤ 7 → xs i ∈ Subgroup.closure S := fun i _ _ =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hz
      exact hF s
  have hrep : ∀ i, 1 ≤ i → i ≤ 7 → Rep n (xTab n α αi β βi (i - 1)) (xs i) := fun i _ _ =>
    rep_xTab hn hx hxi hy hyi (i - 1)
  unfold altCheck at h
  obtain ⟨hmoore, hne⟩ := mooreChecks_spec hn (X := fun i => [xTab n α αi β βi 0,
    xTab n α αi β βi 0, xTab n α αi β βi 1, xTab n α αi β βi 2, xTab n α αi β βi 3,
    xTab n α αi β βi 4, xTab n α αi β βi 5, xTab n α αi β βi 6].getD i
      (xTab n α αi β βi 0)) (xs := xs) (fun i hi1 hi7 => by
        have := hrep i hi1 hi7
        interval_cases i <;> exact this) h
  exact ⟨_, _, q, xs, ⟨hX, hY, hXY, hq, hxs, hmoore, hne⟩⟩

end Soundness

end CFSG.AGLEmbedding.KFactProofs.Fi22Alt
