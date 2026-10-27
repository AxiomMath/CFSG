module

public import CFSG.GH74.Tits83.GlueMoufang

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {X : Type u} [Group X]

theorem ofRankTwoU_eq_root (D : RankTwoSystem X 8) {j : ℤ} (h1 : 1 ≤ j) (h2 : j ≤ 8) :
    ofRankTwoU D j = D.root j := by
  unfold ofRankTwoU
  rw [Rt_pos_idx h1 h2]

theorem chainProd_le_win_std (D : RankTwoSystem X 8) {a b : ℤ} (ha : 1 ≤ a) (hb : b ≤ 8) :
    chainProd D.root (intList a b) ⊆ win (ofRankTwoU D) a b := by
  refine chainProd_subset D.root (win (ofRankTwoU D) a b) _ (fun k hk => ?_)
  obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
  rw [← ofRankTwoU_eq_root D (by omega) (by omega)]
  exact le_iSup₂_of_le k (by simp only [Set.mem_Icc]; omega) le_rfl


theorem comm_win_std (D : RankTwoSystem X 8) {a b : ℤ} (ha : 1 ≤ a) (hab : a < b)
    (hb : b ≤ 8) {x y : X} (hx : x ∈ D.root a) (hy : y ∈ D.root b) :
    ⁅x, y⁆ ∈ win (ofRankTwoU D) (a + 1) (b - 1) :=
  chainProd_le_win_std D (by omega) (by omega) (comm_std D ha hab hb hx hy)

theorem comm_ofRankTwo (D : RankTwoSystem X 8) :
    ∀ i j : ℤ, i < j → j < i + 8 → ∀ u ∈ ofRankTwoU D i, ∀ v ∈ ofRankTwoU D j,
      ⁅u, v⁆ ∈ ⨆ k ∈ Set.Ioo i j, ofRankTwoU D k := by
  intro i j hij hji u hu v hv
  rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
  ·
    let c : ℤ := 2 * k + 8
    have hc : c = 2 * (k + 4) := by dsimp [c]; ring
    obtain ⟨g, hg⟩ := exists_moves_refl D c (by rw [hc]; exact even_two_mul (k + 4))
    let a : ℤ := c - j
    have ha1 : 1 ≤ a := by dsimp [a, c]; omega
    have ha8 : a < 8 := by dsimp [a, c]; omega
    have hx : g * v * g⁻¹ ∈ ofRankTwoU D a := by
      have h := MovesU.conj_mem hg hv
      rwa [show c - j = a by rfl] at h
    have hy : g * u * g⁻¹ ∈ ofRankTwoU D 8 := by
      have h := MovesU.conj_mem hg hu
      rwa [show c - 2 * k = 8 by dsimp [c]; ring] at h
    have hx' : g * v * g⁻¹ ∈ D.root a := by
      rw [ofRankTwoU_eq_root D ha1 (by omega)] at hx
      exact hx
    have hy' : g * u * g⁻¹ ∈ D.root 8 := by
      rw [ofRankTwoU_eq_root D (by norm_num) (by norm_num)] at hy
      exact hy
    have hz : ⁅g * v * g⁻¹, g * u * g⁻¹⁆ ∈ win (ofRankTwoU D) (a + 1) 7 :=
      comm_win_std D ha1 ha8 (by norm_num) hx' hy'
    have hg' : MovesU D g⁻¹ (c - ·) := MovesU.inv_refl hg
    have hconj : g⁻¹ * ⁅g * v * g⁻¹, g * u * g⁻¹⁆ * g ∈
        win (ofRankTwoU D) (2 * k + 1) (j - 1) := by
      have himg : g⁻¹ * ⁅g * v * g⁻¹, g * u * g⁻¹⁆ * g ∈
          (win (ofRankTwoU D) (a + 1) 7).map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨_, hz, by
          change (MulAut.conj g⁻¹) (⁅g * v * g⁻¹, g * u * g⁻¹⁆) =
            g⁻¹ * ⁅g * v * g⁻¹, g * u * g⁻¹⁆ * g
          rw [MulAut.conj_apply, inv_inv]⟩
      rw [MovesU.map_win_refl hg' (a + 1) 7] at himg
      rw [show c - 7 = 2 * k + 1 by dsimp [c]; ring,
        show c - (a + 1) = j - 1 by dsimp [a, c]; ring] at himg
      exact himg
    have heq : ⁅u, v⁆ = (g⁻¹ * ⁅g * v * g⁻¹, g * u * g⁻¹⁆ * g)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    refine SetLike.le_def.mp (iSup₂_le fun t ht => ?_)
      ((win (ofRankTwoU D) (2 * k + 1) (j - 1)).inv_mem hconj)
    have ht' : t ∈ Set.Ioo (2 * k) j := Set.mem_Ioo.2 (by
      simp only [Set.mem_Icc] at ht
      omega)
    exact le_iSup₂_of_le t ht' le_rfl
  ·
    let c : ℤ := -2 * k
    obtain ⟨g, hg⟩ := exists_moves_shift D (-k)
    have hg : MovesU D g (· + c) := by
      simpa [c] using hg
    have hx : g * u * g⁻¹ ∈ ofRankTwoU D 1 := by
      have h := MovesU.conj_mem hg hu
      rwa [show 2 * k + 1 + c = 1 by dsimp [c]; ring] at h
    have hy : g * v * g⁻¹ ∈ ofRankTwoU D (j + c) :=
      MovesU.conj_mem hg hv
    have hb1 : 1 < j + c := by omega
    have hb8 : j + c ≤ 8 := by omega
    have hx' : g * u * g⁻¹ ∈ D.root 1 := by
      rw [ofRankTwoU_eq_root D (by norm_num) (by norm_num)] at hx
      exact hx
    have hy' : g * v * g⁻¹ ∈ D.root (j + c) := by
      rw [ofRankTwoU_eq_root D (by omega) hb8] at hy
      exact hy
    have hz : ⁅g * u * g⁻¹, g * v * g⁻¹⁆ ∈ win (ofRankTwoU D) 2 (j + c - 1) :=
      comm_win_std D (by norm_num) hb1 hb8 hx' hy'
    have hg' : MovesU D g⁻¹ (· - c) := MovesU.inv_shift hg
    have hconj : g⁻¹ * ⁅g * u * g⁻¹, g * v * g⁻¹⁆ * g ∈
        win (ofRankTwoU D) (2 * k + 2) (j - 1) := by
      have himg : g⁻¹ * ⁅g * u * g⁻¹, g * v * g⁻¹⁆ * g ∈
          (win (ofRankTwoU D) 2 (j + c - 1)).map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨_, hz, by
          change (MulAut.conj g⁻¹) (⁅g * u * g⁻¹, g * v * g⁻¹⁆) =
            g⁻¹ * ⁅g * u * g⁻¹, g * v * g⁻¹⁆ * g
          rw [MulAut.conj_apply, inv_inv]⟩
      rw [MovesU.map_win_shift hg' 2 (j + c - 1)] at himg
      rw [show 2 + -c = 2 * k + 2 by dsimp [c]; ring,
        show j + c - 1 + -c = j - 1 by ring] at himg
      exact himg
    have heq : ⁅u, v⁆ = g⁻¹ * ⁅g * u * g⁻¹, g * v * g⁻¹⁆ * g := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    refine SetLike.le_def.mp (iSup₂_le fun t ht => ?_) hconj
    have ht' : t ∈ Set.Ioo (2 * k + 1) j := Set.mem_Ioo.2 (by
      simp only [Set.mem_Icc] at ht
      omega)
    exact le_iSup₂_of_le t ht' le_rfl

theorem unique_std (D : RankTwoSystem X 8) :
    ∀ f g : ℤ → X,
      (∀ k ∈ intList 1 8, f k ∈ ofRankTwoU D k) →
      (∀ k ∈ intList 1 8, g k ∈ ofRankTwoU D k) →
      ((intList 1 8).map f).prod = ((intList 1 8).map g).prod →
      ∀ k ∈ intList 1 8, f k = g k := by
  intro f g hf hg hprod k hk
  have hf' : ∀ k ∈ intList 1 8, f k ∈ D.root k := by
    intro j hj
    have h := hf j hj
    rwa [ofRankTwoU_eq_root D (by simpa using mem_intList_iff.1 hj |>.1)
      (by simpa using mem_intList_iff.1 hj |>.2)] at h
  have hg' : ∀ k ∈ intList 1 8, g k ∈ D.root k := by
    intro j hj
    have h := hg j hj
    rwa [ofRankTwoU_eq_root D (by simpa using mem_intList_iff.1 hj |>.1)
      (by simpa using mem_intList_iff.1 hj |>.2)] at h
  exact D.roots.unique f g hf' hg' hprod k hk


theorem unique_ofRankTwo (D : RankTwoSystem X 8) :
    ∀ i : ℤ, ∀ f g : ℤ → X,
      (∀ k ∈ intList (i + 1) (i + 8), f k ∈ ofRankTwoU D k) →
      (∀ k ∈ intList (i + 1) (i + 8), g k ∈ ofRankTwoU D k) →
      ((intList (i + 1) (i + 8)).map f).prod =
        ((intList (i + 1) (i + 8)).map g).prod →
      ∀ k ∈ intList (i + 1) (i + 8), f k = g k := by
  intro i f g hf hg hprod
  rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
  ·
    let c : ℤ := -(2 * k)
    obtain ⟨g0, hg0⟩ := exists_moves_shift D (-k)
    have hg0 : MovesU D g0 (· + c) := by simpa [c] using hg0
    let F : ℤ → X := fun ℓ => g0 * f (ℓ - c) * g0⁻¹
    let G : ℤ → X := fun ℓ => g0 * g (ℓ - c) * g0⁻¹
    have hlist : (intList 1 8).map (fun ℓ => ℓ - c) = intList (2 * k + 1) (2 * k + 8) := by
      have h := intList_add 1 8 (-c)
      rw [show (1 : ℤ) + -c = 2 * k + 1 by dsimp [c]; ring,
        show (8 : ℤ) + -c = 2 * k + 8 by dsimp [c]; ring] at h
      simpa [sub_eq_add_neg] using h.symm
    have hF : ∀ ℓ ∈ intList 1 8, F ℓ ∈ ofRankTwoU D ℓ := by
      intro ℓ hℓ
      have hmem : ℓ - c ∈ intList (2 * k + 1) (2 * k + 8) := by
        have : ℓ - c ∈ (intList 1 8).map (fun ℓ => ℓ - c) :=
          List.mem_map.2 ⟨ℓ, hℓ, rfl⟩
        rwa [hlist] at this
      have h := MovesU.conj_mem hg0 (hf (ℓ - c) hmem)
      rwa [show ℓ - c + c = ℓ by ring] at h
    have hG : ∀ ℓ ∈ intList 1 8, G ℓ ∈ ofRankTwoU D ℓ := by
      intro ℓ hℓ
      have hmem : ℓ - c ∈ intList (2 * k + 1) (2 * k + 8) := by
        have : ℓ - c ∈ (intList 1 8).map (fun ℓ => ℓ - c) :=
          List.mem_map.2 ⟨ℓ, hℓ, rfl⟩
        rwa [hlist] at this
      have h := MovesU.conj_mem hg0 (hg (ℓ - c) hmem)
      rwa [show ℓ - c + c = ℓ by ring] at h
    have hprodF : ((intList 1 8).map F).prod =
        g0 * ((intList (2 * k + 1) (2 * k + 8)).map f).prod * g0⁻¹ := by
      calc
        ((intList 1 8).map F).prod
            = (((intList 1 8).map (fun ℓ => ℓ - c)).map
                (fun x => g0 * f x * g0⁻¹)).prod := by
              dsimp [F]
              simp [List.map_map, Function.comp_def]
        _ = ((intList (2 * k + 1) (2 * k + 8)).map
              (fun x => g0 * f x * g0⁻¹)).prod := by rw [hlist]
        _ = (((intList (2 * k + 1) (2 * k + 8)).map f).map
              (fun x => g0 * x * g0⁻¹)).prod := by
              simp [List.map_map, Function.comp_def]
        _ = g0 * ((intList (2 * k + 1) (2 * k + 8)).map f).prod * g0⁻¹ :=
              list_prod_conj g0 ((intList (2 * k + 1) (2 * k + 8)).map f)
    have hprodG : ((intList 1 8).map G).prod =
        g0 * ((intList (2 * k + 1) (2 * k + 8)).map g).prod * g0⁻¹ := by
      calc
        ((intList 1 8).map G).prod
            = (((intList 1 8).map (fun ℓ => ℓ - c)).map
                (fun x => g0 * g x * g0⁻¹)).prod := by
              dsimp [G]
              simp [List.map_map, Function.comp_def]
        _ = ((intList (2 * k + 1) (2 * k + 8)).map
              (fun x => g0 * g x * g0⁻¹)).prod := by rw [hlist]
        _ = (((intList (2 * k + 1) (2 * k + 8)).map g).map
              (fun x => g0 * x * g0⁻¹)).prod := by
              simp [List.map_map, Function.comp_def]
        _ = g0 * ((intList (2 * k + 1) (2 * k + 8)).map g).prod * g0⁻¹ :=
              list_prod_conj g0 ((intList (2 * k + 1) (2 * k + 8)).map g)
    have hprodFG : ((intList 1 8).map F).prod = ((intList 1 8).map G).prod := by
      rw [hprodF, hprodG, hprod]
    have huniq := unique_std D F G hF hG hprodFG
    intro j hj
    have hmem : j + c ∈ intList 1 8 := by
      have hjb := mem_intList_iff.1 hj
      dsimp [c] at hjb ⊢
      have : j ∈ (intList 1 8).map (fun ℓ => ℓ - c) := by
        rw [hlist]
        exact hj
      obtain ⟨ℓ, hℓ, heq⟩ := List.mem_map.1 this
      have : ℓ = j + c := by dsimp [c] at heq ⊢; omega
      rwa [this] at hℓ
    have h := huniq (j + c) hmem
    dsimp [F, G] at h
    have := congrArg (fun z => g0⁻¹ * z * g0) h
    simpa [mul_assoc] using this
  ·
    let c : ℤ := 2 * k + 10
    have hcEven : Even c := ⟨k + 5, by dsimp [c]; ring⟩
    obtain ⟨g0, hg0⟩ := exists_moves_refl D c hcEven
    let F : ℤ → X := fun ℓ => (g0 * f (c - ℓ) * g0⁻¹)⁻¹
    let G : ℤ → X := fun ℓ => (g0 * g (c - ℓ) * g0⁻¹)⁻¹
    have hlist : (intList 1 8).map (fun ℓ => c - ℓ) =
        (intList (2 * k + 1 + 1) (2 * k + 1 + 8)).reverse := by
      have h := intList_map_sub (2 * k + 1 + 1) (2 * k + 1 + 8) c
      rw [show c - (2 * k + 1 + 8) = 1 by dsimp [c]; ring,
        show c - (2 * k + 1 + 1) = 8 by dsimp [c]; ring] at h
      have := congrArg List.reverse h
      simpa using this.symm
    have hF : ∀ ℓ ∈ intList 1 8, F ℓ ∈ ofRankTwoU D ℓ := by
      intro ℓ hℓ
      have hmem : c - ℓ ∈ intList (2 * k + 1 + 1) (2 * k + 1 + 8) := by
        have : c - ℓ ∈ (intList 1 8).map (fun ℓ => c - ℓ) :=
          List.mem_map.2 ⟨ℓ, hℓ, rfl⟩
        rw [hlist] at this
        exact List.mem_reverse.1 this
      have h := MovesU.conj_mem hg0 (hf (c - ℓ) hmem)
      rw [show c - (c - ℓ) = ℓ by ring] at h
      exact (ofRankTwoU D ℓ).inv_mem h
    have hG : ∀ ℓ ∈ intList 1 8, G ℓ ∈ ofRankTwoU D ℓ := by
      intro ℓ hℓ
      have hmem : c - ℓ ∈ intList (2 * k + 1 + 1) (2 * k + 1 + 8) := by
        have : c - ℓ ∈ (intList 1 8).map (fun ℓ => c - ℓ) :=
          List.mem_map.2 ⟨ℓ, hℓ, rfl⟩
        rw [hlist] at this
        exact List.mem_reverse.1 this
      have h := MovesU.conj_mem hg0 (hg (c - ℓ) hmem)
      rw [show c - (c - ℓ) = ℓ by ring] at h
      exact (ofRankTwoU D ℓ).inv_mem h
    have hprod' : ((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).map f).prod =
        ((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).map g).prod := by
      simpa using hprod
    have hprodF : ((intList 1 8).map F).prod =
        (g0 * ((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).map f).prod * g0⁻¹)⁻¹ := by
      calc
        ((intList 1 8).map F).prod
            = (((intList 1 8).map (fun ℓ => c - ℓ)).map
                (fun j => (g0 * f j * g0⁻¹)⁻¹)).prod := by
              dsimp [F]
              simp [List.map_map, Function.comp_def]
        _ = (((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).reverse).map
              (fun j => (g0 * f j * g0⁻¹)⁻¹)).prod := by rw [hlist]
        _ = (g0 * ((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).map f).prod * g0⁻¹)⁻¹ := by
              rw [list_prod_conj_inv_reverse g0
                (intList (2 * k + 1 + 1) (2 * k + 1 + 8)) f]
    have hprodG : ((intList 1 8).map G).prod =
        (g0 * ((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).map g).prod * g0⁻¹)⁻¹ := by
      calc
        ((intList 1 8).map G).prod
            = (((intList 1 8).map (fun ℓ => c - ℓ)).map
                (fun j => (g0 * g j * g0⁻¹)⁻¹)).prod := by
              dsimp [G]
              simp [List.map_map, Function.comp_def]
        _ = (((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).reverse).map
              (fun j => (g0 * g j * g0⁻¹)⁻¹)).prod := by rw [hlist]
        _ = (g0 * ((intList (2 * k + 1 + 1) (2 * k + 1 + 8)).map g).prod * g0⁻¹)⁻¹ := by
              rw [list_prod_conj_inv_reverse g0
                (intList (2 * k + 1 + 1) (2 * k + 1 + 8)) g]
    have hprodFG : ((intList 1 8).map F).prod = ((intList 1 8).map G).prod := by
      rw [hprodF, hprodG, hprod]
    have huniq := unique_std D F G hF hG hprodFG
    intro j hj
    have hmem : c - j ∈ intList 1 8 := by
      have hjb := mem_intList_iff.1 hj
      dsimp [c] at hjb ⊢
      rw [mem_intList_iff]
      omega
    have h := huniq (c - j) hmem
    dsimp [F, G] at h
    have h' := congrArg Inv.inv h
    simp only [inv_inv] at h'
    have := congrArg (fun z => g0⁻¹ * z * g0) h'
    simpa [mul_assoc] using this

@[expose] noncomputable def ofRankTwo (D : RankTwoSystem X 8) : TitsSystem X 8 where
  U := ofRankTwoU D
  periodic i := by
    convert ofRankTwoU_add_mul D i 1 using 2
    ring
  ne_bot i := by
    exact D.roots.ne_bot (Rt 8 (i - 1)) (Rt_isRoot (by norm_num) (i - 1))
  comm := comm_ofRankTwo D
  unique := unique_ofRankTwo D
  moufang := moufang_ofRankTwo D

theorem ofRankTwo_U (D : RankTwoSystem X 8) {j : ℤ} (h1 : 1 ≤ j) (h2 : j ≤ 8) :
    (ofRankTwo D).U j = D.root j :=
  ofRankTwoU_eq_root D h1 h2

theorem U_eq_win (D : RankTwoSystem X 8) : D.U = win (ofRankTwo D).U 1 8 := by
  change D.U = win (ofRankTwoU D) 1 8
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (D.U : Set X) := hx
    rw [D.roots.carrier_eq] at hx'
    exact chainProd_le_win_std D (by norm_num) (by norm_num) hx'
  · refine iSup₂_le fun k hk => ?_
    simp only [Set.mem_Icc] at hk
    rw [ofRankTwoU_eq_root D hk.1 hk.2]
    exact D.root_le_U hk.1 hk.2

theorem center_win_ne_bot (D : RankTwoSystem X 8) :
    Subgroup.centralizer (win (ofRankTwo D).U 1 8 : Set X) ⊓ win (ofRankTwo D).U 1 8 ≠ ⊥ := by
  rw [← U_eq_win]
  intro hbot
  have hne : D.U ≠ ⊥ := by
    intro h
    have hroot : D.root 1 = ⊥ :=
      le_bot_iff.1 (h ▸ D.root_le_U (by norm_num) (by norm_num))
    exact D.roots.ne_bot 1 ⟨by norm_num, by norm_num⟩ hroot
  haveI : Nontrivial ↥D.U := (Subgroup.nontrivial_iff_ne_bot D.U).2 hne
  haveI : Group.IsNilpotent ↥D.U := D.isSplit.1
  have hcenter : Subgroup.center ↥D.U ≠ ⊥ := Group.IsNilpotent.center_ne_bot (G := ↥D.U)
  apply hcenter
  rw [eq_bot_iff]
  intro u hu
  have huX : (u : X) ∈ Subgroup.centralizer (D.U : Set X) ⊓ D.U := by
    refine ⟨?_, u.2⟩
    intro v hv
    have h := Subgroup.mem_center_iff.1 hu ⟨v, hv⟩
    simpa using congrArg Subtype.val h
  have hzero : (u : X) ∈ (⊥ : Subgroup X) := by
    rw [← hbot]
    exact huX
  simpa using hzero

end CFSG.GH74.Tits83

end
