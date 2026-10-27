module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Matrix CFSG.AGLEmbedding CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace O8p2

def Amat (c : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, c 0, c 1, c 2; c 0, 0, c 3, c 4; c 1, c 3, 0, c 5; c 2, c 4, c 5, 0]

theorem Amat_add (c c' : Fin 6 → ZMod 2) : Amat (c + c') = Amat c + Amat c' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Amat]

theorem Amat_zero : Amat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Amat]

def Tm8 (c : Fin 6 → ZMod 2) : Matrix ι8 ι8 (ZMod 2) := fromBlocks 1 (Amat c) 0 1

theorem Tm8_mul (c c' : Fin 6 → ZMod 2) : Tm8 c * Tm8 c' = Tm8 (c + c') := by
  simp [Tm8, fromBlocks_multiply, Amat_add, add_comm]

theorem Tm8_zero : Tm8 0 = 1 := by simp [Tm8, Amat_zero]

theorem add_self_fun (c : Fin 6 → ZMod 2) : c + c = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  revert i
  have : ∀ x : ZMod 2, x + x = 0 := by decide
  exact fun i => this _

theorem Tm8_mul_self (c : Fin 6 → ZMod 2) : Tm8 c * Tm8 c = 1 := by
  rw [Tm8_mul, add_self_fun, Tm8_zero]

def Tgl (c : Fin 6 → ZMod 2) : GL ι8 (ZMod 2) :=
  ⟨Tm8 c, Tm8 c, Tm8_mul_self c, Tm8_mul_self c⟩

theorem Tgl_mul (c c' : Fin 6 → ZMod 2) : Tgl c * Tgl c' = Tgl (c + c') :=
  Units.ext (Tm8_mul c c')

theorem Tgl_zero : Tgl 0 = 1 := Units.ext Tm8_zero


def ex (i : Fin 4) : V8 := Pi.single (Sum.inl i) 1

def pr6 : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

theorem gl_ext_cols {g h : GL ι8 (ZMod 2)} (H : ∀ j < 8, actG g (2 ^ j) = actG h (2 ^ j)) :
    g = h := by
  apply gl_ext_act
  intro c hc
  have hcols : colsB g = colsB h := by
    unfold colsB
    exact List.map_congr_left (fun j hj => H j (List.mem_range.1 hj))
  rw [actG_eq_applyB g hc, actG_eq_applyB h hc, hcols]

theorem Tgl_single_act : ∀ k : Fin 6, ∀ j < 8,
    actG (Tgl (Pi.single k 1)) (2 ^ j) =
      eAct (bc (ex (pr6 k).1)) (bc (ex (pr6 k).2)) (2 ^ j) := by
  decide +kernel

theorem Tgl_single_eq (k : Fin 6) :
    Tgl (Pi.single k 1) = eichGL (ex (pr6 k).1) (ex (pr6 k).2) := by
  apply gl_ext_cols
  intro j hj
  rw [actG_eichGL _ _ (show 2 ^ j < 256 by
    calc 2 ^ j < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hj
      _ = 256 := by norm_num)]
  exact Tgl_single_act k j hj

theorem Tgl_single_mem (k : Fin 6) (a : ZMod 2) : Tgl (Pi.single k a) ∈ Om8 := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · rw [Pi.single_zero, Tgl_zero]; exact one_mem _
  · rw [Tgl_single_eq]; exact eichGL_mem _ _

theorem Tgl_mem (c : Fin 6 → ZMod 2) : Tgl c ∈ Om8 := by
  have key : ∀ t : Finset (Fin 6), Tgl (∑ k ∈ t, Pi.single k (c k)) ∈ Om8 := by
    intro t
    induction t using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Tgl_zero]; exact one_mem _
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, ← Tgl_mul]
      exact mul_mem (Tgl_single_mem a (c a)) ih
  have := key Finset.univ
  rwa [Finset.univ_sum_single] at this


def theta8 : Multiplicative (Fin 6 → ZMod 2) →* Om8 where
  toFun c := ⟨Tgl c.toAdd, Tgl_mem _⟩
  map_one' := Subtype.ext (by simpa using Tgl_zero)
  map_mul' x y := Subtype.ext (by simp [Tgl_mul])

theorem Tgl_entry (c : Fin 6 → ZMod 2) (i j : Fin 4) :
    (Tgl c : Matrix ι8 ι8 (ZMod 2)) (Sum.inl i) (Sum.inr j) = Amat c i j := by
  simp [Tgl, Tm8]

theorem theta8_injective : Function.Injective theta8 := by
  intro x y h
  have h' : Tgl x.toAdd = Tgl y.toAdd := congrArg Subtype.val h
  have e : ∀ i j : Fin 4, Amat x.toAdd i j = Amat y.toAdd i j := fun i j => by
    rw [← Tgl_entry, ← Tgl_entry, h']
  apply Multiplicative.toAdd.injective
  funext k
  fin_cases k
  · exact (by simpa [Amat] using e 0 1)
  · exact (by simpa [Amat] using e 0 2)
  · exact (by simpa [Amat] using e 0 3)
  · exact (by simpa [Amat] using e 1 2)
  · exact (by simpa [Amat] using e 1 3)
  · exact (by simpa [Amat] using e 2 3)

theorem pow_two_eq_one6 (a : Multiplicative (Fin 6 → ZMod 2)) : a ^ 2 = 1 := by
  revert a
  decide

theorem om8_exists_E64 : ∃ E : Subgroup Om8, IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 6 := by
  refine ⟨theta8.range, isElemAbelian_range theta8 pow_two_eq_one6, ?_⟩
  rw [card_range_eq_of_injective theta8 theta8_injective, Nat.card_congr Multiplicative.toAdd,
    Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_zmod]


def ey (j : Fin 4) : V8 := Pi.single (Sum.inr j) 1

noncomputable def yGL : GL ι8 (ZMod 2) := eichGL (ex 0) (ey 1) * eichGL (ex 1) (ey 0)

noncomputable def sGL : GL ι8 (ZMod 2) := eichGL (ex 2) (ey 3)

theorem yGL_mem : yGL ∈ Om8 := mul_mem (eichGL_mem _ _) (eichGL_mem _ _)

theorem sGL_mem : sGL ∈ Om8 := eichGL_mem _ _

theorem actG_mul_of {g h : GL ι8 (ZMod 2)} {A B : ℕ → ℕ} (hg : ∀ c < 256, actG g c = A c)
    (hh : ∀ c < 256, actG h c = B c) : ∀ c < 256, actG (g * h) c = A (B c) := by
  intro c hc
  rw [actG_mul, ← hh c hc]
  exact hg _ (actG_lt h c)

theorem actG_eichGL_of (u w : V8) : ∀ c < 256, actG (eichGL u w) c = eAct (bc u) (bc w) c :=
  fun _ hc => actG_eichGL u w hc

def yA (c : ℕ) : ℕ := eAct (bc (ex 0)) (bc (ey 1)) (eAct (bc (ex 1)) (bc (ey 0)) c)

def sA (c : ℕ) : ℕ := eAct (bc (ex 2)) (bc (ey 3)) c

theorem actG_yGL : ∀ c < 256, actG yGL c = yA c :=
  actG_mul_of (A := fun c => eAct (bc (ex 0)) (bc (ey 1)) c)
    (B := fun c => eAct (bc (ex 1)) (bc (ey 0)) c) (actG_eichGL_of _ _) (actG_eichGL_of _ _)

theorem actG_sGL : ∀ c < 256, actG sGL c = sA c := actG_eichGL_of _ _

theorem yGL_pow_three : yGL ^ 3 = 1 := by
  have h : ∀ c < 256, actG (yGL * yGL * yGL) c = yA (yA (yA c)) :=
    actG_mul_of (A := fun c => yA (yA c)) (B := yA)
      (actG_mul_of (A := yA) (B := yA) actG_yGL actG_yGL) actG_yGL
  have h3 : ∀ j < 8, yA (yA (yA (2 ^ j))) = 2 ^ j := by decide +kernel
  have : yGL * yGL * yGL = 1 := by
    apply gl_ext_cols
    intro j hj
    have hj' : 2 ^ j < 256 := by
      calc 2 ^ j < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hj
        _ = 256 := by norm_num
    rw [h _ hj', h3 j hj, actG_one hj']
  simpa [pow_succ] using this

theorem yGL_ne_one : yGL ≠ 1 := by
  intro h
  have h1 : actG yGL 1 = actG 1 1 := by rw [h]
  rw [actG_yGL 1 (by norm_num), actG_one (by norm_num)] at h1
  revert h1
  decide +kernel

theorem sGL_sq : sGL ^ 2 = 1 := by
  have h : ∀ c < 256, actG (sGL * sGL) c = sA (sA c) :=
    actG_mul_of (A := sA) (B := sA) actG_sGL actG_sGL
  have h2 : ∀ j < 8, sA (sA (2 ^ j)) = 2 ^ j := by decide +kernel
  have : sGL * sGL = 1 := by
    apply gl_ext_cols
    intro j hj
    have hj' : 2 ^ j < 256 := by
      calc 2 ^ j < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hj
        _ = 256 := by norm_num
    rw [h _ hj', h2 j hj, actG_one hj']
  simpa [pow_two] using this

theorem sGL_ne_one : sGL ≠ 1 := by
  intro h
  have h1 : actG sGL 8 = actG 1 8 := by rw [h]
  rw [actG_sGL 8 (by norm_num), actG_one (by norm_num)] at h1
  revert h1
  decide +kernel

theorem yGL_comm_sGL : yGL * sGL = sGL * yGL := by
  have h1 : ∀ c < 256, actG (yGL * sGL) c = yA (sA c) :=
    actG_mul_of (A := yA) (B := sA) actG_yGL actG_sGL
  have h2 : ∀ c < 256, actG (sGL * yGL) c = sA (yA c) :=
    actG_mul_of (A := sA) (B := yA) actG_sGL actG_yGL
  have h3 : ∀ j < 8, yA (sA (2 ^ j)) = sA (yA (2 ^ j)) := by decide +kernel
  apply gl_ext_cols
  intro j hj
  have hj' : 2 ^ j < 256 := by
    calc 2 ^ j < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hj
      _ = 256 := by norm_num
  rw [h1 _ hj', h2 _ hj', h3 j hj]

theorem om8_exists_order3_normalizes_two : ∃ y : Om8, orderOf y = 3 ∧
    ∃ W : Subgroup Om8, IsPGroup 2 W ∧ W ≠ ⊥ ∧ y ∈ Subgroup.normalizer (W : Set Om8) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let y : Om8 := ⟨yGL, yGL_mem⟩
  let s : Om8 := ⟨sGL, sGL_mem⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using yGL_pow_three)
  have hy1 : y ≠ 1 := fun h => yGL_ne_one (congrArg Subtype.val h)
  have hs2 : s ^ 2 = 1 := Subtype.ext (by simpa using sGL_sq)
  have hs1 : s ≠ 1 := fun h => sGL_ne_one (congrArg Subtype.val h)
  have hc : Commute y s := Subtype.ext yGL_comm_sGL
  refine ⟨y, orderOf_eq_prime hy3 hy1, Subgroup.zpowers s,
    isPGroup_zpowers_of_pow_eq_one hs2, ?_, mem_normalizer_zpowers_of_commute hc⟩
  intro h
  have : s ∈ (⊥ : Subgroup Om8) := h ▸ Subgroup.mem_zpowers s
  exact hs1 (Subgroup.mem_bot.1 this)


end O8p2

open O8p2

theorem rank2D4At_holds (G : Type) [Group G] [Finite G] : Rank2D4At G := by
  intro X L hX hL hodd hcat
  obtain ⟨e⟩ := bridge_d4two hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk2 : ¬ 2 ∣ Nat.card π.ker := odd_card_ker L hkc hodd
  obtain ⟨E, hEel, hEcard⟩ := om8_exists_E64
  obtain ⟨W, hWp, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_two π hk2
    (isPGroup_of_isElemAbelian hEel)
    (by rw [MonoidHom.range_eq_top_of_surjective π hπs]; exact le_top)
  obtain ⟨hWel, hWcard⟩ := map_subtype_isElemAbelian_card π hWmap hWinj hEel
  exact CFSG.SectionRank.le_pRank Nat.one_lt_two (Subgroup.map_subtype_le _) hWel
    (hWcard.trans hEcard)

end CFSG.LocalAnalysis.GLTheoremA.CatB
