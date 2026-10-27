module

public import CFSG.GH74.BNPair.Cells
public import CFSG.GH74.BNPair.ChainProdFun
public import CFSG.GH74.Tits83.Defs
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {X : Type u} [Group X]

@[expose] def ofRankTwoU (D : RankTwoSystem X 8) (j : ℤ) : Subgroup X :=
  D.root (Rt 8 (j - 1))

theorem ofRankTwoU_add_mul (D : RankTwoSystem X 8) (j k : ℤ) :
    ofRankTwoU D (j + 16 * k) = ofRankTwoU D j := by
  unfold ofRankTwoU
  have h := Rt_add_mul 8 (j - 1) k
  change D.root (Rt 8 (j + 16 * k - 1)) = D.root (Rt 8 (j - 1))
  rw [show j + 16 * k - 1 = (j - 1) + 2 * (8 : ℤ) * k by ring]
  exact congrArg D.root h

@[expose] def MovesU (D : RankTwoSystem X 8) (g : X) (π : ℤ → ℤ) : Prop :=
  ∀ j, (ofRankTwoU D j).map (MulAut.conj g).toMonoidHom = ofRankTwoU D (π j)

namespace MovesU

variable {D : RankTwoSystem X 8}

theorem one : MovesU D (1 : X) (fun x => x) := by
  intro j
  ext x
  simp [Subgroup.mem_map]

theorem mul {g h : X} {π ρ : ℤ → ℤ} (hg : MovesU D g π) (hh : MovesU D h ρ) :
    MovesU D (g * h) (π ∘ ρ) := by
  intro j
  rw [CFSG.LieType.Steinberg.map_conj_mul, hh j, hg (ρ j)]
  rfl

theorem conj_mem {g : X} {π : ℤ → ℤ} (hg : MovesU D g π) {j : ℤ} {x : X}
    (hx : x ∈ ofRankTwoU D j) : g * x * g⁻¹ ∈ ofRankTwoU D (π j) := by
  have h : g * x * g⁻¹ ∈ (ofRankTwoU D j).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rwa [hg j] at h

theorem inv_shift {g : X} {c : ℤ} (hg : MovesU D g (· + c)) :
    MovesU D g⁻¹ (· - c) := by
  intro j
  have h := hg (j - c)
  have h' : (ofRankTwoU D (j - c)).map (MulAut.conj g).toMonoidHom = ofRankTwoU D j := by
    simpa [sub_add_cancel] using h
  simpa using CFSG.LieType.Steinberg.map_conj_inv_of_map_conj h'

theorem inv_refl {g : X} {c : ℤ} (hg : MovesU D g (c - ·)) :
    MovesU D g⁻¹ (c - ·) := by
  intro j
  have h := hg (c - j)
  have h' : (ofRankTwoU D (c - j)).map (MulAut.conj g).toMonoidHom = ofRankTwoU D j := by
    simpa using h
  simpa using CFSG.LieType.Steinberg.map_conj_inv_of_map_conj h'

theorem map_win_shift {g : X} {c : ℤ} (hg : MovesU D g (· + c)) (a b : ℤ) :
    (win (ofRankTwoU D) a b).map (MulAut.conj g).toMonoidHom =
      win (ofRankTwoU D) (a + c) (b + c) := by
  simp only [win, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (k + c) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by rw [hg]))
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (k - c) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by simpa [sub_add_cancel] using (hg (k - c)).symm))

theorem map_win_refl {g : X} {c : ℤ} (hg : MovesU D g (c - ·)) (a b : ℤ) :
    (win (ofRankTwoU D) a b).map (MulAut.conj g).toMonoidHom =
      win (ofRankTwoU D) (c - b) (c - a) := by
  simp only [win, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (c - k) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by rw [hg]))
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (c - k) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by simpa [sub_sub_cancel] using (hg (c - k)).symm))

end MovesU

@[expose] def V (D : RankTwoSystem X 8) : Set X :=
  chainProd D.root (intList 2 8)

@[expose] def Vminus (D : RankTwoSystem X 8) : Set X :=
  chainProd D.root ((intList 2 8).map Neg.neg)

theorem movesU_of_actsPos {D : RankTwoSystem X 8} {g : X} {f : ℤ → ℤ}
    (h : D.ActsPos g f) (h' : D.ActsPos g⁻¹ f) (hf : ∀ q, f (f q) = q) :
    MovesU D g (fun j => f (j - 1) + 1) := by
  intro j
  change (D.root (Rt 8 (j - 1))).map (MulAut.conj g).toMonoidHom =
    D.root (Rt 8 (f (j - 1) + 1 - 1))
  rw [show f (j - 1) + 1 - 1 = f (j - 1) by ring]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact h (j - 1) y hy
  · intro x hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := h' (f (j - 1)) x hx
      rw [hf, inv_inv] at this
      exact this
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem w₀_mul_self (D : RankTwoSystem X 8) : D.w₀ * D.w₀ = 1 := by
  have hrepr : D.w₀ = (D.w₂ * D.w₁) ^ 4 :=
    show altWord D.w₁ D.w₂ (2 * 4) = _ from altWord_two_mul D.w₁ D.w₂ 4
  have h : (D.w₁ * D.w₂) ^ 8 = 1 := D.rank2.dih.pow_eq_one
  have hinv : D.w₂ * D.w₁ = (D.w₁ * D.w₂)⁻¹ := by
    rw [mul_inv_rev, D.rank2.dih.inv_a, D.rank2.dih.inv_b]
  rw [hrepr, ← pow_add]
  rw [show (4 : ℕ) + 4 = 8 by norm_num, hinv, inv_pow, h, inv_one]

section Lifts

variable (D : RankTwoSystem X 8)

@[expose] noncomputable def liftOne : D.N :=
  Classical.choose (QuotientGroup.mk_surjective D.w₁)

@[expose] noncomputable def liftTwo : D.N :=
  Classical.choose (QuotientGroup.mk_surjective D.w₂)

theorem liftOne_mk : ((liftOne D : D.N) : D.Weyl) = D.w₁ :=
  Classical.choose_spec (QuotientGroup.mk_surjective D.w₁)

theorem liftTwo_mk : ((liftTwo D : D.N) : D.Weyl) = D.w₂ :=
  Classical.choose_spec (QuotientGroup.mk_surjective D.w₂)

theorem liftOne_inv_mk : (((liftOne D)⁻¹ : D.N) : D.Weyl) = D.w₁ :=
  CFSG.GH74.BNPair.RankTwoSystem.lift₁_inv (liftOne D) (liftOne_mk D)

theorem liftTwo_inv_mk : (((liftTwo D)⁻¹ : D.N) : D.Weyl) = D.w₂ :=
  CFSG.GH74.BNPair.RankTwoSystem.lift₂_inv (liftTwo D) (liftTwo_mk D)

theorem moves_liftOne :
    MovesU D ((liftOne D : D.N) : X) (fun j => 10 - j) := by
  have hf : (fun j : ℤ => (fun q : ℤ => 8 - q) (j - 1) + 1) = fun j => 10 - j := by
    funext j; ring
  rw [← hf]
  exact movesU_of_actsPos (D.actsPos_lift₁ (liftOne D) (liftOne_mk D))
    (D.actsPos_lift₁ ((liftOne D)⁻¹) (liftOne_inv_mk D)) (by intro q; ring)

theorem moves_liftTwo :
    MovesU D ((liftTwo D : D.N) : X) (fun j => 8 - j) := by
  have hf : (fun j : ℤ => (fun q : ℤ => 6 - q) (j - 1) + 1) = fun j => 8 - j := by
    funext j; ring
  rw [← hf]
  exact movesU_of_actsPos (D.actsPos_lift₂ (liftTwo D) (liftTwo_mk D))
    (D.actsPos_lift₂ ((liftTwo D)⁻¹) (liftTwo_inv_mk D)) (by intro q; ring)

theorem moves_shift_two :
    MovesU D ((((liftOne D * liftTwo D : D.N)) : X)) (· + 2) := by
  have h := MovesU.mul (moves_liftOne D) (moves_liftTwo D)
  convert h using 1
  funext j
  simp only [Function.comp_apply]
  ring

theorem moves_of_liftOne (m : D.N) (hm : (m : D.Weyl) = D.w₁) :
    MovesU D (m : X) (fun j => 10 - j) := by
  have hf : (fun j : ℤ => (fun q : ℤ => 8 - q) (j - 1) + 1) = fun j => 10 - j := by
    funext j; ring
  rw [← hf]
  exact movesU_of_actsPos (D.actsPos_lift₁ m hm)
    (D.actsPos_lift₁ (m⁻¹) (CFSG.GH74.BNPair.RankTwoSystem.lift₁_inv m hm)) (by intro q; ring)

theorem moves_of_liftTwo (m : D.N) (hm : (m : D.Weyl) = D.w₂) :
    MovesU D (m : X) (fun j => 8 - j) := by
  have hf : (fun j : ℤ => (fun q : ℤ => 6 - q) (j - 1) + 1) = fun j => 8 - j := by
    funext j; ring
  rw [← hf]
  exact movesU_of_actsPos (D.actsPos_lift₂ m hm)
    (D.actsPos_lift₂ (m⁻¹) (CFSG.GH74.BNPair.RankTwoSystem.lift₂_inv m hm)) (by intro q; ring)

end Lifts

@[expose] noncomputable def liftZero (D : RankTwoSystem X 8) : D.N :=
  D.lift D.w₀

theorem liftZero_mk (D : RankTwoSystem X 8) : ((liftZero D : D.N) : D.Weyl) = D.w₀ :=
  D.lift_mk D.w₀

theorem liftZero_inv_mk (D : RankTwoSystem X 8) :
    (((liftZero D)⁻¹ : D.N) : D.Weyl) = D.w₀ := by
  rw [QuotientGroup.mk_inv, liftZero_mk, inv_eq_of_mul_eq_one_right (w₀_mul_self D)]

@[expose] noncomputable def VminusSub (D : RankTwoSystem X 8) : Subgroup X :=
  Classical.choose (D.chainProd_good_plist (k := 6) (by norm_num) 9).1

theorem coe_VminusSub (D : RankTwoSystem X 8) :
    (VminusSub D : Set X) = chainProd D.root ((plist 9 6).map (Rt 8)) :=
  Classical.choose_spec (D.chainProd_good_plist (k := 6) (by norm_num) 9).1

theorem plist_nine_map_Rt :
    (plist 9 6).map (Rt 8) = (intList 2 8).map Neg.neg := by
  apply List.ext_getElem
  · simp [plist, intList]
  · intro t h1 h2
    simp only [plist, intList, List.length_map, List.length_range, List.getElem_map,
      List.getElem_range] at h1 h2 ⊢
    have ht : t < 7 := by simpa using h1
    rw [Rt_of_ge (by omega) (by omega)]
    ring

theorem coe_VminusSub' (D : RankTwoSystem X 8) :
    (VminusSub D : Set X) = Vminus D := by
  rw [coe_VminusSub, plist_nine_map_Rt]
  rfl

theorem chainProd_comp {A : ℤ → Subgroup X} (f : ℤ → ℤ) (l : List ℤ) :
    chainProd A (l.map f) = chainProd (fun q => A (f q)) l := by
  simp only [chainProd]
  rw [List.map_map]
  rfl

theorem mem_plist_iff {p q : ℤ} {k : ℕ} : q ∈ plist p k ↔ p ≤ q ∧ q ≤ p + k := by
  simp only [plist, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(q - p).toNat, by omega, by omega⟩

theorem conj_liftOne_Vminus {D : RankTwoSystem X 8} {x : X} (hx : x ∈ Vminus D) :
    ((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹ ∈ Vminus D := by
  have hact := D.actsPos_lift₁ (liftOne D) (liftOne_mk D)
  have hact' := D.actsPos_lift₁ ((liftOne D)⁻¹) (liftOne_inv_mk D)
  rw [← coe_VminusSub'] at hx ⊢
  rw [coe_VminusSub] at hx ⊢
  have hx' : x ∈ chainProd (fun q => D.root (Rt 8 q)) (plist 9 6) := by
    rwa [← chainProd_comp]
  have hconj := chainProd_conj_mem (fun q => D.root (Rt 8 q)) (VminusSub D)
    ((liftOne D : D.N) : X) (plist 9 6) (fun q hq y hy => ?_) x hx'
  · change _ ∈ (VminusSub D : Set X) at hconj
    rw [coe_VminusSub, chainProd_comp] at hconj
    exact hconj
  · have hq' := mem_plist_iff.1 hq
    have h1 := hact q y hy
    change _ ∈ D.root (Rt 8 (8 - q)) at h1
    have e : Rt 8 (8 - q) = Rt 8 (24 - q) := by
      rw [← Rt_add_mul 8 (8 - q) 1]
      congr 1
      ring
    rw [e] at h1
    rw [← SetLike.mem_coe, coe_VminusSub]
    refine mem_chainProd_of_mem D.root (List.mem_map.2 ⟨24 - q, ?_, rfl⟩) h1
    rw [mem_plist_iff]
    omega

theorem tauA_eight : tauA 8 8 = fun q : ℤ => q - 8 := by
  funext q
  unfold tauA
  rw [if_pos (show Even (8 : ℕ) from ⟨4, by norm_num⟩)]
  ring

theorem conj_liftZero_V {D : RankTwoSystem X 8} {x : X} (hx : x ∈ V D) :
    ((liftZero D : D.N) : X) * x * (((liftZero D : D.N) : X))⁻¹ ∈ Vminus D := by
  have hm : ((liftZero D : D.N) : D.Weyl) = altWord D.w₁ D.w₂ 8 := by
    simpa [RankTwoSystem.w₀] using liftZero_mk D
  have hact : D.ActsPos ((liftZero D : D.N) : X) (fun q => q - 8) := by
    simpa [tauA_eight] using D.actsPos_altWord₁ 8 (liftZero D) hm
  unfold V at hx
  rw [← coe_VminusSub']
  rw [coe_VminusSub]
  have hconj := chainProd_conj_mem D.root (VminusSub D) ((liftZero D : D.N) : X)
    (intList 2 8) (fun k hk y hy => ?_) x hx
  · change _ ∈ (VminusSub D : Set X) at hconj
    rw [coe_VminusSub, chainProd_comp] at hconj
    exact hconj
  · obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt 8 (k - 1)) := by
      rwa [Rt_pos_idx (by omega) (by omega)]
    have h1 := hact (k - 1) y hy'
    change _ ∈ D.root (Rt 8 (k - 1 - 8)) at h1
    have e : Rt 8 (k - 1 - 8) = Rt 8 (k + 7) := by
      rw [← Rt_add_mul 8 (k - 1 - 8) 1]
      congr 1
      ring
    rw [e] at h1
    change _ ∈ (VminusSub D : Set X)
    rw [coe_VminusSub]
    refine mem_chainProd_of_mem D.root (List.mem_map.2 ⟨k + 7, ?_, rfl⟩) h1
    rw [mem_plist_iff]
    omega

theorem conj_liftZero_inv_Uminus {D : RankTwoSystem X 8} {x : X} (hx : x ∈ D.Uminus) :
    ((liftZero D)⁻¹ : X) * x * (((liftZero D)⁻¹ : X))⁻¹ ∈ D.U := by
  have hm : (((liftZero D)⁻¹ : D.N) : D.Weyl) = altWord D.w₁ D.w₂ 8 := by
    simpa [RankTwoSystem.w₀] using liftZero_inv_mk D
  have hact : D.ActsPos (((liftZero D)⁻¹ : D.N) : X) (fun q => q - 8) := by
    simpa [tauA_eight] using D.actsPos_altWord₁ 8 ((liftZero D)⁻¹) hm
  refine chainProd_conj_mem D.root D.U (((liftZero D)⁻¹ : D.N) : X)
    ((intList 1 8).map Neg.neg) (fun k hk y hy => ?_) x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
  obtain ⟨hj1, hj2⟩ := mem_intList_iff.1 hj
  have hpos : Rt 8 (j + 7) = -j := by
    rw [Rt_of_ge (by omega) (by omega)]
    ring
  have hy' : y ∈ D.root (Rt 8 (j + 7)) := by rwa [hpos]
  have h1 := hact (j + 7) y hy'
  change _ ∈ D.root (Rt 8 (j + 7 - 8)) at h1
  have e : Rt 8 (j + 7 - 8) = j := by
    rw [show j + 7 - 8 = j - 1 by ring, Rt_pos_idx (by omega) (by omega)]
  rw [e] at h1
  exact D.root_le_U hj1 hj2 h1

theorem H_conj_X1 {D : RankTwoSystem X 8} {h : X} (hh : h ∈ D.B ⊓ D.N) {x : X}
    (hx : x ∈ D.root 1) : h * x * h⁻¹ ∈ D.root 1 :=
  D.roots.invariant 1 ⟨by norm_num, by norm_num⟩ h hh x hx

theorem Vminus_subset_Vm {D : RankTwoSystem X 8} {x : X} (hx : x ∈ Vminus D) : x ∈ D.Vm := by
  unfold Vminus at hx
  rw [D.mem_Vm_iff, ← D.coe_Vm]
  refine chainProd_subset D.root D.Vm _ (fun k hk => ?_) hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
  obtain ⟨hj1, hj2⟩ := mem_intList_iff.1 hj
  exact D.root_le_V D.coe_Vm (by omega) (by omega)

theorem w₀_comm_w₁ (D : RankTwoSystem X 8) : D.w₀ * D.w₁ = D.w₁ * D.w₀ := by
  have hrepr : D.w₀ = (D.w₂ * D.w₁) ^ 4 :=
    show altWord D.w₁ D.w₂ (2 * 4) = _ from altWord_two_mul D.w₁ D.w₂ 4
  have hcomm : (D.w₁ * D.w₂) ^ 4 = (D.w₂ * D.w₁) ^ 4 := by
    have h8 : (D.w₁ * D.w₂) ^ 8 = 1 := D.rank2.dih.pow_eq_one
    have h42 : (D.w₁ * D.w₂) ^ 4 * (D.w₁ * D.w₂) ^ 4 = 1 := by
      rw [← pow_add]
      exact h8
    have hinv : (D.w₂ * D.w₁) = (D.w₁ * D.w₂)⁻¹ := by
      rw [mul_inv_rev, D.rank2.dih.inv_a, D.rank2.dih.inv_b]
    rw [hinv, inv_pow, inv_eq_of_mul_eq_one_right h42]
  have key : ∀ k : ℕ, D.w₁ * (D.w₂ * D.w₁) ^ k = (D.w₁ * D.w₂) ^ k * D.w₁ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc D.w₁ * (D.w₂ * D.w₁) ^ (k + 1)
          = (D.w₁ * (D.w₂ * D.w₁) ^ k) * (D.w₂ * D.w₁) := by rw [pow_succ]; group
        _ = ((D.w₁ * D.w₂) ^ k * D.w₁) * (D.w₂ * D.w₁) := by rw [ih]
        _ = (D.w₁ * D.w₂) ^ (k + 1) * D.w₁ := by rw [pow_succ]; group
  rw [hrepr, key 4, hcomm]

theorem w₀_comm_w₂ (D : RankTwoSystem X 8) : D.w₀ * D.w₂ = D.w₂ * D.w₀ := by
  have hrepr : D.w₀ = (D.w₁ * D.w₂) ^ 4 := by
    have h1 : D.w₀ = altWord D.w₂ D.w₁ 8 := by
      rw [RankTwoSystem.w₀]
      exact D.rank2.dih.altWord_eq
    rw [h1]
    exact show altWord D.w₂ D.w₁ (2 * 4) = _ from altWord_two_mul D.w₂ D.w₁ 4
  have hcomm : (D.w₁ * D.w₂) ^ 4 = (D.w₂ * D.w₁) ^ 4 := by
    have h8 : (D.w₁ * D.w₂) ^ 8 = 1 := D.rank2.dih.pow_eq_one
    have h42 : (D.w₁ * D.w₂) ^ 4 * (D.w₁ * D.w₂) ^ 4 = 1 := by
      rw [← pow_add]
      exact h8
    have hinv : (D.w₂ * D.w₁) = (D.w₁ * D.w₂)⁻¹ := by
      rw [mul_inv_rev, D.rank2.dih.inv_a, D.rank2.dih.inv_b]
    rw [hinv, inv_pow, inv_eq_of_mul_eq_one_right h42]
  have key : ∀ k : ℕ, D.w₂ * (D.w₁ * D.w₂) ^ k = (D.w₂ * D.w₁) ^ k * D.w₂ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc D.w₂ * (D.w₁ * D.w₂) ^ (k + 1)
          = (D.w₂ * (D.w₁ * D.w₂) ^ k) * (D.w₁ * D.w₂) := by rw [pow_succ]; group
        _ = ((D.w₂ * D.w₁) ^ k * D.w₂) * (D.w₁ * D.w₂) := by rw [ih]
        _ = (D.w₂ * D.w₁) ^ (k + 1) * D.w₂ := by rw [pow_succ]; group
  rw [hrepr, key 4, ← hcomm]

theorem comm_std (D : RankTwoSystem X 8) {a b : ℤ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 8)
    {x y : X} (hx : x ∈ D.root a) (hy : y ∈ D.root b) :
    ⁅x, y⁆ ∈ chainProd D.root (intList (a + 1) (b - 1)) := by
  obtain ⟨V₁, hV₁c, -, hV₁l, -⟩ := D.roots.subgroup (a + 1) b (by omega) (by omega) hb
  obtain ⟨V₂, hV₂c, -, -, hV₂r⟩ := D.roots.subgroup a (b - 1) ha (by omega) (by omega)
  have hyV₁ : y ∈ V₁ := by
    have : y ∈ (V₁ : Set X) := by
      rw [hV₁c]
      exact mem_chainProd_of_mem D.root (k := b) (mem_intList_iff.2 ⟨by omega, le_rfl⟩) hy
    exact this
  have hxV₂ : x ∈ V₂ := by
    have : x ∈ (V₂ : Set X) := by
      rw [hV₂c]
      exact mem_chainProd_of_mem D.root (k := a) (mem_intList_iff.2 ⟨le_rfl, by omega⟩) hx
    exact this
  have hz₁ : ⁅x, y⁆ ∈ V₁ := by
    have hx' : x ∈ D.root (a + 1 - 1) := by simpa using hx
    have := hV₁l (by omega) x hx' y hyV₁
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact V₁.mul_mem this (V₁.inv_mem hyV₁)
  have hz₂ : ⁅x, y⁆ ∈ V₂ := by
    have hy' : y ∈ D.root (b - 1 + 1) := by simpa using hy
    have := hV₂r (by omega) y hy' x⁻¹ (V₂.inv_mem hxV₂)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V₂.mul_mem hxV₂ this
  have hz₁' : ⁅x, y⁆ ∈ chainProd D.root (intList (a + 1) b) := by
    have : ⁅x, y⁆ ∈ (V₁ : Set X) := hz₁
    rwa [hV₁c] at this
  have hz₂' : ⁅x, y⁆ ∈ chainProd D.root (intList a (b - 1)) := by
    have : ⁅x, y⁆ ∈ (V₂ : Set X) := hz₂
    rwa [hV₂c] at this
  obtain ⟨f₁, hf₁, he₁⟩ :=
    exists_fun_of_mem_chainProd D.root _ (intList_nodup _ _) _ hz₁'
  obtain ⟨f₂, hf₂, he₂⟩ :=
    exists_fun_of_mem_chainProd D.root _ (intList_nodup _ _) _ hz₂'
  have key := D.roots.unique
    (f := fun k => if a + 1 ≤ k ∧ k ≤ b then f₁ k else 1)
    (g := fun k => if a ≤ k ∧ k ≤ b - 1 then f₂ k else 1)
    (fun k hk => by
      by_cases h : a + 1 ≤ k ∧ k ≤ b
      · simpa [h] using hf₁ k (mem_intList_iff.2 h)
      · simpa [h] using (D.root k).one_mem)
    (fun k hk => by
      by_cases h : a ≤ k ∧ k ≤ b - 1
      · simpa [h] using hf₂ k (mem_intList_iff.2 h)
      · simpa [h] using (D.root k).one_mem)
    (by
      rw [intList_prod_pad (l := 1) (by omega) (by omega) (by omega) f₁,
        intList_prod_pad (l := 1) (by omega) (by omega) (by omega) f₂, ← he₁, ← he₂]) b
    (mem_intList_iff.2 ⟨by omega, hb⟩)
  have hfb : f₁ b = 1 := by
    have h1 : a + 1 ≤ b ∧ b ≤ b := ⟨by omega, le_rfl⟩
    have h2 : ¬(a ≤ b ∧ b ≤ b - 1) := by omega
    simpa [h1, h2] using key
  have hsnoc : intList (a + 1) b = intList (a + 1) (b - 1) ++ [b] := intList_snoc (by omega)
  rw [he₁, hsnoc, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hfb]
  exact prod_mem_chainProd D.root f₁ _ (fun k hk => hf₁ k (by
    have := mem_intList_iff.1 hk
    exact mem_intList_iff.2 ⟨this.1, by omega⟩))

theorem exists_moves_shift (D : RankTwoSystem X 8) (s : ℤ) :
    ∃ g : X, MovesU D g (· + 2 * s) := by
  let g₀ : X := ((liftOne D * liftTwo D : D.N) : X)
  have h₀ : MovesU D g₀ (· + 2) := moves_shift_two D
  have h₀' : MovesU D g₀⁻¹ (· - 2) := MovesU.inv_shift h₀
  have key : ∀ n : ℕ, MovesU D (g₀ ^ n) (· + 2 * (n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using MovesU.one (D := D)
    | succ n ih =>
      have h := MovesU.mul ih h₀
      convert h using 1
      · rw [pow_succ]
      · funext j
        simp only [Function.comp_apply]
        push_cast
        ring
  have key' : ∀ n : ℕ, MovesU D ((g₀⁻¹) ^ n) (· - 2 * (n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using MovesU.one (D := D)
    | succ n ih =>
      have h := MovesU.mul ih h₀'
      convert h using 1
      · rw [pow_succ]
      · funext j
        simp only [Function.comp_apply]
        push_cast
        ring
  rcases Int.eq_nat_or_neg s with ⟨n, rfl | rfl⟩
  · exact ⟨g₀ ^ n, by simpa using key n⟩
  · refine ⟨(g₀⁻¹) ^ n, ?_⟩
    convert key' n using 1
    funext j
    push_cast
    ring

theorem exists_moves_refl (D : RankTwoSystem X 8) (c : ℤ) (hc : Even c) :
    ∃ g : X, MovesU D g (c - ·) := by
  rcases hc with ⟨k, hk⟩
  have hc' : c = 10 + 2 * (k - 5) := by omega
  subst hc'
  obtain ⟨g, hg⟩ := exists_moves_shift D (k - 5)
  refine ⟨g * ((liftOne D : D.N) : X), ?_⟩
  have h := MovesU.mul hg (moves_liftOne D)
  convert h using 1
  funext j
  simp only [Function.comp_apply]
  ring

end CFSG.GH74.Tits83

end
