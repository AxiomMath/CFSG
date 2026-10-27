module

public import CFSG.CGT.Foote82.T66.G8Perm
import CFSG.Quasithin.Background.C58G64DirectLin
public import CFSG.CGT.Foote82.T66.CitedBA

public section

namespace CFSG.CGT.Foote82

namespace G8Proof

open CFSG.Open CFSG.Quasithin.G11 Equiv Equiv.Perm

@[expose] def gk : Fin 9 → Perm (Fin 9) :=
  ![1, 1, 1, swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4, swap 2 6 * swap 3 4,
    swap 2 7 * swap 3 4, swap 2 8 * swap 3 4]

theorem gk_mem (k : Fin 9) : gk k ∈ altOn S7 := by
  refine mem_altOn_of ?_ ?_ ?_ <;> revert k <;> decide

theorem gk_two {k : Fin 9} (hk : k ∈ S7f) : gk k 2 = k := by
  revert k
  decide

theorem gk_zero (k : Fin 9) : gk k 0 = 0 := fix_zero_of_mem_altOn (gk_mem k)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (GLV V)} (φ : ↥G ≃* Perm (Fin 9))

noncomputable abbrev tr (σ : Perm (Fin 9)) : GLV V := ((φ.symm σ : ↥G) : GLV V)

theorem tr_mul (σ τ : Perm (Fin 9)) : tr φ (σ * τ) = tr φ σ * tr φ τ := by
  simp [tr, map_mul]

theorem tr_one : tr φ 1 = 1 := by simp [tr]

theorem tr_inv (σ : Perm (Fin 9)) : tr φ σ⁻¹ = (tr φ σ)⁻¹ := by simp [tr, map_inv]

theorem tr_apply_self (g : ↥G) : tr φ (φ g) = (g : GLV V) := by simp [tr]

noncomputable abbrev P (i j : Fin 9) : Submodule (ZMod 2) V :=
  commSpace (Subgroup.zpowers (tr φ (swap i j))) ⊤

theorem commSpace_tr_conj (σ τ : Perm (Fin 9)) :
    commSpace (Subgroup.zpowers (tr φ (σ * τ * σ⁻¹))) ⊤ =
      conjSub (tr φ σ) (commSpace (Subgroup.zpowers (tr φ τ)) ⊤) := by
  rw [tr_mul, tr_mul, tr_inv, CFSG.Quasithin.C58.G64D.commSpace_zpowers_eq_range,
    CFSG.Quasithin.C58.G64D.commSpace_zpowers_eq_range,
    CFSG.Quasithin.C58.G64D.datum_range_dl_conj]

theorem P_conj (σ : Perm (Fin 9)) (i j : Fin 9) :
    P φ (σ i) (σ j) = conjSub (tr φ σ) (P φ i j) := by
  rw [P, swap_apply_apply, commSpace_tr_conj]

theorem P_self (i : Fin 9) : P φ i i = ⊥ := by
  rw [P, swap_self, ← Equiv.Perm.one_def, tr_one, Subgroup.zpowers_one_eq_bot,
    commSpace_eq_bot_iff]
  intro k hk u _
  rw [Subgroup.mem_bot] at hk
  rw [hk]
  rfl

theorem P_comm (i j : Fin 9) : P φ i j = P φ j i := by
  rw [P, P, swap_comm]

theorem apply_sub_mem (a : GLV V) (u : V) :
    a u - u ∈ commSpace (Subgroup.zpowers a) ⊤ :=
  sub_mem_commSpace (Subgroup.mem_zpowers a) Submodule.mem_top

theorem P_le_sup (j k : Fin 9) : P φ j k ≤ P φ 0 j ⊔ P φ 0 k := by
  by_cases hjk : j = k
  · rw [hjk, P_self]
    exact bot_le
  by_cases hj : j = 0
  · rw [hj]
    exact le_sup_right
  by_cases hk : k = 0
  · rw [hk, P_comm]
    exact le_sup_left
  have e : P φ j k = conjSub (tr φ (swap 0 j)) (P φ 0 k) := by
    have h := P_conj φ (swap 0 j) 0 k
    rwa [swap_apply_left, swap_apply_of_ne_of_ne hk (Ne.symm hjk)] at h
  rw [e]
  intro v hv
  rw [mem_conjSub] at hv
  have hv' : v = (v - (tr φ (swap 0 j)).symm v) + (tr φ (swap 0 j)).symm v := by abel
  rw [hv']
  refine Submodule.add_mem_sup ?_ hv
  have e2 : v - (tr φ (swap 0 j)).symm v =
      (tr φ (swap 0 j)) ((tr φ (swap 0 j)).symm v) - (tr φ (swap 0 j)).symm v := by simp
  rw [e2]
  exact apply_sub_mem _ _

noncomputable abbrev U0 : Submodule (ZMod 2) V := ⨆ j, P φ 0 j

theorem P_le_U0 (i j : Fin 9) : P φ i j ≤ U0 φ :=
  (P_le_sup φ i j).trans (sup_le (le_iSup (fun j => P φ 0 j) i) (le_iSup (fun j => P φ 0 j) j))

theorem invariant_U0 : Invariant G (U0 φ) := by
  intro g hg u hu
  have hgσ : g = tr φ (φ ⟨g, hg⟩) := (tr_apply_self φ ⟨g, hg⟩).symm
  have key : ∀ j, ∀ v ∈ P φ 0 j, g v ∈ U0 φ := by
    intro j v hv
    have h := P_conj φ (φ ⟨g, hg⟩) 0 j
    have hv' : g v ∈ conjSub (tr φ (φ ⟨g, hg⟩)) (P φ 0 j) := by
      rw [← hgσ]
      exact apply_mem_conjSub hv
    rw [← h] at hv'
    exact P_le_U0 φ _ _ hv'
  have hle : U0 φ ≤ (U0 φ).comap (g : V →ₗ[ZMod 2] V) := iSup_le fun j v hv => key j v hv
  exact hle hu

theorem apply_eq_of_U0_eq_bot (h : U0 φ = ⊥) (σ : Perm (Fin 9)) (v : V) : tr φ σ v = v := by
  let K : Subgroup (Perm (Fin 9)) :=
    { carrier := {σ | ∀ v, tr φ σ v = v}
      mul_mem' := fun {a b} ha hb v => by
        show tr φ (a * b) v = v
        rw [tr_mul, LinearEquiv.mul_apply, hb, ha]
      one_mem' := fun v => by
        show tr φ 1 v = v
        rw [tr_one]
        rfl
      inv_mem' := fun {a} ha v => by
        show tr φ a⁻¹ v = v
        rw [tr_inv]
        conv_lhs => rw [← ha v]
        simp }
  have hswap : ∀ τ : Perm (Fin 9), τ.IsSwap → τ ∈ K := by
    rintro τ ⟨x, y, -, rfl⟩ v
    have hP : P φ x y = ⊥ := le_bot_iff.1 (h ▸ P_le_U0 φ x y)
    exact commSpace_eq_bot_iff.1 hP _ (Subgroup.mem_zpowers _) v Submodule.mem_top
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    exact fun τ hτ => hswap τ hτ
  have hσ : σ ∈ K := by
    rw [hK]
    exact Subgroup.mem_top σ
  exact hσ v

variable {φ} in
theorem apply_eq_of_mem_P02
    (hα : ∀ g : ↥G, φ g ∈ altOn S7 → ∀ w ∈ P φ 0 1, (g : GLV V) w = w)
    {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) (hσ2 : σ 2 = 2) {w : V} (hw : w ∈ P φ 0 2) :
    tr φ σ w = w := by
  set τ : Perm (Fin 9) := swap 1 2 with hτ
  have hττ : τ * τ = 1 := swap_mul_self 1 2
  set σ' : Perm (Fin 9) := τ * σ * τ with hσ'
  have e0 : τ 0 = 0 := by rw [hτ]; decide
  have e1 : τ 1 = 2 := by rw [hτ]; decide
  have e2 : τ 2 = 1 := by rw [hτ]; decide
  have hσ'A : σ' ∈ altOn S7 := by
    refine mem_altOn_of ?_ ?_ ?_
    · rw [hσ', map_mul, map_mul, sign_eq_of_mem_altOn' hσ]
      simp
    · rw [hσ', Perm.mul_apply, Perm.mul_apply, e0, fix_zero_of_mem_altOn hσ, e0]
    · rw [hσ', Perm.mul_apply, Perm.mul_apply, e1, hσ2, e2]
  have hfix := hα (φ.symm σ') (by simpa using hσ'A)
  have hP : P φ 0 2 = conjSub (tr φ τ) (P φ 0 1) := by
    have h := P_conj φ τ 0 1
    rwa [hτ, swap_apply_of_ne_of_ne (by decide) (by decide), swap_apply_left] at h
  rw [hP, mem_conjSub] at hw
  have htt : (tr φ τ).symm = tr φ τ := by
    have h1 : tr φ τ * tr φ τ = 1 := by rw [← tr_mul, hττ, tr_one]
    exact (inv_eq_of_mul_eq_one_right h1 : (tr φ τ)⁻¹ = tr φ τ)
  have hσeq : σ = τ * σ' * τ := by
    rw [hσ', ← mul_assoc, ← mul_assoc, hττ, one_mul, mul_assoc, hττ, mul_one]
  have hw' : tr φ τ w ∈ P φ 0 1 := by
    rw [← htt]
    exact hw
  have h2 : tr φ σ' (tr φ τ w) = tr φ τ w := hfix _ hw'
  have h1 : tr φ τ (tr φ τ w) = w := by
    have := congrArg (fun f : GLV V => f w)
      (show tr φ τ * tr φ τ = 1 by rw [← tr_mul, hττ, tr_one])
    simpa using this
  rw [hσeq, tr_mul, tr_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2, h1]

@[expose] noncomputable def theta (w : V) : (Fin 9 → ZMod 2) →ₗ[ZMod 2] V where
  toFun x := ∑ k, x k • tr φ (gk k) w
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem theta_apply (w : V) (x : Fin 9 → ZMod 2) :
    theta φ w x = ∑ k, x k • tr φ (gk k) w := rfl

theorem theta_ev (w : V) (k : Fin 9) : theta φ w (ev k) = tr φ (gk k) w := by
  rw [theta_apply, Finset.sum_eq_single k]
  · simp [ev]
  · intro b _ hb
    simp [ev, Pi.single_apply, hb]
  · simp

variable {φ} in
theorem tr_gk (hα : ∀ g : ↥G, φ g ∈ altOn S7 → ∀ w ∈ P φ 0 1, (g : GLV V) w = w)
    {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) {k : Fin 9} (hk : k ∈ S7f) {w : V}
    (hw : w ∈ P φ 0 2) : tr φ σ (tr φ (gk k) w) = tr φ (gk (σ k)) w := by
  have hσk : σ k ∈ S7f := by
    rw [mem_S7f] at hk ⊢
    constructor
    · intro h
      rw [← fix_zero_of_mem_altOn hσ] at h
      exact hk.1 (σ.injective h)
    · intro h
      rw [← fix_one_of_mem_altOn hσ] at h
      exact hk.2 (σ.injective h)
  set h : Perm (Fin 9) := (gk (σ k))⁻¹ * σ * gk k with hh
  have hhA : h ∈ altOn S7 :=
    (altOn S7).mul_mem ((altOn S7).mul_mem ((altOn S7).inv_mem (gk_mem _)) hσ) (gk_mem k)
  have hh2 : h 2 = 2 := by
    rw [hh, Perm.mul_apply, Perm.mul_apply, gk_two hk, Perm.inv_eq_iff_eq, gk_two hσk]
  have hfix := apply_eq_of_mem_P02 hα hhA hh2 hw
  have e : σ * gk k = gk (σ k) * h := by
    rw [hh, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← LinearEquiv.mul_apply, ← tr_mul, e, tr_mul, LinearEquiv.mul_apply, hfix]

variable {φ} in
theorem theta_equivariant (hα : ∀ g : ↥G, φ g ∈ altOn S7 → ∀ w ∈ P φ 0 1, (g : GLV V) w = w)
    {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) {w : V} (hw : w ∈ P φ 0 2)
    {x : Fin 9 → ZMod 2} (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    tr φ σ (theta φ w x) = theta φ w (pa σ x) := by
  have hterm : ∀ k, x k • tr φ σ (tr φ (gk k) w) = x k • tr φ (gk (σ k)) w := by
    intro k
    by_cases hk : k ∈ S7f
    · rw [tr_gk hα hσ hk hw]
    · have h0 : x k = 0 := by
        rw [mem_S7f] at hk
        simp only [not_and_or, not_not] at hk
        rcases hk with rfl | rfl
        · exact hx0
        · exact hx1
      rw [h0, zero_smul, zero_smul]
  rw [theta_apply, map_sum]
  simp only [map_smul]
  rw [Finset.sum_congr rfl fun k _ => hterm k, theta_apply]
  simp only [pa_apply]
  rw [← Equiv.sum_comp σ (fun k => x (σ⁻¹ k) • tr φ (gk k) w)]
  simp

theorem P_eq_conj {k : Fin 9} (hk : k ∈ S7f) : P φ 0 k = conjSub (tr φ (gk k)) (P φ 0 2) := by
  have h := P_conj φ (gk k) 0 2
  rwa [gk_zero, gk_two hk] at h

theorem ev_add_mem_E7 {a b : Fin 9} (ha : a ∈ S7f) (hb : b ∈ S7f) : ev a + ev b ∈ E7 := by
  rw [mem_S7f] at ha hb
  refine ⟨?_, ?_, ?_⟩
  · simp [ev_apply, Ne.symm ha.1, Ne.symm hb.1]
  · simp [ev_apply, Ne.symm ha.2, Ne.symm hb.2]
  · simp only [Pi.add_apply, Finset.sum_add_distrib, ev, Finset.sum_pi_single', Finset.mem_univ,
      if_true]
    decide

noncomputable abbrev Lsub : Subgroup (GLV V) := ((altOn S7).comap φ.toMonoidHom).map G.subtype

theorem tr_mem_L {σ : Perm (Fin 9)} (hσ : σ ∈ altOn S7) : tr φ σ ∈ Lsub φ :=
  ⟨φ.symm σ, by simpa using hσ, rfl⟩

theorem exists_eq_tr_of_mem_L {l : GLV V} (hl : l ∈ Lsub φ) :
    ∃ σ ∈ altOn S7, l = tr φ σ := by
  obtain ⟨g, hg, rfl⟩ := hl
  exact ⟨φ g, hg, (tr_apply_self φ g).symm⟩

variable {φ} in
theorem map_theta_le (hα : ∀ g : ↥G, φ g ∈ altOn S7 → ∀ w ∈ P φ 0 1, (g : GLV V) w = w)
    {w : V} (hw : w ∈ P φ 0 2) : E7.map (theta φ w) ≤ commSpace (Lsub φ) ⊤ := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  refine E7_le_span.trans (Submodule.span_le.2 ?_)
  rintro _ ⟨a, ha, b, hb, rfl⟩
  show theta φ w (ev a + ev b) ∈ commSpace (Lsub φ) ⊤
  by_cases hab : a = b
  · rw [hab, ev_add_self, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨p, hp, hpa, hpb⟩ : ∃ p ∈ S7f, p ≠ a ∧ p ≠ b := by
    have hcard : ({a, b} : Finset (Fin 9)).card < S7f.card := by
      refine (Finset.card_le_two).trans_lt ?_
      rw [card_S7f]
      norm_num
    obtain ⟨p, hp, hp'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp'
    exact ⟨p, hp, hp'.1, hp'.2⟩
  obtain ⟨σ, hσ, -, hσb⟩ := exists_altOn_move hp hb ha hpb hpa (Ne.symm hab)
  have hb' := mem_S7f.1 hb
  have e : theta φ w (ev a + ev b) = tr φ σ (theta φ w (ev b)) - theta φ w (ev b) := by
    rw [map_add, ← hσb, ← pa_ev, ← theta_equivariant hα hσ hw (by simp [ev_apply, Ne.symm hb'.1])
      (by simp [ev_apply, Ne.symm hb'.2]), CFSG.Quasithin.C58.G64D.datum_sub_eq_add]
  rw [e]
  exact sub_mem_commSpace (tr_mem_L φ hσ) Submodule.mem_top

variable {φ} in
theorem commSpace_le_iSup (hα : ∀ g : ↥G, φ g ∈ altOn S7 → ∀ w ∈ P φ 0 1, (g : GLV V) w = w)
    (hU : U0 φ = ⊤) :
    commSpace (Lsub φ) ⊤ ≤ ⨆ w : ↥(P φ 0 2), E7.map (theta φ (w : V)) := by
  set Y := ⨆ w : ↥(P φ 0 2), E7.map (theta φ (w : V)) with hY
  refine commSpace_le_iff.2 fun l hl v _ => ?_
  obtain ⟨σ, hσ, rfl⟩ := exists_eq_tr_of_mem_L φ hl
  have key : U0 φ ≤ Y.comap (CFSG.Quasithin.C58.G64D.dl (tr φ σ)) := by
    refine iSup_le fun j u hu => ?_
    show (tr φ σ) u - u ∈ Y
    by_cases hj0 : j = 0
    · rw [hj0, P_self, Submodule.mem_bot] at hu
      rw [hu, map_zero, sub_zero]
      exact Y.zero_mem
    by_cases hj1 : j = 1
    · rw [hj1] at hu
      have h := hα (φ.symm σ) (by simpa using hσ) u hu
      rw [show ((φ.symm σ : ↥G) : GLV V) = tr φ σ from rfl] at h
      rw [h, sub_self]
      exact Y.zero_mem
    have hjS : j ∈ S7f := mem_S7f.2 ⟨hj0, hj1⟩
    rw [P_eq_conj φ hjS, mem_conjSub] at hu
    set w := (tr φ (gk j)).symm u with hw
    have hu' : u = theta φ w (ev j) := by rw [theta_ev, hw, LinearEquiv.apply_symm_apply]
    have hσj : σ j ∈ S7f := by
      rw [mem_S7f] at hjS ⊢
      constructor
      · intro h
        rw [← fix_zero_of_mem_altOn hσ] at h
        exact hjS.1 (σ.injective h)
      · intro h
        rw [← fix_one_of_mem_altOn hσ] at h
        exact hjS.2 (σ.injective h)
    have e : (tr φ σ) u - u = theta φ w (ev (σ j) + ev j) := by
      rw [hu', theta_equivariant hα hσ hu (by simp [ev_apply, Ne.symm hj0])
        (by simp [ev_apply, Ne.symm hj1]), pa_ev, ← map_sub,
        show ev (σ j) - ev j = ev (σ j) + ev j by
          funext m
          simp only [Pi.sub_apply, Pi.add_apply]
          exact (show ∀ a b : ZMod 2, a - b = a + b by decide) _ _]
    rw [e]
    exact (le_iSup (fun w : ↥(P φ 0 2) => E7.map (theta φ (w : V))) ⟨w, hu⟩)
      (Submodule.mem_map_of_mem (ev_add_mem_E7 hσj hjS))
  have hv : v ∈ U0 φ := by rw [hU]; exact Submodule.mem_top
  exact key hv

variable {φ} in
theorem finrank_tildeV_ne_four (hirr : IsIrr G ⊤)
    (hα : ∀ g : ↥G, φ g ∈ altOn S7 → ∀ w ∈ P φ 0 1, (g : GLV V) w = w)
    (hL : HasIrrTildeV (Lsub φ)) : Module.finrank (ZMod 2) (TildeV (Lsub φ)) ≠ 4 := by
  classical
  set L := Lsub φ with hLdef
  set W := commSpace L ⊤ with hW
  set T := tildeVBot L with hT
  have hTW : T < W := hL.1
  have hU : U0 φ = ⊤ := by
    rcases hirr.2.2 (U0 φ) (invariant_U0 φ) bot_le le_top with h | h
    · exfalso
      have htriv := apply_eq_of_U0_eq_bot φ h
      have hW0 : W = ⊥ := commSpace_eq_bot_iff.2 fun l hl u _ => by
        obtain ⟨σ, -, rfl⟩ := exists_eq_tr_of_mem_L φ hl
        exact htriv σ u
      rw [hW0] at hTW
      exact not_lt_bot hTW
    · exact h
  have hY := commSpace_le_iSup hα hU
  have hTinv : Invariant L T := by
    intro l hl t ht
    have hfix : l t = t := ht.1 l hl
    rw [hfix]
    exact ht
  obtain ⟨⟨w, hw⟩, hwT⟩ : ∃ w : ↥(P φ 0 2), ¬ E7.map (theta φ (w : V)) ≤ T := by
    by_contra h
    push Not at h
    exact absurd (hY.trans (iSup_le h)) (not_le_of_gt hTW)
  simp only at hwT
  set K : Submodule (ZMod 2) (Fin 9 → ZMod 2) := E7 ⊓ T.comap (theta φ w) with hK
  have hKinv : ∀ σ ∈ altOn S7, ∀ x ∈ K, pa σ x ∈ K := by
    intro σ hσ x hx
    refine ⟨pa_mem_E7 hσ hx.1, ?_⟩
    show theta φ w (pa σ x) ∈ T
    rw [← theta_equivariant hα hσ hw hx.1.1 hx.1.2.1]
    exact hTinv _ (tr_mem_L φ hσ) _ hx.2
  have hK0 : K = ⊥ := by
    by_contra hne
    have hKE : K = E7 := eq_E7_of_invariant (X := K) inf_le_left hKinv hne
    apply hwT
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ K := by rw [hKE]; exact hx
    exact this.2
  set A := E7.map (theta φ w) with hA
  have hAW : A ≤ W := map_theta_le hα hw
  have hAT : A ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxT⟩
    have : x ∈ K := ⟨hx, hxT⟩
    rw [hK0, Submodule.mem_bot] at this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  have hJ : A ⊔ T = W := by
    have hJinv : Invariant L (A ⊔ T) := by
      refine Invariant.sup ?_ hTinv
      rintro l hl _ ⟨x, hx, rfl⟩
      obtain ⟨σ, hσ, rfl⟩ := exists_eq_tr_of_mem_L φ hl
      exact ⟨pa σ x, pa_mem_E7 hσ hx, (theta_equivariant hα hσ hw hx.1 hx.2.1).symm⟩
    rcases hL.2 (A ⊔ T) hJinv le_sup_right (sup_le hAW hTW.le) with h | h
    · exact absurd (le_sup_left.trans h.le) hwT
    · exact h
  have hcardA : Nat.card ↥A = 64 := by
    rw [← card_E7]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun x : ↥E7 => (⟨theta φ w x, x, x.2, rfl⟩ : ↥A))
      ⟨fun x y hxy => ?_, fun y => ?_⟩)
    · have hxy' : theta φ w (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val hxy
      have hmem : ((x : Fin 9 → ZMod 2) - y) ∈ K :=
        ⟨E7.sub_mem x.2 y.2, by
          show theta φ w ((x : Fin 9 → ZMod 2) - y) ∈ T
          rw [hxy']
          exact T.zero_mem⟩
      rw [hK0, Submodule.mem_bot, sub_eq_zero] at hmem
      exact Subtype.ext hmem
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := y
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcardW : Nat.card ↥W = Nat.card ↥A * Nat.card ↥T := by
    rw [← Nat.card_prod]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun p : ↥A × ↥T =>
      (⟨(p.1 : V) + p.2, by rw [← hJ]; exact Submodule.add_mem_sup p.1.2 p.2.2⟩ : ↥W))
      ⟨fun p q hpq => ?_, fun z => ?_⟩)
    · have h1 : (p.1 : V) + p.2 = q.1 + q.2 := congrArg Subtype.val hpq
      have h2 : (p.1 : V) - q.1 = q.2 - p.2 := by
        rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
      have hmA : (p.1 : V) - q.1 ∈ A := A.sub_mem p.1.2 q.1.2
      have hmT : (p.1 : V) - q.1 ∈ T := by rw [h2]; exact T.sub_mem q.2.2 p.2.2
      have h0 : (p.1 : V) - q.1 = 0 := by
        have : (p.1 : V) - q.1 ∈ A ⊓ T := ⟨hmA, hmT⟩
        rw [hAT, Submodule.mem_bot] at this
        exact this
      have h3 : (p.1 : V) = q.1 := sub_eq_zero.1 h0
      have h4 : (p.2 : V) = q.2 := by
        rw [h3] at h1
        exact add_left_cancel h1
      exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
    · have hz : (z : V) ∈ A ⊔ T := by rw [hJ]; exact z.2
      obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.1 hz
      exact ⟨(⟨a, ha⟩, ⟨t, ht⟩), Subtype.ext hat⟩
  set N : Submodule (ZMod 2) ↥W := (fixedSpace L).comap W.subtype with hN
  have hcardN : Nat.card ↥N = Nat.card ↥T := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : ↥N => (⟨(x : ↥W), x.2, (x : ↥W).2⟩ : ↥T))
      ⟨fun x y hxy => ?_, fun y => ?_⟩)
    · have h := congrArg (fun z : ↥T => (z : V)) hxy
      exact Subtype.ext (Subtype.ext h)
    · exact ⟨⟨⟨y, y.2.2⟩, y.2.1⟩, rfl⟩
  have hquot := Submodule.card_eq_card_quotient_mul_card N
  have hTV : Nat.card (TildeV L) = 64 := by
    have hpos : 0 < Nat.card ↥T := Nat.card_pos
    have h := hquot
    rw [hcardW, hcardA, hcardN] at h
    have h' : Nat.card ↥T * 64 = Nat.card ↥T * Nat.card (TildeV L) := by
      rw [mul_comm]
      exact h
    exact (Nat.eq_of_mul_eq_mul_left hpos h').symm
  intro h4
  have h2 : Nat.card (TildeV L) = 2 ^ Module.finrank (ZMod 2) (TildeV L) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hTV, h4] at h2
  exact absurd h2 (by norm_num)

end G8Proof

theorem g8_holds : G8 := by
  intro V _ _ _ G φ hirr hα hL
  exact G8Proof.finrank_tildeV_ne_four hirr hα hL

end CFSG.CGT.Foote82
