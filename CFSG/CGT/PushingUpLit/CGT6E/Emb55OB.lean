module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Cfg
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Faith

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

variable {V : Type} [CommGroup V] {G T Y H Q D : Subgroup (MulAut V)} {y a : MulAut V}

theorem inv_apply_of_apply_eq {g : MulAut V} {u : V} (h : g u = u) : g⁻¹ u = u := by
  have := MulAut.inv_apply_self V g u
  rwa [h] at this

theorem comm_comm_eq (a y : MulAut V) : ⁅a, ⁅a, y⁆⁆ =
    ((a * a) * y * (a * a)⁻¹) * (a * y * a⁻¹)⁻¹ * y * (a * y * a⁻¹)⁻¹ := by
  simp only [commutatorElement_def]; group

namespace Cfg55

variable (k : Cfg55 V G T Y H Q D y a)
include k

theorem aQ : a ∈ Q := k.DQ k.aD

theorem a3 : a ^ 3 = 1 := k.D3 a k.aD

theorem cD : ⁅a, y⁆ ∈ D := by
  have h2 : y * a⁻¹ * y⁻¹ ∈ D := k.Dinv y (k.data.yH k.hy) a⁻¹ (D.inv_mem k.aD)
  have e : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  rw [e]; exact D.mul_mem k.aD h2

theorem cQ : ⁅a, y⁆ ∈ Q := k.DQ k.cD

theorem d0D : ⁅a, ⁅a, y⁆⁆ ∈ D := (k.Dcl a k.aD _ k.cQ).1

theorem d03 : ⁅a, ⁅a, y⁆⁆ ^ 3 = 1 := k.D3 _ k.d0D

theorem y1_notin : a * y * a⁻¹ ∉ Y := by
  intro hmem
  have hcQ := k.cQ
  have hcexp : ⁅a, y⁆ = (a * y * a⁻¹) * y⁻¹ := by rw [commutatorElement_def]
  have h1 : ⁅a, y⁆ = 1 :=
    k.data.inf_eq_one k.hy k.hy1 k.hyQ (hcexp ▸ Y.mul_mem hmem (Y.inv_mem k.hy)) hcQ
  exact k.hya (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem y2_notin : (a * a) * y * (a * a)⁻¹ ∉ Y := by
  intro hmem
  have hQ2 : a * a ∈ Q := Q.mul_mem k.aQ k.aQ
  have hcQ : ⁅a * a, y⁆ ∈ Q := by
    have h1 : y * (a * a)⁻¹ * y⁻¹ ∈ Q := k.data.Qnorm y (k.data.yH k.hy) _ (Q.inv_mem hQ2)
    have e : ⁅a * a, y⁆ = (a * a) * (y * (a * a)⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]; exact Q.mul_mem hQ2 h1
  have hcexp : ⁅a * a, y⁆ = ((a * a) * y * (a * a)⁻¹) * y⁻¹ := by rw [commutatorElement_def]
  have h1 : ⁅a * a, y⁆ = 1 :=
    k.data.inf_eq_one k.hy k.hy1 k.hyQ (hcexp ▸ Y.mul_mem hmem (Y.inv_mem k.hy)) hcQ
  have h2 : (a * a) * y = y * (a * a) := commutatorElement_eq_one_iff_mul_comm.mp h1
  have h3 : a = (a * a) * (a * a) := by
    calc a = a ^ 3 * a := by rw [k.a3, one_mul]
      _ = a * (a * a) * a := by rw [pow_three]
      _ = (a * a) * (a * a) := by group
  apply k.hya
  have : Commute (a * a) y := h2
  have h4 : Commute ((a * a) * (a * a)) y := this.mul_left this
  rw [← h3] at h4
  exact h4.eq.symm

variable [Finite V]

theorem y1_triv : ∀ u ∈ commV Y, (a * y * a⁻¹) u = u :=
  (k.data.sec.pair_orth k.hy k.hy1 (k.data.QG k.aQ) (k.data.conj_sup_three k.aQ) k.y1_notin).2

theorem y2_triv : ∀ u ∈ commV Y, ((a * a) * y * (a * a)⁻¹) u = u :=
  (k.data.sec.pair_orth k.hy k.hy1 (k.data.QG (Q.mul_mem k.aQ k.aQ))
    (k.data.conj_sup_three (Q.mul_mem k.aQ k.aQ)) k.y2_notin).2

theorem d0_apply : ∀ u ∈ commV Y, ⁅a, ⁅a, y⁆⁆ u = y u := by
  intro u hu
  have h1 : (a * y * a⁻¹)⁻¹ u = u := inv_apply_of_apply_eq (k.y1_triv u hu)
  have hyu : y u ∈ commV Y := commV_invariant k.hy hu
  have h2 : (a * y * a⁻¹)⁻¹ (y u) = y u := inv_apply_of_apply_eq (k.y1_triv _ hyu)
  have h3 := k.y2_triv _ hyu
  rw [comm_comm_eq a y]
  simp only [MulAut.mul_apply, h1, h2, h3]

theorem U_le_W : commV Y ≤ commV (Subgroup.zpowers ⁅a, ⁅a, y⁆⁆) := by
  intro w hw
  have hzY := k.data.sec.zpowers_eq k.hy k.hy1
  have hy3 := k.data.sec.pow_three k.hy
  have hfpf : ∀ u ∈ commV Y, y u = u → u = 1 := fun u hu hyu => by
    rw [← hzY] at hu
    exact eq_one_of_mem_commV_of_fixed k.data.sec.elem hy3 hu hyu
  obtain ⟨u, hu, rfl⟩ := exists_apply_mul_inv_eq (fun u hu => commV_invariant k.hy hu) hfpf hw
  have : ⁅a, ⁅a, y⁆⁆ u * u⁻¹ ∈ commV (Subgroup.zpowers ⁅a, ⁅a, y⁆⁆) :=
    G6.mem_commV_of_mem (Subgroup.mem_zpowers _) u
  rwa [k.d0_apply u hu] at this

theorem card_W_le : Nat.card (commV (Subgroup.zpowers ⁅a, ⁅a, y⁆⁆)) ≤ 64 := by
  have hhy1 : a * y * a⁻¹ ∈ conjSub a Y := conj_mem_conjSub k.hy
  have hhy2 : (a * a) * y * (a * a)⁻¹ ∈ conjSub (a * a) Y := conj_mem_conjSub k.hy
  have hne1 : a * y * a⁻¹ ≠ 1 := fun e => k.hy1 (by
    have := congrArg (fun z => a⁻¹ * z * a) e
    simpa [mul_assoc] using this)
  have hne2 : (a * a) * y * (a * a)⁻¹ ≠ 1 := fun e => k.hy1 (by
    have := congrArg (fun z => (a * a)⁻¹ * z * (a * a)) e
    simpa [mul_assoc] using this)
  have hz0 : Subgroup.zpowers y = Y := k.data.sec.zpowers_eq k.hy k.hy1
  have hz1 : Subgroup.zpowers (a * y * a⁻¹) = conjSub a Y :=
    zpowers_eq_of_card_three (by rw [card_conjSub, k.data.sec.ycard]) hhy1 hne1
  have hz2 : Subgroup.zpowers ((a * a) * y * (a * a)⁻¹) = conjSub (a * a) Y :=
    zpowers_eq_of_card_three (by rw [card_conjSub, k.data.sec.ycard]) hhy2 hne2
  have hd0J : ⁅a, ⁅a, y⁆⁆ ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (a * y * a⁻¹) ⊔
      Subgroup.zpowers ((a * a) * y * (a * a)⁻¹) := by
    rw [comm_comm_eq a y]
    have m0 : y ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (a * y * a⁻¹) ⊔
        Subgroup.zpowers ((a * a) * y * (a * a)⁻¹) :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
    have m1 : a * y * a⁻¹ ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (a * y * a⁻¹) ⊔
        Subgroup.zpowers ((a * a) * y * (a * a)⁻¹) :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have m2 : (a * a) * y * (a * a)⁻¹ ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (a * y * a⁻¹) ⊔
        Subgroup.zpowers ((a * a) * y * (a * a)⁻¹) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m2 (Subgroup.inv_mem _ m1)) m0)
      (Subgroup.inv_mem _ m1)
  have h1 : commV (Subgroup.zpowers ⁅a, ⁅a, y⁆⁆) ≤ commV (Subgroup.zpowers y) ⊔
      commV (Subgroup.zpowers (a * y * a⁻¹)) ⊔ commV (Subgroup.zpowers ((a * a) * y * (a * a)⁻¹)) :=
    (G6.commV_mono (Subgroup.zpowers_le.mpr hd0J)).trans
      ((commV_sup_le _ _).trans (sup_le_sup_right (commV_sup_le _ _) _))
  have c0 : Nat.card (commV (Subgroup.zpowers y)) = 4 := by rw [hz0]; exact k.data.sec.ucard
  have c1 : Nat.card (commV (Subgroup.zpowers (a * y * a⁻¹))) = 4 := by
    rw [hz1, card_commV_conjSub]; exact k.data.sec.ucard
  have c2 : Nat.card (commV (Subgroup.zpowers ((a * a) * y * (a * a)⁻¹))) = 4 := by
    rw [hz2, card_commV_conjSub]; exact k.data.sec.ucard
  calc Nat.card (commV (Subgroup.zpowers ⁅a, ⁅a, y⁆⁆))
      ≤ Nat.card ↥(commV (Subgroup.zpowers y) ⊔ commV (Subgroup.zpowers (a * y * a⁻¹)) ⊔
        commV (Subgroup.zpowers ((a * a) * y * (a * a)⁻¹))) := Subgroup.card_le_of_le h1
    _ ≤ Nat.card ↥(commV (Subgroup.zpowers y) ⊔ commV (Subgroup.zpowers (a * y * a⁻¹))) *
        Nat.card (commV (Subgroup.zpowers ((a * a) * y * (a * a)⁻¹))) := card_sup_le_mul _ _
    _ ≤ (Nat.card (commV (Subgroup.zpowers y)) *
          Nat.card (commV (Subgroup.zpowers (a * y * a⁻¹)))) *
        Nat.card (commV (Subgroup.zpowers ((a * a) * y * (a * a)⁻¹))) :=
      Nat.mul_le_mul (card_sup_le_mul _ _) le_rfl
    _ = 64 := by rw [c0, c1, c2]

theorem y_fixes {x : V} (hx : ⁅a, ⁅a, y⁆⁆ x = x) : y x = x := by
  set d0 : MulAut V := ⁅a, ⁅a, y⁆⁆ with hd0
  have h1 : y x * x⁻¹ ∈ commV Y := G6.mem_commV_of_mem k.hy x
  have h2 : y x * x⁻¹ ∈ commV (Subgroup.zpowers d0) := k.U_le_W h1
  have hyd : y * d0 = d0 * y := k.d0H y (k.data.yH k.hy)
  have h3 : d0 (y x * x⁻¹) = y x * x⁻¹ := by
    have h4 : d0 (y x) = y x := by
      calc d0 (y x) = (d0 * y) x := rfl
        _ = (y * d0) x := by rw [hyd]
        _ = y (d0 x) := rfl
        _ = y x := by rw [hx]
    rw [map_mul, map_inv, hx, h4]
  have := eq_one_of_mem_commV_of_fixed k.data.sec.elem k.d03 h2 h3
  exact mul_inv_eq_one.mp this

theorem H_fixes : ∀ h ∈ H, ∀ x : V, ⁅a, ⁅a, y⁆⁆ x = x → h x = x := by
  set d0 : MulAut V := ⁅a, ⁅a, y⁆⁆ with hd0
  let N : Subgroup (MulAut V) :=
    { carrier := {h | h ∈ H ∧ ∀ x : V, d0 x = x → h x = x}
      one_mem' := ⟨H.one_mem, fun x _ => rfl⟩
      mul_mem' := fun {g h} hg hh => ⟨H.mul_mem hg.1 hh.1, fun x hx => by
        show g (h x) = x
        rw [hh.2 x hx, hg.2 x hx]⟩
      inv_mem' := fun {g} hg => ⟨H.inv_mem hg.1, fun x hx =>
        inv_apply_of_apply_eq (hg.2 x hx)⟩ }
  have hNH : N ≤ H := fun n hn => hn.1
  have hNnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    refine ⟨H.mul_mem (H.mul_mem hg hn.1) (H.inv_mem hg), fun x hx => ?_⟩
    have hgd : g * d0 = d0 * g := k.d0H g hg
    have hgx : d0 (g⁻¹ x) = g⁻¹ x := by
      have h1 : g⁻¹ * d0 = d0 * g⁻¹ := by
        calc g⁻¹ * d0 = g⁻¹ * d0 * g * g⁻¹ := by group
          _ = g⁻¹ * (d0 * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * d0) * g⁻¹ := by rw [hgd]
          _ = d0 * g⁻¹ := by group
      calc d0 (g⁻¹ x) = (d0 * g⁻¹) x := rfl
        _ = (g⁻¹ * d0) x := by rw [h1]
        _ = g⁻¹ (d0 x) := rfl
        _ = g⁻¹ x := by rw [hx]
    show g (n (g⁻¹ x)) = x
    rw [hn.2 _ hgx]
    exact MulAut.apply_inv_self V g x
  have hyN : y ∈ N := ⟨k.data.yH k.hy, fun x hx => k.y_fixes hx⟩
  have hYN : Y ≤ N := by
    rw [← k.data.sec.zpowers_eq k.hy k.hy1]
    exact Subgroup.zpowers_le.mpr hyN
  have hHN : H ≤ N := k.data.gen N hNH hNnorm hYN
  intro h hh x hx
  exact (hHN hh).2 x hx

theorem card_le_81 {P : Subgroup (MulAut V)} (hPH : P ≤ H) (hP3 : IsPGroup 3 ↥P) :
    Nat.card ↥P ≤ 81 :=
  card_le_81_of_faithful k.data.sec.elem k.d03 k.card_W_le hP3
    (fun x hx => k.d0H x (hPH hx)) (fun x hx v hv => k.H_fixes x (hPH hx) v hv)

theorem card_Q_le : Nat.card ↥Q ≤ 27 := by
  have hP3 : IsPGroup 3 ↥(Y ⊔ Q) := k.data.sup_Y_Q_three
  have hPH : Y ⊔ Q ≤ H := sup_le k.data.yH k.data.QH
  have h81 := k.card_le_81 hPH hP3
  have hlt : Q < Y ⊔ Q :=
    lt_of_le_of_ne le_sup_right (fun h => k.hyQ (h ▸ Subgroup.mem_sup_left k.hy))
  have hne : Nat.card ↥Q ≠ Nat.card ↥(Y ⊔ Q) := fun h =>
    hlt.ne (Subgroup.eq_of_le_of_card_ge le_sup_right (le_of_eq h.symm))
  obtain ⟨j, hj⟩ := k.data.Q3.exists_card_eq
  obtain ⟨m, hm⟩ := hP3.exists_card_eq
  have hdvd : 3 ^ j ∣ 3 ^ m := hj ▸ hm ▸ Subgroup.card_dvd_of_le le_sup_right
  have hjm : j ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hjm' : j ≠ m := fun h => hne (by rw [hj, hm, h])
  have hlt' : j + 1 ≤ m := by omega
  have : 3 ^ (j + 1) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hlt'
  rw [pow_succ] at this
  omega

end Cfg55

theorem ge_27_of_noncomm {M : Type*} [Group M] {R : Subgroup M} [Finite R] (hR : IsPGroup 3 ↥R)
    {x z : M} (hx : x ∈ R) (hz : z ∈ R) (hxz : x * z ≠ z * x) : 27 ≤ Nat.card ↥R := by
  by_contra hlt
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcomm : ∀ a b : R, a * b = b * a := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    interval_cases k
    · intro a b
      have : Nat.card R = 1 := by simpa using hk
      have h1 : Subsingleton R := (Nat.card_eq_one_iff_unique.mp this).1
      exact Subsingleton.elim _ _
    · have hp : Nat.card R = 3 := by simpa using hk
      have : IsCyclic R := isCyclic_of_prime_card hp
      exact fun a b => (IsCyclic.commGroup (α := R)).mul_comm a b
    · have hp : Nat.card R = 3 ^ 2 := hk
      have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hp
      exact fun a b => this.is_comm.comm a b
  exact hxz (by simpa using congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨z, hz⟩))

namespace Cfg55

variable [Finite V] (k : Cfg55 V G T Y H Q D y a)
include k

theorem Q_eq : Q = Subgroup.closure {a, ⁅a, y⁆} := by
  have hRQ : Subgroup.closure {a, ⁅a, y⁆} ≤ Q := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact k.aQ
    · exact k.cQ
  have hR3 : IsPGroup 3 ↥(Subgroup.closure {a, ⁅a, y⁆}) := k.data.Q3.to_le hRQ
  have hnc : a * ⁅a, y⁆ ≠ ⁅a, y⁆ * a := fun h =>
    k.d01 (commutatorElement_eq_one_iff_mul_comm.mpr h)
  have h27 := ge_27_of_noncomm hR3 (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hnc
  exact (Subgroup.eq_of_le_of_card_ge hRQ (by have := k.card_Q_le; omega)).symm

end Cfg55

end CFSG.CGT.PushingUpLit.CGT6E
