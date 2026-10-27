module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

variable {V : Type} [CommGroup V]

@[expose] def dlt (g : MulAut V) : V →* V where
  toFun v := g v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem dlt_apply (g : MulAut V) (v : V) : dlt g v = g v * v⁻¹ := rfl

@[expose] def SimpleQuot (Y : Subgroup (MulAut V)) : Prop :=
  commV Y ≠ commV Y ⊓ fixV Y ∧
  ∀ N : Subgroup V, (∀ g ∈ Y, ∀ n ∈ N, g n ∈ N) → commV Y ⊓ fixV Y ≤ N → N ≤ commV Y →
    N = commV Y ⊓ fixV Y ∨ N = commV Y

@[expose] def CommGen (Y : Subgroup (MulAut V)) : Prop :=
  ∀ N : Subgroup V, (∀ g ∈ Y, ∀ u ∈ commV Y, g u * u⁻¹ ∈ N) → commV Y ≤ N

@[expose] def cm (M : Subgroup V) (A : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {w | ∃ a ∈ A, ∃ m ∈ M, a m * m⁻¹ = w}

section Basic

variable {Y : Subgroup (MulAut V)}

theorem apply_comm {g y : MulAut V} (h : g * y = y * g) (v : V) : g (y v) = y (g v) := by
  have := congrArg (fun z : MulAut V => z v) h
  simpa [MulAut.mul_apply] using this

theorem apply_mem_commV_of_comm {g : MulAut V} (hg : ∀ y ∈ Y, g * y = y * g) {u : V}
    (hu : u ∈ commV Y) : g u ∈ commV Y :=
  CFSG.Quasithin.apply_mem_commV_of_forall_commute hg hu

theorem apply_mem_fixV_of_comm {g : MulAut V} (hg : ∀ y ∈ Y, g * y = y * g) {w : V}
    (hw : w ∈ fixV Y) : g w ∈ fixV Y := by
  intro y hy
  rw [← apply_comm (hg y hy), hw y hy]

theorem apply_mem_fixV_of_comm' {g : MulAut V} (hg : ∀ y ∈ Y, g * y = y * g) {w : V}
    (hw : w ∈ fixV Y) : g⁻¹ w ∈ fixV Y := by
  refine apply_mem_fixV_of_comm (g := g⁻¹) (fun y hy => ?_) hw
  have := hg y hy
  calc g⁻¹ * y = g⁻¹ * y * (g * g⁻¹) := by simp
    _ = g⁻¹ * (y * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * y) * g⁻¹ := by rw [this]
    _ = y * g⁻¹ := by group

theorem comm_inv {g : MulAut V} (hg : ∀ y ∈ Y, g * y = y * g) : ∀ y ∈ Y, g⁻¹ * y = y * g⁻¹ := by
  intro y hy
  have := hg y hy
  calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * y) * g⁻¹ := by rw [this]
    _ = y * g⁻¹ := by group

end Basic

section MS

variable {Y : Subgroup (MulAut V)}

@[expose] def TrivQ (Y : Subgroup (MulAut V)) (g : MulAut V) : Prop :=
  ∀ u ∈ commV Y, dlt g u ∈ fixV Y

theorem ms_two (hV : ∀ v : V, v ^ 2 = 1) (hY : SimpleQuot Y) {g : MulAut V}
    (hg : ∀ y ∈ Y, g * y = y * g) (hg2 : g ^ 2 = 1) : TrivQ Y g := by
  set K : Subgroup V := commV Y ⊓ (fixV Y).comap (dlt g) with hK
  have hKinv : ∀ y ∈ Y, ∀ n ∈ K, y n ∈ K := by
    intro y hy n hn
    refine ⟨commV_invariant hy hn.1, ?_⟩
    have h1 : dlt g (y n) = y (dlt g n) := by
      simp only [dlt_apply, map_mul, map_inv, apply_comm (hg y hy)]
    have h2 : dlt g n ∈ fixV Y := hn.2
    show dlt g (y n) ∈ fixV Y
    rw [h1, h2 y hy]
    exact h2
  have hWK : commV Y ⊓ fixV Y ≤ K := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    show dlt g w ∈ fixV Y
    rw [dlt_apply]
    exact mul_mem (apply_mem_fixV_of_comm hg hw.2) (inv_mem hw.2)
  have hKU : K ≤ commV Y := inf_le_left
  rcases hY.2 K hKinv hWK hKU with hKW | hKU'
  · exfalso
    apply hY.1
    refine le_antisymm ?_ inf_le_left
    intro u hu
    have hgu : g u ∈ commV Y := apply_mem_commV_of_comm hg hu
    have hw1 : dlt g u ∈ commV Y := mul_mem hgu (inv_mem hu)
    have hg2' : g (g u) = u := by
      have := congrArg (fun z : MulAut V => z u) hg2
      simpa [pow_two, MulAut.mul_apply] using this
    have hw1K : dlt g u ∈ K := by
      refine ⟨hw1, ?_⟩
      show dlt g (dlt g u) ∈ fixV Y
      have h0 : dlt g (dlt g u) = 1 := by
        simp only [dlt_apply, map_mul, map_inv, hg2', mul_inv, inv_inv]
        have ha := hV (u * (g u)⁻¹)
        rw [pow_two] at ha
        rw [mul_comm ((g u)⁻¹) u]
        exact ha
      rw [h0]
      exact one_mem _
    rw [hKW] at hw1K
    have huK : u ∈ K := ⟨hu, hw1K.2⟩
    rw [hKW] at huK
    exact huK
  · intro u hu
    have : u ∈ K := by rw [hKU']; exact hu
    exact this.2

@[expose] def trivQSubgroup (Y : Subgroup (MulAut V)) : Subgroup (MulAut V) where
  carrier := {g | (∀ y ∈ Y, g * y = y * g) ∧ TrivQ Y g}
  one_mem' := ⟨fun y _ => by simp, fun u _ => by simp [dlt_apply]⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨hc₁, ht₁⟩ ⟨hc₂, ht₂⟩
    refine ⟨fun y hy => ?_, fun u hu => ?_⟩
    · calc g₁ * g₂ * y = g₁ * (g₂ * y) := mul_assoc _ _ _
        _ = g₁ * (y * g₂) := by rw [hc₂ y hy]
        _ = g₁ * y * g₂ := (mul_assoc _ _ _).symm
        _ = y * g₁ * g₂ := by rw [hc₁ y hy]
        _ = y * (g₁ * g₂) := mul_assoc _ _ _
    · have e : dlt (g₁ * g₂) u = g₁ (dlt g₂ u) * dlt g₁ u := by
        simp only [dlt_apply, MulAut.mul_apply, map_mul, map_inv]
        group
      rw [e]
      exact mul_mem (apply_mem_fixV_of_comm hc₁ (ht₂ u hu)) (ht₁ u hu)
  inv_mem' := by
    rintro g ⟨hc, ht⟩
    refine ⟨comm_inv hc, fun u hu => ?_⟩
    have hu' : g⁻¹ u ∈ commV Y := apply_mem_commV_of_comm (comm_inv hc) hu
    have e : dlt g⁻¹ u = (dlt g (g⁻¹ u))⁻¹ := by
      simp only [dlt_apply, MulAut.apply_inv_self]
      rw [mul_inv, inv_inv, mul_comm]
    rw [e]
    exact inv_mem (ht _ hu')

theorem conj_mem_trivQSubgroup {c h : MulAut V} (hc : ∀ y ∈ Y, c * y = y * c)
    (hh : h ∈ trivQSubgroup Y) : c * h * c⁻¹ ∈ trivQSubgroup Y := by
  obtain ⟨hch, hth⟩ := hh
  have hcc : ∀ y ∈ Y, c⁻¹ * y = y * c⁻¹ := comm_inv hc
  refine ⟨fun y hy => ?_, fun u hu => ?_⟩
  · calc c * h * c⁻¹ * y = c * h * (c⁻¹ * y) := mul_assoc _ _ _
      _ = c * h * (y * c⁻¹) := by rw [hcc y hy]
      _ = c * (h * y) * c⁻¹ := by group
      _ = c * (y * h) * c⁻¹ := by rw [hch y hy]
      _ = (c * y) * h * c⁻¹ := by group
      _ = (y * c) * h * c⁻¹ := by rw [hc y hy]
      _ = y * (c * h * c⁻¹) := by group
  · have hu' : c⁻¹ u ∈ commV Y := apply_mem_commV_of_comm hcc hu
    have e : dlt (c * h * c⁻¹) u = c (dlt h (c⁻¹ u)) := by
      simp only [dlt_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [e]
    exact apply_mem_fixV_of_comm hc (hth _ hu')

theorem ms_odd (hV : ∀ v : V, v ^ 2 = 1) (hY : SimpleQuot Y) {t d : MulAut V}
    (ht : ∀ y ∈ Y, t * y = y * t) (ht2 : t ^ 2 = 1) (hd : ∀ y ∈ Y, d * y = y * d) {r : ℕ}
    (hr : Odd r) (hdr : d ^ r = 1) (hinv : t * d * t⁻¹ = d⁻¹) : TrivQ Y d := by
  have htH : t ∈ trivQSubgroup Y := ⟨ht, ms_two hV hY ht ht2⟩
  have h1 : t * d = d⁻¹ * t := by
    have := hinv
    rwa [mul_inv_eq_iff_eq_mul] at this
  have h2 : d⁻¹ * t⁻¹ = t⁻¹ * d := by
    have := congrArg (fun z => z⁻¹) h1
    simpa [mul_inv_rev] using this
  have e1 : d * d = d * t * d⁻¹ * t⁻¹ := by
    calc d * d = d * t * (t⁻¹ * d) := by group
      _ = d * t * (d⁻¹ * t⁻¹) := by rw [h2]
      _ = d * t * d⁻¹ * t⁻¹ := by group
  have hdd : d * d ∈ trivQSubgroup Y := by
    rw [e1]
    exact mul_mem (conj_mem_trivQSubgroup hd htH) (inv_mem htH)
  obtain ⟨k, rfl⟩ := hr
  have e2 : d ^ (2 * (k + 1)) = d := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hdr, one_mul]
  have hdH : d ∈ trivQSubgroup Y := by
    have : d = (d * d) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, e2]
    rw [this]
    exact pow_mem hdd _
  exact hdH.2

theorem ms_three (hgen : CommGen Y) {d : MulAut V} (hd : ∀ y ∈ Y, d * y = y * d)
    (h : TrivQ Y d) : ∀ u ∈ commV Y, d u = u := by
  let N : Subgroup V :=
    { carrier := {v | d v = v}
      one_mem' := map_one d
      mul_mem' := fun {a b} ha hb => by
        have ha' : d a = a := ha
        have hb' : d b = b := hb
        show d (a * b) = a * b
        rw [map_mul, ha', hb']
      inv_mem' := fun {a} ha => by
        have ha' : d a = a := ha
        show d a⁻¹ = a⁻¹
        rw [map_inv, ha'] }
  have key : commV Y ≤ N := by
    refine hgen N fun g hg u hu => ?_
    obtain ⟨w, hwdef⟩ : ∃ w, w = d u * u⁻¹ := ⟨_, rfl⟩
    have hw : w ∈ fixV Y := hwdef ▸ h u hu
    have hdu : d u = w * u := by rw [hwdef]; group
    show d (g u * u⁻¹) = g u * u⁻¹
    rw [map_mul, map_inv, apply_comm (hd g hg) u, hdu, map_mul, hw g hg, mul_inv,
      mul_mul_mul_comm, mul_inv_cancel, one_mul]
  intro u hu
  exact key hu

end MS

section Cm

theorem cm_le_commV (M : Subgroup V) (A : Subgroup (MulAut V)) : cm M A ≤ commV A :=
  Subgroup.closure_mono fun _ ⟨a, ha, m, _, e⟩ => ⟨a, ha, m, e⟩

theorem mem_cm {M : Subgroup V} {A : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A) {m : V}
    (hm : m ∈ M) : a m * m⁻¹ ∈ cm M A :=
  Subgroup.subset_closure ⟨a, ha, m, hm, rfl⟩

theorem commV_le_cm_commV_of_odd [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : Odd (Nat.card A)) : commV A ≤ cm (commV A) A := by
  classical
  have : Finite A := Nat.finite_of_card_ne_zero (Odd.pos hA).ne'
  let _ : Fintype A := Fintype.ofFinite A
  let e : V →* V :=
    { toFun := fun v => ∏ a : A, (a : MulAut V) v
      map_one' := by simp
      map_mul' := fun v w => by simp [Finset.prod_mul_distrib] }
  have he : ∀ a' ∈ A, ∀ v, e (a' v) = e v := by
    intro a' ha' v
    show ∏ a : A, (a : MulAut V) (a' v) = ∏ a : A, (a : MulAut V) v
    exact Fintype.prod_equiv (Equiv.mulRight (⟨a', ha'⟩ : A)) _ _ fun a => rfl
  have he1 : ∀ v ∈ commV A, e v = 1 := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, v', rfl⟩ := hw
      rw [map_mul, map_inv, he x hx, mul_inv_cancel]
    | one => exact map_one e
    | mul a b _ _ ha hb => rw [map_mul, ha, hb, one_mul]
    | inv a _ ha => rw [map_inv, ha, inv_one]
  intro v hv
  have hprod : ∏ a : A, ((a : MulAut V) v * v⁻¹) = v := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have h1 : ∏ a : A, (a : MulAut V) v = 1 := he1 v hv
    rw [h1, one_mul, ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hA
    rw [hk, pow_succ, pow_mul, inv_pow, hV v, inv_one, one_pow, one_mul]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)
  rw [← hprod]
  exact prod_mem fun a _ => mem_cm a.2 hv

theorem exists_act_alike {A D : Subgroup (MulAut V)} {M : Subgroup V}
    (hM : ∀ a ∈ A, ∀ m ∈ M, a m ∈ M) (hD : ∀ d ∈ D, ∀ m ∈ M, d m = m) {g : MulAut V}
    (hg : g ∈ A ⊔ D) : ∃ a ∈ A, ∀ m ∈ M, g m = a m := by
  let R : Subgroup (MulAut V) :=
    { carrier := {g | ∃ a ∈ A, ∀ m ∈ M, g m = a m}
      one_mem' := ⟨1, A.one_mem, fun m _ => rfl⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, fun m hm => ?_⟩
        show g₁ (g₂ m) = a₁ (a₂ m)
        rw [h₂ m hm, h₁ _ (hM a₂ ha₂ m hm)]
      inv_mem' := by
        rintro g ⟨a, ha, h⟩
        refine ⟨a⁻¹, A.inv_mem ha, fun m hm => ?_⟩
        have hm' : a⁻¹ m ∈ M := hM a⁻¹ (A.inv_mem ha) m hm
        have h1 : g (a⁻¹ m) = m := by
          rw [h _ hm']
          exact MulAut.apply_inv_self V a m
        calc g⁻¹ m = g⁻¹ (g (a⁻¹ m)) := by rw [h1]
          _ = a⁻¹ m := MulAut.inv_apply_self V g _ }
  have hAR : A ≤ R := fun a ha => ⟨a, ha, fun m _ => rfl⟩
  have hDR : D ≤ R := fun d hd => ⟨1, A.one_mem, fun m hm => hD d hd m hm⟩
  exact sup_le hAR hDR hg

end Cm

section Weyl

variable [Finite V]

theorem weyl_alt1 (hV : ∀ v : V, v ^ 2 = 1) {A B D : Subgroup (MulAut V)} {U : Subgroup V}
    (hAodd : Odd (Nat.card A)) (hDodd : Odd (Nat.card D)) (hAD : A ⊔ D = B ⊔ D)
    (hAB : A ⊔ D ≤ A ⊔ B) (hU : commV A ≤ U) (hDU : ∀ d ∈ D, ∀ u ∈ U, d u = u)
    (hcard : Nat.card (commV B) ≤ Nat.card (commV A)) : D = ⊥ := by
  have hMA : ∀ a ∈ A, ∀ m ∈ commV A, a m ∈ commV A := fun a ha m hm => commV_invariant ha hm
  have hDM : ∀ d ∈ D, ∀ m ∈ commV A, d m = m := fun d hd m hm => hDU d hd m (hU hm)
  have hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ m ∈ commV A, b m = a m := fun b hb =>
    exists_act_alike hMA hDM
      (show b ∈ A ⊔ D by rw [hAD]; exact Subgroup.mem_sup_left hb)
  have hMB : ∀ b ∈ B, ∀ m ∈ commV A, b m ∈ commV A := by
    intro b hb m hm
    obtain ⟨a, ha, h⟩ := hBA b hb
    rw [h m hm]
    exact hMA a ha m hm
  have hAB' : ∀ a ∈ A, ∃ b ∈ B, ∀ m ∈ commV A, a m = b m := fun a ha =>
    exists_act_alike hMB hDM
      (show a ∈ B ⊔ D by rw [← hAD]; exact Subgroup.mem_sup_left ha)
  have hle : commV A ≤ commV B := by
    refine (commV_le_cm_commV_of_odd hV hAodd).trans ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, m, hm, rfl⟩
    obtain ⟨b, hb, h⟩ := hAB' a ha
    rw [h m hm]
    exact Subgroup.subset_closure ⟨b, hb, m, rfl⟩
  have heq : commV A = commV B := Subgroup.eq_of_le_of_card_ge hle hcard
  have hDle : commV D ≤ U := by
    refine (commV_mono (le_sup_right.trans hAB)).trans ?_
    refine (commV_sup_le A B).trans ?_
    rw [← heq, sup_idem]
    exact hU
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have hord : Odd (orderOf d) :=
    Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd)
  exact eq_one_of_trivial_on_commV hV hd hord fun w hw => hDU d hd w (hDle hw)

end Weyl

end CFSG.CGT.PushingUpLit.CGT6X.End3
