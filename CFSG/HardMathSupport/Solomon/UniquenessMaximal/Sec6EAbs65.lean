module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbs64
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbsCount
public import CFSG.LocalAnalysis.ZStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

namespace PlaneQ
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {Q : Subgroup (V ≃ₗ[ZMod 3] V)} {F : Submodule (ZMod 3) V}

theorem le_of_quat (h : PlaneQ Q F) (S : Subgroup (V ≃ₗ[ZMod 3] V)) (hQS : Q ≤ S)
    (hS : ∀ s ∈ S, ∀ f ∈ F, s f ∈ F) (hSf : ∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1)
    (Q' : Subgroup (V ≃ₗ[ZMod 3] V)) (hQ'S : Q' ≤ S) (hQ' : Nonempty (Q' ≃* QuaternionGroup 2)) :
    Q' ≤ Q := by
  have hinjS : Function.Injective (resHom F S hS) := resHom_injective_of_faith S hS hSf
  let φ' : QuaternionGroup 2 ≃* Q' := hQ'.some.symm
  let emb' : QuaternionGroup 2 →* (F ≃ₗ[ZMod 3] F) :=
    (resHom F S hS).comp ((Subgroup.inclusion hQ'S).comp φ'.toMonoidHom)
  have hinj' : Function.Injective emb' :=
    hinjS.comp ((Subgroup.inclusion_injective hQ'S).comp φ'.injective)
  have hr := plane_q8_unique h.card_F h.emb h.emb_injective emb' hinj'
  intro q' hq'
  have hx : resHom F S hS ⟨q', hQ'S hq'⟩ ∈ emb'.range := by
    refine ⟨φ'.symm ⟨q', hq'⟩, ?_⟩
    show resHom F S hS (Subgroup.inclusion hQ'S (φ' (φ'.symm ⟨q', hq'⟩))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hr] at hx
  obtain ⟨q, hq⟩ := (h.mem_range_emb).1 hx
  have h1 : resHom F S hS ⟨q.1, hQS q.2⟩ = resHom F S hS ⟨q', hQ'S hq'⟩ := by
    rw [← hq]
    exact (resHom_congr (F := F) Q S h.mem hS q ⟨q.1, hQS q.2⟩ rfl).symm
  have := hinjS h1
  have h2 : q.1 = q' := congrArg Subtype.val this
  rw [← h2]
  exact q.2

theorem conj_mem (h : PlaneQ Q F) (S : Subgroup (V ≃ₗ[ZMod 3] V)) (hQS : Q ≤ S)
    (hS : ∀ s ∈ S, ∀ f ∈ F, s f ∈ F) (hSf : ∀ s ∈ S, (∀ f ∈ F, s f = f) → s = 1)
    (w : V ≃ₗ[ZMod 3] V) (hw : ∀ s ∈ S, w * s * w⁻¹ ∈ S) :
    ∀ q ∈ Q, w * q * w⁻¹ ∈ Q := by
  have hle : Q.map (MulAut.conj w).toMonoidHom ≤ S := by
    rintro _ ⟨q, hq, rfl⟩
    exact hw q (hQS hq)
  have hQ' : Nonempty (Q.map (MulAut.conj w).toMonoidHom ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.equivMapOfInjective Q (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).symm.trans h.quat.some⟩
  intro q hq
  exact h.le_of_quat S hQS hS hSf _ hle hQ' ⟨q, hq, rfl⟩

end PlaneQ

namespace Datum
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (D : Datum V)

theorem hN1_of (hK : D.HasKa) : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) →
    ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q := by
  intro a ha ha0 w hw hwa
  obtain ⟨S, hS, hSn⟩ := hK a ha ha0
  exact D.planeQ.conj_mem S hS.Q_le hS.mem_F hS.faith w (hSn w hw hwa)

theorem hN2_of (hJ : D.HasJ) : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q,
    w * q * w⁻¹ ∈ D.Q := by
  intro w hw hwA
  obtain ⟨S, hS, hSn⟩ := hJ
  exact D.planeQ.conj_mem S hS.Q_le hS.mem_F hS.faith w (hSn w hw hwA)

theorem exists_comm_conj (h64 : D.Lemma64Concl) (hnc : ¬ ∀ w ∈ D.W, w * D.t = D.t * w) :
    ∃ g ∈ D.W, (g * D.t * g⁻¹) * D.t = D.t * (g * D.t * g⁻¹) ∧ g * D.t * g⁻¹ ≠ D.t := by
  by_contra hcon
  push Not at hcon
  have : Fintype D.W := Fintype.ofFinite _
  let tW : D.W := ⟨D.t, D.Q_le_W D.t_mem⟩
  have ht1 : tW ≠ 1 := fun h => D.t_ne_one (congrArg Subtype.val h)
  have ht2 : tW * tW = 1 := Subtype.ext D.t_mul_self
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar D.W tW ht1 ht2 (by
    intro g hg
    exact Subtype.ext (hcon g g.2 (congrArg Subtype.val hg)))
  let N' : Subgroup (V ≃ₗ[ZMod 3] V) := N.map D.W.subtype
  have hN'odd : Odd (Nat.card N') := by
    have : Nat.card N' = Nat.card N :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective D.W)
    rw [this]; exact hNodd
  have hN'mem : N' ∈ D.NWQ2 := by
    refine ⟨?_, hN'odd, ?_⟩
    · rintro _ ⟨n, _, rfl⟩; exact n.2
    · rintro q hq _ ⟨n, hn, rfl⟩
      refine ⟨⟨q, D.Q_le_W hq⟩ * n * ⟨q, D.Q_le_W hq⟩⁻¹, hNn.conj_mem n hn _, rfl⟩
  have hcomm : ∀ n ∈ N', D.t * n = n * D.t := by
    intro n hn
    have hmem : n ∈ sSup D.NWQ2 := le_sSup hN'mem hn
    exact (Subgroup.mem_centralizer_iff.1 (h64 D.t_mem) n hmem).symm
  apply hnc
  intro w hw
  set n : V ≃ₗ[ZMod 3] V := w * D.t * w⁻¹ * D.t⁻¹ with hn
  have hnN : n ∈ N' := ⟨_, hN ⟨w, hw⟩, rfl⟩
  have htinv : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right D.t_mul_self
  have hs : w * D.t * w⁻¹ = n * D.t := by
    rw [hn, htinv, mul_assoc _ D.t D.t, D.t_mul_self, mul_one]
  have hs2 : (w * D.t * w⁻¹) * (w * D.t * w⁻¹) = 1 := by
    have : (w * D.t * w⁻¹) * (w * D.t * w⁻¹) = w * (D.t * D.t) * w⁻¹ := by group
    rw [this, D.t_mul_self]; group
  have hn2 : n * n = 1 := by
    have h1 : (n * D.t) * (n * D.t) = n * n * (D.t * D.t) := by
      calc (n * D.t) * (n * D.t) = n * (D.t * n) * D.t := by group
        _ = n * (n * D.t) * D.t := by rw [hcomm n hnN]
        _ = n * n * (D.t * D.t) := by group
    rw [← hs, hs2, D.t_mul_self, mul_one] at h1
    exact h1.symm
  have hn1 : n = 1 := by
    have hord : orderOf (⟨n, hnN⟩ : N') ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      apply Subtype.ext; simpa [sq] using hn2)
    have hcard : orderOf (⟨n, hnN⟩ : N') ∣ Nat.card N' := orderOf_dvd_natCard _
    have h2 : orderOf (⟨n, hnN⟩ : N') = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
      · exact h
      · exfalso
        rw [h] at hcard
        exact (Nat.not_even_iff_odd.2 hN'odd) (even_iff_two_dvd.2 hcard)
    have := orderOf_eq_one_iff.1 h2
    exact congrArg Subtype.val this
  rw [hn1, one_mul] at hs
  calc w * D.t = (w * D.t * w⁻¹) * w := by group
    _ = D.t * w := by rw [hs]

theorem card_img (g : V ≃ₗ[ZMod 3] V) (S : Submodule (ZMod 3) V) :
    Nat.card (img g S) = Nat.card S :=
  (Nat.card_congr (g.submoduleMap S).toEquiv).symm

theorem submodule_eq_of_le_card {S T : Submodule (ZMod 3) V} (h : S ≤ T)
    (hc : Nat.card T ≤ Nat.card S) : S = T := by
  have := AddSubgroup.eq_of_le_of_card_ge (H := S.toAddSubgroup) (K := T.toAddSubgroup) h hc
  exact Submodule.toAddSubgroup_injective this

theorem mem_img_inv {x : V ≃ₗ[ZMod 3] V} {S : Submodule (ZMod 3) V} {v : V} :
    v ∈ img x⁻¹ S ↔ x v ∈ S := by
  rw [mem_img]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : x (x⁻¹ s) = s := by
      simp
    rw [this]; exact hs
  · intro h
    refine ⟨x v, h, ?_⟩
    simp

theorem img_le_of_forall {g : V ≃ₗ[ZMod 3] V} {S T : Submodule (ZMod 3) V}
    (h : ∀ s ∈ S, g s ∈ T) : img g S ≤ T := by
  rintro v hv
  obtain ⟨s, hs, rfl⟩ := mem_img.1 hv
  exact h s hs

@[expose] noncomputable def tp (x : V ≃ₗ[ZMod 3] V) : V ≃ₗ[ZMod 3] V := x⁻¹ * D.t * x

theorem tp_mul_self (x : V ≃ₗ[ZMod 3] V) : D.tp x * D.tp x = 1 := by
  have : D.tp x * D.tp x = x⁻¹ * (D.t * D.t) * x := by unfold tp; group
  rw [this, D.t_mul_self]; group

theorem tp_mem (x : V ≃ₗ[ZMod 3] V) : D.tp x ∈ conjSub x D.Q :=
  ⟨D.t, D.t_mem, by simp [tp]⟩

theorem tp_unique (x : V ≃ₗ[ZMod 3] V) : ∀ s ∈ conjSub x D.Q, s * s = 1 → s = 1 ∨ s = D.tp x := by
  rintro s ⟨r, hr, rfl⟩ hs
  have hr2 : r * r = 1 := by
    have : (MulAut.conj x⁻¹).toMonoidHom (r * r) = 1 := by
      rw [map_mul]; exact hs
    have h2 := (MulAut.conj x⁻¹).injective (this.trans (map_one (MulAut.conj x⁻¹)).symm)
    exact h2
  rcases D.t_unique r hr hr2 with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp [tp]

theorem tp_apply_iff_A (x : V ≃ₗ[ZMod 3] V) (v : V) : v ∈ img x⁻¹ D.A ↔ D.tp x v = v := by
  rw [mem_img_inv]
  constructor
  · intro h
    have := D.t_fix_A _ h
    show x⁻¹ (D.t (x v)) = v
    rw [this]
    simp
  · intro h
    apply D.mem_A_of_t_fix
    have h1 : x⁻¹ (D.t (x v)) = v := h
    have h2 : D.t (x v) = x v := by
      have := congrArg x h1
      have e : x (x⁻¹ (D.t (x v))) = D.t (x v) := by
        simp
      rw [e] at this; exact this
    exact h2

theorem tp_apply_iff_F (x : V ≃ₗ[ZMod 3] V) (v : V) : v ∈ img x⁻¹ D.F ↔ D.tp x v = -v := by
  rw [mem_img_inv]
  constructor
  · intro h
    have := D.t_neg_F _ h
    show x⁻¹ (D.t (x v)) = -v
    rw [this, map_neg]
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) (inv_mul_cancel x)
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at this
    rw [this]
  · intro h
    apply D.mem_F_of_t_neg
    have h1 : x⁻¹ (D.t (x v)) = -v := h
    have e : x (x⁻¹ (D.t (x v))) = D.t (x v) := by
      simp
    rw [← e, h1, map_neg]

theorem tp_ne_one (x : V ≃ₗ[ZMod 3] V) : D.tp x ≠ 1 := by
  intro h
  apply D.t_ne_one
  have : D.t = x * (D.tp x) * x⁻¹ := by unfold tp; group
  rw [this, h]; group

theorem card_img_A (x : V ≃ₗ[ZMod 3] V) : Nat.card (img x⁻¹ D.A) = 9 := by
  rw [card_img, D.card_A]

theorem card_img_F (x : V ≃ₗ[ZMod 3] V) : Nat.card (img x⁻¹ D.F) = 9 := by
  rw [card_img, D.card_F]

theorem A_inter_conj_eq_zero (hN1 : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) →
      ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    {x : V ≃ₗ[ZMod 3] V} (hxW : x ∈ D.W) (hcomm : D.tp x * D.t = D.t * D.tp x)
    (hne : D.tp x ≠ D.t) {a : V} (haA : a ∈ D.A) (haA' : a ∈ img x⁻¹ D.A) : a = 0 := by
  by_contra ha0
  have hxa : x a ∈ D.A := mem_img_inv.1 haA'
  have hxa0 : x a ≠ 0 := fun h => ha0 (by simpa using h)
  have hQ : ∀ q ∈ D.Q, ∀ q' ∈ conjSub x D.Q, q * q' * q⁻¹ ∈ conjSub x D.Q := by
    intro q hq q' hq'
    obtain ⟨r, hr, rfl⟩ := hq'
    have hw : x * q * x⁻¹ ∈ D.W := D.W.mul_mem (D.W.mul_mem hxW (D.Q_le_W hq)) (D.W.inv_mem hxW)
    have hwa : (x * q * x⁻¹) (x a) = x a ∨ (x * q * x⁻¹) (x a) = -(x a) := by
      left
      have h1 : (x * q * x⁻¹) (x a) = x (q a) := by
        simp [LinearEquiv.mul_apply]
      rw [h1, D.Q_fix_A q hq a haA]
    have := hN1 (x a) hxa hxa0 _ hw hwa r hr
    refine ⟨_, this, ?_⟩
    show x⁻¹ * (x * q * x⁻¹ * r * (x * q * x⁻¹)⁻¹) * x⁻¹⁻¹ = q * (x⁻¹ * r * x) * q⁻¹
    group
  have ht'comm : ∀ q ∈ D.Q, q * D.tp x = D.tp x * q := by
    intro q hq
    have hs : q⁻¹ * D.tp x * q ∈ conjSub x D.Q := by
      have := hQ q⁻¹ (D.Q.inv_mem hq) (D.tp x) (D.tp_mem x)
      simpa using this
    have hs2 : (q⁻¹ * D.tp x * q) * (q⁻¹ * D.tp x * q) = 1 := by
      have : (q⁻¹ * D.tp x * q) * (q⁻¹ * D.tp x * q) = q⁻¹ * (D.tp x * D.tp x) * q := by group
      rw [this, D.tp_mul_self]; group
    rcases D.tp_unique x _ hs hs2 with h | h
    · exact absurd (by
        have : D.tp x = q * 1 * q⁻¹ := by rw [← h]; group
        simpa using this) (D.tp_ne_one x)
    · calc q * D.tp x = q * (q⁻¹ * D.tp x * q) := by rw [h]
        _ = D.tp x * q := by group
  have hYQ : ∀ q ∈ D.Q, ∀ v ∈ img x⁻¹ D.A, q v ∈ img x⁻¹ D.A := by
    intro q hq v hv
    rw [D.tp_apply_iff_A] at hv ⊢
    have h1 : D.tp x (q v) = q (D.tp x v) := by
      have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) (ht'comm q hq)
      simpa using this.symm
    rw [h1, hv]
  have hYt : ∀ v ∈ img x⁻¹ D.A, D.t v ∈ img x⁻¹ D.A := by
    intro v hv
    rw [D.tp_apply_iff_A] at hv ⊢
    have h1 : D.tp x (D.t v) = D.t (D.tp x v) := by
      have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hcomm
      simpa using this
    rw [h1, hv]
  have hYF : ∀ f ∈ img x⁻¹ D.A, f ∈ D.F → f = 0 := by
    intro f hfY hfF
    by_contra hf0
    have hFY : ∀ g ∈ D.F, g ∈ img x⁻¹ D.A :=
      D.F_le_of_Q_closed (img x⁻¹ D.A).toAddSubgroup hYQ hfY hfF hf0
    have hFle : D.F ≤ img x⁻¹ D.A := fun g hg => hFY g hg
    have hFeq : D.F = img x⁻¹ D.A :=
      submodule_eq_of_le_card hFle (by rw [card_img_A, D.card_F])
    have : a ∈ D.F := by rw [hFeq]; exact haA'
    exact ha0 (D.inter_eq_zero haA this)
  have hYA : img x⁻¹ D.A ≤ D.A := by
    intro y hy
    obtain ⟨a', ha'Y, ha'A, f, hfY, hfF, hyeq⟩ :=
      D.split_of_t_closed (img x⁻¹ D.A).toAddSubgroup hYt hy
    have := hYF f hfY hfF
    rw [hyeq, this, add_zero]; exact ha'A
  have hAeq : img x⁻¹ D.A = D.A := submodule_eq_of_le_card hYA (by rw [D.card_A, card_img_A])
  have hxinvA : ∀ a' ∈ D.A, x⁻¹ a' ∈ D.A := fun a' ha' => hAeq ▸ (mem_img.2 ⟨a', ha', rfl⟩)
  have hxinvW : x⁻¹ ∈ D.W := D.W.inv_mem hxW
  have h2 := hN2 x⁻¹ hxinvW hxinvA D.t D.t_mem
  have h3 : D.tp x ∈ D.Q := by
    have : x⁻¹ * D.t * x⁻¹⁻¹ = D.tp x := by unfold tp; simp
    rwa [this] at h2
  rcases D.t_unique _ h3 (D.tp_mul_self x) with h | h
  · exact D.tp_ne_one x h
  · exact hne h

theorem tp_eq_neg_t (hN1 : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) →
      ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    {x : V ≃ₗ[ZMod 3] V} (hxW : x ∈ D.W) (hcomm : D.tp x * D.t = D.t * D.tp x)
    (hne : D.tp x ≠ D.t) : ∀ v, D.tp x v = -(D.t v) := by
  have hcomm' : ∀ v, D.tp x (D.t v) = D.t (D.tp x v) := fun v => by
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hcomm
    simpa using this
  have hYt : ∀ v ∈ img x⁻¹ D.A, D.t v ∈ img x⁻¹ D.A := by
    intro v hv
    rw [D.tp_apply_iff_A] at hv ⊢
    rw [hcomm', hv]
  have hYF : img x⁻¹ D.A = D.F := by
    have hle : img x⁻¹ D.A ≤ D.F := by
      intro y hy
      obtain ⟨a', ha'Y, ha'A, f, hfY, hfF, hyeq⟩ :=
        D.split_of_t_closed (img x⁻¹ D.A).toAddSubgroup hYt hy
      have := D.A_inter_conj_eq_zero hN1 hN2 hxW hcomm hne ha'A ha'Y
      rw [hyeq, this, zero_add]; exact hfF
    exact submodule_eq_of_le_card hle (by rw [D.card_F, card_img_A])
  have hFfix : ∀ f ∈ D.F, D.tp x f = f := fun f hf =>
    (D.tp_apply_iff_A x f).1 (by rw [hYF]; exact hf)
  have hAneg : ∀ a ∈ D.A, D.tp x a = -a := by
    intro a ha
    have htpA : D.tp x a ∈ D.A := (D.t_comm_preserves hcomm).1 a ha
    have htpsq : D.tp x (D.tp x a) = a := by
      have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e a) (D.tp_mul_self x)
      simpa using this
    have hu : D.tp x (-(a + D.tp x a)) = -(a + D.tp x a) := by
      rw [map_neg, map_add, htpsq, add_comm]
    have huF : -(a + D.tp x a) ∈ D.F := by
      rw [← hYF]; exact (D.tp_apply_iff_A x _).2 hu
    have huA : -(a + D.tp x a) ∈ D.A := D.A.neg_mem (D.A.add_mem ha htpA)
    have h0 := D.inter_eq_zero huA huF
    have : a + D.tp x a = 0 := neg_eq_zero.1 h0
    exact eq_neg_of_add_eq_zero_right this
  intro v
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  rw [map_add, hAneg a ha, hFfix f hf, D.t_apply ha hf]
  abel

theorem imgA_imgF (hN1 : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) →
      ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    {x : V ≃ₗ[ZMod 3] V} (hxW : x ∈ D.W) (hcomm : D.tp x * D.t = D.t * D.tp x)
    (hne : D.tp x ≠ D.t) : img x⁻¹ D.A = D.F ∧ img x⁻¹ D.F = D.A := by
  have hneg := D.tp_eq_neg_t hN1 hN2 hxW hcomm hne
  constructor
  ·
    have hcomm' : ∀ v, D.tp x (D.t v) = D.t (D.tp x v) := fun v => by
      have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) hcomm
      simpa using this
    have hYt : ∀ v ∈ img x⁻¹ D.A, D.t v ∈ img x⁻¹ D.A := by
      intro v hv
      rw [D.tp_apply_iff_A] at hv ⊢
      rw [hcomm', hv]
    have hle : img x⁻¹ D.A ≤ D.F := by
      intro y hy
      obtain ⟨a', ha'Y, ha'A, f, hfY, hfF, hyeq⟩ :=
        D.split_of_t_closed (img x⁻¹ D.A).toAddSubgroup hYt hy
      have := D.A_inter_conj_eq_zero hN1 hN2 hxW hcomm hne ha'A ha'Y
      rw [hyeq, this, zero_add]; exact hfF
    exact submodule_eq_of_le_card hle (by rw [D.card_F, card_img_A])
  · ext v
    rw [D.tp_apply_iff_F]
    constructor
    · intro h
      apply D.mem_A_of_t_fix
      have := hneg v
      rw [h] at this
      exact (neg_inj.1 this).symm
    · intro hv
      rw [hneg, D.t_fix_A v hv]

section AfterSwap
variable {D} {x : V ≃ₗ[ZMod 3] V} (hAF : img x⁻¹ D.A = D.F ∧ img x⁻¹ D.F = D.A)
include hAF

theorem swap_x_A {a : V} (ha : a ∈ D.A) : x a ∈ D.F := by
  have : a ∈ img x⁻¹ D.F := hAF.2 ▸ ha
  exact mem_img_inv.1 this

theorem swap_x_F {f : V} (hf : f ∈ D.F) : x f ∈ D.A := by
  have : f ∈ img x⁻¹ D.A := hAF.1 ▸ hf
  exact mem_img_inv.1 this

theorem swap_xinv_A {a : V} (ha : a ∈ D.A) : x⁻¹ a ∈ D.F := by
  have : x⁻¹ a ∈ img x⁻¹ D.A := mem_img.2 ⟨a, ha, rfl⟩
  exact hAF.1 ▸ this

theorem swap_xinv_F {f : V} (hf : f ∈ D.F) : x⁻¹ f ∈ D.A := by
  have : x⁻¹ f ∈ img x⁻¹ D.F := mem_img.2 ⟨f, hf, rfl⟩
  exact hAF.2 ▸ this

theorem xx_mem_normalizer
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hxW : x ∈ D.W) : x * x ∈ Subgroup.normalizer (D.Q : Set (V ≃ₗ[ZMod 3] V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 : ∀ a ∈ D.A, (x * x) a ∈ D.A := fun a ha => by
    show x (x a) ∈ D.A
    exact swap_x_F hAF (swap_x_A hAF ha)
  have h2 : ∀ a ∈ D.A, (x⁻¹ * x⁻¹) a ∈ D.A := fun a ha => by
    show x⁻¹ (x⁻¹ a) ∈ D.A
    exact swap_xinv_F hAF (swap_xinv_A hAF ha)
  constructor
  · exact hN2 (x * x) (D.W.mul_mem hxW hxW) h1 h
  · intro hh
    have := hN2 (x⁻¹ * x⁻¹) (D.W.mul_mem (D.W.inv_mem hxW) (D.W.inv_mem hxW)) h2 _ hh
    have e : x⁻¹ * x⁻¹ * (x * x * h * (x * x)⁻¹) * (x⁻¹ * x⁻¹)⁻¹ = h := by group
    rwa [e] at this

theorem conj_fix_F {r : V ≃ₗ[ZMod 3] V} (hr : r ∈ D.Q) {f : V} (hf : f ∈ D.F) :
    (x⁻¹ * r * x) f = f := by
  have h1 : x f ∈ D.A := swap_x_F hAF hf
  have h2 : r (x f) = x f := D.Q_fix_A r hr _ h1
  show x⁻¹ (r (x f)) = f
  rw [h2]
  simp

theorem conj_mem_A {r : V ≃ₗ[ZMod 3] V} (hr : r ∈ D.Q) {a : V} (ha : a ∈ D.A) :
    (x⁻¹ * r * x) a ∈ D.A := by
  have h1 : x a ∈ D.F := swap_x_A hAF ha
  have h2 : r (x a) ∈ D.F := D.planeQ.mem r hr _ h1
  exact swap_xinv_F hAF h2

theorem Q_conjQ_commute :
    ∀ q ∈ D.Q, ∀ q' ∈ conjSub x D.Q, q * q' = q' * q := by
  intro q hq q' hq'
  obtain ⟨r, hr, rfl⟩ := hq'
  have hq'eq : (MulAut.conj x⁻¹).toMonoidHom r = x⁻¹ * r * x := by simp
  rw [hq'eq]
  ext v
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  have hA : (x⁻¹ * r * x) a ∈ D.A := conj_mem_A hAF hr ha
  have hF : (x⁻¹ * r * x) f = f := conj_fix_F hAF hr hf
  have e1 : (q * (x⁻¹ * r * x)) (a + f) = (x⁻¹ * r * x) a + q f := by
    show q ((x⁻¹ * r * x) (a + f)) = _
    rw [map_add, hF, map_add, D.Q_fix_A q hq _ hA]
  have e2 : ((x⁻¹ * r * x) * q) (a + f) = (x⁻¹ * r * x) a + q f := by
    show (x⁻¹ * r * x) (q (a + f)) = _
    rw [map_add, D.Q_fix_A q hq a ha, map_add, conj_fix_F hAF hr (D.planeQ.mem q hq f hf)]
  rw [e1, e2]

theorem Q_inf_conjQ : D.Q ⊓ conjSub x D.Q = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro z ⟨hzQ, r, hr, rfl⟩
  have hzeq : (MulAut.conj x⁻¹).toMonoidHom r = x⁻¹ * r * x := by simp
  ext v
  obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
  rw [hzeq] at hzQ ⊢
  have h1 : (x⁻¹ * r * x) a = a := D.Q_fix_A _ hzQ a ha
  have h2 : (x⁻¹ * r * x) f = f := conj_fix_F hAF hr hf
  simp only [map_add, h1, h2, LinearEquiv.coe_one, id_eq]

theorem mem_sup_conjSub :
    ∀ h ∈ D.Q ⊔ conjSub x D.Q, ∃ q ∈ D.Q, ∃ q' ∈ conjSub x D.Q, h = q * q' := by
  have hc := Q_conjQ_commute hAF
  let P : Subgroup (V ≃ₗ[ZMod 3] V) :=
    { carrier := {h | ∃ q ∈ D.Q, ∃ q' ∈ conjSub x D.Q, h = q * q'}
      mul_mem' := by
        rintro _ _ ⟨q1, hq1, q1', hq1', rfl⟩ ⟨q2, hq2, q2', hq2', rfl⟩
        refine ⟨q1 * q2, D.Q.mul_mem hq1 hq2, q1' * q2', (conjSub x D.Q).mul_mem hq1' hq2', ?_⟩
        calc q1 * q1' * (q2 * q2') = q1 * (q1' * q2) * q2' := by group
          _ = q1 * (q2 * q1') * q2' := by rw [← hc q2 hq2 q1' hq1']
          _ = q1 * q2 * (q1' * q2') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨q, hq, q', hq', rfl⟩
        refine ⟨q⁻¹, inv_mem hq, q'⁻¹, inv_mem hq', ?_⟩
        rw [mul_inv_rev]
        exact (Commute.inv_inv (hc q hq q' hq')).eq.symm }
  have hle : D.Q ⊔ conjSub x D.Q ≤ P := by
    refine sup_le ?_ ?_
    · intro q hq; exact ⟨q, hq, 1, one_mem _, by simp⟩
    · intro q' hq'; exact ⟨1, one_mem _, q', hq', by simp⟩
  exact fun h hh => hle hh

theorem perm_of_normalizes
    (hN1 : ∀ a ∈ D.A, a ≠ 0 → ∀ w ∈ D.W, (w a = a ∨ w a = -a) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hxW : x ∈ D.W) (hcomm : D.tp x * D.t = D.t * D.tp x) (hne : D.tp x ≠ D.t)
    {g : V ≃ₗ[ZMod 3] V}
    (hg : g ∈ Subgroup.normalizer ((D.Q ⊔ conjSub x D.Q : Subgroup (V ≃ₗ[ZMod 3] V)) :
      Set (V ≃ₗ[ZMod 3] V))) : D.PermutesAF g := by
  have hneg := D.tp_eq_neg_t hN1 hN2 hxW hcomm hne
  have hc := Q_conjQ_commute hAF
  have hinf := Q_inf_conjQ hAF
  have htH : D.t ∈ D.Q ⊔ conjSub x D.Q := Subgroup.mem_sup_left D.t_mem
  have hsH : g * D.t * g⁻¹ ∈ D.Q ⊔ conjSub x D.Q := (Subgroup.mem_normalizer_iff.1 hg D.t).1 htH
  obtain ⟨q, hq, q', hq', hs⟩ := mem_sup_conjSub hAF _ hsH
  have hs2 : (g * D.t * g⁻¹) * (g * D.t * g⁻¹) = 1 := by
    have : (g * D.t * g⁻¹) * (g * D.t * g⁻¹) = g * (D.t * D.t) * g⁻¹ := by group
    rw [this, D.t_mul_self]; group
  have hqq : q * q = 1 ∧ q' * q' = 1 := by
    have h1 : q * q * (q' * q') = 1 := by
      calc q * q * (q' * q') = q * (q * q') * q' := by group
        _ = q * (q' * q) * q' := by rw [hc q hq q' hq']
        _ = (q * q') * (q * q') := by group
        _ = 1 := by rw [← hs]; exact hs2
    have h2 : q * q = (q' * q')⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : q * q ∈ D.Q ⊓ conjSub x D.Q :=
      ⟨D.Q.mul_mem hq hq, by rw [h2]; exact (conjSub x D.Q).inv_mem ((conjSub x D.Q).mul_mem hq' hq')⟩
    rw [hinf, Subgroup.mem_bot] at h3
    refine ⟨h3, ?_⟩
    rw [h3, one_mul] at h1; exact h1
  have hts : g * D.t * g⁻¹ ≠ 1 := by
    intro h
    apply D.t_ne_one
    have : D.t = g⁻¹ * (g * D.t * g⁻¹) * g := by group
    rw [this, h]; group
  have hts' : g * D.t * g⁻¹ ≠ D.t * D.tp x := by
    intro h
    obtain ⟨a, ha, ha0⟩ := count_exists_ne_zero D.A D.card_A
    have h1 : ∀ v, (g * D.t * g⁻¹) v = -v := fun v => by
      rw [h]
      show D.t (D.tp x v) = -v
      rw [hneg, map_neg, D.t_t]
    have e : (g * D.t * g⁻¹) (g a) = g (D.t a) := by
      show g (D.t (g⁻¹ (g a))) = g (D.t a)
      have := count_inv_apply g a
      rw [this]
    have h2 := h1 (g a)
    rw [e] at h2
    have h3 : D.t a = -a := g.injective (by rw [h2, map_neg])
    rw [D.t_fix_A a ha] at h3
    exact ha0 (eq_zero_of_eq_neg h3)
  rcases D.t_unique q hq hqq.1 with rfl | rfl <;>
    rcases D.tp_unique x q' hq' hqq.2 with rfl | rfl
  · exact absurd (by simpa using hs) hts
  ·
    right
    have hs' : g * D.t * g⁻¹ = D.tp x := by simpa using hs
    have hgA : ∀ a ∈ D.A, g a ∈ D.F := by
      intro a ha
      have : D.tp x (g a) = g a := by
        rw [← hs']
        show g (D.t (g⁻¹ (g a))) = g a
        rw [count_inv_apply g a, D.t_fix_A a ha]
      have h2 : g a ∈ img x⁻¹ D.A := (D.tp_apply_iff_A x _).2 this
      rw [hAF.1] at h2; exact h2
    have hgF : ∀ f ∈ D.F, g f ∈ D.A := by
      intro f hf
      have : D.tp x (g f) = -(g f) := by
        rw [← hs']
        show g (D.t (g⁻¹ (g f))) = -(g f)
        rw [count_inv_apply g f, D.t_neg_F f hf, map_neg]
      have h2 : g f ∈ img x⁻¹ D.F := (D.tp_apply_iff_F x _).2 this
      rw [hAF.2] at h2; exact h2
    exact ⟨count_img_eq_of_le g _ _ hgA (by rw [D.card_A, D.card_F]),
      count_img_eq_of_le g _ _ hgF (by rw [D.card_A, D.card_F])⟩
  ·
    left
    have hgt : g * D.t = D.t * g := by
      calc g * D.t = (g * D.t * g⁻¹) * g := by group
        _ = D.t * g := by simpa using congrArg (· * g) hs
    obtain ⟨hA, hF⟩ := D.t_comm_preserves hgt
    exact ⟨count_img_eq_of_le g _ _ hA rfl, count_img_eq_of_le g _ _ hF rfl⟩
  · exact absurd (by simpa using hs) hts'

theorem conj_H_of_preserves
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hxW : x ∈ D.W) {g : V ≃ₗ[ZMod 3] V} (hgW : g ∈ D.W) (hA : ∀ a ∈ D.A, g a ∈ D.A)
    (hF : ∀ f ∈ D.F, g f ∈ D.F) :
    ∀ h ∈ D.Q ⊔ conjSub x D.Q, g * h * g⁻¹ ∈ D.Q ⊔ conjSub x D.Q := by
  intro h hh
  obtain ⟨q, hq, q', hq', rfl⟩ := mem_sup_conjSub hAF h hh
  have e : g * (q * q') * g⁻¹ = (g * q * g⁻¹) * (g * q' * g⁻¹) := by group
  rw [e]
  refine (D.Q ⊔ conjSub x D.Q).mul_mem (Subgroup.mem_sup_left (hN2 g hgW hA q hq)) ?_
  apply Subgroup.mem_sup_right
  obtain ⟨r, hr, rfl⟩ := hq'
  have hw : x * g * x⁻¹ ∈ D.W := D.W.mul_mem (D.W.mul_mem hxW hgW) (D.W.inv_mem hxW)
  have hwA : ∀ a ∈ D.A, (x * g * x⁻¹) a ∈ D.A := fun a ha => by
    show x (g (x⁻¹ a)) ∈ D.A
    exact swap_x_F hAF (hF _ (swap_xinv_A hAF ha))
  refine ⟨_, hN2 _ hw hwA r hr, ?_⟩
  show x⁻¹ * (x * g * x⁻¹ * r * (x * g * x⁻¹)⁻¹) * x⁻¹⁻¹ = g * (x⁻¹ * r * x) * g⁻¹
  group

theorem xinv_conj_H
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hxW : x ∈ D.W) : ∀ h ∈ D.Q ⊔ conjSub x D.Q, x⁻¹ * h * x ∈ D.Q ⊔ conjSub x D.Q := by
  intro h hh
  obtain ⟨q, hq, q', hq', rfl⟩ := mem_sup_conjSub hAF h hh
  have e : x⁻¹ * (q * q') * x = (x⁻¹ * q * x) * (x⁻¹ * q' * x) := by group
  rw [e]
  refine (D.Q ⊔ conjSub x D.Q).mul_mem ?_ ?_
  · apply Subgroup.mem_sup_right
    exact ⟨q, hq, by show x⁻¹ * q * x⁻¹⁻¹ = _; group⟩
  · apply Subgroup.mem_sup_left
    obtain ⟨r, hr, rfl⟩ := hq'
    have hmem := Subgroup.mem_normalizer_iff.1 (xx_mem_normalizer hAF hN2 hxW)
      ((x * x)⁻¹ * r * (x * x))
    have : (x * x)⁻¹ * r * (x * x) ∈ D.Q := hmem.2 (by
      rw [show (x * x) * ((x * x)⁻¹ * r * (x * x)) * (x * x)⁻¹ = r by group]; exact hr)
    have e2 : x⁻¹ * (MulAut.conj x⁻¹).toMonoidHom r * x = (x * x)⁻¹ * r * (x * x) := by
      show x⁻¹ * (x⁻¹ * r * x⁻¹⁻¹) * x = _
      group
    rw [e2]; exact this

omit hAF in
theorem inv_maps {g : V ≃ₗ[ZMod 3] V} {S T : Submodule (ZMod 3) V} (h : img g S = T) :
    ∀ t ∈ T, g⁻¹ t ∈ S := by
  intro t ht
  rw [← h] at ht
  obtain ⟨s, hs, rfl⟩ := mem_img.1 ht
  have := count_inv_apply g s
  simpa [this] using hs

omit hAF in
theorem permutesAF_inv {g : V ≃ₗ[ZMod 3] V} (hg : D.PermutesAF g) : D.PermutesAF g⁻¹ := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨count_img_eq_of_le _ _ _ (inv_maps h1) (by rw [D.card_A]),
      count_img_eq_of_le _ _ _ (inv_maps h2) rfl⟩
  · right
    exact ⟨count_img_eq_of_le _ _ _ (inv_maps h2) (by rw [D.card_A, D.card_F]),
      count_img_eq_of_le _ _ _ (inv_maps h1) (by rw [D.card_A, D.card_F])⟩

theorem conj_H_of_perm
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hxW : x ∈ D.W) {g : V ≃ₗ[ZMod 3] V} (hgW : g ∈ D.W) (hg : D.PermutesAF g) :
    ∀ h ∈ D.Q ⊔ conjSub x D.Q, g * h * g⁻¹ ∈ D.Q ⊔ conjSub x D.Q := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hA : ∀ a ∈ D.A, g a ∈ D.A := fun a ha => h1 ▸ mem_img.2 ⟨a, ha, rfl⟩
    have hF : ∀ f ∈ D.F, g f ∈ D.F := fun f hf => h2 ▸ mem_img.2 ⟨f, hf, rfl⟩
    exact conj_H_of_preserves hAF hN2 hxW hgW hA hF
  ·
    intro h hh
    set v : V ≃ₗ[ZMod 3] V := g * x with hv
    have hvW : v ∈ D.W := D.W.mul_mem hgW hxW
    have hvA : ∀ a ∈ D.A, v a ∈ D.A := fun a ha => by
      show g (x a) ∈ D.A
      have : g (x a) ∈ img g D.F := mem_img.2 ⟨x a, swap_x_A hAF ha, rfl⟩
      rwa [h2] at this
    have hvF : ∀ f ∈ D.F, v f ∈ D.F := fun f hf => by
      show g (x f) ∈ D.F
      have : g (x f) ∈ img g D.A := mem_img.2 ⟨x f, swap_x_F hAF hf, rfl⟩
      rwa [h1] at this
    have h3 := conj_H_of_preserves hAF hN2 hxW hvW hvA hvF _ (xinv_conj_H hAF hN2 hxW h hh)
    have e : v * (x⁻¹ * h * x) * v⁻¹ = g * h * g⁻¹ := by rw [hv]; group
    rwa [e] at h3

theorem normalizes_of_perm
    (hN2 : ∀ w ∈ D.W, (∀ a ∈ D.A, w a ∈ D.A) → ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q)
    (hxW : x ∈ D.W) {g : V ≃ₗ[ZMod 3] V} (hgW : g ∈ D.W) (hg : D.PermutesAF g) :
    g ∈ Subgroup.normalizer ((D.Q ⊔ conjSub x D.Q : Subgroup (V ≃ₗ[ZMod 3] V)) :
      Set (V ≃ₗ[ZMod 3] V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_H_of_perm hAF hN2 hxW hgW hg h, fun hh => ?_⟩
  have := conj_H_of_perm hAF hN2 hxW (D.W.inv_mem hgW) (permutesAF_inv hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

end AfterSwap

theorem lemma65_abs (hK : D.HasKa) (hJ : D.HasJ) : D.Lemma65Concl := by
  have hN1 := D.hN1_of hK
  have hN2 := D.hN2_of hJ
  have h64 := D.lemma64_abs hK
  by_cases hα : ∀ w ∈ D.W, ∀ q ∈ D.Q, w * q * w⁻¹ ∈ D.Q
  · exact Or.inl hα
  right
  have hnc : ¬ ∀ w ∈ D.W, w * D.t = D.t * w := by
    intro hc; apply hα; intro w hw
    exact hN2 w hw (D.t_comm_preserves (hc w hw)).1
  obtain ⟨g, hgW, hgc, hgne⟩ := D.exists_comm_conj h64 hnc
  have hxW : g⁻¹ ∈ D.W := D.W.inv_mem hgW
  have htp : D.tp g⁻¹ = g * D.t * g⁻¹ := by simp [tp]
  have hcomm : D.tp g⁻¹ * D.t = D.t * D.tp g⁻¹ := by rw [htp]; exact hgc
  have hne : D.tp g⁻¹ ≠ D.t := by rw [htp]; exact hgne
  have hAF := D.imgA_imgF hN1 hN2 hxW hcomm hne
  have hperm : ∀ g' ∈ D.NW (D.Q ⊔ conjSub g⁻¹ D.Q), D.PermutesAF g' := fun g' hg' =>
    perm_of_normalizes hAF hN1 hN2 hxW hcomm hne hg'.2
  have hperm' : ∀ g' ∈ D.W, D.PermutesAF g' → g' ∈ D.NW (D.Q ⊔ conjSub g⁻¹ D.Q) :=
    fun g' hg' hp => ⟨hg', normalizes_of_perm hAF hN2 hxW hg' hp⟩
  exact ⟨g⁻¹, hxW, ⟨Q_inf_conjQ hAF, Q_conjQ_commute hAF⟩, xx_mem_normalizer hAF hN2 hxW,
    hAF, hperm, D.count_dichotomy g⁻¹ hxW hAF hN1 hperm hperm'⟩

end Datum
end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
