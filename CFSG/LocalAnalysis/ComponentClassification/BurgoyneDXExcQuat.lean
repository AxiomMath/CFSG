module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcInv
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSchur

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup
open scoped MatrixGroups

variable {G L : Type} [Group G] [Group L] [Finite G] [Finite L]

theorem exists_quaternion (α : G →* L) (hα : Function.Surjective α) (hker : α.ker ≤ center G)
    (hker2 : IsPGroup 2 α.ker) {Q : Subgroup L} (hQ : ⁅Q, Q⁆ = Q) {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, k)) {c : L} (hcZ : c ∈ center L)
    (hcQ : c ∈ Q) (hc2 : orderOf c = 2) {b : G} (hb : b ∈ ⁅Q.comap α, Q.comap α⁆)
    (hbc : α b = c) :
    (∀ x ∈ ⁅Q.comap α, Q.comap α⁆, x * x = 1 → x ≠ 1 → x = b) ∧
    ∃ x ∈ ⁅Q.comap α, Q.comap α⁆, ∃ y ∈ ⁅Q.comap α, Q.comap α⁆, x * x = b ∧ y * y = b ∧
      x * y * x⁻¹ * y⁻¹ = b ∧ x ≠ 1 ∧ x ≠ b ∧ y ≠ 1 ∧ y ≠ b ∧ y ≠ x ∧ y ≠ b * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := perfectLift_spec α hα hker hker2 hQ hk e
  have hmap := key.1
  have hinj := key.2.2
  set T₀ := ⁅Q.comap α, Q.comap α⁆ with hT₀
  have hT₀Q : ∀ x ∈ T₀, α x ∈ Q := fun x hx =>
    (Subgroup.commutator_le_self (Q.comap α) hx : x ∈ Q.comap α)
  have huniq : ∀ x ∈ T₀, x * x = 1 → x ≠ 1 → x = b := by
    intro x hx hxx hx1
    have hαx : α x ≠ 1 := fun h => hx1 (hinj x hx h)
    have hαc := eq_of_mul_self_of_sl hk e hcZ hcQ hc2 (hT₀Q x hx)
      (by rw [← map_mul, hxx, map_one]) hαx
    have := hinj (x * b⁻¹) (mul_mem hx (inv_mem hb)) (by rw [map_mul, map_inv, hαc, hbc,
      mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  refine ⟨huniq, ?_⟩
  let αQ : T₀ →* Q := (α.comp T₀.subtype).codRestrict Q fun x => hT₀Q x x.2
  let π₀ : T₀ →* SL(2, k) := e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 Q)).comp αQ)
  have hαQinj : Function.Injective αQ := by
    intro x y h
    have h' : α (x : G) = α (y : G) := congrArg Subtype.val h
    apply Subtype.ext
    have := hinj ((x : G) * (y : G)⁻¹) (mul_mem x.2 (inv_mem y.2))
      (by rw [map_mul, map_inv, h', mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  have hπ₀ : Function.Surjective π₀ := by
    intro g
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm g)
    have hqQ : (q : L) ∈ T₀.map α := by rw [hmap]; exact q.2
    obtain ⟨x, hx, hxq⟩ := hqQ
    refine ⟨⟨x, hx⟩, ?_⟩
    change e (QuotientGroup.mk (αQ ⟨x, hx⟩)) = g
    have : αQ ⟨x, hx⟩ = q := Subtype.ext hxq
    rw [this, hq, MulEquiv.apply_symm_apply]
  have hodd : Nat.Coprime 2 (Nat.card π₀.ker) := by
    have hle : π₀.ker.map αQ ≤ pPrimeCore 2 Q := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      change e (QuotientGroup.mk (αQ x)) = 1 at hx
      rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hαQinj] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  obtain ⟨a₀, b₀, hab⟩ := exists_sq_add_sq_eq_neg_one hk
  have hE := isPGroup_two_closure_quaternion (neg_one_mem_center_sl (k := k))
    (by rw [neg_one_mul, neg_neg]) qI_mul_self (qJ_mul_self hab) (qJ_mul_qI hab)
  obtain ⟨T, hTE, hTinj⟩ := exists_lift_of_odd_kernel π₀ hπ₀ hodd hE
  have hiT : qI ∈ T.map π₀ := by rw [hTE]; exact subset_closure (Set.mem_insert _ _)
  have hjT : qJ hab ∈ T.map π₀ := by
    rw [hTE]; exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨x, hxT, hxi⟩ := hiT
  obtain ⟨y, hyT, hyj⟩ := hjT
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [map_one] at hbc
    rw [← hbc, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hbb : b * b = 1 := hinj (b * b) (mul_mem hb hb) (by
    rw [map_mul, hbc, ← pow_two, ← hc2, pow_orderOf_eq_one])
  have hπb : π₀ ⟨b, hb⟩ = -1 := by
    apply sl2_eq_neg_one_of_mul_self hk
    · rw [← map_mul, show (⟨b, hb⟩ : T₀) * ⟨b, hb⟩ = 1 from Subtype.ext hbb, map_one]
    · intro h
      change e (QuotientGroup.mk (αQ ⟨b, hb⟩)) = 1 at h
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h
      have hdvd : orderOf (⟨αQ ⟨b, hb⟩, h⟩ : pPrimeCore 2 Q) ∣ Nat.card (pPrimeCore 2 Q) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at hdvd
      have : orderOf (α b) = 2 := by rw [hbc, hc2]
      change orderOf (α b) ∣ _ at hdvd
      rw [this] at hdvd
      exact absurd (Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card) (by norm_num)
  have hneg1 : (-1 : SL(2, k)) * -1 = 1 := by rw [neg_one_mul, neg_neg]
  have hT_neg : ∀ w ∈ T, π₀ w = -1 → (w : G) = b := by
    intro w hw hw1
    have hw2 : w * w = 1 := hTinj _ (mul_mem hw hw) (by rw [map_mul, hw1, hneg1])
    have hw1' : (w : G) ≠ 1 := by
      intro h
      have h' : w = 1 := Subtype.ext h
      rw [h', map_one] at hw1
      have h00 := congrArg (fun M : SL(2, k) => (M : Matrix (Fin 2) (Fin 2) k) 0 0) hw1
      simp at h00
      apply Ring.two_ne_zero hk
      linear_combination h00
    exact huniq w w.2 (congrArg Subtype.val hw2) hw1'
  have hne := qI_ne hk hab
  have hinvneg : (-1 : SL(2, k))⁻¹ = -1 := inv_eq_of_mul_eq_one_right hneg1
  have hcomm : qI * qJ hab * qI⁻¹ * (qJ hab)⁻¹ = -1 := by
    calc qI * qJ hab * qI⁻¹ * (qJ hab)⁻¹ = (qI * qJ hab) * (qJ hab * qI)⁻¹ := by group
      _ = (qI * qJ hab) * (-1 * (qI * qJ hab))⁻¹ := by rw [qJ_mul_qI]
      _ = -1 := by rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, hinvneg]
  refine ⟨x, x.2, y, y.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hT_neg _ (mul_mem hxT hxT) (by rw [map_mul, hxi, qI_mul_self])
  · exact hT_neg _ (mul_mem hyT hyT) (by rw [map_mul, hyj, qJ_mul_self])
  · exact hT_neg _ (mul_mem (mul_mem (mul_mem hxT hyT) (inv_mem hxT)) (inv_mem hyT))
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxi, hyj, hcomm])
  · intro h
    have h' : x = 1 := Subtype.ext h
    rw [h', map_one] at hxi
    exact hne.1 hxi.symm
  · intro h
    have h' : x = ⟨b, hb⟩ := Subtype.ext h
    rw [h', hπb] at hxi
    exact hne.2.1 hxi.symm
  · intro h
    have h' : y = 1 := Subtype.ext h
    rw [h', map_one] at hyj
    exact hne.2.2.1 hyj.symm
  · intro h
    have h' : y = ⟨b, hb⟩ := Subtype.ext h
    rw [h', hπb] at hyj
    exact hne.2.2.2.1 hyj.symm
  · intro h
    have h' : y = x := Subtype.ext h
    rw [h', hxi] at hyj
    exact hne.2.2.2.2.1 hyj.symm
  · intro h
    have h' : y = ⟨b, hb⟩ * x := Subtype.ext h
    rw [h', map_mul, hπb, hxi] at hyj
    exact hne.2.2.2.2.2 hyj.symm

end CFSG.ComponentClassification.Burgoyne.DX
