module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoU3Ck
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1C
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallInner

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check

variable {G : Type} [Group G]

structure QPair (K : Subgroup G) (t a b : G) : Prop where
  ha : a ∈ K
  hb : b ∈ K
  haa : a * a = t
  hbb : b * b = t
  hba : b * a = t * a * b

theorem QPair.mono {P K : Subgroup G} {t a b : G} (h : QPair P t a b) (hPK : P ≤ K) :
    QPair K t a b :=
  ⟨hPK h.ha, hPK h.hb, h.haa, h.hbb, h.hba⟩

theorem orderOf_eq_four {a t : G} (haa : a * a = t) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    orderOf a = 4 := by
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, sq, haa]
    exact ht1
  · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, sq, haa, ht2]

theorem quat_shape {P : Subgroup G} (e : ↥P ≃* QuaternionGroup 2) {t : G} (htP : t ∈ P)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ a b : G, QPair P t a b ∧ ∀ r ∈ P, r ∈ q8List t a b := by
  obtain ⟨i, hi⟩ : ∃ i : ↥P, i = e.symm (QuaternionGroup.a 1) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ↥P, j = e.symm (QuaternionGroup.xa 0) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ↥P, z = e.symm (QuaternionGroup.a 2) := ⟨_, rfl⟩
  have hii : i * i = z := by
    rw [hi, hz, ← map_mul]
    congr 1
  have hjj : j * j = z := by
    rw [hj, hz, ← map_mul]
    congr 1
  have hji : j * i = z * i * j := by
    rw [hj, hi, hz, ← map_mul, ← map_mul, ← map_mul]
    congr 1
  have hzt : (z : G) = t := by
    have hs2 : (⟨t, htP⟩ : ↥P) * ⟨t, htP⟩ = 1 := Subtype.ext ht2
    have hs1 : (⟨t, htP⟩ : ↥P) ≠ 1 := fun h0 => ht1 (congrArg Subtype.val h0)
    have hw := q8_eq_of_sq_eq_one (w := e ⟨t, htP⟩) (by rw [← map_mul, hs2, map_one])
      (fun h0 => hs1 (e.injective (by rw [h0, map_one])))
    have : (⟨t, htP⟩ : ↥P) = z := by rw [hz, ← hw, MulEquiv.symm_apply_apply]
    exact (congrArg Subtype.val this).symm
  refine ⟨i, j, ⟨i.2, j.2, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hzt, ← Subgroup.coe_mul, hii]
  · rw [← hzt, ← Subgroup.coe_mul, hjj]
  · rw [← hzt, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hji]
  · intro r hr
    obtain ⟨w, hw⟩ : ∃ w, e ⟨r, hr⟩ = w := ⟨_, rfl⟩
    have hsw : (⟨r, hr⟩ : ↥P) = e.symm w := by rw [← hw, MulEquiv.symm_apply_apply]
    have key : ∀ s : ↥P, e.symm w = s → r = (s : G) := fun s hs =>
      congrArg Subtype.val (hsw.trans hs)
    rcases TA3.q8_cases w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [key 1 (by rw [← QuaternionGroup.one_def, map_one])]
      simp [q8List]
    · rw [key i hi.symm]
      simp [q8List]
    · rw [key z hz.symm, hzt]
      simp [q8List]
    · rw [key (z * i) (by rw [hz, hi, ← map_mul]; congr 1), Subgroup.coe_mul, hzt]
      simp [q8List]
    · rw [key j hj.symm]
      simp [q8List]
    · rw [key (j * i) (by rw [hj, hi, ← map_mul]; congr 1), Subgroup.coe_mul]
      simp [q8List]
    · rw [key (j * z) (by rw [hj, hz, ← map_mul]; congr 1), Subgroup.coe_mul, hzt]
      simp [q8List]
    · rw [key (j * (z * i)) (by rw [hj, hz, hi, ← map_mul, ← map_mul]; congr 1),
        Subgroup.coe_mul, Subgroup.coe_mul, hzt]
      simp [q8List]

theorem eq_sylow_of_oddCore [Finite G] {Δ : Set (Subgroup G)}
    (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {K : Subgroup G} (hK : K ∈ Δ) {t : G}
    (ht : IsUniqueInvolution K t)
    (hO : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set G)) = ⊥) {P : Subgroup G}
    (hP : IsSylow2In P K) : P = K := by
  have h1 : Balance.oddCoreIn K = ⊥ :=
    le_bot_iff.mp (hO ▸ Balance.oddCoreIn_le_of_isSubnormal (hΔ.isSubnormal_centralizer hK ht))
  have h2 : classicalInvolutionOddCore ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h1
  have hK2 : IsPGroup 2 ↥K := (hΔ.twoGroup K hK).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq h2).trans QuotientGroup.quotientBot)
  exact (hP.2.2 K le_rfl hK2 hP.1).symm

variable {M : Type} [Group M] [DecidableEq M] {ψ : G →* M}

theorem pair_of_qpair {A : Subgroup M} (hL : ∀ y, ψ y ∈ A) {K : Subgroup G} {t a b : G}
    (hp : QPair K t a b) :
    ψ a ∈ A ∧ ψ b ∈ A ∧ ψ a * ψ a = ψ t ∧ ψ b * ψ b = ψ t ∧ ψ b * ψ a = ψ t * ψ a * ψ b := by
  refine ⟨hL a, hL b, ?_, ?_, ?_⟩
  · rw [← map_mul, hp.haa]
  · rw [← map_mul, hp.hbb]
  · simp only [← map_mul, hp.hba]

theorem eq_of_same_type [Finite G] (hψi : Function.Injective ψ) {P A : Subgroup M}
    (hL : ∀ y, ψ y ∈ A) {t : G} (hF : ExitFacts P A (ψ t)) {Δ : Set (Subgroup G)}
    (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ)
    {K K' : Subgroup G} (hK : K ∈ Δ) (hK' : K' ∈ Δ) (hKt : IsUniqueInvolution K t)
    {a b a' b' : G} (hp : QPair K t a b) (hp' : QPair K' t a' b')
    (hty : (ψ a ∈ P ∧ ψ b ∈ P) ↔ (ψ a' ∈ P ∧ ψ b' ∈ P)) : K = K' := by
  have hmem := hF.1 _ _ _ _ (pair_of_qpair hL hp) (pair_of_qpair hL hp') hty (ψ a) (by simp [q8B])
  rw [q8B_eq (ι := ψ)] at hmem
  obtain ⟨x, hx, hxa⟩ := List.mem_map.1 hmem
  have haK' : a ∈ K' := hψi hxa ▸ mem_of_mem_q8List hp'.ha hp'.hb hp'.haa hx
  exact eq_of_orderOf_eq_four hΔ.hyp hK hK' hp.ha haK' (orderOf_eq_four hp.haa hKt.sq hKt.ne_one)

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3
