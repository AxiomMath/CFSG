module

public import CFSG.GH74.E2.Cl2CaseDefs
public import CFSG.GH74.E2.Cl2Cl3

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

section Aux

variable {Q : Type*} [Group Q]

theorem aux_sqsub_le (A : Subgroup Q) : sqsub A ≤ A :=
  (Subgroup.closure_le _).2 (fun w hw => by
    obtain ⟨u, hu, rfl⟩ := hw
    exact A.mul_mem hu hu)

theorem aux_mem_sqsub {A : Subgroup Q} {u : Q} (hu : u ∈ A) : u * u ∈ sqsub A :=
  Subgroup.subset_closure ⟨u, hu, rfl⟩

theorem aux_eq_one_of_zpow_odd [Finite Q] (hQ : IsPGroup 2 Q) {x : Q} {m : ℤ} (hm : Odd m)
    (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hQ x
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : (orderOf x : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  by_contra hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.1 (by rw [hj]; rfl))
  have h3 : (2 : ℤ) ∣ m := by
    refine dvd_trans ?_ h2
    rw [hj]
    rcases j with _ | j'
    · exact absurd rfl hj0
    · exact ⟨2 ^ j', by push_cast; ring⟩
  exact (Int.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)

end Aux

variable {Q : Type*} [Group Q] [Finite Q] {a b : MulAut Q} {N : Subgroup Q}

theorem caseD (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hc : CaseDHyp Q a b N) : False := by
  obtain ⟨hP, hsqN, hfa, hfb, hrk⟩ := hc
  have hDn : (dsub Q).Normal := inferInstance
  have hDc : ∀ u ∈ dsub Q, ∀ v ∈ dsub Q, u * v = v * u := Cl3.dsub_comm hQ h
  have hbot : fixSub b ≠ ⊥ := by
    intro hb
    have h4 := BPair.relIndex_fixSub_b hQ h.four h.bpair
    rw [hb] at h4
    simp at h4
  obtain ⟨⟨x, hxb⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  have hfixz : zpowers x ≤ fixSub b := zpowers_le.2 hxb
  have hDZ : ∀ d ∈ dsub Q, d ∈ zpowers x → d = 1 := fun d hd hdz => hfb d hd (hfixz hdz)
  have hsqc : ∀ u ∈ dsub Q, u * (x * x) = (x * x) * u := fun u hu =>
    commutatorElement_eq_one_iff_mul_comm.1 (Cl3.sq_cent hQ h hu x)
  set V : Subgroup Q := zpowers (x * x) with hV
  have hVx : V ≤ zpowers x := by
    rw [hV, zpowers_le]
    exact ⟨2, zpow_two x⟩
  have hcommDV : ∀ u ∈ dsub Q, ∀ v ∈ V, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hv
    exact ((show Commute u (x * x) from hsqc u hu).zpow_right k).eq
  set H : Subgroup Q := dsub Q ⊔ zpowers x with hH
  set R : Subgroup Q := sqsub (dsub Q) ⊔ V with hR
  set L : Subgroup Q := dsub Q ⊔ V with hL
  have hRL : R ≤ L := sup_le_sup (aux_sqsub_le _) le_rfl
  have hLH : L ≤ H := sup_le_sup le_rfl hVx
  have hint : dsub Q ⊓ V ≤ sqsub (dsub Q) ⊓ V := by
    intro d hd
    have : d = 1 := hDZ d hd.1 (hVx hd.2)
    rw [this]
    exact one_mem _
  have hnU : ∀ u ∈ dsub Q, ∀ r ∈ sqsub (dsub Q), u * r * u⁻¹ ∈ sqsub (dsub Q) := by
    intro u hu r hr
    have : u * r = r * u := hDc u hu r (aux_sqsub_le _ hr)
    rw [this, mul_inv_cancel_right]
    exact hr
  have hnV : ∀ v ∈ V, ∀ r ∈ V, v * r * v⁻¹ ∈ V := fun v hv r hr =>
    V.mul_mem (V.mul_mem hv hr) (V.inv_mem hv)
  have hRLidx : R.relIndex L = (sqsub (dsub Q)).relIndex (dsub Q) := by
    have := relIndex_sup_of_commute hcommDV (aux_sqsub_le _) (le_refl V) hnU hnV hint
    rw [Subgroup.relIndex_self, mul_one] at this
    exact this
  have hxL : x ∉ L := by
    intro hxL
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hxL
    have hyz' : y = x * z⁻¹ := by rw [← hyz]; group
    have hyx : y ∈ zpowers x := by
      rw [hyz']
      exact (zpowers x).mul_mem (mem_zpowers x) ((zpowers x).inv_mem (hVx hz))
    have hy1 : y = 1 := hDZ y hy hyx
    have hxz : x = z := by rw [← hyz, hy1, one_mul]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
    have hk2 : (x * x) ^ k = x ^ (2 * k) := by rw [zpow_mul, zpow_two]
    have hk3 : x ^ (2 * k) = x := by rw [← hk2, hk, ← hxz]
    have hxk : x ^ (2 * k - 1) = 1 := by
      rw [zpow_sub_one, hk3, mul_inv_cancel]
    exact hx1' (aux_eq_one_of_zpow_odd hQ ⟨k - 1, by ring⟩ hxk)
  have hLH2 : 2 ≤ L.relIndex H := by
    have hne1 : L.relIndex H ≠ 1 := by
      intro h1
      have := Subgroup.relIndex_eq_one.1 h1
      exact hxL (this (Subgroup.mem_sup_right (mem_zpowers x)))
    have hne0 : L.relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hDN : dsub Q ≤ normalizer (R : Set Q) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype (fun r hr => ?_)
    have hcent : R ≤ centralizer ({d} : Set Q) := by
      refine sup_le (fun w hw => ?_) (zpowers_le.2 ?_)
      · rw [mem_centralizer_singleton_iff]
        exact hDc w (aux_sqsub_le _ hw) d hd
      · rw [mem_centralizer_singleton_iff]
        exact (hsqc d hd).symm
    have h1 := mem_centralizer_singleton_iff.1 (hcent hr)
    rw [← h1, mul_inv_cancel_right]
    exact hr
  have hxN : x ∈ normalizer (R : Set Q) := by
    refine Subgroup.mem_normalizer_fintype (fun r hr => ?_)
    have hconj : R ≤ R.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le ?_ ?_
      · refine (Subgroup.closure_le _).2 (fun w hw => ?_)
        obtain ⟨u, hu, rfl⟩ := hw
        have hxu : x * u * x⁻¹ ∈ dsub Q := hDn.conj_mem u hu x
        have : x * (u * u) * x⁻¹ = (x * u * x⁻¹) * (x * u * x⁻¹) := by group
        show x * (u * u) * x⁻¹ ∈ R
        rw [this]
        exact Subgroup.mem_sup_left (aux_mem_sqsub hxu)
      · refine zpowers_le.2 ?_
        show x * (x * x) * x⁻¹ ∈ R
        have : x * (x * x) * x⁻¹ = x * x := by group
        rw [this]
        exact Subgroup.mem_sup_right (mem_zpowers (x * x))
    exact hconj hr
  have hHN : H ≤ normalizer (R : Set Q) := sup_le hDN (zpowers_le.2 hxN)
  have hnormRH : ∀ g ∈ H, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    (Subgroup.mem_normalizer_iff.1 (hHN hg) r).1 hr
  have hsqRH : ∀ g ∈ H, g * g ∈ R := by
    intro g hg
    obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hz
    have hcN : ⁅x ^ i, u⁆ ∈ N := by
      rw [← commutatorElement_inv]
      exact N.inv_mem (Cl3.comm_mem hQ h hu (x ^ i))
    have hcc : ∀ w : Q, ⁅x ^ i, u⁆ * w = w * ⁅x ^ i, u⁆ := fun w =>
      (Subgroup.mem_center_iff.1 (h.N_central hcN) w).symm
    have e1 : x ^ i * u = ⁅x ^ i, u⁆ * u * x ^ i := by
      rw [commutatorElement_def]
      group
    have e2 : u * x ^ i * (u * x ^ i) = (u * u) * ⁅x ^ i, u⁆ * ((x * x) ^ i) := by
      rw [(Commute.refl x).mul_zpow i]
      calc u * x ^ i * (u * x ^ i) = u * (x ^ i * u) * x ^ i := by group
        _ = u * (⁅x ^ i, u⁆ * u * x ^ i) * x ^ i := by rw [e1]
        _ = (u * ⁅x ^ i, u⁆) * u * x ^ i * x ^ i := by group
        _ = (⁅x ^ i, u⁆ * u) * u * x ^ i * x ^ i := by rw [← hcc u]
        _ = (u * u) * ⁅x ^ i, u⁆ * (x ^ i * x ^ i) := by
          rw [mul_assoc ⁅x ^ i, u⁆ u u, hcc (u * u)]
          group
    rw [e2]
    obtain ⟨w, hw, hwc⟩ := hsqN _ hcN
    refine R.mul_mem (R.mul_mem (Subgroup.mem_sup_left (aux_mem_sqsub hu)) ?_) ?_
    · rw [hwc]
      exact Subgroup.mem_sup_left (aux_mem_sqsub hw)
    · exact Subgroup.mem_sup_right (mem_zpowers_iff.2 ⟨i, rfl⟩)
  have hle := FourGen.relIndex_le h.four hnormRH hsqRH
  have hmul := Subgroup.relIndex_mul_relIndex R L H hRL hLH
  rw [hRLidx] at hmul
  have h32 : 16 * 2 ≤ R.relIndex H := by
    rw [← hmul]
    exact Nat.mul_le_mul hrk hLH2
  omega

end CFSG.GH74.E2
