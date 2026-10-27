module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.TL4SepTwoA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {X Q : Type} [Group X] [Finite X] [Group Q]

theorem eq_one_of_mem_member_of_map_eq_one {M : Subgroup X} {z : X} (hz : IsUniqueInvolution M z)
    (h2 : IsPGroup 2 ↥M) (f : X →* Q) (hzf : z ∉ f.ker) {m : X} (hm : m ∈ M) (hfm : f m = 1) :
    m = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨m, hm⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.mp (by simpa using hk))
  have hdvd : 2 ∣ orderOf m := hk ▸ dvd_pow_self 2 hk0
  set y := m ^ (orderOf m / 2) with hy
  have hord : orderOf y = 2 := orderOf_pow_orderOf_div (orderOf_pos m).ne' hdvd
  have hyM : y ∈ M := M.pow_mem hm _
  have hyy : y * y = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hyz : y = z := (hz.unique y hyM hyy).resolve_left hy1
  apply hzf
  rw [MonoidHom.mem_ker, ← hyz, hy, map_pow, hfm, one_pow]

theorem inj_members_of_twoGroupKernel {Φ : Set (Subgroup X)} (hS : Q8Section X Φ)
    (h2' : ∀ J ∈ Φ, IsPGroup 2 ↥J) (f : X →* Q) (hN : IsPGroup 2 ↥f.ker)
    (hno : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → z ∉ f.ker) :
    (∀ M ∈ Φ, ∀ m ∈ M, f m = 1 → m = 1) ∧
      (∀ M ∈ Φ, ∀ M' ∈ Φ, M.map f = M'.map f → M = M') := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ M ∈ Φ, ∀ m ∈ M, f m = 1 → m = 1 := by
    intro M hM m hm hfm
    obtain ⟨z, hz⟩ := (hS.hyp.omega1 M hM).1
    exact eq_one_of_mem_member_of_map_eq_one hz (h2' M hM) f (hno M hM z hz) hm hfm
  refine ⟨hker, fun M hM M' hM' hmap => ?_⟩
  by_contra hne
  have hle : M' ≤ M ⊔ f.ker := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ : f x ∈ M.map f := hmap ▸ Subgroup.mem_map_of_mem f hx
    have hk : y⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hy hk
    rwa [mul_inv_cancel_left] at this
  have hP : IsPGroup 2 ↥(M ⊔ f.ker) := (h2' M hM).to_sup_of_normal_right hN
  obtain ⟨S, hSle⟩ := hP.exists_le_sylow
  have hcomm : Commutes M M' :=
    Q3CP.l67Gen X Φ hS.hyp S M (TL4.mem_RSet_self hM (h2' M hM)) M'
      (TL4.mem_RSet_self hM' (h2' M' hM')) (le_sup_left.trans hSle) (hle.trans hSle) hne
  have hab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
    intro a ha b hb
    obtain ⟨b', hb', hbb'⟩ : f b ∈ M'.map f := hmap ▸ Subgroup.mem_map_of_mem f hb
    have hf : f (a * b) = f (b * a) := by
      rw [map_mul, map_mul, ← hbb', ← map_mul, ← map_mul, hcomm a ha b' hb']
    have h1 : (a * b) * (b * a)⁻¹ = 1 :=
      hker M hM _ (M.mul_mem (M.mul_mem ha hb) (M.inv_mem (M.mul_mem hb ha)))
        (by rw [map_mul, map_inv, hf, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  obtain ⟨P, hPM, hPnc⟩ := (hS.hyp.omega1 M hM).2
  have hPeq : P = M := (hPM.2.2 M le_rfl (h2' M hM) hPM.1).symm
  apply hPnc
  subst hPeq
  exact ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
