module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultCover

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

open Subgroup

variable {J T : Type} [Group J] [Group T]

theorem ker_eq_bot_of_not_sq_dvd [Finite J] (π : J →* T) (hπ : Function.Surjective π)
    (hJ : Group.IsPerfect J) (hz : π.ker ≤ center J) {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p π.ker) (hT : ¬ p ^ 2 ∣ Nat.card T) : π.ker = ⊥ := by
  classical
  have hTfin : Finite T := Finite.of_surjective π hπ
  obtain ⟨P⟩ : Nonempty (Sylow p J) := inferInstance
  have hker : π.ker ≤ (P : Subgroup J) := by
    have hnorm : π.ker.Normal := inferInstance
    exact hp.le_sylow_of_normal P
  let f : ↥(P : Subgroup J) →* ↥((P : Subgroup J).map π) :=
    (π.comp (P : Subgroup J).subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
  have hfker : f.ker ≤ center ↥(P : Subgroup J) := by
    intro x hx
    have hx1 : π (x : J) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact h
    have hxc : (x : J) ∈ center J := hz (MonoidHom.mem_ker.mpr hx1)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc g)
  have hcyc : IsCyclic ↥((P : Subgroup J).map π) := by
    have hPp : IsPGroup p ↥((P : Subgroup J).map π) := P.isPGroup'.map π
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hPp
    have hdvd : Nat.card ↥((P : Subgroup J).map π) ∣ Nat.card T :=
      Subgroup.card_subgroup_dvd_card _
    rw [ha] at hdvd
    have ha1 : a ≤ 1 := by
      by_contra h
      exact hT ((pow_dvd_pow p (by omega : 2 ≤ a)).trans hdvd)
    interval_cases a
    · have : Nat.card ↥((P : Subgroup J).map π) = 1 := by simpa using ha
      have : Subsingleton ↥((P : Subgroup J).map π) := (Nat.card_eq_one_iff_unique.mp this).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.card ↥((P : Subgroup J).map π)).Prime := ⟨by rw [ha]; simpa using Fact.out⟩
      exact isCyclic_of_prime_card (p := Nat.card ↥((P : Subgroup J).map π)) rfl
  have hcomm : ∀ a b : ↥(P : Subgroup J), a * b = b * a := fun a b =>
    (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hfker).is_comm.comm a b
  rw [eq_bot_iff]
  intro z hzk
  obtain ⟨k, hk⟩ := hp ⟨z, hzk⟩
  have hzp : ∃ n : ℕ, z ^ (p ^ n) = 1 := ⟨k, by simpa using congrArg Subtype.val hk⟩
  have h1 := central_mem_commutator_sylow hJ P (hz hzk) hzp
  have h2 : ⁅(P : Subgroup J), (P : Subgroup J)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have := hcomm ⟨a, ha⟩ ⟨b, hb⟩
    have h3 : a * b = b * a := congrArg Subtype.val this
    rw [commutatorElement_def, Subgroup.mem_bot]
    simp [h3, mul_assoc]
  rw [h2] at h1
  exact h1

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
