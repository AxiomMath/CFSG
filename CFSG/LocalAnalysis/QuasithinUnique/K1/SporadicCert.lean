module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique

theorem noStronglyClosedElemAbelian_of_center_witness {X : Type} [Group X] [Finite X]
    (Q : Subgroup X) (hQ : IsSylowTwoOf Q ⊤) (z : X)
    (hcen : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z)
    (g h : X) (hg : g⁻¹ * z * g ∈ Q) (hh : h⁻¹ * z * h ∈ Q)
    (hnc : (g⁻¹ * z * g) * (h⁻¹ * z * h) ≠ (h⁻¹ * z * h) * (g⁻¹ * z * g)) :
    NoStronglyClosedElemAbelian X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine noStronglyClosedElemAbelian_of_sylow Q hQ fun A hA => ?_
  by_contra hA1
  have hQp : IsPGroup 2 Q := hQ.2.1
  have : Group.IsNilpotent Q := hQp.isNilpotent
  have hAQ : A ≤ Q := hA.le
  have hAn : (A.subgroupOf Q).Normal := by
    refine ⟨fun x hx y => ?_⟩
    have hx' : (x : X) ∈ A := hx
    have hconj : (((y : X)⁻¹)⁻¹ * (x : X) * (y : X)⁻¹) ∈ Q := by
      simpa using Q.mul_mem (Q.mul_mem y.2 x.2) (Q.inv_mem y.2)
    have := hA.closed (x : X) hx' ((y : X)⁻¹) hconj
    show (y : X) * (x : X) * (y : X)⁻¹ ∈ A
    simpa using this
  have hAne : A.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAQ ha⟩ : Q) ∈ A.subgroupOf Q := ha
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hAne)
  have hcA : ((c : Q) : X) ∈ A := c.2.1
  have hcQ : ((c : Q) : X) ∈ Q := (c : Q).2
  have hcc : ∀ q ∈ Q, ((c : Q) : X) * q = q * ((c : Q) : X) := by
    intro q hq
    have := Subgroup.mem_center_iff.mp c.2.2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  have hc1' : ((c : Q) : X) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext h'))
  have hzA : z ∈ A := by
    rcases hcen _ hcQ hcc with h' | h'
    · exact absurd h' hc1'
    · rw [← h']; exact hcA
  have hgA : g⁻¹ * z * g ∈ A := hA.closed z hzA g hg
  have hhA : h⁻¹ * z * h ∈ A := hA.closed z hzA h hh
  apply hnc
  exact congrArg Subtype.val (hA.elem.1.is_comm.comm ⟨_, hgA⟩ ⟨_, hhA⟩)

end CFSG.QuasithinUnique.K1
