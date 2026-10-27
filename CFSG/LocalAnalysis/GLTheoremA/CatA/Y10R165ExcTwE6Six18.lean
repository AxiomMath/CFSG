module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six17

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag

section Certificate


theorem concl165Avoid_of_unitary_layers {H G k : Type} [Group H] [Finite H] [Group G]
    [Finite G] [Field k] [Finite k] [CharP k 2] {n : ℕ} (hk : Nat.card k = (2 ^ n) ^ 2)
    (hn : 2 ≤ n) {π : H →* G} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {Ã : Subgroup H} (hÃ : IsElemAbelian p Ã)
    {x z : H} (hxÃ : x ∈ Ã) (hzÃ : z ∈ Ã) (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    {J J₁ : Subgroup G} (hJx : J ≤ Subgroup.centralizer ({π x} : Set G))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({π x} : Set G))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hJz : J ≤ Subgroup.centralizer ({π z} : Set G))
    (hJ₁x : J₁ ≤ Subgroup.centralizer ({π x} : Set G)) (hJ₁q : CFSG.Open.IsQuasisimple ↥J₁)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J₁, Commute a b)
    (eJ : ↥J ≃* ↥(unitarySU 2 n k 3)) (eJ₁ : ↥J₁ ≃* ↥(unitarySU 2 n k 3))
    {F₀ : Subgroup G} (hF₀le : F₀ ≤ J) (hF₀el : IsElemAbelian q F₀)
    (hF₀card : Nat.card F₀ = q ^ 2) {s₀ : G} (hs₀J₁ : s₀ ∈ J₁) (hs₀q : orderOf s₀ = q)
    (hs₀Z : (⟨s₀, hs₀J₁⟩ : ↥J₁) ∉ Subgroup.center ↥J₁) :
    Concl165Avoid H p q Ã π.ker := by
  have hJperf : ⁅J, J⁆ = J :=
    (Subgroup.isPerfect_iff (H := J)).mp (Group.IsPerfect.mk hJq.1)
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ :=
    (Subgroup.isPerfect_iff (H := J₁)).mp (Group.IsPerfect.mk hJ₁q.1)
  obtain ⟨S, eS, hSleC, -, hSker, hSπ, -⟩ :=
    exists_section_lift_SU3 hk hn hπ hker hJperf hJx eJ
  obtain ⟨S₁, eS₁, hS₁leC, -, hS₁ker, hS₁π, -⟩ :=
    exists_section_lift_SU3 hk hn hπ hker hJ₁perf hJ₁x eJ₁
  have hQn : (J.subgroupOf (J ⊓ Subgroup.centralizer ({π z} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_inf le_rfl hJz)).2
      (inf_le_left.trans Subgroup.le_normalizer)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine.concl165Avoid_of_sections hπ hker hp hq
    hÃ hxÃ hzÃ hx1 hzx hJx hJn hJq hpJ le_rfl hJz hQn hJq hpJ eS eS₁ hSleC hS₁leC hSπ hS₁π
    hSker hS₁ker hcomm hF₀le hF₀el hF₀card hs₀J₁ hs₀q hs₀Z

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
