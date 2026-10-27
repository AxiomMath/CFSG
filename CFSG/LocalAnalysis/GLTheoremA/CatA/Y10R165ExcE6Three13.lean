module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three12
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165LayerPullback
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin2

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open
open scoped Matrix MatrixGroups Pointwise

section Certificate


theorem concl165Avoid_of_lifted_layers {H G 𝔽 : Type} [Group H] [Finite H] [Group G] [Finite G]
    [Field 𝔽] [Finite 𝔽] [CharP 𝔽 2]
    {π : H →* G} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H)
    (h2ker : ¬ 2 ∣ Nat.card π.ker)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqF : q ∣ Nat.card 𝔽 - 1)
    {Ã : Subgroup H} (hÃ : IsElemAbelian p Ã)
    {x z : H} (hxÃ : x ∈ Ã) (hzÃ : z ∈ Ã) (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    {J J₁ Q : Subgroup G}
    (hJx : J ≤ Subgroup.centralizer ({π x} : Set G))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({π x} : Set G))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hQJ : Q ≤ J) (hQz : Q ≤ Subgroup.centralizer ({π z} : Set G))
    (hQn : (Q.subgroupOf (J ⊓ Subgroup.centralizer ({π z} : Set G))).Normal)
    (hQq : CFSG.Open.IsQuasisimple ↥Q) (hpQ : p ∣ Nat.card Q)
    (eJ : ↥J ≃* SL(3, 𝔽)) (eJ₁ : ↥J₁ ≃* SL(3, 𝔽))
    (hJ₁x : J₁ ≤ Subgroup.centralizer ({π x} : Set G))
    (hJ₁perf : ⁅J₁, J₁⁆ = J₁)
    {s₀ : G} (hs₀J₁ : s₀ ∈ J₁) (hs₀q : orderOf s₀ = q)
    (hs₀Z : (⟨s₀, hs₀J₁⟩ : ↥J₁) ∉ Subgroup.center ↥J₁)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J₁, Commute a b) :
    Concl165Avoid H p q Ã π.ker := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hJperf : ⁅J, J⁆ = J :=
    (Subgroup.isPerfect_iff (H := J)).mp (Group.IsPerfect.mk hJq.1)
  obtain ⟨S, eS, hSleC, -, hSker, hSπ, -⟩ :=
    exists_section_lift hπ hker hJperf hJx eJ h2ker
  obtain ⟨S₁, eS₁, hS₁leC, -, hS₁ker, hS₁π, -⟩ :=
    exists_section_lift hπ hker hJ₁perf hJ₁x eJ₁ h2ker
  obtain ⟨F₀, hF₀le, hF₀el, hF₀card⟩ :=
    exists_elemAbelian_le_of_mulEquiv
      (e := eJ.trans (Subgroup.topEquiv (G := SL(3, 𝔽))).symm)
      (T := LinEngine.diagSLSub (F := 𝔽) 2 q) le_top
      (LinEngine.isElemAbelian_diagSLSub (F := 𝔽))
      (LinEngine.card_diagSLSub (F := 𝔽) hqF)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine.concl165Avoid_of_sections hπ hker hp hq
    hÃ hxÃ hzÃ hx1 hzx hJx hJn hJq hpJ hQJ hQz hQn hQq hpQ eS eS₁ hSleC hS₁leC hSπ hS₁π
    hSker hS₁ker hcomm hF₀le hF₀el hF₀card hs₀J₁ hs₀q hs₀Z

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
