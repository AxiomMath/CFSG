module

public import CFSG.CGT.PushingUpLit.SolK.RSmall

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

theorem centralizer_singleton_eq_zpowers {G : Type} [Group G] (x : G) :
    Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, mem_centralizer_zpowers_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h]
      _ = x := by group
  · intro h
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [h]

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem mem_Q_of_theta_eq_one (hR : RSmall S) {m : G} (hm : m ∈ M) (h : S.θ ⟨m, hm⟩ = 1) :
    m ∈ pCoreOf 2 M := by
  have hW : ∀ w ∈ S.D.W, m * w * m⁻¹ = w :=
    (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨m, hm⟩).1 h
  have hcent : m ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨w, hw, r, hr, rfl⟩ := S.q_eq q hq
    have h1 := hW w hw
    have h2 := SolCfg.RSmall.central S hR hm hr
    have h3 : m * (w * r) * m⁻¹ = w * r :=
      calc m * (w * r) * m⁻¹ = (m * w * m⁻¹) * (m * r * m⁻¹) := by group
        _ = w * r := by rw [h1, h2]
    calc w * r * m = (m * (w * r) * m⁻¹) * m := by rw [h3]
      _ = m * (w * r) := by group
  exact S.hyp.charTwo M S.hyp.maxLocal.1 ⟨hm, hcent⟩

theorem theta_eq_one_of_mem_Q {q : G} (hq : q ∈ pCoreOf 2 M) :
    S.θ ⟨q, pCoreOf_le_self M hq⟩ = 1 :=
  (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨q, pCoreOf_le_self M hq⟩).2 fun _ hw =>
    mul_inv_eq_iff_eq_mul.2 (S.q_comm_W hq hw)

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
