module

public import CFSG.CGT.PushingUpLit.SolK.Kernel

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

@[expose] def RSmall {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}
    (_S : SolCfg G M X n) : Prop := Nat.card ↥(rOf M X) ≤ 2

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem RSmall.central (hR : RSmall S) {m r : G} (hm : m ∈ M) (hr : r ∈ rOf M X) :
    m * r * m⁻¹ = r := by
  by_cases hr1 : r = 1
  · rw [hr1]; group
  · have hmr : m * r * m⁻¹ ∈ rOf M X := S.R_normalized hm hr
    have hne : (⟨m * r * m⁻¹, hmr⟩ : ↥(rOf M X)) ≠ 1 := fun h => hr1 (by
      have h1 : m * r * m⁻¹ = 1 := congrArg Subtype.val h
      have h2 := congrArg (fun t => m⁻¹ * t * m) h1
      simpa [mul_assoc] using h2)
    have hne' : (⟨r, hr⟩ : ↥(rOf M X)) ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
    exact congrArg Subtype.val (eq_of_card_le_two hR hne hne')

theorem RSmall.sq (hR : RSmall S) {r : G} (hr : r ∈ rOf M X) : r ^ 2 = 1 := by
  by_contra h
  have hr2 : r ^ 2 ∈ rOf M X := (rOf M X).pow_mem hr 2
  have hne : (⟨r ^ 2, hr2⟩ : ↥(rOf M X)) ≠ 1 := fun h' => h (congrArg Subtype.val h')
  have hr1 : (⟨r, hr⟩ : ↥(rOf M X)) ≠ 1 := fun h' => h (by
    have : r = 1 := congrArg Subtype.val h'
    rw [this]; simp)
  have := eq_of_card_le_two hR hne hr1
  have h3 : r ^ 2 = r := congrArg Subtype.val this
  apply hr1
  apply Subtype.ext
  have : r * r = r := by rw [← pow_two]; exact h3
  simpa using this

theorem RSmall.elem (hR : RSmall S) : ∀ q ∈ pCoreOf 2 M, q ^ 2 = 1 := by
  intro q hq
  obtain ⟨w, hw, r, hr, rfl⟩ := S.q_eq q hq
  have hcomm : w * r = r * w := S.W_comm_R hw hr
  have : (w * r) ^ 2 = w ^ 2 * r ^ 2 := by
    rw [pow_two, pow_two, pow_two]
    calc w * r * (w * r) = w * (r * w) * r := by group
      _ = w * (w * r) * r := by rw [← hcomm]
      _ = w * w * (r * r) := by group
  rw [this, S.D.sq hw, SolCfg.RSmall.sq S hR hr, mul_one]

noncomputable def projWFun (q : ↥(pCoreOf 2 M)) : ↥S.D.W :=
  ⟨Classical.choose (S.q_eq q q.2), (Classical.choose_spec (S.q_eq q q.2)).1⟩

theorem projWFun_spec (q : ↥(pCoreOf 2 M)) :
    ∃ r ∈ rOf M X, (q : G) = (projWFun S q : G) * r :=
  (Classical.choose_spec (S.q_eq q q.2)).2

theorem projWFun_eq {q : ↥(pCoreOf 2 M)} {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (h : (q : G) = w * r) : (projWFun S q : G) = w := by
  obtain ⟨r', hr', h'⟩ := projWFun_spec S q
  exact (S.decomp_unique (projWFun S q).2 hw hr' hr (h'.symm.trans h)).1

noncomputable def projW : ↥(pCoreOf 2 M) →* ↥S.D.W :=
  MonoidHom.mk' (projWFun S) (fun q q' => by
    obtain ⟨r, hr, h⟩ := projWFun_spec S q
    obtain ⟨r', hr', h'⟩ := projWFun_spec S q'
    have hcomm : (r : G) * (projWFun S q' : G) = (projWFun S q' : G) * r :=
      (S.W_comm_R (projWFun S q').2 hr).symm
    have hprod : ((q * q' : ↥(pCoreOf 2 M)) : G) =
        ((projWFun S q : G) * (projWFun S q' : G)) * (r * r') := by
      show (q : G) * (q' : G) = _
      rw [h, h']
      calc (projWFun S q : G) * r * ((projWFun S q' : G) * r') =
          (projWFun S q : G) * (r * (projWFun S q' : G)) * r' := by group
        _ = (projWFun S q : G) * ((projWFun S q' : G) * r) * r' := by rw [hcomm]
        _ = _ := by group
    exact Subtype.ext (projWFun_eq S (S.D.W.mul_mem (projWFun S q).2 (projWFun S q').2)
      ((rOf M X).mul_mem hr hr') hprod))

theorem projW_apply {q : ↥(pCoreOf 2 M)} {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (h : (q : G) = w * r) : ((projW S q : ↥S.D.W) : G) = w :=
  projWFun_eq S hw hr h

theorem mem_ker_projW {q : ↥(pCoreOf 2 M)} : q ∈ (projW S).ker ↔ (q : G) ∈ rOf M X := by
  constructor
  · intro h
    obtain ⟨r, hr, e⟩ := projWFun_spec S q
    have h1 : ((projW S q : ↥S.D.W) : G) = 1 := by
      have : projW S q = 1 := h
      rw [this]; rfl
    have h2 : (projWFun S q : G) = 1 := h1
    rw [e, h2, one_mul]
    exact hr
  · intro h
    refine Subtype.ext ?_
    exact projW_apply S S.D.W.one_mem h (by simp)

theorem projW_surjective : Function.Surjective (projW S) := by
  intro w
  refine ⟨⟨(w : G), S.W_le_Q w.2⟩, Subtype.ext ?_⟩
  exact projW_apply S w.2 (rOf M X).one_mem (by simp)

theorem projW_conj {m : G} (hm : m ∈ M) (q : ↥(pCoreOf 2 M))
    (hq : m * (q : G) * m⁻¹ ∈ pCoreOf 2 M) :
    ((projW S ⟨m * (q : G) * m⁻¹, hq⟩ : ↥S.D.W) : G) =
      m * ((projW S q : ↥S.D.W) : G) * m⁻¹ := by
  obtain ⟨r, hr, e⟩ := projWFun_spec S q
  have e' : m * (q : G) * m⁻¹ =
      (m * (projWFun S q : G) * m⁻¹) * (m * r * m⁻¹) := by rw [e]; group
  exact projW_apply S (S.W_normalized hm (projWFun S q).2) (S.R_normalized hm hr) e'

theorem card_Q : Nat.card ↥(pCoreOf 2 M) = Nat.card ↥S.D.W * Nat.card ↥(rOf M X) := by
  have h := Subgroup.card_ker_mul_card_range (projW S)
  rw [MonoidHom.range_eq_top.2 (projW_surjective S), Subgroup.card_top] at h
  have hker : Nat.card (projW S).ker = Nat.card ↥(rOf M X) := by
    refine Nat.card_congr (Equiv.ofBijective (fun k => ⟨((k : ↥(pCoreOf 2 M)) : G),
      (mem_ker_projW S).1 k.2⟩) ⟨?_, ?_⟩)
    · intro k k' hk
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))
    · intro r
      exact ⟨⟨⟨(r : G), r.2.1⟩, (mem_ker_projW S).2 r.2⟩, rfl⟩
  rw [hker] at h
  rw [mul_comm]
  exact h.symm

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
