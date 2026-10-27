module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der615
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Steps

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

section L615

theorem step9_15_of (h94 : Prop9_4) (h916 : Lemma9_16) (h612 : Step9_12) (h613 : Step9_13)
    (h911 : Prop9_11c) (hplane : OddNoncyclicPlane) : Step9_15 := by
  intro G _ _ z k S M p hC Q X hmin
  have hp := hC.prime
  have hp2 := hC.odd
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : z * z = 1 := hC.z_mul_z
  have hPp : IsPGroup p ↥(Op p M) := hC.P_pgroup
  have hQP : Q ≤ Op p M := hmin.Q_mem.1
  have hQp : IsPGroup p ↥Q := hPp.to_le hQP
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op' p M) hmin.Q_mem
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hexp : ∀ x ∈ Q, x ^ p = 1 := hmin.Q_mem.2.2.1
  have hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := hmin.Q_mem.2.2.2.1
  have hXQ : X ≤ Q := hmin.X_le
  have hQe : IsExtraspecialPGroup p ↥Q := h612 G z k S M p hC Q X hmin
  have hR : ⁅Q, zpowers z⁆ = Q := h613 G z k S M p hC Q X hmin
  have hQN : NN z p (Op p M) Q := hR ▸ nn_commutator_QP h94 hC hmin.Q_mem
  have hE : ExtraG p Q := extraG_of_isExtraspecial hQe
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have := hE.card_Z
    have hZ : zOf Q = ⊥ := le_bot_iff.mp (h ▸ (inf_le_left : zOf Q ≤ Q))
    rw [hZ, Subgroup.card_bot] at this
    exact hp.one_lt.ne this
  have hQP' : ⁅Q, Op p M⁆ ≤ zOf Q := hmin.Q_mem.2.2.2.2.1
  have hPn : Op p M ≤ normalizer (Q : Set G) := (Op_le' p M).trans hQn
  have hzP : z ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op' p M hC.z_mem
  have hPQP : Op p M = Q ⊔ (Op p M ⊓ centralizer (Q : Set G)) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨u, huQ, hc⟩ := exists_inner_of_extraspecial hp hQe hexp hQP' hPn hg
      have hmem : u⁻¹ * g ∈ Op p M ⊓ centralizer (Q : Set G) :=
        ⟨(Op p M).mul_mem ((Op p M).inv_mem (hQP huQ)) hg, hc⟩
      have : g = u * (u⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem_sup huQ hmem
    · exact sup_le hQP inf_le_left
  have hzP₀ : z ∈ normalizer ((Op p M ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf hzP (mem_normalizer_centralizer hzQ)
  have hP₀X : Op p M ⊓ centralizer (Q : Set G) ≤ normalizer (X : Set G) :=
    inf_le_right.trans ((Subgroup.centralizer_le (fun x hx => hXQ hx)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hA : ∀ Y₀ : Subgroup G, Y₀ ≤ Op p M ⊓ centralizer (Q : Set G) → Y₀ ≠ ⊥ →
      z ∈ normalizer (Y₀ : Set G) → NN z p (Op p M) Y₀ := by
    intro Y₀ hY₀ hY0 hzY
    by_contra hnot
    have hQY : Q ≤ normalizer (Y₀ : Set G) := by
      intro q hq
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hY₀ hy).2 q hq).symm
    exact h916 G z k S M p hC Y₀ Q (hY₀.trans inf_le_left) hY0 hzY hnot (le_inf hQP hQY) hQ0 hR hQN
  have hB : Op p M ⊓ centralizer (Q : Set G) ≤ Cen z := by
    by_contra hnot
    have hY0 : ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ ≠ ⊥ := fun h =>
      hnot (commutator_zpowers_eq_bot_iff.mp h)
    have hYle : ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ ≤ Op p M ⊓ centralizer (Q : Set G) :=
      commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzP₀)
    have hYz : z ∈ normalizer
        ((⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator_zpowers hzP₀ (mem_Cen_self z)
    have hYc : ⁅⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆, zpowers z⁆ =
        ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ :=
      commutator_zpowers_idem hC.orderOf_z hp hp2 (hPp.to_le inf_le_left) hzP₀
    have hYN : NN z p (Op p M) ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ := hA _ hYle hY0 hYz
    exact h916 G z k S M p hC X _ (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
      (le_inf (hYle.trans inf_le_left) (hYle.trans hP₀X)) hY0 hYc hYN
  have hZQ : zOf Q ≤ Q := inf_le_left
  have hZc : zOf Q ≤ centralizer (Q : Set G) := inf_le_right
  have hZX : zOf Q ≤ normalizer (X : Set G) :=
    hZc.trans ((Subgroup.centralizer_le (fun x hx => hXQ hx)).trans
      (Subgroup.centralizer_le_normalizer _))
  have he : zOf Q ≤ Cen z := by
    by_contra hne
    have hzZ : M ≤ normalizer ((zOf Q : Subgroup G) : Set G) := le_normalizer_zOf hQn
    have hzZ' : z ∈ normalizer ((zOf Q : Subgroup G) : Set G) := hzZ hC.z_mem
    have hQ₁le : ⁅zOf Q, zpowers z⁆ ≤ zOf Q :=
      commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzZ')
    have hQ₁0 : ⁅zOf Q, zpowers z⁆ ≠ ⊥ := fun h => hne (commutator_zpowers_eq_bot_iff.mp h)
    have hQ₁C : Cen z ≤ normalizer ((⁅zOf Q, zpowers z⁆ : Subgroup G) : Set G) := fun c hc =>
      le_normalizer_commutator_zpowers (hzZ (hC.cen_le hc)) hc
    have hQ₁c : ⁅⁅zOf Q, zpowers z⁆, zpowers z⁆ = ⁅zOf Q, zpowers z⁆ :=
      commutator_zpowers_idem hC.orderOf_z hp hp2 (hQp.to_le hZQ) hzZ'
    have hQ₁N : NN z p (Op p M) ⁅zOf Q, zpowers z⁆ :=
      h94 G z k S M p hC _ ((hQ₁le.trans hZQ).trans hQP) hQ₁0 hQ₁C hQ₁c
    exact h916 G z k S M p hC X _ (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
      (le_inf ((hQ₁le.trans hZQ).trans hQP) (hQ₁le.trans hZX)) hQ₁0 hQ₁c hQ₁N
  have hfix : ∀ y ∈ Q, z * y * z⁻¹ = y → y ∈ zOf Q := by
    intro y hyQ hyz
    by_contra hyZ
    have hRy := commutator_le_centralizer_of_fixed hp hp2 hz2 hzQ hexp hcl he hyQ hyz
    rw [hR] at hRy
    exact hyZ ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.mp (hRy hq)⟩
  have hXnc : ¬ X ≤ Cen z := by
    intro hXc
    have hXZ : X ≤ zOf Q := fun x hx => hfix x (hXQ hx) (by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hXc hx)
      rw [← this]; group)
    have hQX : Q ≤ normalizer (X : Set G) := by
      intro q hq
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hXZ hy).2 q hq).symm
    exact h916 G z k S M p hC X Q (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
      (le_inf hQP hQX) hQ0 hR hQN
  have hX₁0 : ⁅X, zpowers z⁆ ≠ ⊥ := fun h => hXnc (commutator_zpowers_eq_bot_iff.mp h)
  have hX₁le : ⁅X, zpowers z⁆ ≤ X :=
    commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hmin.X_inv)
  have hX₁z : z ∈ normalizer ((⁅X, zpowers z⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_zpowers hmin.X_inv (mem_Cen_self z)
  have hX₁c : ⁅⁅X, zpowers z⁆, zpowers z⁆ = ⁅X, zpowers z⁆ :=
    commutator_zpowers_idem hC.orderOf_z hp hp2 (hQp.to_le hXQ) hmin.X_inv
  have hX₁Q : ⁅X, zpowers z⁆ ≤ Q := hX₁le.trans hXQ
  have hP₀X₁ :
      Op p M ⊓ centralizer (Q : Set G) ≤ normalizer ((⁅X, zpowers z⁆ : Subgroup G) : Set G) :=
    inf_le_right.trans ((Subgroup.centralizer_le (fun x hx => hX₁Q hx)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hcyc : IsCyclic ↥(Op p M ⊓ centralizer (Q : Set G)) := by
    by_contra hnc
    obtain ⟨V, hVP₀, hVe, hV2⟩ := hplane G p hp hp2 (Op p M ⊓ centralizer (Q : Set G))
      (hPp.to_le inf_le_left) hnc
    have hX₁N : NN z p (Op p M) ⁅X, zpowers z⁆ := by
      refine h911 G z k S M p hC V ⁅X, zpowers z⁆
        (le_inf (hVP₀.trans inf_le_left) (hVP₀.trans hB)) hVe hV2 ?_ (hX₁Q.trans hQP) hX₁0 hX₁c
        (sup_le (hVP₀.trans hP₀X₁) (Subgroup.zpowers_le.mpr hX₁z))
      intro v hvV hv1
      have hv0 : zpowers v ≠ ⊥ := by
        intro h
        apply hv1
        have : v ∈ zpowers v := Subgroup.mem_zpowers v
        rw [h] at this
        exact Subgroup.mem_bot.mp this
      have hvz : z * v = v * z :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hB (hVP₀ hvV))).symm
      exact hA (zpowers v) (Subgroup.zpowers_le.mpr (hVP₀ hvV)) hv0
        (mem_normalizer_zpowers_of_comm hvz)
    exact h916 G z k S M p hC X ⁅X, zpowers z⁆ (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
      (le_inf (hX₁Q.trans hQP) (hX₁le.trans Subgroup.le_normalizer)) hX₁0 hX₁c hX₁N
  have hZP : zOf (Op p M) = Op p M ⊓ centralizer (Q : Set G) := by
    apply le_antisymm
    · intro w hw
      exact ⟨hw.1, (Subgroup.centralizer_le (fun x hx => hQP hx)) hw.2⟩
    · intro u hu
      refine ⟨hu.1, ?_⟩
      show u ∈ centralizer ((Op p M : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ Q ⊔ (Op p M ⊓ centralizer (Q : Set G)) := hPQP ▸ hh
      have hle : Q ⊔ (Op p M ⊓ centralizer (Q : Set G)) ≤ centralizer ({u} : Set G) := by
        refine sup_le (fun q hq => ?_) (fun a ha => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hu.2 q hq)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_isCyclic hcyc ha hu)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh')
  rw [hZP]
  exact ⟨hPQP, hcyc, hB⟩

end L615

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
