module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der613
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.IG109

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Aux615

variable {G : Type} [Group G]

theorem mem_normalizer_centralizer [Finite G] {Q : Subgroup G} {g : G} (hg : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((centralizer (Q : Set G) : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q := by
    have := (mem_normalizer_iff.mp (inv_mem hg) q).mp hq
    simpa using this
  have hcq := Subgroup.mem_centralizer_iff.mp hc _ hq'
  calc q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcq]
    _ = g * c * g⁻¹ * q := by group

theorem comm_of_isCyclic {H : Subgroup G} (hH : IsCyclic ↥H) {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥H)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have h : (⟨a, ha⟩ : ↥H) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  exact congrArg Subtype.val h

end Aux615

section L615

variable {G : Type} [Group G] [Finite G]

theorem lemma6_15_of (h61 : Prop6_1) (h610 : Lemma6_10) (h612 : Lemma6_12) (h613 : Lemma6_13)
    (h67 : Prop6_7) (hplane : OddNoncyclicPlane) : Lemma6_15 := by
  intro G _ _ z k S M p hC Q X hmin
  have hp := hC.prime
  have hp2 := hC.p_ne_two
  have hPp : IsPGroup p ↥(Op p M) := isPGroup_Op p hp M
  have hQP : Q ≤ Op p M := hmin.Q_mem.1
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op p M) hmin.Q_mem
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hexp : ∀ x ∈ Q, x ^ p = 1 := hmin.Q_mem.2.2.1
  have hXQ : X ≤ Q := hmin.X_le
  have hQe : IsExtraspecialPGroup p ↥Q := h612 G z k S M p hC Q X hmin
  have hR : ⁅Q, zpowers z⁆ = Q := h613 G z k S M p hC Q X hmin
  have hQN : NF z M Q := hR ▸ nf_commutator_QP h61 hC hmin.Q_mem
  have hE : ExtraG p Q := extraG_of_isExtraspecial hQe
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have := hE.card_Z
    have hZ : zOf Q = ⊥ := le_bot_iff.mp (h ▸ (inf_le_left : zOf Q ≤ Q))
    rw [hZ, Subgroup.card_bot] at this
    exact hp.one_lt.ne this
  have hQP' : ⁅Q, Op p M⁆ ≤ zOf Q := hmin.Q_mem.2.2.2.2.1
  have hPn : Op p M ≤ normalizer (Q : Set G) := (Op_le p M).trans hQn
  have hzP : z ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op p M hC.z_mem
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
      z ∈ normalizer (Y₀ : Set G) → NF z M Y₀ := by
    intro Y₀ hY₀ hY0 hzY
    by_contra hnot
    have hQY : Q ≤ normalizer (Y₀ : Set G) := by
      intro q hq
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (hY₀ hy).2 q hq).symm
    exact h610 G z k S M p hC Y₀ Q (hY₀.trans inf_le_left) hY0 hzY hnot (le_inf hQP hQY) hQ0 hR hQN
  have hB : Op p M ⊓ centralizer (Q : Set G) ≤ Cen z := by
    by_contra hnot
    have hY0 : ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ ≠ ⊥ := fun h =>
      hnot (commutator_zpowers_eq_bot_iff.mp h)
    have hYle : ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ ≤ Op p M ⊓ centralizer (Q : Set G) :=
      commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzP₀)
    have hYz : z ∈ normalizer ((⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator_zpowers hzP₀ (mem_Cen_self z)
    have hYc : ⁅⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆, zpowers z⁆ =
        ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ :=
      commutator_zpowers_idem hC.orderOf_z hp hp2 (hPp.to_le inf_le_left) hzP₀
    have hYN : NF z M ⁅Op p M ⊓ centralizer (Q : Set G), zpowers z⁆ := hA _ hYle hY0 hYz
    exact h610 G z k S M p hC X _ (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
      (le_inf (hYle.trans inf_le_left) (hYle.trans hP₀X)) hY0 hYc hYN
  have hcyc : IsCyclic ↥(Op p M ⊓ centralizer (Q : Set G)) := by
    by_contra hnc
    obtain ⟨V, hVP₀, hVe, hV2⟩ := hplane G p hp hp2 (Op p M ⊓ centralizer (Q : Set G))
      (hPp.to_le inf_le_left) hnc
    apply hmin.X_not
    refine h67 G z k S M p hC p V hp (le_inf (hVP₀.trans inf_le_left) (hVP₀.trans hB)) hVe hV2 ?_ X
      (hXQ.trans (hQP.trans (Op_le_Fm p hp M))) hmin.X_ne
      (sup_le (hVP₀.trans hP₀X) (Subgroup.zpowers_le.mpr hmin.X_inv))
    intro v hvV hv1
    have hv0 : zpowers v ≠ ⊥ := by
      intro h
      apply hv1
      have : v ∈ zpowers v := Subgroup.mem_zpowers v
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    have hvz : z * v = v * z := (Subgroup.mem_centralizer_singleton_iff.mp (hB (hVP₀ hvV))).symm
    exact hA (zpowers v) (Subgroup.zpowers_le.mpr (hVP₀ hvV)) hv0 (mem_normalizer_zpowers_of_comm hvz)
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
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu.2 q hq)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_isCyclic hcyc ha hu)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh')
  rw [hZP]
  exact ⟨hPQP, hcyc, hB⟩

end L615

end CFSG.GH74.GLS.Stage2.Bender.Thm1
