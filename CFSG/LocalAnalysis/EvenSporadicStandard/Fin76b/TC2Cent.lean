module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Count
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralOddComplement

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

namespace OuterE

variable (h : OuterE G L z t T E)

include h in
theorem exists_two_subgroup_cent (hzt : ∃ y : G, y * z * y⁻¹ = z * t)
    (haut : Nat.card (MulAut ↥E) = 1920) (hT : Nat.card ↥T = 512) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) {x : G} (hxQ : x ∈ Q) (hxT : x ∉ T)
    (hxN : x ∈ normalizer (T : Set G)) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ centralizer (E : Set G) ∧ 8 ≤ Nat.card R := by
  have hY2 : IsPGroup 2 (T ⊔ zpowers x : Subgroup G) :=
    hQ.to_le (sup_le hTQ (zpowers_le.2 hxQ))
  have hYN : (T ⊔ zpowers x : Subgroup G) ≤ normalizer (E : Set G) :=
    sup_le (fun g hg => h.mem_normalizer_of_mem_normalizer hzt (Subgroup.le_normalizer hg))
      (zpowers_le.2 (h.mem_normalizer_of_mem_normalizer hzt hxN))
  refine ⟨(T ⊔ zpowers x) ⊓ centralizer (E : Set G), hY2.to_le inf_le_left, inf_le_right, ?_⟩
  have h1 := card_le_mul_card_cent E _ hY2 hYN haut
  have hTY : T ≤ (T ⊔ zpowers x : Subgroup G) := le_sup_left
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hTY
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  have hc1 : c ≠ 1 := by
    intro hc1
    rw [hc1, mul_one] at hc
    have : T = (T ⊔ zpowers x : Subgroup G) := Subgroup.eq_of_le_of_card_ge hTY hc.le
    exact hxT (this ▸ mem_sup_right (mem_zpowers x))
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hc
    exact Nat.card_pos.ne' hc
  have hc2 : 2 ≤ c := by omega
  have h2 : 1024 ≤ Nat.card ↥(T ⊔ zpowers x : Subgroup G) := by
    rw [hc, hT]
    nlinarith
  omega

include h in
omit [Finite G] in
theorem card_zpowers_sup : Nat.card ↥(zpowers z ⊔ zpowers t : Subgroup G) = 4 := by
  have hzt_cent : zpowers t ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_le]
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((show Commute z t from h.cfg.t_comm_z.symm).zpow_left k).eq
  have hdisj : Disjoint (zpowers z) (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxt
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq hxz with h1 | h1
    · exact h1
    · rcases mem_zpowers_sq_eq_one h.cfg.t_sq hxt with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) h.cfg.z_ne_t
  have e := Nat.card_congr (prodSupEquiv hzt_cent hdisj).toEquiv
  rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, h.cfg.z_order, h.t_order] at e
  exact e.symm

end OuterE

@[expose] noncomputable def sylowCentOfMax (E : Subgroup G) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) :
    Sylow 2 ↥(centralizer (E : Set G)) :=
  { toSubgroup := S.subgroupOf (centralizer (E : Set G))
    isPGroup' := hS2.comap_subtype
    is_maximal' := by
      intro Q hQ hSQ
      have hR : Q.map (centralizer (E : Set G)).subtype = S := by
        refine hSmax _ (hQ.map _) (by rintro _ ⟨q, -, rfl⟩; exact q.2) ?_
        intro s hs
        exact ⟨⟨s, hSC hs⟩, hSQ (mem_subgroupOf.2 hs), rfl⟩
      ext x
      constructor
      · intro hx
        show (x : G) ∈ S
        rw [← hR]
        exact ⟨x, hx, rfl⟩
      · intro hx
        exact hSQ hx }

theorem card_le_of_maximal (E : Subgroup G) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRC : R ≤ centralizer (E : Set G)) :
    Nat.card R ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SS := sylowCentOfMax E hS2 hSC hSmax
  obtain ⟨P, hP⟩ :=
    (hR2.comap_subtype : IsPGroup 2 (R.subgroupOf (centralizer (E : Set G)))).exists_le_sylow
  have h1 : Nat.card (SS : Subgroup ↥(centralizer (E : Set G))) =
      Nat.card (P : Subgroup ↥(centralizer (E : Set G))) := by
    rw [Sylow.card_eq_multiplicity SS, Sylow.card_eq_multiplicity P]
  have h2 : Nat.card (R.subgroupOf (centralizer (E : Set G))) ≤
      Nat.card (P : Subgroup ↥(centralizer (E : Set G))) := Subgroup.card_le_of_le hP
  have h3 : Nat.card (R.subgroupOf (centralizer (E : Set G))) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
  have h4 : Nat.card (SS : Subgroup ↥(centralizer (E : Set G))) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
  omega

namespace OuterE

variable (h : OuterE G L z t T E)

include h in
theorem sylow_centralizer_shape' (hzt : ∃ y : G, y * z * y⁻¹ = z * t)
    (haut : Nat.card (MulAut ↥E) = 1920) (hT : Nat.card ↥T = 512) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) {x : G} (hxQ : x ∈ Q) (hxT : x ∉ T)
    (hxN : x ∈ normalizer (T : Set G)) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) :
    (∃ k : ℕ, 2 ≤ k ∧ Nonempty (S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup n) := by
  obtain ⟨R, hR2, hRC, hR8⟩ := h.exists_two_subgroup_cent hzt haut hT hQ hTQ hxQ hxT hxN
  have hle := card_le_of_maximal E hS2 hSC hSmax hR2 hRC
  rcases h.sylow_centralizer_shape hzt hS2 hSC hSmax hzS with hS | hS | hS
  · exfalso
    have := h.card_zpowers_sup
    rw [← hS] at this
    omega
  · exact Or.inl hS
  · exact Or.inr hS

include h in
theorem centralizer_oddCore_dihedral {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    {k : ℕ} (hk : 2 ≤ k) (hS : Nonempty (S ≃* DihedralGroup (2 ^ k))) :
    ∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
      N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
      (N : Set (centralizer (E : Set G))) *
        (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) = Set.univ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : t ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    exact h.t_comm_E he
  let Ssyl := sylowCentOfMax E hS2 hSC hSmax
  have hS' : Nonempty (DihedralGroup (2 ^ (k + 1 - 1)) ≃*
      (Ssyl : Subgroup (centralizer (E : Set G)))) := by
    obtain ⟨e⟩ := hS
    rw [Nat.add_sub_cancel]
    exact ⟨e.symm.trans (subgroupOfEquivOfLe hSC).symm⟩
  have ht : ∃ t' ∈ Subgroup.center (centralizer (E : Set G)), orderOf t' = 2 := by
    refine ⟨⟨t, hC⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 g.2 t h.econfig.t_mem).symm
    · rw [Subgroup.orderOf_mk, h.t_order]
  obtain ⟨N, hN, -, -, -, hmem, hprod, hinf, -⟩ :=
    CFSG.Semidihedral.Principal.dihedral_central_involution_normal_odd_complement Ssyl
      (n := k + 1) (by omega) hS' ht
  exact ⟨N, hN, hmem, hinf, hprod⟩

end OuterE

end CFSG.EvenSporadicStandard.Fin76b
