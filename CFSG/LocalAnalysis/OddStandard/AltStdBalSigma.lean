module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalJ
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalSylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.OddStandard.Solomon75

section Shape

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem shape_one_decomp (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    ∃ l ∈ L, c = l ∨ c = l * z := by
  obtain ⟨l, hl, q, hq, rfl⟩ := (mem_sup_iff_mul d).1 (hE hc)
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
  · exact ⟨l, hl, Or.inl (mul_one l)⟩
  · exact ⟨l, hl, Or.inr rfl⟩

theorem mem_of_maximal {R : Subgroup G} (d : Cyc L Q z) (hRC : R ≤ centralizer ({z} : Set G))
    (hR : IsPGroup 2 R)
    (hRmax : ∀ R' : Subgroup G, R' ≤ centralizer ({z} : Set G) → IsPGroup 2 R' → R ≤ R' →
      R' = R) : z ∈ R := by
  have hz : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.order, pow_one])
  have hnorm : R ≤ normalizer (Subgroup.zpowers z : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro r hr
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have := mem_centralizer_singleton_iff.1 (hRC hr)
    exact (Commute.zpow_left (Commute.symm this) j).eq
  have hp := IsPGroup.to_sup_of_normal_right' hR hz hnorm
  have hle : R ⊔ Subgroup.zpowers z ≤ centralizer ({z} : Set G) :=
    sup_le hRC (Subgroup.zpowers_le.2 (by
      rw [mem_centralizer_singleton_iff]))
  have := hRmax _ hle hp le_sup_left
  rw [← this]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem z_not_mem_L (h : Setting G L n) (d : Cyc L Q z) : z ∉ L := by
  intro hzL
  obtain ⟨e⟩ := h.iso
  have h1 := eq_one_of_mem_of_mem_centralizer e (by have := h.hn; omega) hzL (d.le d.mem)
  have := d.order
  rw [h1, orderOf_one] at this
  omega

theorem not_le_centralizer_of_sylow (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (S : Sylow 2 G) :
    ¬ (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
  intro hSC
  have := h.std.simple
  have hzS : z ∈ (S : Subgroup G) :=
    mem_of_maximal d hSC S.isPGroup' (fun R' _ hp hSR' => S.3 hp hSR')
  have hzL := z_not_mem_L h d
  have hrel : (S ⊓ L : Subgroup G).relIndex S = 2 := by
    have hdvd : (S ⊓ L : Subgroup G).relIndex S ∣ 2 := by
      rw [relIndex_dvd_two_iff]
      refine ⟨z, hzS, fun b hb => ?_⟩
      obtain ⟨l, hl, hbl⟩ := shape_one_decomp d hQ2 hE (hSC hb)
      rcases hbl with rfl | rfl
      · exact Or.inr (Subgroup.mem_inf.2 ⟨hb, hl⟩)
      · refine Or.inl (Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ hb hzS, ?_⟩)
        rw [mul_assoc, d.mul_self, mul_one]
        exact hl
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exfalso
      exact hzL (Subgroup.mem_inf.1 ((relIndex_eq_one.1 h1) hzS)).2
    · exact h2
  obtain ⟨g, hg⟩ := exists_conj_mem_of_thompson h.std.simple h.std.nonab S.isPGroup'
    S.not_dvd_index inf_le_left hrel hzS (fun hzU => hzL (Subgroup.mem_inf.1 hzU).2) d.order
  have := not_conj_mem_L h d hQ2 g⁻¹
  rw [inv_inv] at this
  exact this (Subgroup.mem_inf.1 hg).2

omit [Finite G] in
theorem exists_maximal_two_subgroup (c : Subgroup G) :
    ∃ R : Subgroup G, R ≤ c ∧ IsPGroup 2 R ∧
      ∀ R' : Subgroup G, R' ≤ c → IsPGroup 2 R' → R ≤ R' → R' = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 c) := inferInstance
  refine ⟨(S : Subgroup c).map c.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_⟩
  intro R' hR'c hR' hSR'
  have hp : IsPGroup 2 (R'.subgroupOf c) := hR'.of_equiv (subgroupOfEquivOfLe hR'c).symm
  have hle : (S : Subgroup c) ≤ R'.subgroupOf c := fun s hs => hSR' ⟨s, hs, rfl⟩
  have h1 := S.3 hp hle
  rw [← Subgroup.map_subgroupOf_eq_of_le hR'c, h1]

end Shape

end CFSG.OddStandard.AltStdBal
