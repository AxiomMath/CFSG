module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure

public section

namespace CFSG.CGT.PushingUpLit.STT

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Asc76
  CFSG.ComponentClassification.Asc76X

theorem isSzOrU3_of_stated {G : Type} [Group G]
    (h : (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s)) : IsSzOrU3 G := by
  rcases h with ⟨s, -, -, hL⟩ | ⟨s, hs, hst⟩
  · have hS : CFSG.Blueprint.SuzukiModel G 2 s := by
      rcases hL with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact hS
    obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hS
    exact Or.inl ⟨a, ha, ⟨e.trans
      ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
        (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))⟩⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hst
    have hcard : Nat.card K = 2 ^ (2 * s) := by rw [hK, ← pow_mul, mul_comm]
    let e' : G ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ s)) := e
    exact Or.inr ⟨s, hs, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative s hs hcard)⟩⟩

section Borel

variable {G : Type*} [Group G] [Finite G]

theorem isSolvable_of_pGroup_sup_cyclic {Q D : Subgroup G} (hQ : IsPGroup 2 Q) (hD : IsCyclic D)
    (hsup : Q ⊔ D = Subgroup.normalizer (Q : Set G)) : Group.IsSolvable ↥(Q ⊔ D) := by
  set M : Subgroup G := Q ⊔ D with hM
  have hQM : Q ≤ M := le_sup_left
  have hDM : D ≤ M := le_sup_right
  have hnorm : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).2 hsup.le
  have hQp : IsPGroup 2 (Q.subgroupOf M) := hQ.comap_of_injective M.subtype M.subtype_injective
  have : Group.IsSolvable ↥(Q.subgroupOf M) := by
    have := hQp.isNilpotent
    infer_instance
  have hcyc : IsCyclic (↥M ⧸ Q.subgroupOf M) := by
    let f : D →* ↥M ⧸ Q.subgroupOf M :=
      (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hDM)
    have hf : Function.Surjective f := by
      have htop : Q.subgroupOf M ⊔ D.subgroupOf M = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQM hDM, ← hM, Subgroup.subgroupOf_self]
      intro x
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
      have hm : m ∈ Q.subgroupOf M ⊔ D.subgroupOf M := by rw [htop]; exact Subgroup.mem_top m
      obtain ⟨y, hy, d, hd, hyd⟩ := Subgroup.mem_sup_of_normal_left.1 hm
      refine ⟨⟨(d : G), hd⟩, ?_⟩
      rw [← hyd]
      change QuotientGroup.mk (Subgroup.inclusion hDM ⟨(d : G), hd⟩) = QuotientGroup.mk (y * d)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul]
      rfl
    exact isCyclic_of_surjective f hf
  have : Group.IsSolvable (↥M ⧸ Q.subgroupOf M) := inferInstance
  exact Group.isSolvable_of_ker_le_range (Q.subgroupOf M).subtype
    (QuotientGroup.mk' (Q.subgroupOf M)) (by simp)

theorem isSolvable_centralizer_of_borel {q k : ℕ} (h : fusionBenderBorel G q k) {z : G}
    (hz : orderOf z = 2) : Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) := by
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hzp
  have hzQ : z ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers z)
  obtain ⟨⟨-, -, hodd⟩, ⟨D, hDc, -, -, hsup⟩, -, -, -⟩ := h Q
  have hzM : z ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := Subgroup.le_normalizer hzQ
  have hCM : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro g hg
    by_contra hgM
    have h1 := hodd g hgM
    have hg' : z * g = g * z := Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)
    have hzi : z ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
        (Subgroup.normalizer ((Q : Subgroup G) : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
      refine ⟨hzM, z, hzM, ?_⟩
      change g⁻¹ * z * g⁻¹⁻¹ = z
      rw [inv_inv, mul_assoc, hg', ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 := Subgroup.orderOf_dvd_natCard _ hzi
    rw [hz] at h2
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  have hsolv : Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [← hsup]
    exact isSolvable_of_pGroup_sup_cyclic Q.isPGroup' hDc hsup
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCM)

theorem exists_mem_orderOf_eq_two_of_pGroup {R : Subgroup G} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ∃ r ∈ R, orderOf r = 2 := by
  have hdvd : 2 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hR1
    · rw [hn]
      exact dvd_pow_self 2 n.succ_ne_zero
  obtain ⟨⟨r, hrR⟩, hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hdvd
  exact ⟨r, hrR, by rwa [Subgroup.orderOf_mk] at hr⟩

theorem isSolvable_centralizer_of_borel_subgroup {q k : ℕ} (h : fusionBenderBorel G q k)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    Group.IsSolvable ↥(Subgroup.centralizer (R : Set G)) := by
  obtain ⟨r, hrR, hr⟩ := exists_mem_orderOf_eq_two_of_pGroup hR hR1
  have hs := isSolvable_centralizer_of_borel h hr
  have hle : Subgroup.centralizer (R : Set G) ≤ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.centralizer_le (by simpa using hrR)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end Borel

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_centralizer_of_stated_bender
    (h : (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s))
    {R : Subgroup G} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    Group.IsSolvable ↥(Subgroup.centralizer (R : Set G)) := by
  obtain ⟨q, k, -, hB⟩ := exists_fusionBenderBorel_of_isSzOrU3 (isSzOrU3_of_stated h)
  exact isSolvable_centralizer_of_borel_subgroup hB hR hR1

omit [Finite G] in
theorem not_forall_comm_of_borel {q k : ℕ} (h : fusionBenderBorel G q k) :
    ¬ ∀ a b : G, a * b = b * a := by
  intro hcomm
  obtain ⟨Q⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hne : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≠ ⊤ := (h Q).1.1
  apply hne
  rw [Subgroup.normalizer_eq_top_iff]
  exact ⟨fun x hx y => by rwa [hcomm y x, mul_assoc, mul_inv_cancel, mul_one]⟩

theorem not_forall_comm_of_stated_bender
    (h : (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s)) :
    ¬ ∀ a b : G, a * b = b * a := by
  obtain ⟨q, k, -, hB⟩ := exists_fusionBenderBorel_of_isSzOrU3 (isSzOrU3_of_stated h)
  exact not_forall_comm_of_borel hB

end CFSG.CGT.PushingUpLit.STT
