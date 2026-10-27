module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open

section Rank

variable {M : Type*} [Group M] [Finite M] {p : ℕ}

theorem pRank_le_card (hp : p.Prime) (H : Subgroup M) : CFSG.Open.pRank p H ≤ Nat.card M :=
  CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt H

theorem le_pRank_of (hp : p.Prime) {H E : Subgroup M} {k : ℕ} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk

theorem exists_isElemAbelian_card_pRank (hp : p.Prime) (H : Subgroup M) :
    ∃ E : Subgroup M, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ CFSG.Open.pRank p H :=
  CFSG.SectionRank.exists_pRank hp.one_lt H

end Rank

section Frattini

variable {M : Type*} [Group M] [Finite M] {p : ℕ}

theorem isElemAbelian_map_hom {K N : Type*} [Group K] [Group N] {E : Subgroup K}
    (f : K →* N) (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem exists_sylow_le_of_sup_eq_top (hp : p.Prime) {H N : Subgroup M} [N.Normal]
    (hHN : H ⊔ N = ⊤) (hcop : Nat.Coprime p (Nat.card N)) :
    ∃ P : Sylow p M, (P : Subgroup M) ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : N.index ∣ Nat.card H := by
    have h := (Subgroup.relIndex_sup_right (H := H) (K := N)).symm
    rw [hHN, Subgroup.relIndex_top_right] at h
    rw [← h]
    exact Subgroup.index_dvd_card (N.subgroupOf H)
  have h2 : Nat.card N * N.index = Nat.card M := Subgroup.card_mul_index N
  have h3 : p ^ (Nat.card M).factorization p ∣ N.index := by
    have hd : p ^ (Nat.card M).factorization p ∣ Nat.card N * N.index :=
      h2 ▸ Nat.ordProj_dvd _ p
    exact (Nat.Coprime.pow_left _ hcop).dvd_of_dvd_mul_left hd
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) p (h3.trans h1)
  have hKM : Nat.card (K.map H.subtype) = p ^ (Nat.card M).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hK
  exact ⟨Sylow.ofCard (K.map H.subtype) hKM, Subgroup.map_subtype_le K⟩

theorem exists_conj_mem_sylow [Fact p.Prime] {E : Subgroup M} (hE : IsPGroup p E) (P : Sylow p M) :
    ∃ g : M, ∀ x ∈ E, g⁻¹ * x * g ∈ P := by
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Set M) := hQ hx
  rw [← hg, Sylow.coe_smul] at hxQ
  obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.1 hxQ
  have : x = g * y * g⁻¹ := by
    rw [← hyx]
    simp [MulAut.smul_def, MulAut.conj_apply]
  rw [this]
  simpa [mul_assoc] using hy

end Frattini

theorem odd_card_gLAPPrimeCore_of_lt {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hlt : GLATwoLocalRank p M < CFSG.Open.pRank p (⊤ : Subgroup M)) :
    Odd (Nat.card (GLAPPrimeCore p M)) := by
  classical
  by_contra hodd
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p M)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp M
  have h2 : 2 ∣ Nat.card (GLAPPrimeCore p M) := by
    rcases Nat.even_or_odd (Nat.card (GLAPPrimeCore p M)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNnormal : (GLAPPrimeCore p M).Normal := GLAPPrimeCore.normal p M
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(GLAPPrimeCore p M)) := inferInstance
  set T0 : Subgroup M := (T : Subgroup (GLAPPrimeCore p M)).map (GLAPPrimeCore p M).subtype
    with hT0
  have hT0ne : T0 ≠ ⊥ := by
    intro hbot
    have h3 : (T : Subgroup (GLAPPrimeCore p M)) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (GLAPPrimeCore p M).subtype_injective).1 hbot
    have h4 : 2 ∣ Nat.card (T : Subgroup (GLAPPrimeCore p M)) := Sylow.dvd_card_of_dvd_card T h2
    rw [h3] at h4
    simp at h4
  have hT02 : IsPGroup 2 T0 := by
    refine IsPGroup.of_card (n := (Nat.card (GLAPPrimeCore p M)).factorization 2) ?_
    rw [hT0, Subgroup.card_map_of_injective (GLAPPrimeCore p M).subtype_injective]
    exact T.card_eq_multiplicity
  have hH2 : IsTwoLocal (Subgroup.normalizer (T0 : Set M)) := ⟨T0, hT0ne, hT02, rfl⟩
  have hfrat : Subgroup.normalizer (T0 : Set M) ⊔ GLAPPrimeCore p M = ⊤ :=
    Sylow.normalizer_sup_eq_top T
  obtain ⟨P0, hP0⟩ := exists_sylow_le_of_sup_eq_top hp hfrat hcop
  obtain ⟨E, -, hE, hEk⟩ := exists_isElemAbelian_card_pRank hp (⊤ : Subgroup M)
  have hEp : IsPGroup p E := IsPGroup.of_card hEk
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow hEp P0
  set E' : Subgroup M := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'el : IsElemAbelian p E' := isElemAbelian_map_hom _ hE
  have hE'card : Nat.card E' = p ^ CFSG.Open.pRank p (⊤ : Subgroup M) := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hEk
  have hE'le : E' ≤ Subgroup.normalizer (T0 : Set M) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have h7 : g⁻¹ * x * g ∈ (P0 : Subgroup M) := hg x hx
    have h8 : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
      simp
    rw [h8]
    exact hP0 h7
  have h5 : CFSG.Open.pRank p (⊤ : Subgroup M) ≤
      CFSG.Open.pRank p (Subgroup.normalizer (T0 : Set M)) :=
    le_pRank_of hp hE'le hE'el hE'card
  have h6 : CFSG.Open.pRank p (Subgroup.normalizer (T0 : Set M)) ≤ GLATwoLocalRank p M := by
    refine le_csSup ⟨Nat.card M, ?_⟩ ⟨_, hH2, rfl⟩
    rintro k ⟨H', -, rfl⟩
    exact pRank_le_card hp H'
  omega

end CFSG.HardMathSupport.Solomon.Proving
