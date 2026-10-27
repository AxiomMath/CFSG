module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open

variable {K : Type} [Group K]

@[expose] def omega5 (S : Subgroup K) : Subgroup K :=
  Subgroup.closure {g : K | g ∈ S ∧ g ^ 5 = 1}

theorem isMulCommutative_of_exponent_five {S : Subgroup K} (hexp : ∀ s ∈ S, s ^ 5 = 1)
    (h : IsMulCommutative (omega5 S)) : IsMulCommutative S := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : (a : K) ∈ omega5 S := Subgroup.subset_closure ⟨a.2, hexp a a.2⟩
  have hb : (b : K) ∈ omega5 S := Subgroup.subset_closure ⟨b.2, hexp b b.2⟩
  have := congrArg Subtype.val (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact Subtype.ext this

private theorem mem_smul_sylow_iff {p : ℕ} [Fact p.Prime] [Finite K] (Q S : Sylow p K) (c : K)
    (hc : c • Q = S) {x : K} (hx : x ∈ (Q : Subgroup K)) : c * x * c⁻¹ ∈ (S : Subgroup K) := by
  rw [← hc]
  show c * x * c⁻¹ ∈ ((c • Q : Sylow p K) : Subgroup K)
  rw [Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (Q : Subgroup K) hx

variable [Finite K]

theorem isMulCommutative_sylow_of_five_le_pRank (h : 5 ≤ pRank 5 (⊤ : Subgroup K))
    (S : Sylow 5 K) (hS : Nat.card S = 5 ^ 5) : IsMulCommutative (S : Subgroup K) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) (⊤ : Subgroup K)
  have hEp : IsPGroup 5 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
  have hQc : Nat.card Q = 5 ^ 5 := by
    rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity S]
    exact hS
  have hle : 5 ^ 5 ≤ Nat.card E := by
    rw [hEc]
    exact Nat.pow_le_pow_right (by norm_num) h
  have hEQ : E = (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hQc]; exact hle)
  have hQcomm : IsMulCommutative (Q : Subgroup K) := hEQ ▸ hE.1
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K Q S
  have hSQ : (S : Subgroup K) = (Q : Subgroup K).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  rw [hSQ]
  exact (CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.isMulCommutative_map_iff_of_injective
    _ (MulAut.conj c).injective _).2 hQcomm

theorem not_isMulCommutative_omega5 {E : Subgroup K} {g : K} (hE : IsElemAbelian 5 E)
    (hg : g ^ 5 = 1) (hnorm : ∀ x ∈ E, g * x * g⁻¹ ∈ E) (hnc : ∃ x ∈ E, g * x ≠ x * g)
    (S : Sylow 5 K) : ¬ IsMulCommutative (omega5 (S : Subgroup K)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro hcomm
  obtain ⟨x, hxE, hx⟩ := hnc
  have hEp : IsPGroup 5 E := fun y => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 y y.2⟩
  have hgp : IsPGroup 5 (Subgroup.zpowers g) := by
    have hcard : Nat.card (Subgroup.zpowers g) ∣ 5 ^ 1 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (by simpa using hg)
    exact IsPGroup.of_card_dvd_pow hcard
  have hpow : ∀ k : ℕ, ∀ y ∈ E, g ^ k * y * (g ^ k)⁻¹ ∈ E := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have h1 := ih _ (hnorm y hy)
      have e : g ^ (k + 1) * y * (g ^ (k + 1))⁻¹ = g ^ k * (g * y * g⁻¹) * (g ^ k)⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e]
      exact h1
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (E : Set K) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnorm y hy, fun hy => ?_⟩
    have h4 : g ^ 4 = g⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hg
    have h1 := hpow 4 _ hy
    rw [h4] at h1
    have e : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y := by group
    rwa [e] at h1
  have hP : IsPGroup 5 (Subgroup.zpowers g ⊔ E : Subgroup K) := hgp.to_sup_of_normal_right' hEp hle
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K Q S
  have hgQ : g ∈ (Q : Subgroup K) := hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers g))
  have hxQ : x ∈ (Q : Subgroup K) := hQ (Subgroup.mem_sup_right hxE)
  have h1 : c * g * c⁻¹ ∈ (S : Subgroup K) := mem_smul_sylow_iff Q S c hc hgQ
  have h2 : c * x * c⁻¹ ∈ (S : Subgroup K) := mem_smul_sylow_iff Q S c hc hxQ
  have h1' : c * g * c⁻¹ ∈ omega5 (S : Subgroup K) :=
    Subgroup.subset_closure ⟨h1, by rw [conj_pow, hg]; group⟩
  have h2' : c * x * c⁻¹ ∈ omega5 (S : Subgroup K) :=
    Subgroup.subset_closure ⟨h2, by rw [conj_pow, hE.2 x hxE]; group⟩
  have := congrArg Subtype.val (hcomm.is_comm.comm ⟨_, h1'⟩ ⟨_, h2'⟩)
  apply hx
  have h3 : c * g * c⁻¹ * (c * x * c⁻¹) = c * x * c⁻¹ * (c * g * c⁻¹) := this
  have h4 : c * (g * x) * c⁻¹ = c * (x * g) * c⁻¹ := by
    calc c * (g * x) * c⁻¹ = c * g * c⁻¹ * (c * x * c⁻¹) := by group
      _ = c * x * c⁻¹ * (c * g * c⁻¹) := h3
      _ = c * (x * g) * c⁻¹ := by group
  simpa using h4

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
