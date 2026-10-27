module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.RankTwoShapes

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem stronglyClosed_of_alperin (S : Sylow p G) {B : Subgroup G} (hB : B ≤ (S : Subgroup G))
    (h : ∀ Q : Subgroup G, IsAlperinSubgroup p (S : Subgroup G) Q →
      ∀ n ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ B ⊓ Q, n⁻¹ * x * n ∈ B) :
    fusionStronglyClosed (B : Set G) S := by
  intro x hx g hg
  have hP : Subgroup.zpowers x ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 (hB hx)
  have hPg : (Subgroup.zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg)
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  rw [← hcg x (Subgroup.mem_zpowers x)]
  clear hcg
  induction hc with
  | one => simpa using hx
  | @step c n Q _ hQ hPQ hn ih =>
    have hxQ : c⁻¹ * x * c ∈ Q := by
      have := hPQ (Subgroup.mem_map_of_mem (MulAut.conj c⁻¹).toMonoidHom (Subgroup.mem_zpowers x))
      simpa using this
    have e : (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
    rw [e]
    exact h Q hQ n hn _ ⟨ih, hxQ⟩

omit [Finite G] [Fact p.Prime] in
theorem mem_of_isAlperinSubgroup {S Q : Subgroup G} (hQ : IsAlperinSubgroup p S Q) {z : G}
    (hzS : z ∈ S) (hz : ∀ s ∈ S, s * z = z * s) : z ∈ Q :=
  hQ.2.2.1 ⟨Subgroup.mem_centralizer_iff.mpr fun q hq => hz q (hQ.1 hq), hzS⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
