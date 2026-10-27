module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem D2AlmostSimple.le_of_perfect (hSch : KFactCatalogSchreier)
    (h : D2AlmostSimple p X R A X₀ K) {Y : Subgroup X} (hY : ⁅Y, Y⁆ = Y) : Y ≤ K := by
  have : K.Normal := h.normal
  have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := h.component.2.2.2
  have hs : IsSimpleGroup K := ((QuotientGroup.quotientMulEquivOfEq h.center_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have htop : Subgroup.center K = ⊤ :=
      eq_top_iff.mpr fun a _ => Subgroup.mem_center_iff.mpr fun b => hcon b a
    rw [h.center_eq_bot] at htop
    exact bot_ne_top htop
  have := hSch K hs hnab h.catalog
  let ψ : X →* Outer K := (QuotientGroup.mk' (inner K)).comp (MulAut.conjNormal (H := K))
  have hYψ : Y.map ψ = ⊥ := by
    obtain ⟨n, hn⟩ := exists_iterCommutator_eq_bot (⊤ : Subgroup (Outer K))
    rw [eq_bot_iff, ← hn]
    exact le_iterCommutator_of_commutator_eq (by rw [← Subgroup.map_commutator, hY]) le_top n
  intro x hx
  have hψ : ψ x = 1 := (Subgroup.map_eq_bot_iff _).mp hYψ hx
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  have hcent : (c : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hc ⟨y, hy⟩)
    rw [MulAut.conjNormal_apply] at h1
    change (c : X) * y * (c : X)⁻¹ = x * y * x⁻¹ at h1
    calc y * ((c : X)⁻¹ * x) = (c : X)⁻¹ * ((c : X) * y * (c : X)⁻¹) * x := by group
      _ = (c : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (c : X)⁻¹ * x * y := by group
  rw [h.centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hcent ▸ c.2

theorem isSolvable_inf_of_subgroupOf {Y : Type*} [Group Y] {W K : Subgroup Y}
    (h : Group.IsSolvable (W.subgroupOf K)) : Group.IsSolvable (W ⊓ K : Subgroup Y) := by
  rw [← Subgroup.inf_subgroupOf_right] at h
  have e := Subgroup.subgroupOfEquivOfLe (inf_le_right : W ⊓ K ≤ K)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem D2AlmostSimple.perfect_eq_bot_of_isSolvable_inf (hSch : KFactCatalogSchreier)
    (h : D2AlmostSimple p X R A X₀ K) (hsolv : Group.IsSolvable (X₀ ⊓ K : Subgroup X))
    (Y : Subgroup X) (hYX₀ : Y ≤ X₀) (hY : ⁅Y, Y⁆ = Y) : Y = ⊥ := by
  obtain ⟨n, hn⟩ := exists_iterCommutator_eq_bot (X₀ ⊓ K)
  rw [eq_bot_iff, ← hn]
  exact le_iterCommutator_of_commutator_eq hY (le_inf hYX₀ (h.le_of_perfect hSch hY)) n

end CFSG.AGLEmbeddingD2
