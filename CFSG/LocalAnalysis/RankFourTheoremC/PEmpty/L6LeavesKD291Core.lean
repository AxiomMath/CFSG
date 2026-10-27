module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniComm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankFourTheoremC

theorem exists_B_of_cover {p : ℕ} [hpp : Fact p.Prime] (hp5 : 5 ≤ p)
    {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    {S₀ P G : Type} [Group S₀] [Group P] [Group G] (hS₀ : Group.IsPerfect S₀)
    (π : S₀ →* P) (c : G → (S₀ →* S₀)) (Φ : G →* MulAut P) (Z : Subgroup G)
    (hcentral : ∀ w ∈ Z, ∀ B : G, w * B = B * w)
    (hcomm : ∀ α β : MulAut P, α * β * α⁻¹ * β⁻¹ ∈ Φ.range)
    (hker : ∀ B : G, Φ B = 1 → B ∈ Z)
    (e : ↥L ⧸ center ↥L ≃* P) (φ : S₀ →* ↥L) (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s)
    (hc : ∀ B s, π (c B s) = Φ B (π s)) (hcZ : ∀ w ∈ Z, ∀ B : G, c (w * B) = c B)
    (htorus : ∀ B : G, B ^ p = 1 → ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* S₀,
      Function.Injective (π.comp f) ∧ ∀ a, c B (f a) = f a) :
    ∃ B : G, Φ B = l212in_descend e (odC L x) ∧ B ^ p ∈ Z ∧ ∀ w ∈ Z, w ^ p ≠ B ^ p := by
  haveI := hS₀
  have hp : p.Prime := hpp.out
  set ψ : Y →* MulAut P := (l212in_descend e).comp (odC L) with hψ
  haveI : Φ.range.Normal :=
    ⟨fun a ha g => by
      have h := hcomm g a
      have h2 : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
      rw [h2]
      exact mul_mem h ha⟩
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨B, hB⟩ : ψ x ∈ Φ.range :=
    I291LinUni.map_mem_of_pow_eq_one Φ.range hcomm hperf ψ hxp
  have hlift : ∀ s, odC L x (φ s) = φ (c B s) := by
    intro s
    refine l212in_alpha_phi e π φ hφπ (odC L x) (c B) (fun t => ?_) s
    rw [hc, hB]
    rfl
  have hBZ : B ^ p ∈ Z := by
    refine hker _ ?_
    rw [map_pow, hB, ← map_pow, hxp, map_one]
  have hnp : ∀ w ∈ Z, w ^ p ≠ B ^ p := by
    intro w hw hwp
    have hw' : w⁻¹ ∈ Z := Z.inv_mem hw
    have hBp : (w⁻¹ * B) ^ p = 1 := by
      have hc1 : Commute w⁻¹ B := hcentral w⁻¹ hw' B
      rw [hc1.mul_pow, inv_pow, hwp, inv_mul_cancel]
    obtain ⟨f, hfi, hfix⟩ := htorus (w⁻¹ * B) hBp
    rw [hcZ w⁻¹ hw' B] at hfix
    have hinj : Function.Injective (φ.comp f) := by
      intro a b hab
      apply hfi
      change π (f a) = π (f b)
      rw [← hφπ, ← hφπ]
      exact congrArg (fun l : ↥L => e (QuotientGroup.mk l)) hab
    have h3 := od_three_le_pRank_of_torus (L := L) (x := x) (φ.comp f) hinj (fun a => by
      change odC L x (φ (f a)) = φ (f a)
      rw [hlift, hfix])
    omega
  exact ⟨B, hB, hBZ, hnp⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
