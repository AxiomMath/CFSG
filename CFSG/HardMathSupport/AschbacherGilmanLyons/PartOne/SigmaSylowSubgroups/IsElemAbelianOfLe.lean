module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.HardMathSupport.AschbacherGilmanLyons.PartOne

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace SigmaSylowSubgroups

theorem gamma_conj {p k : ℕ} (hp : 1 < p) {E M : Subgroup G} {g : G} (hg : g ∈ M)
    (hE : rankThreeGamma k p E ≤ M) :
    rankThreeGamma k p (E.map (MulAut.conj g⁻¹).toMonoidHom) ≤ M := by
  have mem_map_conj_iff (g y : G) (Q : Subgroup G) :
      g * y * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom ↔ y ∈ Q := by
    rw [mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := by
        have h : g * z * g⁻¹ = g * y * g⁻¹ := hzy
        simpa using h
      exact this ▸ hz
    · intro hy; exact ⟨y, hy, rfl⟩
  have normalizer_conj {g x : G} {Q R : Subgroup G} (hQR : ∀ y, y ∈ Q ↔ g * y * g⁻¹ ∈ R)
      (hx : x ∈ normalizer (Q : Set G)) : g * x * g⁻¹ ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff] at hx ⊢
    intro h
    have h1 := hQR (g⁻¹ * h * g)
    have h2 := hx (g⁻¹ * h * g)
    have h3 := hQR (x * (g⁻¹ * h * g) * x⁻¹)
    have e1 : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    have e2 : g * (x * (g⁻¹ * h * g) * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * h * (g * x * g⁻¹)⁻¹ := by group
    rw [e1] at h1
    rw [e2] at h3
    rw [← h1, h2, h3]
  have pRank_le_map_conj {p : ℕ} (hp : 1 < p) (g : G) (Q : Subgroup G) :
      CFSG.Open.pRank p Q ≤ CFSG.Open.pRank p (Q.map (MulAut.conj g).toMonoidHom) :=
    CFSG.SectionRank.pRank_le_map hp _ (MulAut.conj g).injective Q
  refine sSup_le ?_
  rintro N ⟨R, hRE, hRk, rfl⟩
  set R' := R.map (MulAut.conj g).toMonoidHom with hR'
  have hR'E : R' ≤ E := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e, he, hey⟩ := hRE hy
    have : g * y * g⁻¹ = e := by
      have h : g⁻¹ * e * g⁻¹⁻¹ = y := hey
      rw [← h]; group
    show g * y * g⁻¹ ∈ E
    rw [this]; exact he
  have hr : k ≤ CFSG.Open.pRank p R' := hRk.trans (pRank_le_map_conj hp g R)
  have hle : normalizer (R' : Set G) ≤ rankThreeGamma k p E :=
    le_sSup ⟨R', hR'E, hr, rfl⟩
  intro x hx
  have h1 : g * x * g⁻¹ ∈ normalizer (R' : Set G) :=
    normalizer_conj (fun y => (mem_map_conj_iff g y R).symm) hx
  have h2 : g * x * g⁻¹ ∈ M := hE (hle h1)
  have h3 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [h3]
  exact M.mul_mem (M.mul_mem (M.inv_mem hg) h2) hg

end SigmaSylowSubgroups

end CFSG.HardMathSupport.AschbacherGilmanLyons.PartOne
