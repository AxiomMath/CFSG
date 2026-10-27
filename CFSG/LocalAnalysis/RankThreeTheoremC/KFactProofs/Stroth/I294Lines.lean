module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Defs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

theorem exists_pElement_of_not_isSylowOf {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {D : Subgroup X} {x : X} (hDe : CFSG.Open.IsElemAbelian p D)
    (hS : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X))) (hx : x ∈ D)
    (hns : ¬ CFSG.ABGLocalTools.IsSylowOf p D (centralizer ({x} : Set X))) :
    ∃ q ∈ normalizer (D : Set X), q * x = x * q ∧ q ∉ centralizer (D : Set X) ∧
      ∃ e : ℕ, q ^ p ^ e = 1 := by
  have hp : p.Prime := Fact.out
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  have hDC : D ≤ C := by
    intro d hd
    rw [hC, mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hDe.comm hx hd
  have hDcent : D ≤ centralizer (D : Set X) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro g hg
    exact hDe.comm hg hd
  obtain ⟨Q, hDQ⟩ := (hDe.isPGroup.comap_subtype (K := C)).exists_le_sylow
  set P : Subgroup X := (Q : Subgroup C).map C.subtype with hP
  have hPS : CFSG.ABGLocalTools.IsSylowOf p P C := ⟨Q, rfl⟩
  have hPC : P ≤ C := hPS.le
  have hPp : IsPGroup p P := hPS.isPGroup
  have hDP : D ≤ P := fun d hd =>
    ⟨⟨d, hDC hd⟩, hDQ (show (⟨d, hDC hd⟩ : C) ∈ D.comap C.subtype from hd), rfl⟩
  have hDne : D ≠ P := fun h => hns (by rw [h]; exact hPS)
  haveI : Group.IsNilpotent P := hPp.isNilpotent
  have hlt : D.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [subgroupOf_eq_top] at h
    exact hDne (le_antisymm hDP h)
  obtain ⟨g, hg, hgD⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (D.subgroupOf P) hlt)
  rw [← subgroupOf_normalizer_eq hDP] at hg
  have hgD' : (g : X) ∉ D := hgD
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · exact ((mem_centralizer_iff.1 (hPC g.2)) x (Set.mem_singleton x)).symm
  · intro hgC
    have hR : P ⊓ centralizer (D : Set X) = D :=
      hS.eq_of_le (le_inf hDP hDcent) inf_le_right hPp.to_inf_left
    exact hgD' (hR ▸ (⟨g.2, hgC⟩ : (g : X) ∈ P ⊓ centralizer (D : Set X)))
  · obtain ⟨e, he⟩ := hPp g
    exact ⟨e, by simpa using congrArg (fun a : P => (a : X)) he⟩

theorem linesTrans_of_forall_not_isSylowOf {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {D : Subgroup X} (hDe : CFSG.Open.IsElemAbelian p D)
    (hD : Nat.card D = p ^ 2)
    (hS : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X)))
    (hall : ∀ x ∈ D, x ≠ 1 →
      ¬ CFSG.ABGLocalTools.IsSylowOf p D (centralizer ({x} : Set X)))
    {z : X} (hz : z ∈ D) (hz1 : z ≠ 1) : LinesTrans D z := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro y hy hy1
  by_cases hyz : y ∈ zpowers z
  · refine ⟨1, one_mem _, ?_⟩
    rw [MonoidHom.map_zpowers, zpowers_eq_of_mem_zpowers_of_pow_eq_one (hDe.2 z hz) hz1 hyz hy1]
    simp
  ·
    have hxD : y * z ∈ D := mul_mem hy hz
    have hx1 : y * z ≠ 1 := fun h => hyz (by
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem (mem_zpowers z))
    have hzx : z ∉ zpowers (y * z) := fun h => hyz (by
      have h1 := zpowers_eq_of_mem_zpowers_of_pow_eq_one (hDe.2 _ hxD) hx1 h hz1
      have h2 : y * z ∈ zpowers z := h1 ▸ mem_zpowers (y * z)
      simpa using mul_mem h2 (inv_mem (mem_zpowers z)))
    have hyx : y ∉ zpowers (y * z) := fun h => hyz (by
      have h1 := zpowers_eq_of_mem_zpowers_of_pow_eq_one (hDe.2 _ hxD) hx1 h hy1
      have h2 : y * z ∈ zpowers y := h1 ▸ mem_zpowers (y * z)
      have h3 : z ∈ zpowers y := by simpa using mul_mem (inv_mem (mem_zpowers y)) h2
      have h4 := zpowers_eq_of_mem_zpowers_of_pow_eq_one (hDe.2 _ hy) hy1 h3 hz1
      exact h4 ▸ mem_zpowers y)
    obtain ⟨q, hqN, hqx, hqD, e, hqe⟩ :=
      exists_pElement_of_not_isSylowOf hDe hS hxD (hall _ hxD hx1)
    obtain ⟨k, hk⟩ := exists_pow_conj_zpowers_eq hDe hD hxD hx1 ⟨e, hqe⟩ hqN hqx hqD hz hzx hy hyx
    exact ⟨q ^ k, pow_mem hqN k, by rw [MonoidHom.map_zpowers]; exact hk.symm⟩

theorem exists_sylowLine_of_not_linesTrans {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {D : Subgroup X} (hDe : CFSG.Open.IsElemAbelian p D)
    (hD : Nat.card D = p ^ 2)
    (hS : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X)))
    {z : X} (hz : z ∈ D) (hz1 : z ≠ 1) (hnt : ¬ LinesTrans D z) :
    ∃ x ∈ D, x ≠ 1 ∧ CFSG.ABGLocalTools.IsSylowOf p D (centralizer ({x} : Set X)) := by
  by_contra hno
  push Not at hno
  exact hnt (linesTrans_of_forall_not_isSylowOf hp hDe hD hS hno hz hz1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
