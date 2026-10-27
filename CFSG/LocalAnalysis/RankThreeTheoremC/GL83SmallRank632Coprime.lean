module

public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedSylow
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.DisconnectedInvolutionGraph.Helpers
open scoped Pointwise

private theorem mem_centralizer_of_mem_fixedPoints {M : Type*} [Group M] {D A : Subgroup M}
    [D.Normal] {d : ↥D} (hd : d ∈ FixedPoints.subgroup ↥A ↥D) :
    (d : M) ∈ centralizer (A : Set M) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have := congrArg Subtype.val ((FixedPoints.mem_subgroup _ _ _).mp hd ⟨a, ha⟩)
  change a * (d : M) * a⁻¹ = d at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

private theorem mem_fixedPoints_of_mem_centralizer {M : Type*} [Group M] {D A : Subgroup M}
    [D.Normal] {d : ↥D} (hd : (d : M) ∈ centralizer (A : Set M)) :
    d ∈ FixedPoints.subgroup ↥A ↥D := by
  rw [FixedPoints.mem_subgroup]
  intro a
  apply Subtype.ext
  change (a : M) * (d : M) * (a : M)⁻¹ = d
  rw [mul_inv_eq_iff_eq_mul]
  exact Subgroup.mem_centralizer_iff.mp hd a a.2

private theorem exists_fixed_lift_of_mem
    {M : Type*} [Group M] [Finite M] {D R A : Subgroup M} [D.Normal] [R.Normal]
    (hD3 : ¬ 3 ∣ Nat.card D) (hA : IsPGroup 3 A) {Q : Subgroup (M ⧸ R)}
    (hQD : Q ≤ D.map (QuotientGroup.mk' R))
    (hQA : ∀ a ∈ A, ∀ q ∈ Q, QuotientGroup.mk' R a * q = q * QuotientGroup.mk' R a)
    {q : M ⧸ R} (hq : q ∈ Q) :
    ∃ d ∈ D, d ∈ centralizer (A : Set M) ∧ QuotientGroup.mk' R d = q := by
  let act : MulDistribMulAction ↥A (M ⧸ R) :=
    MulDistribMulAction.compHom (M ⧸ R)
      (MulAut.conj.comp ((QuotientGroup.mk' R).comp A.subtype))
  let ψ : ↥D →* M ⧸ R := (QuotientGroup.mk' R).comp D.subtype
  obtain ⟨d, hdq, hdfix⟩ := coprime_pgroup_fixed_lift (G := ↥D) (K := M ⧸ R) (A := ↥A) 3 hA ψ
    (fun a d => by
      change QuotientGroup.mk' R ((a : M) * (d : M) * (a : M)⁻¹) =
        QuotientGroup.mk' R (a : M) * QuotientGroup.mk' R (d : M) * (QuotientGroup.mk' R (a : M))⁻¹
      simp)
    (fun h => hD3 (h.trans (Subgroup.card_subgroup_dvd_card _))) q
    (by
      obtain ⟨d, hd, hdq⟩ := Subgroup.mem_map.mp (hQD hq)
      exact ⟨⟨d, hd⟩, hdq⟩)
    (fun a => by
      change QuotientGroup.mk' R (a : M) * q * (QuotientGroup.mk' R (a : M))⁻¹ = q
      rw [hQA a a.2 q hq, mul_inv_cancel_right])
  exact ⟨d, d.2, mem_centralizer_of_mem_fixedPoints ((FixedPoints.mem_subgroup _ _ _).mpr hdfix),
    hdq⟩

private theorem exists_conj_mem_of_le_inf_centralizer
    {M : Type*} [Group M] [Finite M] {D A T : Subgroup M} [D.Normal]
    (hD3 : ¬ 3 ∣ Nat.card D) (hA : IsPGroup 3 A) (hT2 : IsPGroup 2 T)
    (hTsyl : ¬ 2 ∣ (T.subgroupOf D).index) (hAT : A ≤ normalizer (T : Set M))
    {X : Subgroup M} (hX2 : IsPGroup 2 X) (hXD : X ≤ D) (hXA : X ≤ centralizer (A : Set M)) :
    ∃ g ∈ centralizer (A : Set M), ∀ x ∈ X, g * x * g⁻¹ ∈ T := by
  let T' : Sylow 2 ↥D := (hT2.comap_subtype (K := D)).toSylow hTsyl
  have hT'inv : InvariantSubgroup (A := ↥A) (T' : Subgroup ↥D) := fun a x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAT a.2) x).mp hx
  obtain ⟨F, hF⟩ := coprime_pgroup_fixed_sylow 3 2 hA hD3 T' hT'inv
  let Fx : Subgroup ↥D := FixedPoints.subgroup ↥A ↥D
  let X' : Subgroup ↥Fx := X.comap (D.subtype.comp Fx.subtype)
  have hX'2 : IsPGroup 2 X' :=
    hX2.comap_of_injective _ (D.subtype_injective.comp Fx.subtype_injective)
  obtain ⟨S, hXS⟩ := hX'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Fx S F
  refine ⟨((g : ↥D) : M), mem_centralizer_of_mem_fixedPoints g.2, fun x hx => ?_⟩
  let xF : ↥Fx := ⟨⟨x, hXD hx⟩, mem_fixedPoints_of_mem_centralizer (hXA hx)⟩
  have hxS : xF ∈ (S : Subgroup ↥Fx) := hXS hx
  have h1 : (MulAut.conj g) • xF ∈ (MulAut.conj g) • (S : Subgroup ↥Fx) :=
    Subgroup.smul_mem_pointwise_smul xF _ _ hxS
  rw [← Sylow.coe_subgroup_smul, hg, hF] at h1
  exact h1

private theorem exists_pSubgroup_map_eq {G N : Type*} [Group G] [Finite G] [Group N] {p : ℕ}
    [Fact p.Prime] (f : G →* N) {W : Subgroup G} {Q : Subgroup N} (hQ : IsPGroup p Q)
    (hWQ : W.map f = Q) :
    ∃ X : Subgroup G, X ≤ W ∧ IsPGroup p X ∧ X.map f = Q := by
  let g : ↥W →* ↥Q :=
    (f.comp W.subtype).codRestrict Q (fun w => hWQ ▸ Subgroup.mem_map_of_mem f w.2)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp (hWQ ▸ hy)
    exact ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := ↥W)
  have hS : ((S.mapSurjective hg : Sylow p ↥Q) : Subgroup ↥Q) = ⊤ :=
    ((S.mapSurjective hg).is_maximal' (hQ.of_equiv Subgroup.topEquiv.symm) le_top).symm
  refine ⟨(S : Subgroup ↥W).map W.subtype, Subgroup.map_subtype_le _,
    S.isPGroup'.map W.subtype, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact hWQ ▸ Subgroup.mem_map_of_mem f s.2
  · intro hy
    have hy' : (⟨y, hy⟩ : ↥Q) ∈ ((S.mapSurjective hg : Sylow p ↥Q) : Subgroup ↥Q) := by
      rw [hS]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hy'
    obtain ⟨s, hs, hsy⟩ := hy'
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsy⟩

set_option linter.unusedVariables false in
theorem exists_section_of_two_subgroup_centralizer {M : Type*} [Group M] [Finite M]
    {D R A T : Subgroup M} [D.Normal] [R.Normal] (hRD : R ≤ D) (hD3 : ¬ 3 ∣ Nat.card D)
    (hA : IsPGroup 3 A) (hT : T ≤ D) (hT2 : IsPGroup 2 T)
    (hTsyl : ¬ 2 ∣ (T.subgroupOf D).index) (hAT : A ≤ normalizer (T : Set M))
    {Q : Subgroup (M ⧸ R)} (hQ2 : IsPGroup 2 Q) (hQD : Q ≤ D.map (QuotientGroup.mk' R))
    (hQA : ∀ a ∈ A, ∀ q ∈ Q, QuotientGroup.mk' R a * q = q * QuotientGroup.mk' R a) :
    ∃ (H : Subgroup M) (c : M ⧸ R), H ≤ T ⊓ centralizer (A : Set M) ∧
      H.map (QuotientGroup.mk' R) = Q.map (MulAut.conj c).toMonoidHom := by
  let W : Subgroup M := D ⊓ centralizer (A : Set M) ⊓ Q.comap (QuotientGroup.mk' R)
  have hWQ : W.map (QuotientGroup.mk' R) = Q := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · intro q hq
      obtain ⟨d, hd, hdc, hdq⟩ := exists_fixed_lift_of_mem hD3 hA hQD hQA hq
      exact ⟨d, ⟨⟨hd, hdc⟩, Subgroup.mem_comap.mpr (hdq ▸ hq)⟩, hdq⟩
  obtain ⟨X, hXW, hX2, hXQ⟩ := exists_pSubgroup_map_eq (QuotientGroup.mk' R) hQ2 hWQ
  obtain ⟨g, hgc, hg⟩ := exists_conj_mem_of_le_inf_centralizer hD3 hA hT2 hTsyl hAT hX2
    (fun x hx => (hXW hx).1.1) (fun x hx => (hXW hx).1.2)
  refine ⟨X.map (MulAut.conj g).toMonoidHom, QuotientGroup.mk' R g, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨hg x hx, Subgroup.mul_mem _ (Subgroup.mul_mem _ hgc (hXW hx).1.2)
      (Subgroup.inv_mem _ hgc)⟩
  · have hcomm : (QuotientGroup.mk' R).comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (QuotientGroup.mk' R g)).toMonoidHom.comp (QuotientGroup.mk' R) := by
      ext x
      simp
    rw [← hXQ, Subgroup.map_map, Subgroup.map_map, hcomm]

end CFSG.LocalAnalysis.RankThreeTheoremC
