module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SL2RankA
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.IVK.L2Borel
  CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Signalizer CFSG.ABGLocalTools
open scoped Pointwise

namespace SL2Rank

section Stab

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

omit [Finite F] in
theorem psl2AutHom_mem_stabilizer (ψ : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (Q : Subgroup K)
    (θ : MulAut K) (hθ : ∀ k, θ k ∈ Q ↔ k ∈ Q) :
    psl2AutHom (MulAut.congr ψ θ) ∈ MulAction.stabilizer (MulAut (PSL2 F))
      (Q.map ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
        ψ.toMonoidHom)) := by
  set π : K →* PSL2 F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp ψ.toMonoidHom with hπ
  have key : ∀ θ' : MulAut K, (∀ k, θ' k ∈ Q ↔ k ∈ Q) →
      ∀ y ∈ Q.map π, psl2AutHom (MulAut.congr ψ θ') y ∈ Q.map π := by
    intro θ' hθ' y hy
    obtain ⟨q, hq, rfl⟩ := hy
    refine ⟨θ' q, (hθ' q).2 hq, ?_⟩
    show QuotientGroup.mk' _ (ψ (θ' q)) = psl2MulAutOf (MulAut.congr ψ θ') (QuotientGroup.mk' _ (ψ q))
    rw [psl2MulAutOf_mk]
    simp
  rw [mem_stabilizer_iff_forall]
  intro y
  refine ⟨fun hy => ?_, key θ hθ y⟩
  have hθinv : ∀ k, θ⁻¹ k ∈ Q ↔ k ∈ Q := fun k => by
    rw [← hθ (θ⁻¹ k)]
    simp
  have h := key θ⁻¹ hθinv _ hy
  have e1 : psl2AutHom (MulAut.congr ψ θ⁻¹) (psl2AutHom (MulAut.congr ψ θ) y) = y := by
    rw [← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    rfl
  rwa [e1] at h

end Stab

section Count

variable {Y : Type} [Group Y] [Finite Y]

theorem card_le_four_mul_card_cent {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup Y}
    (hc : C43b p X) {E : Subgroup Y} (hEN : E ≤ normalizer (X : Set Y))
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card ↥E ≤ 4 * Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) := by
  classical
  obtain ⟨n, hn, ⟨F, _, _, hFcard, ⟨φ⟩⟩, Q, hQ⟩ := hc
  have : Fact p.Prime := ⟨hp⟩
  have hnormal : (ncl X).Normal := Subgroup.normalClosure_normal
  let ψ : ↥(ncl X) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    φ.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hodd : Odd (Nat.card F) := hFcard ▸ (hp.odd_of_ne_two hp2).pow
  have h3 : 3 < Nat.card F := hFcard ▸ hn
  have : IsCyclic (F ≃+* F) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hFcard).2
  let ρ : ↥E →* MulAut (PSL2 F) :=
    (psl2AutHom.comp (MulAut.congr ψ).toMonoidHom).comp
      ((MulAut.conjNormal : Y →* MulAut ↥(ncl X)).comp E.subtype)
  have hρ : ∀ x : ↥E, ρ x = psl2AutHom (MulAut.congr ψ (MulAut.conjNormal (x : Y))) := fun x => rfl
  have hker : ∀ x : ↥E, ρ x = 1 ↔ (x : Y) ∈ centralizer ((ncl X : Subgroup Y) : Set Y) := by
    intro x
    rw [hρ, map_eq_one_iff _ (psl2AutHom_injective hodd h3), EmbeddingLike.map_eq_one_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨k, hk⟩)
      have h2 : (x : Y) * k * (x : Y)⁻¹ = k := h1
      calc k * (x : Y) = ((x : Y) * k * (x : Y)⁻¹) * (x : Y) := by rw [h2]
        _ = (x : Y) * k := by group
    · intro h
      ext k
      show (x : Y) * (k : Y) * (x : Y)⁻¹ = k
      rw [mul_inv_eq_iff_eq_mul]
      exact (h k k.2).symm
  let π : ↥(ncl X) →* PSL2 F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp ψ.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp ψ.surjective
  let Wb : Sylow p (PSL2 F) := Sylow.mapSurjective hπ Q
  have hWb : (Wb : Subgroup (PSL2 F)) = (Q : Subgroup ↥(ncl X)).map π := Sylow.coe_mapSurjective hπ Q
  have hmemQ : ∀ k : ↥(ncl X), k ∈ (Q : Subgroup ↥(ncl X)) ↔ (k : Y) ∈ X := by
    intro k
    have h0 : (k : Y) ∈ X ↔ (k : Y) ∈ Subgroup.map (ncl X).subtype (Q : Subgroup ↥(ncl X)) := by
      rw [hQ]
    rw [h0]
    constructor
    · intro hk
      exact ⟨k, hk, rfl⟩
    · rintro ⟨q, hq, hqk⟩
      have : q = k := Subtype.ext hqk
      exact this ▸ hq
  obtain ⟨c, hc⟩ := exists_psiEquiv_eq (L2.equivPSL F).symm hp hFcard Wb
  let e₁ : PSL2 F ≃* L2 F := (psiEquiv (L2.equivPSL F).symm c).symm.trans (L2.equivPSL F).symm
  have hstd : IsStd e₁ (Wb : Subgroup (PSL2 F)) := by
    intro k
    have h1 : toPSL e₁ k = (psiEquiv (L2.equivPSL F).symm c).symm k := by
      simp [e₁, toPSL]
    rw [h1, hc, Subgroup.mem_map_equiv]
  have hD : ρ.range ≤ MulAction.stabilizer (MulAut (PSL2 F)) (Wb : Subgroup (PSL2 F)) := by
    rintro _ ⟨x, rfl⟩
    rw [hWb, hρ]
    refine psl2AutHom_mem_stabilizer ψ Q _ ?_
    intro k
    rw [hmemQ, hmemQ, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hEN x.2) (k : Y)).symm
  have hsq : ∀ α ∈ ρ.range, α * α = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by simpa [sq] using hE.2 x x.2)
    rw [this, map_one]
  have hrange : Nat.card ρ.range ≤ 4 := card_le_four_of_stab e₁ hstd hodd ρ.range hD hsq
  have hkerCard : Nat.card ρ.ker = Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) := by
    have hmap : ρ.ker.map E.subtype = E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, (hker x).1 (MonoidHom.mem_ker.1 hx)⟩
      · rintro ⟨hyE, hyC⟩
        exact ⟨⟨y, hyE⟩, MonoidHom.mem_ker.2 ((hker ⟨y, hyE⟩).2 hyC), rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective E.subtype_injective]
  calc Nat.card ↥E = Nat.card ρ.ker * Nat.card ρ.range := (Subgroup.card_ker_mul_card_range ρ).symm
    _ ≤ Nat.card ρ.ker * 4 := Nat.mul_le_mul_left _ hrange
    _ = 4 * Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) := by
      rw [hkerCard, mul_comm]

end Count

end SL2Rank

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
