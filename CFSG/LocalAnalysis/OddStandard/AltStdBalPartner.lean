module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicConj
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicZStar
public import CFSG.LocalAnalysis.OddStandard.AltStdBalLocal

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.OddStandard.Solomon75

section Conj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

@[expose] noncomputable def centralizerEquivMap (φ : G ≃* G) (L : Subgroup G) :
    centralizer (L : Set G) ≃* centralizer ((L.map φ.toMonoidHom : Subgroup G) : Set G) :=
  (MulEquiv.subgroupMap φ (centralizer (L : Set G))).trans
    (MulEquiv.subgroupCongr (centralizer_map_equiv φ L).symm)

theorem Setting.conj (h : Setting G L n) (g : G) : Setting G (CFSG.conjugate L g) n := by
  obtain ⟨e⟩ := h.iso
  obtain ⟨S, hS⟩ := h.cyc
  have hφ : CFSG.conjugate L g = L.map (MulAut.conj g⁻¹).toMonoidHom := rfl
  refine ⟨⟨h.std.simple, h.std.nonab, h.std.kProper,
    standardComponentIsStandard_conjugate g h.std.standard⟩, h.hn, ?_, ?_, h.bal⟩
  · exact ⟨(Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.trans e⟩
  · rw [hφ]
    let θ := centralizerEquivMap (MulAut.conj g⁻¹) L
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨Sylow.mapSurjective (f := θ.toMonoidHom)
      (fun y => ⟨θ.symm y, θ.apply_symm_apply y⟩) S, ?_⟩
    show IsCyclic ↥((S : Subgroup (centralizer (L : Set G))).map θ.toMonoidHom)
    exact (Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).isCyclic.1 hS

theorem Cyc.conj (d : Cyc L Q z) (g : G) :
    Cyc (CFSG.conjugate L g) (CFSG.conjugate Q g) (g⁻¹ * z * g) := by
  have hf : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [centralizer_conjugate]
    exact Subgroup.map_mono d.le
  · exact d.pgroup.map _
  · have := d.odd_index
    unfold CFSG.conjugate
    rw [centralizer_map_equiv (MulAut.conj g⁻¹) L, Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact this
  · exact (Subgroup.equivMapOfInjective Q _ hf).isCyclic.1 d.cyclic
  · have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply] at this
    simpa using this.trans d.order
  · exact ⟨z, d.mem, by simp⟩

end Conj

section Partner

open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem eq_of_mem_centralizer_of_commute (h : Setting G L n) (d : Cyc L Q z) {a : G}
    (haK : a ∈ centralizer (L : Set G)) (ha2 : orderOf a = 2) (hcomm : a * z = z * a) :
    a = z := by
  have haQ : a ∈ Q := by
    rw [← cent_inf_eq h d]
    exact ⟨haK, mem_centralizer_singleton_iff.2 hcomm⟩
  exact eq_of_orderOf_eq_two_of_isCyclic d.cyclic haQ d.mem ha2 d.order

theorem exists_partner (h : Setting G L n) (d : Cyc L Q z) :
    ∃ g : G, g⁻¹ * z * g ≠ z ∧ (g⁻¹ * z * g) * z = z * (g⁻¹ * z * g) ∧
      g⁻¹ * z * g ∉ centralizer (L : Set G) ∧
      z ∉ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  have := h.std.simple
  obtain ⟨g, hne, hcomm⟩ := exists_commuting_conj h.std.nonab d.order
  have hord : orderOf (g⁻¹ * z * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply] at this
    simpa using this.trans d.order
  have haK : g⁻¹ * z * g ∉ centralizer (L : Set G) := fun haK =>
    hne (eq_of_mem_centralizer_of_commute h d haK hord hcomm)
  refine ⟨g, hne, hcomm, haK, fun hzK' => ?_⟩
  rw [centralizer_conjugate] at hzK'
  have hz1 : z ∈ (centralizer (L : Set G)).map (MulAut.conj (1 : G)).toMonoidHom := by
    simpa using d.le d.mem
  have hzg : z ∈ (centralizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := hzK'
  have hgN := mem_normalizer_of_even_orderOf_mem h.isStandard (a := 1) (b := g⁻¹) (x := z)
    (by rw [d.order]; exact even_two) hz1 hzg
  have hgN' : g⁻¹ ∈ normalizer (centralizer (L : Set G) : Set G) := by simpa using hgN
  apply haK
  have := (mem_normalizer_iff.1 hgN' z).1 (d.le d.mem)
  simpa using this

end Partner

end CFSG.OddStandard.AltStdBal
