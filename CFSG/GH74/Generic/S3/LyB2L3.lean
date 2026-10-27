module

public import CFSG.GH74.Generic.S3.LyB2Block
public import CFSG.GH74.Generic.S3.V1InnerLib
public import CFSG.GH74.Generic.S3.L3FRankGen4
public import CFSG.GH74.KGroups.L3EpsUniInv

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Blueprint CFSG.BenderSuzuki.MatrixGroups Subgroup
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.KGroups.L3Eps (tInv tInv_mul_self tInv_ne_one blockEmb blockEmb_injective blockSub
  exists_projectiveSL_equiv commutator_mem_blockSub)
open CFSG.GH74.KGroups.L3Eps.Uni (dU IsCover levS levU exists_cover_of_equiv theta_dU_sq theta_dU_ne_one
  levS_commutator_mem)
open CFSG.GH74.Generic.S3.L3Ord (classical_clause)
open scoped commutatorElement MatrixGroups

theorem blockData_of_sl2_embedding {L : Type} [Group L]
    (h : ∀ s : L, s * s = 1 → s ≠ 1 → ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀)
      (φ : SL(2, F₀) →* L), Odd (Nat.card F₀) ∧ Function.Injective φ ∧
        ∀ a ∈ centralizer ({s} : Set L), ∀ b ∈ centralizer ({s} : Set L), ⁅a, b⁆ ∈ φ.range) :
    BlockData L := by
  intro s hs2 hs1
  obtain ⟨F₀, hF, hfin, φ, hodd, hinj, hcomm⟩ := h s hs2 hs1
  refine ⟨F₀, hF, hfin, φ.range, (QuotientGroup.mk' (center SL(2, F₀))).comp
    (MonoidHom.ofInjective hinj).symm.toMonoidHom, hodd, ?_, hcomm⟩
  intro g hg
  have h1 : (MonoidHom.ofInjective hinj).symm g ∈ center SL(2, F₀) :=
    (QuotientGroup.eq_one_iff _).1 hg
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro k
  apply (MonoidHom.ofInjective hinj).symm.injective
  simpa using h1 ((MonoidHom.ofInjective hinj).symm k)

theorem blockData_of_psl2_subgroup {L : Type} [Group L]
    (h : ∀ s : L, s * s = 1 → s ≠ 1 → ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (S : Subgroup L),
      Nonempty (↥S ≃* PSL2MatrixGroup F₀) ∧ Odd (Nat.card F₀) ∧
        ∀ a ∈ centralizer ({s} : Set L), ∀ b ∈ centralizer ({s} : Set L), ⁅a, b⁆ ∈ S) :
    BlockData L := by
  intro s hs2 hs1
  obtain ⟨F₀, hF, hfin, S, ⟨e⟩, hodd, hcomm⟩ := h s hs2 hs1
  refine ⟨F₀, hF, hfin, S, e.toMonoidHom, hodd, ?_, hcomm⟩
  intro g hg
  have : g = 1 := e.injective (by simpa using hg)
  rw [this]
  exact Subgroup.one_mem _

theorem sl2_embedding_of_lin {p f : ℕ} {K : Type} [Group K]
    (hX : StatedClassicalModel K .PSL 3 p f) (hodd : Odd (p ^ f)) :
    ∀ s : K, s * s = 1 → s ≠ 1 → ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (φ : SL(2, F₀) →* K),
      Odd (Nat.card F₀) ∧ Function.Injective φ ∧
        ∀ a ∈ centralizer ({s} : Set K), ∀ b ∈ centralizer ({s} : Set K), ⁅a, b⁆ ∈ φ.range := by
  intro s hs2 hs1
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hoddF : Odd (Nat.card F) := hF ▸ hodd
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hoddF
  have hex2 : e s * e s = 1 := by rw [← map_mul, hs2, map_one]
  have hex1 : e s ≠ 1 := fun h => hs1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := singleInv_projectiveSL h2 (e s) tInv hex2 hex1 tInv_mul_self (tInv_ne_one h2)
  let e' : K ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
  have he' : e' s = tInv := by
    show MulAut.conj g (e s) = tInv
    rw [MulAut.conj_apply]
    exact hg
  have hcen : ∀ a ∈ centralizer ({s} : Set K), e' a ∈ centralizer ({tInv} : Set (projectiveSL 3 F)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    rw [← he', ← map_mul, ← map_mul, ha]
  refine ⟨F, hFf, hFfin, e'.symm.toMonoidHom.comp blockEmb, hoddF,
    e'.symm.injective.comp blockEmb_injective, ?_⟩
  intro a ha b hb
  obtain ⟨A, hA⟩ := commutator_mem_blockSub h2 (hcen a ha) (hcen b hb)
  refine ⟨A, ?_⟩
  show e'.symm (blockEmb A) = ⁅a, b⁆
  rw [hA, map_commutatorElement, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem sl2_embedding_of_uni {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    (hX : StatedClassicalModel K .PSU 3 p f) :
    ∀ s : K, s * s = 1 → s ≠ 1 → ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (φ : SL(2, F₀) →* K),
      Odd (Nat.card F₀) ∧ Function.Injective φ ∧
        ∀ a ∈ centralizer ({s} : Set K), ∀ b ∈ centralizer ({s} : Set K), ⁅a, b⁆ ∈ φ.range := by
  obtain ⟨hadm, F, hFf, hFfin, hF, ⟨e₀⟩⟩ := hX
  have hf : 1 ≤ f := hadm.2.1
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
    ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hS : SingleInv K := SingleInv.of_mulEquiv e₀.symm (singleInv_psu hU hp2)
  intro s hs2 hs1
  obtain ⟨θ₀, hθ₀⟩ := exists_cover_of_equiv hU e₀
  obtain ⟨g, hg⟩ := hS (θ₀ (dU hq)) s (theta_dU_sq hq θ₀) (theta_dU_ne_one hU hq hθ₀) hs2 hs1
  have hθ : IsCover hU ((MulAut.conj g).toMonoidHom.comp θ₀) := hθ₀.comp_equiv (MulAut.conj g)
  have hθt : ((MulAut.conj g).toMonoidHom.comp θ₀) (dU hq) = s := by
    simpa [MulAut.conj_apply] using hg
  have : Fact p.Prime := ⟨hp⟩
  have := hU.finite
  have := hU.charP
  obtain ⟨eS⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p)
    (f := f) hU.card_eq_sq
  refine ⟨CFSG.LieType.Steinberg.fixedSubfield F p f, inferInstance, inferInstance,
    (((MulAut.conj g).toMonoidHom.comp θ₀).comp (levU hq.pos)).comp eS.toMonoidHom, ?_, ?_, ?_⟩
  · rw [CFSG.LieType.Steinberg.card_fixedSubfield hU.card_eq_sq]
    exact hq
  · exact (hθ.injective_comp hU hq.pos).comp eS.injective
  · intro a ha b hb
    rw [← hθt] at ha hb
    obtain ⟨B, hB⟩ := levS_commutator_mem hU hθ hq ha hb
    exact ⟨eS.symm B, by simpa using hB⟩

theorem blockData_of_l3 {K : Type} [Group K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f) : BlockData K := by
  apply blockData_of_sl2_embedding
  rcases hmodel with h | h
  · exact sl2_embedding_of_lin (classical_clause (by decide) h)
      ((hp.odd_of_ne_two hp2).pow : Odd (p ^ f))
  · exact sl2_embedding_of_uni hp hp2 (classical_clause (by decide) h)

end CFSG.GH74.Generic.S3
