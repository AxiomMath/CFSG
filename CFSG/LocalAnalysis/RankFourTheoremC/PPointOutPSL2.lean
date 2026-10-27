module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.GorensteinWalter Subgroup

universe u

theorem commutator_pGammaL2_le_psl (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    commutator (PGammaL2 K) ≤ pGammaL2PSLRange K := by
  classical
  have hJn : (pGammaL2PSLRange K).Normal := pGammaL2PSLRange_normal K hK hcard
  set J := pGammaL2PSLRange K with hJ
  set L := pGammaL2PGLRange K with hL
  set H₂ : Subgroup (PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range with hH₂
  have hmemJ : ∀ g : PGL2 K, (SemidirectProduct.inl g : PGammaL2 K) ∈ J ↔ g ∈ H₂ := by
    intro g
    rw [hJ, mem_pGammaL2PSLRange_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, SemidirectProduct.inl_injective hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hJL : J ≤ L := by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K x).mp hx
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp (pgl2_psl2Range_index_eq_two K hK)
  have hcomm : ∀ γ : PGammaL2 K, ∀ l ∈ L, γ * l * γ⁻¹ * l⁻¹ ∈ J := by
    intro γ l hl
    obtain ⟨g, rfl⟩ := hl
    have hconj : γ * SemidirectProduct.inl g * γ⁻¹ ∈ L :=
      (pGammaL2PGLRange_normal K).conj_mem _ ⟨g, rfl⟩ γ
    obtain ⟨g', hg'⟩ := hconj
    have hiff : g' ∈ H₂ ↔ g ∈ H₂ := by
      rw [← hmemJ, ← hmemJ, hg']
      constructor
      · intro h
        have := hJn.conj_mem _ h γ⁻¹
        simpa [mul_assoc] using this
      · intro h
        exact hJn.conj_mem _ h γ
    have hg'g : g' * g⁻¹ ∈ H₂ := by
      by_cases hg : g ∈ H₂
      · exact H₂.mul_mem (hiff.mpr hg) (H₂.inv_mem hg)
      · have h1 : g * a ∈ H₂ := by
          rcases ha g with h | h
          · exact h.1
          · exact absurd h.2 (by tauto)
        have hg2 : g' ∉ H₂ := fun h => hg (hiff.mp h)
        have h2 : g' * a ∈ H₂ := by
          rcases ha g' with h | h
          · exact h.1
          · exact absurd h.2 (by tauto)
        have := H₂.mul_mem h2 (H₂.inv_mem h1)
        simpa [mul_assoc] using this
    have : γ * SemidirectProduct.inl g * γ⁻¹ * (SemidirectProduct.inl g)⁻¹ =
        SemidirectProduct.inl (g' * g⁻¹) := by
      rw [← hg', map_mul, map_inv]
    rw [this]
    exact (hmemJ _).mpr hg'g
  have hcyc : IsCyclic (PGammaL2 K ⧸ L) := pGammaL2_quotient_pgl_isCyclic K hK
  have hQ : IsMulCommutative (PGammaL2 K ⧸ J) := by
    refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.map J L (MonoidHom.id (PGammaL2 K)) (fun x hx => hJL hx)) ?_
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hq' : (QuotientGroup.mk g : PGammaL2 K ⧸ L) = 1 := hq
    have hgL : g ∈ L := (QuotientGroup.eq_one_iff g).mp hq'
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := hcomm g'⁻¹ g⁻¹ (L.inv_mem hgL)
    have h2 := J.inv_mem this
    simpa [mul_assoc] using h2
  have := Abelianization.commutator_subset_ker (QuotientGroup.mk' J)
  rwa [QuotientGroup.ker_mk'] at this

theorem exists_conj_eq_commutator_psl2 (K : Type u) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hf : 1 ≤ f) (hKcard : Nat.card K = p ^ f) (hcard : 3 < Nat.card K)
    (α β : MulAut (PSL2 K)) : ∃ y : PSL2 K, α * β * α⁻¹ * β⁻¹ = MulAut.conj y := by
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, f, Fact.out, hpodd, hf, hKcard⟩
  obtain ⟨a, rfl⟩ := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard α
  obtain ⟨b, rfl⟩ := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard β
  have hc : a * b * a⁻¹ * b⁻¹ ∈ pGammaL2PSLRange K :=
    commutator_pGammaL2_le_psl K hK hcard (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top b))
  obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff K _).mp hc
  refine ⟨y, ?_⟩
  have h1 : pGammaL2ToMulAutPSL2 K hK hcard (a * b * a⁻¹ * b⁻¹) =
      pGammaL2ToMulAutPSL2 K hK hcard (a) * pGammaL2ToMulAutPSL2 K hK hcard b *
        (pGammaL2ToMulAutPSL2 K hK hcard a)⁻¹ * (pGammaL2ToMulAutPSL2 K hK hcard b)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [← h1, ← hy, pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]

theorem exists_conj_eq_commutator_of_mulEquiv_psl2 {X : Type*} [Group X] (K : Type u) [Field K]
    [Finite K] {p f : ℕ} [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (hKcard : Nat.card K = p ^ f) (hcard : 3 < Nat.card K)
    (e : X ≃* PSL2 K) (α β : MulAut X) :
    ∃ k : X, ∀ z : X, (α * β * α⁻¹ * β⁻¹) z = k * z * k⁻¹ := by
  obtain ⟨y, hy⟩ := exists_conj_eq_commutator_psl2 K hpodd hf hKcard hcard
    (MulAut.congr e α) (MulAut.congr e β)
  refine ⟨e.symm y, fun z => ?_⟩
  have h1 : e ((α * β * α⁻¹ * β⁻¹) z) = y * e z * y⁻¹ := by
    have := congrArg (fun φ : MulAut (PSL2 K) => φ (e z)) hy
    simpa [MulAut.congr_apply, MulAut.conj_apply] using this
  apply e.injective
  rw [h1]
  simp [map_mul, map_inv]

end CFSG.LocalAnalysis.RankFourTheoremC
