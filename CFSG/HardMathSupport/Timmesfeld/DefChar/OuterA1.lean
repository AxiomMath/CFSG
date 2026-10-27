module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.GorensteinWalter CFSG.Open

theorem mem_range_toPGL_of_pow_eq_one {K : Type} [Field K] [Finite K]
    (_hK : IsOddPrimePower (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (g : PGL2 K)
    (hg : g ^ p = 1) :
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd (hp.odd_of_ne_two hp2) hg

theorem exists_inner_of_elemAbelian_psl2 {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hKc : 3 < Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (D : Subgroup (MulAut (PSL2 K))) (hexp : ∀ a ∈ D, a ^ p = 1)
    (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range, x ≠ 1 := by
  classical
  obtain ⟨ℓ, f, hℓ, -, hf, hKcard⟩ := id hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hinj := pGammaL2ToMulAutPSL2_injective K hK hKc
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hKc
  let Ψe : PGammaL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hK hKc) ⟨hinj, hsurj⟩
  let N : Subgroup (PGammaL2 K) := (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range
  have hcyc : IsCyclic (PGammaL2 K ⧸ N) := pGammaL2_quotient_pgl_isCyclic K hK
  let Θ : MulAut (PSL2 K) →* PGammaL2 K ⧸ N :=
    (QuotientGroup.mk' N).comp Ψe.symm.toMonoidHom
  let α : D →* PGammaL2 K ⧸ N := Θ.comp D.subtype
  have hexpα : Monoid.exponent α.range ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
    obtain ⟨x, rfl⟩ := α.rangeRestrict_surjective y
    have : (x : D) ^ p = 1 := Subtype.ext (hexp x x.2)
    rw [← map_pow, this, map_one]
  rw [IsCyclic.exponent_eq_card] at hexpα
  have hsplit : Nat.card D = Nat.card α.range * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
  have hrle : Nat.card α.range ≤ p := Nat.le_of_dvd hp.pos hexpα
  have hk1 : 1 < Nat.card α.ker := by
    by_contra hle
    have h1 : Nat.card D ≤ p * 1 := by
      rw [hsplit]
      exact Nat.mul_le_mul hrle (by omega)
    omega
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdk' : Θ (d : MulAut (PSL2 K)) = 1 := hdk
  have hdN : Ψe.symm (d : MulAut (PSL2 K)) ∈ N := (QuotientGroup.eq_one_iff _).1 hdk'
  obtain ⟨g, hg⟩ := hdN
  have hdg : (d : MulAut (PSL2 K)) = pgl2InnerAutPSL2 K hK hKc g := by
    rw [← pGammaL2ToMulAutPSL2_inl K hK hKc, ← Ψe.apply_symm_apply (d : MulAut (PSL2 K)), ← hg]
    rfl
  have hgp : g ^ p = 1 := by
    have h1 : Ψe.symm ((d : MulAut (PSL2 K)) ^ p) = 1 := by
      rw [hexp d d.2, map_one]
    rw [map_pow, ← hg, ← map_pow] at h1
    exact SemidirectProduct.inl_injective (by rw [map_one]; exact h1)
  obtain ⟨y, hy⟩ := mem_range_toPGL_of_pow_eq_one hK hp hp2 g hgp
  refine ⟨d, ⟨d.2, y, ?_⟩, fun h => hd1' (Subtype.ext h)⟩
  rw [hdg, ← hy, pgl2InnerAutPSL2_toPGL]

theorem defCharOuterRankFamA_one :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, (∃ q, idx.1 = .A 1 q) →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic = p →
          ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 3 →
            ∃ x ∈ D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, x ≠ 1 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨q, hq⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hq
  subst hq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p = q.p := by simpa using hch.symm
  subst hpq
  have hlin : CFSG.AGLEmbedding.IsLinTwoIndex q.p q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, rfl, rfl⟩
  obtain ⟨e0⟩ := hS
  obtain ⟨e1⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
  let e : S ≃* PSL2 (GaloisField q.p q.exponent) := e0.trans e1
  set φ : MulAut S ≃* MulAut (PSL2 (GaloisField q.p q.exponent)) := MulAut.congr e with hφ
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hodd : IsOddPrimePower (Nat.card (GaloisField q.p q.exponent)) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.odd_of_ne_two hp2, q.exponent_pos, hKq⟩
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := hv
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff] at this
    simpa [TauCeti.PrimePower.card_def] using this.1.2 rfl
  have hcardD : Nat.card (D.map φ.toMonoidHom) = q.p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := exists_inner_of_elemAbelian_psl2
    (K := GaloisField q.p q.exponent) hodd (by rw [hKq]; omega) hp hp2 (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ q.p = 1
      rw [← map_pow, hD.2 a ha, map_one])
    (by
      rw [hcardD]
      simpa using Nat.pow_lt_pow_right hp.one_lt (show 1 < 3 by norm_num))
  obtain ⟨x, hxD, rfl⟩ := hx'D
  obtain ⟨g, hg⟩ := hx'I
  refine ⟨x, ⟨hxD, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
  apply φ.injective
  change _ = φ.toMonoidHom x
  rw [← hg]
  ext s
  simp [hφ, MulAut.congr_apply]

end CFSG.HardMathSupport.Timmesfeld.DefChar
