module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.LieType.Ree.SmallReeModelSchreier

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ
  exists_eq_conj_mul_frobeniusΓ_pow)

theorem exists_inner_of_elemAbelian_of_outerCyclic {G : Type} [Group G] (F : MulAut G)
    (hF : ∀ α : MulAut G, ∃ (g : G) (k : ℕ), α = MulAut.conj g * F ^ k) {p : ℕ} (hp : p.Prime)
    (D : Subgroup (MulAut G)) (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ innerAut G, x ≠ 1 := by
  classical
  have : (innerAut G).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal G
  let π : MulAut G →* MulAut G ⧸ innerAut G := QuotientGroup.mk' (innerAut G)
  have hcyc : IsCyclic (MulAut G ⧸ innerAut G) := by
    refine ⟨⟨π F, fun x => ?_⟩⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, k, hα⟩ := hF α
    have h1 : π (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
    have : π α = π F ^ k := by rw [hα, map_mul, h1, one_mul, map_pow]
    change π α ∈ Subgroup.zpowers (π F)
    rw [this]
    exact ⟨(k : ℤ), by simp⟩
  let α : D →* MulAut G ⧸ innerAut G := π.comp D.subtype
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
  have hfin : Finite α.ker := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial α.ker := Finite.one_lt_card_iff_nontrivial.1 hk1
  obtain ⟨⟨d, hdk⟩, hd1⟩ := exists_ne (1 : α.ker)
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  refine ⟨(d : MulAut G), ⟨d.2, ?_⟩, fun h => hd1' (Subtype.ext h)⟩
  have : π (d : MulAut G) = 1 := hdk
  exact (QuotientGroup.eq_one_iff _).1 this

theorem defCharOuterRankFamReeG2 :
    DefCharOuterRankFam .reeG2 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨d, hv⟩ := idx
  obtain ⟨m, rfl⟩ := hidx
  obtain ⟨e0⟩ := hS
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : S ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    ((e0.trans b.symm).trans e1).trans E
  set φ := MulAut.congr e with hφ
  have hcardD : Nat.card (D.map φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := exists_inner_of_elemAbelian_of_outerCyclic
    (frobeniusΓ : MulAut (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m))
    (exists_eq_conj_mul_frobeniusΓ_pow hm1 hK) hp (D.map φ.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change φ a ^ p = 1
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
