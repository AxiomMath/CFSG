module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_inner_of_elemAbelian_primeFormP {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hpq : ¬ p ∣ ℓ ^ f + 1)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hexp : ∀ a ∈ D, a ^ p = 1) (hcard : p < Nat.card D) :
    ∃ x ∈ D ⊓ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), x ≠ 1 := by
  classical
  have hfin := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, hDnorm, -, hDI⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set Dl := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDl
  set F := primeFormFieldFactor h hC hn hq with hF
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  let α : D →* (K ≃+* K) := F.comp D.subtype
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
  set x : MulAut T := (d : MulAut T) with hx
  have hxD : x ∈ D := d.2
  have hxDl : x ∈ Dl := by
    rw [← hFker, MonoidHom.mem_ker]
    exact hdk
  have hIN : (inner T).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hcop : Nat.Coprime p (Nat.card (Dl ⧸ (inner T).subgroupOf Dl)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hpq (hd.trans hDI)
  have hxI : x ∈ inner T := by
    set y : Dl ⧸ (inner T).subgroupOf Dl := QuotientGroup.mk ⟨x, hxDl⟩ with hy
    have hyp : y ^ p = 1 := by
      rw [hy, ← QuotientGroup.mk_pow]
      have : (⟨x, hxDl⟩ : Dl) ^ p = 1 := Subtype.ext (hexp x hxD)
      rw [this]; rfl
    have hyd : orderOf y ∣ Nat.card (Dl ⧸ (inner T).subgroupOf Dl) := orderOf_dvd_natCard y
    have hyo : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
    have : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop hyo hyd
    have hy1 : y = 1 := orderOf_eq_one_iff.1 this
    rw [hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
    exact hy1
  exact ⟨x, ⟨hxD, hxI⟩, fun h => hd1' (Subtype.ext h)⟩

theorem defCharOuterRankFamTwistedA : DefCharOuterRankFam .twistedA := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  set φ := MulAut.congr e with hφ
  have hpq' : p = q.p := hpq
  subst hpq'
  have hndvd : ¬ q.p ∣ q.p ^ q.exponent + 1 := by
    intro hd
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hd))
  have hcardD : Nat.card (D.map φ.toMonoidHom) = q.p ^ 3 := by
    rw [Subgroup.card_map_of_injective φ.injective]; exact hcard
  obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ := exists_inner_of_elemAbelian_primeFormP h (n := r + 1)
    (by omega) hq' hp hndvd (D.map φ.toMonoidHom)
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
