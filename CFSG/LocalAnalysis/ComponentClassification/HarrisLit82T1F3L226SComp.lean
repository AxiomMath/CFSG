module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace F3L226S

open F3L226

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hatIn_oPrimeResidualOf_normal (w : G) (L₁ : Subgroup G) :
    ((hatIn w (GH74.GLS.oPrimeResidualOf 3 L₁)).subgroupOf (hatIn w L₁)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨x, hx, hxn⟩ := hn
  obtain ⟨m, hm, hmg⟩ := g.2
  refine ⟨m * x * m⁻¹, ?_, ?_⟩
  · exact conj_mem_oPrimeResidualOf 3 hm hx
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hxn, ← hmg, map_mul, map_inv]

omit [Finite G] in
theorem isSubnormal_of_hatIn {w : G} {L₁ : Subgroup G} (hL₁C : L₁ ≤ centralizer {w})
    (hsn : (hatIn w (GH74.GLS.oPrimeResidualOf 3 L₁)).IsSubnormal) :
    (((pPrimeCore 2 ↥(centralizer ({w} : Set G))).map (centralizer {w}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {w})).IsSubnormal := by
  set C := centralizer ({w} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set L₃ := GH74.GLS.oPrimeResidualOf 3 L₁ with hL₃
  have hL₃C : L₃ ≤ C := (map_subtype_le _).trans hL₁C
  have h1 := hsn.comap π
  have h3 : (hatIn w L₃).comap π = L₃.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
    rw [hatIn, comap_map_eq, QuotientGroup.ker_mk']
  rw [h3] at h1
  have h2 : ((pPrimeCore 2 ↥C).map C.subtype ⊔ L₃).subgroupOf C =
      L₃.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
    rw [Subgroup.subgroupOf_sup (map_subtype_le _) hL₃C, sup_comm]
    congr 1
    exact comap_map_eq_self_of_injective C.subtype_injective _
  rw [h2]
  exact h1

theorem lemma226_of_twoComponent {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) (hc : z₁ * z₂ = z₂ * z₁)
    {L₁ : Subgroup G} (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hns : ¬ (((pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {z₁})).IsSubnormal)
    {K : Subgroup G} (hK : IsTwoComponentIn K (centralizer {z₁})) (hz₂K : z₂ ∈ K) :
    centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) ∧
      ⁅K, GH74.GLS.oPrimeResidualOf 3 L₁⁆ = K ∧
      (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z₁} : Set G) with hC
  have hz₂C : z₂ ∈ C := mem_centralizer_singleton_iff.mpr hc.symm
  have hL₁C : L₁ ≤ C := hL₁.1.trans inf_le_left
  set t : MBar z₁ := QuotientGroup.mk (⟨z₂, hz₂C⟩ : ↥C) with ht
  obtain ⟨hKc, hKq⟩ := isComponentOf_hatIn hK
  have htK : t ∈ hatIn z₁ K := mk_mem_hatIn hz₂K hz₂C
  have hM := isSolvableTwoComponentIn_hatIn hz₂ hz₂C hL₁
  set M := hatIn z₁ L₁ with hMdef
  have hMsol : Group.IsSolvable ↥M := F3L221.isSolvable_of_isSolvableTwoComponentIn hM
  set L₃ := GH74.GLS.oPrimeResidualOf 3 L₁ with hL₃
  have hL₃L₁ : L₃ ≤ L₁ := map_subtype_le _
  set X := hatIn z₁ L₃ with hXdef
  have hXM : X ≤ M := hatIn_mono hL₃L₁
  have hXn : (X.subgroupOf M).Normal := hatIn_oPrimeResidualOf_normal z₁ L₁
  have hXs : (X.subgroupOf (centralizer {t})).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hXM hM.1 hXn.isSubnormal hM.2.1
  have hXsol : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hXM) (inclusion_injective hXM)
  have hXC : X ≤ centralizer {t} := hXM.trans hM.1
  have hXns : ¬ X.IsSubnormal := fun hsn => hns (isSubnormal_of_hatIn hL₁C hsn)
  have hNt := compCentralizer_le_centralizer hKc htK
  have hXK : ¬ ∀ x ∈ X, ∀ d ∈ hatIn z₁ K, d * x = x * d := fun hcen =>
    hXns (isSubnormal_of_le_compCentralizer (le_compCentralizer hKc htK hXC hXs hXsol hcen)
      hNt hXs)
  have hnc : ¬ ∀ y ∈ hatIn z₁ K, y * t = t * y := by
    intro hcen
    apply hXK
    have hKC : hatIn z₁ K ≤ centralizer {t} := fun y hy =>
      mem_centralizer_singleton_iff.mpr (hcen y hy)
    intro x hx d hd
    exact (F3L221.commute_of_isQuasisimple hKC (isSubnormal_of_isComponentOf hKc).subgroupOf hKq
      hXC hXs hXsol x hx d hd).symm
  have hnorm : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) := by
    intro c hc'
    obtain ⟨hc₁, hc₂⟩ := mem_inf.mp hc'
    rw [F3L221.mem_normalizer_iff_map_conj_eq]
    by_contra hne
    have hmapC : C.map (MulAut.conj c).toMonoidHom = C := by
      ext y
      rw [mem_map_equiv, MulAut.conj_symm_apply]
      constructor
      · intro hy
        have h1 := mul_mem (mul_mem hc₁ hy) (inv_mem hc₁)
        rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at h1
      · intro hy
        exact mul_mem (mul_mem (inv_mem hc₁) hy) hc₁
    have hK' : IsTwoComponentIn (K.map (MulAut.conj c).toMonoidHom) C := by
      have h1 := L35.isTwoComponentIn_map_of_injective (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective hK
      rwa [hmapC] at h1
    have hz₂K' : z₂ ∈ K.map (MulAut.conj c).toMonoidHom := by
      refine ⟨z₂, hz₂K, ?_⟩
      have h1 : c * z₂ = z₂ * c := mem_centralizer_singleton_iff.mp hc₂
      show c * z₂ * c⁻¹ = z₂
      rw [h1, mul_inv_cancel_right]
    apply hnc
    intro y hy
    exact hatIn_commute hK hK' (Ne.symm hne) hy (mk_mem_hatIn hz₂K' hz₂C)
  have hL₃N : L₃ ≤ normalizer (K : Set G) := (hL₃L₁.trans hL₁.1).trans hnorm
  have hXN : X ≤ normalizer ((hatIn z₁ K : Subgroup (MBar z₁)) : Set (MBar z₁)) :=
    hatIn_le_normalizer hL₃N
  have hcomm : ⁅K, L₃⁆ = K := by
    rcases commute_or_le_commutator hKc hXN with h | h
    · exact absurd h hXK
    · exact commutator_eq_of_le_hatIn hK hL₃N h
  refine ⟨hnorm, hcomm, fun hcen => hnc ?_⟩
  rintro _ ⟨⟨k, hkC⟩, hk, rfl⟩
  replace hk : k ∈ K := hk
  have h1 := mem_center_iff.mp hcen (QuotientGroup.mk ⟨k, hk⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
  have h2 := (mem_pPrimeCore_iff hK (mul_mem (inv_mem (mul_mem hk hz₂K)) (mul_mem hz₂K hk))).mp
    (by convert h1 using 1)
  have h3 : (QuotientGroup.mk (⟨k, hkC⟩ * ⟨z₂, hz₂C⟩) : MBar z₁) =
      QuotientGroup.mk (⟨z₂, hz₂C⟩ * ⟨k, hkC⟩) := by
    rw [QuotientGroup.eq]
    convert h2 using 1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h3
  exact h3

end F3L226S

end CFSG.ComponentClassification.HarrisLit.T1
