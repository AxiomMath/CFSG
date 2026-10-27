module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem exists_fixed_of_perm_pow_three {α : Type} [Finite α] (σ : Equiv.Perm α)
    (h3 : σ ^ 3 = 1) (hcop : Nat.Coprime 3 (Nat.card α)) : ∃ a : α, σ a = a := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let H : Subgroup (Equiv.Perm α) := Subgroup.zpowers σ
  have hH : IsPGroup 3 H := by
    have hord : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hcard : Nat.card H = orderOf σ := by
      rw [Nat.card_zpowers]
    have hdvd : Nat.card H ∣ 3 ^ 1 := by rw [hcard, pow_one]; exact hord
    rw [IsPGroup.iff_card]
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨i, hi⟩
  have hfix := hH.card_modEq_card_fixedPoints α
  have hne : (MulAction.fixedPoints H α).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints H α) = 0 := by
      simp [hemp]
    rw [h0] at hfix
    have h3dvd : 3 ∣ Nat.card α := (Nat.modEq_zero_iff_dvd).1 hfix
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3dvd) (by norm_num)
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, ?_⟩
  have hσ : σ ∈ H := Subgroup.mem_zpowers σ
  have := (MulAction.mem_fixedPoints.1 ha) ⟨σ, hσ⟩
  simpa [Equiv.Perm.smul_def] using this

theorem pQuot_equiv_image {A : Type} [Group A] [Finite A] (L : Subgroup A) :
    Nonempty (PQuot 3 L ≃* PQuot 3 (L.map (QuotientGroup.mk' (GLAPPrimeCore 3 A)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let π := QuotientGroup.mk' (GLAPPrimeCore 3 A)
  let f : ↥L →* ↥(L.map π) := (π.comp L.subtype).codRestrict (L.map π) (fun x => ⟨x, x.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 y.2
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  have hcopA : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 A)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := A)
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    have hmap : Nat.card (f.ker.map L.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective Subtype.val_injective
    have hle : f.ker.map L.subtype ≤ GLAPPrimeCore 3 A := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      have hfy : f y = 1 := hy
      have hπ : π (y : A) = 1 := congrArg Subtype.val hfy
      exact (QuotientGroup.eq_one_iff (y : A)).1 hπ
    have hdv : Nat.card (f.ker.map L.subtype) ∣ Nat.card (GLAPPrimeCore 3 A) :=
      Subgroup.card_dvd_of_le hle
    have hcop' : Nat.Coprime 3 (Nat.card f.ker) := by
      rw [← hmap]
      exact Nat.Coprime.coprime_dvd_right hdv hcopA
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop'
  obtain ⟨h1, h2⟩ := CFSG.prime_complement_kernel_core_preimage f hf hker
  let F : ↥L →* ↥(L.map π) ⧸ GLAPPrimeCore 3 ↥(L.map π) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(L.map π))).comp f
  have hF : Function.Surjective F := fun y => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective y
    obtain ⟨z, hz⟩ := hf x
    refine ⟨z, ?_⟩
    show QuotientGroup.mk (f z) = y
    rw [hz, hx]
  have hkerF : F.ker = GLAPPrimeCore 3 ↥L := by
    have h := MonoidHom.comap_ker (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(L.map π))) f
    rw [QuotientGroup.ker_mk'] at h
    have h1' : (GLAPPrimeCore 3 ↥(L.map π)).comap f = GLAPPrimeCore 3 ↥L := h1
    rw [← h, h1']
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerF).symm.trans (QuotientGroup.quotientKerEquivOfSurjective F hF)⟩

theorem psimple_equiv {P P' : Type} [Group P] [Group P'] (e : P ≃* P') :
    Nonempty (P ⧸ Subgroup.center P ≃* P' ⧸ Subgroup.center P') :=
  ⟨QuotientGroup.congr (Subgroup.center P) (Subgroup.center P') e (Subgroup.map_center_eq e)⟩

theorem u4_catalogIs_of_equiv {S S' : Type} [Group S] [Group S'] {Q : TauCeti.CFSGIndex → Prop}
    (e : S ≃* S') (h : catalogIs S Q) : catalogIs S' Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
