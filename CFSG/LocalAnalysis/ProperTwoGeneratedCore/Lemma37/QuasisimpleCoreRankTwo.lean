module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRankTwoCovering
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreA0TypeTwo

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem BadLift.quasiImage_ne_top
    (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (IH : CanonicalBelow (Nat.card J)) : quasiImage B u ≠ ⊤ := by
  intro htop
  have hrank := hu.pRank_eq_two_of_quasiImage_eq_top h hz htop
  set X := quasiNormalizer u with hX
  set N₀ := (CFSG.pPrimeCore 2 X).map X.subtype with hN₀
  have hN₀X : N₀ ≤ X := Subgroup.map_subtype_le _
  have hXN₀ : X ≤ Subgroup.normalizer (N₀ : Set J) := by
    intro x hx
    have hmem : (⟨x, hx⟩ : X) ∈
        Subgroup.normalizer ((CFSG.pPrimeCore 2 X : Subgroup X) : Set X) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map X.subtype (Subgroup.mem_map_of_mem X.subtype hmem)
  have hN₀odd : Odd (Nat.card N₀) := by
    rw [hN₀, Subgroup.card_map_of_injective X.subtype_injective]
    exact quasi_oddCore_odd u
  have hN₀B : ¬ N₀ ≤ B := by
    intro hle
    apply hu.subgroupOf_ne_top h
    have hker : (quasiMk u).ker ≤ B.subgroupOf X := by
      rw [QuotientGroup.ker_mk']
      exact fun o ho => Subgroup.mem_subgroupOf.mpr (hle ⟨o, ho, rfl⟩)
    have hcomap := congrArg (Subgroup.comap (quasiMk u)) htop
    rwa [Subgroup.comap_map_eq_self hker, Subgroup.comap_top] at hcomap
  obtain ⟨g, hgQ, hgz⟩ := hz.exists_conj_commute h hu.sq
  have hgX : g * z * g⁻¹ ∈ X :=
    (h.mem_quasiNormalizer_conj_iff hu.sq g z).mp
      (h.mem_quasiNormalizer_of_mul_eq (h.conj_mul_self hu.sq g) hgz.symm)
  obtain ⟨c, hcX, hcB⟩ := hu.toEscapingLift.exists_mem_inv_mul_mem h hz hgX
  obtain ⟨n, hnNV, hnQ, hnz, hmax⟩ := hz.exists_sylowPlaced h hgQ (h.conj_mul_self hu.sq g) hgz
  have hwk : n⁻¹ * (g⁻¹ * u * g) * n = (g * n)⁻¹ * u * (g * n) := by group
  rw [hwk] at hnQ hnz hmax
  set k := g * n with hk
  have hww : (k⁻¹ * u * k) * (k⁻¹ * u * k) = centralElt J := h.conj_mul_self hu.sq k
  have hkB : c⁻¹ * k ∈ B := by
    rw [hk, ← mul_assoc]
    exact B.mul_mem hcB (hz.normalizer_fourGroup_le h hnNV)
  have hrankw : CFSG.Open.pRank 2 (quasiNormalizer (k⁻¹ * u * k)) ≤ 2 := by
    have h1 := CFSG.SectionRank.pRank_le_map (p := 2) (by decide) (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective (quasiNormalizer (k⁻¹ * u * k))
    have h2 : (quasiNormalizer (k⁻¹ * u * k)).map (MulAut.conj k).toMonoidHom ≤ X := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (h.mem_quasiNormalizer_conj_iff hu.sq k x).mp hx
    have h3 := CFSG.SectionRank.pRank_mono (p := 2) (by decide) h2
    omega
  set N := N₀.map (MulAut.conj k⁻¹).toMonoidHom with hN
  have hNmem : ∀ y, y ∈ N ↔ k * y * k⁻¹ ∈ N₀ := fun y => by
    rw [hN, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hNX : N ≤ quasiNormalizer (k⁻¹ * u * k) := fun y hy =>
    (h.mem_quasiNormalizer_conj_iff hu.sq k y).mpr (hN₀X ((hNmem y).mp hy))
  have hXN : quasiNormalizer (k⁻¹ * u * k) ≤ Subgroup.normalizer (N : Set J) := by
    intro x hx
    have hx' := (h.mem_quasiNormalizer_conj_iff hu.sq k x).mp hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hNmem, hNmem, Subgroup.mem_normalizer_iff.mp (hXN₀ hx') (k * y * k⁻¹),
      show k * (x * y * x⁻¹) * k⁻¹ = k * x * k⁻¹ * (k * y * k⁻¹) * (k * x * k⁻¹)⁻¹ by group]
  have hNodd : Odd (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
    exact hN₀odd
  have hNB : ¬ N ≤ B := by
    intro hle
    apply hN₀B
    intro y hy
    have hy' : c * y * c⁻¹ ∈ N₀ := (Subgroup.mem_normalizer_iff.mp (hXN₀ hcX) y).mp hy
    have h1 : k⁻¹ * (c * y * c⁻¹) * k ∈ B := hle ((hNmem _).mpr (by
      rw [show k * (k⁻¹ * (c * y * c⁻¹) * k) * k⁻¹ = c * y * c⁻¹ by group]
      exact hy'))
    rw [show y = (c⁻¹ * k) * (k⁻¹ * (c * y * c⁻¹) * k) * (c⁻¹ * k)⁻¹ by group]
    exact B.mul_mem (B.mul_mem hkB h1) (B.inv_mem hkB)
  by_cases hQX : (Q : Subgroup J) ≤ quasiNormalizer (k⁻¹ * u * k)
  · exact (A0Config.false_of_a0Config ⟨h, hz, hnQ, hww, hnz, hrankw, hNX, hXN, hNodd, hNB, hQX⟩
      IH).elim
  obtain ⟨W, hW, hWsq⟩ :=
    hz.exists_cover_of_sylowPlaced h hnQ hww hnz hrankw hNX hXN hNodd hNB hQX hmax
  apply hu.not_embedded
  refine hu.toEscapingLift.fusionStronglyEmbedded_of_le h hz
    (W := W.map (MulAut.conj k).toMonoidHom) (fun t ht ht2 => ?_) (fun y hy hyy => ?_)
  · rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    refine hW _ ((h.mem_quasiNormalizer_conj_iff hu.sq k _).mpr ?_) ?_
    · rw [show k * (k⁻¹ * t * k) * k⁻¹ = t by group]
      exact ht
    · have := (MulAut.conj k⁻¹).orderOf_eq t
      simp only [MulAut.conj_apply, inv_inv] at this
      rw [this, ht2]
  · rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hy
    refine hWsq _ hy ?_
    calc k⁻¹ * y * k * (k⁻¹ * y * k) = k⁻¹ * (y * y) * k⁻¹⁻¹ := by group
      _ = centralElt J := by
        rw [hyy, Setting.conj_eq_of_mem_center h.centralElt_mem_center]

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
