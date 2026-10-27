module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Y
public import CFSG.ClassicalInvolution.Q3.Q3CHLayer
public import CFSG.ClassicalInvolution.Q3.Q3AMBadLayer
public import CFSG.ClassicalInvolution.Q3.TL4OddCover

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem mk_ne_one_of_sq {H : Type} [Group H] [Finite H] {x : H} (hx : x * x = 1) (hx1 : x ≠ 1) :
    (QuotientGroup.mk x : H ⧸ classicalInvolutionOddCore H) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
  have hdvd : orderOf (⟨x, h⟩ : classicalInvolutionOddCore H) ∣
      Nat.card (classicalInvolutionOddCore H) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card H))
    (even_iff_two_dvd.mpr hdvd)

theorem isPGroup_zpowers_of_sq_sq {H : Type} [Group H] {e : H} (h : e * e * (e * e) = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers e) := by
  have h4 : e ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, sq, h]
  have hd : orderOf e ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

section Triv

variable {Y : Type} [Group Y]

@[expose] def VertexTriv (Ω : Set (Subgroup Y)) (M : Subgroup Y) (a : Y) : Prop :=
  ∀ m ∈ coreAt a M, ∀ ℓ ∈ linkLayerAt Ω M a,
    m * ℓ * m⁻¹ * ℓ⁻¹ ∈ oddCoreOf (linkLayerAt Ω M a)

noncomputable def conjQuotEquiv [Finite Y] (H : Subgroup Y) (g : Y) :
    ↥H ⧸ classicalInvolutionOddCore ↥H ≃*
      ↥(conjSub g H) ⧸ classicalInvolutionOddCore ↥(conjSub g H) :=
  QuotientGroup.congr _ _ (H.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective) (CFSG.ComponentClassification.OddCore.equiv_invariant _)

variable {Ω : Set (Subgroup Y)} {M : Subgroup Y} {a : Y}

theorem VertexTriv.conj [Finite Y] (hΩ : ConjInvariant Ω) (h : VertexTriv Ω M a) (g : Y) :
    VertexTriv Ω (conjSub g M) (g * a * g⁻¹) := by
  intro m' hm' ℓ' hℓ'
  rw [← conjSub_coreAt_conj, mem_conjSub_iff] at hm'
  rw [← conjSub_linkLayerAt hΩ, mem_conjSub_iff] at hℓ'
  rw [← conjSub_linkLayerAt hΩ, Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
  have h1 := h _ hm' _ hℓ'
  have e : g⁻¹ * (m' * ℓ' * m'⁻¹ * ℓ'⁻¹) * g =
      g⁻¹ * m' * g * (g⁻¹ * ℓ' * g) * (g⁻¹ * m' * g)⁻¹ * (g⁻¹ * ℓ' * g)⁻¹ := by group
  rw [e]
  exact h1

end Triv

section Cover


variable {Y : Type} [Group Y]

variable {Ω : Set (Subgroup Y)} {M : Subgroup Y} {a : Y}

theorem coverSp4_conj [Finite Y] (hΩ : ConjInvariant Ω)
    (h : CoverSp4 (↥(linkLayerAt Ω M a) ⧸ classicalInvolutionOddCore ↥(linkLayerAt Ω M a)))
    (g : Y) : CoverSp4 (↥(linkLayerAt Ω (conjSub g M) (g * a * g⁻¹)) ⧸
      classicalInvolutionOddCore ↥(linkLayerAt Ω (conjSub g M) (g * a * g⁻¹))) := by
  rw [← conjSub_linkLayerAt hΩ]
  exact h.of_mulEquiv (conjQuotEquiv _ g)

end Cover

section Layer


variable {r : ℕ} {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {M : Subgroup Y} {a : Y}

theorem exists_layer3_at_vertex (hΩ : TypeRFam r Ω) (hM : M ∈ Ω) (ha : IsUniqueInvolution M a)
    (htriv : VertexTriv Ω M a)
    (hcov : CoverSp4 (↥(linkLayerAt Ω M a) ⧸ classicalInvolutionOddCore ↥(linkLayerAt Ω M a)))
    {m w : Y} (hm : m ∈ coreAt a M) (hw : w ∈ linkLayerAt Ω M a) (hww : w * w = a)
    (haΛ : a ∈ linkLayerAt Ω M a) (hs2 : m * w * (m * w) = 1) :
    ∃ L : Subgroup Y, Q3NL.IsSectionMember3 (Subgroup.centralizer ({m * w} : Set Y)) L a := by
  classical
  obtain ⟨ψ, hψ, hker, hcen⟩ := hcov
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha.sq) ha.ne_one
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(linkLayerAt Ω M a)) with hπ
  have hac : π ⟨a, haΛ⟩ ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective
      (classicalInvolutionOddCore ↥(linkLayerAt Ω M a)) q
    have hcomm : ℓ * (⟨a, haΛ⟩ : ↥(linkLayerAt Ω M a)) = ⟨a, haΛ⟩ * ℓ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer ℓ.2))
    calc π ℓ * π ⟨a, haΛ⟩ = π (ℓ * ⟨a, haΛ⟩) := by rw [map_mul]
      _ = π (⟨a, haΛ⟩ * ℓ) := by rw [hcomm]
      _ = π ⟨a, haΛ⟩ * π ℓ := by rw [map_mul]
  obtain ⟨f, hf, hfa⟩ := hcen _ hac
  have hfz : ψ f ≠ 1 := by
    rw [hfa]
    exact mk_ne_one_of_sq (Subtype.ext ha.sq) (fun h => ha.ne_one (congrArg Subtype.val h))
  have hub : π ⟨w, hw⟩ * π ⟨w, hw⟩ = ψ f := by
    rw [hfa, ← map_mul]
    congr 1
    exact Subtype.ext hww
  obtain ⟨Lb, hLc, hLn, hubL, hLiso⟩ := Q3CH.exists_layer_bar_comp rfl ψ hψ hker hf hfz hub
  have hmC := coreAt_le_centralizer a M hm
  have hwC := linkLayerAt_le_centralizer hw
  have hsa : m * w * a = a * (m * w) := by
    rw [mul_assoc, Subgroup.mem_centralizer_singleton_iff.mp hwC, ← mul_assoc,
      Subgroup.mem_centralizer_singleton_iff.mp hmC, mul_assoc]
  have hN : ∀ g ∈ Subgroup.centralizer ({a} : Set Y), ∀ y ∈ linkLayerAt Ω M a,
      g * y * g⁻¹ ∈ linkLayerAt Ω M a := fun g hg y hy =>
    conj_mem_linkLayerAt hΩ.hyp.conjInvariant hg
      (conjSub_eq_of_mem_normalizer (hΩ.tight M hM a ha hg)) hy
  have hact : ∀ y ∈ linkLayerAt Ω M a,
      m * w * y * (m * w)⁻¹ * (w * y * w⁻¹)⁻¹ ∈ oddCoreOf (linkLayerAt Ω M a) := by
    intro y hy
    have hwy : w * y * w⁻¹ ∈ linkLayerAt Ω M a := (linkLayerAt Ω M a).mul_mem
      ((linkLayerAt Ω M a).mul_mem hw hy) ((linkLayerAt Ω M a).inv_mem hw)
    have e1 : m * w * y * (m * w)⁻¹ * (w * y * w⁻¹)⁻¹ =
        m * (w * y * w⁻¹) * m⁻¹ * (w * y * w⁻¹)⁻¹ := by group
    rw [e1]
    exact htriv m hm _ hwy
  exact Q3AM.exists_layer_of_action hao linkLayerAt_le_centralizer hN haΛ hw hww hsa hs2 hact
    hLc hLn hubL hLiso

end Layer

end CFSG.ClassicalInvolution.Q3.TL4
