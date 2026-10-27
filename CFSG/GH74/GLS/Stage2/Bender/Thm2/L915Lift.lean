module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Gen

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem exists_lift_quasisimple {O J : Subgroup Y} [O.Normal]
    (hOJ : O ≤ centralizer (J : Set Y)) (hJn : ∀ y : Y, y ∈ normalizer (J : Set Y))
    {Ī : Subgroup (Y ⧸ O)} (hĪ : IsQuasisimple ↥Ī) (hle : Ī ≤ J.map (QuotientGroup.mk' O)) :
    ∃ I : Subgroup Y, IsQuasisimple ↥I ∧ I ≤ J ∧ I.map (QuotientGroup.mk' O) = Ī ∧
      (∀ c : Y, QuotientGroup.mk' O c ∈ normalizer (Ī : Set (Y ⧸ O)) → c ∈ normalizer (I : Set Y)) ∧
      (∀ w : Y, QuotientGroup.mk' O w ∈ centralizer (Ī : Set (Y ⧸ O)) → w ∈ centralizer (I : Set Y)) := by
  set π := QuotientGroup.mk' O with hπ
  set H₀ : Subgroup Y := J ⊓ Ī.comap π with hH₀
  let f : ↥H₀ →* ↥Ī := (π.comp H₀.subtype).codRestrict Ī (fun x => x.2.2)
  have hf : Function.Surjective f := by
    intro ī
    obtain ⟨j, hjJ, hjπ⟩ := hle ī.2
    refine ⟨⟨j, hjJ, ?_⟩, Subtype.ext hjπ⟩
    show π j ∈ Ī
    rw [hjπ]
    exact ī.2
  have hker : f.ker ≤ center ↥H₀ := by
    intro x hx
    have hx1 : π (x : Y) = 1 := by
      have h1 : ((f x : ↥Ī) : Y ⧸ O) = ((1 : ↥Ī) : Y ⧸ O) := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact h1
    have hxO : (x : Y) ∈ O := (QuotientGroup.eq_one_iff _).mp hx1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa [Subgroup.coe_mul] using Subgroup.mem_centralizer_iff.mp (hOJ hxO) g g.2.1
  have hqs : IsQuasisimple ↥(commutator ↥H₀) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hker hĪ
  obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective f hf hker hĪ.1
  have hIeq : (commutator ↥H₀).map H₀.subtype = ⁅H₀, H₀⁆ := Subgroup.map_subtype_commutator H₀
  set I : Subgroup Y := (commutator ↥H₀).map H₀.subtype with hI
  have hIH : I ≤ H₀ := Subgroup.map_subtype_le _
  have hIqs : IsQuasisimple ↥I :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator ↥H₀).equivMapOfInjective H₀.subtype H₀.subtype_injective) hqs
  have hIJ : I ≤ J := hIH.trans inf_le_left
  have hIπ : I.map π = Ī := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hIH hx).2
    · intro ī hī
      obtain ⟨h, hh⟩ := hsurj ⟨ī, hī⟩
      refine ⟨(h : ↥H₀), ⟨h, h.2, rfl⟩, ?_⟩
      have h1 : ((f (h : ↥H₀) : ↥Ī) : Y ⧸ O) = ī := congrArg Subtype.val hh
      exact h1
  refine ⟨I, hIqs, hIJ, hIπ, ?_, ?_⟩
  ·
    intro c hc
    have hH₀n : ∀ c : Y, π c ∈ normalizer (Ī : Set (Y ⧸ O)) → ∀ y ∈ H₀, c * y * c⁻¹ ∈ H₀ := by
      intro c hc y hy
      refine ⟨(mem_normalizer_iff.mp (hJn c) y).mp hy.1, ?_⟩
      show π (c * y * c⁻¹) ∈ Ī
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hc (π y)).mp hy.2
    have hH₀n' : (H₀.map (MulAut.conj c).toMonoidHom) = H₀ := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact hH₀n c hc y hy
      · intro y hy
        have hc' : π c⁻¹ ∈ normalizer (Ī : Set (Y ⧸ O)) := by
          rw [map_inv]
          exact Subgroup.inv_mem _ hc
        refine ⟨c⁻¹ * y * c, ?_, ?_⟩
        · have := hH₀n c⁻¹ hc' y hy
          simpa using this
        · show c * (c⁻¹ * y * c) * c⁻¹ = y
          group
    have hH₀n'' : H₀.map (↑(MulAut.conj c) : Y →* Y) = H₀ := hH₀n'
    rw [hIeq, mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, hH₀n'']
  ·
    intro w hw
    have hcomm : ⁅I, zpowers w⁆ ≤ centralizer (I : Set Y) := by
      refine Subgroup.commutator_le.mpr fun i hi g hg => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hiJ : i ∈ J := hIJ hi
      have hJc : ⁅i, w ^ k⁆ ∈ J := by
        rw [commutatorElement_def]
        have h1 : (w ^ k) * i⁻¹ * (w ^ k)⁻¹ ∈ J :=
          (mem_normalizer_iff.mp (hJn (w ^ k)) i⁻¹).mp (J.inv_mem hiJ)
        have he : i * w ^ k * i⁻¹ * (w ^ k)⁻¹ = i * ((w ^ k) * i⁻¹ * (w ^ k)⁻¹) := by group
        rw [he]
        exact J.mul_mem hiJ h1
      have hπi : π i ∈ Ī := hIπ ▸ ⟨i, hi, rfl⟩
      have hπ : π ⁅i, w ^ k⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, map_zpow]
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.zpow_mem _ hw k) (π i) hπi
      have hmem : ⁅i, w ^ k⁆ ∈ O := (QuotientGroup.eq_one_iff _).mp hπ
      exact Subgroup.centralizer_le hIJ (hOJ hmem)
    exact le_centralizer_of_commutator_le_centralizer hIqs.1 hcomm (Subgroup.mem_zpowers w)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
