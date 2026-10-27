module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3AutCentralizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3AutTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217U0

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

theorem exists_mulEquiv_map_mk {X : Type*} [Group X] {I : Subgroup X}
    (hI : ∀ i ∈ I, i ∈ Subgroup.center X → i = 1) :
    Nonempty (↥I ≃* ↥(I.map (QuotientGroup.mk' (Subgroup.center X)))) := by
  refine ⟨MulEquiv.ofBijective ((QuotientGroup.mk' (Subgroup.center X)).subgroupMap I) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center X) (x : X) = 1 := congrArg Subtype.val hx
    have h2 : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).1 h1
    exact Subtype.ext (hI _ x.2 h2)
  · exact MonoidHom.subgroupMap_surjective _ _

variable {G : Type} [Group G] [Finite G]

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.centralizes_D {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (ha : Valid217 A c L a) {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgI : g ∈ Subgroup.centralizer (iCore L a : Set G)) :
    ∀ δ ∈ dGroup a c, g * δ = δ * g := by
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  obtain ⟨a', I', ha'G, ha'c, ha3, hI'C, ⟨φ⟩, hI, hD9, hDI, hDcomm, hCeq, hNC⟩ :=
    h.local_frame hθ hAL ha
  have hI'perf : ⁅I', I'⁆ = I' := perfect_of_equiv_alt6 I' φ
  have hZI' := center_eq_bot_of_equiv_alt6 I' φ
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨g, hgL⟩ with hα
  have hαapp : ∀ x : ↥L, ((α x : ↥L) : G) = g * x * g⁻¹ := fun x => rfl
  set ᾱ : MulAut (↥L ⧸ center ↥L) := KFacts.centerDescend ↥L α with hᾱ
  have hq3 : (a' : ↥L ⧸ center ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, show a' ^ 3 = 1 from ha3]; rfl
  have hq1 : (a' : ↥L ⧸ center ↥L) ≠ 1 := fun h1 => ha'c ((QuotientGroup.eq_one_iff _).1 h1)
  have hC1080 := card_centralizer_of_nonCentral e hq3 hq1 hNC
  set IQ : Subgroup (↥L ⧸ center ↥L) := I'.map (QuotientGroup.mk' (center ↥L)) with hIQ
  have hI'Z : ∀ i ∈ I', i ∈ center ↥L → i = 1 := by
    intro i hi hiz
    have : (⟨i, hi⟩ : ↥I') ∈ center ↥I' := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (Subgroup.mem_center_iff.1 hiz z)
    rw [hZI', Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨ψI⟩ := exists_mulEquiv_map_mk hI'Z
  have hIQcard : Nat.card IQ = 360 := by
    rw [← Nat.card_congr ψI.toEquiv, Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card,
      card_alternatingGroup]
    decide
  have hIQC : IQ ≤ centralizer ({(a' : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L)) := by
    rintro _ ⟨i, hi, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show QuotientGroup.mk i * QuotientGroup.mk a' = QuotientGroup.mk a' * QuotientGroup.mk i
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.1 (hI'C hi)
  have hIQperf : ⁅IQ, IQ⁆ = IQ := by
    rw [hIQ, ← Subgroup.map_commutator, hI'perf]
  have hIQA6 : Nonempty (↥IQ ≃* alternatingGroup (Fin 6)) := ⟨ψI.symm.trans φ⟩
  have hᾱI : ∀ y ∈ IQ, ᾱ y = y := by
    rintro _ ⟨i, hi, rfl⟩
    show KFacts.centerDescend ↥L α (QuotientGroup.mk i) = QuotientGroup.mk i
    rw [KFacts.centerDescend_mk]
    congr 1
    apply Subtype.ext
    rw [hαapp]
    have hiG : (i : G) ∈ iCore L a := by
      rw [hI]; exact ⟨i, hi, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hgI (i : G) hiG
    calc g * (i : G) * g⁻¹ = (i : G) * g * g⁻¹ := by rw [← this]
      _ = i := by group
  obtain ⟨n, hn⟩ := aut_eq_conj_of_trivial_on_perfect e hq3 hq1 hC1080 hIQC
    hIQperf hIQcard hIQA6 ᾱ hᾱI
  have hαconj : α = MulAut.conj (a' ^ n) := by
    apply centerDescend_injective hq.1
    rw [← hᾱ, hn, KFacts.centerDescend_conj, QuotientGroup.mk_zpow]
  have hab := h.isElemAbelian_A
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDA : dGroup a c ≤ A :=
    sup_le (Subgroup.zpowers_le.2 ha.mem) (Subgroup.zpowers_le.2 h.c_mem_A)
  intro δ hδ
  have hδL : δ ∈ L := hAL (hDA hδ)
  have h1 := hαapp ⟨δ, hδL⟩
  rw [hαconj, MulAut.conj_apply] at h1
  have h2 : (((a' ^ n * ⟨δ, hδL⟩ * (a' ^ n)⁻¹ : ↥L)) : G) = a ^ n * δ * (a ^ n)⁻¹ := by
    simp [ha'G]
  rw [h2] at h1
  have h3 : a ^ n * δ = δ * a ^ n :=
    (Commute.zpow_left (show Commute a δ from hcomm a ha.mem δ (hDA hδ)) n).eq
  have h4 : a ^ n * δ * (a ^ n)⁻¹ = δ := by
    rw [h3]; group
  rw [h4] at h1
  calc g * δ = (g * δ * g⁻¹) * g := by group
    _ = δ * g := by rw [← h1]

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
