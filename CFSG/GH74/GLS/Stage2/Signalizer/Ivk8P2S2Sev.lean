module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Comp
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Two
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem caseA_unique_involution (h172 : Lemma17_2) {G : Type} [Group G] [Finite G] {z : G}
    {k : Kind} {S M : Subgroup G} (h : Fail17 G z k S M) (hMC : M = Cen z)
    (hD1 : pPrimeCoreOf 2 M ≠ ⊥) {J : Subgroup G} (hJ : IsPCompIn 2 M J)
    (hJq : ¬ pPrimeCoreOf 2 J ≤ centralizer (J : Set G)) {u : G} (hu : orderOf u = 2)
    (huD : u ∈ centralizer (pPrimeCoreOf 2 M : Set G)) : u = z := by
  have hz2 : orderOf z = 2 := h.ctx.ctx.central.1
  have hcoat : IsCoatom M := h.ctx.mem.1
  have hsimp : IsSimpleGroup G := (isKProperSimple_iff.1 h.ctx.ctx.std.kps).1
  have hMmem : ∀ y : G, y ∈ M ↔ y * z = z * y := fun y => by
    rw [hMC]; exact Subgroup.mem_centralizer_singleton_iff
  have hDM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hDn : ∀ m ∈ M, ∀ d ∈ pPrimeCoreOf 2 M, m * d * m⁻¹ ∈ pPrimeCoreOf 2 M :=
    fun m hm d hd => pPrimeCoreOf_norm hm hd
  have hNorm : normalizer (pPrimeCoreOf 2 M : Set G) = M :=
    normalizer_eq_of_coatom hcoat hD1 hDM hDn
  have hCD : ∀ w ∈ centralizer (pPrimeCoreOf 2 M : Set G), w ∈ M := fun w hw =>
    hNorm ▸ Subgroup.centralizer_le_normalizer _ hw
  obtain ⟨L, hLJ, hLpc⟩ : ∃ L : Subgroup ↥M, L.map M.subtype = J ∧ IsPComponent 2 L :=
    ⟨J.subgroupOf M, Subgroup.map_subgroupOf_eq_of_le hJ.1, hJ.2⟩
  subst hLJ
  have hnq : ¬ pPrimeCoreOf 2 L ≤ centralizer (L : Set ↥M) := by
    intro hle
    apply hJq
    rw [pPrimeCoreOf_map_subtype]
    rintro _ ⟨x', hx', rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y', hy', rfl⟩
    exact congrArg Subtype.val ((mem_centralizer_iff.mp (hle hx')) y' hy')
  have hfwd : ∀ w ∈ centralizer (pPrimeCoreOf 2 M : Set G),
      (∀ x ∈ L.map M.subtype, w * x * w⁻¹ ∈ L.map M.subtype) ∧
      (∀ x ∈ pPrimeCoreOf 2 (L.map M.subtype), w * x * w⁻¹ ∈ pPrimeCoreOf 2 (L.map M.subtype)) ∧
      (∀ x ∈ L.map M.subtype, x * w * x⁻¹ * w⁻¹ ∈ pPrimeCoreOf 2 (L.map M.subtype)) := by
    intro w hw
    have hwM := hCD w hw
    have hv : (⟨w, hwM⟩ : ↥M) ∈ centralizer (pPrimeCore 2 ↥M : Set ↥M) := by
      rw [mem_centralizer_iff]
      intro o ho
      apply Subtype.ext
      exact mem_centralizer_iff.mp hw (o : G) ⟨o, ho, rfl⟩
    obtain ⟨hvN, hcom, hnorm⟩ := keyA hLpc hnq hv
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x', hx', rfl⟩
      exact ⟨⟨w, hwM⟩ * x' * ⟨w, hwM⟩⁻¹, (mem_normalizer_iff.mp hvN x').mp hx', rfl⟩
    · intro x hx
      rw [pPrimeCoreOf_map_subtype] at hx ⊢
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨⟨w, hwM⟩ * x' * ⟨w, hwM⟩⁻¹, hnorm x' hx', rfl⟩
    · rintro _ ⟨x', hx', rfl⟩
      rw [pPrimeCoreOf_map_subtype]
      exact ⟨x' * ⟨w, hwM⟩ * x'⁻¹ * ⟨w, hwM⟩⁻¹, hcom x' hx', rfl⟩
  have hY : ∀ w ∈ centralizer (pPrimeCoreOf 2 M : Set G),
      w ∈ M ⊓ centralizerSection (L.map M.subtype) (pPrimeCoreOf 2 (L.map M.subtype)) := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hfwd w hw
    obtain ⟨h1', h2', -⟩ := hfwd w⁻¹ ((centralizer (pPrimeCoreOf 2 M : Set G)).inv_mem hw)
    refine Subgroup.mem_inf.2 ⟨hCD w hw, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨h1 x, fun hx => ?_⟩
      have := h1' _ hx
      simpa [mul_assoc] using this
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨h2 x, fun hx => ?_⟩
      have := h2' _ hx
      simpa [mul_assoc] using this
    · exact h3
  have hzD : z ∈ centralizer (pPrimeCoreOf 2 M : Set G) := by
    rw [mem_centralizer_iff]
    intro d hd
    exact (hMmem d).1 (hDM hd)
  have hOdd : OddCover z M := fun m hm =>
    ⟨m, by rw [← hMC]; exact hm, 1, one_mem _, (mul_one m).symm⟩
  have hrank := h172 G z k S M h hOdd (L.map M.subtype) hJ
  by_contra hne
  have hzu : z * u = u * z := ((hMmem u).1 (hCD u huD)).symm
  have h2 := two_le_pRank_of_two_involutions (K := M ⊓ centralizerSection (L.map M.subtype)
    (pPrimeCoreOf 2 (L.map M.subtype))) hz2 hu (Ne.symm hne) hzu (hY z hzD) (hY u huD)
  omega

theorem lemma17_7_of (h172 : Lemma17_2) (h171 : Prop17_1) (hB : Lemma17_7B) : Lemma17_7 := by
  intro G _ _ z k S M h hL u hu huD
  obtain ⟨hMC, hD1⟩ := h171 G z k S M h.ctx h.fail
  by_cases hA : ∃ J : Subgroup G, IsPCompIn 2 M J ∧ ¬ pPrimeCoreOf 2 J ≤ centralizer (J : Set G)
  · obtain ⟨J, hJ, hJq⟩ := hA
    exact caseA_unique_involution h172 h hMC hD1 hJ hJq hu huD
  · have hA' : ∀ J : Subgroup G, IsPCompIn 2 M J → pPrimeCoreOf 2 J ≤ centralizer (J : Set G) :=
      fun J hJ => by
        by_contra hcon
        exact hA ⟨J, hJ, hcon⟩
    exact hB G z k S M h hL hA' u hu huD

theorem prop17_8_of_leaves (h172 : Lemma17_2) (h171 : Prop17_1) (hB : Lemma17_7B)
    (hAB : IG_11_7) : Prop17_8 :=
  prop17_8_of (lemma17_7_of h172 h171 hB) h171 hAB

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
