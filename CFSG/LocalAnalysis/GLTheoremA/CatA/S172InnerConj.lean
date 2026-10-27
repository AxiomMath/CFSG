module

public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem isQuasisimple_of_open {Q : Type*} [Group Q]
    (h : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsimple := h.2
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcon _ _
  have htop : (⊤ : Subgroup Q) ≤ Subgroup.center Q := h.1 ▸ hle
  obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : Q ⧸ Subgroup.center Q)).mp
    hsimple.toNontrivial
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ha ((QuotientGroup.eq_one_iff x).mpr (htop (Subgroup.mem_top x)))

private theorem commutator_mul_central {G : Type*} [Group G] {a b z w : G}
    (haz : Commute a z) (hbz : Commute b z) (haw : Commute a w) (hbw : Commute b w)
    (hzw : Commute z w) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [haz.eq, hbw.eq]
  have hza : Commute z a := haz.symm
  have hwb : Commute w b := hbw.symm
  have hwa : Commute w a := haw.symm
  have hzb : Commute z b := hbz.symm
  have hzc : Commute z (a * b * a⁻¹ * b⁻¹) :=
    ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  have hwc : Commute w (a * b * a⁻¹ * b⁻¹) :=
    ((hwa.mul_right hwb).mul_right hwa.inv_right).mul_right hwb.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹
      = z * (a * w) * b * a⁻¹ * z⁻¹ * b⁻¹ * w⁻¹ := by group
    _ = z * (w * a) * b * a⁻¹ * z⁻¹ * b⁻¹ * w⁻¹ := by rw [← hwa.eq]
    _ = z * w * (a * b * a⁻¹) * (z⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = z * w * (a * b * a⁻¹) * (b⁻¹ * z⁻¹) * w⁻¹ := by rw [(hzb.inv_inv).eq]
    _ = (z * w) * (a * b * a⁻¹ * b⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = w * (z * (a * b * a⁻¹ * b⁻¹) * z⁻¹) * w⁻¹ := by rw [hzw.eq]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hzc.eq, mul_inv_cancel_right, hwc.eq, mul_inv_cancel_right]

private theorem centralizes_of_central_conj {H : Type} [Group H] {L : Subgroup H}
    (hL : ⁅L, L⁆ = L) (g : H)
    (hg : ∀ l ∈ L, ∃ z ∈ L, (∀ m ∈ L, m * z = z * m) ∧ g * l * g⁻¹ = l * z) :
    ∀ l ∈ L, g * l = l * g := by
  have hle : L ≤ Subgroup.centralizer ({g} : Set H) := by
    calc L = ⁅L, L⁆ := hL.symm
      _ ≤ Subgroup.centralizer ({g} : Set H) := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        obtain ⟨za, hza, hzac, hza'⟩ := hg a ha
        obtain ⟨zb, hzb, hzbc, hzb'⟩ := hg b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hconj : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
          have h1 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
          rw [h1, hza', hzb']
          exact commutator_mul_central (hzac a ha) (hzac b hb) (hzbc a ha) (hzbc b hb)
            (hzac zb hzb).symm
        calc ⁅a, b⁆ * g = g * ⁅a, b⁆ * g⁻¹ * g := by rw [hconj]
          _ = g * ⁅a, b⁆ := by group
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hl)).symm

private theorem inner_conj_central {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {R : Type} [Group R] (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) {b : Ω} {s : ↥S} {r : R}
    (hs : θ (QuotientGroup.mk s) = r)
    (hφ : CFSG.Assembly.LargeEvenInduces θ
      (fun l l' => (l' : Ω) = b⁻¹ * (l : Ω) * b) (MulAut.conj r))
    (hbinvN : b⁻¹ ∈ Subgroup.normalizer (S : Set Ω)) :
    ∀ l : ↥S, ∃ z : ↥S, z ∈ Subgroup.center ↥S ∧
      b⁻¹ * (l : Ω) * b = (s : Ω) * (l : Ω) * (s : Ω)⁻¹ * (z : Ω) := by
  intro l
  have hmem : (b⁻¹ * (l : Ω) * b) ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp hbinvN) (l : Ω)
    rw [inv_inv] at this
    exact this.mp l.property
  let l' : ↥S := ⟨b⁻¹ * (l : Ω) * b, hmem⟩
  let sls : ↥S := s * l * s⁻¹
  have hkey : (QuotientGroup.mk l' : ↥S ⧸ Subgroup.center ↥S) =
      QuotientGroup.mk sls := by
    apply θ.injective
    rw [← hφ l l' rfl, ← hs, MulAut.conj_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  have hzcenter : sls⁻¹ * l' ∈ Subgroup.center ↥S := by
    have h1 : (l')⁻¹ * sls ∈ Subgroup.center ↥S := QuotientGroup.eq.mp hkey
    simpa using Subgroup.inv_mem _ h1
  refine ⟨sls⁻¹ * l', hzcenter, ?_⟩
  have hzmul : (sls : Ω) * ((sls⁻¹ * l' : ↥S) : Ω) = (l' : Ω) := by
    show ((sls * (sls⁻¹ * l') : ↥S) : Ω) = ((l' : ↥S) : Ω)
    congr 1
    group
  change b⁻¹ * (l : Ω) * b = (sls : Ω) * ((sls⁻¹ * l' : ↥S) : Ω)
  rw [hzmul]

private theorem mem_sup_centralizer_of_inner_conj {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {b : Ω} {s : ↥S} (hperf : commutator ↥S = ⊤)
    (hlocal : ∀ l : ↥S, ∃ z : ↥S, z ∈ Subgroup.center ↥S ∧
      b⁻¹ * (l : Ω) * b = (s : Ω) * (l : Ω) * (s : Ω)⁻¹ * (z : Ω)) :
    b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  let w : Ω := b * (s : Ω)
  have hL : ⁅(S : Subgroup Ω), S⁆ = S := by
    haveI : Group.IsPerfect ↥S := ⟨hperf⟩
    exact Subgroup.commutator_eq_self
  have hg : ∀ l ∈ S, ∃ z ∈ S, (∀ m ∈ S, m * z = z * m) ∧ w⁻¹ * l * w = l * z := by
    intro l hl
    obtain ⟨z, hzcenter, hzrel⟩ := hlocal ⟨l, hl⟩
    refine ⟨(z : Ω), z.property, ?_, ?_⟩
    · intro m hm
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter ⟨m, hm⟩)
    · have hzc : (s : Ω)⁻¹ * (z : Ω) * (s : Ω) = (z : Ω) := by
        have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter s)
        change (s : Ω) * (z : Ω) = (z : Ω) * (s : Ω) at hcomm
        calc (s : Ω)⁻¹ * (z : Ω) * (s : Ω) = (s : Ω)⁻¹ * ((z : Ω) * (s : Ω)) := by group
          _ = (s : Ω)⁻¹ * ((s : Ω) * (z : Ω)) := by rw [hcomm]
          _ = (z : Ω) := by group
      calc w⁻¹ * l * w = (s : Ω)⁻¹ * (b⁻¹ * l * b) * (s : Ω) := by
              rw [show w = b * (s : Ω) from rfl]; group
        _ = (s : Ω)⁻¹ * ((s : Ω) * (l : Ω) * (s : Ω)⁻¹ * (z : Ω)) * (s : Ω) := by rw [hzrel]
        _ = (l : Ω) * (z : Ω) := by
              calc (s : Ω)⁻¹ * ((s : Ω) * (l : Ω) * (s : Ω)⁻¹ * (z : Ω)) * (s : Ω)
                  = (s : Ω)⁻¹ * (s : Ω) * (l : Ω) * ((s : Ω)⁻¹ * (z : Ω) * (s : Ω)) := by group
                _ = (l : Ω) * (z : Ω) := by rw [hzc]; group
  have hcomm := centralizes_of_central_conj hL w⁻¹ (by simpa [inv_inv] using hg)
  have hwC : w ∈ Subgroup.centralizer (S : Set Ω) := by
    have hinv : w⁻¹ ∈ Subgroup.centralizer (S : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (hcomm l hl).symm
    simpa using Subgroup.inv_mem _ hinv
  have hbw : b = w * (s : Ω)⁻¹ := by
    rw [show w = b * (s : Ω) from rfl]
    group
  rw [hbw, sup_comm]
  exact Subgroup.mul_mem_sup hwC (Subgroup.inv_mem S s.property)

theorem mem_sup_centralizer_of_largeEvenInduces_conj {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {R : Type} [Group R] (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) {r : R} {b : Ω}
    (hperf : commutator ↥S = ⊤) (hbN : b ∈ Subgroup.normalizer (S : Set Ω))
    (hφ : CFSG.Assembly.LargeEvenInduces θ
      (fun l l' => (l' : Ω) = b⁻¹ * (l : Ω) * b) (MulAut.conj r)) :
    b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  obtain ⟨s, hs⟩ : ∃ s : ↥S, θ (QuotientGroup.mk s) = r := by
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨s, hq⟩
  have hbinvN : b⁻¹ ∈ Subgroup.normalizer (S : Set Ω) :=
    (Subgroup.normalizer (S : Set Ω)).inv_mem hbN
  exact mem_sup_centralizer_of_inner_conj hperf (inner_conj_central θ hs hφ hbinvN)

theorem innerDiagMarking_rawDatum_of_hasLabel (hRig : CFSG.StandardType.GGLabelRigidInput)
    {Ω : Type} [Group Ω] {S B : Subgroup Ω} {lab₀ : CFSG.Assembly.LargeEvenLabel}
    (hqs : CFSG.IsQuasisimple ↥S)
    (hHasTarget : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥S (· = lab₀))
    (hiso : ∀ lab, CFSG.StandardType.GGLabelIso lab lab₀ → lab = lab₀)
    (hid : InnerDiagMarking B S) :
    commutator ↥S = ⊤ ∧
      CFSG.Assembly.LargeEvenRawDatum lab₀
        (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥S ⧸ Subgroup.center ↥S ≃* R,
            B ≤ Subgroup.normalizer (S : Set Ω) ∧
            ∀ b ∈ B, ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ
              (fun l l' => (l' : Ω) = b⁻¹ * (l : Ω) * b) φ) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hid
  obtain ⟨labT, hlabT, hHasLabTarget, R0, hR0, I0, F0, θ0, hPeq⟩ :=
    CFSG.StandardType.largeEvenMarking_exists_hasLabel hHasTarget
  have hlabT₀ : CFSG.Assembly.LargeEvenInLambda2 lab₀ := hPeq ▸ hlabT
  have hHasLabTarget₀ : CFSG.StandardType.GGHasLabel lab₀
      (↥S ⧸ Subgroup.center ↥S) := hPeq ▸ hHasLabTarget
  have hHasLab : CFSG.StandardType.GGHasLabel lab (↥S ⧸ Subgroup.center ↥S) := by
    unfold CFSG.StandardType.GGHasLabel
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hIso : CFSG.StandardType.GGLabelIso lab lab₀ :=
    hRig lab lab₀ (↥S ⧸ Subgroup.center ↥S) hlab hlabT₀ hHasLab hHasLabTarget₀
  have hlab_eq : lab = lab₀ := hiso lab hIso
  subst hlab_eq
  exact ⟨hperf, hraw⟩

end CFSG.LocalAnalysis.GLTheoremA.S172X

end