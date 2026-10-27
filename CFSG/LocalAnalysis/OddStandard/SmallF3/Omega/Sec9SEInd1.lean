module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped commutatorElement

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

private lemma commutatorElement_mul_center_left {H : Type} [Group H] {a z : H}
    (hz : z ∈ Subgroup.center H) (b : H) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅z, b⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz b).symm
  rw [h1]
  group

private lemma commutatorElement_mul_center_right {H : Type} [Group H] {a w : H}
    (hw : w ∈ Subgroup.center H) (b : H) : ⁅a, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅a, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw a)
  rw [h1]
  group

private lemma commutatorElement_mul_center {H : Type} [Group H] {a b z w : H}
    (hz : z ∈ Subgroup.center H) (hw : w ∈ Subgroup.center H) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_center_left hz (b * w), commutatorElement_mul_center_right hw b]

private lemma conj_eq_mul_center_of_inducesViaP_one {L : Subgroup G} {hQ : Q.Nondegenerate}
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G}
    (h : InducesViaP L (Subgroup.center ↥L) hQ e s 1) (l : ↥L) :
    ∃ z ∈ Subgroup.center ↥L,
      (⟨s * (l : G) * s⁻¹, (Subgroup.mem_normalizer_iff.mp h.1 (l : G)).mp l.2⟩ : ↥L) =
        l * z := by
  let l' : ↥L :=
    ⟨s * (l : G) * s⁻¹, (Subgroup.mem_normalizer_iff.mp h.1 (l : G)).mp l.2⟩
  have heq : e (QuotientGroup.mk l') = e (QuotientGroup.mk l) := by
    apply Subtype.ext
    have h1 := h.2 l l' rfl
    rw [map_one, MulAut.one_apply] at h1
    exact h1
  have hmk : QuotientGroup.mk l' = QuotientGroup.mk l := e.injective heq
  have hmem : l'⁻¹ * l ∈ Subgroup.center ↥L := QuotientGroup.eq.mp hmk
  refine ⟨(l'⁻¹ * l)⁻¹, (Subgroup.center ↥L).inv_mem hmem, ?_⟩
  show l' = l * (l'⁻¹ * l)⁻¹
  group

private lemma conj_commutatorElement_eq_of_inducesViaP_one {L : Subgroup G}
    {hQ : Q.Nondegenerate} {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G}
    (h : InducesViaP L (Subgroup.center ↥L) hQ e s 1) (a b : ↥L) :
    s * ((⁅a, b⁆ : ↥L) : G) * s⁻¹ = ((⁅a, b⁆ : ↥L) : G) := by
  obtain ⟨za, hza, ha⟩ := conj_eq_mul_center_of_inducesViaP_one (h := h) a
  obtain ⟨zb, hzb, hb⟩ := conj_eq_mul_center_of_inducesViaP_one (h := h) b
  have hza' : s * (a : G) * s⁻¹ = ((a * za : ↥L) : G) := congrArg Subtype.val ha
  have hzb' : s * (b : G) * s⁻¹ = ((b * zb : ↥L) : G) := congrArg Subtype.val hb
  have hcz : ⁅((a * za : ↥L) : G), ((b * zb : ↥L) : G)⁆ = ((⁅a, b⁆ : ↥L) : G) :=
    congrArg Subtype.val (commutatorElement_mul_center (a := a) (b := b) hza hzb)
  calc s * ((⁅a, b⁆ : ↥L) : G) * s⁻¹
      = ⁅s * (a : G) * s⁻¹, s * (b : G) * s⁻¹⁆ :=
        conjugate_commutatorElement (g₁ := (a : G)) (g₂ := (b : G)) (g₃ := s)
    _ = ((⁅a, b⁆ : ↥L) : G) := by rw [hza', hzb']; exact hcz

theorem inducesViaP_mul {L : Subgroup G} {hQ : Q.Nondegenerate}
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s s' : G} {x x' : ProjSim Q}
    (h : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (h' : InducesViaP L (Subgroup.center ↥L) hQ e s' x') :
    InducesViaP L (Subgroup.center ↥L) hQ e (s * s') (x * x') := by
  refine ⟨mul_mem h.1 h'.1, ?_⟩
  intro l l'' hl''
  have hmem : s' * (l : G) * s'⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp h'.1 (l : G)).mp l.2
  let l' : ↥L := ⟨s' * (l : G) * s'⁻¹, hmem⟩
  have hl'val : (l' : G) = s' * (l : G) * s'⁻¹ := rfl
  have hstep : (l'' : G) = s * (l' : G) * s⁻¹ := by
    rw [hl'val, hl'']
    group
  calc ((e (QuotientGroup.mk l'') : omegaProj hQ) : ProjOrth Q)
      = projSimAct Q x ((e (QuotientGroup.mk l') : omegaProj hQ) : ProjOrth Q) :=
        h.2 l' l'' hstep
    _ = projSimAct Q x (projSimAct Q x'
          ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q)) := by
        rw [h'.2 l l' rfl]
    _ = projSimAct Q (x * x') ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) := by
        rw [← MulAut.mul_apply, ← map_mul]

theorem inducesViaP_one_of_centralizer {L : Subgroup G} {hQ : Q.Nondegenerate}
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {c : G}
    (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    InducesViaP L (Subgroup.center ↥L) hQ e c 1 := by
  refine ⟨Subgroup.centralizer_le_normalizer (L : Set G) hc, ?_⟩
  intro l l' hl
  have hcomm : (l : G) * c = c * (l : G) :=
    Subgroup.mem_centralizer_iff.mp hc (l : G) l.2
  have hval : (l' : G) = (l : G) := by
    rw [hl, ← hcomm]
    group
  have hsub : l' = l := Subtype.ext hval
  rw [hsub, map_one, MulAut.one_apply]

theorem inducesViaP_of_mem {L : Subgroup G} {hQ : Q.Nondegenerate}
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L) :
    InducesViaP L (Subgroup.center ↥L) hQ e (l : G)
      (projOrthToProjSim Q ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q)) := by
  refine ⟨Subgroup.le_normalizer l.2, ?_⟩
  intro l₁ l₁' hl₁
  have hl₁eq : l₁' = (l : ↥L) * l₁ * (l : ↥L)⁻¹ := by
    apply Subtype.ext
    rw [hl₁]
    rfl
  have hkey : (e (QuotientGroup.mk l₁') : omegaProj hQ) =
      e (QuotientGroup.mk l) * e (QuotientGroup.mk l₁) * (e (QuotientGroup.mk l))⁻¹ := by
    rw [hl₁eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      map_mul, map_mul, map_inv]
  calc ((e (QuotientGroup.mk l₁') : omegaProj hQ) : ProjOrth Q)
      = ((e (QuotientGroup.mk l) * e (QuotientGroup.mk l₁) *
          (e (QuotientGroup.mk l))⁻¹ : omegaProj hQ) : ProjOrth Q) := by rw [hkey]
    _ = ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) *
        ((e (QuotientGroup.mk l₁) : omegaProj hQ) : ProjOrth Q) *
        ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q)⁻¹ := rfl
    _ = projSimAct Q
          (projOrthToProjSim Q ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q))
          ((e (QuotientGroup.mk l₁) : omegaProj hQ) : ProjOrth Q) := by
        rw [projSimAct_projOrthToProjSim]

theorem mem_centralizer_of_inducesViaP_one {L : Subgroup G} {hQ : Q.Nondegenerate}
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} (hL : commutator ↥L = ⊤)
    (h : InducesViaP L (Subgroup.center ↥L) hQ e s 1) :
    s ∈ Subgroup.centralizer (L : Set G) := by
  let K : Subgroup ↥L := (Subgroup.centralizer ({s} : Set G)).comap L.subtype
  have hK : commutator ↥L ≤ K := by
    change ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ K
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    change ((⁅a, b⁆ : ↥L) : G) ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have hc := conj_commutatorElement_eq_of_inducesViaP_one h a b
    have := congrArg (· * s) hc
    simpa [mul_assoc] using this
  have htop : (⊤ : Subgroup ↥L) ≤ K := by
    rw [← hL]
    exact hK
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  let x' : ↥L := ⟨x, hx⟩
  have hxK : x' ∈ K := htop trivial
  change ((x' : G) ∈ Subgroup.centralizer ({s} : Set G)) at hxK
  rw [Subgroup.mem_centralizer_iff] at hxK
  exact (hxK s (by simp)).symm

end CFSG.OddStandard.SmallF3.Omega
