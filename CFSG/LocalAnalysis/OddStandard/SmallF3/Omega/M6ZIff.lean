module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZQ8
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZQ6
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FivePocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem m6z_mem_omegaGroup_of_invType (hQ : Q.Nondegenerate) {u : OGroup Q}
    (hu : u * u = 1) (ht : invType u = (4, 1)) : u ∈ omegaGroup hQ := by
  refine (involution_mem_omegaGroup_iff hQ hu).mpr ⟨?_, ?_⟩
  · rw [show invDim u = 4 from congrArg Prod.fst ht]; decide
  · rw [show invDim u = 4 from congrArg Prod.fst ht,
        show invSign u = 1 from congrArg Prod.snd ht]; decide

private theorem m6z_card_eq_mul_of_card_fiber {α β : Type*} [Finite α] [Finite β] (F : α → β)
    (k : ℕ) (h : ∀ b, Nat.card {a // F a = b} = k) : Nat.card α = k * Nat.card β := by
  have := Fintype.ofFinite β
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma,
    Finset.sum_congr rfl fun b _ => h b, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_comm, Nat.card_eq_fintype_card]

private def m6zOmegaOfInvType (hQ : Q.Nondegenerate)
    (u : {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)}) : omegaGroup hQ :=
  ⟨u.1, m6z_mem_omegaGroup_of_invType hQ u.2.1 u.2.2⟩

private noncomputable def m6zPhi (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (u : {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)}) :
    {x : omegaProj hQ // IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) x} :=
  ⟨omegaToProj hQ (m6zOmegaOfInvType hQ u),
    m6z_isI4PlusIn_omegaProj_of_invType (y := m6zOmegaOfInvType hQ u) hQ u.2.1 u.2.2 h5⟩

theorem m6z_card_pocketed_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card {x : X // IsI4PlusIn (⊤ : Subgroup X) x} =
      Nat.card {y : Y // IsI4PlusIn (⊤ : Subgroup Y) y} :=
  Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ⟨
    fun hx => isI4PlusIn_top_map_mulEquiv e hx,
    fun hx => by
      have h := isI4PlusIn_top_map_mulEquiv e.symm hx
      change IsI4PlusIn (⊤ : Subgroup X) (e.symm (e x)) at h
      rwa [MulEquiv.symm_apply_apply] at h⟩)

theorem m6z_isI4PlusIn_omega_iff (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V ≤ 8)
    (hπ : Module.finrank (ZMod 3) V = 8 → piOrth Q ∉ omegaGroup hQ) (g : omegaGroup hQ) :
    IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) g ↔
      (g : OGroup Q) * g = 1 ∧ invType (g : OGroup Q) = (4, 1) := by
  constructor
  · intro hg
    exact m6z_invType_of_pocket_omega hQ hdim (fun h8 h => hπ h8 (h ▸ g.2)) hg
  · rintro ⟨hg, htype⟩
    exact asc82PocketCover_holds V Q hQ g (Subtype.ext hg) htype

theorem m6z_card_pocketed_omega (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V ≤ 8)
    (hπ : Module.finrank (ZMod 3) V = 8 → piOrth Q ∉ omegaGroup hQ) :
    Nat.card {g : omegaGroup hQ // IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) g} =
      Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} := by
  let f : {g : omegaGroup hQ // IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) g} →
      {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} :=
    fun g => ⟨(g : OGroup Q), (m6z_isI4PlusIn_omega_iff hQ hdim hπ g).mp g.2⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨g₁, _⟩ ⟨g₂, _⟩ h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h1)
  · rintro ⟨u, hu1, htu⟩
    have hmem : u ∈ omegaGroup hQ := m6z_mem_omegaGroup_of_invType hQ hu1 htu
    refine ⟨⟨⟨u, hmem⟩, ?_⟩, Subtype.ext rfl⟩
    exact (m6z_isI4PlusIn_omega_iff hQ hdim hπ ⟨u, hmem⟩).mpr ⟨hu1, htu⟩

theorem m6z_card_pocketed_omegaProj_of_not_mem (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V ≤ 8) (hπ : piOrth Q ∉ omegaGroup hQ) :
    Nat.card {x : omegaProj hQ // IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) x} =
      Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} := by
  rw [← m6z_card_pocketed_omega hQ hdim (fun _ => hπ)]
  exact (m6z_card_pocketed_of_mulEquiv (omegaProjEquiv hQ hπ)).symm

theorem m6z_card_pocketed_omegaProj_six (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Nat.card {x : omegaProj hQ // IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) x} =
      Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} := by
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  let f := m6zPhi (V := V) (Q := Q) hQ h5
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro u u' h
    have hproj : omegaToProj hQ (m6zOmegaOfInvType hQ u) =
        omegaToProj hQ (m6zOmegaOfInvType hQ u') := congrArg Subtype.val h
    rcases omegaToProj_eq_iff hQ hproj with h1 | h1
    · exact Subtype.ext h1.symm
    · exfalso
      have h1' : u'.1 = piOrth Q * u.1 := h1
      have h3 := invType_piOrth_mul_of_even_minus hQ u.2.1 (by rw [hdim]; decide) hs
      rw [hdim, show invDim u.1 = 4 from congrArg Prod.fst u.2.2,
        show invSign u.1 = 1 from congrArg Prod.snd u.2.2] at h3
      have h2 : invType (piOrth Q * u.1) = (4, 1) := by
        rw [← h1']; exact u'.2.2
      rw [h3] at h2
      have hfst : 6 - 4 = 4 := congrArg Prod.fst h2
      omega
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy1, hy2, hyx⟩ := m6z_exists_lift_of_pocket_omegaProj_six hQ hdim hs hx
    refine ⟨⟨(y : OGroup Q), hy1, hy2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change toProj Q (y : OGroup Q) = (x : ProjOrth Q)
    rw [← coe_omegaToProj hQ y, hyx]

theorem m6z_card_pocketed_omegaProj_eight (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = 1) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} =
      2 * Nat.card {x : omegaProj hQ // IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) x} := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  refine m6z_card_eq_mul_of_card_fiber
    (m6zPhi (V := V) (Q := Q) hQ h5) 2 ?_
  intro x
  obtain ⟨y, hy1, hy2, hyx⟩ := m6z_exists_lift_of_pocket_omegaProj_eight hQ hdim x.2
  have hpi8 : invDim (piOrth Q) = 8 := by
    rw [show invDim (piOrth Q) = Module.finrank (ZMod 3) V from
      congrArg Prod.fst (invType_piOrth hQ), hdim]
  have hpi_ne_one : piOrth Q ≠ 1 := by
    intro h
    have h0 : invDim (piOrth Q) = 0 := by
      rw [h]; exact congrArg Prod.fst (invType_one (Q := Q))
    omega
  have hpi1 : (piOrth Q * (y : OGroup Q)) * (piOrth Q * (y : OGroup Q)) = 1 :=
    piOrth_mul_mul_self hy1
  have hpi2 : invType (piOrth Q * (y : OGroup Q)) = (4, 1) := by
    have h := invType_piOrth_mul_of_even_plus hQ hy1 (by rw [hdim]; decide) hs
    rw [hdim, show invDim (y : OGroup Q) = 4 from congrArg Prod.fst hy2,
      show invSign (y : OGroup Q) = 1 from congrArg Prod.snd hy2] at h
    rw [show (8 - 4, (-1 : ℤˣ) ^ 4 * 1) = (4, 1) from by decide] at h
    exact h
  let yT : {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} := ⟨(y : OGroup Q), hy1, hy2⟩
  let pT : {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} :=
    ⟨piOrth Q * (y : OGroup Q), hpi1, hpi2⟩
  have hΦy : m6zPhi (V := V) (Q := Q) hQ h5 yT = x := by
    apply Subtype.ext
    apply Subtype.ext
    change toProj Q (y : OGroup Q) = (x : ProjOrth Q)
    rw [← coe_omegaToProj hQ y, hyx]
  have hΦp : m6zPhi (V := V) (Q := Q) hQ h5 pT = x := by
    apply Subtype.ext
    apply Subtype.ext
    change toProj Q (piOrth Q * (y : OGroup Q)) = (x : ProjOrth Q)
    rw [map_mul, toProj_piOrth, one_mul, ← coe_omegaToProj hQ y, hyx]
  let F := {u : {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} //
    m6zPhi (V := V) (Q := Q) hQ h5 u = x}
  let xF : F := ⟨yT, hΦy⟩
  let pF : F := ⟨pT, hΦp⟩
  have hyT_ne : yT ≠ pT := by
    intro h
    have h1 : (y : OGroup Q) = piOrth Q * (y : OGroup Q) := congrArg Subtype.val h
    have h2 : (1 : OGroup Q) = piOrth Q := by
      have := congrArg (fun z : OGroup Q => z * (y : OGroup Q)⁻¹) h1
      simpa [mul_assoc] using this
    exact hpi_ne_one h2.symm
  have hne : pF ≠ xF := fun h => hyT_ne (congrArg Subtype.val h).symm
  have huniq : ∀ z : F, z ≠ xF → z = pF := by
    intro z hz
    have hz' : m6zPhi (V := V) (Q := Q) hQ h5 z.1 =
        m6zPhi (V := V) (Q := Q) hQ h5 yT := by rw [z.2, ← hΦy]
    have hproj : omegaToProj hQ (m6zOmegaOfInvType hQ z.1) =
        omegaToProj hQ (m6zOmegaOfInvType hQ yT) := congrArg Subtype.val hz'
    rcases omegaToProj_eq_iff hQ hproj.symm with h1 | h1
    · exact absurd (Subtype.ext (Subtype.ext h1)) hz
    · exact Subtype.ext (Subtype.ext h1)
  exact (Nat.card_eq_two_iff' xF).mpr ⟨pF, hne, huniq⟩

end CFSG.OddStandard.SmallF3.Omega
