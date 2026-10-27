module

public import CFSG.LargeExtraspecial.S3Thompson
public import CFSG.LargeExtraspecial.GLRElimSylow
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4FusionTwo
public import CFSG.LargeExtraspecial.GLRTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial Subgroup CFSG.GH74.GLS.Bg.Thompson
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] (S : Setting G)
variable (M0bar : Subgroup S.O) (hM0 : M0bar ≤ S.Mbar)

@[expose] noncomputable def M0 : Subgroup S.M := M0bar.comap S.ρ

@[expose] noncomputable def M0G : Subgroup G := (M0 S M0bar).map S.M.subtype

theorem mem_M0_iff {x : S.M} : x ∈ M0 S M0bar ↔ S.ρ x ∈ M0bar := Iff.rfl

theorem mem_M0G_iff {x : G} :
    x ∈ M0G S M0bar ↔ ∃ h : x ∈ S.M, (⟨x, h⟩ : S.M) ∈ M0 S M0bar := by
  rw [M0G]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem mem_M0G_of_mem {x : G} (hxM : x ∈ S.M) (hx : (⟨x, hxM⟩ : S.M) ∈ M0 S M0bar) :
    x ∈ M0G S M0bar :=
  Subgroup.mem_map_of_mem S.M.subtype hx

theorem mem_M0G_iff_rho {x : G} (hxM : x ∈ S.M) :
    x ∈ M0G S M0bar ↔ S.ρ ⟨x, hxM⟩ ∈ M0bar := by
  constructor
  · intro hx
    obtain ⟨h, hh⟩ := (mem_M0G_iff S M0bar).mp hx
    have hh' : (⟨x, h⟩ : S.M) = ⟨x, hxM⟩ := Subtype.ext rfl
    rwa [hh'] at hh
  · intro hx
    exact (mem_M0G_iff S M0bar).mpr ⟨hxM, hx⟩

theorem index_M0 (hidx : M0bar.relIndex S.Mbar = 2) : (M0 S M0bar).index = 2 := by
  rw [M0, Subgroup.index_comap]
  exact hidx

theorem relIndex_M0G_M (hidx : M0bar.relIndex S.Mbar = 2) :
    (M0G S M0bar).relIndex S.M = 2 := by
  rw [M0G]
  have h := Subgroup.relIndex_map_map_of_injective (M0 S M0bar) (⊤ : Subgroup S.M)
    S.M.subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right,
    index_M0 S M0bar hidx] at h
  exact h

theorem QG_le_M0G : S.QG ≤ M0G S M0bar := by
  intro x hx
  refine mem_M0G_of_mem S M0bar (S.QG_le_M hx) ?_
  rw [mem_M0_iff, S.ρ_eq_one_of_mem_Q (S.mem_QG_iff.mp hx).2]
  exact M0bar.one_mem

theorem relIndex_inf_M0G {T : Subgroup G} (hTM : T ≤ S.M) (hidx : M0bar.relIndex S.Mbar = 2)
    (hT : ¬ T ≤ M0G S M0bar) : (T ⊓ M0G S M0bar).relIndex T = 2 := by
  have hle : (T ⊓ M0G S M0bar).relIndex T ≤ (M0G S M0bar).relIndex T := by
    have h := Subgroup.relIndex_inf_le (H := M0G S M0bar) (K := T) (L := T)
    simpa [inf_comm] using h
  have hEq : (M0G S M0bar).relIndex S.M = 2 := relIndex_M0G_M S M0bar hidx
  have hle2 : (M0G S M0bar).relIndex T ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right hTM (by rw [hEq]; norm_num)
    rwa [hEq] at h
  have hne0 : (T ⊓ M0G S M0bar).relIndex T ≠ 0 := by
    intro h0
    have hmul := Subgroup.relIndex_mul_card (T ⊓ M0G S M0bar) T
    rw [h0, zero_mul] at hmul
    exact (Nat.card_pos (α := T)).ne' hmul.symm
  have hne1 : (T ⊓ M0G S M0bar).relIndex T ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hT (h1.trans inf_le_right)
  omega

namespace PGLData

private def QClass (τ : G) : Set G :=
  {y : G | ∃ x ∈ S.QG, x⁻¹ * τ * x = y}

private def InvCoset (τ : G) : Set G :=
  {y : G | (∃ x ∈ S.QG, y = τ * x) ∧ y * y = 1}

private def CQ (τ : G) : Subgroup G := S.QG ⊓ Subgroup.centralizer {τ}

private theorem card_QG (hw : S.width = 3) : Nat.card S.QG = 128 := by
  rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw]
  norm_num

private theorem card_QClass_eq_card_relIndex (τ : G) :
    Nat.card ↥(QClass S τ) = (Subgroup.centralizer {τ}).relIndex S.QG := by
  rw [QClass, Nat.card_coe_set_eq]
  exact (CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.relIndex_centralizer_eq_ncard S.QG τ).symm

private theorem card_QClass_eq_sixteen (hw : S.width = 3) {τ : G}
    (hcard : Nat.card (CQ S τ) = 8) :
    Nat.card ↥(QClass S τ) = 16 := by
  have hrel := card_QClass_eq_card_relIndex S τ
  have h1 : (Subgroup.centralizer {τ}).relIndex S.QG = (CQ S τ).relIndex S.QG := by
    rw [CQ, inf_comm, Subgroup.inf_relIndex_right]
  rw [h1] at hrel
  have hmul := Subgroup.relIndex_mul_card (CQ S τ) S.QG
  rw [show CQ S τ ⊓ S.QG = CQ S τ from inf_eq_left.mpr inf_le_left,
    hcard, card_QG S hw] at hmul
  rw [hrel]
  omega

private theorem card_InvCoset_eq_sixteen {τ : G} (hττ : τ * τ = 1)
    (hcount : Nat.card {x : G // x ∈ S.QG ∧ (τ * x) * (τ * x) = 1} = 16) :
    Nat.card ↥(InvCoset S τ) = 16 := by
  rw [← hcount]
  refine Nat.card_congr ?_
  refine
    { toFun := fun y =>
        ⟨τ * y.1, ⟨by
          obtain ⟨x, hx, hyx⟩ := y.2.1
          rw [hyx]
          simpa [← mul_assoc, hττ, one_mul] using hx, by
          obtain ⟨x, hx, hyx⟩ := y.2.1
          rw [hyx]
          have hy2 : (τ * x) * (τ * x) = 1 := by simpa [hyx] using y.2.2
          simpa [← mul_assoc, hττ, one_mul] using hy2⟩⟩
      invFun := fun x => ⟨τ * x.1, ⟨⟨x.1, x.2.1, rfl⟩, x.2.2⟩⟩
      left_inv := fun y => by
        ext
        change τ * (τ * y.1) = y.1
        rw [← mul_assoc, hττ, one_mul]
      right_inv := fun x => by
        ext
        change τ * (τ * x.1) = x.1
        rw [← mul_assoc, hττ, one_mul] }

private theorem QClass_subset_InvCoset (hw : S.width = 3) {τ : G} (hτM : τ ∈ S.M)
    (hττ : τ * τ = 1) (hcard : Nat.card (CQ S τ) = 8)
    (hcount : Nat.card {x : G // x ∈ S.QG ∧ (τ * x) * (τ * x) = 1} = 16) :
    QClass S τ ⊆ InvCoset S τ := by
  rintro y ⟨x, hx, rfl⟩
  have hxM : x ∈ S.M := S.QG_le_M hx
  have hxρ : S.ρ ⟨x, hxM⟩ = 1 := S.ρ_eq_one_of_mem_Q (S.mem_QG_iff.mp hx).2
  have hyM : x⁻¹ * τ * x ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hxM) hτM) hxM
  have hρ : S.ρ ⟨x⁻¹ * τ * x, hyM⟩ = S.ρ ⟨τ, hτM⟩ := by
    have h1 : (⟨x⁻¹ * τ * x, hyM⟩ : S.M) =
        (⟨x, hxM⟩ : S.M)⁻¹ * ⟨τ, hτM⟩ * ⟨x, hxM⟩ :=
      Subtype.ext (by simp [mul_assoc])
    rw [h1, map_mul, map_mul, map_inv, hxρ, inv_one, one_mul, mul_one]
  have hq0M : (x⁻¹ * τ * x) * τ⁻¹ ∈ S.M := S.M.mul_mem hyM (S.M.inv_mem hτM)
  have hq0 : (x⁻¹ * τ * x) * τ⁻¹ ∈ S.QG := by
    rw [← S.ρ_eq_one_iff ⟨_, hq0M⟩]
    have h1 : (⟨(x⁻¹ * τ * x) * τ⁻¹, hq0M⟩ : S.M) =
        ⟨x⁻¹ * τ * x, hyM⟩ * (⟨τ, hτM⟩ : S.M)⁻¹ :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_inv, hρ, mul_inv_cancel]
  refine ⟨⟨τ * (x⁻¹ * τ * x), ?_, ?_⟩, ?_⟩
  · have hqeq : τ * (x⁻¹ * τ * x) =
        τ * ((x⁻¹ * τ * x) * τ⁻¹) * τ⁻¹ := by
      calc τ * (x⁻¹ * τ * x)
          = τ * (x⁻¹ * τ * x) * (τ⁻¹ * τ) := by group
        _ = τ * (x⁻¹ * τ * x) * (τ⁻¹ * τ⁻¹) := by
              rw [inv_mul_cancel, show τ⁻¹ * τ⁻¹ = 1 by
                rw [← mul_inv_rev, hττ, inv_one]]
        _ = τ * ((x⁻¹ * τ * x) * τ⁻¹) * τ⁻¹ := by group
    rw [hqeq]
    exact S.conj_mem_QG hτM hq0
  · rw [← mul_assoc, hττ, one_mul]
  · calc (x⁻¹ * τ * x) * (x⁻¹ * τ * x) = x⁻¹ * (τ * τ) * x := by group
      _ = 1 := by rw [hττ]; group

private theorem QClass_eq_InvCoset (hw : S.width = 3) {τ : G} (hτM : τ ∈ S.M)
    (hττ : τ * τ = 1) (hcard : Nat.card (CQ S τ) = 8)
    (hcount : Nat.card {x : G // x ∈ S.QG ∧ (τ * x) * (τ * x) = 1} = 16) :
    QClass S τ = InvCoset S τ := by
  have hsub := QClass_subset_InvCoset S hw hτM hττ hcard hcount
  have hQ := card_QClass_eq_sixteen S hw hcard
  have hI := card_InvCoset_eq_sixteen S hττ hcount
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  have hI' : (InvCoset S τ).ncard = 16 := by
    rw [show (InvCoset S τ).ncard = Nat.card ↥(InvCoset S τ) from
      (Nat.card_coe_set_eq _).symm, hI]
  have hQ' : (QClass S τ).ncard = 16 := by
    rw [show (QClass S τ).ncard = Nat.card ↥(QClass S τ) from
      (Nat.card_coe_set_eq _).symm, hQ]
  rw [hI', hQ']

private theorem outer_involutions_conj (hw : S.width = 3)
    (hcls : ∀ u ∈ S.Mbar, u ∉ M0bar → u * u = 1 → ∀ u' ∈ S.Mbar, u' ∉ M0bar →
      u' * u' = 1 → ∃ k ∈ S.Mbar, k * u * k⁻¹ = u')
    (hsq : ∀ y : S.M, S.ρ y ∉ M0bar → (y : G) * y = 1 →
      Nat.card {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} = 16 ∧
      Nat.card (CQ S (y : G)) = 8 ∧ ∀ x ∈ CQ S (y : G), x * x = 1)
    {τ a : G} (hτM : τ ∈ S.M) (hτM0 : S.ρ ⟨τ, hτM⟩ ∉ M0bar) (hττ : τ * τ = 1)
    (haM : a ∈ S.M) (haM0 : S.ρ ⟨a, haM⟩ ∉ M0bar) (haa : a * a = 1) :
    ∃ m : S.M, (m : G) * τ * (m : G)⁻¹ = a := by
  set u : S.O := S.ρ ⟨τ, hτM⟩ with hu
  set u' : S.O := S.ρ ⟨a, haM⟩ with hu'
  have huM : u ∈ S.Mbar := ⟨⟨τ, hτM⟩, rfl⟩
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul]
    rw [show (⟨τ, hτM⟩ : S.M) * ⟨τ, hτM⟩ = 1 from Subtype.ext (by simpa using hττ), map_one]
  have hu'M : u' ∈ S.Mbar := ⟨⟨a, haM⟩, rfl⟩
  have hu'2 : u' * u' = 1 := by
    rw [hu', ← map_mul]
    rw [show (⟨a, haM⟩ : S.M) * ⟨a, haM⟩ = 1 from Subtype.ext (by simpa using haa), map_one]
  obtain ⟨k, hk, hku⟩ := hcls u huM hτM0 hu2 u' hu'M haM0 hu'2
  obtain ⟨m0, hm0⟩ := MonoidHom.mem_range.mp (show k ∈ S.ρ.range from hk)
  set b : G := (m0 : G) * τ * (m0 : G)⁻¹ with hb
  have hbM : b ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem m0.2 hτM) (S.M.inv_mem m0.2)
  have hb2 : b * b = 1 := by
    rw [hb]
    calc (m0 : G) * τ * (m0 : G)⁻¹ * ((m0 : G) * τ * (m0 : G)⁻¹)
        = (m0 : G) * (τ * τ) * (m0 : G)⁻¹ := by group
      _ = 1 := by rw [hττ]; group
  have hbρ : S.ρ ⟨b, hbM⟩ = u' := by
    have h1 : (⟨b, hbM⟩ : S.M) = m0 * ⟨τ, hτM⟩ * m0⁻¹ :=
      Subtype.ext (by simp [hb])
    rw [h1, map_mul, map_mul, map_inv, hm0, ← hu, hku]
  have hbM0 : S.ρ ⟨b, hbM⟩ ∉ M0bar := by rw [hbρ]; exact haM0
  obtain ⟨hbcount, hbcard, -⟩ := hsq ⟨b, hbM⟩ hbM0 (by simpa using hb2)
  have habQ : a * b⁻¹ ∈ S.QG := by
    have habM : a * b⁻¹ ∈ S.M := S.M.mul_mem haM (S.M.inv_mem hbM)
    refine (S.ρ_eq_one_iff ⟨_, habM⟩).mp ?_
    have h1 : (⟨a * b⁻¹, habM⟩ : S.M) = ⟨a, haM⟩ * (⟨b, hbM⟩ : S.M)⁻¹ :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_inv, ← hu', hbρ, mul_inv_cancel]
  have hbii : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hb2, inv_one]
  have hbaQ : b * a ∈ S.QG := by
    have h : b * a = b * (a * b⁻¹) * b⁻¹ := by
      calc b * a = b * a * (b⁻¹ * b⁻¹) := by rw [hbii, mul_one]
        _ = b * (a * b⁻¹) * b⁻¹ := by group
    rw [h]
    exact S.conj_mem_QG hbM habQ
  have haInv : a ∈ InvCoset S b := by
    refine ⟨⟨b * a, hbaQ, by rw [← mul_assoc, hb2, one_mul]⟩, haa⟩
  have hEq := QClass_eq_InvCoset S hw hbM hb2 hbcard hbcount
  rw [← hEq] at haInv
  obtain ⟨x, hxQ, hx⟩ := haInv
  have hxM : x ∈ S.M := S.QG_le_M hxQ
  refine ⟨⟨x⁻¹ * (m0 : G), S.M.mul_mem (S.M.inv_mem hxM) m0.2⟩, ?_⟩
  have hx' : x⁻¹ * b * x = a := hx
  calc (x⁻¹ * (m0 : G)) * τ * (x⁻¹ * (m0 : G))⁻¹
      = x⁻¹ * b * x := by rw [hb]; group
    _ = a := hx'

private def CM (τ : G) : Subgroup G := S.M ⊓ Subgroup.centralizer {τ}

private theorem map_CM_eq_centralizer (hw : S.width = 3) {τ : G} (hτM : τ ∈ S.M)
    (hττ : τ * τ = 1) (hcard : Nat.card (CQ S τ) = 8)
    (hcount : Nat.card {x : G // x ∈ S.QG ∧ (τ * x) * (τ * x) = 1} = 16) :
    ((CM S τ).subgroupOf S.M).map S.ρ =
      S.Mbar ⊓ Subgroup.centralizer ({S.ρ ⟨τ, hτM⟩} : Set S.O) := by
  set u : S.O := S.ρ ⟨τ, hτM⟩ with hu
  set Cbar : Subgroup S.O :=
    S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O) with hCbar
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    refine mem_centralizer_singleton_iff.mpr ?_
    have hxc : x * ⟨τ, hτM⟩ = ⟨τ, hτM⟩ * x :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
    calc S.ρ x * u = S.ρ x * S.ρ ⟨τ, hτM⟩ := by rw [hu]
      _ = S.ρ (x * ⟨τ, hτM⟩) := by rw [map_mul]
      _ = S.ρ (⟨τ, hτM⟩ * x) := by rw [hxc]
      _ = u * S.ρ x := by rw [map_mul, hu]
  · rintro z ⟨hzMbar, hzcent⟩
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp (show z ∈ S.ρ.range from hzMbar)
    have hzcomm : z * u = u * z := mem_centralizer_singleton_iff.mp hzcent
    set b : G := (n : G) * τ * (n : G)⁻¹ with hb
    have hbM : b ∈ S.M := S.M.mul_mem (S.M.mul_mem n.2 hτM) (S.M.inv_mem n.2)
    have hb2 : b * b = 1 := by
      rw [hb]
      calc (n : G) * τ * (n : G)⁻¹ * ((n : G) * τ * (n : G)⁻¹)
          = (n : G) * (τ * τ) * (n : G)⁻¹ := by group
        _ = 1 := by rw [hττ]; group
    have hbρ : S.ρ ⟨b, hbM⟩ = u := by
      have h1 : (⟨b, hbM⟩ : S.M) = n * ⟨τ, hτM⟩ * n⁻¹ := Subtype.ext (by simp [hb])
      rw [h1, map_mul, map_mul, map_inv, hn, hu]
      calc z * (S.ρ ⟨τ, hτM⟩) * z⁻¹ = z * u * z⁻¹ := by rw [hu]
        _ = u := by rw [hzcomm]; group
    have hbτM : b * τ⁻¹ ∈ S.M := S.M.mul_mem hbM (S.M.inv_mem hτM)
    have hbτQ : b * τ⁻¹ ∈ S.QG := by
      refine (S.ρ_eq_one_iff ⟨_, hbτM⟩).mp ?_
      have h1 : (⟨b * τ⁻¹, hbτM⟩ : S.M) = ⟨b, hbM⟩ * (⟨τ, hτM⟩ : S.M)⁻¹ :=
        Subtype.ext (by simp)
      rw [h1, map_mul, map_inv, hbρ, mul_inv_cancel]
    have hbInv : b ∈ InvCoset S τ := by
      refine ⟨⟨τ * b, ?_, by rw [← mul_assoc, hττ, one_mul]⟩, hb2⟩
      have h : τ * b = τ * (b * τ⁻¹) * τ⁻¹ := by
        calc τ * b = τ * b * (τ⁻¹ * τ⁻¹) := by
              rw [show τ⁻¹ * τ⁻¹ = 1 by rw [← mul_inv_rev, hττ, inv_one], mul_one]
          _ = τ * (b * τ⁻¹) * τ⁻¹ := by group
      rw [h]
      exact S.conj_mem_QG hτM hbτQ
    have hEq := QClass_eq_InvCoset S hw hτM hττ hcard hcount
    rw [← hEq] at hbInv
    obtain ⟨x, hxQ, hx⟩ := hbInv
    have hxM : x ∈ S.M := S.QG_le_M hxQ
    have hxnM : x * (n : G) ∈ S.M := S.M.mul_mem hxM n.2
    refine ⟨⟨x * (n : G), hxnM⟩, ⟨hxnM, ?_⟩, ?_⟩
    · refine mem_centralizer_singleton_iff.mpr ?_
      have h2 : x * (n : G) * τ * (x * (n : G))⁻¹ = τ := by
        calc x * (n : G) * τ * (x * (n : G))⁻¹
            = x * b * x⁻¹ := by rw [hb]; group
          _ = τ := by rw [← hx]; group
      calc (x * (n : G)) * τ = ((x * (n : G)) * τ * (x * (n : G))⁻¹) * (x * (n : G)) :=
            by group
        _ = τ * (x * (n : G)) := by rw [h2]
    · have h1 : (⟨x * (n : G), hxnM⟩ : S.M) = ⟨x, hxM⟩ * n := Subtype.ext (by simp)
      rw [h1, map_mul, S.ρ_eq_one_of_mem_Q (S.mem_QG_iff.mp hxQ).2, one_mul, hn]

private theorem card_CM (hw : S.width = 3) {τ : G} (hτM : τ ∈ S.M) (hττ : τ * τ = 1)
    (hcard : Nat.card (CQ S τ) = 8)
    (hcount : Nat.card {x : G // x ∈ S.QG ∧ (τ * x) * (τ * x) = 1} = 16)
    (h12 : Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({S.ρ ⟨τ, hτM⟩} : Set S.O)) = 12) :
    Nat.card (CM S τ) = 96 := by
  set u : S.O := S.ρ ⟨τ, hτM⟩ with hu
  set Cbar : Subgroup S.O :=
    S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O) with hCbar
  let f : CM S τ →* S.O := S.ρ.comp (Subgroup.inclusion (inf_le_left : CM S τ ≤ S.M))
  have hrange : f.range = Cbar := by
    have hmap := map_CM_eq_centralizer S hw hτM hττ hcard hcount
    have h1 : f.range = ((CM S τ).subgroupOf S.M).map S.ρ := by
      ext z
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨⟨c.1, c.2.1⟩, c.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [h1, hmap]
  have hCQle : CQ S τ ≤ CM S τ := by
    intro x hx
    exact ⟨S.QG_le_M hx.1, hx.2⟩
  have hker : f.ker = (CQ S τ).subgroupOf (CM S τ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxM : ((x : CM S τ) : G) ∈ S.M := (Subgroup.mem_inf.mp x.2).1
      have hxQ : ((x : CM S τ) : G) ∈ S.QG := by
        rw [← S.ρ_eq_one_iff ⟨_, hxM⟩]
        exact hx
      exact ⟨hxQ, (Subgroup.mem_inf.mp x.2).2⟩
    · rintro ⟨hxQ, hxc⟩
      rw [show f x = S.ρ ⟨((x : CM S τ) : G), (Subgroup.mem_inf.mp x.2).1⟩ from rfl]
      exact (S.ρ_eq_one_iff _).mpr hxQ
  have hkerCard : Nat.card f.ker = Nat.card (CQ S τ) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCQle).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hkerCard, hrange, hCbar, h12, hcard] at hmul
  omega

private theorem cl_sq_mul {y : S.M} (hyy : (y : G) * (y : G) = 1) {x : G} (hxQ : x ∈ S.QG) :
    S.cl (((y : G) * x) * ((y : G) * x)) =
      ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) + S.cl x := by
  have hyM : (y : G) ∈ S.M := y.2
  have hconv : (y : G) * x * (y : G) = (y : G) * x * (y : G)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hyy]
  have hprod : ((y : G) * x) * ((y : G) * x) = ((y : G) * x * (y : G)⁻¹) * x := by
    calc ((y : G) * x) * ((y : G) * x) = ((y : G) * x * (y : G)) * x := by group
      _ = ((y : G) * x * (y : G)⁻¹) * x := by rw [hconv]
  rw [hprod, S.cl_mul (S.conj_mem_QG hyM hxQ) hxQ, ← S.ρ_cl y hxQ]

private abbrev Fix (y : S.M) : Type _ :=
  {v : S.Qt // ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}

private theorem card_Fix {y : S.M} (hyM0 : y ∈ M0 S M0bar) (hy1 : S.ρ y ≠ 1)
    (hyy : (y : G) * (y : G) = 1)
    (h16 : ∀ w ∈ M0bar, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16) :
    Nat.card (Fix S y) = 16 :=
  (h16 (S.ρ y) hyM0 hy1 (by rw [← map_mul, show y * y = 1 from Subtype.ext hyy, map_one])).2

private theorem card_involution_coset_le {y : S.M} (hyM0 : y ∈ M0 S M0bar)
    (hy1 : S.ρ y ≠ 1) (hyy : (y : G) * (y : G) = 1)
    (h16 : ∀ w ∈ M0bar, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16) :
    Nat.card {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} ≤ 32 := by
  classical
  let F := Fix S y
  have hFix : Nat.card F = 16 := card_Fix S M0bar hyM0 hy1 hyy h16
  haveI : Finite S.Qt := inferInstance
  haveI : Finite F := by
    dsimp [F]
    infer_instance
  haveI : Finite (F × Bool) := inferInstance
  let e : F → G := fun v => Classical.choose (S.exists_cl v.1)
  have he_mem : ∀ v : F, e v ∈ S.QG := fun v =>
    (Classical.choose_spec (S.exists_cl v.1)).1
  have he_cl : ∀ v : F, S.cl (e v) = v.1 := fun v =>
    (Classical.choose_spec (S.exists_cl v.1)).2
  let fixOf : {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} → F :=
    fun x => ⟨S.cl x.1, by
      have hcl := cl_sq_mul S hyy x.2.1
      rw [show ((y : G) * x.1) * ((y : G) * x.1) = 1 from x.2.2, S.cl_one] at hcl
      have h2 : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x.1) = -(S.cl x.1) :=
        add_eq_zero_iff_eq_neg.mp hcl.symm
      simpa [ZModModule.neg_eq_self] using h2⟩
  let φ : {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} →
      F × Bool := fun x => (fixOf x, decide (x.1 = e (fixOf x)))
  have hfiber : ∀ x : {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1},
      x.1 = e (fixOf x) ∨ x.1 = e (fixOf x) * S.z := by
    intro x
    have hcl : S.cl (e (fixOf x)) = S.cl x.1 := by
      rw [he_cl]
    exact (S.cl_eq_cl_iff (he_mem (fixOf x)) x.2.1).mp hcl
  have hφ : Function.Injective φ := by
    intro x1 x2 h
    have hv : fixOf x1 = fixOf x2 := congrArg Prod.fst h
    have hb : decide (x1.1 = e (fixOf x1)) = decide (x2.1 = e (fixOf x2)) :=
      congrArg Prod.snd h
    have heq : e (fixOf x1) = e (fixOf x2) := congrArg e hv
    have hf2 := hfiber x2
    rw [← heq] at hf2
    rw [← heq] at hb
    by_cases h1 : x1.1 = e (fixOf x1)
    · by_cases h2 : x2.1 = e (fixOf x1)
      · exact Subtype.ext (h1.trans h2.symm)
      · rw [h1] at hb
        simp [h2] at hb
    · by_cases h2 : x2.1 = e (fixOf x1)
      · rw [h2] at hb
        simp [h1] at hb
      · have h1' := (hfiber x1).resolve_left h1
        have h2' := hf2.resolve_left h2
        exact Subtype.ext (h1'.trans (h2'.symm))
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, show Nat.card F = 16 from hFix,
    show Nat.card Bool = 2 from by simp] at hcard
  omega

private theorem rho_eq_one_iff_mem_Q (x : S.M) : S.ρ x = 1 ↔ x ∈ S.Q := by
  rw [S.ρ_eq_one_iff, S.mem_QG_iff]
  constructor
  · rintro ⟨h, hx⟩
    have hx' : (⟨(x : G), h⟩ : S.M) = x := Subtype.ext rfl
    rwa [hx'] at hx
  · intro hx
    exact ⟨x.2, by simpa using hx⟩

private theorem exists_le_centralizer_card_eq_sixtyFour_of_mem_Q
    (hw : S.width = 3) {y : G} (hyQ : y ∈ S.QG) (hyy : y * y = 1) :
    ∃ P : Subgroup G, P ≤ CM S y ∧ IsPGroup 2 P ∧ Nat.card P = 64 := by
  set C : Subgroup G := S.QG ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hC2 : IsPGroup 2 C := (S.isPGroup_QG).to_le inf_le_left
  have hCcard : 64 ≤ Nat.card C := by
    by_cases hy : y = 1 ∨ y = S.z
    · have hCeq : C = S.QG := by
        ext q
        constructor
        · exact fun h => h.1
        · intro hq
          refine ⟨hq, mem_centralizer_singleton_iff.mpr ?_⟩
          rcases hy with rfl | rfl
          · rw [mul_one, one_mul]
          · exact S.z_comm_QG hq
      rw [hCeq, card_QG S hw]
      norm_num
    · push Not at hy
      have hrel := S.relIndex_centralizer_eq_two hyQ hy.1 hy.2
      have hCsub : C ≤ S.QG := inf_le_left
      have hmul := Subgroup.relIndex_mul_card C S.QG
      rw [show C ⊓ S.QG = C from inf_eq_left.mpr hCsub,
        show C.relIndex S.QG = 2 from by rw [hC]; exact hrel, card_QG S hw] at hmul
      omega
  obtain ⟨P, -, hPcard⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
    (p := 2) (n := 6) (H := ⊤) Nat.prime_two hC2 (by simpa using hCcard)
  refine ⟨P.map C.subtype, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨S.QG_le_M p.2.1, p.2.2⟩
  · exact IsPGroup.of_card (n := 6)
      (by rw [Subgroup.card_map_of_injective C.subtype_injective, hPcard])
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hPcard]
    norm_num

private theorem card_comap_of_le_Mbar (C : Subgroup S.O) (hC : C ≤ S.Mbar) :
    Nat.card (C.comap S.ρ : Subgroup S.M) = Nat.card C * Nat.card S.Q := by
  classical
  let N : Subgroup S.M := C.comap S.ρ
  let f : N →* S.O := S.ρ.comp N.subtype
  have hrange : f.range = C := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hz
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (show z ∈ S.ρ.range from hC hz)
      refine ⟨⟨x, ?_⟩, hx⟩
      show S.ρ x ∈ C
      rw [hx]
      exact hz
  have hQN : S.Q ≤ N := by
    intro x hx
    show S.ρ x ∈ C
    rw [(rho_eq_one_iff_mem_Q S x).mpr hx]
    exact C.one_mem
  have hker : f.ker = S.Q.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact rho_eq_one_iff_mem_Q S x
  have hkerCard : Nat.card f.ker = Nat.card S.Q := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hkerCard, hrange, mul_comm] at hmul
  exact hmul.symm

private theorem exists_le_centralizer_card_eq_sixtyFour_of_not_mem_Q
    (hw : S.width = 3) {y : S.M} (hyM0 : y ∈ M0 S M0bar)
    (hyy : (y : G) * (y : G) = 1) (hy1 : S.ρ y ≠ 1)
    (h16 : ∀ w ∈ M0bar, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16) :
    ∃ P : Subgroup G, P ≤ CM S (y : G) ∧ IsPGroup 2 P ∧ Nat.card P = 64 := by
  classical
  set w : S.O := S.ρ y with hwdef
  set Cbar : Subgroup S.O := S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O) with hCbar
  have hww : w * w = 1 := by
    rw [hwdef, ← map_mul, show y * y = 1 from Subtype.ext hyy, map_one]
  have hCbar16 : Nat.card Cbar = 16 := (h16 w (by rw [hwdef]; exact hyM0) hy1 hww).1
  have hCbarle : Cbar ≤ S.Mbar := inf_le_left
  set N : Subgroup S.M := Cbar.comap S.ρ with hN
  have hNcard : Nat.card N = 2 ^ 11 := by
    rw [hN, card_comap_of_le_Mbar S Cbar hCbarle, hCbar16, S.card_Q_eq, hw]
    norm_num
  have hN2 : IsPGroup 2 N := IsPGroup.of_card (n := 11) (by rw [hNcard])
  let P : Subgroup G := N.map S.M.subtype
  have hPcard : Nat.card P = 2 ^ 11 := by
    rw [show P = N.map S.M.subtype from rfl,
      Subgroup.card_map_of_injective S.M.subtype_injective, hNcard]
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 11) (by rw [hPcard])
  let Orb : Set G := {z : G | ∃ n ∈ P, n⁻¹ * (y : G) * n = z}
  have hOrbCard : Nat.card ↥Orb = (Subgroup.centralizer ({(y : G)} : Set G)).relIndex P := by
    rw [Nat.card_coe_set_eq]
    exact (CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.relIndex_centralizer_eq_ncard P (y : G)).symm
  have hOrbLe : Nat.card ↥Orb ≤ 32 := by
    let F : ↥Orb → {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} :=
      fun z =>
        ⟨(y : G) * z.1, ⟨by
          obtain ⟨n, hnP, hz⟩ := z.2
          obtain ⟨n', hn', hnEq⟩ := Subgroup.mem_map.mp hnP
          have hnC : S.ρ n' ∈ Cbar := hn'
          have hcomm : S.ρ n' * w = w * S.ρ n' :=
            mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hnC).2
          have hzM : z.1 ∈ S.M := by
            rw [← hz, ← hnEq]
            exact S.M.mul_mem (S.M.mul_mem (S.M.inv_mem n'.2) y.2) n'.2
          have hzρ : S.ρ ⟨z.1, hzM⟩ = w := by
            have h1 : (⟨z.1, hzM⟩ : S.M) = n'⁻¹ * y * n' := by
              apply Subtype.ext
              rw [← hz, ← hnEq]
              rfl
            rw [h1, map_mul, map_mul, map_inv]
            calc (S.ρ n')⁻¹ * w * S.ρ n' = (S.ρ n')⁻¹ * (S.ρ n' * w) := by
                  rw [hcomm]; group
              _ = w := by group
          have hyzM : (y : G) * z.1 ∈ S.M := S.M.mul_mem y.2 hzM
          have hρ : S.ρ ⟨(y : G) * z.1, hyzM⟩ = 1 := by
            have h1 : (⟨(y : G) * z.1, hyzM⟩ : S.M) = y * ⟨z.1, hzM⟩ :=
              Subtype.ext rfl
            rw [h1, map_mul, hzρ, hww]
          exact (S.mem_QG_iff).mpr ⟨hyzM, (rho_eq_one_iff_mem_Q S _).mp hρ⟩, by
          obtain ⟨n, hnP, hz⟩ := z.2
          obtain ⟨n', hn', hnEq⟩ := Subgroup.mem_map.mp hnP
          have hz2 : z.1 * z.1 = 1 := by
            rw [← hz, ← hnEq]
            calc (n' : G)⁻¹ * (y : G) * n' * ((n' : G)⁻¹ * (y : G) * n')
                = (n' : G)⁻¹ * ((y : G) * (y : G)) * n' := by group
              _ = 1 := by rw [hyy]; group
          rw [show (y : G) * ((y : G) * z.1) = z.1 by
            rw [← mul_assoc, hyy, one_mul], hz2]⟩⟩
    have hF : Function.Injective F := by
      intro z1 z2 h
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    exact (Nat.card_le_card_of_injective F hF).trans
      (card_involution_coset_le S M0bar hyM0 hy1 hyy h16)

  have hCMleP : CM S (y : G) ≤ P := by
    intro x hx
    have hxM : x ∈ S.M := (Subgroup.mem_inf.mp hx).1
    have hxc : x ∈ Subgroup.centralizer ({(y : G)} : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxρ : S.ρ ⟨x, hxM⟩ ∈ Cbar := by
      refine ⟨⟨⟨x, hxM⟩, rfl⟩, ?_⟩
      refine mem_centralizer_singleton_iff.mpr ?_
      have hpair : (⟨x, hxM⟩ : S.M) * y = y * ⟨x, hxM⟩ :=
        Subtype.ext (mem_centralizer_singleton_iff.mp hxc)
      have := congrArg (fun t : S.M => S.ρ t) hpair
      simpa using this
    refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
    change S.ρ ⟨x, hxM⟩ ∈ Cbar
    exact hxρ
  have hInter : P ⊓ Subgroup.centralizer ({(y : G)} : Set G) = CM S (y : G) := by
    ext x
    constructor
    · rintro ⟨hxP, hxc⟩
      obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hxP
      exact ⟨p.2, hxc⟩
    · intro hx
      exact ⟨hCMleP hx, (Subgroup.mem_inf.mp hx).2⟩
  have hmul := Subgroup.relIndex_mul_card
    (Subgroup.centralizer ({(y : G)} : Set G)) P
  rw [inf_comm (Subgroup.centralizer ({(y : G)} : Set G)) P, hInter, ← hOrbCard,
    hPcard] at hmul
  norm_num at hmul
  have hOrbLe' : Orb.ncard ≤ 32 := by
    rw [← Nat.card_coe_set_eq]
    exact hOrbLe
  have hCMge : 64 ≤ Nat.card (CM S (y : G)) := by
    have h1 : 2048 ≤ 32 * Nat.card (CM S (y : G)) := by
      calc 2048 = Orb.ncard * Nat.card (CM S (y : G)) := by rw [hmul]
        _ ≤ 32 * Nat.card (CM S (y : G)) := Nat.mul_le_mul_right _ hOrbLe'
    have h2 : 32 * 64 ≤ 32 * Nat.card (CM S (y : G)) := by
      calc 32 * 64 = 2048 := by norm_num
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hCM2 : IsPGroup 2 (CM S (y : G)) := hP2.to_le hCMleP
  obtain ⟨P0, -, hP0card⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
    (p := 2) (n := 6) (H := ⊤) Nat.prime_two hCM2 (by simpa using hCMge)
  refine ⟨P0.map (CM S (y : G)).subtype, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact p.2
  · exact IsPGroup.of_card (n := 6)
      (by rw [Subgroup.card_map_of_injective (CM S (y : G)).subtype_injective, hP0card])
  · rw [Subgroup.card_map_of_injective (CM S (y : G)).subtype_injective, hP0card]
    norm_num

private theorem exists_le_centralizer_card_eq_sixtyFour_of_mem_M0
    (hw : S.width = 3) {y : G} (hyM : y ∈ S.M) (hyy : y * y = 1)
    (hyM0 : y ∈ M0G S M0bar)
    (h16 : ∀ w ∈ M0bar, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16) :
    ∃ P : Subgroup G, P ≤ CM S y ∧ IsPGroup 2 P ∧ Nat.card P = 64 := by
  by_cases hyQ : y ∈ S.QG
  · exact exists_le_centralizer_card_eq_sixtyFour_of_mem_Q S hw hyQ hyy
  · have hy1 : S.ρ ⟨y, hyM⟩ ≠ 1 := fun h =>
      hyQ (S.mem_QG_iff.mpr ⟨hyM, (rho_eq_one_iff_mem_Q S _).mp h⟩)
    have hyM0' : (⟨y, hyM⟩ : S.M) ∈ M0 S M0bar :=
      (mem_M0G_iff_rho S M0bar hyM).mp hyM0
    exact exists_le_centralizer_card_eq_sixtyFour_of_not_mem_Q S M0bar hw hyM0' hyy hy1 h16

private theorem map_CM_conj {τ : G} {g : G} (hg : g * S.z * g⁻¹ = τ) :
    (CM S (g⁻¹ * S.z * g)).map (MulAut.conj g).toMonoidHom = CM S τ := by
  have hg' : g⁻¹ * τ * g = S.z := by rw [← hg]; group
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyM : y ∈ S.M := (Subgroup.mem_inf.mp hy).1
    have hyc : y ∈ Subgroup.centralizer ({(g⁻¹ * S.z * g)} : Set G) :=
      (Subgroup.mem_inf.mp hy).2
    have hycomm : y * (g⁻¹ * S.z * g) = (g⁻¹ * S.z * g) * y :=
      mem_centralizer_singleton_iff.mp hyc
    refine ⟨?_, ?_⟩
    · refine (S.mem_M_iff).mpr ?_
      calc (g * y * g⁻¹) * S.z
          = g * (y * (g⁻¹ * S.z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * S.z * g) * y) * g⁻¹ := by rw [hycomm]
        _ = S.z * (g * y * g⁻¹) := by group
    · refine mem_centralizer_singleton_iff.mpr ?_
      calc (g * y * g⁻¹) * τ
          = g * (y * (g⁻¹ * τ * g)) * g⁻¹ := by group
        _ = g * (y * S.z) * g⁻¹ := by rw [hg']
        _ = g * (S.z * y) * g⁻¹ := by rw [S.mem_M_iff.mp hyM]
        _ = τ * (g * y * g⁻¹) := by rw [← hg']; group
  · rintro ⟨hxM, hxc⟩
    have hxc' : x * τ = τ * x := mem_centralizer_singleton_iff.mp hxc
    have hxM' : S.z * x = x * S.z := (S.mem_M_iff.mp hxM).symm
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, ?_⟩
    · refine (S.mem_M_iff).mpr ?_
      calc (g⁻¹ * x * g) * S.z
          = g⁻¹ * (x * (g * S.z * g⁻¹)) * g := by group
        _ = g⁻¹ * (x * τ) * g := by rw [hg]
        _ = g⁻¹ * (τ * x) * g := by rw [hxc']
        _ = (g⁻¹ * τ * g) * (g⁻¹ * x * g) := by group
        _ = S.z * (g⁻¹ * x * g) := by rw [hg']
    · refine mem_centralizer_singleton_iff.mpr ?_
      calc (g⁻¹ * x * g) * (g⁻¹ * S.z * g)
          = g⁻¹ * (x * S.z) * g := by group
        _ = g⁻¹ * (S.z * x) * g := by rw [hxM']
        _ = (g⁻¹ * S.z * g) * (g⁻¹ * x * g) := by group
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

private theorem card_CM_conj {τ : G} {g : G} (hg : g * S.z * g⁻¹ = τ) :
    Nat.card (CM S (g⁻¹ * S.z * g)) = Nat.card (CM S τ) := by
  rw [← map_CM_conj S hg]
  exact (Subgroup.card_map_of_injective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).symm

private theorem not_isConj_z_of_outer_involution (hw : S.width = 3)
    (hcls : ∀ u ∈ S.Mbar, u ∉ M0bar → u * u = 1 → ∀ u' ∈ S.Mbar, u' ∉ M0bar →
      u' * u' = 1 → ∃ k ∈ S.Mbar, k * u * k⁻¹ = u')
    (h12 : ∀ u ∈ S.Mbar, u ∉ M0bar → u * u = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O)) = 12 ∧
      ∀ N : Subgroup S.O, N ≤ S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O) →
        (∀ c ∈ S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O), ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
        IsPGroup 2 N → N ≤ Subgroup.zpowers u)
    (h16 : ∀ w ∈ M0bar, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16)
    (hsq : ∀ y : S.M, S.ρ y ∉ M0bar → (y : G) * y = 1 →
      Nat.card {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} = 16 ∧
      Nat.card (CQ S (y : G)) = 8 ∧ ∀ x ∈ CQ S (y : G), x * x = 1)
    (hQz : ∀ y : S.M, S.ρ y ∉ M0bar → ∀ e ∈ S.QG, IsConj e S.z → e * y = y * e →
      e = S.z)
    {τ : G} (hτM : τ ∈ S.M) (hτM0 : S.ρ ⟨τ, hτM⟩ ∉ M0bar) (hττ : τ * τ = 1)
    (hEcard : Nat.card (CQ S τ) = 8) (hEelem : ∀ x ∈ CQ S τ, x * x = 1)
    (hcount : Nat.card {x : G // x ∈ S.QG ∧ (τ * x) * (τ * x) = 1} = 16) :
    ¬ IsConj S.z τ := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  set z' : G := g⁻¹ * S.z * g with hz'
  have hz'M : z' ∈ S.M := by
    rw [hz', S.mem_M_iff]
    calc (g⁻¹ * S.z * g) * S.z
        = g⁻¹ * (S.z * (g * S.z * g⁻¹)) * g := by group
      _ = g⁻¹ * (S.z * τ) * g := by rw [hg]
      _ = g⁻¹ * (τ * S.z) * g := by rw [(S.z_comm hτM).symm]
      _ = S.z * (g⁻¹ * S.z * g) := by rw [← hg]; group
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc (g⁻¹ * S.z * g) * (g⁻¹ * S.z * g)
        = g⁻¹ * (S.z * S.z) * g := by group
      _ = 1 := by rw [S.z_mul_z]; group
  have hτCM : Nat.card (CM S τ) = 96 :=
    card_CM S hw hτM hττ hEcard hcount (h12 (S.ρ ⟨τ, hτM⟩)
      ⟨⟨τ, hτM⟩, rfl⟩ hτM0
      (by rw [← map_mul, show (⟨τ, hτM⟩ : S.M) * ⟨τ, hτM⟩ = 1 from
        Subtype.ext hττ, map_one])).1
  have hcardCMz' : Nat.card (CM S z') = 96 := by
    rw [hz', card_CM_conj S hg]
    exact hτCM
  have hz'M0 : z' ∉ M0G S M0bar := by
    intro hz0
    obtain ⟨P, hPle, -, hPcard⟩ :=
      exists_le_centralizer_card_eq_sixtyFour_of_mem_M0 S M0bar hw hz'M hz'2 hz0 h16
    have hdvd : 64 ∣ 96 := by
      calc 64 = Nat.card P := hPcard.symm
        _ ∣ Nat.card (CM S z') := Subgroup.card_dvd_of_le hPle
        _ = 96 := hcardCMz'
    norm_num at hdvd
  have hz'M0rho : S.ρ ⟨z', hz'M⟩ ∉ M0bar := fun h =>
    hz'M0 ((mem_M0G_iff_rho S M0bar hz'M).mpr h)
  obtain ⟨m, hm⟩ := outer_involutions_conj S M0bar hw hcls hsq hτM hτM0 hττ
    hz'M hz'M0rho hz'2
  let hG : G := g * (m : G)
  have hhτ : hG * τ * hG⁻¹ = S.z := by
    calc (g * (m : G)) * τ * (g * (m : G))⁻¹
        = g * ((m : G) * τ * (m : G)⁻¹) * g⁻¹ := by group
      _ = g * z' * g⁻¹ := by rw [hm]
      _ = S.z := by rw [hz']; group
  have hhz : hG * S.z * hG⁻¹ = τ := by
    calc (g * (m : G)) * S.z * (g * (m : G))⁻¹
        = g * ((m : G) * S.z * (m : G)⁻¹) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by
          rw [show (m : G) * S.z * (m : G)⁻¹ = S.z by
            rw [S.mem_M_iff.mp m.2]; group]
      _ = τ := hg
  have hGz : hG⁻¹ * S.z * hG = τ := by
    calc hG⁻¹ * S.z * hG = hG⁻¹ * (hG * τ * hG⁻¹) * hG := by rw [← hhτ]
      _ = τ := by group
  have hHGτ : hG⁻¹ * τ * hG = S.z := by
    calc hG⁻¹ * τ * hG = hG⁻¹ * (hG * S.z * hG⁻¹) * hG := by rw [hhz]
      _ = S.z := by group
  let E : Subgroup G := CQ S τ
  let E' : Subgroup G := E.map (MulAut.conj hG).toMonoidHom
  have hEcard8 : Nat.card E = 8 := hEcard
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hEcard8]; norm_num)
  have hE'card : Nat.card E' = 8 := by
    rw [show E' = E.map (MulAut.conj hG).toMonoidHom from rfl,
      Subgroup.card_map_of_injective
        (f := (MulAut.conj hG).toMonoidHom) (MulAut.conj hG).injective, hEcard8]
  have hE'elem : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    calc (hG * e * hG⁻¹) * (hG * e * hG⁻¹) = hG * (e * e) * hG⁻¹ := by group
      _ = 1 := by rw [hEelem e he]; group
  have hτE' : τ ∈ E' := by
    refine Subgroup.mem_map.mpr ⟨S.z, ?_, ?_⟩
    · rw [show E = CQ S τ from rfl]
      exact ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hτM).symm⟩
    · simpa [MulAut.conj_apply] using hhz
  have hE'leCM : E' ≤ CM S τ := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    have heCM : e ∈ CM S τ :=
      ⟨S.QG_le_M (Subgroup.mem_inf.mp he).1, (Subgroup.mem_inf.mp he).2⟩
    have heM : e ∈ S.M := (Subgroup.mem_inf.mp heCM).1
    have hec : e * τ = τ * e :=
      mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp heCM).2
    refine ⟨?_, ?_⟩
    · refine (S.mem_M_iff).mpr ?_
      calc (hG * e * hG⁻¹) * S.z
          = hG * (e * (hG⁻¹ * S.z * hG)) * hG⁻¹ := by group
        _ = hG * (e * τ) * hG⁻¹ := by rw [hGz]
        _ = hG * (τ * e) * hG⁻¹ := by rw [hec]
        _ = S.z * (hG * e * hG⁻¹) := by
          rw [show hG * (τ * e) * hG⁻¹ =
            (hG * τ * hG⁻¹) * (hG * e * hG⁻¹) by group, hhτ]
    · refine mem_centralizer_singleton_iff.mpr ?_
      calc (hG * e * hG⁻¹) * τ
          = hG * (e * (hG⁻¹ * τ * hG)) * hG⁻¹ := by group
        _ = hG * (e * S.z) * hG⁻¹ := by rw [hHGτ]
        _ = hG * (S.z * e) * hG⁻¹ := by rw [S.mem_M_iff.mp heM]
        _ = τ * (hG * e * hG⁻¹) := by
          rw [show hG * (S.z * e) * hG⁻¹ =
            (hG * S.z * hG⁻¹) * (hG * e * hG⁻¹) by group, hhz]
  have hzE' : S.z ∉ E' := by
    intro hzE
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hzE
    have hzE : (e : G) ∈ S.QG := (Subgroup.mem_inf.mp he).1
    have h2 : hG⁻¹ * S.z * hG = τ := by rw [← hhτ]; group
    have heτ : (e : G) = τ := by
      have heq' : hG * e * hG⁻¹ = S.z := by
        simpa [MulAut.conj_apply] using heq
      have h3 : hG⁻¹ * S.z * hG = (e : G) := by
        calc hG⁻¹ * S.z * hG = hG⁻¹ * (hG * e * hG⁻¹) * hG := by rw [← heq']
          _ = e := by group
      rw [← h2]
      exact h3.symm
    exact hτM0 ((mem_M0G_iff_rho S M0bar hτM).mp
      (QG_le_M0G S M0bar (heτ ▸ hzE)))

  have hτE : τ ∉ E := by
    intro hτ
    have hτQ : τ ∈ S.QG := (Subgroup.mem_inf.mp hτ).1
    exact hτM0 ((mem_M0G_iff_rho S M0bar hτM).mp (QG_le_M0G S M0bar hτQ))
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hx2 := hEelem x hx
    have hy2 := hEelem y hy
    have hxy2 := hEelem (x * y) (E.mul_mem hx hy)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hxyinv : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy2
    calc x * y = (x * y)⁻¹ := hxyinv.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hxinv, hyinv]
  have hE'comm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hy
    calc (hG * e * hG⁻¹) * (hG * f * hG⁻¹) = hG * (e * f) * hG⁻¹ := by group
      _ = hG * (f * e) * hG⁻¹ := by rw [hEcomm e he f hf]
      _ = (hG * f * hG⁻¹) * (hG * e * hG⁻¹) := by group
  have hE_normal : ∀ c ∈ CM S τ, ∀ e ∈ E, c * e * c⁻¹ ∈ E := by
    intro c hc e he
    have hcM : c ∈ S.M := (Subgroup.mem_inf.mp hc).1
    let Cτ : Subgroup G := Subgroup.centralizer ({τ} : Set G)
    have hcC : c ∈ Cτ := (Subgroup.mem_inf.mp hc).2
    have heC : e ∈ Cτ := (Subgroup.mem_inf.mp he).2
    have hcent : c * e * c⁻¹ ∈ Cτ :=
      Cτ.mul_mem (Cτ.mul_mem hcC heC) (Cτ.inv_mem hcC)
    exact ⟨S.conj_mem_QG hcM (Subgroup.mem_inf.mp he).1, hcent⟩
  have hnormal_CM : ∀ c ∈ CM S τ, hG⁻¹ * c * hG ∈ CM S τ := by
    intro c hc
    have hcM : c ∈ S.M := (Subgroup.mem_inf.mp hc).1
    have hcc : c * τ = τ * c :=
      mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    have hcz : c * S.z = S.z * c := S.mem_M_iff.mp hcM
    refine ⟨?_, ?_⟩
    · refine (S.mem_M_iff).mpr ?_
      calc (hG⁻¹ * c * hG) * S.z
          = hG⁻¹ * (c * (hG * S.z * hG⁻¹)) * hG := by group
        _ = hG⁻¹ * (c * τ) * hG := by rw [hhz]
        _ = hG⁻¹ * (τ * c) * hG := by rw [hcc]
        _ = (hG⁻¹ * τ * hG) * (hG⁻¹ * c * hG) := by group
        _ = S.z * (hG⁻¹ * c * hG) := by rw [hHGτ]
    · refine mem_centralizer_singleton_iff.mpr ?_
      calc (hG⁻¹ * c * hG) * τ
          = hG⁻¹ * (c * (hG * τ * hG⁻¹)) * hG := by group
        _ = hG⁻¹ * (c * S.z) * hG := by rw [hhτ]
        _ = hG⁻¹ * (S.z * c) * hG := by rw [hcz]
        _ = (hG⁻¹ * S.z * hG) * (hG⁻¹ * c * hG) := by group
        _ = τ * (hG⁻¹ * c * hG) := by rw [hGz]
  have hE'_normal : ∀ c ∈ CM S τ, ∀ x ∈ E', c * x * c⁻¹ ∈ E' := by
    intro c hc x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    have hc' := hnormal_CM c hc
    have hmem := hE_normal (hG⁻¹ * c * hG) hc' e he
    refine Subgroup.mem_map.mpr ⟨(hG⁻¹ * c * hG) * e * (hG⁻¹ * c * hG)⁻¹, hmem, ?_⟩
    show hG * ((hG⁻¹ * c * hG) * e * (hG⁻¹ * c * hG)⁻¹) * hG⁻¹ = c * (hG * e * hG⁻¹) * c⁻¹
    group
  have hE'M : E' ≤ S.M := hE'leCM.trans inf_le_left
  let N : Subgroup S.O := (E'.subgroupOf S.M).map S.ρ
  have hNle : N ≤ S.Mbar ⊓ Subgroup.centralizer ({S.ρ ⟨τ, hτM⟩} : Set S.O) := by
    rintro n ⟨x, hx, rfl⟩
    have hxE : (x : G) ∈ E' := hx
    have hxCM : (x : G) ∈ CM S τ := hE'leCM hxE
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hxτ : (x : G) * τ = τ * (x : G) :=
      mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxCM).2
    refine mem_centralizer_singleton_iff.mpr ?_
    calc S.ρ x * S.ρ ⟨τ, hτM⟩ = S.ρ (x * ⟨τ, hτM⟩) := by rw [map_mul]
      _ = S.ρ (⟨τ, hτM⟩ * x) := by
          rw [show x * ⟨τ, hτM⟩ = ⟨τ, hτM⟩ * x from Subtype.ext hxτ]
      _ = S.ρ ⟨τ, hτM⟩ * S.ρ x := by rw [map_mul]
  have hNnormal : ∀ c ∈ S.Mbar ⊓ Subgroup.centralizer
      ({S.ρ ⟨τ, hτM⟩} : Set S.O), ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    rintro c hc n ⟨x, hx, rfl⟩
    have hmap := map_CM_eq_centralizer S hw hτM hττ hEcard hcount
    have hc' : c ∈ Subgroup.map S.ρ ((CM S τ).subgroupOf S.M) := by
      rwa [hmap]
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hc'
    have hdCM : (d : G) ∈ CM S τ := hd
    have hxE : (x : G) ∈ E' := hx
    have hconjE := hE'_normal (d : G) hdCM (x : G) hxE
    refine Subgroup.mem_map.mpr ⟨(d : S.M) * x * (d : S.M)⁻¹, hconjE, ?_⟩
    rw [map_mul, map_mul, map_inv, hdc]
  have hN2 : IsPGroup 2 N := by
    have hE'2 : IsPGroup 2 ↥E' := IsPGroup.of_card (n := 3) (by rw [hE'card]; norm_num)
    have hE'2' : IsPGroup 2 ↥(E'.subgroupOf S.M) :=
      hE'2.of_equiv (Subgroup.subgroupOfEquivOfLe hE'M).symm
    simpa [N] using hE'2'.map S.ρ
  have hNleZ : N ≤ Subgroup.zpowers (S.ρ ⟨τ, hτM⟩) :=
    (h12 (S.ρ ⟨τ, hτM⟩) ⟨⟨τ, hτM⟩, rfl⟩ hτM0
      (by rw [← map_mul, show (⟨τ, hτM⟩ : S.M) * ⟨τ, hτM⟩ = 1 from Subtype.ext hττ,
        map_one])).2 N hNle hNnormal hN2

  have hu2 : S.ρ ⟨τ, hτM⟩ * S.ρ ⟨τ, hτM⟩ = 1 := by
    rw [← map_mul, show (⟨τ, hτM⟩ : S.M) * ⟨τ, hτM⟩ = 1 from Subtype.ext hττ, map_one]
  have hE'le_union : ∀ x ∈ E', x ∈ E ∨ ∃ e ∈ E, x = τ * e := by
    intro x hx
    have hxCM : x ∈ CM S τ := hE'leCM hx
    have hxM : x ∈ S.M := (Subgroup.mem_inf.mp hxCM).1
    have hxc : x ∈ Subgroup.centralizer ({τ} : Set G) := (Subgroup.mem_inf.mp hxCM).2
    have hxτ : x * τ = τ * x := mem_centralizer_singleton_iff.mp hxc
    have hxN : S.ρ ⟨x, hxM⟩ ∈ N :=
      Subgroup.mem_map_of_mem S.ρ (show ⟨x, hxM⟩ ∈ E'.subgroupOf S.M from hx)
    rcases (CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self hu2).mp
      (hNleZ hxN) with hx1 | hxu
    · left
      have hxQ : x ∈ S.QG :=
        S.mem_QG_iff.mpr ⟨hxM, (rho_eq_one_iff_mem_Q S ⟨x, hxM⟩).mp hx1⟩
      exact ⟨hxQ, hxc⟩
    · right
      have hyM : τ * x ∈ S.M := S.M.mul_mem hτM hxM
      have hyρ : S.ρ ⟨τ * x, hyM⟩ = 1 := by
        have h1 : (⟨τ * x, hyM⟩ : S.M) = ⟨τ, hτM⟩ * ⟨x, hxM⟩ := Subtype.ext rfl
        rw [h1, map_mul, hxu, hu2]
      have hyQ : τ * x ∈ S.QG :=
        S.mem_QG_iff.mpr ⟨hyM, (rho_eq_one_iff_mem_Q S ⟨τ * x, hyM⟩).mp hyρ⟩
      have hyc : τ * x ∈ Subgroup.centralizer ({τ} : Set G) := by
        refine mem_centralizer_singleton_iff.mpr ?_
        calc (τ * x) * τ = τ * (x * τ) := by group
          _ = τ * (τ * x) := by rw [hxτ]
      refine ⟨τ * x, ⟨hyQ, hyc⟩, ?_⟩
      show x = τ * (τ * x)
      rw [← mul_assoc, hττ, one_mul]
  have hHidx : (E' ⊓ E).relIndex E' = 2 := by
    refine Subgroup.relIndex_eq_two_iff.mpr ⟨τ, hτE', fun b hb => ?_⟩
    by_cases hbE : b ∈ E
    · have hbH : b ∈ E' ⊓ E := ⟨hb, hbE⟩
      have hbτE' : b * τ ∈ E' := E'.mul_mem hb hτE'
      have hbτ_notE : b * τ ∉ E := by
        intro hbt
        exact hτE (by
          have : τ = b⁻¹ * (b * τ) := by group
          rw [this]
          exact E.mul_mem (E.inv_mem hbE) hbt)
      exact Or.inr ⟨hbH, fun h => hbτ_notE h.2⟩
    · have hbτE' : b * τ ∈ E' := E'.mul_mem hb hτE'
      have hbτE : b * τ ∈ E := by
        rcases hE'le_union b hb with h | ⟨e, he, hbe⟩
        · exact absurd h hbE
        · have heτ : e * τ = τ * e :=
            mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp he).2
          rw [hbe]
          have h : (τ * e) * τ = e := by
            calc (τ * e) * τ = τ * (e * τ) := by group
              _ = τ * (τ * e) := by rw [heτ]
              _ = e := by rw [← mul_assoc, hττ, one_mul]
          rw [h]
          exact he
      exact Or.inl ⟨⟨hbτE', hbτE⟩, fun h => hbE h.2⟩
  have hHcard : Nat.card ↥(E' ⊓ E) = 4 := by
    have hmul := Subgroup.relIndex_mul_card (E' ⊓ E) E'
    rw [show (E' ⊓ E) ⊓ E' = E' ⊓ E from inf_eq_left.mpr inf_le_left,
      hHidx, hE'card] at hmul
    omega

  haveI : Fintype ↥(E' ⊓ E) := Fintype.ofFinite _
  haveI : Nontrivial ↥(E' ⊓ E) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card, hHcard]
      norm_num)
  obtain ⟨w, hw1⟩ := exists_ne (1 : ↥(E' ⊓ E))
  have hwE' : (w : G) ∈ E' := (Subgroup.mem_inf.mp w.2).1
  have hwE : (w : G) ∈ E := (Subgroup.mem_inf.mp w.2).2
  have hw1G : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwz : (w : G) ≠ S.z := fun h => hzE' (h ▸ hwE')
  have hwM : (w : G) ∈ S.M := S.QG_le_M (Subgroup.mem_inf.mp hwE).1
  have hτwM : τ * (w : G) ∈ S.M := S.M.mul_mem hτM hwM
  have hτw2 : (τ * (w : G)) * (τ * (w : G)) = 1 := by
    have hcomm := hE'comm τ hτE' (w : G) hwE'
    have hw2 := hE'elem (w : G) hwE'
    calc (τ * (w : G)) * (τ * (w : G)) = τ * ((w : G) * τ) * (w : G) := by group
      _ = τ * (τ * (w : G)) * (w : G) := by rw [hcomm]
      _ = (τ * τ) * ((w : G) * (w : G)) := by group
      _ = 1 := by rw [hττ, hw2, mul_one]
  have hwρ : S.ρ ⟨(w : G), hwM⟩ = 1 :=
    S.ρ_eq_one_of_mem_Q (S.mem_QG_iff.mp (Subgroup.mem_inf.mp hwE).1).2
  have hτwρ : S.ρ ⟨τ * (w : G), hτwM⟩ = S.ρ ⟨τ, hτM⟩ := by
    have h1 : (⟨τ * (w : G), hτwM⟩ : S.M) = ⟨τ, hτM⟩ * ⟨(w : G), hwM⟩ :=
      Subtype.ext rfl
    rw [h1, map_mul, hwρ, mul_one]
  have hτw_outer : S.ρ ⟨τ * (w : G), hτwM⟩ ∉ M0bar := by
    rw [hτwρ]
    exact hτM0
  obtain ⟨m', hm'⟩ := outer_involutions_conj S M0bar hw hcls hsq hτwM hτw_outer hτw2
    hτM hτM0 hττ
  have hconjZτw : IsConj S.z (τ * (w : G)) := by
    have h1 : IsConj (τ * (w : G)) τ := isConj_iff.mpr ⟨(m' : G), hm'⟩
    exact hconj.trans h1.symm
  obtain ⟨e, he, hew⟩ := Subgroup.mem_map.mp hwE'
  have hew' : hG * e * hG⁻¹ = (w : G) := by
    simpa [MulAut.conj_apply] using hew
  have hzE_mem : S.z ∈ E :=
    ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hτM).symm⟩
  have he' : S.z * e ∈ E := E.mul_mem hzE_mem he
  have hτw_eq : τ * (w : G) = hG * (S.z * e) * hG⁻¹ := by
    rw [show τ = hG * S.z * hG⁻¹ from hhz.symm, ← hew']
    group
  have he'_ne_z : S.z * e ≠ S.z := by
    intro h
    have he1 : e = 1 := by
      have := congrArg (fun x => S.z⁻¹ * x) h
      simpa [← mul_assoc] using this
    apply hw1G
    rw [← hew', he1]
    group
  have he'_notconj : ¬ IsConj (S.z * e) S.z := by
    intro hce
    have hz_eq : S.z * e = S.z :=
      hQz ⟨τ, hτM⟩ hτM0 (S.z * e) (Subgroup.mem_inf.mp he').1 hce
        (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp he').2)
    exact he'_ne_z hz_eq
  have he'_conj_of : IsConj S.z (τ * (w : G)) → IsConj (S.z * e) S.z := by
    intro h
    have h1 : IsConj (S.z * e) (τ * (w : G)) :=
      isConj_iff.mpr ⟨hG, hτw_eq.symm⟩
    exact h1.trans h.symm
  exact he'_notconj (he'_conj_of hconjZτw)

private theorem isSylowIn_centralizer_and_center_inf_zConj (hw : S.width = 3)
    (hcls : ∀ u ∈ S.Mbar, u ∉ M0bar → u * u = 1 → ∀ u' ∈ S.Mbar, u' ∉ M0bar →
      u' * u' = 1 → ∃ k ∈ S.Mbar, k * u * k⁻¹ = u')
    (h16 : ∀ w ∈ M0bar, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16)
    (hsq : ∀ y : S.M, S.ρ y ∉ M0bar → (y : G) * y = 1 →
      Nat.card {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} = 16 ∧
      Nat.card (CQ S (y : G)) = 8 ∧ ∀ x ∈ CQ S (y : G), x * x = 1)
    (hQz : ∀ y : S.M, S.ρ y ∉ M0bar → ∀ e ∈ S.QG, IsConj e S.z → e * y = y * e →
      e = S.z)
    (hsq2 : ∀ y : S.M, S.ρ y ∉ M0bar → ((y : G) * y = 1 ∨ (y : G) * y = S.z) →
      ∀ w : S.M, S.ρ w ∈ M0bar → S.ρ w ≠ 1 → S.ρ w * S.ρ w = 1 →
        S.ρ w * S.ρ y = S.ρ y * S.ρ w →
        ∃ x ∈ S.QG ⊓ Subgroup.centralizer ({(y : G)} : Set G),
          (w : G) * x * (w : G)⁻¹ ≠ x ∧ (w : G) * x * (w : G)⁻¹ ≠ x * S.z)
    {τ : G} (hτM : τ ∈ S.M) (hτM0 : S.ρ ⟨τ, hτM⟩ ∉ M0bar) (hττ : τ * τ = 1)
    (hEcard : Nat.card (CQ S τ) = 8) (hEelem : ∀ x ∈ CQ S τ, x * x = 1)
    (hA : ¬ IsConj S.z τ) (T₁ : Subgroup G) (hT₁ : IsSylowIn 2 T₁ (CM S τ)) :
    (∀ x : T₁, x ∈ Subgroup.center T₁ → IsConj S.z (x : G) → (x : G) = S.z) ∧
      IsSylowIn 2 T₁ (Subgroup.centralizer ({τ} : Set G)) := by
  have hτT₁ : τ ∈ T₁ := by
    have hNle : Subgroup.zpowers τ ≤ CM S τ := by
      intro x hx
      rcases (CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self hττ).mp hx with
        h1 | h2
      · rw [h1]
        exact ⟨S.M.one_mem, mem_centralizer_singleton_iff.mpr (by simp)⟩
      · rw [h2]
        exact ⟨hτM, mem_centralizer_singleton_iff.mpr (by rw [hττ])⟩
    have hN2 : IsPGroup 2 (Subgroup.zpowers τ) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by
        rw [Nat.card_zpowers]
        simpa [pow_two] using orderOf_dvd_of_pow_eq_one (by rwa [pow_two]))
    have hNnormal : ∀ c ∈ CM S τ, ∀ n ∈ Subgroup.zpowers τ,
        c * n * c⁻¹ ∈ Subgroup.zpowers τ := by
      intro c hc n hn
      have hcc : c * τ = τ * c :=
        mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
      rcases (CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self hττ).mp hn with
        h1 | h2
      · rw [h1, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h2, show c * τ * c⁻¹ = τ by rw [hcc]; group]
        exact Subgroup.mem_zpowers τ
    exact CFSG.LargeExtraspecial.GLR.SylowIn.le_of_normal hT₁ hNle hN2 hNnormal
      (Subgroup.mem_zpowers τ)
  have hEnormal : ∀ c ∈ CM S τ, ∀ e ∈ CQ S τ, c * e * c⁻¹ ∈ CQ S τ := by
    intro c hc e he
    have hcM : c ∈ S.M := (Subgroup.mem_inf.mp hc).1
    have hcent : c * e * c⁻¹ ∈ Subgroup.centralizer ({τ} : Set G) :=
      (Subgroup.centralizer ({τ} : Set G)).mul_mem
        ((Subgroup.centralizer ({τ} : Set G)).mul_mem
          (Subgroup.mem_inf.mp hc).2 (Subgroup.mem_inf.mp he).2)
        ((Subgroup.centralizer ({τ} : Set G)).inv_mem (Subgroup.mem_inf.mp hc).2)
    exact ⟨S.conj_mem_QG hcM (Subgroup.mem_inf.mp he).1, hcent⟩
  have hE2 : IsPGroup 2 (CQ S τ) := (S.isPGroup_QG).to_le inf_le_left
  have hEleT₁ : CQ S τ ≤ T₁ :=
    CFSG.LargeExtraspecial.GLR.SylowIn.le_of_normal hT₁
      (fun x hx => ⟨S.QG_le_M hx.1, hx.2⟩) hE2 hEnormal
  have hzE : S.z ∈ CQ S τ :=
    ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hτM).symm⟩
  have hzT₁ : S.z ∈ T₁ := hEleT₁ hzE
  have hZ : ∀ x : T₁, x ∈ Subgroup.center T₁ → IsConj S.z (x : G) → (x : G) = S.z := by
    intro x hxcenter hxconj
    have hxT : (x : G) ∈ T₁ := x.2
    have hxM : (x : G) ∈ S.M := (CFSG.LargeExtraspecial.GLR.SylowIn.le hT₁ hxT).1
    have hxord : orderOf (x : G) = 2 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hxconj
      rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, S.orderOf_z]
    have hx2 : (x : G) * (x : G) = 1 := by
      rw [← pow_two, ← hxord, pow_orderOf_eq_one]
    have hxcommτ : (x : G) * τ = τ * (x : G) := by
      have h := mem_center_iff.mp hxcenter ⟨τ, hτT₁⟩
      exact congrArg Subtype.val h.symm
    by_cases hxQ : (x : G) ∈ S.QG
    · exact hQz ⟨τ, hτM⟩ hτM0 (x : G) hxQ hxconj.symm hxcommτ
    · by_cases hxM0 : (x : G) ∈ M0G S M0bar
      · have hxM0rho : S.ρ ⟨(x : G), hxM⟩ ∈ M0bar :=
          (mem_M0G_iff_rho S M0bar hxM).mp hxM0
        have hxρne1 : S.ρ ⟨(x : G), hxM⟩ ≠ 1 := fun h =>
          hxQ (S.mem_QG_iff.mpr ⟨hxM, (rho_eq_one_iff_mem_Q S ⟨x, hxM⟩).mp h⟩)
        have hxρ2 : S.ρ ⟨(x : G), hxM⟩ * S.ρ ⟨(x : G), hxM⟩ = 1 := by
          rw [← map_mul, show (⟨(x : G), hxM⟩ : S.M) * ⟨(x : G), hxM⟩ = 1 from
            Subtype.ext hx2, map_one]
        have hcommρ : S.ρ ⟨(x : G), hxM⟩ * S.ρ ⟨τ, hτM⟩ =
            S.ρ ⟨τ, hτM⟩ * S.ρ ⟨(x : G), hxM⟩ := by
          rw [← map_mul, ← map_mul,
            show (⟨(x : G), hxM⟩ : S.M) * ⟨τ, hτM⟩ = ⟨τ, hτM⟩ * ⟨(x : G), hxM⟩ from
              Subtype.ext hxcommτ]
        obtain ⟨e, he, hne1, -⟩ := hsq2 ⟨τ, hτM⟩ hτM0 (Or.inl hττ)
          ⟨(x : G), hxM⟩ hxM0rho hxρne1 hxρ2 hcommρ
        have heT : e ∈ T₁ := hEleT₁ he
        have hxcomm : x * e * x⁻¹ = e := by
          have h := mem_center_iff.mp hxcenter ⟨e, heT⟩
          have h' := congrArg Subtype.val h
          have h1 : (e * (x : G)) * (x : G)⁻¹ = e := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
          have hxe : (x : G) * e = e * (x : G) := h'.symm
          rw [hxe]
          exact h1
        exact absurd hxcomm hne1
      · have hxM0rho : S.ρ ⟨(x : G), hxM⟩ ∉ M0bar := fun h =>
          hxM0 ((mem_M0G_iff_rho S M0bar hxM).mpr h)
        obtain ⟨m, hm⟩ := outer_involutions_conj S M0bar hw hcls hsq hτM hτM0 hττ
          hxM hxM0rho hx2
        exact absurd (hxconj.trans (isConj_iff.mpr ⟨(m : G), hm⟩).symm) hA
  refine ⟨hZ, ?_⟩
  refine CFSG.LargeExtraspecial.GLR.SylowIn.of_normalizer hT₁ inf_le_right ?_
  intro P hPC hP2 s hsP hsN
  have hsC : s ∈ Subgroup.centralizer ({τ} : Set G) := hPC hsP
  have hszT : s * S.z * s⁻¹ ∈ T₁ :=
    (mem_normalizer_iff.mp hsN S.z).mp hzT₁
  have hszCenter : (⟨s * S.z * s⁻¹, hszT⟩ : T₁) ∈ Subgroup.center T₁ := by
    refine mem_center_iff.mpr fun t => ?_
    have ht' : s⁻¹ * (t : G) * s ∈ T₁ := by
      have := (mem_normalizer_iff.mp (inv_mem hsN) (t : G)).mp t.2
      rwa [inv_inv] at this
    have hcomm : S.z * (s⁻¹ * (t : G) * s) = (s⁻¹ * (t : G) * s) * S.z :=
      (S.z_comm (CFSG.LargeExtraspecial.GLR.SylowIn.le hT₁ ht').1).symm
    apply Subtype.ext
    calc (t : G) * (s * S.z * s⁻¹) = s * ((s⁻¹ * (t : G) * s) * S.z) * s⁻¹ := by group
      _ = s * (S.z * (s⁻¹ * (t : G) * s)) * s⁻¹ := by rw [← hcomm]
      _ = (s * S.z * s⁻¹) * (t : G) := by group
  have hszeq : (⟨s * S.z * s⁻¹, hszT⟩ : T₁) = ⟨S.z, hzT₁⟩ :=
    Subtype.ext (hZ ⟨s * S.z * s⁻¹, hszT⟩ hszCenter (isConj_iff.mpr ⟨s, rfl⟩))
  have hszEq : s * S.z * s⁻¹ = S.z := congrArg Subtype.val hszeq
  have hsM : s ∈ S.M := by
    refine (S.mem_M_iff).mpr ?_
    calc s * S.z = s * S.z * s⁻¹ * s := by group
      _ = S.z * s := by rw [hszEq]
  exact ⟨hsM, hsC⟩

private theorem isSylowIn_map_conj {p : ℕ} {P H : Subgroup G} (h : IsSylowIn p P H) (g : G) :
    IsSylowIn p (P.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective P H (MulAut.conj g).injective]
  exact h.2.2

private theorem exists_conj_eq_of_isSylowIn {p : ℕ} [Fact p.Prime] [Finite G] {P Q H : Subgroup G}
    (hP : IsSylowIn p P H) (hQ : IsSylowIn p Q H) :
    ∃ g ∈ H, P.map (MulAut.conj g).toMonoidHom = Q := by
  have hPidx : ¬ p ∣ (P.subgroupOf H).index := by
    simpa [Subgroup.relIndex] using hP.2.2
  have hQidx : ¬ p ∣ (Q.subgroupOf H).index := by
    simpa [Subgroup.relIndex] using hQ.2.2
  let P' : Sylow p H := (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).toSylow hPidx
  let Q' : Sylow p H := (hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm).toSylow hQidx
  haveI : Finite (Sylow p H) :=
    Finite.of_injective (fun S : Sylow p H => (S : Set H))
      (fun S T h => Sylow.ext (by
        ext x
        exact Set.ext_iff.mp h x))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' Q'
  have hsub : (P' : Subgroup H).map (MulAut.conj (g : H)).toMonoidHom = (Q' : Subgroup H) := by
    have h := congrArg (fun S : Sylow p H => (S : Subgroup H)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    convert h using 2
    ext x
    rfl
  have hP' : (P' : Subgroup H) = P.subgroupOf H := rfl
  have hQ' : (Q' : Subgroup H) = Q.subgroupOf H := rfl
  have hleft : ((P' : Subgroup H).map (MulAut.conj (g : H)).toMonoidHom).map H.subtype =
      P.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Subgroup.map_map]
    have hcomp : H.subtype.comp (MulAut.conj (g : H)).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hP', Subgroup.map_subgroupOf_eq_of_le hP.1]
  refine ⟨(g : G), g.2, ?_⟩
  calc P.map (MulAut.conj (g : G)).toMonoidHom
      = ((P' : Subgroup H).map (MulAut.conj (g : H)).toMonoidHom).map H.subtype :=
        hleft.symm
    _ = (Q' : Subgroup H).map H.subtype := by rw [hsub]
    _ = Q := by rw [hQ', Subgroup.map_subgroupOf_eq_of_le hQ.1]

private theorem map_centralizer_conj {y g : G} :
    (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.mp hc
    calc (g * c * g⁻¹) * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
      _ = g * (y * c) * g⁻¹ := by rw [h]
      _ = (g * y * g⁻¹) * (g * c * g⁻¹) := by group
  · intro hz
    have h := mem_centralizer_singleton_iff.mp hz
    refine ⟨g⁻¹ * z * g, ?_, ?_⟩
    · refine mem_centralizer_singleton_iff.mpr ?_
      calc (g⁻¹ * z * g) * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [h]
        _ = y * (g⁻¹ * z * g) := by group
    · show g * (g⁻¹ * z * g) * g⁻¹ = z
      group

end PGLData

open PGLData

theorem false_of_pglData {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 3) (M0bar : Subgroup S.O) (hM0 : M0bar ≤ S.Mbar)
    (hidx : M0bar.relIndex S.Mbar = 2)
    (hcls : ∀ u ∈ S.Mbar, u ∉ M0bar → u * u = 1 → ∀ u' ∈ S.Mbar, u' ∉ M0bar →
      u' * u' = 1 → ∃ k ∈ S.Mbar, k * u * k⁻¹ = u')
    (h12 : ∀ u ∈ S.Mbar, u ∉ M0bar → u * u = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O)) = 12 ∧
      ∀ N : Subgroup S.O, N ≤ S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O) →
        (∀ c ∈ S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O), ∀ n ∈ N,
          c * n * c⁻¹ ∈ N) →
        IsPGroup 2 N → N ≤ Subgroup.zpowers u)
    (h16 : ∀ w ∈ M0bar, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16)
    (hQz : ∀ y : S.M, S.ρ y ∉ M0bar → ∀ e ∈ S.QG, IsConj e S.z → e * y = y * e →
      e = S.z)
    (hSigma : ((∃ τ : S.M, S.ρ τ ∉ M0bar ∧ τ * τ = 1) ∧
        ∀ τ : S.M, S.ρ τ ∉ M0bar → τ * τ = 1 →
          Nat.card {x : G // x ∈ S.QG ∧ ((τ : G) * x) * ((τ : G) * x) = 1} = 16 ∧
          Nat.card ↥(S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G)) = 8 ∧
          ∀ x ∈ S.QG ⊓ Subgroup.centralizer ({(τ : G)} : Set G), x * x = 1) ∨
      ((∀ y : S.M, S.ρ y ∉ M0bar → y * y ≠ 1) ∧
        ∃ s : S.M, S.ρ s ∉ M0bar ∧ (s : G) * s = S.z))
    (hSigma2 : ∀ y : S.M, S.ρ y ∉ M0bar → ((y : G) * y = 1 ∨ (y : G) * y = S.z) →
      ∀ w : S.M, S.ρ w ∈ M0bar → S.ρ w ≠ 1 → S.ρ w * S.ρ w = 1 →
        S.ρ w * S.ρ y = S.ρ y * S.ρ w →
        ∃ x ∈ S.QG ⊓ Subgroup.centralizer ({(y : G)} : Set G),
          (w : G) * x * (w : G)⁻¹ ≠ x ∧ (w : G) * x * (w : G)⁻¹ ≠ x * S.z) :
    False := by
  classical
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, -, b, -, hab⟩ := S.exists_not_commute
    exact ⟨a, b, hab⟩
  rcases hSigma with h0 | h1
  · obtain ⟨⟨τ, hτM0, hττS⟩, hsq⟩ := h0
    have hτM : (τ : G) ∈ S.M := τ.2
    have hττ : (τ : G) * (τ : G) = 1 := by
      simpa using congrArg (fun t : S.M => (t : G)) hττS
    have hsqCQ : ∀ y : S.M, S.ρ y ∉ M0bar → (y : G) * y = 1 →
        Nat.card {x : G // x ∈ S.QG ∧ ((y : G) * x) * ((y : G) * x) = 1} = 16 ∧
        Nat.card (CQ S (y : G)) = 8 ∧ ∀ x ∈ CQ S (y : G), x * x = 1 := by
      intro y hy1 hy2
      obtain ⟨hc, hcard', helem'⟩ := hsq y hy1 (Subtype.ext hy2)
      exact ⟨hc, by simpa [CQ] using hcard', by simpa [CQ] using helem'⟩
    obtain ⟨hcount, hcard, hEelem⟩ := hsqCQ τ hτM0 hττ
    have hA : ¬ IsConj S.z (τ : G) :=
      not_isConj_z_of_outer_involution S M0bar hw hcls h12 h16 hsqCQ hQz
        hτM hτM0 hττ hcard hEelem hcount
    have hP2 : IsPGroup 2 (Subgroup.zpowers (τ : G)) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by
        rw [Nat.card_zpowers]
        simpa [pow_two] using orderOf_dvd_of_pow_eq_one (by rwa [pow_two]))
    obtain ⟨T, hPT, hT⟩ := CFSG.LargeExtraspecial.GLR.exists_isSylowIn_le
      (H := S.M) (P := Subgroup.zpowers (τ : G)) (Subgroup.zpowers_le.mpr hτM) hP2
    have hτT : (τ : G) ∈ T := hPT (Subgroup.mem_zpowers (τ : G))
    have hτM0G : (τ : G) ∉ M0G S M0bar := fun h =>
      hτM0 ((mem_M0G_iff_rho S M0bar hτM).mp h)
    have hTnotM0 : ¬ T ≤ M0G S M0bar := fun h => hτM0G (h hτT)
    let U : Subgroup G := T ⊓ M0G S M0bar
    have hUT : U ≤ T := inf_le_left
    have hUidx : U.relIndex T = 2 :=
      relIndex_inf_M0G S M0bar hT.1 hidx hTnotM0
    have hTtop : IsSylowIn 2 T ⊤ := CFSG.LargeExtraspecial.GLR.Config.sylowIn_top hT
    have hTidx : ¬ 2 ∣ T.index := by
      have h := hTtop.2.2
      simpa [Subgroup.relIndex_top_right] using h
    have hgU : (τ : G) ∉ U := fun h => hτM0G h.2
    have hd : (1 : G) * (1 : G) = 1 := by simp
    have hdU : ∀ x : G, x⁻¹ * (1 : G) * x ∈ T → x⁻¹ * (1 : G) * x ∈ U := by
      intro x hx
      simpa using hx
    obtain ⟨x, hxU, hext⟩ :=
      CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup
        hnonab hT.2.1 hTidx hUT hUidx hτT hgU hττ hd hdU
    let y : G := x⁻¹ * (τ : G) * x
    have hyU : y ∈ U := hxU
    have hyM : y ∈ S.M := hT.1 hxU.1
    have hxyτ : x * y * x⁻¹ = (τ : G) := by
      rw [show y = x⁻¹ * (τ : G) * x from rfl]
      group
    have hS₂ : IsSylowIn 2 ((T ⊓ Subgroup.centralizer ({y} : Set G)).map
        (MulAut.conj x).toMonoidHom) (Subgroup.centralizer ({(τ : G)} : Set G)) := by
      have h := isSylowIn_map_conj (p := 2) (P := T ⊓ Subgroup.centralizer ({y} : Set G))
        (H := Subgroup.centralizer ({y} : Set G)) hext x
      rwa [map_centralizer_conj (y := y) (g := x), hxyτ] at h
    obtain ⟨T₁, -, hT₁⟩ := CFSG.LargeExtraspecial.GLR.exists_isSylowIn_le
      (H := CM S (τ : G)) (P := ⊥) (bot_le) (IsPGroup.of_subsingleton 2 _)
    obtain ⟨hZ, hT₁G⟩ :=
      isSylowIn_centralizer_and_center_inf_zConj S M0bar hw hcls h16 hsqCQ hQz hSigma2
        hτM hτM0 hττ hcard hEelem hA T₁ hT₁
    obtain ⟨c, hcC, hcMap⟩ := exists_conj_eq_of_isSylowIn (p := 2) hT₁G hS₂
    have hzT : S.z ∈ T :=
      CFSG.LargeExtraspecial.GLR.Config.QG_le_of_sylowIn hT S.z_mem_QG
    have hzy : S.z ∈ Subgroup.centralizer ({y} : Set G) :=
      mem_centralizer_singleton_iff.mpr (S.z_comm hyM).symm
    let z₂ : G := x * S.z * x⁻¹
    have hz₂S₂ : z₂ ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)).map
        (MulAut.conj x).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨S.z, ?_, ?_⟩
      · exact ⟨hzT, hzy⟩
      · rfl
    have hz₂center : ∀ s ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)).map
        (MulAut.conj x).toMonoidHom, z₂ * s = s * z₂ := by
      rintro s ⟨t, ht, rfl⟩
      have hzt : S.z * t = t * S.z := (S.z_comm (hT.1 ht.1)).symm
      calc (x * S.z * x⁻¹) * (x * t * x⁻¹) = x * (S.z * t) * x⁻¹ := by group
        _ = x * (t * S.z) * x⁻¹ := by rw [hzt]
        _ = (x * t * x⁻¹) * (x * S.z * x⁻¹) := by group
    have hz₂S₂' : z₂ ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)).map
        (MulAut.conj x).toMonoidHom := hz₂S₂
    rw [← hcMap] at hz₂S₂'
    obtain ⟨z₁, hz₁T₁, hz₁eq⟩ := Subgroup.mem_map.mp hz₂S₂'
    have hz₁center : (⟨z₁, hz₁T₁⟩ : T₁) ∈ Subgroup.center T₁ := by
      refine mem_center_iff.mpr fun t => ?_
      apply Subtype.ext
      have hct : c * (t : G) * c⁻¹ ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)).map
          (MulAut.conj x).toMonoidHom := by
        rw [← hcMap]
        simpa [MulAut.conj_apply] using
          Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom t.2
      have hcomm := hz₂center _ hct
      have hz₂eq : z₂ = c * z₁ * c⁻¹ := hz₁eq.symm
      calc (t : G) * z₁ = c⁻¹ * (c * (t : G) * c⁻¹) * c * z₁ * c⁻¹ * c := by group
        _ = c⁻¹ * ((c * (t : G) * c⁻¹) * (c * z₁ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * z₁ * c⁻¹) * (c * (t : G) * c⁻¹)) * c := by rw [← hz₂eq, ← hcomm]
        _ = z₁ * (t : G) := by group
    have hz₁conj : IsConj S.z z₁ := by
      have h1 : IsConj S.z z₂ := by
        refine isConj_iff.mpr ⟨x, ?_⟩
        rw [show z₂ = x * S.z * x⁻¹ from rfl]
      have hz₁eqG : c * z₁ * c⁻¹ = z₂ := by
        simpa [MulAut.conj_apply] using hz₁eq
      have h2 : IsConj z₂ z₁ := by
        refine isConj_iff.mpr ⟨c⁻¹, ?_⟩
        show c⁻¹ * z₂ * (c⁻¹)⁻¹ = z₁
        rw [← hz₁eqG]
        group
      exact h1.trans h2
    have hz₁eqz : z₁ = S.z := hZ ⟨z₁, hz₁T₁⟩ hz₁center hz₁conj
    have hcz : c * S.z * c⁻¹ = z₂ := by
      rw [← hz₁eqz]
      exact hz₁eq
    have hmM : c⁻¹ * x ∈ S.M := by
      refine (S.mem_M_iff).mpr ?_
      calc (c⁻¹ * x) * S.z = c⁻¹ * (x * S.z) := by group
        _ = c⁻¹ * (z₂ * x) := by
            rw [show z₂ = x * S.z * x⁻¹ from rfl]
            group
        _ = c⁻¹ * (c * S.z * c⁻¹) * x := by rw [← hcz]; group
        _ = S.z * (c⁻¹ * x) := by group
    have hmy : (⟨c⁻¹ * x, hmM⟩ : S.M)⁻¹ * (⟨τ, hτM⟩ : S.M) *
        (⟨c⁻¹ * x, hmM⟩ : S.M) = ⟨y, hyM⟩ := by
      have hcτ : c * (τ : G) * c⁻¹ = (τ : G) := by
        rw [mem_centralizer_singleton_iff.mp hcC]
        group
      apply Subtype.ext
      show (c⁻¹ * x)⁻¹ * (τ : G) * (c⁻¹ * x) = y
      rw [show y = x⁻¹ * (τ : G) * x from rfl]
      calc (c⁻¹ * x)⁻¹ * (τ : G) * (c⁻¹ * x)
          = x⁻¹ * (c * (τ : G) * c⁻¹) * x := by group
        _ = x⁻¹ * (τ : G) * x := by rw [hcτ]
    have hyM0' : y ∈ M0G S M0bar := hyU.2
    have hyM0 : y ∉ M0G S M0bar := by
      intro hyM0''
      have hρy : S.ρ ⟨y, hyM⟩ ∈ M0bar := (mem_M0G_iff_rho S M0bar hyM).mp hyM0''
      have hρeq : S.ρ ⟨c⁻¹ * x, hmM⟩ * S.ρ ⟨y, hyM⟩ *
          (S.ρ ⟨c⁻¹ * x, hmM⟩)⁻¹ = S.ρ ⟨(τ : G), hτM⟩ := by
        have h1 : (⟨y, hyM⟩ : S.M) =
            (⟨c⁻¹ * x, hmM⟩ : S.M)⁻¹ * ⟨τ, hτM⟩ * (⟨c⁻¹ * x, hmM⟩ : S.M) :=
          hmy.symm
        rw [h1, map_mul, map_mul, map_inv]
        group
      have hM0norm : (M0bar.subgroupOf S.Mbar).Normal :=
        Subgroup.normal_of_index_eq_two (by simpa [Subgroup.relIndex] using hidx)
      have hconj := hM0norm.conj_mem
        (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar)
        (show (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar) ∈
          M0bar.subgroupOf S.Mbar from hρy)
        (⟨S.ρ ⟨c⁻¹ * x, hmM⟩, ⟨⟨c⁻¹ * x, hmM⟩, rfl⟩⟩ : S.Mbar)
      have : S.ρ ⟨(τ : G), hτM⟩ ∈ M0bar := by
        rw [← hρeq]
        simpa [Subgroup.mem_subgroupOf] using hconj
      exact hτM0 this
    exact hyM0 hyM0'
  · obtain ⟨hnoinv, ⟨s, hsM0, hssq⟩⟩ := h1
    have hsM : (s : G) ∈ S.M := s.2
    have hsz : (s : G) * (s : G) = S.z := hssq
    have hsz2 : (s : G) ^ 2 = S.z := by rw [pow_two, hssq]
    have hs4 : (s : G) ^ 4 = 1 := by
      calc (s : G) ^ 4 = ((s : G) ^ 2) ^ 2 := by
            simpa using (pow_mul (s : G) 2 2)
        _ = 1 := by rw [hsz2, pow_two, S.z_mul_z]
    have hP2 : IsPGroup 2 (Subgroup.zpowers (s : G)) :=
      IsPGroup.of_card_dvd_pow (n := 2) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hs4)
    obtain ⟨T, hPT, hT⟩ := CFSG.LargeExtraspecial.GLR.exists_isSylowIn_le
      (H := S.M) (P := Subgroup.zpowers (s : G)) (Subgroup.zpowers_le.mpr hsM) hP2
    have hsT : (s : G) ∈ T := hPT (Subgroup.mem_zpowers (s : G))
    have hsM0G : (s : G) ∉ M0G S M0bar := fun h =>
      hsM0 ((mem_M0G_iff_rho S M0bar hsM).mp h)
    have hTnotM0 : ¬ T ≤ M0G S M0bar := fun h => hsM0G (h hsT)
    let U : Subgroup G := T ⊓ M0G S M0bar
    have hUT : U ≤ T := inf_le_left
    have hUidx : U.relIndex T = 2 :=
      relIndex_inf_M0G S M0bar hT.1 hidx hTnotM0
    have hTtop : IsSylowIn 2 T ⊤ := CFSG.LargeExtraspecial.GLR.Config.sylowIn_top hT
    have hTidx : ¬ 2 ∣ T.index := by
      have h := hTtop.2.2
      simpa [Subgroup.relIndex_top_right] using h
    have hgU : (s : G) ∉ U := fun h => hsM0G h.2
    have hd : S.z * S.z = 1 := S.z_mul_z
    have hdU : ∀ x : G, x⁻¹ * S.z * x ∈ T → x⁻¹ * S.z * x ∈ U := by
      intro x hxT
      have hxM : x⁻¹ * S.z * x ∈ S.M := hT.1 hxT
      by_contra hnotU
      have hout : S.ρ ⟨x⁻¹ * S.z * x, hxM⟩ ∉ M0bar := fun h =>
        hnotU ⟨hxT, (mem_M0G_iff_rho S M0bar hxM).mpr h⟩
      have hsq : (⟨x⁻¹ * S.z * x, hxM⟩ : S.M) * ⟨x⁻¹ * S.z * x, hxM⟩ = 1 := by
        apply Subtype.ext
        calc (x⁻¹ * S.z * x) * (x⁻¹ * S.z * x) = x⁻¹ * (S.z * S.z) * x := by group
          _ = 1 := by rw [S.z_mul_z]; group
      exact hnoinv ⟨x⁻¹ * S.z * x, hxM⟩ hout hsq
    obtain ⟨x, hxU, hext⟩ :=
      CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup
        hnonab hT.2.1 hTidx hUT hUidx hsT hgU hssq hd hdU
    let y : G := x⁻¹ * (s : G) * x
    have hyU : y ∈ U := hxU
    have hyM : y ∈ S.M := hT.1 hxU.1
    have hxys : x * y * x⁻¹ = (s : G) := by
      rw [show y = x⁻¹ * (s : G) * x from rfl]
      group
    have hS₂ : IsSylowIn 2 ((T ⊓ Subgroup.centralizer ({y} : Set G)).map
        (MulAut.conj x).toMonoidHom) (Subgroup.centralizer ({(s : G)} : Set G)) := by
      have h := isSylowIn_map_conj (p := 2) (P := T ⊓ Subgroup.centralizer ({y} : Set G))
        (H := Subgroup.centralizer ({y} : Set G)) hext x
      rwa [map_centralizer_conj (y := y) (g := x), hxys] at h
    obtain ⟨S₁, -, hS₁⟩ := CFSG.LargeExtraspecial.GLR.exists_isSylowIn_le
      (H := Subgroup.centralizer ({(s : G)} : Set G)) (P := ⊥) (bot_le)
      (IsPGroup.of_subsingleton 2 _)
    obtain ⟨c, hcC, hcMap⟩ := exists_conj_eq_of_isSylowIn (p := 2) hS₁ hS₂
    have hsCM : Subgroup.centralizer ({(s : G)} : Set G) ≤ S.M := by
      intro g hg
      refine (S.mem_M_iff).mpr ?_
      have hgs : g * (s : G) = (s : G) * g := mem_centralizer_singleton_iff.mp hg
      calc g * S.z = g * ((s : G) * (s : G)) := by rw [hssq]
        _ = (g * (s : G)) * (s : G) := by group
        _ = ((s : G) * g) * (s : G) := by rw [hgs]
        _ = (s : G) * (g * (s : G)) := by group
        _ = (s : G) * ((s : G) * g) := by rw [hgs]
        _ = ((s : G) * (s : G)) * g := by group
        _ = S.z * g := by rw [hssq]
    have hzT : S.z ∈ T :=
      CFSG.LargeExtraspecial.GLR.Config.QG_le_of_sylowIn hT S.z_mem_QG
    have hzy : S.z ∈ Subgroup.centralizer ({y} : Set G) :=
      mem_centralizer_singleton_iff.mpr (S.z_comm hyM).symm
    let z₂ : G := x * S.z * x⁻¹
    have hz₂S₂ : z₂ ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)).map
        (MulAut.conj x).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨S.z, ⟨hzT, hzy⟩, rfl⟩
    have hz₂center : ∀ t ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)).map
        (MulAut.conj x).toMonoidHom, z₂ * t = t * z₂ := by
      rintro t ⟨u, hu, rfl⟩
      have hzu : S.z * u = u * S.z := (S.z_comm (hT.1 hu.1)).symm
      calc (x * S.z * x⁻¹) * (x * u * x⁻¹) = x * (S.z * u) * x⁻¹ := by group
        _ = x * (u * S.z) * x⁻¹ := by rw [hzu]
        _ = (x * u * x⁻¹) * (x * S.z * x⁻¹) := by group
    rw [← hcMap] at hz₂S₂
    obtain ⟨z₁, hz₁S₁, hz₁eq⟩ := Subgroup.mem_map.mp hz₂S₂
    have hz₁S₁M : z₁ ∈ S.M := hsCM (hS₁.1 hz₁S₁)
    have hz₁center : (⟨z₁, hz₁S₁⟩ : S₁) ∈ Subgroup.center S₁ := by
      refine mem_center_iff.mpr fun t => ?_
      apply Subtype.ext
      have hct : c * (t : G) * c⁻¹ ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)).map
          (MulAut.conj x).toMonoidHom := by
        rw [← hcMap]
        simpa [MulAut.conj_apply] using
          Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom t.2
      have hcomm := hz₂center _ hct
      have hz₁eqG : c * z₁ * c⁻¹ = z₂ := by
        simpa [MulAut.conj_apply] using hz₁eq
      calc (t : G) * z₁ = c⁻¹ * ((c * (t : G) * c⁻¹) * (c * z₁ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * z₁ * c⁻¹) * (c * (t : G) * c⁻¹)) * c := by rw [hz₁eqG, hcomm]
        _ = z₁ * (t : G) := by group
    have hz₁conj : IsConj S.z z₁ := by
      have h1 : IsConj S.z z₂ := isConj_iff.mpr ⟨x, rfl⟩
      have h2 : IsConj z₂ z₁ := by
        refine isConj_iff.mpr ⟨c⁻¹, ?_⟩
        have hz₁eqG : c * z₁ * c⁻¹ = z₂ := by
          simpa [MulAut.conj_apply] using hz₁eq
        show c⁻¹ * z₂ * (c⁻¹)⁻¹ = z₁
        rw [← hz₁eqG]
        group
      exact h1.trans h2
    have hz₁2 : z₁ * z₁ = 1 := by
      obtain ⟨d, hd⟩ := isConj_iff.mp hz₁conj
      rw [← hd]
      calc (d * S.z * d⁻¹) * (d * S.z * d⁻¹) = d * (S.z * S.z) * d⁻¹ := by group
        _ = 1 := by rw [S.z_mul_z]; group
    have hz₁M0 : z₁ ∈ M0G S M0bar := by
      by_contra hnot
      have hout : S.ρ ⟨z₁, hz₁S₁M⟩ ∉ M0bar := fun h =>
        hnot ((mem_M0G_iff_rho S M0bar hz₁S₁M).mpr h)
      have hsq : (⟨z₁, hz₁S₁M⟩ : S.M) * ⟨z₁, hz₁S₁M⟩ = 1 := Subtype.ext hz₁2
      exact hnoinv ⟨z₁, hz₁S₁M⟩ hout hsq
    have hsC : (s : G) ∈ Subgroup.centralizer ({(s : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr rfl
    have hNs : Subgroup.zpowers (s : G) ≤ Subgroup.centralizer ({(s : G)} : Set G) :=
      Subgroup.zpowers_le.mpr hsC
    have hNsnorm : ∀ g ∈ Subgroup.centralizer ({(s : G)} : Set G),
        ∀ n ∈ Subgroup.zpowers (s : G), g * n * g⁻¹ ∈ Subgroup.zpowers (s : G) := by
      intro g hg n hn
      have hgs : g * (s : G) = (s : G) * g := mem_centralizer_singleton_iff.mp hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hconj : (MulAut.conj g) (s : G) = (s : G) := by
        rw [MulAut.conj_apply]
        rw [hgs]
        group
      have hpow : g * (s : G) ^ k * g⁻¹ = (s : G) ^ k := by
        calc g * (s : G) ^ k * g⁻¹ = (MulAut.conj g) ((s : G) ^ k) := rfl
          _ = ((MulAut.conj g) (s : G)) ^ k := by rw [map_zpow]
          _ = (s : G) ^ k := by rw [hconj]
      rw [hpow]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    have hsS₁ : (s : G) ∈ S₁ :=
      CFSG.LargeExtraspecial.GLR.SylowIn.le_of_normal hS₁ hNs hP2 hNsnorm
        (Subgroup.mem_zpowers (s : G))
    have hz₁eqz : z₁ = S.z := by
      by_cases hz₁Q : z₁ ∈ S.QG
      · have hz₁s : z₁ * (s : G) = (s : G) * z₁ :=
          (congrArg Subtype.val (mem_center_iff.mp hz₁center ⟨s, hsS₁⟩)).symm
        exact hQz ⟨s, hsM⟩ hsM0 z₁ hz₁Q hz₁conj.symm hz₁s
      · exfalso
        have hz₁M0rho : S.ρ ⟨z₁, hz₁S₁M⟩ ∈ M0bar :=
          (mem_M0G_iff_rho S M0bar hz₁S₁M).mp hz₁M0
        have hz₁ρne1 : S.ρ ⟨z₁, hz₁S₁M⟩ ≠ 1 := fun h =>
          hz₁Q (S.mem_QG_iff.mpr ⟨hz₁S₁M, (rho_eq_one_iff_mem_Q S ⟨z₁, hz₁S₁M⟩).mp h⟩)
        have hz₁ρ2 : S.ρ ⟨z₁, hz₁S₁M⟩ * S.ρ ⟨z₁, hz₁S₁M⟩ = 1 := by
          rw [← map_mul, show (⟨z₁, hz₁S₁M⟩ : S.M) * ⟨z₁, hz₁S₁M⟩ = 1 from
            Subtype.ext hz₁2, map_one]
        have hcommρ : S.ρ ⟨z₁, hz₁S₁M⟩ * S.ρ ⟨s, hsM⟩ =
            S.ρ ⟨s, hsM⟩ * S.ρ ⟨z₁, hz₁S₁M⟩ := by
          have hz₁s : z₁ * (s : G) = (s : G) * z₁ :=
            (congrArg Subtype.val (mem_center_iff.mp hz₁center ⟨s, hsS₁⟩)).symm
          rw [← map_mul, ← map_mul, show (⟨z₁, hz₁S₁M⟩ : S.M) * ⟨s, hsM⟩ =
            ⟨s, hsM⟩ * ⟨z₁, hz₁S₁M⟩ from Subtype.ext hz₁s]
        obtain ⟨e, he, hne, -⟩ := hSigma2 ⟨s, hsM⟩ hsM0 (Or.inr hssq)
          ⟨z₁, hz₁S₁M⟩ hz₁M0rho hz₁ρne1 hz₁ρ2 hcommρ
        have hCQs : CQ S (s : G) ≤ S₁ := by
          refine CFSG.LargeExtraspecial.GLR.SylowIn.le_of_normal hS₁
            (fun x hx => hx.2) ((S.isPGroup_QG).to_le inf_le_left) ?_
          intro g hg e he
          have hgC : g ∈ Subgroup.centralizer ({(s : G)} : Set G) := hg
          have hgM : g ∈ S.M := hsCM hgC
          let Cs : Subgroup G := Subgroup.centralizer ({(s : G)} : Set G)
          have hcent : g * e * g⁻¹ ∈ Cs :=
            Cs.mul_mem (Cs.mul_mem hgC (Subgroup.mem_inf.mp he).2)
              (Cs.inv_mem hgC)
          exact ⟨S.conj_mem_QG hgM (Subgroup.mem_inf.mp he).1, hcent⟩
        have heS₁ : e ∈ S₁ := hCQs he
        have hz₁comm : z₁ * e = e * z₁ := by
          have h := mem_center_iff.mp hz₁center ⟨e, heS₁⟩
          exact (congrArg Subtype.val h).symm
        have hcontra : z₁ * e * z₁⁻¹ = e := by
          have h := hz₁comm
          calc z₁ * e * z₁⁻¹ = (e * z₁) * z₁⁻¹ := by rw [h]
            _ = e := by rw [mul_assoc, mul_inv_cancel, mul_one]
        exact (hne hcontra).elim
    have hcz : c * S.z * c⁻¹ = z₂ := by
      rw [← hz₁eqz]
      simpa [MulAut.conj_apply] using hz₁eq
    have hmM : c⁻¹ * x ∈ S.M := by
      refine (S.mem_M_iff).mpr ?_
      calc (c⁻¹ * x) * S.z = c⁻¹ * (x * S.z) := by group
        _ = c⁻¹ * (z₂ * x) := by
            rw [show z₂ = x * S.z * x⁻¹ from rfl]
            group
        _ = c⁻¹ * (c * S.z * c⁻¹) * x := by rw [← hcz]; group
        _ = S.z * (c⁻¹ * x) := by group
    have hmy : (⟨c⁻¹ * x, hmM⟩ : S.M)⁻¹ * (⟨s, hsM⟩ : S.M) *
        (⟨c⁻¹ * x, hmM⟩ : S.M) = ⟨y, hyM⟩ := by
      have hcs : c * (s : G) * c⁻¹ = (s : G) := by
        rw [mem_centralizer_singleton_iff.mp hcC]
        group
      apply Subtype.ext
      show (c⁻¹ * x)⁻¹ * (s : G) * (c⁻¹ * x) = y
      rw [show y = x⁻¹ * (s : G) * x from rfl]
      calc (c⁻¹ * x)⁻¹ * (s : G) * (c⁻¹ * x)
          = x⁻¹ * (c * (s : G) * c⁻¹) * x := by group
        _ = x⁻¹ * (s : G) * x := by rw [hcs]
    have hyM0' : y ∈ M0G S M0bar := hyU.2
    have hyM0 : y ∉ M0G S M0bar := by
      intro hyM0''
      have hρy : S.ρ ⟨y, hyM⟩ ∈ M0bar := (mem_M0G_iff_rho S M0bar hyM).mp hyM0''
      have hρeq : S.ρ ⟨c⁻¹ * x, hmM⟩ * S.ρ ⟨y, hyM⟩ *
          (S.ρ ⟨c⁻¹ * x, hmM⟩)⁻¹ = S.ρ ⟨(s : G), hsM⟩ := by
        have h1 : (⟨y, hyM⟩ : S.M) =
            (⟨c⁻¹ * x, hmM⟩ : S.M)⁻¹ * ⟨s, hsM⟩ * (⟨c⁻¹ * x, hmM⟩ : S.M) :=
          hmy.symm
        rw [h1, map_mul, map_mul, map_inv]
        group
      have hM0norm : (M0bar.subgroupOf S.Mbar).Normal :=
        Subgroup.normal_of_index_eq_two (by simpa [Subgroup.relIndex] using hidx)
      have hconj := hM0norm.conj_mem
        (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar)
        (show (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar) ∈
          M0bar.subgroupOf S.Mbar from hρy)
        (⟨S.ρ ⟨c⁻¹ * x, hmM⟩, ⟨⟨c⁻¹ * x, hmM⟩, rfl⟩⟩ : S.Mbar)
      have : S.ρ ⟨(s : G), hsM⟩ ∈ M0bar := by
        rw [← hρeq]
        simpa [Subgroup.mem_subgroupOf] using hconj
      exact hsM0 this
    exact hyM0 hyM0'

end CFSG.GF2Type.Smith1979W3
