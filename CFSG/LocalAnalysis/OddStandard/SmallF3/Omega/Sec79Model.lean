module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.ClassicalInvolution.Balance.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem inducesTypeSome_sq_mem_centralizer {L : Subgroup G} (hctr : centerIn L = ⊥) {s : G}
    {n : ℕ} {ε : ℤˣ} {r : ℕ} {α : ℤˣ} (h : InducesTypeSome L s n ε r α) :
    s * s ∈ centralizer (L : Set G) := by
  obtain ⟨V, hAdd, hMod, hFin, Q, _hQ, e, x, _hfin, _hsign, hvia, htype⟩ := h
  letI := hAdd
  letI := hMod
  letI := hFin
  obtain ⟨y, hyx, _hyne, t, htt, _httype, hty⟩ := htype
  have hyy : y * y = 1 := by rw [← hty, ← map_mul, htt, map_one]
  have hsq : ∀ w : ProjOrth Q, projSimAct Q x (projSimAct Q x w) = w := by
    intro w
    rw [← hyx]
    simp only [projSimAct_projOrthToProjSim]
    rw [inv_eq_of_mul_eq_one_right hyy,
      show y * (y * w * y) * y = (y * y) * w * (y * y) by group, hyy]
    group
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : (z : G) ∈ centerIn L := ⟨z, hz, rfl⟩
    rw [hctr] at hz'
    exact Subtype.ext (by simpa using hz')
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  let l₀ : ↥L := ⟨l, hl⟩
  have hl1 : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hvia.1 l).mp hl
  have hl2 : s * (s * l * s⁻¹) * s⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hvia.1 (s * l * s⁻¹)).mp hl1
  let l₁ : ↥L := ⟨s * l * s⁻¹, hl1⟩
  let l₂ : ↥L := ⟨s * (s * l * s⁻¹) * s⁻¹, hl2⟩
  have he1 := hvia.2 l₀ l₁ rfl
  have he2 := hvia.2 l₁ l₂ rfl
  have heq : e (QuotientGroup.mk l₂) = e (QuotientGroup.mk l₀) := by
    apply Subtype.ext
    rw [he2, he1, hsq]
  have hmk : QuotientGroup.mk l₂ = QuotientGroup.mk l₀ := e.injective heq
  have hl2l : l₂ = l₀ := by
    have hmem : l₂ / l₀ ∈ Subgroup.center ↥L := QuotientGroup.eq_iff_div_mem.mp hmk
    rw [hcenter] at hmem
    exact div_eq_one.mp (by simpa using hmem)
  have hconj : (s * s) * l * (s * s)⁻¹ = l := by
    have h : s * (s * l * s⁻¹) * s⁻¹ = l := by
      have hval : (l₂ : G) = (l₀ : G) := congrArg Subtype.val hl2l
      simpa only [l₂, l₀, Subgroup.coe_mk] using hval
    calc (s * s) * l * (s * s)⁻¹ = s * (s * l * s⁻¹) * s⁻¹ := by group
      _ = l := h
  have hcomm : l * (s * s) = (s * s) * l := by
    have h : (s * s) * l = l * (s * s) := by
      calc (s * s) * l = (s * s) * l * (s * s)⁻¹ * (s * s) := by group
        _ = l * (s * s) := by rw [hconj]
    exact h.symm
  exact hcomm

theorem innerOn_of_hyp62At [Finite G] {L : Subgroup G} (hL : IsOm6P L) (hctr : centerIn L = ⊥)
    (hH : Hyp62At L) {s : G} {r : ℕ} {α : ℤˣ} (h : InducesTypeSome L s 6 1 r α) :
    InnerOn L s := by
  obtain ⟨V, hAdd, hMod, hFin, Q, hQ, e, x, hfin, hsign, hvia, htype⟩ := h
  letI := hAdd
  letI := hMod
  letI := hFin
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : (z : G) ∈ centerIn L := ⟨z, hz, rfl⟩
    rw [hctr] at hz'
    exact Subtype.ext (by simpa using hz')
  have hOpen : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hodd_le : oddCore ↥L ≤ Subgroup.center ↥L :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple hOpen
  have hodd : oddCore ↥L = ⊥ := le_bot_iff.mp (hcenter ▸ hodd_le)
  have hEq : oddCore ↥L = Subgroup.center ↥L := by rw [hodd, hcenter]
  let e' : ↥L ⧸ oddCore ↥L ≃* omegaProj hQ :=
    (QuotientGroup.quotientMulEquivOfEq hEq).trans e
  have he' : ∀ l : ↥L, e' (QuotientGroup.mk l) = e (QuotientGroup.mk l) := fun _ => rfl
  have hvia' : InducesViaP L (oddCore ↥L) hQ e' s x := by
    refine ⟨hvia.1, fun l l' hl => ?_⟩
    simp only [he']
    exact hvia.2 l l' hl
  have homega : SimInOmegaStar hQ x :=
    hH V Q hQ e' hfin hsign s x hvia' (SimHasType.simInGStar htype)
  obtain ⟨y, hy, hyx⟩ := homega
  obtain ⟨q, hq⟩ := e.surjective ⟨y, hy⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hl' : ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) = y :=
    congrArg Subtype.val hq
  have hconj : ∀ a : ↥L, s * (a : G) * s⁻¹ = (l : G) * (a : G) * (l : G)⁻¹ := by
    intro a
    have ha : s * (a : G) * s⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hvia.1 (a : G)).mp a.2
    let a₁ : ↥L := ⟨s * (a : G) * s⁻¹, ha⟩
    have h1 := hvia.2 a a₁ rfl
    have h2 : e (QuotientGroup.mk a₁) = e (QuotientGroup.mk (l * a * l⁻¹)) := by
      apply Subtype.ext
      rw [h1, ← hyx, projSimAct_projOrthToProjSim, ← hl']
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv,
        Subgroup.coe_mul, Subgroup.coe_inv]
    have h3 : QuotientGroup.mk a₁ = QuotientGroup.mk (l * a * l⁻¹) := e.injective h2
    have h4 : a₁ = l * a * l⁻¹ := by
      have hmem : a₁ / (l * a * l⁻¹) ∈ Subgroup.center ↥L :=
        QuotientGroup.eq_iff_div_mem.mp h3
      rw [hcenter] at hmem
      exact div_eq_one.mp (by simpa using hmem)
    simpa only [a₁, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv] using
      congrArg Subtype.val h4
  have hc : (l : G)⁻¹ * s ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hconj ⟨a, ha⟩
    have h' : (l : G)⁻¹ * s * a = a * ((l : G)⁻¹ * s) := by
      calc (l : G)⁻¹ * s * a = (l : G)⁻¹ * (s * a * s⁻¹) * s := by group
        _ = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * s := by rw [h]
        _ = a * ((l : G)⁻¹ * s) := by group
    exact h'.symm
  have hs : s = (l : G) * ((l : G)⁻¹ * s) := by group
  show s ∈ L ⊔ centralizer (L : Set G)
  rw [hs]
  exact Subgroup.mul_mem_sup l.2 hc

theorem sec79_not_inner_of_i1 [Finite G] (hP : Asc82Tab6P) {L : Subgroup G} (hL : IsOm6P L)
    {s : G} (hs2 : orderOf s = 2) (hsN : s ∈ normalizer (L : Set G))
    (h : ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) : ¬ InnerOn L s := by
  rintro hin
  have hnot : s ∉ centralizer (L : Set G) :=
    hP.nontrivial G L hL s hs2 hsN (Or.inr (Or.inr (Or.inl h)))
  have hiff := (hP.inner_iff G L hL s hs2 hsN).mp ⟨hin, hnot⟩
  rcases hiff with h4 | h2
  · exact (hP.excl G L hL s hs2 hsN 0 2 (by norm_num) (by norm_num) (by norm_num))
      (show KindP L s 0 from h4) (show KindP L s 2 from h)
  · exact (hP.excl G L hL s hs2 hsN 1 2 (by norm_num) (by norm_num) (by norm_num))
      (show KindP L s 1 from h2) (show KindP L s 2 from h)

theorem sec79_not_inner_of_i3 [Finite G] (hP : Asc82Tab6P) {L : Subgroup G} (hL : IsOm6P L)
    {s : G} (hs2 : orderOf s = 2) (hsN : s ∈ normalizer (L : Set G))
    (h : ∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) : ¬ InnerOn L s := by
  rintro hin
  have hnot : s ∉ centralizer (L : Set G) :=
    hP.nontrivial G L hL s hs2 hsN (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hiff := (hP.inner_iff G L hL s hs2 hsN).mp ⟨hin, hnot⟩
  rcases hiff with h4 | h2
  · exact (hP.excl G L hL s hs2 hsN 0 3 (by norm_num) (by norm_num) (by norm_num))
      (show KindP L s 0 from h4) (show KindP L s 3 from h)
  · exact (hP.excl G L hL s hs2 hsN 1 3 (by norm_num) (by norm_num) (by norm_num))
      (show KindP L s 1 from h2) (show KindP L s 3 from h)

theorem sec79_hyp62_no_i1 [Finite G] (hP : Asc82Tab6P) {L : Subgroup G} (hL : IsOm6P L)
    (hH : Hyp62At L) {s : G} (hs2 : orderOf s = 2) (hsN : s ∈ normalizer (L : Set G)) :
    ¬ ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α := by
  rintro ⟨α, hα⟩
  exact (sec79_not_inner_of_i1 hP hL hs2 hsN ⟨α, hα⟩)
    (innerOn_of_hyp62At hL (hP.center_triv G L hL) hH hα)

theorem sec79_hyp62_no_i3 [Finite G] (hP : Asc82Tab6P) {L : Subgroup G} (hL : IsOm6P L)
    (hH : Hyp62At L) {s : G} (hs2 : orderOf s = 2) (hsN : s ∈ normalizer (L : Set G)) :
    ¬ ∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α := by
  rintro ⟨α, hα⟩
  exact (sec79_not_inner_of_i3 hP hL hs2 hsN ⟨α, hα⟩)
    (innerOn_of_hyp62At hL (hP.center_triv G L hL) hH hα)

end CFSG.OddStandard.SmallF3.Omega
