module

public import CFSG.LargeExtraspecial.S13EightA
public import CFSG.LargeExtraspecial.S13SevenE
public import CFSG.LargeExtraspecial.S13Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

omit [Finite G] in
theorem coe_mul_mul (m h : S.M) (g : G) : ((m * h : S.M) : G) * g = (m : G) * ((h : G) * g) := by
  rw [Subgroup.coe_mul, mul_assoc]

theorem ρ_pt (H : Hyp4 S g) (m p : S.M) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((p : G) * g * S.z * ((p : G) * g)⁻¹)) =
      S.cl (((m * p : S.M) : G) * g * S.z * (((m * p : S.M) : G) * g)⁻¹) := by
  rw [ρ_cl_conj_z S m (conj_mem_QG' S p.2 H.conj_mem), coe_mul_mul]

theorem ρ_mem_clSub (m p : S.M) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa ((p : G) * g))) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa (((m * p : S.M) : G) * g)) := by
  rw [coe_mul_mul]
  exact apply_mem_clSub_Qa_mul m ((p : G) * g) hv

theorem clSub_eq_of_pt_eq (H : Hyp4 S g) {p q : S.M}
    (h : S.cl ((p : G) * g * S.z * ((p : G) * g)⁻¹) = S.cl ((q : G) * g * S.z * ((q : G) * g)⁻¹)) :
    S.clSub (S.QG ⊓ S.Qa ((q : G) * g)) = S.clSub (S.QG ⊓ S.Qa ((p : G) * g)) :=
  clSub_eq_of_cl_eq (conj_mem_QG' S p.2 H.conj_mem) (conj_ne_z' S p.2 H.conj_ne)
    (conj_mem_QG' S q.2 H.conj_mem) h

theorem clSub_eq_of_pt_eq_base (H : Hyp4 S g) {p : S.M}
    (h : S.cl ((p : G) * g * S.z * ((p : G) * g)⁻¹) = S.cl (g * S.z * g⁻¹)) :
    S.clSub (S.QG ⊓ S.Qa ((p : G) * g)) = S.clSub (S.QG ⊓ S.Qa g) :=
  clSub_eq_of_cl_eq H.conj_mem H.conj_ne (conj_mem_QG' S p.2 H.conj_mem) h.symm

theorem mem_clSub_base_symm (H : Hyp4 S g) {p : S.M}
    (h : S.cl ((p : G) * g * S.z * ((p : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((p : G) * g)) := by
  have h1 := cl_mem_clSub_symm H (h₁ := 1) (h₂ := p)
    (by simp only [OneMemClass.coe_one, one_mul]; exact h)
  simp only [OneMemClass.coe_one, one_mul] at h1
  exact h1

namespace Hyp13

theorem inv_eq_of_mem_Lbar (H : Hyp4 S g) {p : S.M} {l : S.O} (hl : l ∈ S.Lbar ((p : G) * g)) :
    l⁻¹ = l :=
  (eq_inv_of_mul_eq_one_left (mul_self_of_mem_Lbar S (conj_mem_QG' S p.2 H.conj_mem) hl)).symm

theorem exists_pre_config (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {σ : S.O}
    (hσ : σ ∈ S.Lbar g) (hσE : σ ∉ Ebar S g K)
    (hpts : ∀ v ∈ Vt S g σ, v ≠ 0 → ∃ m : S.M, v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧
      σ ∈ S.Lbar ((m : G) * g) ∧ Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((m : G) * g)))
    (hVP : Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa g)) (h3 : finrank (ZMod 2) (Vt S g σ) = 3)
    {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) {c : S.M}
    (hcU : S.cl ((c : G) * g * S.z * ((c : G) * g)⁻¹) ∉
      Vt S g σ ⊔ (Vt S g σ).map (k : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap)
    (ha : S.cl (g * S.z * g⁻¹) ∈ perp S (Fbar S ((c : G) * g) K)) :
    ∃ me mF pX pU : S.M,
      (S.cl ((me : G) * g * S.z * ((me : G) * g)⁻¹) ∈ Vt S g σ ∧
        S.cl ((me : G) * g * S.z * ((me : G) * g)⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ∧
        σ ∈ S.Lbar ((me : G) * g) ∧ Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((me : G) * g))) ∧
      (S.cl ((mF : G) * g * S.z * ((mF : G) * g)⁻¹) ∈ Vt S g σ ∧
        σ ∈ S.Lbar ((mF : G) * g) ∧ Vt S g σ ≤ S.clSub (S.QG ⊓ S.Qa ((mF : G) * g))) ∧
      (S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∉ Vt S g σ ∧
        S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
        S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((me : G) * g)) ∧
        S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa ((mF : G) * g))) ∧
      (S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) ∧
        S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((mF : G) * g)) ∧
        S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa ((me : G) * g)) ∧
        S.cl (g * S.z * g⁻¹) ∈ perp S (Fbar S ((pU : G) * g) K) ∧
        Fbar S ((pU : G) * g) K ≠ Fbar S g K) := by
  obtain ⟨x, hxF, hxP, hxV, hWx, hcodim⟩ := Y.exists_x hCE hσ hσE hpts hVP hk hk1 hcU ha
  set V := Vt S g σ with hV
  set a := S.cl (g * S.z * g⁻¹) with hadef
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S Y.haQ Y.hne
  set W₀ := V ⊓ perp S (Fbar S ((c : G) * g) K) with hW₀
  obtain ⟨vf, hvfV, hvfx⟩ : ∃ v ∈ V, v ∉ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) := by
    by_contra hcon
    push Not at hcon
    have hσx := Y.mem_Lbar_of_le_clSub hσ hσE (U := V) (by omega) hpts hxV hcon
    exact hxV (cl_mem_Vt hσx)
  have hvf0 : vf ≠ 0 := fun h => hvfx (h ▸ zero_mem _)
  obtain ⟨mf, rfl, -, hVf⟩ := hpts vf hvfV hvf0
  have haW₀ : a ∈ W₀ := Submodule.mem_inf.mpr ⟨cl_a_mem_Vt hσ, ha⟩
  obtain ⟨ve, hveW₀, hvea⟩ : ∃ v ∈ W₀, v ∉ (ZMod 2) ∙ a := by
    by_contra hcon
    push Not at hcon
    have h1 := Submodule.finrank_mono (show W₀ ≤ (ZMod 2) ∙ a from fun v hv => hcon v hv)
    rw [finrank_span_singleton ha0] at h1
    omega
  have hve0 : ve ≠ 0 := fun h => hvea (h ▸ zero_mem _)
  have hveV : ve ∈ V := (Submodule.mem_inf.mp hveW₀).1
  have hex : ve ∈ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) := hWx hveW₀
  have hax : a ∈ S.clSub (S.QG ⊓ S.Qa ((x : G) * g)) := hWx haW₀
  obtain ⟨me, rfl, hσe, hVe⟩ := hpts ve hveV hve0
  set pe := S.cl ((me : G) * g * S.z * ((me : G) * g)⁻¹) with hpe
  set pf := S.cl ((mf : G) * g * S.z * ((mf : G) * g)⁻¹) with hpf
  set px := S.cl ((x : G) * g * S.z * ((x : G) * g)⁻¹) with hpx
  have hfe : pe ≠ pf := fun h => hvfx (h ▸ hex)
  obtain ⟨l, hl, hla, hle⟩ := exists_Lbar_fix_add Y.H (e := me) (f := mf) (hVf (cl_a_mem_Vt hσ))
    (hVf hveV) (fun h => by
      rcases mem_span_cl_iff.mp h with h | h
      · exact hve0 h
      · exact hfe h)
    (fun h => by
      rcases mem_span_cl_iff.mp h with h | h
      · apply hvea
        have h' : a = pe := eq_of_add_eq_zero_zmod2 h
        rw [h']
        exact Submodule.mem_span_singleton_self _
      · have h' : a + pe = pf := h
        exact hvfx (h' ▸ add_mem hax hex))
  have hll : l⁻¹ = l := inv_eq_of_mem_Lbar Y.H hl
  obtain ⟨ml, rfl⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar _ hl)
  have hf'V : pe + pf ∈ V := add_mem hveV hvfV
  have hf'0 : pe + pf ≠ 0 := fun h => hfe (eq_of_add_eq_zero_zmod2 h)
  obtain ⟨mF, hmF, hσF, hVF⟩ := hpts _ hf'V hf'0
  have hρe : ((S.ρ ml : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) pe =
      S.cl ((mF : G) * g * S.z * ((mF : G) * g)⁻¹) := by rw [hle, hmF]
  have hWlme : S.clSub (S.QG ⊓ S.Qa (((ml * me : S.M) : G) * g)) =
      S.clSub (S.QG ⊓ S.Qa ((mF : G) * g)) :=
    clSub_eq_of_pt_eq Y.H ((ρ_pt Y.H ml me).symm.trans hρe).symm
  have hWl1 : S.clSub (S.QG ⊓ S.Qa ((ml : G) * g)) = S.clSub (S.QG ⊓ S.Qa g) :=
    clSub_eq_of_pt_eq_base Y.H ((ρ_cl_conj_z S ml Y.haQ).symm.trans hla)
  set pU : S.M := ml * x with hpU
  have hpu : S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) =
      ((S.ρ ml : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) px := (ρ_pt Y.H ml x).symm
  have hxF' : px ∉ S.clSub (S.QG ⊓ S.Qa ((mF : G) * g)) := by
    intro h
    have h1 := cl_mem_clSub_symm Y.H h
    rw [← hmF] at h1
    exact hvfx (by simpa using sub_mem h1 hex)
  refine ⟨me, mF, x, pU, ⟨hveV, hvea, hσe, hVe⟩, ⟨hmF ▸ hf'V, hσF, hVF⟩,
    ⟨hxV, hxP, cl_mem_clSub_symm Y.H hex, hxF'⟩, ?_⟩
  have hua : S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [hpu, ← hWl1]
    exact apply_mem_clSub_Qa_mul ml g hxP
  have huF : S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((mF : G) * g)) := by
    rw [hpu, ← hWlme]
    exact ρ_mem_clSub ml me (cl_mem_clSub_symm Y.H hex)
  have hue : S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) ∉
      S.clSub (S.QG ⊓ S.Qa ((me : G) * g)) := by
    intro h
    apply hxF'
    have h1 := ρ_mem_clSub ml⁻¹ me h
    rw [hpu, map_inv, inv_apply_apply_O] at h1
    have hpt' : S.cl ((mF : G) * g * S.z * ((mF : G) * g)⁻¹) =
        S.cl (((ml⁻¹ * me : S.M) : G) * g * S.z * (((ml⁻¹ * me : S.M) : G) * g)⁻¹) := by
      rw [← ρ_pt Y.H, map_inv, hll]
      exact hρe.symm
    rwa [clSub_eq_of_pt_eq Y.H hpt'] at h1
  have Yu : Hyp13 S ((pU : G) * g) K := Y.mul rfl
  have hFx : Fbar S ((x : G) * g) K = Fbar S ((c : G) * g) K := by
    have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
    have e1 : (x : G) * g = ((x * c⁻¹ : S.M) : G) * ((c : G) * g) := (coe_mul_inv_mul x c g).symm
    have h1 := Yc.Fbar_mul_eq_of_mem (h := x * c⁻¹) (by rw [← e1]; exact hxF)
    rwa [← e1] at h1
  have hperpu : a ∈ perp S (Fbar S ((pU : G) * g) K) := by
    intro w hw
    have hw' : (((S.ρ ml)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Fbar S ((c : G) * g) K := by
      rw [← hFx]
      exact (mem_Fbar_mul_iff Y.normal ml ((x : G) * g)).mp (by rw [← coe_mul_mul]; exact hw)
    have h1 := ha _ hw'
    have h2 := polar_O_apply (S.ρ ml) ((((S.ρ ml)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) a
    rw [apply_inv_apply_O, hla] at h2
    rw [h2]
    exact h1
  have hneu : Fbar S ((pU : G) * g) K ≠ Fbar S g K := by
    intro h
    have h1 : S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹) ∈ Fbar S g K := h ▸ cl_mem_Fbar Yu.H
    have hFF : S.cl ((mF : G) * g * S.z * ((mF : G) * g)⁻¹) ∉ Fbar S g K := by
      intro hF
      have h2 := Y.Fbar_inf_Vt_le hσ hσE hpts (Submodule.mem_inf.mpr ⟨hF, hmF ▸ hf'V⟩)
      rcases mem_span_cl_iff.mp h2 with h2 | h2
      · exact hf'0 (hmF.trans h2)
      · apply hvfx
        have h3 : pf = a + pe := by
          rw [← hmF] at h2
          have h2' : pe + pf = a := h2
          rw [← h2', add_comm pe pf, add_assoc, add_self_vec (ZMod 2) pe, add_zero]
        rw [h3]
        exact add_mem hax hex
    have h2 := Y.Fbar_inf_clSub_le (e := mF) (hVP (hmF ▸ hf'V)) hFF
      (Submodule.mem_inf.mpr ⟨h1, huF⟩)
    rcases mem_span_cl_iff.mp h2 with h2 | h2
    · exact pt_ne_zero Y.H pU h2
    · apply hxV
      have h3 : px = a := by
        have h4 := congrArg (((S.ρ ml)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h2
        rw [hpu, inv_apply_apply_O] at h4
        have h5 := inv_apply_apply_O (S.ρ ml) a
        rw [hla] at h5
        exact h4.trans h5
      rw [h3]
      exact cl_a_mem_Vt hσ
  exact ⟨hua, huF, hue, hperpu, hneu⟩

end Hyp13

end CFSG.LargeExtraspecial.S13
