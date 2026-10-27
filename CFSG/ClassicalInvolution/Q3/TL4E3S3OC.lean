module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OEdge
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFix2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

namespace E3S3O

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y}
  {R' T W : Subgroup Y}

namespace Ctx

variable (h : Ctx n R S t J u L Rd Sd S' R' T W)
include h

theorem le_centralizer_of_mem' {s : Y} (hs : IsUniqueInvolution L s) {M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L) :
    M ≤ Subgroup.centralizer ({s} : Set Y) :=
  h.le_centralizer_of_mem hs (h.fam_eq ▸ hM)

theorem mem_nbr_of_sylow {s : Y} (hs : IsUniqueInvolution L s) {M Q : Subgroup Y}
    (hMa : XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M) (hQ : IsSylow2In Q M)
    (hQs : Q ≤ Subgroup.centralizer ({s} : Set Y)) :
    M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L := by
  have hΩ' := TightLargeHypR.typeRFam h.std.large
  have hLΩ : L ∈ CoreAssembly.conjClass (tightCore Rd) := h.fam_eq ▸ h.star.1
  refine ⟨hMa.1, fun e => h.not_xMem (e ▸ hMa), Q, mem_RSet_of_isSylow2In hMa.1 hQ, hQ.1,
    hQs.trans (hΩ'.tight L hLΩ s hs)⟩

theorem secImg_eq_of_normalizes {s : Y} (hs : IsUniqueInvolution L s) {M₀ : Subgroup Y}
    (hM₀ : M₀ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L)
    (hM₀a : XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M₀) {T₀ : Subgroup Y}
    (hT₀ : IsSylow2In T₀ (coreAt (u * t) M₀))
    (hTN : ∀ τ (hτ : τ ∈ T₀), QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) (u * t)))
          ⟨τ, coreAt_le_layerY hM₀a (hT₀.1 hτ)⟩ ∈ Subgroup.normalizer
        (secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd) :
          Set (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (u * t)))) :
    secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M₀ =
      secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd) := by
  have hΩ' := TightLargeHypR.typeRFam h.std.large
  have hcl := hΩ'.hyp.conjInvariant
  have hsa := h.mem_centralizer_a hs
  have hJa := h.std.xMem_K
  have hJs : tightCore Rd ≤ Subgroup.centralizer ({s} : Set Y) :=
    h.le_centralizer_of_mem hs (by rw [h.core]; exact h.J_mem_nbr)
  have hfix := secAct_eq_of_le_centralizer hcl hsa hJs
  have hM₀s := h.le_centralizer_of_mem' hs hM₀
  have hT₀M : T₀ ≤ M₀ := hT₀.1.trans (coreAt_le _ M₀)
  obtain ⟨m, hm, hTm, Q, hQ, -, hQs⟩ := exists_conj_normalizer_of_fixed hΩ' hsa hs.sq hJa hfix
    hT₀.2.1 (fun τ hτ => coreAt_le_layerY hM₀a (hT₀.1 hτ)) (hT₀M.trans hM₀s) hTN
  obtain ⟨hmY, hmO⟩ := mem_oddCoreOf_iff.mp hm
  have hJm := XMem.conj' hcl hJa (layerY_le_centralizer hmY)
  have hJmL := h.mem_nbr_of_sylow hs hJm hQ hQs
  by_cases heq : M₀ = conjSub m (tightCore Rd)
  · rw [heq]
    exact secImg_conj_of_mem (ν := ⟨m, hmY⟩) hmO _
  · exfalso
    have hT₀s : IsSylow2In T₀ M₀ := ((isSylow2In_coreAt_iff hM₀a).mp hT₀).1
    have hnbr : M₀ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (conjSub m (tightCore Rd)) :=
      ⟨hM₀a.1, heq, T₀, mem_RSet_of_isSylow2In hM₀a.1 hT₀s, hT₀s.1, hTm⟩
    exact h.not_mem_omegaNbr (h.fam_eq ▸ hJmL) (h.fam_eq ▸ hM₀) (h.fam_eq ▸ hnbr)

theorem exists_nbr_of_fixed {s : Y} (hs : IsUniqueInvolution L s)
    {Mb : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (u * t))}
    (hMb : Mb ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (u * t))
    (hfix : ∀ m ∈ Mb, secAct (conjInvariant_conjClass (tightCore Rd))
      (h.mem_centralizer_a hs) m = m) :
    ∃ M₀, M₀ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L ∧
      XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M₀ ∧
        secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M₀ = Mb := by
  have hΩ' := TightLargeHypR.typeRFam h.std.large
  obtain ⟨M₀, hM₀a, hM₀b, Q, hQ, -, hQs⟩ :=
    exists_xMem_of_fixed hΩ' (h.mem_centralizer_a hs) hs.sq hMb hfix
  exact ⟨M₀, h.mem_nbr_of_sylow hs hM₀a hQ hQs, hM₀a, hM₀b⟩

theorem exists_conj_of_nbr {s : Y} (hs : IsUniqueInvolution L s) {M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L)
    (hMa : XMem (CoreAssembly.conjClass (tightCore Rd)) (u * t) M) :
    ∃ c ∈ orbW Rd (u * t),
      conjSub c (secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd)) =
        secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M := by
  have hΩ' := TightLargeHypR.typeRFam h.std.large
  have hΦ := hΩ'.secFam (x := u * t)
  have hcl := hΦ.hyp.conjInvariant
  have hO := secQuot_oddCore_eq_bot (Ω := CoreAssembly.conjClass (tightCore Rd)) (x := u * t)
  have hn := h.std.natCard_secQuot_lt
  have hJb := secImg_mem h.std.xMem_K
  have hMb := secImg_mem hMa
  by_cases hc : ∃ g ∈ omegaGen (secFam (CoreAssembly.conjClass (tightCore Rd)) (u * t)),
      conjSub g (secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) (tightCore Rd)) =
        secImg (CoreAssembly.conjClass (tightCore Rd)) (u * t) M
  · obtain ⟨g, hg, hgM⟩ := hc
    obtain ⟨c, hcW, e⟩ :=
      Vtx.exists_orbGrp_conj hcl hJb (Vtx.commute_conj_of_not_conj h.thm4 hΦ hO hn hJb) hg
    exact ⟨c, hcW, e ▸ hgM⟩
  · exfalso
    have hcomm := Vtx.commutes_of_not_conj h.thm4 hΦ hO hn hJb hMb hc
    obtain ⟨T₀, hT₀, -⟩ :=
      IsSylow2In.exists_ge (P := coreAt (u * t) M) (IsPGroup.of_bot (p := 2)) bot_le
    refine hc ⟨1, Subgroup.one_mem _, ?_⟩
    rw [conjSub_one]
    refine (h.secImg_eq_of_normalizes hs hM hMa hT₀ fun τ hτ => ?_).symm
    refine mem_normalizer_iff_conjSub_eq.mpr (Vtx.conjSub_eq_of_forall_commute fun x hx => ?_)
    exact (hcomm x hx _ ⟨_, Subgroup.mem_subgroupOf.mpr (hT₀.1 hτ), rfl⟩).symm

end Ctx

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
