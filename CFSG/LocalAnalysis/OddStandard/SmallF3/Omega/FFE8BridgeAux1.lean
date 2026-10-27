module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma fk3_ffSim_apply (g : OGroup Q) :
    ffSim Q g = QuotientGroup.mk (orthToSim Q g) := by
  rw [ffSim, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

theorem ffOutFFE8Bridge_pi_not_mem (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) :
    piOrth Q ∉ omegaGroup hQ := by
  intro h
  have h' := (piOrth_mem_omegaGroup_iff hQ).mp h
  rw [hdim, hsgn] at h'
  norm_num at h'

theorem ffOutFFE8Bridge_inj (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {g g' : OGroup Q} (hg : g ∈ omegaGroup hQ)
    (hg' : g' ∈ omegaGroup hQ) (h : ffSim Q g = ffSim Q g') : g = g' := by
  have h1 : ffSim Q (g⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases (ffSim_eq_one_iff (Q := Q)).mp h1 with h2 | h2
  · exact inv_mul_eq_one.mp h2
  · exfalso
    apply ffOutFFE8Bridge_pi_not_mem hQ hdim hsgn
    rw [← h2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hg'

theorem ffOutFFE8Bridge_map_comap (hQ : Q.Nondegenerate) {Ē : Subgroup (ProjSim Q)}
    (h : Ē ≤ ffOmegaSim hQ) :
    ((Ē.comap (ffSim Q)) ⊓ omegaGroup hQ).map (ffSim Q) = Ē := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact (Subgroup.mem_comap.mp hg.1)
  · intro hx
    obtain ⟨g, hg, hgsim⟩ := (mem_ffOmegaSim_iff hQ).mp (h hx)
    refine Subgroup.mem_map.mpr ⟨g, ?_, hgsim⟩
    exact Subgroup.mem_inf.mpr ⟨by rwa [Subgroup.mem_comap, hgsim], hg⟩

theorem ffOutFFE8Bridge_elemAb (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} (hle : Ē ≤ ffOmegaSim hQ)
    (h : IsElemAb2 Ē 3) : IsElemAb2 ((Ē.comap (ffSim Q)) ⊓ omegaGroup hQ) 3 := by
  let E : Subgroup (OGroup Q) := (Ē.comap (ffSim Q)) ⊓ omegaGroup hQ
  have hle' : E ≤ omegaGroup hQ := inf_le_right
  have hcomm : IsMulCommutative E := by
    rw [isMulCommutative_iff]
    intro a b
    have habar : ffSim Q (a : OGroup Q) ∈ Ē :=
      Subgroup.mem_comap.mp a.2.1
    have hbbar : ffSim Q (b : OGroup Q) ∈ Ē :=
      Subgroup.mem_comap.mp b.2.1
    have hbar : ffSim Q (a : OGroup Q) * ffSim Q (b : OGroup Q) =
        ffSim Q (b : OGroup Q) * ffSim Q (a : OGroup Q) :=
      congrArg Subtype.val (h.1.1.is_comm.comm
        ⟨ffSim Q (a : OGroup Q), habar⟩ ⟨ffSim Q (b : OGroup Q), hbbar⟩)
    apply Subtype.ext
    change (a : OGroup Q) * (b : OGroup Q) = (b : OGroup Q) * (a : OGroup Q)
    exact ffOutFFE8Bridge_inj hQ hdim hsgn (E.mul_mem a.2 b.2).2
      (E.mul_mem b.2 a.2).2 (by
        rw [map_mul, map_mul]
        exact hbar)
  have hexp : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    have hxbar : ffSim Q (x : OGroup Q) ∈ Ē := Subgroup.mem_comap.mp hx.1
    have hx2 : ffSim Q ((x : OGroup Q) ^ 2) = 1 := by
      rw [map_pow]
      exact h.1.2 (ffSim Q (x : OGroup Q)) hxbar
    rcases (ffSim_eq_one_iff (Q := Q)).mp hx2 with h2 | h2
    · exact h2
    · exfalso
      apply ffOutFFE8Bridge_pi_not_mem hQ hdim hsgn
      rw [← h2]
      exact Subgroup.pow_mem (omegaGroup hQ) hx.2 2
  have hcardmap : Nat.card (E.map (ffSim Q)) = Nat.card E := by
    rw [← SetLike.coe_sort_coe, Subgroup.coe_map,
      Nat.card_image_of_injOn (fun a ha b hb hab =>
        ffOutFFE8Bridge_inj hQ hdim hsgn ha.2 hb.2 hab)]
    rfl
  have hmap : E.map (ffSim Q) = Ē :=
    ffOutFFE8Bridge_map_comap hQ hle
  have hcardE : Nat.card E = Nat.card Ē := by
    rw [← hcardmap, hmap]
  exact ⟨⟨hcomm, hexp⟩, hcardE.trans h.2⟩

theorem ffOutFFE8Bridge_main (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q}
    (h : FFE8SData hQ Ē z ν) :
    ∃ (E : Subgroup (OGroup Q)) (t ν' : OGroup Q), FFE8VData hQ E t ν' ∧
      Ē = E.map (ffSim Q) ∧ z = ffSim Q t ∧ ν = ffSim Q ν' := by
  let E : Subgroup (OGroup Q) := (Ē.comap (ffSim Q)) ⊓ omegaGroup hQ
  obtain ⟨y, hyz, hyne, t, htt, htype, hty⟩ := h.z_type
  have htdim : invDim t = 4 := by
    simpa [invType] using congrArg Prod.fst htype
  have htsign : invSign t = 1 := by
    simpa [invType] using congrArg Prod.snd htype
  have hsimt : ffSim Q t = z := by
    rw [fk3_ffSim_apply, ← projOrthToProjSim_toProj, hty, hyz]
  have htomega : t ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ htt, htdim, htsign]
    norm_num
  have htE : t ∈ E := by
    refine Subgroup.mem_inf.mpr ⟨?_, htomega⟩
    rw [Subgroup.mem_comap, hsimt]
    exact h.z_mem
  obtain ⟨ν', hν'omega, hν'sim⟩ := (mem_ffOmegaSim_iff hQ).mp h.nu_mem
  have hcube : ν' ^ 3 = 1 := by
    have h1 : ffSim Q (ν' ^ 3) = 1 := by
      rw [map_pow, hν'sim]
      simpa [h.nu_order] using pow_orderOf_eq_one ν
    rcases (ffSim_eq_one_iff (Q := Q)).mp h1 with h2 | h2
    · exact h2
    · exfalso
      apply ffOutFFE8Bridge_pi_not_mem hQ hdim hsgn
      rw [← h2]
      exact Subgroup.pow_mem _ hν'omega 3
  have hsl : ∀ g : OGroup Q,
      ffSim Q (ν' * g * ν'⁻¹) = ν * ffSim Q g * ν⁻¹ := by
    intro g
    rw [map_mul, map_mul, map_inv, hν'sim]
  have hnormal : ν' ∈ Subgroup.normalizer (E : Set (OGroup Q)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_comap, hsl]
        exact (Subgroup.mem_normalizer_iff.mp h.nu_norm (ffSim Q g)).mp
          (Subgroup.mem_comap.mp hg.1)
      · exact (omegaGroup_normal hQ).conj_mem g hg.2 ν'
    · intro hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have hg' := Subgroup.mem_inf.mp hg
        have hmem : ν * ffSim Q g * ν⁻¹ ∈ Ē := by
          simpa only [hsl g] using Subgroup.mem_comap.mp hg'.1
        exact (Subgroup.mem_normalizer_iff.mp h.nu_norm (ffSim Q g)).mpr hmem
      · have hg' := Subgroup.mem_inf.mp hg
        have hconj := (omegaGroup_normal hQ).conj_mem (ν' * g * ν'⁻¹) hg'.2 ν'⁻¹
        simpa [mul_assoc] using hconj
  have hfix : ∀ e ∈ E, ν' * e = e * ν' → e = 1 ∨ e = t := by
    intro e he hcomm
    have hebar : ffSim Q e ∈ Ē := Subgroup.mem_comap.mp he.1
    have hcommbar : ν * ffSim Q e = ffSim Q e * ν := by
      have := congrArg (ffSim Q) hcomm
      rw [map_mul, map_mul, hν'sim] at this
      exact this
    rcases h.nu_fix (ffSim Q e) hebar hcommbar with h1 | h1
    · rcases (ffSim_eq_one_iff (Q := Q)).mp h1 with he1 | hepi
      · exact Or.inl he1
      · exfalso
        apply ffOutFFE8Bridge_pi_not_mem hQ hdim hsgn
        rw [← hepi]
        exact he.2
    · refine Or.inr (ffOutFFE8Bridge_inj hQ hdim hsgn he.2 htomega ?_)
      rw [h1, hsimt]
  refine ⟨E, t, ν', ?_, ?_, hsimt.symm, hν'sim.symm⟩
  · refine ⟨inf_le_right, ?_, htE, htt, htdim, htsign, hcube, hnormal, hfix⟩
    exact ffOutFFE8Bridge_elemAb hQ hdim hsgn h.le_omega h.elemAb
  · exact (ffOutFFE8Bridge_map_comap hQ h.le_omega).symm

end CFSG.OddStandard.SmallF3.Omega
