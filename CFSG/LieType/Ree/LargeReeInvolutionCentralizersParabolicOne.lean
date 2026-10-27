module

public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom pairedTorusHom_apply f4i torusPair)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem canonicalRep_conj_torusTwo
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : Kˣ) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
        pairedTorusHom a (f4i 1) (f4i 2) v *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ =
      pairedTorusHom a (f4i 1) (f4i 2) v * pairedTorusHom a (f4i 0) (f4i 3) v := by
  have h := congrArg Subtype.val (CFSG.SectionRank.LargeRee.torus_reflections (a := a) hK v).2.1
  have hn : (nrep F4.tag K (F4.blockElt (CFSG.SectionRank.LargeRee.fi 0)) : ModGL F4.tag K) =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) := by
    change canonicalRep (coxeterSystem F4.tag) K _ = _
    rw [blockElt_eq]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn] at h
  rw [← rankOneTorusPair_left, ← rankOneTorusPair_right, LargeReeCover.torusPair_eq_reeTorus,
    LargeReeCover.torusPair_eq_reeTorus]
  simp only [CFSG.SectionRank.LargeRee.reeTorus_one, mul_one, one_mul]
  exact h

theorem rankOne_canonicalRep_one_mem_reeGamma :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
      F4.reeGamma K a :=
  (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem _)).2

theorem rankOneGroupOne_le_reeGamma
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ F4.reeGamma K a := by
  rw [rankOneGroupOne, Subgroup.closure_le]
  rintro g ((hg | hg) | rfl)
  · exact (Subgroup.mem_inf.1 hg).2
  · exact (Subgroup.mem_inf.1 (rankOneTorusOne_le hK hg)).2
  · exact rankOne_canonicalRep_one_mem_reeGamma

theorem rankOneGroupOne_le_normalizer_complement
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ Subgroup.normalizer
      (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
  rw [rankOneGroupOne, Subgroup.closure_le]
  rintro g ((hg | hg) | rfl)
  · exact reeFixedPosUnipotent_le_normalizer _ (reeFixedOrbitUnipotent_le _ hg)
  · exact reeFixedTorus_le_normalizer_complement _ (rankOneTorusOne_le hK hg)
  · exact mem_normalizer_of_map_eq (map_conj_reeFixedOrbitComplementUnipotent _)

theorem rankOneTorusTwo_le_normalizer_rankOneGroupOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusTwo K a ≤ Subgroup.normalizer (rankOneGroupOne K a : Set (ModGL F4.tag K)) := by
  have key : ∀ t ∈ rankOneTorusTwo K a, ∀ g ∈ rankOneGroupOne K a,
      t * g * t⁻¹ ∈ rankOneGroupOne K a := by
    intro t ht g hg
    have hle : rankOneGroupOne K a ≤
        (rankOneGroupOne K a).comap (MulAut.conj t).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ((hx | ⟨u, rfl⟩) | rfl)
      · have hxU : t * x * t⁻¹ ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ :=
          (Subgroup.mem_normalizer_iff.1
            (reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent _ (rankOneTorusTwo_le hK ht))
              x).1 hx
        exact Subgroup.subset_closure (.inl (.inl hxU))
      · obtain ⟨v, rfl⟩ := ht
        have hc : pairedTorusHom a (f4i 1) (f4i 2) v * pairedTorusHom a (f4i 0) (f4i 3) u *
            (pairedTorusHom a (f4i 1) (f4i 2) v)⁻¹ = pairedTorusHom a (f4i 0) (f4i 3) u := by
          rw [(rankOne_commute_pairedTorusHom 1 2 0 3 v u).eq, mul_inv_cancel_right]
        have hu : pairedTorusHom a (f4i 0) (f4i 3) u ∈ rankOneGroupOne K a :=
          Subgroup.subset_closure (.inl (.inr ⟨u, rfl⟩))
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [hc]
        exact hu
      · obtain ⟨v, rfl⟩ := ht
        have hr := canonicalRep_conj_torusTwo (a := a) hK v
        have hTT' := (rankOne_commute_pairedTorusHom (a := a) (K := K) 1 2 0 3 v v).eq
        simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [centralZ_conj_eq_of_conj_eq hr hTT']
        exact mul_mem (inv_mem (Subgroup.subset_closure (.inl (.inr ⟨_, rfl⟩))))
          (Subgroup.subset_closure (.inr rfl))
    exact hle hg
  intro t ht
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => key t ht g hg, fun hg => ?_⟩
  have h := key t⁻¹ (inv_mem ht) _ hg
  rwa [show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at h

theorem rankOneTorusTwo_le_normalizer_sup_rankOneGroupOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneTorusTwo K a ≤ Subgroup.normalizer
      ((F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊔ rankOneGroupOne K a :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) :=
  fun _ ht => Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.2
    ⟨reeFixedTorus_le_normalizer_complement _ (rankOneTorusTwo_le hK ht),
      rankOneTorusTwo_le_normalizer_rankOneGroupOne hK ht⟩)

theorem exists_mul_of_mem_reeFixedBorel_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {b : ModGL F4.tag K} (hb : b ∈ F4.reeFixedBorel K a) :
    ∃ t ∈ rankOneTorusTwo K a,
      ∃ s ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊔ rankOneGroupOne K a,
        t * s = b := by
  have hb' : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, x, hx, rfl⟩ := hb'
  obtain ⟨u, v, rfl⟩ := rankOne_exists_torusPair_eq hK hh
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_reeFixedPosUnipotent ⟨0, by decide⟩ hx
  refine ⟨pairedTorusHom a (f4i 1) (f4i 2) v, ⟨v, rfl⟩,
    pairedTorusHom a (f4i 0) (f4i 3) u * (y * z), ?_, ?_⟩
  · refine mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure (.inl (.inr ⟨u, rfl⟩))))
      (mul_mem (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (.inl (.inl hz)))))
  · beta_reduce
    rw [rankOneTorusPair_eq_mul, (rankOne_commute_pairedTorusHom 0 3 1 2 u v).eq, mul_assoc]

theorem exists_mul_of_mem_reeLocalParabolic_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL F4.tag K} (hg : g ∈ F4.reeLocalParabolic K a ⟨0, by decide⟩) :
    ∃ t ∈ rankOneTorusTwo K a,
      ∃ s ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊔ rankOneGroupOne K a,
        t * s = g := by
  have hg' : g ∈ ((F4.reeGamma K a ⊓ parabolicSubgroup F4.tag K
      (F4.fixedOrbitSet ⟨0, by decide⟩) : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) :=
    hg
  rw [coe_reeGamma_inf_parabolicSubgroup] at hg'
  rcases hg' with hB | hD
  · exact exists_mul_of_mem_reeFixedBorel_zero hK hB
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hD
    obtain ⟨t, ht, s, hs, rfl⟩ := exists_mul_of_mem_reeFixedBorel_zero hK hb
    obtain ⟨t', ht', s', hs', rfl⟩ := exists_mul_of_mem_reeFixedBorel_zero hK hb'
    have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
        F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊔ rankOneGroupOne K a :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (.inr rfl))
    have hsn := mul_mem hs hn
    have hconj : t'⁻¹ * (s * canonicalRep (coxeterSystem F4.tag) K
        (F4.fixedOrbitElement ⟨0, by decide⟩)) * t' ∈
          F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ⊔ rankOneGroupOne K a := by
      have := (Subgroup.mem_normalizer_iff.1
        (rankOneTorusTwo_le_normalizer_sup_rankOneGroupOne hK (inv_mem ht')) _).1 hsn
      rwa [inv_inv] at this
    refine ⟨t * t', mul_mem ht ht', t'⁻¹ * (s * canonicalRep (coxeterSystem F4.tag) K
        (F4.fixedOrbitElement ⟨0, by decide⟩)) * t' * s', mul_mem hconj hs', ?_⟩
    group

end CFSG.LieType.Ree.LargeReeInvolution
