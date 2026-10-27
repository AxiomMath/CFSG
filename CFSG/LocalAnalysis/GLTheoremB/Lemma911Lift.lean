module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Orbit

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Lift

variable {Q : Type} [Group Q] [Finite Q] {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Q] [Finite Γ] in
theorem iSup_map_perfect (ρ : Γ →* MulAut Q) {J : Subgroup Q} (hJ : ⁅J, J⁆ = J) :
    ⁅⨆ γ : Γ, J.map (ρ γ).toMonoidHom, ⨆ γ : Γ, J.map (ρ γ).toMonoidHom⁆ =
      ⨆ γ : Γ, J.map (ρ γ).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.2 fun a ha c hc => ?_
    rw [commutatorElement_def]
    exact (⨆ γ : Γ, J.map (ρ γ).toMonoidHom).mul_mem
      ((⨆ γ : Γ, J.map (ρ γ).toMonoidHom).mul_mem
        ((⨆ γ : Γ, J.map (ρ γ).toMonoidHom).mul_mem ha hc)
        ((⨆ γ : Γ, J.map (ρ γ).toMonoidHom).inv_mem ha))
      ((⨆ γ : Γ, J.map (ρ γ).toMonoidHom).inv_mem hc)
  · refine iSup_le fun γ => ?_
    have h1 : ⁅J.map (ρ γ).toMonoidHom, J.map (ρ γ).toMonoidHom⁆ = J.map (ρ γ).toMonoidHom := by
      rw [← Subgroup.map_commutator, hJ]
    have h2 : J.map (ρ γ).toMonoidHom ≤ ⨆ γ : Γ, J.map (ρ γ).toMonoidHom :=
      le_iSup (fun γ => J.map (ρ γ).toMonoidHom) γ
    calc J.map (ρ γ).toMonoidHom = ⁅J.map (ρ γ).toMonoidHom, J.map (ρ γ).toMonoidHom⁆ := h1.symm
      _ ≤ _ := Subgroup.commutator_mono h2 h2

omit [Finite Q] [Finite Γ] in
theorem map_iSup_map_le (ρ : Γ →* MulAut Q) (J : Subgroup Q) (γ : Γ) :
    (⨆ δ : Γ, J.map (ρ δ).toMonoidHom).map (ρ γ).toMonoidHom ≤
      ⨆ δ : Γ, J.map (ρ δ).toMonoidHom := by
  rw [Subgroup.map_iSup]
  refine iSup_le fun δ => ?_
  rw [← map_mul_act]
  exact le_iSup (fun δ => J.map (ρ δ).toMonoidHom) (γ * δ)

theorem exists_invariant_two_subgroup_of_quot (hΓ : IsPGroup 3 Γ) (ρ : Γ →* MulAut Q)
    (N : Subgroup Q) [N.Normal] (hN2 : IsPGroup 2 ↥N) (hρN : ∀ γ, N.map (ρ γ).toMonoidHom = N)
    {J : Subgroup Q} (hJp : ⁅J, J⁆ = J) (hJc : IsComponentOf (J.map (QuotientGroup.mk' N)) ⊤)
    (hA7 : Nonempty ((↥(J.map (QuotientGroup.mk' N)) ⧸
      Subgroup.center ↥(J.map (QuotientGroup.mk' N))) ≃* ↥S7.Alt7)) :
    ∃ S : Subgroup Q, IsPGroup 2 ↥S ∧ S ≤ ⨆ γ : Γ, J.map (ρ γ).toMonoidHom ∧
      (∀ γ : Γ, S.map (ρ γ).toMonoidHom ≤ S) ∧
      (⨆ γ : Γ, J.map (ρ γ).toMonoidHom) ≤
        ⨆ y ∈ (⨆ γ : Γ, J.map (ρ γ).toMonoidHom), S.map (MulAut.conj y).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : Q →* Q ⧸ N := QuotientGroup.mk' N with hπ
  set ρ' : Γ →* MulAut (Q ⧸ N) := quotAutHom N ρ hρN with hρ'
  have hρ'mk : ∀ (γ : Γ) (q : Q), ρ' γ (π q) = π (ρ γ q) := fun γ q => quotAutHom_mk N ρ hρN γ q
  obtain ⟨St, hSt2, hStJ, hStinv, hStgen⟩ :=
    exists_invariant_two_subgroup_generating hΓ ρ' hJc hA7
  set Jst : Subgroup Q := ⨆ γ : Γ, J.map (ρ γ).toMonoidHom with hJst
  have hπJ : ∀ γ : Γ, (J.map (ρ γ).toMonoidHom).map π = (J.map π).map (ρ' γ).toMonoidHom := by
    intro γ
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hπJst : Jst.map π = ⨆ γ : Γ, (J.map π).map (ρ' γ).toMonoidHom := by
    rw [hJst, Subgroup.map_iSup]
    exact iSup_congr hπJ
  set S : Subgroup Q := Jst ⊓ St.comap π with hS
  have hStπ : St ≤ Jst.map π := hπJst ▸ hStJ
  have hπS : S.map π = St := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact hs.2
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := hStπ hz
      exact ⟨j, ⟨hj, hz⟩, rfl⟩
  have hker : IsPGroup 2 ↥π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hN2
  have hSt2' : IsPGroup 2 ↥(St.comap π) := hSt2.comap_of_ker_isPGroup π hker
  have hS2 : IsPGroup 2 ↥S := hSt2'.to_le inf_le_right
  refine ⟨S, hS2, inf_le_left, ?_, ?_⟩
  · intro γ
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨map_iSup_map_le ρ J γ ⟨s, hs.1, rfl⟩, ?_⟩
    show π (ρ γ s) ∈ St
    rw [← hρ'mk]
    exact hStinv γ ⟨π s, hs.2, rfl⟩
  ·
    set T : Subgroup Q := ⨆ y ∈ Jst, S.map (MulAut.conj y).toMonoidHom with hT
    have hTJ : T ≤ Jst := by
      refine iSup₂_le fun y hy => ?_
      rintro _ ⟨s, hs, rfl⟩
      exact Jst.mul_mem (Jst.mul_mem hy hs.1) (Jst.inv_mem hy)
    have hTn : (T.subgroupOf Jst).Normal := by
      have hkey : ∀ g ∈ Jst, ∀ z ∈ T, g * z * g⁻¹ ∈ T := by
        intro g hg z hz
        have hmap : T.map (MulAut.conj g).toMonoidHom ≤ T := by
          rw [hT, Subgroup.map_iSup]
          refine iSup_le fun y => ?_
          rw [Subgroup.map_iSup]
          refine iSup_le fun hy => ?_
          rw [Subgroup.map_map]
          refine le_trans ?_ (le_iSup₂_of_le (g * y) (Jst.mul_mem hg hy) le_rfl)
          refine le_of_eq ?_
          congr 1
          ext x
          simp [mul_assoc]
        exact hmap ⟨z, hz, rfl⟩
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).2 fun g hg => ?_
      refine Subgroup.mem_normalizer_iff.2 fun z => ⟨hkey g hg z, fun hz => ?_⟩
      have := hkey g⁻¹ (Jst.inv_mem hg) _ hz
      simpa [mul_assoc] using this
    have hJstT : Jst.map π ≤ T.map π := by
      rw [hπJst]
      refine le_trans hStgen ?_
      refine iSup₂_le fun yt hyt => ?_
      rw [← hπJst] at hyt
      obtain ⟨y, hy, rfl⟩ := hyt
      rintro _ ⟨s', hs', rfl⟩
      rw [← hπS] at hs'
      obtain ⟨s, hs, rfl⟩ := hs'
      have h1 : y * s * y⁻¹ ∈ T :=
        (le_iSup₂_of_le y hy le_rfl : S.map (MulAut.conj y).toMonoidHom ≤ T) ⟨s, hs, rfl⟩
      exact ⟨y * s * y⁻¹, h1, by simp⟩
    set K : Subgroup Q := Jst ⊓ N with hK
    have hK2 : IsPGroup 2 ↥K := hN2.to_le inf_le_right
    have hJsup : Jst ≤ T ⊔ K := by
      intro j hj
      obtain ⟨t, ht, htj⟩ := hJstT ⟨j, hj, rfl⟩
      have hk : t⁻¹ * j ∈ K := by
        refine ⟨Jst.mul_mem (Jst.inv_mem (hTJ ht)) hj, ?_⟩
        have h3 : π (t⁻¹ * j) = 1 := by rw [map_mul, map_inv, htj, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).1 h3
      have : j = t * (t⁻¹ * j) := by group
      rw [this]
      exact Subgroup.mul_mem_sup ht hk
    exact le_of_perfect_of_le_sup_pGroup (q := 2) (iSup_map_perfect ρ hJp) hTJ hTn inf_le_left
      hK2 hJsup

end Lift

end CFSG.LocalAnalysis.GLTheoremB
