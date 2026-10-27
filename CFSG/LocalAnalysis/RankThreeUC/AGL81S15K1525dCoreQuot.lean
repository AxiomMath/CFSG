module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K1525dCoreProof

theorem le_pCore_of_normal {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup ⟨inferInstance, hN⟩

theorem quotient_pCore_equiv {G : Type*} [Group G] [Finite G] {A U M : Subgroup G}
    (hUA : U ≤ A) (hMA : M ≤ A) (hA : A ≤ U ⊔ M)
    (hUn : A ≤ Subgroup.normalizer (U : Set G)) (hU2 : IsPGroup 2 ↥U)
    (hMs : IsSimpleGroup ↥M) (hM2 : ¬ IsPGroup 2 ↥M) :
    Nonempty (↥A ⧸ CFSG.pCore 2 ↥A ≃* ↥M) := by
  set N : Subgroup ↥A := U.subgroupOf A with hN
  haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUA).mpr hUn
  have hN2 : IsPGroup 2 ↥N :=
    hU2.of_injective (Subgroup.subgroupOfEquivOfLe hUA).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUA).injective
  let ψ : ↥M →* ↥A ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hMA)
  have hmemN : ∀ m : ↥M, ψ m = 1 → (m : G) ∈ U := by
    intro m hm
    have h1 : Subgroup.inclusion hMA m ∈ N := (QuotientGroup.eq_one_iff (N := N) _).1 hm
    exact h1
  have hker2 : IsPGroup 2 ↥ψ.ker := by
    intro m
    have hmU := hmemN m (MonoidHom.mem_ker.1 m.2)
    obtain ⟨k, hk⟩ := hU2 ⟨((m : ↥M) : G), hmU⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
    rcases hMs.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      apply hM2
      rw [h] at hker2
      exact hker2.of_equiv Subgroup.topEquiv
  have hsurj : Function.Surjective ψ := by
    have h1 : N ⊔ M.subgroupOf A = ⊤ := by
      rw [hN, ← Subgroup.subgroupOf_sup hUA hMA, Subgroup.subgroupOf_eq_top]
      exact hA
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have ha : a ∈ N ⊔ M.subgroupOf A := h1 ▸ Subgroup.mem_top a
    obtain ⟨n, hn, m', hm', rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha
    refine ⟨⟨(m' : G), hm'⟩, ?_⟩
    have hn1 : (QuotientGroup.mk n : ↥A ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show (QuotientGroup.mk (Subgroup.inclusion hMA ⟨(m' : G), hm'⟩) : ↥A ⧸ N) =
      QuotientGroup.mk (n * m')
    rw [QuotientGroup.mk_mul, hn1, one_mul]
    rfl
  let e1 : ↥M ≃* ↥A ⧸ N := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hpc : CFSG.pCore 2 ↥A = N := by
    apply le_antisymm
    · have hQ2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥A).map (QuotientGroup.mk' N)) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥A)).map (QuotientGroup.mk' N)
      haveI hQn : ((CFSG.pCore 2 ↥A).map (QuotientGroup.mk' N)).Normal :=
        Subgroup.Normal.map inferInstance (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      haveI hQ'n : (((CFSG.pCore 2 ↥A).map (QuotientGroup.mk' N)).comap ψ).Normal :=
        Subgroup.normal_comap ψ
      have hQ'2 : IsPGroup 2 ↥(((CFSG.pCore 2 ↥A).map (QuotientGroup.mk' N)).comap ψ) :=
        hQ2.comap_of_injective ψ hinj
      have hbot : ((CFSG.pCore 2 ↥A).map (QuotientGroup.mk' N)) = ⊥ := by
        rcases hMs.eq_bot_or_eq_top_of_normal
          (((CFSG.pCore 2 ↥A).map (QuotientGroup.mk' N)).comap ψ) with h | h
        · rw [← Subgroup.map_comap_eq_self_of_surjective hsurj
            ((CFSG.pCore 2 ↥A).map (QuotientGroup.mk' N)), h, Subgroup.map_bot]
        · exfalso
          apply hM2
          rw [h] at hQ'2
          exact hQ'2.of_equiv Subgroup.topEquiv
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
      exact hbot
    · exact le_pCore_of_normal hN2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans e1.symm⟩

end K1525dCoreProof

end CFSG.LocalAnalysis.RankThreeUC.S15
