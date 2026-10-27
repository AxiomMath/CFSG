module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BThLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenHyp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenTr
public import CFSG.Sporadic.ThSchreier.NodeCentralCentralizer
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.Sporadic.Bridge.ThSurj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

section Core

variable {X G : Type*} [Group X] [Group G] [Finite G]

private theorem isExtraspecial_of_thLocal (e : X ≃* G) {Q M : Subgroup G} {a : G} {z : X}
    (hez : e z = a) (hQ : timmesfeldIsExtraspecial ↥Q)
    (hZ : (Subgroup.center ↥Q).map Q.subtype = Subgroup.zpowers a)
    (hcent : Subgroup.centralizer ({a} : Set G) = M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hF : ∀ F : Subgroup G, F ≤ M → IsElemAbelian 3 F → Nat.card F = 27 →
      Q ⊓ Subgroup.centralizer (F : Set G) ≤ Subgroup.zpowers a ∧
      (∀ H : Subgroup G, H ≤ F → Nat.card H * 3 = Nat.card F →
        Nat.card ↥(Q ⊓ Subgroup.centralizer (H : Set G)) ≤ 2 ^ 3) ∧
      ∀ T : Subgroup G, IsPGroup 2 T → T ≤ M → F ≤ Subgroup.normalizer (T : Set G) → T ≤ Q)
    {A B R0 R1 : Subgroup X} (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 27) (hBA : B ≤ A)
    (hBz : ∀ x ∈ B, x * z = z * x) (hzR0 : z ∈ R0) (hR0z : ∀ r ∈ R0, r * z = z * r)
    (hR0 : IsPGroup 2 R0) (hAR0 : A ≤ Subgroup.normalizer (R0 : Set X)) (hR1 : IsPGroup 2 R1)
    (hAR1 : A ≤ Subgroup.normalizer (R1 : Set X)) (h01 : R0 < R1) :
    timmesfeldIsExtraspecial ↥R1 := by
  set f := e.toMonoidHom
  have hinj : Function.Injective f := e.injective
  have hcomm : ∀ x : X, x * z = z * x → f x ∈ M := fun x hx => by
    rw [← hcent, Subgroup.mem_centralizer_singleton_iff, ← hez]
    exact (map_mul e x z).symm.trans ((congrArg e hx).trans (map_mul e z x))
  have hnorm : ∀ Y : Subgroup X, A ≤ Subgroup.normalizer (Y : Set X) →
      A.map f ≤ Subgroup.normalizer ((Y.map f : Subgroup G) : Set G) :=
    fun Y hY => (Subgroup.map_mono hY).trans (Subgroup.le_normalizer_map _)
  have hBM : B.map f ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcomm x (hBz x hx)
  have hR0M : R0.map f ≤ M := by
    rintro _ ⟨r, hr, rfl⟩
    exact hcomm r (hR0z r hr)
  have hB' := hB.map f
  obtain ⟨hCB, hH, hU⟩ := hF _ hBM hB' ((Subgroup.card_map_of_injective hinj).trans hBc)
  have hU' : ∀ T : Subgroup G, IsPGroup 2 T → A.map f ≤ Subgroup.normalizer (T : Set G) →
      T ≤ Subgroup.centralizer (((Subgroup.center ↥Q).map Q.subtype : Subgroup G) : Set G) →
        T ≤ Q := by
    intro T hT hAT hTZ
    refine hU T hT ?_ ((Subgroup.map_mono hBA).trans hAT)
    rw [← hcent]
    refine hTZ.trans (Subgroup.centralizer_le ?_)
    rw [hZ, Set.singleton_subset_iff]
    exact Subgroup.mem_zpowers a
  have hZR0 : (Subgroup.center ↥Q).map Q.subtype ≤ R0.map f := by
    rw [hZ, Subgroup.zpowers_le, ← hez]
    exact ⟨z, hzR0, rfl⟩
  have hCB' : Q ⊓ Subgroup.centralizer ((B.map f : Subgroup G) : Set G) ≤
      (Subgroup.center ↥Q).map Q.subtype := by
    rw [hZ]
    exact hCB
  have hM : ∀ T : Subgroup G, R0.map f ≤ T → T ≤ Q → A.map f ≤ Subgroup.normalizer (T : Set G) →
      ∀ s ∈ T, (∀ t ∈ T, s * t = t * s) → s ∈ (Subgroup.center ↥Q).map Q.subtype :=
    fun T hR0T hTQ hAT => radical_le_of_hyperplane_bound (p := 3) (k := 2) (by norm_num)
      (fun j hj0 hj2 => by interval_cases j <;> decide) hQ rfl hB' (hBM.trans hMQ) hCB' hH
      (hZR0.trans hR0T) hTQ ((Subgroup.map_mono hBA).trans hAT)
  have h := (isExtraspecial_of_nondeg_chain hQ rfl hZR0
    (hU _ (hR0.map f) hR0M ((Subgroup.map_mono hBA).trans (hnorm R0 hAR0))) (hnorm R0 hAR0) hU'
    hM (hR1.map f) (hnorm R1 hAR1) ((Subgroup.map_lt_map_iff_of_injective hinj).2 h01)).2
  exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
    (MulEquiv.subgroupMap e R1).symm h

end Core

section Centre


private theorem thJ_central_eq_one (t : ↥J) (ht : ∀ u : ↥J, u * t = t * u) : t = 1 := by
  haveI : IsSimpleGroup ↥J := Kernel.isSimpleGroup_J th_kernel_facts
  have hnc : ¬ IsMulCommutative ↥J := by
    intro hcomm
    haveI : IsMulCommutative ↥J := hcomm
    have hp : (Nat.card ↥J).Prime := (Group.is_simple_iff_prime_card).mp inferInstance
    rw [natCard_J] at hp
    exact (by norm_num : ¬ Nat.Prime 90745943887872000) hp
  have hZ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative (G := ↥J) hnc
  exact Subgroup.mem_bot.1 (hZ ▸ Subgroup.mem_center_iff.2 ht)

end Centre

section Local


private theorem thJ_local {F : Subgroup ↥J} (hFM : F ≤ M) (hF : IsElemAbelian 3 F)
    (hc : Nat.card F = 27) :
    Q ⊓ Subgroup.centralizer (F : Set ↥J) ≤ Subgroup.zpowers a ∧
      (∀ H : Subgroup ↥J, H ≤ F → Nat.card H * 3 = Nat.card F →
        Nat.card ↥(Q ⊓ Subgroup.centralizer (H : Set ↥J)) ≤ 2 ^ 3) ∧
      ∀ T : Subgroup ↥J, IsPGroup 2 T → T ≤ M → F ≤ Subgroup.normalizer (T : Set ↥J) →
        T ≤ Q := by
  have hF' : IsElemAbelian 3 (F.subgroupOf M) := hF.subgroupOf M
  have hc' : Nat.card (F.subgroupOf M) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv, hc]
  refine ⟨fun c hcQF => ?_, fun H hHF hH => ?_, fun T hT hTM hFT t ht => ?_⟩
  · obtain ⟨hcQ, hcF⟩ := Subgroup.mem_inf.1 hcQF
    have hmem : (⟨c, Q_le_M hcQ⟩ : ↥M) ∈
        Q.subgroupOf M ⊓ Subgroup.centralizer ((F.subgroupOf M : Subgroup ↥M) : Set ↥M) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hcQ, Subgroup.mem_centralizer_iff.2
        fun f hf => Subtype.ext (Subgroup.mem_centralizer_iff.1 hcF f
          (Subgroup.mem_subgroupOf.1 hf))⟩
    have h := Q_inf_centralizer_le_zpowers_of_elemAbelian max3Data hF' hc' hmem
    rw [← z_eq_a]
    exact (mem_zpowers_zM _).1 h
  · have hH' : Nat.card (H.subgroupOf M) * 3 = Nat.card (F.subgroupOf M) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hHF.trans hFM)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv, hH]
    have h := card_Q_inf_centralizer_le_of_index_three max3Data hF' hc'
      (Subgroup.subgroupOf_mono M hHF) hH'
    let φ : ↥(Q ⊓ Subgroup.centralizer (H : Set ↥J)) →
        ↥(Q.subgroupOf M ⊓ Subgroup.centralizer ((H.subgroupOf M : Subgroup ↥M) : Set ↥M)) :=
      fun x => ⟨⟨x, Q_le_M (Subgroup.mem_inf.1 x.2).1⟩, Subgroup.mem_inf.2
        ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 x.2).1, Subgroup.mem_centralizer_iff.2
          fun h hh => Subtype.ext (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 x.2).2 h
            (Subgroup.mem_subgroupOf.1 hh))⟩⟩
    have hφ : Function.Injective φ := fun x y hxy => by
      have e := congrArg Subtype.val (congrArg Subtype.val hxy)
      exact Subtype.ext e
    exact (Nat.card_le_card_of_injective φ hφ).trans h
  · have hT' : IsPGroup 2 (T.subgroupOf M) := hT.comap_subtype
    have hFT' : F.subgroupOf M ≤
        Subgroup.normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTM]
      exact Subgroup.subgroupOf_mono M hFT
    have h := le_Q_of_elemAbelian_le_normalizer max3Data hF' hc' hT' hFT'
      (Subgroup.mem_subgroupOf.2 ht : (⟨t, hTM ht⟩ : ↥M) ∈ T.subgroupOf M)
    exact Subgroup.mem_subgroupOf.1 h

end Local

section Row


theorem rowTh_holds : I301BRow .th := by
  intro S _ _ hS B I K R0 R1 y _ hBe hBc _ _ _ _ _ _ hR0 hR0c _ _ hKB hR1 hKB1 h01
  obtain ⟨i, hi, ⟨e₁⟩⟩ := hS
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have eS : S ≃* ↥J := (e₁.trans (by exact b.symm)).trans thEquivJ
  have hAut : ∀ α : MulAut ↥J, ∃ g : ↥J, α = MulAut.conj g := fun α => by
    have hmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J :=
      inner_J ▸ Subgroup.mem_top α
    obtain ⟨f, hf⟩ := hmem
    exact ⟨f, hf.symm⟩
  have hAutS : ∀ α : MulAut S, ∃ g : S, α = MulAut.conj g := fun α => by
    obtain ⟨g, hg⟩ := hAut ((eS.symm.trans α).trans eS)
    refine ⟨eS.symm g, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun β : MulAut ↥J => β (eS x)) hg
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [MulAut.conj_apply]
    apply eS.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨Φ⟩ := @nonempty_mulAut_equiv_of_inner S ↥J _ inferInstance eS thJ_central_eq_one hAutS
  have hR0c' : Nat.card R0 = 2 ^ 5 := hR0c
  have hBe' : IsElemAbelian 3 B := hBe
  have hBc' : Nat.card B = 3 ^ 3 := hBc
  have hR0e : timmesfeldIsExtraspecial ↥R0 := hR0.resolve_right (by rw [hR0c']; norm_num)
  obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥R0)).mp hR0e.2.2.2
  set z : MulAut S := ((c : ↥R0) : MulAut S) with hz
  have hzR0 : z ∈ R0 := (c : ↥R0).2
  have hzc : ∀ r ∈ R0, r * z = z * r := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨r, hr⟩)
  have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hz2 : orderOf z = 2 := by
    have h1 : orderOf c ∣ 2 := hR0e.2.2.2 ▸ orderOf_dvd_natCard c
    have h2 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.1 h)
    have h3 : orderOf c = 2 := ((Nat.dvd_prime Nat.prime_two).1 h1).resolve_left h2
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, h3]
  obtain ⟨g, hg⟩ := isConj_iff.1
    (all_involutions_conjugate (Φ z) (by rw [MulEquiv.orderOf_eq, hz2]))
  obtain ⟨e, hez⟩ : ∃ e : MulAut S ≃* ↥J, e z = a := by
    refine ⟨Φ.trans (MulAut.conj g⁻¹), ?_⟩
    show g⁻¹ * Φ z * g⁻¹⁻¹ = a
    rw [← hg]
    group
  obtain ⟨hcent, -, -, -⟩ := ctuc_Th_full_central_involution_centralizer
  have hQe : timmesfeldIsExtraspecial ↥Q :=
    (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff ↥Q).2 isExtraspecialPGroup_Q
  have hZ : (Subgroup.center ↥Q).map Q.subtype = Subgroup.zpowers a := by
    rw [center_Q, ← z_eq_a, Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.2 z_mem_Q)]
  exact @isExtraspecial_of_thLocal (MulAut S) ↥J _ inferInstance inferInstance e _ _ _ _ hez hQe
    hZ hcent M_le_normalizer_Q (fun F hFM hF hc => thJ_local hFM hF hc) _ _ _ _ hBe'
    (hBc'.trans (by norm_num)) le_sup_right
    (fun x hx => comm_of_mem_normalizer hR0e hzR0 hzc hz1 (hKB (le_sup_right (a := K) hx))) hzR0
    hzc hR0e.1 hKB hR1 hKB1 h01

end Row

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
