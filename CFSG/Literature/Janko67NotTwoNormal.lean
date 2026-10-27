module

public import CFSG.Literature.Janko67Setting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_7

public section

namespace CFSG.Literature.Janko67

open CFSG CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial CFSG.BenderSuzuki.External


theorem exists_conj_mem_M_ne {G : Type} [Group G] [Finite G]
    (hidx : ∀ N : Subgroup G, N.index ≠ 2) (S : Setting G) (f : S.M ≃* C0) (hf : f S.zM = tC) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.M ∧ g * S.z * g⁻¹ ≠ S.z := by
  classical
  by_contra hgoal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ = S.z := by
    intro g hg
    by_contra hne
    exact hgoal ⟨g, hg, hne⟩
  have htC_mem : tC ∈ P0 := by
    rw [P0]
    have h : a1C * a1C = tC := by
      apply Subtype.ext
      apply Subtype.ext
      exact alpha1_sq
    rw [← h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  obtain ⟨P, hP_eq, hP_center⟩ := exists_sylow_eq_map_P0 S f hf
  have hP_le_M : (P : Subgroup G) ≤ S.M := by
    rw [hP_eq]
    exact Subgroup.map_subtype_le _
  have hzP : S.z ∈ (P : Subgroup G) := by
    rw [hP_eq]
    refine Subgroup.mem_map.mpr ⟨S.zM, ?_, rfl⟩
    refine Subgroup.mem_map.mpr ⟨tC, htC_mem, ?_⟩
    rw [← hf]
    exact f.symm_apply_apply S.zM
  have hz_centerIn : S.z ∈ centerIn (G := G) (P : Subgroup G) := by
    refine ⟨hzP, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.mp (hP_le_M hd)
  have hcenterP : centerIn (G := G) (P : Subgroup G) = Subgroup.zpowers S.z := by
    apply le_antisymm
    · intro c hc
      rcases hP_center c hc.1 (fun d hd =>
        (Subgroup.mem_centralizer_iff.mp hc.2 d hd).symm) with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers S.z
    · rw [Subgroup.zpowers_le]
      exact hz_centerIn
  have hpnormal : ∀ T : Sylow 2 G, centerIn (G := G) (P : Subgroup G) ≤ (T : Subgroup G) →
      centerIn (G := G) (P : Subgroup G) = centerIn (G := G) (T : Subgroup G) := by
    intro T hle
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
    have hPT : (T : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hcenterT : centerIn (G := G) (T : Subgroup G) =
        (centerIn (G := G) (P : Subgroup G)).map (MulAut.conj g).toMonoidHom := by
      rw [hPT, centerIn_eq_map_center, centerIn_eq_map_center]
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map] at hx ⊢
        rcases hx with ⟨y, hy, rfl⟩
        rcases Subgroup.mem_map.mp y.2 with ⟨p, hpP, hp_eq⟩
        refine ⟨p, ?_, hp_eq⟩
        rw [Subgroup.mem_map]
        refine ⟨⟨p, hpP⟩, ?_, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        have hz' : MulAut.conj g (z : G) ∈
            (P : Subgroup G).map (MulAut.conj g).toMonoidHom :=
          Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom z.2
        have hcomm := (Subgroup.mem_center_iff.mp hy) ⟨MulAut.conj g (z : G), hz'⟩
        have hp_eq' : MulAut.conj g p = y.val := hp_eq
        have hval : MulAut.conj g (z : G) * y.val = y.val * MulAut.conj g (z : G) := by
          have h := congrArg Subtype.val hcomm
          rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
          exact h
        have hval' : MulAut.conj g (z : G) * MulAut.conj g p =
            MulAut.conj g p * MulAut.conj g (z : G) := by
          rw [hp_eq']; exact hval
        exact (MulAut.conj g).injective (by
          simpa [map_mul] using hval')
      · intro hx
        rw [Subgroup.mem_map] at hx ⊢
        rcases hx with ⟨x, hxinner, rfl⟩
        rcases Subgroup.mem_map.mp hxinner with ⟨p0, hp0center, hp0_eq⟩
        have hxP : x ∈ P := by rw [← hp0_eq]; exact p0.2
        refine ⟨⟨MulAut.conj g x,
          Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hxP⟩, ?_, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        rcases Subgroup.mem_map.mp y.2 with ⟨q, hqP, hq_eq⟩
        have hcomm := (Subgroup.mem_center_iff.mp hp0center) ⟨q, hqP⟩
        have hcomm' : q * p0.val = p0.val * q := by
          simpa using congrArg Subtype.val hcomm
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hq_eq]
        change MulAut.conj g q * MulAut.conj g x =
          MulAut.conj g x * MulAut.conj g q
        rw [← map_mul, ← map_mul, ← hp0_eq]
        change MulAut.conj g (q * p0.val) = MulAut.conj g (p0.val * q)
        rw [hcomm']
    have hzmem : S.z ∈ centerIn (G := G) (P : Subgroup G) := by
      rw [hcenterP]
      exact Subgroup.mem_zpowers S.z
    have hzT : S.z ∈ (T : Subgroup G) := hle hzmem
    have hw_mem_T : MulAut.conj g S.z ∈ centerIn (G := G) (T : Subgroup G) := by
      rw [hcenterT]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzmem
    have hw_comm : S.z * MulAut.conj g S.z = MulAut.conj g S.z * S.z :=
      (Subgroup.mem_centralizer_iff.mp hw_mem_T.2) S.z hzT
    have hwM : MulAut.conj g S.z ∈ S.M := by
      rw [Setting.M, Subgroup.mem_centralizer_singleton_iff]
      exact hw_comm.symm
    have hw_eq : MulAut.conj g S.z = S.z := by
      have h := hW' g (by simpa [MulAut.conj_apply] using hwM)
      simpa [MulAut.conj_apply] using h
    have hw_eq' : (MulAut.conj g).toMonoidHom S.z = S.z := hw_eq
    rw [hcenterT, hcenterP, MonoidHom.map_zpowers, hw_eq']
  let ZN : Subgroup G :=
    Subgroup.normalizer ((centerIn (G := G) (P : Subgroup G) : Subgroup G) : Set G)
  have hZN_eq : ZN = S.M := by
    apply le_antisymm
    · intro g hg
      rw [Setting.M, Subgroup.mem_centralizer_singleton_iff]
      have hzmem : S.z ∈ centerIn (G := G) (P : Subgroup G) := by
        rw [hcenterP]
        exact Subgroup.mem_zpowers S.z
      have hw_mem : g * S.z * g⁻¹ ∈ centerIn (G := G) (P : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hg S.z).mp hzmem
      have hcomm : S.z * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * S.z :=
        (Subgroup.mem_centralizer_iff.mp hw_mem.2) S.z hzP
      have hwM : g * S.z * g⁻¹ ∈ S.M := by
        rw [Setting.M, Subgroup.mem_centralizer_singleton_iff]
        exact hcomm.symm
      have hw_eq : g * S.z * g⁻¹ = S.z := hW' g hwM
      have h := congrArg (fun x => x * g) hw_eq
      simpa [mul_assoc] using h
    · change S.M ≤
        Subgroup.normalizer ((centerIn (G := G) (P : Subgroup G) : Subgroup G) : Set G)
      rw [hcenterP, Subgroup.zpowers_eq_closure]
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer
        (Subgroup.closure ({S.z} : Set G) : Set G))
      rw [Subgroup.centralizer_closure ({S.z} : Set G)]
  obtain ⟨K, hKindex⟩ := exists_index_two_C0
  let eZN : ZN ≃* C0 := (MulEquiv.subgroupCongr hZN_eq).trans f
  let KZN : Subgroup ZN := K.comap eZN.toMonoidHom
  have hKZN_index : KZN.index = 2 := by
    change (K.comap eZN.toMonoidHom).index = 2
    rw [Subgroup.index_comap_of_surjective K eZN.surjective, hKindex]
  have hKZN_ne_top : KZN ≠ ⊤ := by
    intro h
    have h1 : KZN.index = 1 := by rw [h, Subgroup.index_top]
    omega
  have hres_le : hktAbelianPResidual 2 ZN ≤ KZN := by
    have hKnormal : KZN.Normal := Subgroup.normal_of_index_eq_two hKZN_index
    have : KZN.Normal := hKnormal
    have hcard : Nat.card (ZN ⧸ KZN) = 2 := by
      rw [← Subgroup.index_eq_card, hKZN_index]
    have hcomm : commutator ZN ≤ KZN :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
        (isCyclic_of_prime_card (p := 2) hcard).isMulCommutative
    have hpRes : hktPResidual 2 ZN ≤ KZN :=
      hktPResidual_le KZN hKnormal
        (IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num))
    exact hktAbelianPResidual_le hcomm hpRes
  have hres_ne_top : hktAbelianPResidual 2 ZN ≠ ⊤ := by
    intro h
    exact hKZN_ne_top (top_le_iff.mp (h ▸ hres_le))
  let : (hktAbelianPResidual 2 ZN).Normal := hktAbelianPResidual_normal
  have hNontrivZN : Nontrivial (ZN ⧸ hktAbelianPResidual 2 ZN) :=
    QuotientGroup.nontrivial_iff.mpr hres_ne_top
  let : (hktAbelianPResidual 2 G).Normal := hktAbelianPResidual_normal
  obtain ⟨e⟩ := huppert_IV_3_7_second_grun (Q := G) (q := 2) P hpnormal
  have hNontrivG : Nontrivial (G ⧸ hktAbelianPResidual 2 G) :=
    e.toEquiv.nontrivial
  have hPquot : IsPGroup 2 (G ⧸ hktAbelianPResidual 2 G) :=
    hktAbelianPResidual_quotient_isPGroup
  have : Group.IsNilpotent (G ⧸ hktAbelianPResidual 2 G) := hPquot.isNilpotent
  have : IsCoatomic (Subgroup (G ⧸ hktAbelianPResidual 2 G)) :=
    Finite.to_isCoatomic
  obtain ⟨K', hK'⟩ :=
    IsCoatomic.exists_coatom (Subgroup (G ⧸ hktAbelianPResidual 2 G))
  have hK'index : K'.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hPquot).mp hK'
  let K'' : Subgroup G := K'.comap (QuotientGroup.mk' (hktAbelianPResidual 2 G))
  have hK''index : K''.index = 2 := by
    change (K'.comap (QuotientGroup.mk' (hktAbelianPResidual 2 G))).index = 2
    rw [Subgroup.index_comap_of_surjective K' (QuotientGroup.mk'_surjective _), hK'index]
  exact hidx K'' hK''index

end CFSG.Literature.Janko67
