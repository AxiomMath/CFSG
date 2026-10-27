module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneP

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_eq_of_isMaximalTwoLocal_le_normalizer {M W : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hW : IsPGroup 2 W) (hW1 : W ≠ ⊥)
    (hMW : M ≤ Subgroup.normalizer (W : Set G)) : Subgroup.normalizer (W : Set G) = M := by
  by_contra hne
  exact hM.2 _ (lt_of_le_of_ne hMW (Ne.symm hne)) (isPLocal_normalizer_of_isPGroup hW hW1)

omit [Finite G] in
theorem mem_normalizer_normalClosureIn_blockU {X M : Subgroup G} {g : G}
    (hg : ∀ m ∈ M, g ∈ Subgroup.normalizer (conjugate X m : Set G)) :
    g ∈ Subgroup.normalizer (normalClosureIn M (blockU X) : Set G) := by
  have key : ∀ a : G, (∀ m ∈ M, a ∈ Subgroup.normalizer (conjugate X m : Set G)) →
      ∀ w ∈ normalClosureIn M (blockU X), a * w * a⁻¹ ∈ normalClosureIn M (blockU X) := by
    intro a ha w hw
    have hle : normalClosureIn M (blockU X) ≤
        (normalClosureIn M (blockU X)).comap (MulAut.conj a).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨m, hm, u, hu, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hmu : m * u * m⁻¹ ∈ blockU (conjugate X m⁻¹) := by
        rw [blockU_conjugate]
        exact ⟨u, hu, by simp [MulAut.conj_apply]⟩
      have h1 := conj_mem_blockU (ha m⁻¹ (inv_mem hm)) hmu
      rw [blockU_conjugate] at h1
      obtain ⟨u', hu', he⟩ := h1
      rw [← he]
      exact Subgroup.subset_closure ⟨m, hm, u', hu', by simp [MulAut.conj_apply]⟩
    have := hle hw
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨key g hg w, fun hw => ?_⟩
  have := key g⁻¹ (fun m hm => inv_mem (hg m hm)) _ hw
  simpa [mul_assoc] using this

theorem normalizer_normalClosureIn_blockU_eq {X M : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hX : IsShortGroup X) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) :
    Subgroup.normalizer (normalClosureIn M (blockU X) : Set G) = M := by
  have hUQ : blockU X ≤ oTwoIn M :=
    (blockU_le_oTwoIn X).trans (ThreeFromEight.oTwoIn_le_oTwoIn_of_isSubnormal hXM hsub)
  have hWQ : normalClosureIn M (blockU X) ≤ oTwoIn M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨m, hm, u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (SixThree.le_normalizer_oTwoIn M hm) u).mp (hUQ hu)
  refine normalizer_eq_of_isMaximalTwoLocal_le_normalizer hM ((isPGroup_oTwoIn M).to_le hWQ)
    (fun h => ?_) le_normalizer_normalClosureIn
  exact blockU_ne_bot_of_short hX (le_bot_iff.mp (h ▸ le_normalClosureIn))

theorem exists_mem_normalizer_not_mem_of_lt_isPGroup_two {Q T : Subgroup G} (hT : IsPGroup 2 T)
    (hQT : Q < T) : ∃ w ∈ T, w ∈ Subgroup.normalizer (Q : Set G) ∧ w ∉ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hT.isNilpotent
  have hlt : Q.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact absurd (Subgroup.subgroupOf_eq_top.mp h) (not_le_of_gt hQT)
  obtain ⟨w, hw, hwQ⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨w, w.2, ?_, fun h => hwQ (Subgroup.mem_subgroupOf.mpr h)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hw ⟨g, hQT.le hg⟩).mp
      (Subgroup.mem_subgroupOf.mpr hg))
  · intro hg
    have hgT : g ∈ T := by
      rw [show g = (w : G)⁻¹ * ((w : G) * g * (w : G)⁻¹) * w by group]
      exact mul_mem (mul_mem (inv_mem w.2) (hQT.le hg)) w.2
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hw ⟨g, hgT⟩).mpr
      (Subgroup.mem_subgroupOf.mpr hg))

theorem oTwoIn_le_of_oTwoIn_inf_eq {M H : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hQH : oTwoIn M ≤ H) (h31 : oTwoIn (H ⊓ M) = oTwoIn M) : oTwoIn H ≤ oTwoIn M := by
  have hT : IsPGroup 2 (oTwoIn H ⊔ oTwoIn M : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_oTwoIn H) (isPGroup_oTwoIn M)
      (hQH.trans (SixThree.le_normalizer_oTwoIn H))
  have hTH : oTwoIn H ⊔ oTwoIn M ≤ H := sup_le (oTwoIn_le H) hQH
  have hTM : (oTwoIn H ⊔ oTwoIn M) ⊓ M ≤ oTwoIn M := by
    refine le_trans ?_ h31.le
    refine SixThree.le_oTwoIn_of_isPGroup (inf_le_inf_right M hTH) (hT.to_le inf_le_left) ?_
    refine (le_inf ?_ (inf_le_right.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf (inf_le_left.trans (SixThree.le_normalizer_oTwoIn H))
      (inf_le_right.trans (SixThree.le_normalizer_oTwoIn M))).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  by_contra hne
  have hlt : oTwoIn M < oTwoIn H ⊔ oTwoIn M :=
    lt_of_le_of_ne le_sup_right fun h => hne (le_sup_left.trans h.ge)
  obtain ⟨w, hwT, hwN, hwQ⟩ := exists_mem_normalizer_not_mem_of_lt_isPGroup_two hT hlt
  rw [normalizer_oTwoIn_eq_of_isMaximalTwoLocal hM] at hwN
  exact hwQ (hTM (Subgroup.mem_inf.mpr ⟨hwT, hwN⟩))

theorem eq_of_forall_conjugate_isSubnormal {X M H : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hH : IsMaximalTwoLocal H) (hX : InClassX X) (hXM : X ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal)
    (hCH : M ⊓ Subgroup.centralizer (blockU X : Set G) ≤ H)
    (hconj : ∀ m ∈ M, conjugate X m ≤ H ∧ ((conjugate X m).subgroupOf H).IsSubnormal) :
    H = M := by
  have hXH : X ≤ H := by simpa [ThreeFromEight.conjugate_one] using (hconj 1 M.one_mem).1
  have hQH : oTwoIn M ≤ H := (le_inf (oTwoIn_le M)
    (le_centralizer_blockU_of_le_centralizerModCore hX.1 (isPGroup_oTwoIn M)
      (oTwoIn_le_centralizerModCore_of_isSubnormal hX.1.residual_eq hXM hsub))).trans hCH
  have hRQ := oTwoIn_le_of_oTwoIn_inf_eq hM hQH (oTwoIn_inf_eq hX hXM hsub hXH hCH)
  set Qb := ((oTwoIn M).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) with hQb
  let Xb : G → Subgroup (H ⧸ pCore 2 H) := fun m =>
    ((conjugate X m).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  have h2 : pCore 2 (H ⧸ pCore 2 H) = ⊥ := pCore_quotient_by_pCore_eq_bot _ 2
  have hQb2 : IsPGroup 2 Qb := ((isPGroup_oTwoIn M).comap_subtype).map _
  have hXm : ∀ m : G, InClassX (conjugate X m) := fun m => inClassX_conjugate hX m
  have hXbs : ∀ m ∈ M, (Xb m).IsSubnormal := fun m hm =>
    (hconj m hm).2.map (QuotientGroup.mk'_surjective _)
  have hXbQ : ∀ m ∈ M, Xb m ≤ Subgroup.centralizer (Qb : Set _) := fun m hm =>
    map_mk_le_centralizer (hconj m hm).1 (hconj m hm).2
      (oTwoIn_le_centralizerModCore_of_isSubnormal (hXm m).1.residual_eq
        (CFSG.GroupTheory.conjugate_le_of_mem hXM hm) (isSubnormal_conjugate hsub hm))
  have hW := normalizer_normalClosureIn_blockU_eq hM hX.1 hXM hsub
  have hkeyN : ∀ y : H, (∀ m ∈ M, QuotientGroup.mk' (pCore 2 H) y ∈
      Subgroup.centralizer (Xb m : Set _)) →
      QuotientGroup.mk' (pCore 2 H) y ∈ Subgroup.normalizer (Qb : Set _) := by
    intro y hy
    have hyM : (y : G) ∈ M := by
      rw [← hW]
      exact mem_normalizer_normalClosureIn_blockU fun m hm =>
        (mem_centralizerModCore_of_mk_mem_centralizer (hXm m).1.residual_eq (hconj m hm).1
          (hconj m hm).2 (hy m hm)).1
    exact mk_oTwo_mem_normalizer_map (SixThree.le_normalizer_oTwoIn M hyM)
  have hE : ∀ J : Subgroup (H ⧸ pCore 2 H), IsComponent J → ⁅J, Qb⁆ = ⊥ := by
    intro J hJ
    by_cases hJX : ∃ m ∈ M, J ≤ Xb m
    · obtain ⟨m, hm, hle⟩ := hJX
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans (hXbQ m hm))
    · have hJC : ∀ m ∈ M, J ≤ Subgroup.centralizer (Xb m : Set _) := fun m hm =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          ((LocalCores.component_subnormal_subgroup hJ (hXbs m hm)).resolve_left
            fun hle => hJX ⟨m, hm, hle⟩)
      refine commutator_eq_bot_of_isComponent_of_le_normalizer hJ hQb2 fun j hj => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) j
      exact hkeyN y fun m hm => hJC m hm hj
  have hkey : ∀ f ∈ fittingSubgroup (H ⧸ pCore 2 H),
      (∀ m ∈ M, f ∈ Subgroup.centralizer (Xb m : Set _)) →
      f ∈ Subgroup.centralizer (Qb : Set _) := by
    intro f hf hfX
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) f
    have hyN := hkeyN y hfX
    refine mem_centralizer_of_commutator_mem_normalizer h2 hQb2 hf fun q hq => ?_
    have hqN := Subgroup.le_normalizer hq
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hyN hqN) (inv_mem hyN)) (inv_mem hqN)
  have hF : ⁅fittingSubgroup (H ⧸ pCore 2 H), Qb⁆ = ⊥ := by
    rcases hX.1.quotient_type with hq | hp
    ·
      have hFX : ∀ m ∈ M, fittingSubgroup (H ⧸ pCore 2 H) ≤
          Subgroup.centralizer (Xb m : Set _) := fun m hm => by
        have hqm : IsQuasisimple (conjugate X m ⧸ pCore 2 (conjugate X m)) :=
          LocalCores.isQuasisimple_of_mulEquiv
            (quotTopEquiv ((MulAut.conj m⁻¹).subgroupMap X)) hq
        have hXbE : Xb m ≤ layer _ :=
          le_sSup (isComponent_map_mk_oTwo hqm (hconj m hm).1 (hconj m hm).2)
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp
          ((Subgroup.commutator_mono le_rfl hXbE).trans LocalCores.fitting_layer_commute.le))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun f hf =>
        hkey f hf fun m hm => hFX m hm hf
    ·
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3 := card_top_eq_three_of_inClassX hX hp
      have h3m : ∀ m : G, Nat.card (conjugate X m ⧸ pCore 2 (conjugate X m)) = 3 := fun m => by
        rw [← h3]
        exact (Nat.card_congr (quotTopEquiv ((MulAut.conj m⁻¹).subgroupMap X)).toEquiv).symm
      have hYF : (⨆ m ∈ M, Xb m) ≤ fittingSubgroup (H ⧸ pCore 2 H) := iSup₂_le fun m hm =>
        (le_pCore_of_isSubnormal_of_isPGroup (hXbs m hm)
          (isPGroup_map_mk_oTwo (h3m m) (hconj m hm).1 (hconj m hm).2)).trans (pCore_le_fitting _ 3)
      exact commutator_fittingSubgroup_eq_bot_of_le_centralizer h2 hQb2 hYF
        (iSup₂_le fun m hm => hXbQ m hm) fun f hf hfY => hkey f hf fun m hm => by
          have hle : Xb m ≤ ⨆ m ∈ M, Xb m := le_iSup₂_of_le m hm le_rfl
          exact Subgroup.centralizer_le hle hfY
  have hQR : oTwoIn M ≤ oTwoIn H :=
    le_oTwoIn_of_map_mk_eq_bot hQH (eq_bot_of_commutator_eq_bot h2 hQb2 hE hF)
  have hHM : H ≤ M := by
    rw [← normalizer_oTwoIn_eq_of_isMaximalTwoLocal hM, ← le_antisymm hRQ hQR]
    exact SixThree.le_normalizer_oTwoIn H
  by_contra hne
  exact hH.2 M (lt_of_le_of_ne hHM hne) hM.1

theorem exists_conjugate_not_isSubnormal {X M H : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hH : IsMaximalTwoLocal H) (hX : InClassX X) (hXM : X ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal)
    (hCH : M ⊓ Subgroup.centralizer (blockU X : Set G) ≤ H) (hne : H ≠ M)
    (hle : ∀ m ∈ M, conjugate X m ≤ H) :
    ∃ m ∈ M, ¬ ((conjugate X m).subgroupOf H).IsSubnormal := by
  by_contra h
  exact hne (eq_of_forall_conjugate_isSubnormal hM hH hX hXM hsub hCH fun m hm =>
    ⟨hle m hm, not_not.mp fun hs => h ⟨m, hm, hs⟩⟩)

end CFSG.CGT.PushingUpLit.ThmOne
