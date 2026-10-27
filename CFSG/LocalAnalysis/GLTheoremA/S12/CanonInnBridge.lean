module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonInn

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup map_fixSubgroup_le
  normal_map_fixSubgroup)

variable {Γ : Type} [Group Γ]

theorem mem_fixSubgroup_conjAut (L : Subgroup Γ) {y : Γ} (hy : y ∈ Subgroup.normalizer (L : Set Γ))
    (l : L) : l ∈ fixSubgroup (conjAut L y hy) ↔ (l : Γ) ∈ Subgroup.centralizer ({y} : Set Γ) := by
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [coe_conjAut] at h'
    calc (l : Γ) * y = y * (y⁻¹ * l * y) := by group
      _ = y * l := by rw [h']
  · intro h
    apply Subtype.ext
    rw [coe_conjAut]
    calc y⁻¹ * (l : Γ) * y = y⁻¹ * ((l : Γ) * y) := by group
      _ = y⁻¹ * (y * l) := by rw [h]
      _ = l := by group

theorem fixSubgroup_conjAut_eq (L : Subgroup Γ) {y : Γ} (hy : y ∈ Subgroup.normalizer (L : Set Γ)) :
    fixSubgroup (conjAut L y hy) = (L ⊓ Subgroup.centralizer ({y} : Set Γ)).comap L.subtype := by
  ext l
  rw [mem_fixSubgroup_conjAut, Subgroup.mem_comap, Subgroup.mem_inf]
  exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩

theorem conjAut_pow (L : Subgroup Γ) {y : Γ} (hy : y ∈ Subgroup.normalizer (L : Set Γ)) {p : ℕ}
    (hyp : y ^ p = 1) : conjAut L y hy ^ p = 1 := by
  unfold conjAut
  rw [← map_pow]
  have : (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : Subgroup.normalizer (L : Set Γ)) ^ p = 1 :=
    Subtype.ext (by simp [hyp])
  rw [this, map_one]

theorem isComponentOf_fixSubgroup_conjAut (L : Subgroup Γ) {y : Γ}
    (hy : y ∈ Subgroup.normalizer (L : Set Γ)) {K : Subgroup Γ}
    (hK : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ))) :
    IsComponentOf (K.subgroupOf L) (fixSubgroup (conjAut L y hy)) := by
  have hKL : K ≤ L := hK.1.trans inf_le_left
  refine ⟨?_, ?_, hK.2.2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)⟩
  · rw [fixSubgroup_conjAut_eq]
    exact Subgroup.comap_mono hK.1
  · have h := CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_inf_comap L.subtype hK.2.1 ⊤
    rw [top_inf_eq, top_inf_eq, ← fixSubgroup_conjAut_eq] at h
    exact h

section Quotient

variable {X : Type} [Group X]

theorem isComponentOf_map_centerQuot (α : MulAut X) {J : Subgroup X}
    (hJ : IsComponentOf J (fixSubgroup α)) :
    IsComponentOf (J.map (QuotientGroup.mk' (Subgroup.center X)))
      (fixSubgroup (centerQuotAut X α)) := by
  set π := QuotientGroup.mk' (Subgroup.center X)
  have hker : π.ker ≤ Subgroup.center X := by rw [QuotientGroup.ker_mk']
  have hαβ : ∀ k, π (α k) = centerQuotAut X α (π k) := fun k => (centerQuotAut_mk X α k).symm
  have hmapC := map_fixSubgroup_le π hker α (centerQuotAut X α) hαβ
  have h1 := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map π
    (fun g hg => hker (MonoidHom.mem_ker.2 hg)) hJ
  refine CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_trans h1 ?_
  exact CFSG.Open.IsSubnormal.step hmapC
    (normal_map_fixSubgroup π hker α (centerQuotAut X α) hαβ (QuotientGroup.mk'_surjective _))
    (CFSG.Open.IsSubnormal.refl _)

theorem hasLabel_map_centerQuot {J : Subgroup X} {T : GLALabel → Prop} (hJl : HasLabel ↥J T) :
    HasLabel ↥(J.map (QuotientGroup.mk' (Subgroup.center X))) T := by
  set π := QuotientGroup.mk' (Subgroup.center X)
  have hqJ : CFSG.Open.IsQuasisimple ↥J := hasLabel_isQuasisimple hJl
  let φ : ↥J →* ↥(J.map π) :=
    (π.comp J.subtype).codRestrict _ (fun j => Subgroup.mem_map_of_mem π j.2)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨_, ⟨j, hj, rfl⟩⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  haveI hperf : Group.IsPerfect ↥J := ⟨hqJ.1⟩
  have hker : φ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have hj1 : π (j : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hj)
    have hjZ : (j : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).1 hj1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hjZ (g : X)
  obtain ⟨e⟩ := quotEquiv_of_perfect_central φ hφsurj hperf hker
  exact hasLabel_of_equiv_centerQuot
    ((Group.IsPerfect.ofSurjective (f := φ) hφsurj).commutator_eq_top) e hJl

end Quotient

theorem mk'_bijective_of_center_eq_bot {S : Type} [Group S] (h : Subgroup.center S = ⊥) :
    Function.Bijective (QuotientGroup.mk' (Subgroup.center S)) := by
  refine ⟨fun a b hab => ?_, QuotientGroup.mk'_surjective _⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, h,
    Subgroup.mem_bot, inv_mul_eq_one] at hab
  exact hab

noncomputable def quotCenterEquivOfBot {S : Type} [Group S] (h : Subgroup.center S = ⊥) :
    S ⧸ Subgroup.center S ≃* S :=
  (MulEquiv.ofBijective _ (mk'_bijective_of_center_eq_bot h)).symm

theorem quotCenterEquivOfBot_mk {S : Type} [Group S] (h : Subgroup.center S = ⊥) (s : S) :
    quotCenterEquivOfBot h (QuotientGroup.mk s) = s := by
  rw [quotCenterEquivOfBot, MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply,
    QuotientGroup.mk'_apply]

theorem innDiagKind_centerQuot {L : Subgroup Γ} {y : Γ} {lab : GLALabel}
    (hy : y ∈ Subgroup.normalizer (L : Set Γ)) (hM : MarkedInnDiag L y lab) :
    InnDiagKind (↥L ⧸ Subgroup.center ↥L) lab (centerQuotAut ↥L (conjAut L y hy)) := by
  have hLl : HasLabel ↥L (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hM
  have hq := hasLabel_isQuasisimple hLl
  have hcen := center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hS : commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨-, lab', hlam, hraw⟩ := hM
  refine ⟨hS, lab', hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hlab, φ, hφ, hind⟩
  refine ⟨hs, hna, (quotCenterEquivOfBot hcen).trans θ, hlab, φ, hφ, ?_⟩
  intro s s' hss'
  subst hss'
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective s
  rw [centerQuotAut_mk, MulEquiv.trans_apply, MulEquiv.trans_apply, quotCenterEquivOfBot_mk,
    quotCenterEquivOfBot_mk]
  exact hind l (conjAut L y hy l) (coe_conjAut L hy l)

theorem marked_bridge {L K : Subgroup Γ} {y : Γ} {labL : GLALabel} {p : ℕ}
    (hy : y ∈ Subgroup.normalizer (L : Set Γ)) (hyp : y ^ p = 1) (hM : MarkedInnDiag L y labL)
    (hK : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set Γ))) {T : GLALabel → Prop}
    (hKl : HasLabel ↥K T) :
    Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ ∧
      InnDiagKind (↥L ⧸ Subgroup.center ↥L) labL (centerQuotAut ↥L (conjAut L y hy)) ∧
      centerQuotAut ↥L (conjAut L y hy) ^ p = 1 ∧
      IsComponentOf ((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
        (fixSubgroup (centerQuotAut ↥L (conjAut L y hy))) ∧
      HasLabel ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) T := by
  have hLl : HasLabel ↥L (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hM
  have hKL : K ≤ L := hK.1.trans inf_le_left
  refine ⟨center_centerQuot_eq_bot (hasLabel_isQuasisimple hLl), innDiagKind_centerQuot hy hM,
    by rw [← map_pow, conjAut_pow L hy hyp, map_one],
    isComponentOf_map_centerQuot _ (isComponentOf_fixSubgroup_conjAut L hy hK),
    hasLabel_map_centerQuot ((hasLabel_congr (Subgroup.subgroupOfEquivOfLe hKL) T).2 hKl)⟩

end CFSG.LocalAnalysis.GLTheoremA.CanonInn

end
