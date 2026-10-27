module

public import CFSG.CGT.T75E.Iso
public import CFSG.CGT.T75E.WcLocal
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

section Primitive


theorem isPreprimitive_P : MulAction.IsPreprimitive ↥P (Fin 315) := by
  have := CFSG.Sporadic.J2.isPreprimitive
  exact MulAction.IsPreprimitive.of_surjective (M := ↥CFSG.Sporadic.J2.J) (φ := ⇑jEquivP)
    (f := (⟨id, fun _ _ => rfl⟩ : Fin 315 →ₑ[⇑jEquivP] Fin 315)) Function.surjective_id

theorem isCoatom_stabilizer_P (q : Fin 315) : IsCoatom (MulAction.stabilizer ↥P q) := by
  have := isPreprimitive_P
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive ↥P q

theorem card_stabilizer_P (q : Fin 315) : Nat.card (MulAction.stabilizer ↥P q) = 1920 := by
  have := isPreprimitive_P
  have h1 : Nat.card (MulAction.orbit ↥P q) * Nat.card (MulAction.stabilizer ↥P q) =
      Nat.card ↥P := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥P q)]
  have h2 : Nat.card (MulAction.orbit ↥P q) = 315 := by
    rw [MulAction.orbit_eq_univ, Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h2, card_P] at h1
  omega

end Primitive

section Classes


@[expose] noncomputable def tP : ↥P := ⟨permTwoA, permTwoA_mem⟩

theorem cent2A_fix_314 : ∀ g ∈ cent2AChain.originalSubgroup, g (314 : Fin 315) = 314 := by
  intro g hg
  have hle : cent2AChain.originalSubgroup ≤
      MulAction.stabilizer (Equiv.Perm (Fin 315)) (314 : Fin 315) := by
    rw [cent2AChain, ofArrays_originalSubgroup, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hc := cent2A_check.1
    rw [← Kernel.cent2ABase_eq] at hc
    have hrep := rep_permOfArr_of_chainOK hc (j := i) (by
      have : cent2AStrong.size = 5 := rfl
      omega)
    have h314 := hrep ⟨314, by norm_num⟩
    have hfix : (cent2AStrong[i]!)[314]! = 314 := by interval_cases i <;> decide +kernel
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    apply Fin.ext
    show ((Monster.B.Co2.permOfArr 315 cent2AStrong[i]!) ⟨314, by norm_num⟩ : ℕ) = 314
    rw [← h314, hfix]
  exact hle hg

theorem centralizer_tP :
    Subgroup.centralizer ({tP} : Set ↥P) = MulAction.stabilizer ↥P (314 : Fin 315) := by
  have hle : Subgroup.centralizer ({tP} : Set ↥P) ≤ MulAction.stabilizer ↥P (314 : Fin 315) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hmem : (g : Equiv.Perm (Fin 315)) ∈ centralizerIn P permTwoA :=
      mem_centralizerIn.2 ⟨g.2, congrArg Subtype.val hg⟩
    rw [(inner_classes).2.2.2.2] at hmem
    rw [MulAction.mem_stabilizer_iff]
    exact cent2A_fix_314 _ hmem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_stabilizer_P,
    CFSG.ComponentClassification.M12Cover.card_centralizer_eq_centralizerIn P tP]
  show 1920 ≤ Nat.card (centralizerIn P permTwoA)
  rw [(inner_classes).2.2.2.2]
  exact cent2A_facts.2.1.ge

theorem isCoatom_centralizer_conj_tP (c : ↥P) :
    IsCoatom (Subgroup.centralizer ({c * tP * c⁻¹} : Set ↥P)) := by
  have h : Subgroup.centralizer ({c * tP * c⁻¹} : Set ↥P) =
      MulAction.stabilizer ↥P (c • (314 : Fin 315)) := by
    ext g
    have hg : g ∈ Subgroup.centralizer ({c * tP * c⁻¹} : Set ↥P) ↔
        c⁻¹ * g * c ∈ Subgroup.centralizer ({tP} : Set ↥P) := by
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc c⁻¹ * g * c * tP = c⁻¹ * (g * (c * tP * c⁻¹)) * c := by group
          _ = c⁻¹ * (c * tP * c⁻¹ * g) * c := by rw [h]
          _ = tP * (c⁻¹ * g * c) := by group
      · intro h
        calc g * (c * tP * c⁻¹) = c * (c⁻¹ * g * c * tP) * c⁻¹ := by group
          _ = c * (tP * (c⁻¹ * g * c)) * c⁻¹ := by rw [h]
          _ = c * tP * c⁻¹ * g := by group
    rw [hg, centralizer_tP, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      rw [mul_smul, mul_smul] at h
      exact inv_smul_eq_iff.1 h
    · intro h
      rw [mul_smul, mul_smul, h, inv_smul_smul]
  rw [h]
  exact isCoatom_stabilizer_P _

end Classes

section Main


theorem orderOf_ne_four_of_mem_centralizerIn_permA {y : Equiv.Perm (Fin 315)}
    (hy : y ∈ centralizerIn P permA) : orderOf y ≠ 4 := by
  intro h4
  obtain ⟨reps, -, hcov, -, hsz⟩ := Kernel.centralizerIn_P_permA.2.2
  obtain ⟨r, hr, -⟩ := hcov y hy h4
  have : reps = [] := List.map_eq_nil_iff.1 hsz
  rw [this] at hr
  exact List.not_mem_nil hr

theorem lemma26Hyp_false_P {T : Subgroup ↥P} (hyp : Lemma26Hyp ↥P T) (hnd : Lemma26Nondeg T) :
    False := by
  have : IsSimpleGroup ↥P := isSimpleGroup_P
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hyp_ne_bot hyp)
  have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
  have haD : a ∈ classD T := mem_classD_of_mem ha ha1'
  have ha2 : orderOf a = 2 := hyp.2.2.2.1.1 a haD
  have ha2' : orderOf (a : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ha2
  obtain ⟨r, hr, c, hc, hac⟩ := inner_classes.1 (a : Equiv.Perm (Fin 315)) a.2 ha2'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  ·
    obtain ⟨d, hd, e, he, h4⟩ := hnd
    have hz : (d * e) ^ 2 ∈ classD T := hyp.2.2.2.1.2.2 d hd e he h4
    obtain ⟨w, hw⟩ := isConj_iff.1 (hyp_isConj_of_mem_classD hyp haD hz)
    have hcP : a = (⟨c, hc⟩ : ↥P) * ⟨permA, permA_mem⟩ * (⟨c, hc⟩ : ↥P)⁻¹ := Subtype.ext hac
    set u : ↥P := w * ⟨c, hc⟩ with hu
    have hz' : (d * e) ^ 2 = u * ⟨permA, permA_mem⟩ * u⁻¹ := by
      rw [← hw, hcP, hu]
      group
    set y : ↥P := u⁻¹ * (d * e) * u with hy
    have hy4 : orderOf y = 4 := by rw [hy, orderOf_inv_mul_mul_eq]; exact h4
    have hy2 : y ^ 2 = ⟨permA, permA_mem⟩ := by
      have h1 : y ^ 2 = u⁻¹ * (d * e) ^ 2 * u := by
        rw [hy, pow_two, pow_two]
        group
      rw [h1, hz']
      group
    have hmem : (y : Equiv.Perm (Fin 315)) ∈ centralizerIn P permA := by
      refine mem_centralizerIn.2 ⟨y.2, ?_⟩
      have h2 : (y : Equiv.Perm (Fin 315)) ^ 2 = permA := by
        rw [← Subgroup.coe_pow, hy2]
      rw [← h2]
      group
    exact orderOf_ne_four_of_mem_centralizerIn_permA hmem (by rw [Subgroup.orderOf_coe]; exact hy4)
  ·
    have hcP : a = (⟨c, hc⟩ : ↥P) * tP * (⟨c, hc⟩ : ↥P)⁻¹ := Subtype.ext hac
    exact hyp_false_of_isCoatom_centralizer hyp ha ha1'
      (by rw [hcP]; exact isCoatom_centralizer_conj_tP ⟨c, hc⟩)

end Main

section Excl


theorem j2_excl : Lemma26ExclAt fun K => CFSG.Blueprint.NativeSporadic.IsSporadic K .J2 := by
  intro K _ _ _ T hyp hnd hJ
  obtain ⟨e⟩ := hJ
  have e' : K ≃* ↥P := e.trans nativeEquivP
  exact lemma26Hyp_false_P (lemma26Hyp_map_mulEquiv e' hyp) (lemma26Nondeg_map_mulEquiv e' hnd)

end Excl

end CFSG.CGT.T75E
