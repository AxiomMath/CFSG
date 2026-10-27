module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Fi22D4
public import CFSG.HardMathSupport.Solomon.Proving.Fi22Facts
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.Native CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Fischer CFSG.Open

theorem i242_isDFourTwo_of_equiv {Y : Type} [Group Y]
    (e : Y ≃* omegaT) : IsDFourTwo Y := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 2 1 := ⟨Nat.prime_two, le_rfl, le_refl 4⟩
  have hmod : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2)))) .POmegaPlus 4 2 1 :=
    ⟨hadm, ZMod 2, inferInstance, inferInstance, by simp, ⟨MulEquiv.refl _⟩⟩
  have hLie : CFSG.Blueprint.LieModel
      (StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2)))) .POmegaPlus 4 2 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmod⟩
  obtain ⟨f⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT hLie
  exact ⟨hadm, ZMod 2, inferInstance, inferInstance, by simp, ⟨e.trans f.symm⟩⟩

theorem i242_reduction
    {K : Type} [Group K] [Finite K] (hF : Fi22Facts) (hK : IsFiTwentyTwo K)
    (θ : K ≃* fi22P) (Y0 : Subgroup (Equiv.Perm (Fin 3510)))
    (hY0 : Y0 ≤ ⨆ i : Fin 6, fi22FiveD i) (A : Subgroup (MulAut K)) (hA : IsElemAbelian 5 A)
    (hAc : Nat.card A = 5 ^ 2) :
    ∃ Y : Subgroup K, Y ≤ (⨆ φ ∈ A, ⨆ (_ : φ ≠ 1), fixSub φ) ∧ Nonempty (Y ≃* Y0) := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcen, hfac, -, hinner⟩ := hF K hK
  have hψinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro a b hab
    have : a⁻¹ * b ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ : MulAut K => φ x) hab
      simp only [MulAut.conj_apply] at this
      have h2 : a * x * a⁻¹ = b * x * b⁻¹ := this
      calc x * (a⁻¹ * b) = a⁻¹ * (a * x * a⁻¹) * b := by group
        _ = a⁻¹ * (b * x * b⁻¹) * b := by rw [h2]
        _ = a⁻¹ * b * x := by group
    rw [hcen, Subgroup.mem_bot] at this
    exact (inv_mul_eq_one.1 this)
  set A0 : Subgroup K := A.comap (MulAut.conj : K →* MulAut K) with hA0
  have hAle : A ≤ (MulAut.conj : K →* MulAut K).range := by
    intro φ hφ
    have hord : φ ^ 5 = 1 := hA.2 φ hφ
    have hd : orderOf φ ∣ 5 := orderOf_dvd_of_pow_eq_one hord
    have hp : IsPGroup 5 (Subgroup.zpowers φ) := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hd with h1 | h1
      · exact IsPGroup.iff_card.2 ⟨0, by rw [Nat.card_zpowers, h1]; simp⟩
      · exact IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, h1]; simp⟩
    obtain ⟨k, hk⟩ := hinner φ hp
    exact ⟨k, hk.symm⟩
  have hA0map : A0.map (MulAut.conj : K →* MulAut K) = A := by
    rw [hA0, Subgroup.map_comap_eq, inf_eq_right.2 hAle]
  have hA0card : Nat.card A0 = 5 ^ (Nat.card K).factorization 5 := by
    rw [hfac, ← hAc, ← hA0map, Subgroup.card_map_of_injective hψinj]
  set Q' : Subgroup fi22P := fi22FiveQ.subgroupOf fi22P with hQ'
  set QK : Subgroup K := Q'.map θ.symm.toMonoidHom with hQK
  have hQ'card : Nat.card Q' = 25 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22FiveQ_le_P).toEquiv).trans card_fi22FiveQ
  have hQKcard : Nat.card QK = 5 ^ (Nat.card K).factorization 5 := by
    rw [hfac, hQK, Subgroup.card_map_of_injective θ.symm.injective, hQ'card]
    norm_num
  let SA : Sylow 5 K := Sylow.ofCard A0 hA0card
  let SQ : Sylow 5 K := Sylow.ofCard QK hQKcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K SQ SA
  have hgmap : (SA : Subgroup K) = QK.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hSA : (SA : Subgroup K) = A0 := rfl
  let xP : Fin 6 → fi22P := fun i => ⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩
  let aK : Fin 6 → K := fun i => g * θ.symm (xP i) * g⁻¹
  have haA0 : ∀ i, aK i ∈ A0 := by
    intro i
    rw [← hSA, hgmap]
    refine ⟨θ.symm (xP i), ⟨xP i, ?_, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (fi22FiveLine_mem_Q i)
  have haone : ∀ i, MulAut.conj (aK i) ≠ 1 := by
    intro i h
    have h1 : aK i = 1 := hψinj (by rw [h, map_one])
    have h2 : θ.symm (xP i) = 1 := by
      have : g * θ.symm (xP i) * g⁻¹ = 1 := h1
      simpa using this
    have h3 : xP i = 1 := θ.symm.injective (by rw [h2, map_one])
    exact fi22FiveLine_ne_one i (congrArg Subtype.val h3)
  let ci : Fin 6 → Subgroup K := fun i =>
    (((fi22FiveD i).subgroupOf fi22P).map θ.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom
  have hci : ∀ i, ci i ≤ ⨆ φ ∈ A, ⨆ (_ : φ ≠ 1), fixSub φ := by
    intro i
    refine le_trans ?_ (le_iSup₂_of_le (MulAut.conj (aK i)) (haA0 i)
      (le_iSup (fun _ : MulAut.conj (aK i) ≠ 1 => fixSub (MulAut.conj (aK i))) (haone i)))
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    have hdc : (d : Equiv.Perm (Fin 3510)) * fi22FiveLine i = fi22FiveLine i * d :=
      (Subgroup.mem_centralizer_singleton_iff.1
        (fi22FiveC_le_centralizer_line i (fi22FiveD_le_C i (Subgroup.mem_subgroupOf.1 hd))))
    have hdc' : d * xP i = xP i * d := Subtype.ext hdc
    show MulAut.conj (aK i) (g * θ.symm d * g⁻¹) = g * θ.symm d * g⁻¹
    have : θ.symm d * θ.symm (xP i) = θ.symm (xP i) * θ.symm d := by
      rw [← map_mul, ← map_mul, hdc']
    simp only [MulAut.conj_apply, aK]
    calc g * θ.symm (xP i) * g⁻¹ * (g * θ.symm d * g⁻¹) * (g * θ.symm (xP i) * g⁻¹)⁻¹
        = g * (θ.symm (xP i) * θ.symm d * (θ.symm (xP i))⁻¹) * g⁻¹ := by group
      _ = g * (θ.symm d * θ.symm (xP i) * (θ.symm (xP i))⁻¹) * g⁻¹ := by rw [this]
      _ = g * θ.symm d * g⁻¹ := by group
  have hD_P : (⨆ i : Fin 6, fi22FiveD i) ≤ fi22P := iSup_le fun i => fi22FiveD_le_P i
  have hYle : Y0 ≤ fi22P := hY0.trans hD_P
  set Y0P : Subgroup fi22P := Y0.subgroupOf fi22P with hY0P
  have h1 : Y0 ≤ (⨆ i : Fin 6, (fi22FiveD i).subgroupOf fi22P).map fi22P.subtype := by
    rw [Subgroup.map_iSup]
    refine hY0.trans (iSup_le fun i => le_iSup_of_le i ?_)
    rw [Subgroup.map_subgroupOf_eq_of_le (fi22FiveD_le_P i)]
  have h2 : Y0P ≤ ⨆ i : Fin 6, (fi22FiveD i).subgroupOf fi22P := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := h1 (Subgroup.mem_subgroupOf.1 hy)
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz
  refine ⟨(Y0P.map θ.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom, ?_, ⟨?_⟩⟩
  · refine le_trans (Subgroup.map_mono (Subgroup.map_mono h2)) ?_
    rw [Subgroup.map_iSup, Subgroup.map_iSup]
    exact iSup_le hci
  · exact ((MulEquiv.subgroupMap (MulAut.conj g) (Y0P.map θ.symm.toMonoidHom)).symm.trans
      ((MulEquiv.subgroupMap θ.symm Y0P).symm.trans (Subgroup.subgroupOfEquivOfLe hYle)))

theorem input24_2_holds :
    LocalBalance.CaseThreeNs.Input24_2 := by
  intro K _ _ hK A hA hAc
  obtain ⟨e⟩ := hK
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have b : CFSG.Blueprint.NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := b0
  let θ : K ≃* fi22P := (e.trans b.symm).trans fi22PermEquiv
  obtain ⟨Y0, hY0, ⟨eY0⟩⟩ := i242_exists_Y
  obtain ⟨Y, hY, ⟨eY⟩⟩ := i242_reduction Proving.fi22Facts_holds ⟨e⟩ θ Y0 hY0 A hA hAc
  exact ⟨Y, hY, i242_isDFourTwo_of_equiv (eY.trans eY0)⟩

end CFSG.HardMathSupport.Solomon.Coordinator
