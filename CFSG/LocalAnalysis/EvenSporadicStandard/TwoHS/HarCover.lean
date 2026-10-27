module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HSData

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic

structure CoverMaps (E : Type) [Group E] where
  g : Fin 6 → E
  ρ : E →* Equiv.Perm (Fin 11200)
  π : E →* ↥hsP
  ρ_g : ∀ i, ρ (g i) = harYPerm i
  π_g : ∀ i, ((π (g i) : ↥hsP) : Equiv.Perm (Fin 3850)) = harXPerm i
  π_surj : Function.Surjective π
  π_ker : ∀ x, π x = 1 ↔ x ∈ center E

section Maps

variable {E : Type} [Group E] (M : CoverMaps E)

@[expose] def CoverMaps.gE : List E := (List.finRange 6).map M.g

def CoverMaps.uE : List E := harUW.map (wordVal M.gE)

end Maps

section Reps

variable {E : Type} [Group E] (M : CoverMaps E)

theorem harLiftOK_true : harLiftOK = true := Certificates.certificate26130.2.2

theorem harYs_perm : ∀ g ∈ harYs, permOK 11200 g = true := by
  have h := harModelOK_true
  simp only [harModelOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨hperm, -⟩, -⟩ := h
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact (hperm i).1

theorem harXs_perm : ∀ g ∈ harXs, permOK 3850 g = true := by
  have h := harPOK_true
  simp only [harPOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨⟨-, hB⟩, -⟩, -⟩, -⟩, -⟩ := h
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact (hB i).1

theorem harU_perm : ∀ g ∈ harU, permOK 11200 g = true := by
  have h := harLiftOK_true
  simp only [harLiftOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.1.1.1

theorem harUX_perm : ∀ g ∈ harUX, permOK 3850 g = true := by
  have h := harLiftOK_true
  simp only [harLiftOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.1.1.2

theorem tp_harY (i : Fin 6) : tp 11200 (harY i) = harYPerm i := rfl

theorem tp_harX (i : Fin 6) : tp 3850 (harX i) = harXPerm i :=
  rep_unique (rep_tp (harXs_perm _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)))
    (rep_harX i).1

theorem CoverMaps.rho_gE : M.gE.map M.ρ = harYs.map (tp 11200) := by
  simp [CoverMaps.gE, harYs, List.map_map, Function.comp_def, M.ρ_g, tp_harY]

theorem CoverMaps.pi_gE : M.gE.map (hsP.subtype.comp M.π) = harXs.map (tp 3850) := by
  simp [CoverMaps.gE, harXs, List.map_map, Function.comp_def, M.π_g, tp_harX]

theorem harUW_letters : ∀ w ∈ harUW, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6 := by decide

theorem harU_length : harU.length = 3 := rfl

theorem harYs_length : harYs.length = 6 := rfl

theorem harXs_length : harXs.length = 6 := rfl

set_option maxRecDepth 100000 in
theorem CoverMaps.uE_rho : M.uE.map M.ρ = harU.map (tp 11200) := by
  unfold CoverMaps.uE harU
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply]
  have hr := rep_wordTbl'' (n := 11200) (by norm_num) harYs_perm w (by
    rw [harYs_length]
    exact harUW_letters w hw)
  have hperm : permOK 11200 (wordTbl 11200 harYs w) = true :=
    harU_perm _ (List.mem_map.2 ⟨w, hw, rfl⟩)
  rw [map_wordVal, M.rho_gE]
  exact (rep_unique (rep_tp hperm) hr).symm

set_option maxRecDepth 100000 in
theorem CoverMaps.uE_pi : M.uE.map (hsP.subtype.comp M.π) = harUX.map (tp 3850) := by
  unfold CoverMaps.uE harUX
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro w hw
  simp only [Function.comp_apply]
  have hr := rep_wordTbl'' (n := 3850) (by norm_num) harXs_perm w (by
    rw [harXs_length]
    exact harUW_letters w hw)
  have hperm : permOK 3850 (wordTbl 3850 harXs w) = true :=
    harUX_perm _ (List.mem_map.2 ⟨w, hw, rfl⟩)
  rw [map_wordVal, M.pi_gE]
  exact (rep_unique (rep_tp hperm) hr).symm

theorem CoverMaps.rep_tU (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) :
    Rep 11200 (tU w) (M.ρ (wordVal M.uE w)) := by
  have hr := rep_wordTbl'' (n := 11200) (by norm_num) harU_perm w (by
    rw [harU_length]
    exact hw)
  rw [map_wordVal, M.uE_rho]
  exact hr

theorem CoverMaps.rep_tUX (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 3) :
    Rep 3850 (tUX w) ((M.π (wordVal M.uE w) : ↥hsP) : Equiv.Perm (Fin 3850)) := by
  have hr := rep_wordTbl'' (n := 3850) (by norm_num) harUX_perm w (by
    have : harUX.length = 3 := rfl
    rw [this]
    exact hw)
  have h := map_wordVal (hsP.subtype.comp M.π) M.uE w
  rw [M.uE_pi] at h
  rw [← h] at hr
  exact hr

def CoverMaps.tE : E := wordVal M.uE [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]

def CoverMaps.z1E : E := wordVal M.uE [3, 3, 3, 3]

def CoverMaps.y2E : E := wordVal M.uE [1, 2, 1, 2, 3]

theorem CoverMaps.rep_tE : Rep 11200 harC0 (M.ρ M.tE) :=
  M.rep_tU _ (by decide)

theorem CoverMaps.rep_z1E : Rep 11200 harZ1 (M.ρ M.z1E) :=
  M.rep_tU _ (by decide)

theorem CoverMaps.rep_y2E : Rep 11200 (tU [1, 2, 1, 2, 3]) (M.ρ M.y2E) :=
  M.rep_tU _ (by decide)

theorem CoverMaps.rho_tE_ne : M.ρ M.tE ≠ 1 := by
  intro h
  have hl := harLiftOK_true
  simp only [harLiftOK, Bool.and_eq_true, Bool.not_eq_true'] at hl
  have hne := hl.1.1.1.1.2
  have := (tblEq_iff_eq M.rep_tE (Rep.idT (n := 11200) (by norm_num))).2 (by rw [h])
  rw [this] at hne
  exact absurd hne (by decide)

theorem CoverMaps.rep_piTE : Rep 3850 (tUX [1, 2, 1, 2, 3, 1, 2, 1, 2, 3])
    ((M.π M.tE : ↥hsP) : Equiv.Perm (Fin 3850)) :=
  M.rep_tUX _ (by decide)

theorem CoverMaps.pi_tE : M.π M.tE = 1 := by
  have hl := harLiftOK_true
  simp only [harLiftOK, Bool.and_eq_true] at hl
  have h1 := hl.2
  have := (tblEq_idT_iff (n := 3850) (by norm_num) M.rep_piTE).1 h1
  exact Subtype.ext this

theorem CoverMaps.tE_mem_center : M.tE ∈ center E := (M.π_ker _).1 M.pi_tE

theorem CoverMaps.rho_injective [IsSimpleGroup ↥hsP] (hperf : Group.IsPerfect E)
    (hZ : Nat.card (center E) = 2) : Function.Injective M.ρ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have htne : M.tE ≠ 1 := fun h => M.rho_tE_ne (by rw [h, map_one])
  by_cases hxz : x ∈ center E
  · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(center E))).1 hZ
    have h1 : (⟨x, hxz⟩ : ↥(center E)) = y := hy _ (fun h => hx1 (congrArg Subtype.val h))
    have h2 : (⟨M.tE, M.tE_mem_center⟩ : ↥(center E)) = y :=
      hy _ (fun h => htne (congrArg Subtype.val h))
    have : x = M.tE := congrArg Subtype.val (h1.trans h2.symm)
    exact M.rho_tE_ne (by rw [← this, hx])
  · have hQ : ((M.ρ.ker).map M.π).Normal := Subgroup.Normal.map inferInstance M.π M.π_surj
    have hQne : (M.ρ.ker).map M.π ≠ ⊥ := by
      intro h
      have : M.π x ∈ (M.ρ.ker).map M.π := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact hxz ((M.π_ker x).1 this)
    have hQtop : (M.ρ.ker).map M.π = ⊤ := by
      have := hQ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M.ρ.ker).map M.π) with h | h
      · exact absurd h hQne
      · exact h
    have hfac : ∀ e : E, ∃ c ∈ center E, M.ρ e = M.ρ c := by
      intro e
      have : M.π e ∈ (M.ρ.ker).map M.π := by rw [hQtop]; trivial
      obtain ⟨n, hn, hne⟩ := this
      refine ⟨n⁻¹ * e, (M.π_ker _).1 ?_, ?_⟩
      · rw [map_mul, map_inv, hne, inv_mul_cancel]
      · have hn' : M.ρ n = 1 := hn
        rw [map_mul, map_inv, hn', inv_one, one_mul]
    have hcomm : commutator E ≤ M.ρ.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨c, hc, hac⟩ := hfac a
      obtain ⟨d, hd, hbd⟩ := hfac b
      rw [MonoidHom.mem_ker, map_commutatorElement, hac, hbd, ← map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 hc) d).symm, map_one]
    rw [Group.isPerfect_def.1 hperf] at hcomm
    have : M.tE ∈ M.ρ.ker := hcomm trivial
    exact M.rho_tE_ne this

end Reps


structure CoverModel (E : Type) [Group E] extends CoverMaps E where
  ρ_inj : Function.Injective toCoverMaps.ρ

section Existence


theorem card_eq_of_double_cover {E : Type} [Group E] (hZ : Nat.card (center E) = 2)
    (hq : IsSporadic (E ⧸ center E) .HS) : Nat.card E = 88704000 := by
  obtain ⟨e₀⟩ := hq
  have e : E ⧸ center E ≃* NativeSporadic.HS := e₀
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center E)
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS, hZ] at h1
  omega

theorem isSimpleGroup_hsP : IsSimpleGroup ↥hsP :=
  isSimpleGroup_of_mulEquiv_perm CFSG.Sporadic.HS.fam_hs_simplicity.2.2 hsPermEquiv

theorem exists_coverMaps {E : Type} [Group E] [Finite E] (hperf : Group.IsPerfect E)
    (hZ : Nat.card (center E) = 2) (hq : IsSporadic (E ⧸ center E) .HS) :
    Nonempty (CoverMaps E) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_cover_of_doubleCover_hs hperf hZ hq
  let π : E →* ↥hsP := harPiHom.comp φ.symm.toMonoidHom
  have hsurj : Function.Surjective π := harPiHom_surjective.comp φ.symm.surjective
  have hcard := card_eq_of_double_cover hZ hq
  have hker2 : Nat.card π.ker = 2 := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, hcard, card_hsP] at h1
    omega
  have hkc : π.ker ≤ center E := by
    obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : ↥π.ker)).1 hker2
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    by_cases hz1 : z = 1
    · rw [hz1]; simp
    · have h1 : (⟨z, hz⟩ : ↥π.ker) = x := hx _ (fun h => hz1 (congrArg Subtype.val h))
      have hgz : g * z * g⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv]
        have : π z = 1 := hz
        rw [this]; simp
      have hgz1 : g * z * g⁻¹ ≠ 1 := by
        intro h
        apply hz1
        have h' : z = g⁻¹ * (g * z * g⁻¹) * g := by group
        rw [h', h]
        simp
      have h2 : (⟨g * z * g⁻¹, hgz⟩ : ↥π.ker) = x := hx _ (fun h => hgz1 (congrArg Subtype.val h))
      have h3 : g * z * g⁻¹ = z := congrArg Subtype.val (h2.trans h1.symm)
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h3]
  have hkeq : π.ker = center E :=
    Subgroup.eq_of_le_of_card_ge hkc (by rw [hker2, hZ])
  refine ⟨{ g := fun i => φ (PresentedGroup.of i), ρ := harRhoHom.comp φ.symm.toMonoidHom,
            π := π, ρ_g := fun i => ?_, π_g := fun i => ?_, π_surj := hsurj,
            π_ker := fun x => ?_ }⟩
  · simp [harRhoHom_of]
  · simp [π, harPiHom_of]
  · rw [← hkeq, MonoidHom.mem_ker]

theorem exists_coverModel {E : Type} [Group E] [Finite E] (hperf : Group.IsPerfect E)
    (hZ : Nat.card (center E) = 2) (hq : IsSporadic (E ⧸ center E) .HS) :
    Nonempty (CoverModel E) := by
  obtain ⟨M⟩ := exists_coverMaps hperf hZ hq
  have := isSimpleGroup_hsP
  exact ⟨⟨M, M.rho_injective hperf hZ⟩⟩

end Existence

end CFSG.EvenSporadicStandard.TwoHS
