module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.GenerationSingular
public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.GenerationLayer
public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.GenerationBranch
import CFSG.GroupTheory.NatL2SectionCentralizer
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstarNormalizer
import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet O2Trivial)
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem commute_of_mem_normal_odd_g45id {Γ : Type*} [Group Γ] [Finite Γ]
    {H A : Subgroup Γ} (hAH : A ≤ H) (hAnorm : (A.subgroupOf H).Normal)
    (hodd : Odd (Nat.card A))
    (hcenter : CFSG.pPrimeCore 2 ↥H = Subgroup.center ↥H) :
    ∀ a ∈ A, ∀ h ∈ H, a * h = h * a := by
  have hcop : Nat.Coprime 2 (Nat.card (A.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  have hAle : A.subgroupOf H ≤ CFSG.pPrimeCore 2 ↥H :=
    CFSG.le_pPrimeCore_of_normal_coprime hAnorm hcop
  intro a ha h hh
  have haH : a ∈ H := hAH ha
  have hmem : (⟨a, haH⟩ : ↥H) ∈ Subgroup.center ↥H := by
    rw [← hcenter]
    exact hAle ha
  have h1 := Subgroup.mem_center_iff.mp hmem ⟨h, hh⟩
  exact (congrArg Subtype.val h1).symm

private theorem commute_of_mem_gomiGstar1_g45id (h : GomiThm45Counterexample c G S)
    (h33 : GomiFact33) {M : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hP1 : (gomiPstar1Set (autOn M (gomiV M))).Nonempty)
    (hO_le_S : autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ≤
      gomiGstar1 (autOn M (gomiV M))) :
    ∀ b ∈ gomiGstar1 (autOn M (gomiV M)),
      ∀ x ∈ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M),
        b * x = x * b := by
  set W := gomiV M
  set Y := autOn M W
  set O := autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) W
  set S₁ := gomiGstar1 Y
  have hW : CFSG.Open.IsElemAbelian 2 W := (gomiV_moduleSetting M).1
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hW.2 (w : Ω) w.2)
  have hO_le_Y : O ≤ Y := AutOn.autOn_mono inf_le_left
  have hO_normal_Y : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_Y).mpr
      (le_normalizer_autOn_inf_centralizer hMG (gomiV_moduleSetting G).2)
  have hS_le_N : S₁ ≤ Subgroup.normalizer (O : Set (MulAut W)) :=
    (gomiGstar1_le Y).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_Y).mp hO_normal_Y)
  have hO_normal_S : (O.subgroupOf S₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_S).mpr hS_le_N
  have hodd : Odd (Nat.card O) := odd_card_autOn_inf_centralizer h hMG hGM
  have hO2 : O2Trivial S₁ :=
    o2Trivial_of_normal (o2Trivial_autOn_gomiV h hMG hGM) (gomiGstar1_le Y)
      (gomiGstar1_subgroupOf_normal Y)
  have hcenter : CFSG.pPrimeCore 2 ↥S₁ = Subgroup.center ↥S₁ :=
    (h33 W hW2 Y hP1 hO2).2.2
  have hcomm := commute_of_mem_normal_odd_g45id hO_le_S hO_normal_S hodd hcenter
  intro b hb x hx
  exact (hcomm x hx b hb).symm

private theorem commute_of_mem_gomiPstar0_g45id (h : GomiThm45Counterexample c G S)
    (h31 : GomiFact31) {M : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hO_le_S : autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ≤
      gomiGstar0 (autOn M (gomiV M))) :
    ∀ B ∈ gomiPstar0Set (autOn M (gomiV M)), ∀ b ∈ B,
      ∀ x ∈ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M),
        b * x = x * b := by
  set W := gomiV M
  set Y := autOn M W
  set O := autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) W
  set S₀ := gomiGstar0 Y
  have hO_le_Y : O ≤ Y := AutOn.autOn_mono inf_le_left
  have hO_normal_Y : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_Y).mpr
      (le_normalizer_autOn_inf_centralizer hMG (gomiV_moduleSetting G).2)
  have hY_le_N : Y ≤ Subgroup.normalizer (O : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_Y).mp hO_normal_Y
  have hS_le_N : S₀ ≤ Subgroup.normalizer (O : Set (MulAut W)) :=
    (gomiGstar0_le Y).trans hY_le_N
  intro B hB b hb x hx
  set N := gomiOrbitSpan Y B with hN
  have hNmem : N ∈ gomiNSet Y := ⟨B, hB, hN⟩
  have hB_le_N : B ≤ N := by
    rw [hN, gomiOrbitSpan]
    refine le_iSup₂_of_le (f := fun g (_ : g ∈ gomiGstar0 Y) =>
      B.map (MulAut.conj g).toMonoidHom) (1 : MulAut W) (one_mem _) ?_
    change B ≤ Subgroup.map (MonoidHom.id (MulAut W)) B
    rw [Subgroup.map_id]
  have hNnorm : S₀ ≤ Subgroup.normalizer (N : Set (MulAut W)) := by
    have := le_normalizer_iSup_map_conj S₀ B
    simpa [gomiOrbitSpan, hN] using this
  have hxN : x ∈ Subgroup.normalizer (N : Set (MulAut W)) := hNnorm (hO_le_S hx)
  have hcO : b * x * b⁻¹ * x⁻¹ ∈ O := by
    have hbY : b ∈ Y := hB.1.1.1 hb
    have hconj : b * x * b⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hY_le_N hbY) x).1 hx
    exact O.mul_mem hconj (O.inv_mem hx)
  have hcN : b * x * b⁻¹ * x⁻¹ ∈ N := by
    have h1 : x * b * x⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hxN b).1 (hB_le_N hb)
    have h2 : x * b * x⁻¹ * b⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem (hB_le_N hb))
    simpa [mul_assoc] using N.inv_mem h2
  have hE := inf_autOn_inf_centralizer_eq_bot h h31 hMG hGM hNmem
  have hc_bot : b * x * b⁻¹ * x⁻¹ ∈ (⊥ : Subgroup (MulAut W)) := by
    rw [← hE]
    exact Subgroup.mem_inf.mpr ⟨hcN, hcO⟩
  have hc1 : b * x * b⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hc_bot
  calc b * x = (b * x * b⁻¹ * x⁻¹) * (x * b) := by group
    _ = x * b := by rw [hc1, one_mul]

private theorem false_of_commute_g45id (h : GomiThm45Counterexample c G S)
    {M X : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hJM : thompsonJ S ≤ M) (hX : IsGomiSingularSubgroup M (S ⊓ M) X)
    {𝒮 : Set (Subgroup (MulAut ↥(gomiV M)))}
    (h𝒮 : 𝒮 ⊆ PstarSet (autOn M (gomiV M))) (hne : 𝒮.Nonempty)
    (hN : autOn G (gomiV M) ≤
      Subgroup.normalizer
        ((sSup 𝒮 : Subgroup (MulAut ↥(gomiV M))) : Set (MulAut ↥(gomiV M))))
    (hcomm : autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ≤
      (sSup 𝒮 : Subgroup (MulAut ↥(gomiV M))) →
      ∀ B ∈ 𝒮, ∀ b ∈ B,
        ∀ x ∈ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M),
          b * x = x * b) : False := by
  have hW : CFSG.Open.IsElemAbelian 2 (gomiV M) := (gomiV_moduleSetting M).1
  have hMW : M ≤ Subgroup.normalizer (gomiV M : Set Ω) := (gomiV_moduleSetting M).2
  have hXle : X ≤ Subgroup.centralizer (gomiV G : Set Ω) :=
    le_centralizer_gomiV_of_isGomiSingularSubgroup h hMG hGM hJM hX
  have hXsub : X ≤ M ⊓ Subgroup.centralizer (gomiV G : Set Ω) := le_inf hX.le hXle
  have hXbar_le_O : autOn X (gomiV M) ≤
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :=
    AutOn.autOn_mono hXsub
  have h2 : 2 ∣ Nat.card (sSup 𝒮 : Subgroup (MulAut ↥(gomiV M))) := by
    obtain ⟨B, hB⟩ := hne
    have hBeven : Even (Nat.card B) :=
      E3.even_card_of_isPGroup (X := B) (A := B) le_rfl
        (E3.isPGroup_of_isElemAbelian2 (h𝒮 hB).1.2.2.1) (h𝒮 hB).1.2.1
    exact (even_iff_two_dvd.mp hBeven).trans
      (Subgroup.card_dvd_of_le
        (le_sSup hB : B ≤ (sSup 𝒮 : Subgroup (MulAut ↥(gomiV M)))))
  have hO_le_S : autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ≤
      (sSup 𝒮 : Subgroup (MulAut ↥(gomiV M))) :=
    autOn_inf_centralizer_le h hMG hGM (sSup_le fun B hB => (h𝒮 hB).1.1) hN h2
  obtain ⟨C, n, hn, hnat⟩ := hX.natural
  refine (not_autOn_le_sSup_of_isNatL2Section (M := M) (X := X) (W := gomiV M) (C := C)
    hW hMW hX.le hX.twoResidual_eq hnat ?_ ?_ ?_) (hXbar_le_O.trans hO_le_S)
  · intro B hB
    exact (h𝒮 hB).1.1
  · intro B hB b hb
    exact (h𝒮 hB).1.2.2.1.2 b hb
  · intro B hB b hb x hx
    exact hcomm hO_le_S B hB b hb x (hXbar_le_O hx)

theorem false_of_gomiPstar1Set_nonempty (h : GomiThm45Counterexample c G S) (h33 : GomiFact33)
    {M X : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hJM : thompsonJ S ≤ M) (hX : IsGomiSingularSubgroup M (S ⊓ M) X)
    (hP1 : (gomiPstar1Set (autOn M (gomiV M))).Nonempty) : False := by
  refine false_of_commute_g45id h hMG hGM hJM hX
    (𝒮 := gomiPstar1Set (autOn M (gomiV M))) (fun B hB => hB.1) hP1 ?_ ?_
  · exact (AutOn.autOn_le_normalizer_autOn hGM).trans
      (normalizer_le_normalizer_gomiGstar1 (autOn M (gomiV M)))
  · intro hO_le_S B hB b hb
    exact commute_of_mem_gomiGstar1_g45id h h33 hMG hGM hP1 hO_le_S b (le_sSup hB hb)

theorem false_of_gomiPstar0Set_nonempty (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    {M X : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hJM : thompsonJ S ≤ M) (hX : IsGomiSingularSubgroup M (S ⊓ M) X)
    (hP0 : (gomiPstar0Set (autOn M (gomiV M))).Nonempty) : False := by
  refine false_of_commute_g45id h hMG hGM hJM hX
    (𝒮 := gomiPstar0Set (autOn M (gomiV M))) (fun B hB => hB.1) hP0 ?_ ?_
  · exact (AutOn.autOn_le_normalizer_autOn hGM).trans
      (normalizer_le_normalizer_gomiGstar0 (autOn M (gomiV M)))
  · intro hO_le_S B hB b hb
    exact commute_of_mem_gomiPstar0_g45id h h31 hMG hGM hO_le_S B hB b hb

theorem false_of_isGomiSingularSubgroup (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h33 : GomiFact33) {M X : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) (hJM : thompsonJ S ≤ M)
    (hX : IsGomiSingularSubgroup M (S ⊓ M) X) : False := by
  have hP : (Pset (autOn M (gomiV M))).Nonempty :=
    pset_autOn_gomiV_nonempty h hMG hGM hJM
  obtain ⟨A, hA⟩ := pstarSet_nonempty hP
  by_cases hA0 : A ∈ gomiPstar0Set (autOn M (gomiV M))
  · exact false_of_gomiPstar0Set_nonempty h h31 hMG hGM hJM hX ⟨A, hA0⟩
  · exact false_of_gomiPstar1Set_nonempty h h33 hMG hGM hJM hX ⟨A, hA, hA0⟩

end CFSG.GroupTheory.GomiThm45Counterexample
