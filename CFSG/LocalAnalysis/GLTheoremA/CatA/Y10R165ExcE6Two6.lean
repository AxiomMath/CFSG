module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two4
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open Subgroup
open CFSG.Open
open CFSG.SeitzReduction.E6Pilot
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley
open CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.RankThree.PartTwo.Census.Exceptional
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups


private theorem e6TwoOrtho3_highRoot_check (i : Fin 3) :
    e6TwoOrtho3 i + highRoot .E6 ≠ 0 ∧ e6TwoOrtho3 i - highRoot .E6 ≠ 0 ∧
      CFSG.LieType.Chevalley.RootOps.isRootB .E6 (e6TwoOrtho3 i + highRoot .E6) = false ∧
      CFSG.LieType.Chevalley.RootOps.isRootB .E6 (e6TwoOrtho3 i - highRoot .E6) = false := by
  fin_cases i <;> decide +kernel

private theorem e6TwoOrtho3_mem_a5LeviRoots (i : Fin 3) :
    e6TwoOrtho3 i ∈ a5LeviRoots := by
  have hroot : IsRoot .E6 (e6TwoOrtho3 i) :=
    CFSG.LieType.Chevalley.RootOps.isRootB_iff.mp (e6TwoOrtho3_check.1 i)
  rw [mem_a5LeviRoots]
  refine ⟨hroot, ?_⟩
  fin_cases i <;> rfl

private theorem adjoint_rootGroup_eq_subgroupOf_e6 {K : Type} [Field K] [Finite K]
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ =
      (rootSubgroup .E6 K γ).subgroupOf (adjointGroup .E6 K) := by
  have hmap := CFSG.SeitzReduction.E6Pilot.map_subtype_rootGroup_E6 (K := K) hγ
  change (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ).map
      (adjointGroup .E6 K).subtype = rootSubgroup .E6 K γ at hmap
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf]
    have hmem : (g : ModGL .E6 K) ∈
        (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ).map
          (adjointGroup .E6 K).subtype := ⟨g, hg, rfl⟩
    rwa [hmap] at hmem
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hmem : (g : ModGL .E6 K) ∈
        (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ).map
          (adjointGroup .E6 K).subtype := by
      rw [hmap]
      exact hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hmem
    have hygg : y = g := Subtype.ext hyg
    simpa [hygg] using hy


section CenterAvoidance

variable {A H : Type} [Group A] [Group H]

private theorem inf_center_sup_three_ranges_eq_bot
    (φ0 φ1 φ2 : A →* H)
    (hinj0 : Function.Injective φ0) (hinj1 : Function.Injective φ1)
    (hinj2 : Function.Injective φ2)
    (hcomm01 : ∀ a b : A, φ0 a * φ1 b = φ1 b * φ0 a)
    (hcomm02 : ∀ a b : A, φ0 a * φ2 b = φ2 b * φ0 a)
    (hcomm12 : ∀ a b : A, φ1 a * φ2 b = φ2 b * φ1 a)
    (hZ : Subgroup.center A = ⊥) :
    ((φ0.range ⊔ φ1.range) ⊔ φ2.range) ⊓ Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzP, hzZ⟩ := Subgroup.mem_inf.mp hz
  have hcomm01R : ∀ a ∈ φ0.range, ∀ b ∈ φ1.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hcomm01 a b
  have hcommR01R2 : ∀ a ∈ φ0.range ⊔ φ1.range, ∀ b ∈ φ2.range, a * b = b * a := by
    intro a ha b hb
    obtain ⟨b0, rfl⟩ := hb
    obtain ⟨a0, ha0, a1, ha1, rfl⟩ :=
      CFSG.Quasithin.G8.mem_sup_of_commute hcomm01R ha
    obtain ⟨x0, rfl⟩ := ha0
    obtain ⟨x1, rfl⟩ := ha1
    calc (φ0 x0 * φ1 x1) * φ2 b0 = φ0 x0 * (φ1 x1 * φ2 b0) := by group
      _ = φ0 x0 * (φ2 b0 * φ1 x1) := by rw [hcomm12 x1 b0]
      _ = (φ0 x0 * φ2 b0) * φ1 x1 := by group
      _ = (φ2 b0 * φ0 x0) * φ1 x1 := by rw [hcomm02 x0 b0]
      _ = φ2 b0 * (φ0 x0 * φ1 x1) := by group
  obtain ⟨w, hw, a2, ha2, hzeq⟩ :=
    CFSG.Quasithin.G8.mem_sup_of_commute hcommR01R2 hzP
  obtain ⟨a0, ha0, a1, ha1, hweq⟩ :=
    CFSG.Quasithin.G8.mem_sup_of_commute hcomm01R hw
  obtain ⟨x0, rfl⟩ := ha0
  obtain ⟨x1, rfl⟩ := ha1
  obtain ⟨x2, rfl⟩ := ha2
  have hzdecomp : z = φ0 x0 * φ1 x1 * φ2 x2 := by rw [hzeq, hweq]
  have hz_center : ∀ b : H, Commute z b := fun b =>
    (Subgroup.mem_center_iff.mp hzZ b).symm
  have hx0 : x0 ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hinj0
    have h1 : Commute (φ1 x1) (φ0 b) :=
      (commute_iff_eq (φ1 x1) (φ0 b)).2 (hcomm01 b x1).symm
    have h2 : Commute (φ2 x2) (φ0 b) :=
      (commute_iff_eq (φ2 x2) (φ0 b)).2 (hcomm02 b x2).symm
    have h12 : Commute (φ1 x1 * φ2 x2) (φ0 b) := h1.mul_left h2
    have hz' : Commute (φ0 x0 * (φ1 x1 * φ2 x2)) (φ0 b) := by
      simpa [hzdecomp, mul_assoc] using hz_center (φ0 b)
    have h := hz'.mul_left h12.inv_left
    have hx : Commute (φ0 x0) (φ0 b) := by simpa [mul_assoc] using h
    simpa [map_mul] using hx.eq.symm
  rw [hZ, Subgroup.mem_bot] at hx0
  have hx0eq : φ0 x0 = 1 := by rw [hx0, map_one]
  have hzdecomp1 : z = φ1 x1 * φ2 x2 := by rw [hzdecomp, hx0eq, one_mul]
  have hx1 : x1 ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hinj1
    have h2 : Commute (φ2 x2) (φ1 b) :=
      (commute_iff_eq (φ2 x2) (φ1 b)).2 (hcomm12 b x2).symm
    have hz' : Commute (φ1 x1 * φ2 x2) (φ1 b) := by
      simpa [hzdecomp1] using hz_center (φ1 b)
    have h := hz'.mul_left h2.inv_left
    have hx : Commute (φ1 x1) (φ1 b) := by simpa [mul_assoc] using h
    simpa [map_mul] using hx.eq.symm
  rw [hZ, Subgroup.mem_bot] at hx1
  have hx1eq : φ1 x1 = 1 := by rw [hx1, map_one]
  have hzdecomp2 : z = φ2 x2 := by rw [hzdecomp1, hx1eq, one_mul]
  have hx2 : x2 ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hinj2
    have hz' : Commute (φ2 x2) (φ2 b) := by
      simpa [hzdecomp2] using hz_center (φ2 b)
    simpa [map_mul] using hz'.eq.symm
  rw [hZ, Subgroup.mem_bot] at hx2
  rw [hzdecomp2, hx2, map_one]
  exact Subgroup.mem_bot.mpr rfl

end CenterAvoidance

section FData

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem exists_F_gen {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ Nat.card F - 1 ∨ Nat.card F = 2 ∧ q = 3) :
    ∃ (c : SL(2, F)) (ρ : Fin 3 → SL(2, F) →* ↥(e6Data_valid.minGroup F))
      (G : Subgroup ↥(e6Data_valid.minGroup F)),
      orderOf c = q ∧
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A) ∧
      (∀ i A, ρ i A ∈ Subgroup.center ↥(e6Data_valid.minGroup F) → A = 1) ∧
      (∀ i A, ρ i A ∈ e6Data_valid.rootGroup F (e6TwoOrtho3 i) ⊔
        e6Data_valid.rootGroup F (-e6TwoOrtho3 i)) ∧
      (∀ N : Subgroup ↥(e6Data_valid.minGroup F), (∀ i, ρ i c ∈ N) → G ≤ N) ∧
      IsElemAbelian q G ∧ Nat.card G = q ^ 3 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨c, hc⟩ := exists_orderOf_eq_of_dvd_card_sl2 (F := F) hq hq2 hdiv
  have hcp : c ^ q = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    exact hq.ne_one hc.symm
  have hroot : ∀ i : Fin 3, IsRoot .E6 (e6TwoOrtho3 i) := fun i =>
    CFSG.LieType.Chevalley.RootOps.isRootB_iff.mp (e6TwoOrtho3_check.1 i)
  choose ρ hρinj hρmem hρcen using fun i =>
    CFSG.RankThree.PartTwo.Census.Exceptional.exists_rootSL2' (τ := .E6) e6Data_valid F
      neighbour_cartan_E6 (hroot i)
  have hρcomm : ∀ i j : Fin 3, i ≠ j → ∀ A B : SL(2, F),
      ρ i A * ρ j B = ρ j B * ρ i A := by
    intro i j hij A B
    have hcheck := e6TwoOrtho3_check.2 i j hij
    have h1 : e6TwoOrtho3 i + e6TwoOrtho3 j ≠ 0 := hcheck.1
    have h2 : e6TwoOrtho3 i - e6TwoOrtho3 j ≠ 0 := hcheck.2.1
    have h3 : ¬ IsRoot .E6 (e6TwoOrtho3 i + e6TwoOrtho3 j) := by
      intro h
      have h' : CFSG.LieType.Chevalley.RootOps.isRootB .E6
          (e6TwoOrtho3 i + e6TwoOrtho3 j) = true :=
        CFSG.LieType.Chevalley.RootOps.isRootB_iff.mpr h
      rw [hcheck.2.2.1] at h'
      exact Bool.false_ne_true h'
    have h4 : ¬ IsRoot .E6 (e6TwoOrtho3 i - e6TwoOrtho3 j) := by
      intro h
      have h' : CFSG.LieType.Chevalley.RootOps.isRootB .E6
          (e6TwoOrtho3 i - e6TwoOrtho3 j) = true :=
        CFSG.LieType.Chevalley.RootOps.isRootB_iff.mpr h
      rw [hcheck.2.2.2] at h'
      exact Bool.false_ne_true h'
    have hle := CFSG.RankThree.PartTwo.Census.Exceptional.rankOne_le_centralizer
      (τ := .E6) e6Data_valid F (hroot i) (hroot j) h1 h2 h3 h4
    exact (Subgroup.mem_centralizer_iff.1 (hle (hρmem i A)) (ρ j B) (hρmem j B)).symm
  obtain ⟨G, hGel, hGcard, hGle⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_elemAbelian_pow_of_commuting_sl2 (p := q) (c := c)
      hcp hc1 ρ hρinj (fun i j hij A B => (commute_iff_eq _ _).2 (hρcomm i j hij A B))
  exact ⟨c, ρ, G, hc, hρinj, hρcomm, hρcen, hρmem, hGle, hGel, hGcard⟩

end FData

private theorem e6TwoFData_body :
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (q : ℕ), q.Prime → q ≠ 2 →
    (q ∣ Nat.card F - 1 ∨ Nat.card F = 2 ∧ q = 3) →
    ∃ F0 : Subgroup ↥(e6Data_valid.minGroup F),
      IsElemAbelian q F0 ∧ Nat.card F0 = q ^ 3 ∧
      F0 ⊓ Subgroup.center ↥(e6Data_valid.minGroup F) = ⊥ ∧
      (∀ x ∈ e6Data_valid.rootGroup F (highRoot .E6) ⊔
          e6Data_valid.rootGroup F (-highRoot .E6),
        F0 ≤ Subgroup.centralizer ({x} : Set ↥(e6Data_valid.minGroup F))) ∧
      F0.map (e6Isogeny F) ≤
        Subgroup.normalizer (a5Levi F : Set (adjointGroup .E6 F)) := by
  intro F _ _ _ q hq hq2 hdiv
  obtain ⟨c, ρ, G, hc, hρinj, hρcomm, _hρcen, hρmem, hGle, hGel, hGcard⟩ :=
    exists_F_gen (F := F) hq hq2 hdiv
  haveI : Fact q.Prime := ⟨hq⟩
  have hroot : ∀ i : Fin 3, IsRoot .E6 (e6TwoOrtho3 i) := fun i =>
    CFSG.LieType.Chevalley.RootOps.isRootB_iff.mp (e6TwoOrtho3_check.1 i)
  let L : Subgroup ↥(e6Data_valid.minGroup F) :=
    e6Data_valid.rootGroup F (highRoot .E6) ⊔ e6Data_valid.rootGroup F (-highRoot .E6)
  let P : Subgroup ↥(e6Data_valid.minGroup F) :=
    ((ρ 0).range ⊔ (ρ 1).range) ⊔ (ρ 2).range
  have hGP : G ≤ P := by
    refine hGle P ?_
    intro i
    fin_cases i
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Set.mem_range_self c))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Set.mem_range_self c))
    · exact Subgroup.mem_sup_right (Set.mem_range_self c)
  have hrankCent : ∀ i, (e6Data_valid.rootGroup F (e6TwoOrtho3 i) ⊔
      e6Data_valid.rootGroup F (-e6TwoOrtho3 i)) ≤
      Subgroup.centralizer (L : Set ↥(e6Data_valid.minGroup F)) := by
    intro i
    have hcheck := e6TwoOrtho3_highRoot_check i
    have h1 : e6TwoOrtho3 i + highRoot .E6 ≠ 0 := hcheck.1
    have h2 : e6TwoOrtho3 i - highRoot .E6 ≠ 0 := hcheck.2.1
    have h3 : ¬ IsRoot .E6 (e6TwoOrtho3 i + highRoot .E6) := by
      intro h
      have h' : CFSG.LieType.Chevalley.RootOps.isRootB .E6
          (e6TwoOrtho3 i + highRoot .E6) = true :=
        CFSG.LieType.Chevalley.RootOps.isRootB_iff.mpr h
      rw [hcheck.2.2.1] at h'
      exact Bool.false_ne_true h'
    have h4 : ¬ IsRoot .E6 (e6TwoOrtho3 i - highRoot .E6) := by
      intro h
      have h' : CFSG.LieType.Chevalley.RootOps.isRootB .E6
          (e6TwoOrtho3 i - highRoot .E6) = true :=
        CFSG.LieType.Chevalley.RootOps.isRootB_iff.mpr h
      rw [hcheck.2.2.2] at h'
      exact Bool.false_ne_true h'
    exact CFSG.RankThree.PartTwo.Census.Exceptional.rankOne_le_centralizer
      (τ := .E6) e6Data_valid F (hroot i) (isRoot_highRoot .E6) h1 h2 h3 h4
  have hAcent : ∀ i, (ρ i).range ≤
      Subgroup.centralizer (L : Set ↥(e6Data_valid.minGroup F)) := by
    intro i y hy
    obtain ⟨A, rfl⟩ := hy
    exact hrankCent i (hρmem i A)
  have hPcent : P ≤ Subgroup.centralizer (L : Set ↥(e6Data_valid.minGroup F)) := by
    dsimp [P]
    exact sup_le (sup_le (hAcent 0) (hAcent 1)) (hAcent 2)
  have hGcentL : G ≤ Subgroup.centralizer (L : Set ↥(e6Data_valid.minGroup F)) :=
    hGP.trans hPcent
  have hZSL2 : Subgroup.center (SL(2, F)) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2.center_eq_bot F
  have hPcenter : P ⊓ Subgroup.center ↥(e6Data_valid.minGroup F) = ⊥ := by
    dsimp [P]
    exact inf_center_sup_three_ranges_eq_bot (ρ 0) (ρ 1) (ρ 2)
      (hρinj 0) (hρinj 1) (hρinj 2)
      (hρcomm 0 1 (by decide)) (hρcomm 0 2 (by decide)) (hρcomm 1 2 (by decide))
      hZSL2
  have hGcenter : G ⊓ Subgroup.center ↥(e6Data_valid.minGroup F) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxP : x ∈ P ⊓ Subgroup.center ↥(e6Data_valid.minGroup F) := ⟨hGP hx.1, hx.2⟩
    rw [hPcenter] at hxP
    exact hxP
  have hyA5 : ∀ i, ρ i c ∈ (a5Levi F).comap (e6Isogeny F) := by
    intro i
    rw [Subgroup.mem_comap]
    have hmem : e6TwoOrtho3 i ∈ a5LeviRoots := e6TwoOrtho3_mem_a5LeviRoots i
    have hnegmem : -e6TwoOrtho3 i ∈ a5LeviRoots := by
      rw [mem_a5LeviRoots] at hmem ⊢
      exact ⟨IsRoot.neg hmem.1, by simpa using congrArg Neg.neg hmem.2⟩
    have hmapRank : (e6Data_valid.rootGroup F (e6TwoOrtho3 i) ⊔
        e6Data_valid.rootGroup F (-e6TwoOrtho3 i)).map (e6Isogeny F) ≤ a5Levi F := by
      rw [Subgroup.map_sup,
        CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := F) (hroot i),
        CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := F)
          (IsRoot.neg (hroot i))]
      refine sup_le ?_ ?_
      · rw [adjoint_rootGroup_eq_subgroupOf_e6 (hroot i)]
        simpa [a5Levi] using Subgroup.subgroupOf_mono (adjointGroup .E6 F)
          (rootSubgroup_le_rootSpan (S := a5LeviRoots) hmem)
      · rw [adjoint_rootGroup_eq_subgroupOf_e6 (IsRoot.neg (hroot i))]
        simpa [a5Levi] using Subgroup.subgroupOf_mono (adjointGroup .E6 F)
          (rootSubgroup_le_rootSpan (S := a5LeviRoots) hnegmem)
    exact hmapRank (Subgroup.mem_map_of_mem (e6Isogeny F) (hρmem i c))
  have hGN : G ≤ (a5Levi F).comap (e6Isogeny F) := hGle _ hyA5
  have hGmapLe : G.map (e6Isogeny F) ≤ a5Levi F := by
    rw [Subgroup.map_le_iff_le_comap]
    exact hGN
  have hGnorm : G.map (e6Isogeny F) ≤
      Subgroup.normalizer (a5Levi F : Set (adjointGroup .E6 F)) :=
    hGmapLe.trans (Subgroup.le_normalizer)
  refine ⟨G, hGel, hGcard, hGcenter, ?_, hGnorm⟩
  intro x hx
  exact hGcentL.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx))

theorem e6TwoFData_holds : E6TwoFData := e6TwoFData_body

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
