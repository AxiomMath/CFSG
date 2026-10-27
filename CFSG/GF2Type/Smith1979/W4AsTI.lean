module

public import CFSG.LargeExtraspecial.S4TwoMain
public import CFSG.GH74.KGroups.L28
public import CFSG.GH74.KGH
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open
  CFSG.ComponentClassification.GSThmB.Cat81A8

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem map_subtype_ne_bot {K : Subgroup S.Mbar} (hK : K ≠ ⊥) : K.map S.Mbar.subtype ≠ ⊥ :=
  fun h => hK ((Subgroup.map_eq_bot_iff_of_injective K S.Mbar.subtype_injective).mp h)

theorem map_subtype_conj_mem {K : Subgroup S.Mbar} (hK : K.Normal) (m : S.M) {z : S.O}
    (hz : z ∈ K.map S.Mbar.subtype) : S.ρ m * z * (S.ρ m)⁻¹ ∈ K.map S.Mbar.subtype := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
  let y : S.Mbar := ⟨S.ρ m, ⟨m, rfl⟩⟩
  exact Subgroup.mem_map.mpr ⟨y * x * y⁻¹, hK.conj_mem x hx y, rfl⟩

theorem centralizes_of_conjNormal_eq_one {x : S.Mbar}
    (hx : (MulAut.conjNormal : S.Mbar →* MulAut (M0 S g)) x = 1) {l : S.O}
    (hl : l ∈ S.Lbar g) : (x : S.O) * l = l * (x : S.O) := by
  have hlM : l ∈ S.Mbar := S.Lbar_le_Mbar g hl
  have hlL : (⟨l, hlM⟩ : S.Mbar) ∈ M0 S g := LM_le_M0 (Subgroup.mem_subgroupOf.mpr hl)
  have h1 : (MulAut.conjNormal : S.Mbar →* MulAut (M0 S g)) x ⟨⟨l, hlM⟩, hlL⟩ =
      ⟨⟨l, hlM⟩, hlL⟩ :=
    congrArg (fun φ : MulAut (M0 S g) => φ ⟨⟨l, hlM⟩, hlL⟩) hx
  have h2 : x * (⟨l, hlM⟩ : S.Mbar) * x⁻¹ = ⟨l, hlM⟩ := by
    have h3 := MulAut.conjNormal_apply (H := M0 S g) x ⟨⟨l, hlM⟩, hlL⟩
    rw [h1] at h3
    exact h3.symm
  have h4 : (x : S.O) * l * (x : S.O)⁻¹ = l := congrArg Subtype.val h2
  exact mul_inv_eq_iff_eq_mul.mp h4

noncomputable abbrev conjKer (S₀ : Setting G) (g₀ : G) : Subgroup S₀.Mbar :=
  (MulAut.conjNormal : S₀.Mbar →* MulAut (M0 S₀ g₀)).ker

theorem conjKer_normal (S₀ : Setting G) (g₀ : G) : (conjKer S₀ g₀).Normal :=
  MonoidHom.normal_ker _

theorem injective_conjNormal_M0 (H : Hyp4 S g) (hirr : ¬ S.IsReducible) :
    Function.Injective (MulAut.conjNormal : S.Mbar →* MulAut (M0 S g)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have hZ1 : (conjKer S g).map S.Mbar.subtype ≠ ⊥ := map_subtype_ne_bot hne
  have hZn : ∀ m : S.M, ∀ z ∈ (conjKer S g).map S.Mbar.subtype,
      S.ρ m * z * (S.ρ m)⁻¹ ∈ (conjKer S g).map S.Mbar.subtype :=
    fun m z hz => map_subtype_conj_mem (conjKer_normal S g) m hz
  have hZL : ∀ z ∈ (conjKer S g).map S.Mbar.subtype, ∀ l ∈ S.Lbar g, z * l = l * z := by
    intro z hz l hl
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hx1 : (MulAut.conjNormal : S.Mbar →* MulAut (M0 S g)) x = 1 := MonoidHom.mem_ker.mp hx
    exact centralizes_of_conjNormal_eq_one hx1 hl
  exact hirr (CFSG.LargeExtraspecial.S4.isReducible_of_le_centralizer H hZ1 hZn hZL)

theorem card_Mbar_dvd_1512 (H : Hyp4 S g)
    (hirr : ¬ S.IsReducible) (h : StatedClassicalModel (M0 S g) .PSL 2 2 3) :
    Nat.card S.Mbar ∣ 1512 := by
  have hL := CFSG.GH74.lieModel_of_statedClassicalModel (by decide) h
  have hdvd := Subgroup.card_dvd_of_injective (MulAut.conjNormal : S.Mbar →* MulAut (M0 S g))
    (injective_conjNormal_M0 H hirr)
  rwa [CFSG.GH74.KGroups.L28.card_mulAut hL] at hdvd

theorem gen4_Mbar_of_L28 (H : Hyp4 S g)
    (hirr : ¬ S.IsReducible) (h : StatedClassicalModel (M0 S g) .PSL 2 2 3) :
    CFSG.GH74.SectionalTwoRankLE S.Mbar 4 := by
  haveI : Finite S.Mbar := Finite.of_surjective _ S.ρ.rangeRestrict_surjective
  intro P hP
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
  have hd : Nat.card P ∣ 1512 :=
    (Subgroup.card_subgroup_dvd_card P).trans (card_Mbar_dvd_1512 H hirr h)
  rw [hm] at hd
  have h8 : 2 ^ m ∣ 8 :=
    (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 189)).dvd_of_dvd_mul_right hd
  have hle : Nat.card P ≤ 8 := by
    rw [hm]
    exact Nat.le_of_dvd (by norm_num) h8
  obtain ⟨t, -, ht, hcard⟩ :=
    CFSG.CGT.PushingUpLit.SolK.exists_gen_of_start P ∅ (by simp) 0 (by simp)
  refine ⟨t, ?_, ht⟩
  by_contra hc
  have h16 : 2 ^ 4 ≤ 2 ^ (t.card + 0) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h16' : (2 : ℕ) ^ 4 = 16 := by norm_num
  omega

theorem card_perm9 : Nat.card (Equiv.Perm (Fin 9)) = 362880 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem gen4_perm9 :
    CFSG.GH74.SectionalTwoRankLE (Equiv.Perm (Fin 9)) 4 := by
  classical
  let f : Equiv.Perm (Fin 8) →* Equiv.Perm (Fin 9) :=
    Equiv.Perm.extendDomainHom (finSuccAboveEquiv (8 : Fin 9))
  have hf : Function.Injective f := Equiv.Perm.extendDomainHom_injective _
  have hT8 : IsPGroup 2 T8 := IsPGroup.of_card (n := 7) (by rw [card_T8]; norm_num)
  have hcard : Nat.card (Subgroup.map f T8) = 128 := by
    rw [Subgroup.card_map_of_injective hf, card_T8]
  have hidx : ¬ 2 ∣ (Subgroup.map f T8).index := by
    have h := (Subgroup.map f T8).card_mul_index
    rw [hcard, card_perm9] at h
    omega
  have hT9 : CFSG.GH74.SectionalTwoRankLE
      (((IsPGroup.map hT8 f).toSylow hidx : Sylow 2 (Equiv.Perm (Fin 9))) :
        Subgroup (Equiv.Perm (Fin 9))) 4 :=
    CFSG.GH74.SectionalTwoRankLE.of_mulEquiv (T8.equivMapOfInjective f hf) gen4_T8
  exact CFSG.CGT.PushingUpLit.SolK.SectionalTwoRankLE.of_sylow _ hT9

noncomputable def mulAutEquivPerm9 {K₀ : Type*} [Group K₀]
    (e : K₀ ≃* alternatingGroup (Fin 9)) : MulAut K₀ ≃* Equiv.Perm (Fin 9) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num)
      (by norm_num))).symm

theorem gen4_Mbar_of_A9 (H : Hyp4 S g) (hirr : ¬ S.IsReducible)
    (e : M0 S g ≃* alternatingGroup (Fin 9)) : CFSG.GH74.SectionalTwoRankLE S.Mbar 4 :=
  CFSG.GH74.SectionalTwoRankLE.of_injective (MulAut.conjNormal : S.Mbar →* MulAut (M0 S g))
    (injective_conjNormal_M0 H hirr)
    (CFSG.GH74.SectionalTwoRankLE.of_mulEquiv (mulAutEquivPerm9 e).symm gen4_perm9)

theorem gen4_of_ti
    (hF2 : Form2StrongStmt) (hBen : BenderConjCountInput) (hWT : WeaklyClosedTITransitive.{0})
    (H : Hyp4 S g) (C : Cons311 S g) (hNo : NoA2 S g)
    (hTI : ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨ S.Lbar ((h : G) * g) = S.Lbar g)
    (hirr : ¬ S.IsReducible) : CFSG.GH74.SectionalTwoRankLE S.Mbar 4 := by
  obtain ⟨-, hM0⟩ := CFSG.LargeExtraspecial.S4.lemma_4_2 hF2 hBen hWT H C hNo hTI hirr
  rcases hM0 with h8 | hN
  · exact gen4_Mbar_of_L28 H hirr h8
  · obtain ⟨e⟩ := hN
    exact gen4_Mbar_of_A9 H hirr e

end CFSG.GF2Type.Smith1979.W4As
