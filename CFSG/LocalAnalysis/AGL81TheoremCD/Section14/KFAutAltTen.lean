module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTenGood
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
open Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {N : Subgroup X}

private theorem fixes_block_of_cube_one {B : Finset (Fin 10)} (hB : B.card = 5)
    {y : Perm (Fin 10)} (hy3 : y ^ 3 = 1)
    (h : (∀ i ∈ B, y i ∈ B) ∨ (∀ i ∈ B, y i ∉ B)) :
    ∀ x, y x ∈ B ↔ x ∈ B := by
  classical
  rcases h with h | h
  · have himg : B.image y = B := Finset.eq_of_subset_of_card_le
      (fun z hz => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        exact h i hi)
      (by rw [Finset.card_image_of_injective _ y.injective])
    intro x
    constructor
    · intro hx
      have hximg : y x ∈ B.image y := by rw [himg]; exact hx
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hximg
      exact y.injective hzy ▸ hz
    · exact h x
  · exfalso
    have hBc : Bᶜ.card = 5 := by
      rw [Finset.card_compl, Fintype.card_fin, hB]
    have hmap : ∀ i ∈ B, y i ∈ Bᶜ := fun i hi => Finset.mem_compl.mpr (h i hi)
    have himg : B.image y = Bᶜ := Finset.eq_of_subset_of_card_le
      (fun z hz => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        exact hmap i hi)
      (by rw [Finset.card_image_of_injective _ y.injective, hBc, hB])
    have hmap' : ∀ i ∈ Bᶜ, y i ∈ B := by
      intro i hi
      by_contra hc
      have hiy : y i ∈ Bᶜ := Finset.mem_compl.mpr hc
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (himg.symm ▸ hiy)
      have hji' : j = i := y.injective hji
      exact (Finset.mem_compl.mp hi) (hji' ▸ hj)
    have h3 : ∀ i ∈ B, (y ^ 3) i ∈ Bᶜ := by
      intro i hi
      have h1 : y i ∈ Bᶜ := hmap i hi
      have h2 : y (y i) ∈ B := hmap' (y i) h1
      have h3 : y (y (y i)) ∈ Bᶜ := hmap (y (y i)) h2
      simpa [pow_succ, pow_two] using h3
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by rw [hB]; norm_num)
    have hx : (y ^ 3) i₀ ∈ Bᶜ := h3 i₀ hi₀
    have hy : (y ^ 3) i₀ = i₀ := DFunLike.congr_fun hy3 i₀
    rw [hy] at hx
    exact (Finset.mem_compl.mp hx) hi₀

private theorem card_le_three_of_cube_one_perm_five {α : Type} [Finite α]
    (hα : Nat.card α = 5) {A : Subgroup (Perm α)} (hexp : ∀ x ∈ A, x ^ 3 = 1) :
    Nat.card A ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA3
  have hdiv : 3 ^ k ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card A
    rw [Nat.card_perm, hα, hk] at h
    norm_num at h
    exact h
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have h9 : 9 ∣ 3 ^ k := by
      have h := pow_dvd_pow 3 h2
      simpa using h
    have : 9 ∣ 120 := h9.trans hdiv
    norm_num at this
  calc Nat.card A = 3 ^ k := hk
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := by norm_num

private def restrictHom (C : Finset (Fin 10)) (H : Subgroup (alternatingGroup (Fin 10)))
    (h : ∀ y ∈ H, ∀ x, (y : Perm (Fin 10)) x ∈ C ↔ x ∈ C) : H →* Perm C where
  toFun y := (y.1 : Perm (Fin 10)).subtypePerm (h y.1 y.2)
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

private theorem restrictHom_apply (C : Finset (Fin 10))
    (H : Subgroup (alternatingGroup (Fin 10)))
    (h : ∀ y ∈ H, ∀ x, (y : Perm (Fin 10)) x ∈ C ↔ x ∈ C) (y : H) (x : C) :
    ((restrictHom C H h y x : C) : Fin 10) = (y : Perm (Fin 10)) x := rfl

private theorem exists_mem_sylow_fixing_block
    (S : Sylow 5 (alternatingGroup (Fin 10))) {B : Finset (Fin 10)}
    (hBcard : B.card = 5)
    (hBS : ∀ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), ∀ i ∈ B,
      (s : Perm (Fin 10)) i ∈ B) :
    ∃ s ∈ (S : Subgroup (alternatingGroup (Fin 10))), s ≠ 1 ∧
      ∀ i ∈ B, (s : Perm (Fin 10)) i = i := by
  classical
  have hSmap : ∀ s ∈ (S : Subgroup (alternatingGroup (Fin 10))),
      ∀ x, (s : Perm (Fin 10)) x ∈ B ↔ x ∈ B := by
    intro s hs x
    constructor
    · intro hx
      have hinv : s⁻¹ ∈ (S : Subgroup (alternatingGroup (Fin 10))) :=
        (S : Subgroup (alternatingGroup (Fin 10))).inv_mem hs
      have h := hBS s⁻¹ hinv ((s : Perm (Fin 10)) x) hx
      simpa using h
    · intro hx
      exact hBS s hs x hx
  let ρ : (S : Subgroup (alternatingGroup (Fin 10))) →* Perm ↥B :=
    restrictHom B (S : Subgroup (alternatingGroup (Fin 10))) hSmap
  have hScard : Nat.card (S : Subgroup (alternatingGroup (Fin 10))) = 25 := by
    simpa using CFSG.AGLEmbedding.KFactProofs.SmallIdent.sylowSq_of_isAltTwoP
      (p := 5) Nat.prime_five (by norm_num) (K := alternatingGroup (Fin 10))
      (hK := ⟨MulEquiv.refl (alternatingGroup (Fin 10))⟩) S
  have hBnat : Nat.card ↥B = 5 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hBcard]
  have hrange_le : Nat.card ρ.range ≤ 5 := by
    have h25 : Nat.card ρ.range ∣ 25 := by
      rw [← hScard]
      exact Subgroup.card_range_dvd ρ
    have h120 : Nat.card ρ.range ∣ 120 := by
      have h := Subgroup.card_subgroup_dvd_card ρ.range
      rwa [Nat.card_perm, hBnat] at h
    have h5 : Nat.card ρ.range ∣ 5 := by
      have h := Nat.dvd_gcd h25 h120
      norm_num at h ⊢
      exact h
    exact Nat.le_of_dvd (by norm_num) h5
  have hker_ne : ρ.ker ≠ ⊥ := by
    intro hbot
    have h := Subgroup.card_ker_mul_card_range ρ
    rw [hScard, hbot] at h
    have h1 : Nat.card ρ.range = 25 := by simpa using h
    omega
  haveI : Nontrivial ↥(ρ.ker) := (Subgroup.nontrivial_iff_ne_bot ρ.ker).mpr hker_ne
  obtain ⟨s, hs, hsne⟩ := Subgroup.exists_ne_one_of_nontrivial ρ.ker
  have hsfix : ∀ i ∈ B, (s : Perm (Fin 10)) i = i := by
    intro i hi
    have h1 : ρ s = 1 := MonoidHom.mem_ker.mpr hs
    have h2 := congrArg (fun z : Perm ↥B => ((z ⟨i, hi⟩ : ↥B) : Fin 10)) h1
    rw [restrictHom_apply] at h2
    simpa using h2
  refine ⟨s.1, s.2, ?_, hsfix⟩
  intro h
  exact hsne (Subtype.ext h)

private abbrev blockImage (D : AltTenSetup X N) (R : Subgroup X) :
    Subgroup (alternatingGroup (Fin 10)) :=
  (R.subgroupOf D.K).map D.e.toMonoidHom

private theorem le_generalizedFitting (D : AltTenSetup X N) {R : Subgroup X}
    (hRN : R ≤ N) (hexp : ∀ x ∈ R, x ^ 3 = 1) : R ≤ D.K := by
  haveI : D.K.Normal := D.hKn
  have hQdvd : Nat.card (X ⧸ D.K) ∣ 2 :=
    card_quotient_dvd_two_of_equiv_alternating (K := D.K) D.hKC (n := 10)
      (by norm_num) D.e
  have hmapbot : R.map (QuotientGroup.mk' D.K) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hy3 : (QuotientGroup.mk' D.K x) ^ 3 = 1 := by
      rw [← map_pow, hexp x hx, map_one]
    have hy2 : (QuotientGroup.mk' D.K x) ^ 2 = 1 := by
      have hpow : (QuotientGroup.mk' D.K x) ^ Nat.card (X ⧸ D.K) = 1 :=
        pow_card_eq_one'
      have hcases : Nat.card (X ⧸ D.K) = 1 ∨ Nat.card (X ⧸ D.K) = 2 := by
        have hle : Nat.card (X ⧸ D.K) ≤ 2 := Nat.le_of_dvd (by norm_num) hQdvd
        have hpos : 0 < Nat.card (X ⧸ D.K) := Nat.card_pos
        omega
      rcases hcases with h | h
      · rw [h, pow_one] at hpow
        rw [hpow]
        simp
      · rwa [h] at hpow
    have h1 : QuotientGroup.mk' D.K x = 1 := by
      calc QuotientGroup.mk' D.K x
          = (QuotientGroup.mk' D.K x) ^ 3 * ((QuotientGroup.mk' D.K x) ^ 2)⁻¹ := by
              group
        _ = 1 := by rw [hy3, hy2]; simp
    simpa using h1
  have hle := (Subgroup.map_eq_bot_iff R (f := QuotientGroup.mk' D.K)).mp hmapbot
  simpa [QuotientGroup.ker_mk'] using hle

private theorem card_blockImage (D : AltTenSetup X N) {R : Subgroup X} (hRK : R ≤ D.K) :
    Nat.card (blockImage D R) = Nat.card R := by
  change Nat.card ((R.subgroupOf D.K).map D.e.toMonoidHom) = Nat.card R
  rw [Subgroup.card_map_of_injective D.e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv

private theorem blockImage_exp (D : AltTenSetup X N) {R : Subgroup X}
    (hRK : R ≤ D.K) (hexp : ∀ x ∈ R, x ^ 3 = 1) :
    ∀ y ∈ blockImage D R, y ^ 3 = 1 := by
  intro y hy
  change y ∈ (R.subgroupOf D.K).map D.e.toMonoidHom at hy
  obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
  have hy0R : ((y0 : ↥D.K) : X) ∈ R := Subgroup.mem_subgroupOf.mp hy0
  have h3 : y0 ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hexp ((y0 : ↥D.K) : X) hy0R
  simpa [map_pow] using congrArg (fun z : ↥D.K => D.e z) h3

private theorem blockImage_fixes_block (D : AltTenSetup X N) {R : Subgroup X}
    (hRK : R ≤ D.K) (hRN : R ≤ N) (hexp : ∀ x ∈ R, x ^ 3 = 1) :
    ∀ y ∈ blockImage D R, ∀ x, (y : Perm (Fin 10)) x ∈ D.B ↔ x ∈ D.B := by
  have hexp' := blockImage_exp D hRK hexp
  have hW : blockImage D R ≤ (N.subgroupOf D.K).map D.e.toMonoidHom :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.K hRN)
  intro y hy x
  have hyW : y ∈ (N.subgroupOf D.K).map D.e.toMonoidHom := hW hy
  have hcases := D.hBover _ D.hNW D.hWne y hyW
  have hy3 : (y : Perm (Fin 10)) ^ 3 = 1 :=
    congrArg (fun z : alternatingGroup (Fin 10) => (z : Perm (Fin 10))) (hexp' y hy)
  exact fixes_block_of_cube_one D.hBcard hy3 hcases x

private theorem card_range_restrictHom_le_three {C : Finset (Fin 10)}
    {H : Subgroup (alternatingGroup (Fin 10))}
    (h : ∀ y ∈ H, ∀ x, (y : Perm (Fin 10)) x ∈ C ↔ x ∈ C)
    (hC : Nat.card ↥C = 5) (hexp : ∀ y ∈ H, y ^ 3 = 1) :
    Nat.card (restrictHom C H h).range ≤ 3 := by
  refine card_le_three_of_cube_one_perm_five hC ?_
  rintro _ ⟨y, rfl⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext (hexp y y.2)
  rw [← map_pow, hy3, map_one]

private theorem card_blockImage_le_nine (D : AltTenSetup X N) {R : Subgroup X}
    (hRK : R ≤ D.K) (hRN : R ≤ N) (hexp : ∀ x ∈ R, x ^ 3 = 1) :
    Nat.card (blockImage D R) ≤ 9 := by
  let R₁ := blockImage D R
  have hR₁exp := blockImage_exp D hRK hexp
  have hR₁B := blockImage_fixes_block D hRK hRN hexp
  have hR₁Bc : ∀ y ∈ R₁, ∀ x, (y : Perm (Fin 10)) x ∈ D.Bᶜ ↔ x ∈ D.Bᶜ := by
    intro y hy x
    have h := hR₁B y hy x
    simp only [Finset.mem_compl]
    exact not_congr h
  let ρB : R₁ →* Perm ↥D.B := restrictHom D.B R₁ hR₁B
  let ρBc : R₁ →* Perm ↥D.Bᶜ := restrictHom D.Bᶜ R₁ hR₁Bc
  have hρB_apply : ∀ (y : R₁) (x : ↥D.B),
      ((ρB y x : ↥D.B) : Fin 10) = (y : Perm (Fin 10)) x := fun y x => rfl
  have hρBc_apply : ∀ (y : R₁) (x : ↥D.Bᶜ),
      ((ρBc y x : ↥D.Bᶜ) : Fin 10) = (y : Perm (Fin 10)) x := fun y x => rfl
  have hBnat : Nat.card ↥D.B = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, D.hBcard]
  have hBcnat : Nat.card ↥D.Bᶜ = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      D.hBcard]
  have hB3 : Nat.card ρB.range ≤ 3 := card_range_restrictHom_le_three hR₁B hBnat hR₁exp
  have hBc3 : Nat.card ρBc.range ≤ 3 :=
    card_range_restrictHom_le_three hR₁Bc hBcnat hR₁exp
  let Ψ : R₁ → ↥(ρB.range) × ↥(ρBc.range) := fun y =>
    (⟨ρB y, ⟨y, rfl⟩⟩, ⟨ρBc y, ⟨y, rfl⟩⟩)
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    have h1 : ρB a = ρB b :=
      congrArg (fun z : ↥(ρB.range) => (z.1 : Perm ↥D.B)) (congrArg Prod.fst hab)
    have h2 : ρBc a = ρBc b :=
      congrArg (fun z : ↥(ρBc.range) => (z.1 : Perm ↥D.Bᶜ)) (congrArg Prod.snd hab)
    have hper : (a : Perm (Fin 10)) = (b : Perm (Fin 10)) :=
      Equiv.Perm.ext fun x => by
        by_cases hx : x ∈ D.B
        · have h3 := congrArg (fun z : Perm ↥D.B => ((z ⟨x, hx⟩ : ↥D.B) : Fin 10)) h1
          rw [hρB_apply, hρB_apply] at h3
          simpa using h3
        · have hxBc : x ∈ D.Bᶜ := Finset.mem_compl.mpr hx
          have h3 := congrArg
            (fun z : Perm ↥D.Bᶜ => ((z ⟨x, hxBc⟩ : ↥D.Bᶜ) : Fin 10)) h2
          rw [hρBc_apply, hρBc_apply] at h3
          simpa using h3
    exact Subtype.ext (Subtype.ext hper)
  have hle := Nat.card_le_card_of_injective Ψ hΨinj
  calc Nat.card R₁ ≤ Nat.card (↥(ρB.range) × ↥(ρBc.range)) := hle
    _ = Nat.card ↥(ρB.range) * Nat.card ↥(ρBc.range) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul hB3 hBc3
    _ = 9 := by norm_num

private theorem exists_fixing_Bc (D : AltTenSetup X N) {R : Subgroup X}
    (hRK : R ≤ D.K) (hRN : R ≤ N) (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hR1_9 : Nat.card (blockImage D R) = 9) :
    ∃ r0 ∈ blockImage D R, r0 ≠ 1 ∧
      ∀ i ∉ D.B, (r0 : Perm (Fin 10)) i = i := by
  let R₁ := blockImage D R
  have hR₁9 : Nat.card R₁ = 9 := hR1_9
  have hR₁exp := blockImage_exp D hRK hexp
  have hR₁B := blockImage_fixes_block D hRK hRN hexp
  have hR₁Bc : ∀ y ∈ R₁, ∀ x, (y : Perm (Fin 10)) x ∈ D.Bᶜ ↔ x ∈ D.Bᶜ := by
    intro y hy x
    have h := hR₁B y hy x
    simp only [Finset.mem_compl]
    exact not_congr h
  let ρBc : R₁ →* Perm ↥D.Bᶜ := restrictHom D.Bᶜ R₁ hR₁Bc
  have hρBc_apply : ∀ (y : R₁) (x : ↥D.Bᶜ),
      ((ρBc y x : ↥D.Bᶜ) : Fin 10) = (y : Perm (Fin 10)) x := fun y x => rfl
  have hBcnat : Nat.card ↥D.Bᶜ = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      D.hBcard]
  have hBc3 : Nat.card ρBc.range ≤ 3 :=
    card_range_restrictHom_le_three hR₁Bc hBcnat hR₁exp
  have hker_ne : ρBc.ker ≠ ⊥ := by
    intro hbot
    have h := Subgroup.card_ker_mul_card_range ρBc
    rw [hR₁9, hbot] at h
    have h1 : Nat.card ρBc.range = 9 := by simpa using h
    omega
  haveI : Nontrivial ↥(ρBc.ker) := (Subgroup.nontrivial_iff_ne_bot ρBc.ker).mpr hker_ne
  obtain ⟨r0, hr0, hr0ne⟩ := Subgroup.exists_ne_one_of_nontrivial ρBc.ker
  have hr0fix : ∀ i ∉ D.B, ((r0 : alternatingGroup (Fin 10)) : Perm (Fin 10)) i = i := by
    intro i hi
    have h1 : ρBc r0 = 1 := MonoidHom.mem_ker.mpr hr0
    have h2 := congrArg
      (fun z : Perm ↥D.Bᶜ => ((z ⟨i, Finset.mem_compl.mpr hi⟩ : ↥D.Bᶜ) : Fin 10)) h1
    rw [hρBc_apply] at h2
    simpa using h2
  refine ⟨r0.1, r0.2, ?_, hr0fix⟩
  intro h
  exact hr0ne (Subtype.ext h)

private theorem exists_r_fixing_Bc (D : AltTenSetup X N) {R : Subgroup X}
    (hRK : R ≤ D.K) (hRN : R ≤ N) (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hR1_9 : Nat.card (blockImage D R) = 9) :
    ∃ rK ∈ R.subgroupOf D.K, rK ≠ 1 ∧
      ∀ i ∉ D.B, (D.e rK : Perm (Fin 10)) i = i := by
  obtain ⟨r0, hr0, hr0ne, hr0fix⟩ := exists_fixing_Bc D hRK hRN hexp hR1_9
  change r0 ∈ (R.subgroupOf D.K).map D.e.toMonoidHom at hr0
  obtain ⟨rK, hrKRk, hrKe⟩ := Subgroup.mem_map.mp hr0
  have hrKe' : D.e rK = r0 := hrKe
  refine ⟨rK, hrKRk, ?_, ?_⟩
  · intro h
    apply hr0ne
    rw [← hrKe', h, map_one]
  · intro i hi
    rw [hrKe']
    exact hr0fix i hi

private theorem exists_five_commuting_three (D : AltTenSetup X N) {R : Subgroup X}
    (hRK : R ≤ D.K) (hRN : R ≤ N) (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hR1_9 : Nat.card (blockImage D R) = 9) :
    ∃ r ∈ R, r ≠ 1 ∧ ∃ x ∈ N, x ≠ 1 ∧ IsPGroup 5 (Subgroup.zpowers x) ∧
      x * r = r * x := by
  obtain ⟨rK, hrKRk, hrKne, hrKfix⟩ := exists_r_fixing_Bc D hRK hRN hexp hR1_9
  let yX : X := (rK : ↥D.K)
  have hyR : yX ∈ R := Subgroup.mem_subgroupOf.mp hrKRk
  have hy_ne : yX ≠ 1 := by
    intro h
    exact hrKne (Subtype.ext h)
  obtain ⟨s, hsS, hsne, hsfix⟩ := exists_mem_sylow_fixing_block D.S D.hBcard D.hBS
  let sK : ↥D.K := D.e.symm s
  have hsK_T : sK ∈ (D.T : Subgroup ↥D.K) := by
    have hs' : s ∈ (D.T : Subgroup ↥D.K).map D.e.toMonoidHom := by
      rw [← D.hScoe]
      exact hsS
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hs'
    have hte' : D.e t = s := hte
    have hst : sK = t := by
      dsimp [sK]
      rw [← hte', MulEquiv.symm_apply_apply]
    rwa [hst]
  let xX : X := (sK : ↥D.K)
  have hxN : xX ∈ N := Subgroup.mem_subgroupOf.mp (D.hTN hsK_T)
  have hx_ne : xX ≠ 1 := by
    intro h
    have h1 : sK = 1 := Subtype.ext h
    have h2 : D.e sK = 1 := by rw [h1, map_one]
    rw [show D.e sK = s from MulEquiv.apply_symm_apply D.e s] at h2
    exact hsne h2
  have hxP : IsPGroup 5 (Subgroup.zpowers xX) := by
    have hzp : IsPGroup 5 (Subgroup.zpowers sK) :=
      D.T.isPGroup'.to_le (Subgroup.zpowers_le.mpr hsK_T)
    have h := hzp.map D.K.subtype
    rwa [MonoidHom.map_zpowers] at h
  have hdisj : Disjoint (s : Perm (Fin 10)) (D.e rK : Perm (Fin 10)) := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro i
    by_cases hi : i ∈ D.B
    · exact Or.inl (hsfix i hi)
    · exact Or.inr (hrKfix i hi)
  have hcommP : (s : Perm (Fin 10)) * (D.e rK : Perm (Fin 10)) =
      (D.e rK : Perm (Fin 10)) * (s : Perm (Fin 10)) := hdisj.commute.eq
  have hcommA : s * D.e rK = D.e rK * s := Subtype.ext hcommP
  have hcommK : sK * rK = rK * sK := by
    apply D.e.injective
    rw [map_mul, map_mul]
    rw [show D.e sK = s from MulEquiv.apply_symm_apply D.e s]
    exact hcommA
  have hcommX : xX * yX = yX * xX := by
    have h := congrArg (fun z : ↥D.K => (z : X)) hcommK
    simpa [xX, yX] using h
  exact ⟨yX, hyR, hy_ne, xX, hxN, hx_ne, hxP, hcommX⟩

private theorem exists_commuting_pelement (D : AltTenSetup X N) {R : Subgroup X}
    (hO : CFSG.pPrimeCore 5 X = ⊥) (hN : IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10))
    (hRK : R ≤ D.K) (hRN : R ≤ N) (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hR1_9 : Nat.card (blockImage D R) = 9) :
    ∃ r ∈ R, r ≠ 1 ∧ ∃ c ∈ CFSG.generalizedFitting X,
      c * r = r * c ∧ IsPGroup 5 (Subgroup.zpowers c) ∧ c ∉ N := by
  obtain ⟨r, hrR, hrne, x, hxN, hxne, hxP, hcomm⟩ :=
    exists_five_commuting_three D hRK hRN hexp hR1_9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr3 : r ^ 3 = 1 := hexp r hrR
  have hr_order : orderOf r = 3 := orderOf_eq_prime hr3 hrne
  have horder : (orderOf r).Prime := by rw [hr_order]; exact Nat.prime_three
  have horder2 : orderOf r ≠ 2 := by rw [hr_order]; norm_num
  have horder5 : orderOf r ≠ 5 := by rw [hr_order]; norm_num
  obtain ⟨c, hcF, hcy, hcP, hcN⟩ :=
    (good_altTen hO hN e).2 x r hxN (hRN hrR) hxne hxP horder horder2 horder5 hcomm
  exact ⟨r, hrR, hrne, ⟨c, hcF, hcy, hcP, hcN⟩⟩

theorem autMAt_altTen {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 5 X = ⊥)
    {N : Subgroup X} (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10)) : AutMAt 5 N := by
  classical
  intro R hRN hexp h9
  obtain ⟨D⟩ := exists_altTen_setup hO hN e
  have hRK : R ≤ D.K := le_generalizedFitting D hRN hexp
  have hcardR1 : Nat.card (blockImage D R) = Nat.card R := card_blockImage D hRK
  have hle : Nat.card (blockImage D R) ≤ 9 := card_blockImage_le_nine D hRK hRN hexp
  have hR1_9 : Nat.card (blockImage D R) = 9 := by
    rw [hcardR1] at hle ⊢
    omega
  exact ⟨by rw [← hcardR1]; exact hR1_9,
    exists_commuting_pelement D hO hN e hRK hRN hexp hR1_9⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
