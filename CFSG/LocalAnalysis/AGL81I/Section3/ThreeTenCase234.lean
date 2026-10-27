module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL2Y
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBorelCase
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSylowTransfer

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn)

variable {H : Type} [Group H] [Finite H]

theorem centralizer_inf_eq_bot_of_threeTenHyp {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) :
    D ⊓ Subgroup.centralizer (I : Set H) = ⊥ := by
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  by_contra hne
  haveI hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  have hCnormal : (Subgroup.centralizer (I : Set H)).Normal := inferInstance
  let A : Subgroup H := D ⊓ Subgroup.centralizer (I : Set H)
  have hAne : A ≠ ⊥ := hne
  have hNY : Subgroup.normalizer (A : Set H) ⊓ (I ⊔ D) ≤ Y :=
    normalizer_inter_le_Y_of_nontrivial_le
      ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
      (show A ≤ D from inf_le_left) hAne
  have hI_le : I ≤ Subgroup.normalizer (A : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have haC : a ∈ Subgroup.centralizer (I : Set H) := (Subgroup.mem_inf.mp ha).2
      have hcomm : x * a = a * x := (Subgroup.mem_centralizer_iff.mp haC) x hx
      have hfix : x * a * x⁻¹ = a := by
        calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [hcomm]
          _ = a := by group
      rwa [hfix]
    · intro ha
      have haC : x * a * x⁻¹ ∈ Subgroup.centralizer (I : Set H) :=
        (Subgroup.mem_inf.mp ha).2
      have hcomm : x⁻¹ * (x * a * x⁻¹) = (x * a * x⁻¹) * x⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp haC) x⁻¹ (I.inv_mem hx)
      have hfix : x⁻¹ * (x * a * x⁻¹) * x = x * a * x⁻¹ := by
        calc x⁻¹ * (x * a * x⁻¹) * x = (x * a * x⁻¹) * x⁻¹ * x := by rw [hcomm]
          _ = x * a * x⁻¹ := by group
      have h' : x⁻¹ * (x * a * x⁻¹) * x = a := by group
      rw [← h', hfix]
      exact ha
  have hD_le : D ≤ Subgroup.normalizer (A : Set H) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have haD : a ∈ D := (Subgroup.mem_inf.mp ha).1
      have haC : a ∈ Subgroup.centralizer (I : Set H) := (Subgroup.mem_inf.mp ha).2
      exact ⟨D.mul_mem (D.mul_mem hy haD) (D.inv_mem hy),
        hCnormal.conj_mem a haC y⟩
    · intro ha
      have haD : y * a * y⁻¹ ∈ D := (Subgroup.mem_inf.mp ha).1
      have haC : y * a * y⁻¹ ∈ Subgroup.centralizer (I : Set H) :=
        (Subgroup.mem_inf.mp ha).2
      have hyinv : y⁻¹ ∈ D := D.inv_mem hy
      have h1 : y⁻¹ * (y * a * y⁻¹) * y ∈ D :=
        D.mul_mem (D.mul_mem hyinv haD) hy
      have h2 : y⁻¹ * (y * a * y⁻¹) * y ∈ Subgroup.centralizer (I : Set H) := by
        simpa using hCnormal.conj_mem (y * a * y⁻¹) haC y⁻¹
      rw [show y⁻¹ * (y * a * y⁻¹) * y = a by group] at h1 h2
      exact ⟨h1, h2⟩
  exact (not_le_of_gt hYlt)
    (le_trans (le_inf (sup_le hI_le hD_le) le_rfl) hNY)

theorem dvd_card_mulAut_of_threeTenHyp {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) :
    d ∣ Nat.card (MulAut ↥I) := by
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hhyp' : ThreeTenHyp I D P Y p d :=
    ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
  haveI : I.Normal := normal_of_oPPrimeHull_eq hI
  haveI : Fact d.Prime := ⟨hd⟩
  have hcent : D ⊓ Subgroup.centralizer (I : Set H) = ⊥ :=
    centralizer_inf_eq_bot_of_threeTenHyp hhyp'
  have hdvdD : d ∣ Nat.card ↥D := by
    rcases hD.isPGroup.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hDne
    · exact h1
  have hdvdAut : Nat.card ↥D ∣ Nat.card (MulAut ↥I) := by
    let φ : ↥D →* MulAut ↥I := (MulAut.conjNormal (H := I)).comp D.subtype
    have hφinj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      have hmem : (y : H)⁻¹ * (x : H) ∈ D ⊓ Subgroup.centralizer (I : Set H) := by
        refine ⟨D.mul_mem (D.inv_mem y.2) x.2, ?_⟩
        change (y : H)⁻¹ * (x : H) ∈ Subgroup.centralizer (I : Set H)
        rw [Subgroup.mem_centralizer_iff]
        intro i hi
        have hconj : (MulAut.conjNormal (x : H)) ⟨i, hi⟩ =
            (MulAut.conjNormal (y : H)) ⟨i, hi⟩ := by
          have hxy' := congrArg (fun f : MulAut ↥I => f ⟨i, hi⟩) hxy
          simpa [φ] using hxy'
        have hv : (x : H) * i * (x : H)⁻¹ = (y : H) * i * (y : H)⁻¹ := by
          have := congrArg Subtype.val hconj
          simpa using this
        have key : ((y : H)⁻¹ * (x : H)) * i = i * ((y : H)⁻¹ * (x : H)) := by
          calc ((y : H)⁻¹ * (x : H)) * i
              = (y : H)⁻¹ * ((x : H) * i) := by group
            _ = (y : H)⁻¹ * ((y : H) * i * (y : H)⁻¹ * (x : H)) := by
                have h2 : (x : H) * i = (y : H) * i * (y : H)⁻¹ * (x : H) := by
                  calc (x : H) * i = (x : H) * i * (x : H)⁻¹ * (x : H) := by group
                    _ = ((y : H) * i * (y : H)⁻¹) * (x : H) := by rw [hv]
                    _ = (y : H) * i * (y : H)⁻¹ * (x : H) := by group
                rw [h2]
            _ = i * ((y : H)⁻¹ * (x : H)) := by group
        exact key.symm
      rw [hcent] at hmem
      have h1 : (y : H)⁻¹ * (x : H) = 1 := Subgroup.mem_bot.mp hmem
      calc (x : H) = (y : H) * ((y : H)⁻¹ * (x : H)) := by group
        _ = (y : H) * 1 := by rw [h1]
        _ = (y : H) := by group
    have hcard : Nat.card ↥(φ.range) = Nat.card ↥D := by
      rw [MonoidHom.range_eq_map]
      rw [Subgroup.card_map_of_injective (K := ⊤) hφinj, Subgroup.card_top]
    have hdvd := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hcard] at hdvd
  exact hdvdD.trans hdvdAut

theorem inf_ne_bot_of_dvd_card {I D : Subgroup H} {d : ℕ} [Fact d.Prime]
    (hD : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (hI : I.Normal)
    (hdvd : d ∣ Nat.card ↥I) : D ⊓ I ≠ ⊥ := by
  intro hbot
  have hEsyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ I) I :=
    isSylowOf_inf_of_normal hI hD
  have hcard := hEsyl.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hfpos : 0 < (Nat.card ↥I).factorization d :=
    Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hdvd
  have hpow : 1 < d ^ (Nat.card ↥I).factorization d :=
    one_lt_pow' (Fact.out : d.Prime).one_lt hfpos.ne'
  exact (ne_of_gt hpow) hcard.symm

theorem false_of_normalizer_generation {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) (hEne : D ⊓ I ≠ ⊥)
    (hgen : Subgroup.normalizer (P.subgroupOf I : Set ↥I) ⊔
      Subgroup.normalizer ((D ⊓ I).subgroupOf I : Set ↥I) = ⊤) : False := by
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hhyp' : ThreeTenHyp I D P Y p d :=
    ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hDY : D ≤ Y := d_le_Y_of_threeTenHyp hhyp'
  have hNP : Subgroup.normalizer (P : Set H) ⊓ I ≤ Y := hN
  have hNE : Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I ≤ Y := by
    have h := normalizer_inter_le_Y_of_nontrivial_le hhyp' inf_le_left hEne
    exact le_trans (inf_le_inf_left _ (le_sup_left : I ≤ I ⊔ D)) h
  have hNPmap : (Subgroup.normalizer (P.subgroupOf I : Set ↥I)).map I.subtype =
      Subgroup.normalizer (P : Set H) ⊓ I := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPI, Subgroup.subgroupOf_map_subtype]
  have hNEmap : (Subgroup.normalizer ((D ⊓ I).subgroupOf I : Set ↥I)).map I.subtype =
      Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I := by
    rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right : D ⊓ I ≤ I),
      Subgroup.subgroupOf_map_subtype]
  have hsup : Subgroup.normalizer (P : Set H) ⊓ I ⊔
      Subgroup.normalizer ((D ⊓ I : Subgroup H) : Set H) ⊓ I = I := by
    have hmap := congrArg (fun K : Subgroup ↥I => K.map I.subtype) hgen
    rw [Subgroup.map_sup, hNPmap, hNEmap, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap
  have hI_le_Y : I ≤ Y := by
    rw [← hsup]
    exact sup_le hNP hNE
  exact (not_le_of_gt hYlt) (sup_le hI_le_Y hDY)

@[expose] def ThreeTenCase2SmallType (X : Type) [Group X] : Prop :=
  IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 7)))
    (fun B _ => Nat.card B = 2) X

@[expose] def ThreeTenCase3SmallType (X : Type) [Group X] : Prop :=
  IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 2) X ∨
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X ∨
    IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) X

@[expose] def ThreeTenCase4SmallType (X : Type) [Group X] : Prop :=
  IsSLType 2 (ZMod 5) X ∨
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
      (fun B _ => IsQ8D8Type B) X

@[expose] def ThreeTenCase2FiniteInput : Prop :=
  (∀ (X : Type) [Group X] [Finite X], ThreeTenCase2SmallType X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 7 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X) ∧
  (∀ (X : Type) [Group X] [Finite X] (P E : Subgroup X) (d : ℕ),
    ThreeTenCase2SmallType X → d.Prime → d ≠ 2 → d ≠ 7 →
      CFSG.ABGLocalTools.IsSylowOf 7 P ⊤ →
      CFSG.ABGLocalTools.IsSylowOf d E ⊤ →
      Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤)

@[expose] def ThreeTenCase3FiniteInput : Prop :=
  (∀ (X : Type) [Group X] [Finite X], ThreeTenCase3SmallType X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 5 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X) ∧
  (∀ (X : Type) [Group X] [Finite X] (P E : Subgroup X) (d : ℕ),
    ThreeTenCase3SmallType X → d.Prime → d ≠ 2 → d ≠ 5 →
      CFSG.ABGLocalTools.IsSylowOf 5 P ⊤ →
      CFSG.ABGLocalTools.IsSylowOf d E ⊤ →
      Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤)

@[expose] def ThreeTenCase4FiniteInput : Prop :=
  (∀ (X : Type) [Group X] [Finite X], ThreeTenCase4SmallType X →
    ∀ d : ℕ, d.Prime → d ≠ 2 → d ≠ 3 →
      d ∣ Nat.card (MulAut X) → d ∣ Nat.card X) ∧
  (∀ (X : Type) [Group X] [Finite X] (P E : Subgroup X) (d : ℕ),
    ThreeTenCase4SmallType X → d.Prime → d ≠ 2 → d ≠ 3 →
      CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ →
      CFSG.ABGLocalTools.IsSylowOf d E ⊤ →
      Subgroup.normalizer (P : Set X) ⊔ Subgroup.normalizer (E : Set X) = ⊤)

theorem threeTenCase2_of_finiteInput (h : ThreeTenCase2FiniteInput) : ThreeTenCase2 := by
  intro H _ _ I D P Y p d hhyp hcase
  obtain ⟨rfl, htype⟩ := hcase
  exfalso
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hhyp' : ThreeTenHyp I D P Y 7 d :=
    ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Fact (Nat.Prime 7) := ⟨hp⟩
  have hdvdAut : d ∣ Nat.card (MulAut ↥I) := dvd_card_mulAut_of_threeTenHyp hhyp'
  have hdvdI : d ∣ Nat.card ↥I := h.1 ↥I htype d hd hd2 hdp hdvdAut
  have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  have hEne : D ⊓ I ≠ ⊥ := inf_ne_bot_of_dvd_card hD hInormal hdvdI
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 7 P I := hP.of_le hPI le_top
  have hEsyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ I) I :=
    isSylowOf_inf_of_normal hInormal hD
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 7 (P.subgroupOf I) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 7) I
      (A := P.subgroupOf I) (B := ⊤)).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPI,
      Subgroup.map_top, Subgroup.range_subtype]
    exact hPsyl
  have hE'syl : CFSG.ABGLocalTools.IsSylowOf d ((D ⊓ I).subgroupOf I) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := d) I
      (A := (D ⊓ I).subgroupOf I) (B := ⊤)).mp ?_
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (inf_le_right : D ⊓ I ≤ I),
      Subgroup.map_top, Subgroup.range_subtype]
    exact hEsyl
  have hgen : Subgroup.normalizer (P.subgroupOf I : Set ↥I) ⊔
      Subgroup.normalizer ((D ⊓ I).subgroupOf I : Set ↥I) = ⊤ :=
    h.2 ↥I (P.subgroupOf I) ((D ⊓ I).subgroupOf I) d htype hd hd2 hdp hP'syl hE'syl
  exact false_of_normalizer_generation hhyp' hEne hgen

theorem threeTenCase3_of_finiteInput (h : ThreeTenCase3FiniteInput) : ThreeTenCase3 := by
  intro H _ _ I D P Y p d hhyp hcase
  obtain ⟨rfl, htype⟩ := hcase
  exfalso
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hhyp' : ThreeTenHyp I D P Y 5 d :=
    ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hdvdAut : d ∣ Nat.card (MulAut ↥I) := dvd_card_mulAut_of_threeTenHyp hhyp'
  have hdvdI : d ∣ Nat.card ↥I := h.1 ↥I htype d hd hd2 hdp hdvdAut
  have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  have hEne : D ⊓ I ≠ ⊥ := inf_ne_bot_of_dvd_card hD hInormal hdvdI
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 5 P I := hP.of_le hPI le_top
  have hEsyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ I) I :=
    isSylowOf_inf_of_normal hInormal hD
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 5 (P.subgroupOf I) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 5) I
      (A := P.subgroupOf I) (B := ⊤)).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPI,
      Subgroup.map_top, Subgroup.range_subtype]
    exact hPsyl
  have hE'syl : CFSG.ABGLocalTools.IsSylowOf d ((D ⊓ I).subgroupOf I) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := d) I
      (A := (D ⊓ I).subgroupOf I) (B := ⊤)).mp ?_
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (inf_le_right : D ⊓ I ≤ I),
      Subgroup.map_top, Subgroup.range_subtype]
    exact hEsyl
  have hgen : Subgroup.normalizer (P.subgroupOf I : Set ↥I) ⊔
      Subgroup.normalizer ((D ⊓ I).subgroupOf I : Set ↥I) = ⊤ :=
    h.2 ↥I (P.subgroupOf I) ((D ⊓ I).subgroupOf I) d htype hd hd2 hdp hP'syl hE'syl
  exact false_of_normalizer_generation hhyp' hEne hgen

theorem threeTenCase4_of_finiteInput (h : ThreeTenCase4FiniteInput) : ThreeTenCase4 := by
  intro H _ _ I D P Y p d hhyp hcase
  obtain ⟨rfl, htype⟩ := hcase
  exfalso
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hhyp' : ThreeTenHyp I D P Y 3 d :=
    ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hdvdAut : d ∣ Nat.card (MulAut ↥I) := dvd_card_mulAut_of_threeTenHyp hhyp'
  have hdvdI : d ∣ Nat.card ↥I := h.1 ↥I htype d hd hd2 hdp hdvdAut
  have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  have hEne : D ⊓ I ≠ ⊥ := inf_ne_bot_of_dvd_card hD hInormal hdvdI
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P I := hP.of_le hPI le_top
  have hEsyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ I) I :=
    isSylowOf_inf_of_normal hInormal hD
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf I) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) I
      (A := P.subgroupOf I) (B := ⊤)).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPI,
      Subgroup.map_top, Subgroup.range_subtype]
    exact hPsyl
  have hE'syl : CFSG.ABGLocalTools.IsSylowOf d ((D ⊓ I).subgroupOf I) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := d) I
      (A := (D ⊓ I).subgroupOf I) (B := ⊤)).mp ?_
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (inf_le_right : D ⊓ I ≤ I),
      Subgroup.map_top, Subgroup.range_subtype]
    exact hEsyl
  have hgen : Subgroup.normalizer (P.subgroupOf I : Set ↥I) ⊔
      Subgroup.normalizer ((D ⊓ I).subgroupOf I : Set ↥I) = ⊤ :=
    h.2 ↥I (P.subgroupOf I) ((D ⊓ I).subgroupOf I) d htype hd hd2 hdp hP'syl hE'syl
  exact false_of_normalizer_generation hhyp' hEne hgen

end CFSG.LocalAnalysis.AGL81I.Section3
