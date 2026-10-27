module

public import CFSG.CGT.PushingUpLit.Glue.CStarBridge
public import CFSG.CGT.PushingUpLit.Glue.BlockInX

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin

section Subnormal

variable {Γ : Type} [Group Γ]

theorem isSubnormal_of_mem_family {𝒢 : Set (Subgroup Γ)}
    (hinv : ∀ E ∈ 𝒢, ∀ g : Γ, A1b.conjSub g E ∈ 𝒢)
    (hcomm : ∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x)
    {E : Subgroup Γ} (hE : E ∈ 𝒢) : E.IsSubnormal := by
  have hNn : (sSup 𝒢).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : sSup 𝒢 ≤ (sSup 𝒢).comap (MulAut.conj g).toMonoidHom :=
      sSup_le fun F hF x hx =>
        le_sSup (hinv F hF g) ⟨x, hx, rfl⟩
    exact hle hn
  have hEN : E ≤ sSup 𝒢 := le_sSup hE
  have hnorm : sSup 𝒢 ≤ Subgroup.normalizer (E : Set Γ) := by
    refine sSup_le fun F hF => ?_
    by_cases hFE : F = E
    · rw [hFE]
      exact Subgroup.le_normalizer
    · intro y hy
      exact Subgroup.centralizer_le_normalizer (E : Set Γ) (Subgroup.mem_centralizer_iff.mpr fun h hh =>
        hcomm E hE F hF (Ne.symm hFE) h hh y hy)
  exact Subgroup.IsSubnormal.step E (sSup 𝒢) hEN (Subgroup.Normal.isSubnormal hNn)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hEN).mpr hnorm)

end Subnormal

section Borel

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem isSylowOf_inf_of_isSubnormal {T H : Subgroup Γ} (hT : IsSylowOf 2 T ⊤)
    (hH : H.IsSubnormal) : IsSylowOf 2 (T ⊓ H) H := by
  have hT' : ABGLocalTools.IsSylowOf 2 T ⊤ := ABGLocalTools.isSylowOf_iff.2 hT
  have key : ∀ K : Subgroup Γ, K.IsSubnormal → ABGLocalTools.IsSylowOf 2 (T ⊓ K) K := by
    intro K hK
    induction hK with
    | top => simpa using hT'
    | step H K hHK _ hN ih =>
      have h1 := ih.inf_of_le_normalizer hHK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
      rwa [inf_assoc, inf_eq_right.mpr hHK] at h1
  exact ABGLocalTools.isSylowOf_iff.1 (key H hH)

omit [Finite Γ] in
theorem two_dvd_card_sl2 (F : Type) [Field F] [CharP F 2] :
    2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  let x : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have hx1 : x ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [x] at this
  have hxx : x * x = 1 := by
    apply Subtype.ext
    show (!![1, 1; 0, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  have hx2 : x ^ 2 = 1 := by rw [pow_two, hxx]
  have h2 : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have h := orderOf_dvd_natCard x
  rwa [h2] at h

theorem false_of_sl_normalizes {T E : Subgroup Γ} (hT : IsSylowOf 2 T ⊤) (hEsub : E.IsSubnormal)
    {n : ℕ} (hE : IsNaturalSLTwoModule ↥E n)
    (hnorm : E ≤ Subgroup.normalizer ((T ⊓ E : Subgroup Γ) : Set Γ)) : False := by
  obtain ⟨-, hp, hodd⟩ := isSylowOf_inf_of_isSubnormal hT hEsub
  have hPn : ((T ⊓ E).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnorm
  have hPp : IsPGroup 2 ((T ⊓ E).subgroupOf E) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hPcore : (T ⊓ E).subgroupOf E ≤ pCore 2 ↥E := le_sSup ⟨hPn, hPp⟩
  have hdvd : (pCore 2 ↥E).index ∣ ((T ⊓ E).subgroupOf E).index :=
    Subgroup.index_dvd_of_le hPcore
  have hodd' : ¬ 2 ∣ (pCore 2 ↥E).index := fun h => hodd (h.trans hdvd)
  obtain ⟨φ, -⟩ := hE
  have hcard : (pCore 2 ↥E).index =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr φ.toEquiv
  exact hodd' (hcard ▸ two_dvd_card_sl2 (GaloisField 2 n))

omit [Finite Γ] in
theorem false_of_alt_top {E : Subgroup Γ} {m : ℕ} (hm : 1 ≤ m) (hE : IsNaturalAltModule ↥E m)
    (e : ↥(⊤ : Subgroup (↥E ⧸ pCore 2 ↥E)) ≃* alternatingGroup (Fin (2 * m))) : False := by
  obtain ⟨φ, -⟩ := hE
  have h1 : Nat.card (↥E ⧸ pCore 2 ↥E) = Nat.card (alternatingGroup (Fin (2 * m + 1))) :=
    Nat.card_congr φ.toEquiv
  have h2 : Nat.card (↥E ⧸ pCore 2 ↥E) = Nat.card (alternatingGroup (Fin (2 * m))) := by
    rw [← Nat.card_congr (Subgroup.topEquiv (G := ↥E ⧸ pCore 2 ↥E)).toEquiv]
    exact Nat.card_congr e.toEquiv
  rw [h1] at h2
  have : Nontrivial (Fin (2 * m + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have : Nontrivial (Fin (2 * m)) := Fin.nontrivial_iff_two_le.2 (by omega)
  simp only [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h2
  have hd1 : 2 ∣ (2 * m + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hd2 : 2 ∣ (2 * m).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  rw [Nat.div_left_inj hd1 hd2, Nat.factorial_succ] at h2
  have h3 : (2 * m + 1) = 1 := Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) (by simpa using h2)
  omega

theorem not_le_cStarIn_of_block {T E : Subgroup Γ} (hT : IsSylowOf 2 T ⊤) (hEsub : E.IsSubnormal)
    (hlast : ((∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∧
          cStarIn ⊤ T ⊓ E = Subgroup.normalizer ((T ⊓ E : Subgroup Γ) : Set Γ) ⊓ E) ∨
        ∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m ∧
          Nonempty ((((cStarIn ⊤ T ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
            alternatingGroup (Fin (2 * m)))) :
    ¬ E ≤ cStarIn ⊤ T := by
  intro hEC
  rcases hlast with ⟨⟨n, hn, hE⟩, hCE⟩ | ⟨m, hm, hE, ⟨e⟩⟩
  · refine false_of_sl_normalizes hT hEsub hE fun x hx => ?_
    have hx' : x ∈ cStarIn ⊤ T ⊓ E := ⟨hEC hx, hx⟩
    rw [hCE] at hx'
    exact hx'.1
  · have htop : (cStarIn ⊤ T ⊓ E).subgroupOf E = ⊤ :=
      Subgroup.subgroupOf_eq_top.mpr (le_inf hEC le_rfl)
    rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at e
    exact false_of_alt_top hm hE e

end Borel

theorem charTwo_of_isSubnormal_top {Γ : Type} [Group Γ] [Finite Γ]
    (hΓ : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup Γ)) {E : Subgroup Γ} (hE : E.IsSubnormal) :
    CFSG.QuasithinUnique.CharTwo E := by
  have key : ∀ K : Subgroup Γ, K.IsSubnormal → CFSG.QuasithinUnique.CharTwo K := by
    intro K hK
    induction hK with
    | top => exact hΓ
    | step H K hHK _ hN ih => exact CFSG.QuasithinUnique.CharTwo.of_normal ih hHK hN
  exact key E hE

theorem aschbacherLocalFactorization_of_bhs (h : BHSLocalCStar) : AschbacherLocalFactorization := by
  intro G _ _ _ hchar T
  by_cases hC : characteristicCoreStar (T : Subgroup G) = ⊤
  · rw [hC]
    exact sup_top_eq _
  · have hC' : cStarIn (⊤ : Subgroup G) (T : Subgroup G) ≠ ⊤ := by
      rwa [← characteristicCoreStar_eq_cStarIn]
    have hch := charTwo_top_of_isCharacteristicP hchar
    have hTs := isSylowOf_top T
    obtain ⟨𝒢, hB, hinv, hcomm, hgen, -, -, hlast⟩ := h G ⊤ T hch hTs hC'
    have hinv' : ∀ F ∈ 𝒢, ∀ g : G, A1b.conjSub g F ∈ 𝒢 := fun F hF g =>
      hinv F hF g (Subgroup.mem_top g)
    have hmem : ∀ E ∈ 𝒢, E ∈ blocksStar (T : Subgroup G) := by
      intro E hE
      have hsub : E.IsSubnormal := isSubnormal_of_mem_family hinv' hcomm hE
      have hcharE := charTwo_of_isSubnormal_top hch hsub
      refine ⟨⟨hsub, inClassX_of_isBTBlock (hB E hE) hcharE⟩, fun g hg => ?_⟩
      have hF : A1b.conjSub g E ∈ 𝒢 := hinv' E hE g
      have hle : A1b.conjSub g E ≤ cStarIn ⊤ (T : Subgroup G) := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨c, hc, hcy⟩ := hg hy
        have h1 : (MulAut.conj g).toMonoidHom y = c := by
          rw [← hcy]
          simp [MulAut.conj_apply]
          group
        rw [← characteristicCoreStar_eq_cStarIn, h1]
        exact hc
      exact not_le_cStarIn_of_block hTs (isSubnormal_of_mem_family hinv' hcomm hF) (hlast _ hF) hle
    refine eq_top_iff.mpr ?_
    rw [← hgen, ← characteristicCoreStar_eq_cStarIn]
    exact sup_le le_sup_right
      (le_trans (iSup₂_le fun E hE => le_iSup₂_of_le E (hmem E hE) le_rfl) le_sup_left)

end CFSG.CGT.PushingUpLit.Glue
