module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFactsBasic
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Pointwise

namespace ChapterII

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subtype_comp_wreathModelHom_subtype {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) :
    H.subtype.comp
        (wreathModelHom (S.subtype hSH) ((Subgroup.subgroupOfEquivOfLe hSH).trans e)) =
      wreathModelHom S e :=
  rfl

omit [Finite G] in
theorem modelT_sylow_subtype (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) :
    modelT n (S.subtype hSH) ((Subgroup.subgroupOfEquivOfLe hSH).trans e) =
      (modelT n S e).subgroupOf H := by
  have h : modelT n S e =
      (modelT n (S.subtype hSH) ((Subgroup.subgroupOfEquivOfLe hSH).trans e)).map H.subtype := by
    unfold modelT
    rw [Subgroup.map_map, subtype_comp_wreathModelHom_subtype]
  rw [h]
  exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm

omit [Finite G] in
theorem modelBase_sylow_subtype {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) :
    modelBase (S.subtype hSH) ((Subgroup.subgroupOfEquivOfLe hSH).trans e) =
      (modelBase S e).subgroupOf H := by
  have h : modelBase S e =
      (modelBase (S.subtype hSH) ((Subgroup.subgroupOfEquivOfLe hSH).trans e)).map H.subtype := by
    unfold modelBase
    rw [Subgroup.map_map, subtype_comp_wreathModelHom_subtype]
  rw [h]
  exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm

theorem automizerIndex_T_eq_base (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H) :
    automizerIndex ((wreathedSetting n S e p f).T.subgroupOf H) =
      automizerIndex
        (modelBase (S.subtype hSH) ((Subgroup.subgroupOfEquivOfLe hSH).trans e)) := by
  rw [wreathedSetting_T_eq n (by omega) S e p f, ← modelT_sylow_subtype n S e hSH]
  exact Nat.card_congr (originalFourToBaseNormalizerQuotientEquiv n hn _ _).toEquiv

omit [Finite G] in
theorem sylow_le_of_D_le (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) {H : Subgroup G}
    (hDH : (wreathedSetting n S e p f).D ≤ H ∨ (wreathedSetting n S e p f).height = 1) :
    (S : Subgroup G) ≤ H := by
  rcases hDH with h | h
  · rwa [wreathedSetting_D_eq n (by omega) S e p f] at h
  · exact absurd h (show n ≠ 1 by omega)

omit [Finite G] in
theorem isKleinFour_T_subgroupOf (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) {H : Subgroup G} (hTH : (wreathedSetting n S e p f).T ≤ H) :
    IsKleinFour ((wreathedSetting n S e p f).T.subgroupOf H) := by
  have := modelT_isKleinFour n hn S e
  rw [← wreathedSetting_T_eq n hn S e p f] at this
  exact Semidihedral.Local.isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTH).symm

section Automizer

variable {Γ : Type*} [Group Γ]

theorem normalizerMonoidHom_eq_one_iff (V : Subgroup Γ) (y : Subgroup.normalizer (V : Set Γ)) :
    V.normalizerMonoidHom y = 1 ↔ (y : Γ) ∈ Subgroup.centralizer (V : Set Γ) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

theorem three_dvd_automizerIndex_of_mem [Finite Γ] (V : Subgroup Γ) {y : Γ}
    (hyN : y ∈ Subgroup.normalizer (V : Set Γ)) (hyC : y ∉ Subgroup.centralizer (V : Set Γ))
    (hy3 : y ^ 3 ∈ Subgroup.centralizer (V : Set Γ)) : 3 ∣ automizerIndex V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [automizerIndex_eq_card_range]
  let y' : Subgroup.normalizer (V : Set Γ) := ⟨y, hyN⟩
  let ψ : V.normalizerMonoidHom.range := ⟨V.normalizerMonoidHom y', y', rfl⟩
  have hψ : orderOf ψ = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change V.normalizerMonoidHom y' ^ 3 = 1
      rw [← map_pow, normalizerMonoidHom_eq_one_iff]
      exact hy3
    · intro h
      apply hyC
      rw [← normalizerMonoidHom_eq_one_iff V y']
      exact congrArg Subtype.val h
  rw [← hψ]
  exact orderOf_dvd_natCard ψ

theorem exists_mem_of_three_dvd_automizerIndex [Finite Γ] (V : Subgroup Γ)
    (h3 : 3 ∣ automizerIndex V) :
    ∃ y ∈ Subgroup.normalizer (V : Set Γ), y ∉ Subgroup.centralizer (V : Set Γ) ∧
      y ^ 3 ∈ Subgroup.centralizer (V : Set Γ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [automizerIndex_eq_card_range] at h3
  obtain ⟨⟨ψ, y, rfl⟩, hψ⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨y, y.2, fun hy => ?_, ?_⟩
  · have h1 : V.normalizerMonoidHom y = 1 := (normalizerMonoidHom_eq_one_iff V y).mpr hy
    have h2 : (⟨V.normalizerMonoidHom y, y, rfl⟩ : V.normalizerMonoidHom.range) = 1 :=
      Subtype.ext h1
    rw [h2, orderOf_one] at hψ
    omega
  · have h1 := pow_orderOf_eq_one (⟨V.normalizerMonoidHom y, y, rfl⟩ :
      V.normalizerMonoidHom.range)
    rw [hψ] at h1
    have h2 : V.normalizerMonoidHom (y ^ 3) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val h1
    exact (normalizerMonoidHom_eq_one_iff V (y ^ 3)).mp h2

end Automizer

theorem isSylowOf_of_le (P : Sylow 2 G) {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) :
    IsSylowOf 2 (P : Subgroup G) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_iff.mpr ⟨hPK, P.isPGroup', fun hdvd =>
    P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPK))⟩

theorem mem_normalizer_of_conj_mem {J : Subgroup G} {g : G}
    (h : ∀ y ∈ J, g * y * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem isSolvable_of_isDGroupData {H : Type} [Group H] [Finite H] {K : Subgroup H}
    (hK : IsDGroupData K) {n : ℕ} (hW : HasWreathedSylow H n) : Group.IsSolvable H := by
  obtain ⟨hK', hW'⟩ := CFSG.ABGDGroups.isDGroupData_quotient_oddCore hK hW
  obtain ⟨U, hUn, -, ⟨eU⟩, -, -, -, ⟨e3⟩⟩ := CFSG.ABGDGroups.wreathed_dGroup_structure
    (SimpleOddIndexQuotient.actual_oddCore_quotient_eq_bot H) hK' hW'
  have : Group.IsSolvable U := Group.isSolvable_of_comm fun a b =>
    eU.injective (by rw [map_mul, map_mul, mul_comm])
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have : Group.IsSolvable ((H ⧸ CFSG.oddCore H) ⧸ U) :=
    Group.isSolvable_of_surjective (f := e3.symm.toMonoidHom) e3.symm.surjective
  have : Group.IsSolvable (H ⧸ CFSG.oddCore H) := Group.isSolvable_of_subgroup_quotient U
  have : Group.IsSolvable (CFSG.oddCore H) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCore H)
  exact Group.isSolvable_of_subgroup_quotient (CFSG.oddCore H)

theorem sylow_le_of_normal_of_isQDGroup (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) {H X : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    (hQD : IsQDGroup H) (hXH : X ≤ H) (hHX : H ≤ Subgroup.normalizer (X : Set G))
    (hTX : (wreathedSetting n S e p f).T ≤ X) : (S : Subgroup G) ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hSL, hmin⟩ := hQD.involutionClosure_quotient_oddCore
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  set X' := X.subgroupOf H
  have hX'n : X'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX
  have hxX : (wreathedSetting n S e p f).x ∈ X := hTX (wreathedSetting n S e p f).x_mem_T
  have hxorder : orderOf (wreathedSetting n S e p f).x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hXb1 : X'.map π ≠ ⊥ := by
    intro hbot
    have h1 : π ⟨_, hXH hxX⟩ = 1 := by
      rw [← Subgroup.mem_bot, ← hbot]
      exact ⟨_, hxX, rfl⟩
    have hmem : (⟨_, hXH hxX⟩ : H) ∈ CFSG.oddCore H := (QuotientGroup.eq_one_iff _).mp h1
    have hdvd := Subgroup.orderOf_dvd_natCard (CFSG.oddCore H) hmem
    rw [Subgroup.orderOf_mk, hxorder] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCore H)) (even_iff_two_dvd.mpr hdvd)
  have hle := hmin _ (hX'n.map π (QuotientGroup.mk'_surjective _)) hXb1
  have hSb := hSL ((S.subtype hSH).mapSurjective (QuotientGroup.mk'_surjective _))
  intro s hs
  have hsb : π ⟨s, hSH hs⟩ ∈ X'.map π := by
    apply hle
    apply hSb
    rw [Sylow.coe_mapSurjective]
    exact ⟨⟨s, hSH hs⟩, hs, rfl⟩
  obtain ⟨y, hyX, hy⟩ := hsb
  have ho : y⁻¹ * ⟨s, hSH hs⟩ ∈ CFSG.oddCore H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (π y)⁻¹ * π ⟨s, hSH hs⟩ = 1
    rw [hy, inv_mul_cancel]
  set ρ := QuotientGroup.mk' X'
  have hρy : ρ y = 1 := (QuotientGroup.eq_one_iff y).mpr hyX
  have hρ : ρ ⟨s, hSH hs⟩ = ρ (y⁻¹ * ⟨s, hSH hs⟩) := by
    rw [map_mul, map_inv, hρy, inv_one, one_mul]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨s, hs⟩
  have h1 : orderOf (ρ ⟨s, hSH hs⟩) ∣ 2 ^ k := by
    rw [← hk, Subgroup.orderOf_mk]
    have := orderOf_map_dvd ρ ⟨s, hSH hs⟩
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (ρ ⟨s, hSH hs⟩) ∣ Nat.card (CFSG.oddCore H) := by
    rw [hρ]
    refine (orderOf_map_dvd ρ _).trans ?_
    rw [← Subgroup.orderOf_mk _ ho]
    exact orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_card_oddCore H))) h1 h2
  rw [orderOf_eq_one_iff] at h3
  have h4 : (⟨s, hSH hs⟩ : H) ∈ X' := (QuotientGroup.eq_one_iff _).mp h3
  exact h4

end ChapterII

open ChapterII

variable {G : Type} [Group G] [Finite G]

theorem wreathedSetting_fusion_cases (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ H : Subgroup G, H ≠ ⊤ → (wreathedSetting n S e p f).T ≤ H →
      ((wreathedSetting n S e p f).D ≤ H ∨ (wreathedSetting n S e p f).height = 1) →
        IsQDGroup H ∨ IsQGroup H ∨ IsDGroup H ∨ HasNormalPComplement 2 H := by
  intro H _ _ hDH
  have hSH := sylow_le_of_D_le n hn S e p f hDH
  exact fusion_class_cases (Or.inl ⟨n, Or.inr (hasWreathedSylow_of hn (S.subtype hSH)
    ((Subgroup.subgroupOfEquivOfLe hSH).trans e))⟩)

theorem wreathedSetting_qd_or_d_of_three (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ H : Subgroup G, (wreathedSetting n S e p f).T ≤ H →
      ((wreathedSetting n S e p f).D ≤ H ∨ (wreathedSetting n S e p f).height = 1) →
        3 ∣ automizerIndex ((wreathedSetting n S e p f).T.subgroupOf H) →
          IsQDGroup H ∨ IsDGroupWrt ((wreathedSetting n S e p f).T.subgroupOf H) := by
  intro H hTH hDH h3
  have hSH := sylow_le_of_D_le n hn S e p f hDH
  set SH := S.subtype hSH
  set eH : (SH : Subgroup H) ≃* Wreath (2 ^ n) := (Subgroup.subgroupOfEquivOfLe hSH).trans e
  have hA := automizerIndex_T_eq_base n hn S e p f hSH
  rcases fusion_class_cases (Or.inl ⟨n, Or.inr (hasWreathedSylow_of hn SH eH)⟩) with
    hQD | hQ | hD | hC
  · exact Or.inl hQD
  · rw [hA, ((wreathed_isQGroup_iff hn SH eH).mp hQ).baseIndex] at h3
    norm_num at h3
  · exact Or.inr ⟨hD, isKleinFour_T_subgroupOf n (by omega) S e p f hTH, h3⟩
  · rw [hA, ((wreathed_hasNormalPComplement_iff hn SH eH).mp hC).baseIndex] at h3
    norm_num at h3

theorem wreathedSetting_solvable_dgroup_signalizer (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ H : Subgroup G, (wreathedSetting n S e p f).D ≤ H →
      IsDGroupWrt ((wreathedSetting n S e p f).T.subgroupOf H) → Group.IsSolvable H →
        ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ X : Subgroup G, X ≤ H → IsPGroup r X →
          (wreathedSetting n S e p f).T ≤ Subgroup.normalizer (X : Set G) →
            X ≤ oddCoreIn H := by
  intro H hDH hDw _ r hr hr2 X hXH hX hTX
  have hSH := sylow_le_of_D_le n hn S e p f (Or.inl hDH)
  have hW := hasWreathedSylow_of hn (S.subtype hSH) ((Subgroup.subgroupOfEquivOfLe hSH).trans e)
  obtain ⟨hD, hK4, -⟩ := hDw
  rcases hD with ⟨hdih, -⟩ | ⟨K, hK⟩
  · exact (not_hasWreathedSylow_and_dihedral hW hdih).elim
  · have : Fact r.Prime := ⟨hr⟩
    have hXodd : Odd (Nat.card (X.subgroupOf H)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
      obtain ⟨k, hk⟩ := hX.exists_card_eq
      rw [hk]
      exact (hr.odd_of_ne_two hr2).pow
    have hXT : (wreathedSetting n S e p f).T.subgroupOf H ≤
        Subgroup.normalizer ((X.subgroupOf H : Subgroup H) : Set H) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hXH]
      exact fun t ht => hTX ht
    have h := CFSG.ABGDGroups.wreathed_dGroup_odd_four_invariant_le_oddCore hK hW hK4 hXodd hXT
    intro x hx
    exact ⟨⟨x, hXH hx⟩, h hx, rfl⟩

theorem wreathedSetting_normal_contains_three [IsSimpleGroup G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) :
    ∀ H : Subgroup G, (wreathedSetting n S e p f).D ≤ H →
      (IsQDGroup H ∨ (IsDGroupWrt ((wreathedSetting n S e p f).T.subgroupOf H) ∧
        ¬ Group.IsSolvable H)) →
        ∀ X : Subgroup G, X ≤ H → H ≤ Subgroup.normalizer (X : Set G) →
          (wreathedSetting n S e p f).T ≤ X →
            ∃ T₁ : Subgroup G, T₁ ≤ X ∧ IsKleinFour T₁ ∧
              3 ∣ automizerIndex (T₁.subgroupOf X) := by
  intro H hDH hcase X hXH hHX hTX
  have hSH := sylow_le_of_D_le n hn S e p f (Or.inl hDH)
  set SH := S.subtype hSH
  set eH : (SH : Subgroup H) ≃* Wreath (2 ^ n) := (Subgroup.subgroupOfEquivOfLe hSH).trans e
  have hW := hasWreathedSylow_of hn SH eH
  rcases hcase with hQD | ⟨⟨hD, -, -⟩, hns⟩
  swap
  · exfalso
    apply hns
    rcases hD with ⟨hdih, -⟩ | ⟨K, hK⟩
    · exact (not_hasWreathedSylow_and_dihedral hW hdih).elim
    · exact isSolvable_of_isDGroupData hK hW
  set T := (wreathedSetting n S e p f).T
  set U := modelBase S e
  have hTeq : T = modelT n S e := wreathedSetting_T_eq n (by omega) S e p f
  have hTU : T ≤ U := by
    rw [hTeq]
    exact modelT_le_base n (by omega) S e
  have hUS : U ≤ (S : Subgroup G) := modelBase_le_sylow S e
  have hSX := sylow_le_of_normal_of_isQDGroup n hn S e p f hSH hQD hXH hHX hTX
  refine ⟨T, hTX, ?_, ?_⟩
  · rw [hTeq]
    exact modelT_isKleinFour n (by omega) S e
  have h6 : automizerIndex (modelBase SH eH) = 6 :=
    ((wreathed_isQDGroup_iff hn SH eH).mp hQD).baseIndex
  rw [modelBase_sylow_subtype S e hSH] at h6
  obtain ⟨y, hyN, hyC, hy3⟩ := exists_mem_of_three_dvd_automizerIndex (U.subgroupOf H)
    (by rw [h6]; norm_num)
  rw [← Subgroup.subgroupOf_normalizer_eq (hUS.trans hSH)] at hyN
  rw [centralizer_subgroupOf (hUS.trans hSH)] at hyC hy3
  set g : G := (y : G)
  have hgH : g ∈ H := y.2
  have hgS : ((g • S : Sylow 2 G) : Subgroup G) ≤ X := by
    intro z hz
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hz
    have h := (Subgroup.mem_normalizer_iff.mp (hHX hgH) _).mp (hSX hz)
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h
  obtain ⟨k, hkX, hconj⟩ :=
    (isSylowOf_of_le S hSX).exists_mem_conj (isSylowOf_of_le (g • S) hgS)
  have hkg : k⁻¹ * g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro s hs
    have hs' : g * s * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply, show g⁻¹ * (g * s * g⁻¹) * g = s by group]
      exact hs
    have h := (hconj _).mp hs'
    rwa [show k⁻¹ * (g * s * g⁻¹) * k = k⁻¹ * g * s * (k⁻¹ * g)⁻¹ by group] at h
  obtain ⟨s, hs, hsc⟩ := BrauerWong.exists_sylow_mul_mem_centralizer n hn S e _ hkg
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = k * s := ⟨_, rfl⟩
  have hxX : x ∈ X := hxdef ▸ X.mul_mem hkX (hSX hs)
  have hxc : x⁻¹ * g ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rwa [hxdef, show (k * s)⁻¹ * g = s⁻¹ * (k⁻¹ * g) by group]
  have hact : ∀ u ∈ U, x * u * x⁻¹ = g * u * g⁻¹ := by
    intro u hu
    have hc := Subgroup.mem_centralizer_iff.mp hxc u (hUS hu)
    calc x * u * x⁻¹ = x * (u * (x⁻¹ * g)) * (x⁻¹ * g)⁻¹ * x⁻¹ := by group
      _ = x * ((x⁻¹ * g) * u) * (x⁻¹ * g)⁻¹ * x⁻¹ := by rw [hc]
      _ = g * u * g⁻¹ := by group
  have hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hyN u).mp hu
  have hxN : x ∈ Subgroup.normalizer (U : Set G) :=
    mem_normalizer_of_conj_mem fun u hu => (hact u hu) ▸ hgU u hu
  have hxC : x ∉ Subgroup.centralizer (U : Set G) := by
    intro hx
    apply hyC
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := Subgroup.mem_centralizer_iff.mp hx u hu
    have h3 : g * u * g⁻¹ = u := by
      rw [← hact u hu, ← h1]
      group
    calc u * g = (g * u * g⁻¹) * g := by rw [h3]
      _ = g * u := by group
  have hg3 : g ^ 3 ∈ Subgroup.centralizer (U : Set G) := by
    rw [show g ^ 3 = ((y ^ 3 : H) : G) from (Subgroup.coe_pow _ y 3).symm]
    exact hy3
  have hx3 : x ^ 3 ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have key : x ^ 3 * u * (x ^ 3)⁻¹ = g ^ 3 * u * (g ^ 3)⁻¹ := by
      have h1 := hact u hu
      have h2 := hact _ (hgU u hu)
      have h3 := hact _ (hgU _ (hgU u hu))
      calc x ^ 3 * u * (x ^ 3)⁻¹ = x * (x * (x * u * x⁻¹) * x⁻¹) * x⁻¹ := by
            rw [pow_three]
            group
        _ = g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ := by rw [h1, h2, h3]
        _ = g ^ 3 * u * (g ^ 3)⁻¹ := by
            rw [pow_three]
            group
    have hc := Subgroup.mem_centralizer_iff.mp hg3 u hu
    have h4 : x ^ 3 * u * (x ^ 3)⁻¹ = u := by
      rw [key, ← hc]
      group
    calc u * x ^ 3 = x ^ 3 * u * (x ^ 3)⁻¹ * x ^ 3 := by rw [h4]
      _ = x ^ 3 * u := by group
  have hxNT : x ∈ Subgroup.normalizer (T : Set G) := by
    rw [hTeq]
    exact modelBase_normalizer_le_modelT_normalizer n (by omega) S e hxN
  have hxCT : x ∉ Subgroup.centralizer (T : Set G) := by
    intro hx
    apply hxC
    rw [← modelBaseNormalizer_inter_modelTCentralizer n (by omega) S e]
    exact ⟨hxN, hTeq ▸ hx⟩
  have hx3T : x ^ 3 ∈ Subgroup.centralizer (T : Set G) := Subgroup.centralizer_le hTU hx3
  have hx'N : (⟨x, hxX⟩ : X) ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTX]
    exact hxNT
  have hx'C : (⟨x, hxX⟩ : X) ∉ Subgroup.centralizer ((T.subgroupOf X : Subgroup X) : Set X) := by
    rw [centralizer_subgroupOf hTX]
    exact hxCT
  have hx'3 : (⟨x, hxX⟩ : X) ^ 3 ∈
      Subgroup.centralizer ((T.subgroupOf X : Subgroup X) : Set X) := by
    rw [centralizer_subgroupOf hTX, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hx3T
  exact three_dvd_automizerIndex_of_mem (T.subgroupOf X) hx'N hx'C hx'3

end CFSG.Wreathed.OriginalAllPrime
