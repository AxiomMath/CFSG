module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoD
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoD1

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]


omit [Finite G]
  in
theorem mem_zStarIn_of_mem_coreActionKernel {J : Subgroup G} {g : G} (hgJ : g ∈ J)
    (hgK : g ∈ coreActionKernel J) : g ∈ zStarIn J := by
  refine ⟨⟨g, hgJ⟩, GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_, rfl⟩
  have h1 := (mem_coreActionKernel.mp hgK).2 (m⁻¹ : J) (m⁻¹).2
  obtain ⟨y, hy, hyeq⟩ := h1
  have hy' : (y : G) = (m : G) * g⁻¹ * (m : G)⁻¹ * g := by
    have : (y : G) = ((m⁻¹ : J) : G)⁻¹ * g⁻¹ * ((m⁻¹ : J) : G) * g := hyeq
    rw [this]
    simp
  have h2 := (pPrimeCore_normal (p := 2) (G := J)).conj_mem y hy ⟨g, hgJ⟩
  convert h2 using 1
  apply Subtype.ext
  simp only [commutatorElement_def, coe_mul, coe_inv]
  rw [hy']
  group

omit [Finite G]
  in
theorem mem_of_isolated_gen {J S : Subgroup G} {a : G} (haS : a ∈ S) (haa : a * a = 1)
    (hcent : ∀ s ∈ S, s * a = a * s) (haK : a ∈ coreActionKernel J) {E : Subgroup G}
    (hES : E ≤ S)
    (hiso : ∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E) : a ∈ E :=
  hiso a (mem_inf.mpr ⟨haS, mem_sup_right haK⟩) haa fun e he => (hcent e (hES he)).symm

theorem two_lt_card_of_zOne_gen {J S : Subgroup G} (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (hT : IsSylowTwoIn (S ⊓ J) J) (hS2 : IsPGroup 2 S) (hSN : S ≤ normalizer (J : Set G))
    {a : G} (haS : a ∈ S) (ha2 : orderOf a = 2) (hcent : ∀ s ∈ S, s * a = a * s)
    (haK : a ∈ coreActionKernel J) {E : Subgroup G} (hES : E ≤ S)
    (hiso : ∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E)
    (hZ : S ⊓ zStarIn J = ⊥) : 2 < Nat.card ↥(E ⊓ withKernel J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha2
  have haE := mem_of_isolated_gen haS haa hcent haK hES hiso
  set T := S ⊓ J with hTdef
  have hTne : T ≠ ⊥ := by
    intro hT1
    have h64 := GrS4.sixtyFour_le_card hL hT
    rw [hT1, Subgroup.card_bot] at h64
    omega
  set P' := T ⊔ E with hP'
  have hP'2 : IsPGroup 2 P' := hS2.to_le (sup_le inf_le_left hES)
  have : Group.IsNilpotent P' := hP'2.isNilpotent
  have hTn : (T.subgroupOf P').Normal := by
    refine (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer ?_)
    intro e he
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer (hES he), hSN (hES he)⟩
  have hTne' : T.subgroupOf P' ≠ ⊥ := by
    intro h
    apply hTne
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, mem_sup_left hy⟩ : P') ∈ T.subgroupOf P' := hy
    rw [h, mem_bot] at h1
    rw [mem_bot]
    exact congrArg Subtype.val h1
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hTne'
  obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hmeet
  obtain ⟨hwT, hwZ⟩ := mem_inf.mp hw
  set K := T ⊓ centralizer (E : Set G) with hK
  have hwK : ((w : P') : G) ∈ K := by
    refine mem_inf.mpr ⟨hwT, mem_centralizer_iff.mpr fun e he => ?_⟩
    have := mem_center_iff.mp hwZ ⟨e, mem_sup_right he⟩
    exact congrArg Subtype.val this
  have hK2 : IsPGroup 2 K := hS2.to_le (inf_le_left.trans inf_le_left)
  have hKnt : Nontrivial K := by
    refine ⟨⟨⟨((w : P') : G), hwK⟩, 1, fun h => hw1 ?_⟩⟩
    have h1 := congrArg Subtype.val h
    exact Subtype.ext h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥K)).mp hK2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card_iff_nontrivial.mpr hKnt
    omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (by
    rw [hn]; exact dvd_pow_self 2 hn0)
  have hz' : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hz2 : (z : G) * (z : G) = 1 := by rw [← pow_two, ← hz', pow_orderOf_eq_one]
  obtain ⟨hzT, hzC⟩ := mem_inf.mp z.2
  have hzE : (z : G) ∈ E := hiso z (mem_inf.mpr ⟨(mem_inf.mp hzT).1,
    mem_sup_left (mem_inf.mp hzT).2⟩) hz2 fun e he => (mem_centralizer_iff.mp hzC e he).symm
  by_contra hle
  push Not at hle
  have hza : (z : G) = a := by
    have hsub : zpowers a ≤ E ⊓ withKernel J :=
      zpowers_le.mpr (mem_inf.mpr ⟨haE, mem_sup_right haK⟩)
    have hcard : Nat.card ↥(zpowers a) = 2 := by rw [Nat.card_zpowers, ha2]
    have heq := Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard]; exact hle)
    have hzA : (z : G) ∈ zpowers a := by
      rw [heq]
      exact mem_inf.mpr ⟨hzE, mem_sup_left (mem_inf.mp hzT).2⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hzA
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · exfalso
      have hz1 : (z : G) ≠ 1 := by
        intro h
        have : z = 1 := Subtype.ext h
        rw [this, orderOf_one] at hz
        omega
      apply hz1
      rw [← hk, zpow_mul, zpow_two, show a * a = 1 from haa, one_zpow]
    · rw [← hk, zpow_add, zpow_mul, zpow_two, show a * a = 1 from haa, one_zpow, one_mul,
        zpow_one]
  have haJ : a ∈ J := hza ▸ (mem_inf.mp hzT).2
  have := mem_inf.mpr ⟨haS, mem_zStarIn_of_mem_coreActionKernel haJ haK⟩
  rw [hZ, mem_bot] at this
  exact ha1 this

theorem wGroup_eq_of_not_stronglyIsolated_gen (hGW : GWTwoBalanced G) {J S W : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hT : IsSylowTwoIn (S ⊓ J) J)
    (hS2 : IsPGroup 2 S) (hSN : S ≤ normalizer (J : Set G)) {a : G} (haS : a ∈ S)
    (ha2 : orderOf a = 2) (hcent : ∀ s ∈ S, s * a = a * s) (haK : a ∈ coreActionKernel J)
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    {F : Subgroup G} (hFS : F ≤ S) (hF : IsEightGroup F)
    (hns : ∃ s ∈ S, s * s = 1 ∧ (∀ e ∈ F, s * e = e * s) ∧ s ∉ F) : wGroup F = W := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have key : ∀ n : ℕ, ∀ F : Subgroup G, F ≤ S → IsEightGroup F →
      (∃ s ∈ S, s * s = 1 ∧ (∀ e ∈ F, s * e = e * s) ∧ s ∉ F) →
      8 - Nat.card ↥(F ⊓ withKernel J) ≤ n → wGroup F = W := by
    intro n
    induction n with
    | zero =>
      intro F hFS hF _ hn
      have h1 : F ⊓ withKernel J = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [hF.2]
        omega)
      exact hWB F (le_inf hFS (h1 ▸ inf_le_right)) (hF.1.isAbelianTwoOfRank hF.2.ge)
    | succ n ih =>
      intro F hFS hF hns hn
      by_cases hle : F ≤ withKernel J
      · exact hWB F (le_inf hFS hle) (hF.1.isAbelianTwoOfRank hF.2.ge)
      have hEK : F ⊓ withKernel J ≤ F := inf_le_left
      by_cases hiso : ∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ F, s * e = e * s) → s ∈ F
      ·
        have haE := mem_of_isolated_gen haS haa hcent haK hFS hiso
        have hEC : 2 ≤ Nat.card ↥(F ⊓ coreActionKernel J) := by
          have hsub : zpowers a ≤ F ⊓ coreActionKernel J :=
            zpowers_le.mpr (mem_inf.mpr ⟨haE, haK⟩)
          have := Subgroup.card_le_of_le hsub
          rw [Nat.card_zpowers, ha2] at this
          exact this
        have hECK : Nat.card ↥(F ⊓ coreActionKernel J) ≤ Nat.card ↥(F ⊓ withKernel J) :=
          Subgroup.card_le_of_le (inf_le_inf_left _ le_sup_right)
        by_cases h2 : Nat.card ↥(F ⊓ withKernel J) ≤ 2
        · exfalso
          have hZ : S ⊓ zStarIn J ≠ ⊥ := fun hZ =>
            absurd (two_lt_card_of_zOne_gen hL hT hS2 hSN haS ha2 hcent haK hFS hiso hZ)
              (by omega)
          obtain ⟨s, hsS, hss, hsc, hsn⟩ := l34WCriterionD1Fact_of_certs G J S hJ hL hT hS2
            hSN hZ F hFS hF (by omega) hEC
          exact hsn (hiso s hsS hss hsc)
        have h4 : Nat.card ↥(F ⊓ withKernel J) = 4 := by
          have hdvd : Nat.card ↥(F ⊓ withKernel J) ∣ 8 := by
            have := Subgroup.card_dvd_of_le hEK
            rwa [hF.2] at this
          have hne : Nat.card ↥(F ⊓ withKernel J) ≠ 8 := fun h8 => hle (by
            have := Subgroup.eq_of_le_of_card_ge hEK (by rw [h8, hF.2])
            exact this ▸ inf_le_right)
          obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
            (show Nat.card ↥(F ⊓ withKernel J) ∣ 2 ^ 3 by norm_num; exact hdvd)
          interval_cases k <;> simp only [Nat.reducePow] at hk' <;> omega
        obtain ⟨-, hnext⟩ := l34WCriterionDFact_of_certs G J S hJ hL hT hS2 hSN F hFS hF h4
          hEC hiso
        obtain ⟨s, hsS, hss, hsc, hsn⟩ := hns
        obtain ⟨s', hs'S, hs's, hs'c, hs'n⟩ := hnext s hsS hss hsc hsn
        set E₁ := F ⊓ withKernel J with hE₁
        have hE₁e : IsElemTwo E₁ := hF.1.mono hEK
        have hsE₁ : s ∉ E₁ := fun h => hsn (hEK h)
        obtain ⟨hE', hE'c⟩ := GrS4.isElemTwo_sup_zpowers hE₁e hss hsE₁
          (fun e he => (hsc e (hEK he)).symm)
        have hs'E₁ : s' ∉ E₁ := fun h => hs'n (mem_sup_left h)
        obtain ⟨hF', hF'c⟩ := GrS4.isElemTwo_sup_zpowers hE₁e hs's hs'E₁
          (fun e he => (hs'c e (mem_sup_left he)).symm)
        have hE'8 : 8 ≤ Nat.card ↥(E₁ ⊔ zpowers s) := by omega
        have hF'8 : 8 ≤ Nat.card ↥(E₁ ⊔ zpowers s') := by omega
        have hFS₁ : E₁ ⊔ zpowers s' ≤ S ⊓ withKernel J :=
          sup_le (le_inf (hEK.trans hFS) inf_le_right) (zpowers_le.mpr hs'S)
        have hEE' : ∀ u ∈ F, ∀ v ∈ E₁ ⊔ zpowers s, u * v = v * u := by
          intro u hu v hv
          have hle' : E₁ ⊔ zpowers s ≤ centralizer ({u} : Set G) := by
            refine sup_le (fun w hw => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr ?_)
            · exact hF.1.1 w (hEK hw) u hu
            · exact mem_centralizer_singleton_iff.mpr (hsc u hu)
          exact (mem_centralizer_singleton_iff.mp (hle' hv)).symm
        have hE'F : ∀ u ∈ E₁ ⊔ zpowers s, ∀ v ∈ E₁ ⊔ zpowers s', u * v = v * u := by
          intro u hu v hv
          have hle' : E₁ ⊔ zpowers s' ≤ centralizer ({u} : Set G) := by
            refine sup_le (fun w hw => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr ?_)
            · exact hE'.1 w (mem_sup_left hw) u hu
            · exact mem_centralizer_singleton_iff.mpr (hs'c u hu)
          exact (mem_centralizer_singleton_iff.mp (hle' hv)).symm
        rw [wGroup_eq_of_commute hGW (hF.1.isAbelianTwoOfRank hF.2.ge)
          (hE'.isAbelianTwoOfRank hE'8) hEE', wGroup_eq_of_commute hGW
          (hE'.isAbelianTwoOfRank hE'8) (hF'.isAbelianTwoOfRank hF'8) hE'F]
        exact hWB _ hFS₁ (hF'.isAbelianTwoOfRank hF'8)
      ·
        push Not at hiso
        obtain ⟨s, hsS, hss, hsF, hsn⟩ := hiso
        set F₁ : Subgroup G := F ⊓ withKernel J with hF₁def
        have hF₁K : F₁ ≤ withKernel J := inf_le_right
        have hF₁ : IsElemTwo F₁ := hF.1.mono hEK
        have hsF₁ : s ∉ F₁ := fun h => hsn (hEK h)
        obtain ⟨-, hA₀c⟩ := GrS4.isElemTwo_sup_zpowers hF₁ hss hsF₁
          (fun e he => (hsF e (hEK he)).symm)
        obtain ⟨hB, hBc⟩ := GrS4.isElemTwo_sup_zpowers hF.1 hss hsn (fun e he => (hsF e he).symm)
        have hF₁lt : Nat.card F₁ < 8 := by
          have h1 : Nat.card F₁ ≤ 8 := hF.2 ▸ Subgroup.card_le_of_le hEK
          refine lt_of_le_of_ne h1 fun h => hle ?_
          have h2 : F₁ = F := Subgroup.eq_of_le_of_card_ge hEK (by rw [h, hF.2])
          exact h2 ▸ hF₁K
        have hF₁4 := GrS4.card_le_four_of_lt_eight hF₁ hF₁lt
        have hpos : 0 < Nat.card F₁ := Nat.card_pos
        obtain ⟨F', h1, h2, h3, h4⟩ := GrS4.exists_eight_between 8 (A := F₁ ⊔ zpowers s)
          (B := F ⊔ zpowers s) (by omega) (sup_le_sup_right hEK _) hB (by omega)
          (by rw [hBc, hF.2]; omega)
        have hF'S : F' ≤ S := h2.trans (sup_le hFS (zpowers_le.mpr hsS.1))
        have hcard : Nat.card F₁ < Nat.card ↥(F' ⊓ withKernel J) := by
          have hc := Subgroup.card_le_of_le
            (le_inf h1 (sup_le hF₁K (zpowers_le.mpr hsS.2)) :
              F₁ ⊔ zpowers s ≤ F' ⊓ withKernel J)
          omega
        have hmeas : 8 - Nat.card ↥(F' ⊓ withKernel J) ≤ n := by omega
        have hFF' : ¬ F ≤ F' := fun hFF => by
          have heq : F = F' := Subgroup.eq_of_le_of_card_ge hFF (by rw [hF.2, h4])
          rw [← heq] at hcard
          exact absurd hcard (lt_irrefl _)
        have hns' : ∃ t ∈ S, t * t = 1 ∧ (∀ e ∈ F', t * e = e * t) ∧ t ∉ F' := by
          obtain ⟨t, htF, htF'⟩ : ∃ t ∈ F, t ∉ F' := by
            by_contra h
            push Not at h
            exact hFF' h
          exact ⟨t, hFS htF, hF.1.2 t htF,
            fun e he => hB.1 t ((le_sup_left : F ≤ F ⊔ zpowers s) htF) e (h2 he), htF'⟩
        rw [← ih F' hF'S ⟨h3, h4⟩ hns' hmeas]
        exact wGroup_eq_of_commute hGW (hF.1.isAbelianTwoOfRank hF.2.ge)
          (h3.isAbelianTwoOfRank h4.ge)
          (fun u hu v hv => hB.1 u ((le_sup_left : F ≤ F ⊔ zpowers s) hu) v (h2 hv))
  exact key 8 F hFS hF hns (by omega)

end CFSG.ComponentClassification.GrSLit.GrS5S
