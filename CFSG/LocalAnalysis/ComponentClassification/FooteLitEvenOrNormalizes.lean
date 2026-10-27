module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Statement
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndPair
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSec4KnownInputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Pair

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_normalizer_conjugate_of_generation
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hGen : FooteL2FourgroupGeneration)
    (htype : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ p ^ f ≠ 9 ∧
      Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p f)
    {M : Subgroup G} (hM : IsFooteM L M) {g : G} {E : Subgroup G}
    (hE : E ≤ coreActionKernel (conjugate M g) ⊓ normalizer (M : Set G))
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8)
    (hEC : ∀ x ∈ E, x ∈ coreActionKernel M → x = 1) :
    M ≤ normalizer (conjugate M g : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM' := isFooteM_conjugate h hM g
  set N := normalizer (M : Set G) with hN
  set Ng := normalizer (conjugate M g : Set G) with hNg
  set O := oddCoreIn M with hO
  have hEN : E ≤ N := hE.trans inf_le_right
  have hECg : E ≤ coreActionKernel (conjugate M g) := hE.trans inf_le_left
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hE2 ha hb
  have hNX : ∀ X : Subgroup G, X ≤ E → 4 ≤ Nat.card X → normalizer (X : Set G) ≤ Ng := by
    intro X hXE hX4
    obtain ⟨W, hW, hWX⟩ := exists_isKleinFour_le (fun x hx => hE2 x (hXE hx)) hX4
    exact foote_cor_4_8_iv h h47 hST hM' (hXE.trans hECg) hW hWX
  have hOle : O ≤ Ng := by
    refine le_of_forall_hyperplane_inf_centralizer_le
      ⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩ hE2 ?_
      (fun x hx => mem_normalizer_oddCoreIn (hEN hx)) (odd_card_oddCoreIn M) ?_
    · intro hbot
      rw [hbot, card_bot] at hE8
      omega
    · intro B hBE hB
      refine inf_le_right.trans (le_trans ?_ (hNX B hBE (by omega)))
      intro x hx
      exact mem_normalizer_of_forall_commute fun u hu => (mem_centralizer_iff.mp hx u hu)
  set T := (⨆ (X : Subgroup G) (_ : X ≤ E) (_ : 4 ≤ Nat.card X), normalizer (X : Set G)) ⊔ O
    with hT
  have hTNg : T ≤ Ng := sup_le (iSup₂_le fun X hXE => iSup_le fun hX4 => hNX X hXE hX4) hOle
  refine le_trans ?_ hTNg
  have hOM : O ≤ M := map_subtype_le _
  have hON : O ≤ N := hOM.trans le_normalizer
  set ON := O.subgroupOf N with hONdef
  have hONn : ON.Normal :=
    (normal_subgroupOf_iff_le_normalizer hON).mpr fun x hx => mem_normalizer_oddCoreIn hx
  set q := QuotientGroup.mk' ON with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective ON
  have hONodd : Odd (Nat.card ON) := by
    rw [hONdef, Nat.card_congr (subgroupOfEquivOfLe hON).toEquiv]
    exact odd_card_oddCoreIn M
  have hqker : ∀ n : ↥N, q n = 1 ↔ (n : G) ∈ O := fun n => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  set S := (M.subgroupOf N).map q with hS
  have hSn : S.Normal :=
    ((normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl).map q hqs
  obtain ⟨-, ⟨ε⟩⟩ := hM.quotient h
  set φ : ↥M →* ↥N ⧸ ON := q.comp (Subgroup.inclusion (le_normalizer : M ≤ N)) with hφ
  have hker : φ.ker = pPrimeCore 2 ↥M := by
    ext m
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hqker, mem_pPrimeCore_iff_mem_oddCoreIn]
    rfl
  have hrange : φ.range = S := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  let eS : ↥S ≃* L ⧸ Open.fusionZStar L :=
    (MulEquiv.subgroupCongr hrange).symm.trans ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans ε))
  obtain ⟨p, f, hp, hp2, hf, hpf, hpf9, hlie⟩ := htype
  have hlieS : Blueprint.LieModel ↥S .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv eS.symm hlie
  have hqE : ∀ x : ↥N, (x : G) ∈ E → q x = 1 → x = 1 := by
    intro x hxE hx1
    have hxO : (x : G) ∈ O := (hqker x).mp hx1
    have h1 : orderOf (x : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (hE2 _ hxE)
    have h2 : orderOf (x : G) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    have h3 : orderOf (x : G) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr (odd_card_oddCoreIn M)) h1 h2
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  set Ebar := (E.subgroupOf N).map q with hEbar
  have hEinj : Function.Injective (q.comp (E.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subtype.ext (hqE x x.2 hx)
  have hErange : (q.comp (E.subgroupOf N).subtype).range = Ebar := by
    rw [MonoidHom.range_comp, range_subtype]
  have hEbar8 : Nat.card Ebar = 8 := by
    rw [← hErange, ← Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv, ← hE8]
    exact Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv
  have hEbar2 : ∀ e ∈ Ebar, e ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE2 _ hx)
    rw [← map_pow, hx2, map_one]
  have hEbarC : Ebar ⊓ centralizer (S : Set (↥N ⧸ ON)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hxE, rfl⟩, hxS⟩
    rw [mem_bot]
    have hxC : (x : G) ∈ coreActionKernel M := by
      refine mem_coreActionKernel.mpr ⟨x.2, fun j hj => ?_⟩
      have hjS : q ⟨j, le_normalizer hj⟩ ∈ S := ⟨⟨j, le_normalizer hj⟩, hj, rfl⟩
      have h1 := mem_centralizer_iff.mp hxS _ hjS
      have h2 : q ((⟨j, le_normalizer hj⟩ : ↥N)⁻¹ * x⁻¹ * ⟨j, le_normalizer hj⟩ * x) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc (q ⟨j, le_normalizer hj⟩)⁻¹ * (q x)⁻¹ * q ⟨j, le_normalizer hj⟩ * q x
            = (q ⟨j, le_normalizer hj⟩)⁻¹ * (q x)⁻¹ * (q ⟨j, le_normalizer hj⟩ * q x) := by
              group
          _ = (q ⟨j, le_normalizer hj⟩)⁻¹ * (q x)⁻¹ * (q x * q ⟨j, le_normalizer hj⟩) := by
              rw [h1]
          _ = 1 := by group
      exact (hqker _).mp h2
    have hx1 : x = 1 := Subtype.ext (hEC _ hxE hxC)
    rw [hx1, map_one]
  have hgen := hGen _ S hSn ⟨p, f, hp, hp2, hf, hpf, hpf9, hlieS⟩ Ebar hEbar2 hEbar8 hEbarC
  have hle : (⨆ (X : Subgroup (↥N ⧸ ON)) (_ : X ≤ Ebar) (_ : 4 ≤ Nat.card X),
      normalizer (X : Set (↥N ⧸ ON))) ≤ (T.subgroupOf N).map q := by
    refine iSup₂_le fun X hXE => iSup_le fun hX4 => ?_
    set X₀ := X.comap q ⊓ E.subgroupOf N with hX₀
    have hX₀X : X₀.map q = X := by
      apply le_antisymm
      · exact (map_mono inf_le_left).trans (map_comap_le q X)
      · intro x hx
        obtain ⟨e, he, rfl⟩ := mem_map.mp (hXE hx)
        exact mem_map_of_mem q (mem_inf.mpr ⟨hx, he⟩)
    have hX₀inj : Function.Injective (q.comp X₀.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      exact Subtype.ext (hqE x (mem_inf.mp x.2).2 hx)
    have hX₀card : Nat.card X₀ = Nat.card X := by
      have hr : (q.comp X₀.subtype).range = X := by
        rw [MonoidHom.range_comp, range_subtype, hX₀X]
      rw [← hr]
      exact Nat.card_congr (MonoidHom.ofInjective hX₀inj).toEquiv
    have hX₀p : IsPGroup 2 X₀ := by
      have h8 : Nat.card X₀ ∣ 2 ^ 3 := by
        rw [hX₀card, show (2 : ℕ) ^ 3 = 8 by norm_num, ← hEbar8]
        exact card_dvd_of_le hXE
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h8
      exact IsPGroup.of_card hk
    have : Fact (IsPGroup 2 ↥X₀) := ⟨hX₀p⟩
    have hnorm := CFSG.normalizer_map_quotient_eq_map_normalizer 2 X₀ ON hONn
      (Nat.coprime_two_left.mpr hONodd)
    rw [← hX₀X]
    refine (le_of_eq hnorm).trans (map_mono fun n hn => ?_)
    show (n : G) ∈ T
    apply mem_sup_left
    have hX₀E : X₀.map N.subtype ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_inf.mp hx).2
    have hX₀4 : 4 ≤ Nat.card (X₀.map N.subtype) := by
      rw [card_map_of_injective N.subtype_injective, hX₀card]
      exact hX4
    exact mem_iSup_of_mem (X₀.map N.subtype) (mem_iSup_of_mem hX₀E (mem_iSup_of_mem hX₀4
      (le_normalizer_map N.subtype (mem_map_of_mem _ hn))))
  intro m hm
  have hmS : q ⟨m, le_normalizer hm⟩ ∈ S := ⟨⟨m, le_normalizer hm⟩, hm, rfl⟩
  obtain ⟨t, htT, hqt⟩ := mem_map.mp (hle (hgen hmS))
  have h1 : q ((⟨m, le_normalizer hm⟩ : ↥N) * t⁻¹) = 1 := by
    rw [map_mul, map_inv, hqt, mul_inv_cancel]
  have h2 : m * (t : G)⁻¹ ∈ O := (hqker _).mp h1
  rw [show m = m * (t : G)⁻¹ * t by group]
  exact mul_mem (mem_sup_right h2) htT

theorem footeEvenOrNormalizes
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hGen : FooteL2FourgroupGeneration) (h410 : FooteLemma410Statement) {M : Subgroup G}
    (hM : IsFooteM L M) : FooteEvenOrNormalizes M := by
  intro g E hE hE2 hE8
  by_cases hinv : ∃ x ∈ coreActionKernel M ⊓ coreActionKernel (conjugate M g), orderOf x = 2
  · exact Or.inl hinv
  have hEC : ∀ x ∈ E, x ∈ coreActionKernel M → x = 1 := by
    intro x hxE hxC
    by_contra hx1
    exact hinv ⟨x, mem_inf.mpr ⟨hxC, (mem_inf.mp (hE hxE)).1⟩,
      orderOf_eq_prime (hE2 x hxE) hx1⟩
  rcases h.footeFamilyType with hA7 | ⟨p, f, hp, hp2, hf, hpf, hlie⟩
  · exact h410 G L h (Or.inl hA7) M hM g E hE hE2 hE8
  · by_cases h9 : p ^ f = 9
    · exact h410 G L h (Or.inr ⟨p, f, hp, h9, hlie⟩) M hM g E hE hE2 hE8
    · exact Or.inr (le_normalizer_conjugate_of_generation h h47 hST hGen
        ⟨p, f, hp, hp2, hf, hpf, h9, hlie⟩ hM hE hE2 hE8 hEC)

end CFSG.ComponentClassification.FooteLit
