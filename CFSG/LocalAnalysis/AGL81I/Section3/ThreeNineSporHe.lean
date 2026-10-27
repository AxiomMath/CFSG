module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporHe

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open Subgroup

private theorem exists_maximal_of_mulEquiv' {A A' : Type*} [Group A] [Group A'] {n : ℕ}
    (e : A ≃* A') (h : ∃ R : Subgroup A, Nat.card R = n ∧ ∀ Y : Subgroup A, R ≤ Y → Y = R ∨ Y = ⊤) :
    ∃ R : Subgroup A', Nat.card R = n ∧ ∀ Y : Subgroup A', R ≤ Y → Y = R ∨ Y = ⊤ := by
  obtain ⟨R, hRc, hRmax⟩ := h
  refine ⟨R.map e.toMonoidHom, by rw [card_map_of_injective e.injective, hRc], fun Y hY => ?_⟩
  have hY' : R ≤ Y.map e.symm.toMonoidHom := fun r hr => ⟨e r, hY ⟨r, hr, rfl⟩, by simp⟩
  rcases hRmax _ hY' with h1 | h1
  · left
    rw [← h1, map_map]
    convert (map_id Y).symm
    ext x
    simp
  · right
    rw [eq_top_iff]
    intro x _
    have : e.symm x ∈ Y.map e.symm.toMonoidHom := h1 ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x from e.symm.injective hyx] at hy

theorem normalizer_sylow_seven_he
    {L : Type*} [Group L] [Finite L] (e : L ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)
    (T : Sylow 7 L) :
    Nat.card (normalizer ((T : Subgroup L) : Set L)) = 6174 ∧
      ∀ H : Subgroup L, normalizer ((T : Subgroup L) : Set L) ≤ H →
        H = normalizer ((T : Subgroup L) : Set L) ∨ H = ⊤ := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : IsSimpleGroup L := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e
  have hLc : Nat.card L = 4030387200 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He
  have hN := exists_maximal_of_mulEquiv' (A := ↥CFSG.Sporadic.He.J)
    (A' := CFSG.Blueprint.NativeSporadic.He) CFSG.Sporadic.He.heEquivJ.symm
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.heSeven_maximal_J
  obtain ⟨R, hRc, hRmax⟩ := exists_maximal_of_mulEquiv'
    (A := CFSG.Blueprint.NativeSporadic.Carrier .He) (A' := L) e.symm hN
  obtain ⟨P⟩ : Nonempty (Sylow 7 R) := inferInstance
  have hPc : Nat.card (P : Subgroup R) = 7 ^ 3 := by
    rw [Sylow.card_eq_multiplicity P, hRc,
      factorization_eq_of_pow_dvd (e := 3) Nat.prime_seven (by norm_num) (by norm_num)
      (by norm_num)]
  have hone : Nat.card (Sylow 7 R) = 1 := by
    have hidx : (P : Subgroup R).index = 18 := by
      have h1 := (P : Subgroup R).card_mul_index
      rw [hPc, hRc] at h1
      omega
    have hdvd : Nat.card (Sylow 7 R) ∣ 18 := hidx ▸ Sylow.card_dvd_index P
    have hmod : Nat.card (Sylow 7 R) % 7 = 1 := card_sylow_modEq_one (p := 7) (G := R)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 7 R) = m at hdvd hmod hle ⊢
    interval_cases m <;> omega
  have hPn : (P : Subgroup R).Normal := by
    have : Subsingleton (Sylow 7 R) := (Nat.card_eq_one_iff_unique.mp hone).1
    exact Sylow.normal_of_subsingleton P
  set T₀ : Subgroup L := (P : Subgroup R).map R.subtype with hT₀
  have hT₀c : Nat.card T₀ = 7 ^ 3 := by
    rw [hT₀, card_map_of_injective R.subtype_injective, hPc]
  have hRN : R ≤ normalizer (T₀ : Set L) := by
    have hsub : T₀.subgroupOf R = (P : Subgroup R) := by
      rw [hT₀]
      exact comap_map_eq_self_of_injective R.subtype_injective _
    have : (T₀.subgroupOf R).Normal := by rw [hsub]; exact hPn
    exact le_normalizer_of_normal_subgroupOf (map_subtype_le _)
  have hNtop : normalizer (T₀ : Set L) ≠ ⊤ := by
    intro htop
    have : T₀.Normal := normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T₀ with h | h
    · rw [h, card_bot] at hT₀c
      norm_num at hT₀c
    · rw [h, card_top, hLc] at hT₀c
      norm_num at hT₀c
  have hNR : normalizer (T₀ : Set L) = R := ((hRmax _ hRN).resolve_right hNtop)
  have hT₀idx : ¬ 7 ∣ (T₀.subgroupOf ⊤).index := by
    change ¬ 7 ∣ T₀.relIndex ⊤
    rw [relIndex_top_right]
    have h1 := T₀.card_mul_index
    rw [hT₀c, hLc] at h1
    have h2 : T₀.index = 11750400 := by omega
    rw [h2]
    norm_num
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq (L := ⊤) le_top
    le_top (IsPGroup.of_card hT₀c) T.isPGroup' hT₀idx
    (by rw [Sylow.card_eq_multiplicity T, hLc, hT₀c,
      factorization_eq_of_pow_dvd (e := 3) Nat.prime_seven (by norm_num) (by norm_num)
      (by norm_num)])
  have hNT : normalizer ((T : Subgroup L) : Set L) = R.map (MulAut.conj l).toMonoidHom := by
    rw [← hl, ← map_equiv_normalizer_eq, hNR]
  rw [hNT]
  refine ⟨by rw [card_map_of_injective (MulAut.conj l).injective, hRc], fun H hH => ?_⟩
  have hle : R ≤ H.map (MulAut.conj l).symm.toMonoidHom := by
    intro r hr
    exact ⟨MulAut.conj l r, hH ⟨r, hr, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, MulAut.conj_apply]; group⟩
  rcases hRmax _ hle with h1 | h1
  · left
    rw [← h1, map_map]
    convert (map_id H).symm
    ext x
    simp
  · right
    rw [eq_top_iff]
    intro x _
    have : (MulAut.conj l).symm x ∈ H.map (MulAut.conj l).symm.toMonoidHom := h1 ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x from (MulAut.conj l).symm.injective hyx] at hy

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_he
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 7 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .He) : False := by
  obtain ⟨e⟩ := hs
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e
  have hcK : Nat.card ↥K = 4030387200 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) ≤ 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.AT_He_Schreier.1
  have hO0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hdp := h.d_prime
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    have := Nat.le_of_dvd hO0 hd
    have := hdp.two_le
    exact h.d_ne_two (by omega)
  obtain ⟨S, hS⟩ := h.exists_sylow_subgroupOf_eq_normalizer hZ
    (fun h7 => by have := Nat.le_of_dvd hO0 h7; omega)
    (fun S => (SporCent.normalizer_sylow_seven_he e S).2)
  obtain ⟨hd1, hd2⟩ := h.dvd_card_of_subgroupOf_le (h.D_le_K_of_not_dvd hZ houtd) hS.le
  rw [(SporCent.normalizer_sylow_seven_he e S).1] at hd1 hd2
  have hd3 : d = 3 := by
    have h' : d ∣ 2 * (3 ^ 2 * 7 ^ 3) := by norm_num; exact hd1
    rcases hdp.dvd_mul.1 h' with h2 | h37
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 h2) h.d_ne_two
    · rcases hdp.dvd_mul.1 h37 with h3 | h7
      · exact (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_three).1 (hdp.dvd_of_dvd_pow h3)
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_seven).1 (hdp.dvd_of_dvd_pow h7))
          h.d_ne
  subst hd3
  rw [hcK, SporCent.factorization_eq_of_pow_dvd (e := 3) Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num)] at hd2
  norm_num at hd2

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
