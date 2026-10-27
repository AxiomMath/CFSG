module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Sylow
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Torus
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Pilot
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

set_option linter.unusedSectionVars false


theorem exists_fixed_subfield (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq2 : 2 ≤ q) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : Algebra k K), Nat.card k = q ∧
      ringChar k = ringChar K ∧ ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hKcard⟩ := FiniteField.card K (ringChar K)
  have hpr' : Fact (ringChar K).Prime := ⟨hpr⟩
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hKcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨i, -, hqi⟩ := (Nat.dvd_prime_pow hpr).1 hdvd
  have hi : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hqi
    omega
  let k := GaloisField (ringChar K) i
  have hkcard : Nat.card (GaloisField (ringChar K) i) = q := by
    rw [GaloisField.card (ringChar K) i hi, hqi]
  have hK' : Nat.card K = (ringChar K ^ i) ^ 2 := by
    rw [hK, hqi]
  obtain ⟨ιk⟩ := nonempty_ringHom_of_card_sq (ℓ := ringChar K) (f := i) (hkcard.trans hqi)
    (by rw [hqi] at hK; exact hK)
  letI : Algebra (GaloisField (ringChar K) i) K := ιk.toAlgebra
  refine ⟨GaloisField (ringChar K) i, inferInstance, inferInstance, inferInstance, hkcard, ?_, ?_⟩
  · exact ringChar.eq _ _
  · intro c
    rw [hσ]
    have hc : c ^ q = c := by
      rw [← hkcard]
      haveI : Fintype (GaloisField (ringChar K) i) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    rw [← map_pow, hc]

theorem exists_ord_three_units (k : Type) [Field k] [Finite k] (hq : Nat.card k % 3 = 1) :
    ∃ ω : kˣ, orderOf ω = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype k := Fintype.ofFinite k
  have hcard : Nat.card kˣ = Nat.card k - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, Nat.card_eq_fintype_card]
  have h3 : 3 ∣ Nat.card kˣ := by
    rw [hcard]
    omega
  exact exists_prime_orderOf_dvd_card' 3 h3

theorem not_normalizesRIn_of_map {r : ℕ} {F M : Type*} [Group F] [Group M]
    {E₀ : Subgroup M} (hn : ¬ NormalizesRIn r E₀) (g : M) (ι : F →* M) (E₃ : Subgroup F)
    (hι : Function.Injective ι) (hE₃ : E₃.map ι = E₀.map (MulAut.conj g).toMonoidHom) :
    ¬ NormalizesRIn r E₃ := by
  rintro ⟨R₃, hR1, hRp, hRn⟩
  apply hn
  set R₆ : Subgroup M := R₃.map ι with hR₆
  have hR₆1 : R₆ ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R₃ hι).mp h)
  have hR₆p : IsPGroup r R₆ :=
    hRp.of_surjective (ι.subgroupMap R₃) (ι.subgroupMap_surjective R₃)
  have hnorm₆ : E₃.map ι ≤ Subgroup.normalizer (R₆ : Set M) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_conj_eq_iff_mem_normalizer]
    have hxn := (map_conj_eq_iff_mem_normalizer R₃ x).2 (hRn hx)
    have hcomp : (MulAut.conj (ι x)).toMonoidHom.comp ι = ι.comp (MulAut.conj x).toMonoidHom := by
      ext z
      simp [MulAut.conj_apply]
    rw [hR₆, Subgroup.map_map, hcomp, ← Subgroup.map_map, hxn]
  refine ⟨R₆.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · exact fun h =>
      hR₆1 ((Subgroup.map_eq_bot_iff_of_injective R₆ (MulAut.conj g⁻¹).injective).mp h)
  · exact hR₆p.of_surjective ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap R₆)
      ((MulAut.conj g⁻¹).toMonoidHom.subgroupMap_surjective R₆)
  · intro y hy
    rw [mem_normalizer_map_conj_iff, inv_inv]
    exact hnorm₆ (hE₃ ▸ Subgroup.mem_map_of_mem _ hy)

theorem exists_conj_zSplit_mem (hNR : LangPlaneKillsRoot .F4) (hP : F4PureSplit)
    (k : Type) [Field k] [Finite k] (hq : Nat.card k % 3 = 1) (E₃ : Subgroup (adjointGroup .F4 k))
    (hexp : ∀ x ∈ E₃, x ^ 3 = 1) (hcard : Nat.card E₃ = 3 ^ 2) (hn : ¬ NormalizesRIn (ringChar k) E₃) :
    ∃ ω : kˣ, orderOf ω = 3 ∧ ∃ g : adjointGroup .F4 k,
      zSplit k ω ∈ E₃.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨ω, hω⟩ := exists_ord_three_units k hq
  have hn3 : ¬ 3 ∣ Nat.card k := by omega
  have hLT : LangToralOrParabolic .F4 := langToralOrParabolic_of_langToralPlane
    CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three
  rcases hLT k hn3 E₃ hexp hcard with hD | hnorm
  · let D : LangPlaneData .F4 k E₃ := hD.some
    have hkills : ∀ α, IsRoot .F4 α → ¬ D.Kills α := by
      intro α hα hk
      obtain ⟨u, hu1, hun, hcomm⟩ := hNR k E₃ D α hα hk
      exact hn (normalizesRNative_of_unip ⟨u, hu1, hun, hcomm⟩)
    have hE : ∃ e ∈ E₃, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : E₃ = ⊥ := (Subgroup.eq_bot_iff_forall E₃).2 hcon
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    obtain ⟨e, he, he1⟩ := hE
    obtain ⟨g, hg⟩ := hP k hq ω hω E₃ hexp hcard D hkills e he he1
    exact ⟨ω, hω, g, e, he, hg⟩
  · exact absurd hnorm hn

theorem twE6HighInF4_one_of (hNR : LangPlaneKillsRoot .F4) (hP : F4PureSplit) :
    TwE6HighInF4 1 := by
  intro q K _ _ σ hK hσ hq E₀ hexp hcard hn
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    have : Nat.card K ≤ 1 := by
      rw [hK]
      interval_cases q <;> norm_num
    omega
  obtain ⟨k, hkF, hkfin, hkalg, hkq, hkchar, hfix⟩ := exists_fixed_subfield q K σ hK hσ hq2
  have hσk : ∀ c : K, σ c = c ^ Nat.card k := fun c => by rw [hkq]; exact hσ c
  have hK' : Nat.card K = (Nat.card k) ^ 2 := by rw [hkq]; exact hK
  have hq' : Nat.card k % 3 = 1 := by rw [hkq]; exact hq
  have hq2' : 2 ≤ Nat.card k := by rw [hkq]; exact hq2
  obtain ⟨g₀, hg₀⟩ := threeSubgroup_conj_into_F4 σ hσk hK' hfix hq' hq2' E₀ hexp
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  set E₃ : Subgroup (adjointGroup .F4 k) := (E₀.map (MulAut.conj g₀).toMonoidHom).comap ι with hE₃def
  have hE₃ : E₃.map ι = E₀.map (MulAut.conj g₀).toMonoidHom := Subgroup.map_comap_eq_self hg₀
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hx)
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map ι) = Nat.card E₃ := Subgroup.card_map_of_injective hι
    have h2 : Nat.card (E₀.map (MulAut.conj g₀).toMonoidHom) = Nat.card E₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective
    rw [← h1, hE₃, h2, hcard]
  have hn3 : ¬ NormalizesRIn (ringChar k) E₃ := by
    rw [hkchar]
    exact not_normalizesRIn_of_map hn g₀ ι E₃ hι hE₃
  obtain ⟨ω, hω, g₁, hg₁⟩ := exists_conj_zSplit_mem hNR hP k hq' E₃ hexp₃ hcardE₃ hn3
  have hzne : zSplit k ω ≠ 1 := (f4SplitFrame_of k hq' ω hω).1
  obtain ⟨z, hz, hgood⟩ := zSplit_twE6_good k K ω
  have hz1 : z ≠ 1 := by
    intro h
    apply hzne
    rw [← hz, h, map_one]
  have hιz : ι (zSplit k ω) = phiG σ hfix z := by
    rw [← hz, hιdef]
    simp
  have hrange : ι.range = (phiG σ hfix).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(e6FixedF4EquivAll k).symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e6FixedF4EquivAll k y, by simp [hιdef]⟩
  have hcl := closure_top_of_commute σ hσk hfix z hz1 hgood
  refine ⟨k, inferInstance, inferInstance, ι g₁ * g₀, ι, E₃.map (MulAut.conj g₁).toMonoidHom, hkq, hkchar,
    hι, ?_, zSplit k ω, hg₁, hzne, ?_⟩
  · rw [Subgroup.map_map]
    have hc1 : ι.comp (MulAut.conj g₁).toMonoidHom = ((MulAut.conj (ι g₁)).toMonoidHom).comp ι := by
      ext x
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [hc1, ← Subgroup.map_map, hE₃, Subgroup.map_map]
    have hc2 : ((MulAut.conj (ι g₁)).toMonoidHom).comp (MulAut.conj g₀).toMonoidHom =
        (MulAut.conj (ι g₁ * g₀)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hc2]
  · rw [hιz, hrange]
    exact hcl

end CFSG.LieType.SeitzGeneration.ExcHighThree
