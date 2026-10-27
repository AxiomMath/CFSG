module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.CentralLift
public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma126

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def NoncentralWitness (K : Type) [Group K] (q k : ℕ) : Prop :=
  ∃ E : Subgroup K, IsElemAbelian q E ∧ Nat.card E = q ^ k ∧
    ∃ T : Subgroup K, IsPGroup 2 T ∧ ¬ T ≤ Subgroup.center K ∧
      E ≤ Subgroup.normalizer (T : Set K)

theorem noncentralWitness_three {K : Type} [Group K] [Finite K] {q k : ℕ} (hq : q.Prime)
    (hk : 3 ≤ k) (h : NoncentralWitness K q k) : NoncentralWitness K q 3 := by
  obtain ⟨E, hE, hEc, T, hT2, hTnc, hET⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd : q ^ 3 ∣ Nat.card E := by
    rw [hEc]
    exact pow_dvd_pow q hk
  obtain ⟨E', hE'card, -, hE'E⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hq (H := ⊥) (L := E) (n := 3)
      (by simp) hdvd bot_le
  exact ⟨E', isElemAbelian_mono hE hE'E, hE'card, T, hT2, hTnc, hE'E.trans hET⟩

theorem exists_isLabel_of_hasLabel {K : Type} [Group K] (h : HasLabel K (fun _ => True)) :
    ∃ lab, Rk2IsLabel K lab := by
  obtain ⟨lab, -, hlab⟩ := rk2_exists_label h
  exact ⟨lab, hlab⟩

theorem exists_two_subgroup_map_eq_of_cover {Y R : Type} [Group Y] [Finite Y] [Group R]
    {φ : Y →* R} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {U : Subgroup R} (hU2 : IsPGroup 2 U) {S : Subgroup Y}
    (hSU : ∀ x ∈ S, ∀ u ∈ U, φ x * u * (φ x)⁻¹ ∈ U) :
    ∃ T : Subgroup Y, IsPGroup 2 T ∧ T.map φ = U ∧ S ≤ Subgroup.normalizer (T : Set Y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup Y := U.comap φ with hH
  have hZH : φ.ker ≤ H := by
    intro z hz
    rw [hH, Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]
    exact U.one_mem
  have hZc : ∀ z ∈ φ.ker, ∀ g ∈ H, z * g = g * z := by
    intro z hz g _
    exact (Subgroup.mem_center_iff.1 (hker hz) g).symm
  have hq : ∀ g ∈ H, ∃ n : ℕ, g ^ 2 ^ n ∈ φ.ker := by
    intro g hg
    obtain ⟨n, hn⟩ := hU2 (⟨φ g, hg⟩ : U)
    refine ⟨n, MonoidHom.mem_ker.2 ?_⟩
    rw [map_pow]
    exact congrArg Subtype.val hn
  obtain ⟨T, hTH, hT2, hHT, hchar⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S12.exists_char_sylow_two hZH hZc hq
  have hmapH : H.map φ = U := by
    rw [hH]
    exact Subgroup.map_comap_eq_self_of_surjective hφ U
  have hTmap : T.map φ = U := by
    refine le_antisymm ?_ ?_
    · rw [← hmapH]
      exact Subgroup.map_mono hTH
    · rw [← hmapH]
      calc H.map φ ≤ (T ⊔ φ.ker).map φ := Subgroup.map_mono hHT
        _ = T.map φ ⊔ (φ.ker).map φ := Subgroup.map_sup T φ.ker φ
        _ = T.map φ := by
            have hkerbot : (φ.ker).map φ = ⊥ := by
              rw [Subgroup.map_eq_bot_iff φ.ker (f := φ)]
            rw [hkerbot, sup_bot_eq]
  have hSH : S ≤ Subgroup.normalizer (H : Set Y) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs y hy
    rw [hH, Subgroup.mem_comap] at hy ⊢
    rw [map_mul, map_mul, map_inv]
    exact hSU s hs (φ y) hy
  exact ⟨T, hT2, hTmap, fun s hs => hchar s (hSH hs)⟩

theorem noncentralWitness_of_cover {Y R : Type} [Group Y] [Finite Y] [Group R] {φ : Y →* R}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {q k : ℕ} (hq : q.Prime)
    (hqk : ¬ q ∣ Nat.card φ.ker) {X E : Subgroup R} (hX2 : IsPGroup 2 X)
    (hXZ : ¬ X ≤ (Subgroup.center Y).map φ) (hE : IsElemAbelian q E)
    (hEc : Nat.card E = q ^ k) (hXE : E ≤ Subgroup.normalizer (X : Set R)) :
    NoncentralWitness Y q k := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E', hE'le, hE'el, hE'map, hE'card⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_elemAbelian_lift hq hqk
      (π := φ) (P := E.comap φ) (E := E)
      (Subgroup.map_comap_eq_self_of_surjective hφ E) hE
  have hSU : ∀ x ∈ E', ∀ u ∈ X, φ x * u * (φ x)⁻¹ ∈ X := by
    intro x hx u hu
    have hφx : φ x ∈ E := by
      rw [← hE'map]
      exact Subgroup.mem_map_of_mem φ hx
    exact (Subgroup.le_normalizer_iff.1 hXE) (φ x) hφx u hu
  obtain ⟨T, hT2, hTmap, hE'T⟩ :=
    exists_two_subgroup_map_eq_of_cover hφ hker hX2 (S := E') hSU
  have hTnc : ¬ T ≤ Subgroup.center Y := by
    intro hTZ
    apply hXZ
    rw [← hTmap]
    exact Subgroup.map_mono hTZ
  exact ⟨E', hE'el, by rw [hE'card, hEc], T, hT2, hTnc, hE'T⟩

theorem noncentralWitness_of_center_quotient {K R : Type} [Group K] [Finite K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {q k : ℕ} (hq : q.Prime)
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center K)) {X E : Subgroup R} (hX : X ≠ ⊥)
    (hX2 : IsPGroup 2 X) (hE : IsElemAbelian q E) (hEc : Nat.card E = q ^ k)
    (hXE : E ≤ Subgroup.normalizer (X : Set R)) : NoncentralWitness K q k := by
  classical
  let φ : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : φ.ker = Subgroup.center K := by
    rw [show φ = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hZmap : (Subgroup.center K).map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff (Subgroup.center K) (f := φ), hker]
  have hXZ : ¬ X ≤ (Subgroup.center K).map φ := by
    rw [hZmap, le_bot_iff]
    exact hX
  exact noncentralWitness_of_cover hφ hker.le hq (by rwa [hker]) hX2 hXZ hE hEc hXE

private theorem exists_elemAbelian_normalizer_twoSubgroup_of_central_lift {K R : Type} [Group K]
    [Finite K] [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {h w : Fin k → R} (hpow : ∀ i, h i ^ p = 1)
    (hcomm : ∀ i j, Commute (h i) (h j))
    (hind : Nat.card (Subgroup.closure (Set.range h)) = p ^ k)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hcross : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i))
    {X : Subgroup R} (hX2 : IsPGroup 2 X) (hNX : ∀ i, h i ∈ Subgroup.normalizer (X : Set R)) :
    ∃ W T : Subgroup K, IsElemAbelian p W ∧
      Nat.card W = p ^ (k + CFSG.Open.pRank p (Subgroup.center K)) ∧
      IsPGroup 2 T ∧
      T.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))) = X ∧
      W ≤ Subgroup.normalizer (T : Set K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : φ.ker = Subgroup.center K := by
    rw [show φ = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hkerle : φ.ker ≤ Subgroup.center K := hker.le
  set D : Subgroup R := Subgroup.closure (Set.range h) with hD
  have hDcard : Nat.card D = p ^ k := hind
  have hFcomm := comap_closure_comm_of_cross hφ hkerle hp hp2 hcomm hpow hinv hcross
  choose y hy using fun i => exists_lift_pow_eq_one hφ hkerle hp hp2 (hpow i) (hinv i)
  set E : Subgroup K := Subgroup.closure (Set.range y) with hE
  have hyE : ∀ i, y i ∈ E := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hEcomap : E ≤ D.comap φ := by
    rw [hE, hD]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_comap.2 (by
      rw [(hy i).1]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hEcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x :=
    fun x hx z hz => hFcomm x (hEcomap hx) z (hEcomap hz)
  have hEmap : E.map φ = D := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact hEcomap
    · rw [hD]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨y i, hyE i, (hy i).1⟩
  have hEcard : Nat.card E = p ^ k := by
    refine le_antisymm ?_ ?_
    · rw [hE]
      exact card_closure_le_pow_of_commuting hp (fun i => (hy i).2)
        (fun i j => hEcomm (y i) (hyE i) (y j) (hyE j))
    · have h := Subgroup.card_map_dvd (H := E) φ
      rw [hEmap, hDcard] at h
      exact Nat.le_of_dvd Nat.card_pos h
  have hEker : E ⊓ φ.ker = ⊥ := by
    let ψ : E →* D := (φ.comp E.subtype).codRestrict D (fun x => hEcomap x.2)
    have hψrange : ψ.range = ⊤ := by
      have hmap : Subgroup.map D.subtype ψ.range = D := by
        apply le_antisymm
        · rintro _ ⟨x, -, rfl⟩
          exact x.2
        · refine (Subgroup.closure_le _).2 ?_
          rintro _ ⟨i, rfl⟩
          refine ⟨ψ ⟨y i, hyE i⟩, ?_, ?_⟩
          · exact MonoidHom.mem_range.2 ⟨⟨y i, hyE i⟩, rfl⟩
          · exact (hy i).1
      have htop : Subgroup.map D.subtype ψ.range =
          Subgroup.map D.subtype (⊤ : Subgroup D) := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
        exact hmap
      exact Subgroup.map_injective D.subtype_injective htop
    have hcard := Subgroup.card_ker_mul_card_range ψ
    rw [hψrange, Subgroup.card_top, hDcard, hEcard] at hcard
    have hker1 : Nat.card ψ.ker = 1 := by
      have hpk : 0 < p ^ k := pow_pos hp.pos k
      have h1 : Nat.card ψ.ker * p ^ k = 1 * p ^ k := by rw [hcard, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpk h1
    have hψker : ψ.ker = ⊥ := (Subgroup.eq_bot_iff_card ψ.ker).mpr hker1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : E) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact MonoidHom.mem_ker.1 hx.2
    rw [hψker] at hx'
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.1 hx')
  obtain ⟨A, hAle, hAab, hAcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (Subgroup.center K)
  have hEA : E ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxker : x ∈ E ⊓ φ.ker := by
      refine ⟨hx.1, ?_⟩
      rw [hker]
      exact hAle hx.2
    rw [hEker] at hxker
    exact Subgroup.mem_bot.1 hxker
  let W : Subgroup K := E ⊔ A
  have hkercomap : φ.ker ≤ D.comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact D.one_mem
  have hAle_comap : A ≤ D.comap φ := (hker ▸ hAle).trans hkercomap
  have hWcomap : W ≤ D.comap φ := sup_le hEcomap hAle_comap
  have hWcomm : ∀ x ∈ W, ∀ z ∈ W, x * z = z * x :=
    fun x hx z hz => hFcomm x (hWcomap hx) z (hWcomap hz)
  have hEpowval : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    rw [hE] at hx
    exact CFSG.RankThree.CentralCover.pow_eq_one_of_mem_closure
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hEcomm (y i) (hyE i) (y j) (hyE j))
      (by rintro _ ⟨i, rfl⟩; exact (hy i).2) hx
  have hWpow : ∀ x ∈ W, x ^ p = 1 := by
    intro x hx
    rw [show W = Subgroup.closure ((E : Set K) ∪ (A : Set K)) from
      Subgroup.sup_eq_closure E A] at hx
    refine CFSG.RankThree.CentralCover.pow_eq_one_of_mem_closure ?_ ?_ hx
    · rintro s (hs | hs) t (ht | ht)
      · exact hEcomm s hs t ht
      · exact Subgroup.mem_center_iff.1 (hAle ht) s
      · exact (Subgroup.mem_center_iff.1 (hAle hs) t).symm
      · exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    · rintro s (hs | hs)
      · exact hEpowval s hs
      · exact hAab.2 s hs
  have hWab : IsElemAbelian p W :=
    ⟨⟨⟨fun x z => Subtype.ext (hWcomm x x.2 z z.2)⟩⟩, fun x hx => hWpow x hx⟩
  have hWcard : Nat.card W = p ^ (k + CFSG.Open.pRank p (Subgroup.center K)) := by
    have hcommEA : ∀ x ∈ E, ∀ z ∈ A, x * z = z * x := fun x _ z hz =>
      Subgroup.mem_center_iff.1 (hAle hz) x
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E A hcommEA
    rw [hEA, Subgroup.card_bot, mul_one, hEcard, hAcard, ← pow_add] at hcard
    exact hcard
  have hDnorm : D ≤ Subgroup.normalizer (X : Set R) := by
    rw [hD]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact hNX i
  have hSU : ∀ x ∈ E, ∀ u ∈ X, φ x * u * (φ x)⁻¹ ∈ X := by
    intro x hx u hu
    exact (Subgroup.le_normalizer_iff.1 hDnorm) (φ x) (hEcomap hx) u hu
  obtain ⟨T, hT2, hTmap, hET⟩ :=
    exists_two_subgroup_map_eq_of_cover hφ hkerle hX2 (S := E) hSU
  have hAT : A ≤ Subgroup.normalizer (T : Set K) :=
    hAle.trans ((Subgroup.center_le_centralizer (T : Set K)).trans
      (Subgroup.centralizer_le_normalizer _))
  exact ⟨W, T, hWab, hWcard, hT2, hTmap, sup_le hET hAT⟩

theorem noncentralWitness_of_central_lift {K R : Type} [Group K] [Finite K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {h w : Fin k → R} (hpow : ∀ i, h i ^ p = 1) (hcomm : ∀ i j, Commute (h i) (h j))
    (hind : Nat.card (Subgroup.closure (Set.range h)) = p ^ k)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hcross : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i))
    {X : Subgroup R} (hX1 : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hNX : ∀ i, h i ∈ Subgroup.normalizer (X : Set R)) :
    NoncentralWitness K p (k + CFSG.Open.pRank p (Subgroup.center K)) := by
  classical
  let φ : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  obtain ⟨W, T, hWab, hWcard, hT2, hTmap, hWT⟩ :=
    exists_elemAbelian_normalizer_twoSubgroup_of_central_lift θ hp hp2 hpow hcomm hind hinv
      hcross hX2 hNX
  have hker : φ.ker = Subgroup.center K := by
    rw [show φ = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hZmap : (Subgroup.center K).map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff (Subgroup.center K) (f := φ), hker]
  have hTnc : ¬ T ≤ Subgroup.center K := by
    intro hTZ
    have hle : X ≤ (Subgroup.center K).map φ := by
      rw [← hTmap]
      exact Subgroup.map_mono hTZ
    rw [hZmap] at hle
    exact hX1 (le_bot_iff.1 hle)
  exact ⟨W, hWab, hWcard, T, hT2, hTnc, hWT⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
