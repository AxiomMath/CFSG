module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcTorus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

private theorem card_map_eq_card_of_inf_ker_eq_bot {S K : Type} [Group S] [Group K]
    (α : S →* K) {E : Subgroup S} (h : E ⊓ α.ker = ⊥) :
    Nat.card (E.map α) = Nat.card E := by
  have hker : (α.comp E.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : S) ∈ E ⊓ α.ker := ⟨x.2, hx⟩
    rw [h] at hx'
    exact Subtype.ext (Subgroup.mem_bot.mp hx')
  have hinj : Function.Injective (α.comp E.subtype) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hbij : Function.Bijective
      (fun x : E => (⟨α x, ⟨x, x.2, rfl⟩⟩ : E.map α)) := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => ?_⟩
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Nat.card_congr (Equiv.ofBijective _ hbij).symm

theorem le_evenRank_of_map {S K : Type} [Group S] [Group K] [Finite K]
    (α : S →* K) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X E : Subgroup S} (hX2 : IsPGroup 2 X) (hXα : X.map α ≠ ⊥)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hinj : E ⊓ α.ker = ⊥)
    (hXE : E ≤ Subgroup.normalizer (X : Set S)) : k ≤ evenRank K := by
  have hX2' : IsPGroup 2 (X.map α) := hX2.map α
  have hE' : IsElemAbelian r (E.map α) := CFSG.SectionRank.isElemAbelian_map hE α
  have hEcard' : Nat.card (E.map α) = r ^ k := by
    rw [card_map_eq_card_of_inf_ker_eq_bot α hinj, hEcard]
  have hXE' : E.map α ≤ Subgroup.normalizer (X.map α : Set K) :=
    (Subgroup.map_mono hXE).trans (X.le_normalizer_map α)
  exact le_evenRank_of_normalizer hr hr2 hXα hX2' hE' hEcard' hXE'

theorem le_twoLocalPrimeRank_of_map {S K : Type} [Group S] [Group K] [Finite K]
    (α : S →* K) {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X E : Subgroup S} (hX2 : IsPGroup 2 X) (hXα : X.map α ≠ ⊥)
    (hE : IsElemAbelian r E) (hEcard : Nat.card E = r ^ k)
    (hinj : E ⊓ α.ker = ⊥)
    (hXE : E ≤ Subgroup.normalizer (X : Set S)) : k ≤ GLATwoLocalRank r K := by
  have hX2' : IsPGroup 2 (X.map α) := hX2.map α
  have hE' : IsElemAbelian r (E.map α) := CFSG.SectionRank.isElemAbelian_map hE α
  have hEcard' : Nat.card (E.map α) = r ^ k := by
    rw [card_map_eq_card_of_inf_ker_eq_bot α hinj, hEcard]
  have hXE' : E.map α ≤ Subgroup.normalizer (X.map α : Set K) :=
    (Subgroup.map_mono hXE).trans (X.le_normalizer_map α)
  have h1 : k ≤ CFSG.Open.pRank r (Subgroup.normalizer (X.map α : Set K)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove r hr _)
      ⟨E.map α, hXE', hE', hEcard'⟩
  have h2 : CFSG.Open.pRank r (Subgroup.normalizer (X.map α : Set K)) ≤
      CFSG.Open.twoLocalPrimeRank r K :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr _
      ⟨X.map α, hXα, hX2', rfl⟩
  exact h1.trans h2

theorem exists_surjective_of_hopfMultiplier_card {S₀ J K : Type} [Group S₀] [Group J] [Group K]
    [Finite S₀] [Finite K] (hS₀ : Group.IsPerfect S₀) (hK : Group.IsPerfect K)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀)
    (hk₀ : p₀.ker ≤ Subgroup.center S₀) (θ : K ⧸ Subgroup.center K ≃* J) {m : ℕ}
    (hcop : Nat.Coprime (Nat.card (Subgroup.center K)) m)
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) =
      Nat.card p₀.ker * m) :
    ∃ α : S₀ →* K, Function.Surjective α ∧
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).comp α = p₀ := by
  let q : K →* J := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = Subgroup.center K := by
    rw [show q = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  exact CFSG.LocalAnalysis.RankThreeUC.S15.ACore.exists_lift_of_coprime_card hS₀ hK p₀ hp₀ hk₀
    q hq (by rw [hqker]) (by simpa [hqker] using hcop) hcard

theorem exists_mulEquiv_of_hopfMultiplier_card {S₀ J K : Type} [Group S₀] [Group J] [Group K]
    [Finite S₀] [Finite K] (hS₀ : Group.IsPerfect S₀) (hK : Group.IsPerfect K)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀)
    (hk₀ : p₀.ker ≤ Subgroup.center S₀) (θ : K ⧸ Subgroup.center K ≃* J)
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) = Nat.card p₀.ker)
    (hZ : Nat.card (Subgroup.center K) = Nat.card p₀.ker) :
    ∃ e : S₀ ≃* K,
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).comp e.toMonoidHom = p₀ := by
  have hcard' : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) =
      Nat.card p₀.ker * 1 := by simpa using hcard
  have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) 1 := by simp
  obtain ⟨α, hα, hαcomp⟩ :=
    exists_surjective_of_hopfMultiplier_card hS₀ hK p₀ hp₀ hk₀ θ hcop hcard'
  let q : K →* J := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = Subgroup.center K := by
    rw [show q = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have h1 := Subgroup.card_ker_mul_card_range p₀
  rw [MonoidHom.range_eq_top.2 hp₀, Subgroup.card_top] at h1
  have h2 := Subgroup.card_ker_mul_card_range q
  rw [MonoidHom.range_eq_top.2 hq, Subgroup.card_top, hqker, hZ] at h2
  have hcardSK : Nat.card S₀ = Nat.card K :=
    calc Nat.card S₀ = Nat.card p₀.ker * Nat.card J := h1.symm
      _ = Nat.card K := h2
  have h3 := Subgroup.card_ker_mul_card_range α
  rw [MonoidHom.range_eq_top.2 hα, Subgroup.card_top, hcardSK] at h3
  have hkerα : α.ker = ⊥ := by
    refine Subgroup.card_eq_one.mp (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K)) ?_)
    rw [mul_comm (Nat.card K) (Nat.card α.ker), h3, mul_one]
  have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).mp hkerα
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hα⟩, hαcomp⟩


open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LieType.Steinberg.Isogeny

section TorusWitness


theorem map_minTorus_le_normalizer_rootGroup {F : Type} [Field F]
    (V : Subgroup (Fin (Tag.rank .E6) → Fˣ)) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) :
    V.map (minTorus e6Data_valid F) ≤
      Subgroup.normalizer ((e6Data_valid.rootGroup F γ :
        Subgroup ↥(e6Data_valid.minGroup F)) : Set _) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hv
  have hconv : ∀ w ∈ V, ∀ k ∈ e6Data_valid.rootGroup F γ,
      minTorus e6Data_valid F w * k * (minTorus e6Data_valid F w)⁻¹ ∈
        e6Data_valid.rootGroup F γ := by
    intro w _ k hk
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup F).1 hk
    rw [minTorus_conj_xm e6Data_valid F w hγ c]
    exact e6Data_valid.xm_mem_rootGroup F γ _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hconv u hu h
  · intro hh
    have hh' := hconv u⁻¹ (V.inv_mem hu)
      (minTorus e6Data_valid F u * h * (minTorus e6Data_valid F u)⁻¹) hh
    have hcalc : minTorus e6Data_valid F u⁻¹ *
        (minTorus e6Data_valid F u * h * (minTorus e6Data_valid F u)⁻¹) *
        (minTorus e6Data_valid F u⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    rwa [hcalc] at hh'

theorem exists_elemAbelian_729_le_normalizer_rootGroup_E6 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    ∃ E X : Subgroup ↥(e6Data_valid.minGroup F),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 ∧
        E ≤ Subgroup.normalizer (X : Set _) := by
  have h3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hpow : ∀ u : Fin (Tag.rank .E6) → Fˣ, u ^ 3 = 1 := by
    intro u
    funext i
    have h := pow_card_eq_one' (G := Fˣ) (x := u i)
    rw [h3] at h
    simpa using h
  let E : Subgroup ↥(e6Data_valid.minGroup F) :=
    (⊤ : Subgroup (Fin (Tag.rank .E6) → Fˣ)).map (minTorus e6Data_valid F)
  let X : Subgroup ↥(e6Data_valid.minGroup F) := e6Data_valid.rootGroup F γ
  have hEcard : Nat.card E = 3 ^ 6 := by
    rw [show E = (⊤ : Subgroup (Fin (Tag.rank .E6) → Fˣ)).map
        (minTorus e6Data_valid F) from rfl,
      Subgroup.card_map_of_injective (minTorus_injective e6Data_valid F),
      Subgroup.card_top, Nat.card_fun, h3, Nat.card_fin]
    norm_num [Tag.rank]
  have hE : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨u, -, hu⟩ := a.2
      obtain ⟨v, -, hv⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · intro x hx
      obtain ⟨u, -, hu⟩ := hx
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hu, ← Subgroup.coe_pow, ← map_pow, hpow u, map_one]
  have hXcard : Nat.card X = 4 := by
    have hbij : Function.Bijective (fun c : F =>
        (⟨e6Data_valid.xm F γ c, e6Data_valid.xm_mem_rootGroup F γ c⟩ : X)) := by
      refine ⟨fun c d h => e6Data_valid.xm_injective F hγ (congrArg Subtype.val h),
        fun y => ?_⟩
      obtain ⟨c, hc⟩ := (e6Data_valid.mem_rootGroup F).1 y.2
      exact ⟨c, Subtype.ext hc⟩
    have hc : Nat.card F = Nat.card X := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [← hc, hF]
  have hXne : X ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot X, hXcard]
    norm_num
  have hX2 : IsPGroup 2 X := IsPGroup.of_card (n := 2) (by rw [hXcard]; norm_num)
  exact ⟨E, X, hXne, hX2, hE, hEcard,
    map_minTorus_le_normalizer_rootGroup (V := ⊤) hγ⟩

end TorusWitness

theorem rk2_low_e6_cover (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6) (hn : lab.n = 2)
    (hc : ¬ Subgroup.center K = ⊥) :
    6 ≤ evenRank K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hn
  subst htag
  subst hn
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 2 :=
    lieModel_of_markedModel_E6 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hcardF : Nat.card F = 4 := by rw [hFcard]; norm_num
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := 2) (by norm_num) hFcard
  let S₀ : Type := ↥(e6Data_valid.minGroup F)
  haveI hS₀fin : Finite S₀ :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := F) e6Data_valid
  have hS₀perf : Group.IsPerfect S₀ := CFSG.LieType.CurtisTits.isPerfect_e6 F
  have hS₀center : Nat.card (Subgroup.center S₀) = 3 := by
    have h := (card_center_e6 (k := F)).1
    rw [hcardF] at h
    simpa using h
  let J : Type := CFSG.Blueprint.AdjointQuotient Tag.E6 F
  let eAdj : J ≃* adjointGroup Tag.E6 F := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv Tag.E6 F
  let p₀ : S₀ →* J := eAdj.symm.toMonoidHom.comp (e6Isogeny F)
  have hp₀ : Function.Surjective p₀ := eAdj.symm.surjective.comp (e6Isogeny_surjective F)
  have hp₀ker : p₀.ker = (e6Isogeny F).ker :=
    MonoidHom.ker_comp_of_injective _ _ eAdj.symm.injective
  have hk₀ : p₀.ker ≤ Subgroup.center S₀ := by
    rw [hp₀ker, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
  have hMcard : Nat.card (CFSG.Open.griessHopfMultiplier J) = 3 := by
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.FieldFour.e6_four_hopfMultiplier (K := F) hFcard
    rw [Nat.card_congr eM.toEquiv,
      Nat.card_congr (Multiplicative.toAdd :
        Multiplicative (ZMod (Nat.gcd 3 (Nat.card F - 1))) ≃
          ZMod (Nat.gcd 3 (Nat.card F - 1))),
      Nat.card_zmod, hcardF]
    norm_num
  haveI : Finite (CFSG.Open.griessHopfMultiplier J) :=
    Nat.finite_of_card_ne_zero (by rw [hMcard]; norm_num)
  have hdvd : Nat.card (Subgroup.center K) ∣ 3 := by
    have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ' φ
    rwa [hMcard] at h
  have hZcard : Nat.card (Subgroup.center K) = 3 := by
    have hpos : 1 < Nat.card (Subgroup.center K) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hc
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd with h1 | h3
    · omega
    · exact h3
  have hhopf : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) = 3 := by
    rw [← Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess J).toEquiv]
    exact hMcard
  have hp₀card : Nat.card p₀.ker = 3 := by
    rw [hp₀ker, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center,
      hS₀center]
  obtain ⟨e, -⟩ :=
    exists_mulEquiv_of_hopfMultiplier_card hS₀perf hQ'.1 p₀ hp₀ hk₀ φ
      (by rw [hhopf, hp₀card]) (by rw [hZcard, hp₀card])
  obtain ⟨E₀, X₀, hX₀, hX₀2, hE₀, hE₀card, hE₀norm⟩ :=
    exists_elemAbelian_729_le_normalizer_rootGroup_E6 hcardF
      (IsRoot.basis (τ := .E6) 0)
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  exact le_evenRank_of_map e.toMonoidHom Nat.prime_three (by norm_num) hX₀2
    (by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective X₀ (f := e.toMonoidHom) e.injective]
      exact hX₀)
    hE₀ hE₀card (by
      rw [hker]
      simp) hE₀norm

theorem rk2_low_e6_two_all (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6) (hn : 2 ≤ lab.n) :
    5 ≤ evenRank K := by
  by_cases h3 : 3 ≤ lab.n
  · exact (rk2_low_e6_of_three_le K lab hK htag h3).trans' (by norm_num)
  · have h2 : lab.n = 2 := by omega
    by_cases hc : Subgroup.center K = ⊥
    · exact rk2_low_e6_two_of_center_eq_bot K lab hK htag h2 hc
    · exact (rk2_low_e6_cover K lab hK htag h2 hc).trans' (by norm_num)

theorem rk2_low_e6_big (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6)
    (h : 3 ≤ lab.n ∨ (lab.n = 2 ∧ ¬ Subgroup.center K = ⊥)) :
    6 ≤ evenRank K := by
  rcases h with h3 | ⟨h2, hc⟩
  · exact rk2_low_e6_of_three_le K lab hK htag h3
  · exact rk2_low_e6_cover K lab hK htag h2 hc

end CFSG.LocalAnalysis.GLTheoremA
