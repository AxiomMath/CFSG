module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDReduce
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Cover
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD

open CFSG CFSG.Open Subgroup

theorem s622_quot_core {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {D V M₀ : Subgroup A} {z : A} (hKD : CFSG.Open.IsKGroup ↥D) (hzord : orderOf z = p)
    (hzD : z ∈ normalizer (D : Set A)) (hpD : ¬ p ∣ Nat.card D)
    (hV : CFSG.ABGLocalTools.IsSylowOf 2 V D) (hzV : z ∈ normalizer (V : Set A))
    (hM₀D : M₀ ≤ D)
    (H1 : ∀ U : Subgroup A, U ≤ V → U ≠ ⊥ → z ∈ normalizer (U : Set A) →
      normalizer (U : Set A) ⊓ D ≤ M₀)
    (H2 : centralizer ({z} : Set A) ⊓ D ≤ M₀)
    (hEven : KFactFieldAutEven) (hOdd : KFactFieldAutOdd) :
    D ≤ M₀ ⊔ rankThreePrimeCore 2 D := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp0 : 0 < p := hp.pos
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  obtain ⟨hOD, hDO, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  set O : Subgroup A := rankThreePrimeCore 2 D with hOdef
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  have hOmax : ∀ R : Subgroup A, R ≤ D → (R.subgroupOf D).Normal → Odd (Nat.card R) → R ≤ O :=
    fun R hRD hRn hRo => le_sSup
      (show R ∈ {N : Subgroup A | N ≤ D ∧ (N.subgroupOf D).Normal ∧
        Nat.Coprime 2 (Nat.card N)} from ⟨hRD, hRn, Nat.coprime_two_left.mpr hRo⟩)
  by_cases hV0 : V = ⊥
  ·
    have hDodd : Odd (Nat.card D) := by
      rw [← Nat.not_even_iff_odd]
      intro he
      have hbot : CFSG.ABGLocalTools.IsSylowOf 2 (⊥ : Subgroup A) D := hV0 ▸ hV
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hbot).2.2
        (by rw [Subgroup.relIndex_bot_left]; exact even_iff_two_dvd.mp he)
    have hDn : (D.subgroupOf D).Normal := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    exact (hOmax D le_rfl hDn hDodd).trans le_sup_right
  have hVM0 : V ≤ M₀ := fun v hv =>
    H1 V le_rfl hV0 hzV (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hv, hV.le hv⟩)
  set W : Subgroup A := D ⊔ zpowers z with hWdef
  have hDW : D ≤ W := le_sup_left
  have hOW : O ≤ W := hOD.trans hDW
  have hzO : z ∈ normalizer (O : Set A) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.mem_normalizer_rankThreePrimeCore 2 D hzD
  have hWN : W ≤ normalizer (O : Set A) := sup_le hDO (Subgroup.zpowers_le.mpr hzO)
  haveI hN0 : (O.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOW).mpr hWN
  have hpO : ¬ p ∣ Nat.card O := fun h => hpD (h.trans (Subgroup.card_dvd_of_le hOD))
  have hpN0 : ¬ p ∣ Nat.card (O.subgroupOf W) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOW).toEquiv]
    exact hpO
  have hcardO' : Nat.card (O.subgroupOf D) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOD).toEquiv
  set zW : W := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩ with hzWdef
  have hzWord : orderOf zW = p := (Subgroup.orderOf_mk z _).trans hzord
  have hzWp : zW ^ p = 1 := Subtype.ext hzp
  set π : W →* W ⧸ (O.subgroupOf W) := QuotientGroup.mk' _ with hπdef
  set zb : W ⧸ (O.subgroupOf W) := π zW with hzbdef
  have hzb_p : zb ^ p = 1 := by rw [hzbdef, ← map_pow, hzWp, map_one]
  have hzb_ne : zb ≠ 1 := by
    intro h
    have hz1 : z ∈ O := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff zW).mp h)
    have h1 := orderOf_dvd_natCard (⟨z, hOD hz1⟩ : ↥D)
    rw [Subgroup.orderOf_mk, hzord] at h1
    exact hpD h1
  have hzb_ord : orderOf zb = p := orderOf_eq_prime hzb_p hzb_ne
  set ρ : ↥D →* W ⧸ (O.subgroupOf W) := π.comp (Subgroup.inclusion hDW) with hρdef
  have hρ : ∀ d : ↥D, ρ d = π ⟨(d : A), hDW d.2⟩ := fun d => rfl
  have hker : ∀ d : ↥D, ρ d = 1 ↔ (d : A) ∈ O := by
    intro d
    rw [hρ]
    exact (QuotientGroup.eq_one_iff _).trans Subgroup.mem_subgroupOf
  set Xs : Subgroup (W ⧸ (O.subgroupOf W)) := ρ.range with hXsdef
  have hXD : ∀ w : W, π w ∈ Xs → (w : A) ∈ D := by
    intro w hw
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hw
    rw [hρ] at hd
    have h1 : (⟨(d : A), hDW d.2⟩ : W)⁻¹ * w ∈ O.subgroupOf W := QuotientGroup.eq.mp hd
    have h2 : (d : A)⁻¹ * (w : A) ∈ O := by
      have := Subgroup.mem_subgroupOf.mp h1
      simpa using this
    have e : (w : A) = (d : A) * ((d : A)⁻¹ * (w : A)) := by group
    rw [e]
    exact D.mul_mem d.2 (hOD h2)
  have hzD' : ∀ d : A, d ∈ D → z * d * z⁻¹ ∈ D := fun d hd =>
    (Subgroup.mem_normalizer_iff.mp hzD d).mp hd
  have hzV' : ∀ d : A, d ∈ V → z * d * z⁻¹ ∈ V := fun d hd =>
    (Subgroup.mem_normalizer_iff.mp hzV d).mp hd
  have hρconj : ∀ d : ↥D, ρ ⟨z * (d : A) * z⁻¹, hzD' d d.2⟩ = zb * ρ d * zb⁻¹ := by
    intro d
    rw [hρ, hρ, hzbdef, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hXs_top : (⊤ : Subgroup ↥Xs).map Xs.subtype = Xs := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hzX : zb ∈ Subgroup.normalizer (Xs : Set (W ⧸ (O.subgroupOf W))) := by
    apply mem_normalizer_of_forward hp0 hzb_p
    rintro _ ⟨d, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨⟨z * (d : A) * z⁻¹, hzD' d d.2⟩, hρconj d⟩
  have hpXs : ¬ p ∣ Nat.card Xs := fun h => hpD (h.trans (Subgroup.card_range_dvd ρ))
  set Vb : Subgroup (W ⧸ (O.subgroupOf W)) := (V.subgroupOf D).map ρ with hVbdef
  set Mb : Subgroup (W ⧸ (O.subgroupOf W)) := ((M₀ ⊔ O).subgroupOf D).map ρ with hMbdef
  have hVsyl : CFSG.ABGLocalTools.IsSylowOf 2 Vb Xs := by
    have hVs : CFSG.ABGLocalTools.IsSylowOf 2 (V.subgroupOf D) ⊤ :=
      isSylowOf_subgroupOf_top hV
    have h1 := isSylowOf_two_map_surjective ρ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ρ) hVs
    have h2 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Xs).mpr h1
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict, hXs_top] at h2
    exact h2
  have hVz : zb ∈ Subgroup.normalizer (Vb : Set (W ⧸ (O.subgroupOf W))) := by
    apply mem_normalizer_of_forward hp0 hzb_p
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← hρconj d]
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr
      (hzV' _ (Subgroup.mem_subgroupOf.mp hd)))
  have hVM : Vb ≤ Mb := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (hVM0 (Subgroup.mem_subgroupOf.mp hd))))
  have hKX : CFSG.Open.IsKGroup ↥Xs :=
    CFSG.Open.IsKGroup.of_surjective hKD ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
  have hodd : CFSG.oddCore ↥Xs = ⊥ := by
    rw [eq_bot_iff]
    show sSup {N : Subgroup ↥Xs | N.Normal ∧ Odd (Nat.card N)} ≤ ⊥
    apply sSup_le
    rintro R ⟨hRn, hRo⟩
    set f : ↥D →* ↥Xs := ρ.rangeRestrict with hfdef
    have hfs : Function.Surjective f := MonoidHom.rangeRestrict_surjective ρ
    have hkerf : f.ker = O.subgroupOf D := by
      ext d
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker d]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have hcardO : Nat.card (O.subgroupOf D) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOD).toEquiv
    set R' : Subgroup ↥D := R.comap f with hR'def
    have hR'n : R'.Normal := hRn.comap f
    have hidx : R'.index = R.index := Subgroup.index_comap_of_surjective R hfs
    have hpos : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hcardeq : Nat.card R' = Nat.card O * Nat.card R := by
      have h1 := Subgroup.card_mul_index R'
      have h2 := Subgroup.card_mul_index R
      have h3 := Subgroup.card_ker_mul_card_of_surjective hfs
      rw [hkerf, hcardO] at h3
      have key : Nat.card R' * R.index = (Nat.card O * Nat.card R) * R.index := by
        calc Nat.card R' * R.index = Nat.card D := by rw [← hidx]; exact h1
          _ = Nat.card O * Nat.card ↥Xs := h3.symm
          _ = Nat.card O * (Nat.card R * R.index) := by rw [h2]
          _ = (Nat.card O * Nat.card R) * R.index := by ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) key
    have hR'odd : Odd (Nat.card R') := by
      rw [hcardeq]
      exact hOodd.mul hRo
    have hR'O : R' ≤ O.subgroupOf D := by
      intro d hd
      have hR''le : R'.map D.subtype ≤ O := by
        apply hOmax (R'.map D.subtype) (Subgroup.map_subtype_le R')
        · have hsub : (R'.map D.subtype).subgroupOf D = R' :=
            Subgroup.comap_map_eq_self_of_injective D.subtype_injective R'
          rw [hsub]
          exact hR'n
        · rw [Subgroup.card_map_of_injective D.subtype_injective]
          exact hR'odd
      exact Subgroup.mem_subgroupOf.mpr (hR''le (Subgroup.mem_map_of_mem _ hd))
    intro r hr
    obtain ⟨d, rfl⟩ := hfs r
    have hdk : d ∈ f.ker := by
      rw [hkerf]
      exact hR'O hr
    exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp hdk)
  have hC : ∀ g ∈ Xs, zb * g = g * zb → g ∈ Mb := by
    intro g hg hcg
    have hA₀ : IsPGroup p (Subgroup.zpowers zW) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, hzWord, pow_one]⟩
    have hcop := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p (O.subgroupOf W) hpN0
      (Subgroup.zpowers zW) hA₀
    have hmapz : (Subgroup.zpowers zW).map π = Subgroup.zpowers zb :=
      MonoidHom.map_zpowers π zW
    have hcop' : (Subgroup.centralizer ((Subgroup.zpowers zW : Subgroup W) : Set W)).map π =
        Subgroup.centralizer ((Subgroup.zpowers zb : Subgroup (W ⧸ (O.subgroupOf W))) :
          Set (W ⧸ (O.subgroupOf W))) := by
      rw [← hmapz]
      exact hcop
    have hgC : g ∈ (Subgroup.centralizer ((Subgroup.zpowers zW : Subgroup W) : Set W)).map π := by
      rw [hcop']
      exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact (Commute.zpow_left hcg k).eq)
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hgC
    have hcz : zW * c = c * zW := Subgroup.mem_centralizer_iff.mp hc zW (Subgroup.mem_zpowers zW)
    have hczA : z * (c : A) = (c : A) * z := congrArg Subtype.val hcz
    have hcD : (c : A) ∈ D := hXD c hg
    have hcM0 : (c : A) ∈ M₀ := H2 (Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_iff.mpr (fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact hczA), hcD⟩)
    have hmemT : (⟨(c : A), hcD⟩ : ↥D) ∈ (M₀ ⊔ O).subgroupOf D :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hcM0)
    exact Subgroup.mem_map_of_mem ρ hmemT
  have hN : ∀ U : Subgroup (W ⧸ (O.subgroupOf W)), U ≤ Vb → U ≠ ⊥ → IsPGroup 2 U →
      zb ∈ Subgroup.normalizer (U : Set (W ⧸ (O.subgroupOf W))) →
      Subgroup.normalizer (U : Set (W ⧸ (O.subgroupOf W))) ⊓ Xs ≤ Mb := by
    intro U hUV hU1 hU2 hzU
    set U₁ : Subgroup A := ((U.comap ρ).map D.subtype) ⊓ V with hU₁def
    have hU₁V : U₁ ≤ V := inf_le_right
    have hU₁D : U₁ ≤ D := hU₁V.trans hV.le
    have hVlift : ∀ y ∈ U, ∃ v : ↥D, (v : A) ∈ U₁ ∧ ρ v = y := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (hUV hy)
      exact ⟨v, Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨v, hy, rfl⟩,
        Subgroup.mem_subgroupOf.mp hv⟩, rfl⟩
    have hU₁ne : U₁ ≠ ⊥ := by
      obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
      obtain ⟨v, hvU₁, hvy⟩ := hVlift y.1 y.2
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      refine ⟨⟨(v : A), hvU₁⟩, fun h => hy1 ?_⟩
      have hv1 : (v : A) = 1 := congrArg Subtype.val h
      have hvone : v = 1 := Subtype.ext hv1
      apply Subtype.ext
      simp only [Subgroup.coe_one]
      rw [← hvy, hvone, map_one]
    have hzU₁ : z ∈ Subgroup.normalizer (U₁ : Set A) := by
      apply mem_normalizer_of_forward hp0 hzp
      intro u hu
      obtain ⟨hu1, huV⟩ := Subgroup.mem_inf.mp hu
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hu1
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨⟨z * (d : A) * z⁻¹, hzD' d d.2⟩, ?_, rfl⟩,
        hzV' _ huV⟩
      show ρ ⟨z * (d : A) * z⁻¹, hzD' d d.2⟩ ∈ U
      rw [hρconj d]
      exact (Subgroup.mem_normalizer_iff.mp hzU (ρ d)).mp hd
    have hH1 : Subgroup.normalizer (U₁ : Set A) ⊓ D ≤ M₀ := H1 U₁ hU₁V hU₁ne hzU₁
    set P : Subgroup A := U₁ ⊔ O with hPdef
    have hPD : P ≤ D := sup_le hU₁D hOD
    have hPTgt : P ≤ M₀ ⊔ O :=
      sup_le ((hU₁V.trans hVM0).trans le_sup_left) le_sup_right
    have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 U₁ P := by
      haveI : (O.subgroupOf D).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOD).mpr hDO
      have hcopN : Nat.Coprime 2 (Nat.card (O.subgroupOf D)) := by
        rw [hcardO']
        exact Nat.coprime_two_left.mpr hOodd
      have hQ : IsPGroup 2 (U₁.subgroupOf D) := (hV.isPGroup.to_le hU₁V).comap_subtype
      have hs := CFSG.ABGLocalTools.isSylowOf_sup_of_coprime hcopN hQ
      have hs' := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff D).mpr hs
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hU₁D, inf_eq_left.mpr hOD, sup_comm] at hs'
      exact hs'
    have key : ∀ e : ↥D, ρ e ∈ Subgroup.normalizer (U : Set (W ⧸ (O.subgroupOf W))) →
        P.map (MulAut.conj (e : A)).toMonoidHom ≤ P := by
      intro e he
      rw [hPdef, Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨u, hu, rfl⟩
        obtain ⟨hu1, -⟩ := Subgroup.mem_inf.mp hu
        obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hu1
        have hρg : ρ (e * d₀ * e⁻¹) ∈ U := by
          rw [map_mul, map_mul, map_inv]
          exact (Subgroup.mem_normalizer_iff.mp he (ρ d₀)).mp hd₀
        obtain ⟨v, hvU₁, hvρ⟩ := hVlift _ hρg
        have hk : ρ ((e * d₀ * e⁻¹) * v⁻¹) = 1 := by
          rw [map_mul, map_inv, hvρ, mul_inv_cancel]
        have hO' : (((e * d₀ * e⁻¹) * v⁻¹ : ↥D) : A) ∈ O := (hker _).mp hk
        have hgA : (e : A) * (d₀ : A) * (e : A)⁻¹ =
            (((e * d₀ * e⁻¹) * v⁻¹ : ↥D) : A) * (v : A) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        show (e : A) * (d₀ : A) * (e : A)⁻¹ ∈ P
        rw [hgA]
        exact P.mul_mem (Subgroup.mem_sup_right hO') (Subgroup.mem_sup_left hvU₁)
      · rintro _ ⟨o, ho, rfl⟩
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hDO e.2) o).mp ho)
    have hdN : ∀ d : ↥D, ρ d ∈ Subgroup.normalizer (U : Set (W ⧸ (O.subgroupOf W))) →
        (d : A) ∈ Subgroup.normalizer (P : Set A) := by
      intro d hd
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact key d hd (Subgroup.mem_map_of_mem _ hh)
      · intro hh
        have hd' : ρ d⁻¹ ∈ Subgroup.normalizer (U : Set (W ⧸ (O.subgroupOf W))) := by
          rw [map_inv]
          exact inv_mem hd
        have hmem := key d⁻¹ hd' (Subgroup.mem_map_of_mem _ hh)
        have e : (MulAut.conj ((d⁻¹ : ↥D) : A)).toMonoidHom ((d : A) * h * (d : A)⁻¹) = h := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_inv]
          group
        rw [e] at hmem
        exact hmem
    have hPH : P ≤ Subgroup.normalizer (P : Set A) ⊓ D := le_inf Subgroup.le_normalizer hPD
    have hPHn : (P.subgroupOf (Subgroup.normalizer (P : Set A) ⊓ D)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr inf_le_left
    have hfr := s622_le_sup_normalizer Nat.prime_two hPH hPHn hPsyl
    rintro x ⟨hxN, hxX⟩
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hxX
    have hdH : (d : A) ∈ Subgroup.normalizer (P : Set A) ⊓ D :=
      Subgroup.mem_inf.mpr ⟨hdN d hxN, d.2⟩
    have hdT := hfr hdH
    have hTgt : P ⊔ (Subgroup.normalizer (U₁ : Set A) ⊓
        (Subgroup.normalizer (P : Set A) ⊓ D)) ≤ M₀ ⊔ O := by
      apply sup_le hPTgt
      intro x hx
      have hxD : x ∈ D := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2
      exact Subgroup.mem_sup_left (hH1 (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hxD⟩))
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr (hTgt hdT))
  have hXM : Xs ≤ Mb :=
    abstract_reduction hp hp5 hzb_ord hzX hpXs hVsyl hVz hVM hKX hodd hC hN hEven hOdd
  intro d hd
  have hmem : ρ ⟨d, hd⟩ ∈ Xs := MonoidHom.mem_range.mpr ⟨⟨d, hd⟩, rfl⟩
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp (hXM hmem)
  have hk : ρ (t⁻¹ * ⟨d, hd⟩) = 1 := by
    rw [map_mul, map_inv, hte, inv_mul_cancel]
  have hO' : ((t⁻¹ * ⟨d, hd⟩ : ↥D) : A) ∈ O := (hker _).mp hk
  have hdeq : d = (t : A) * ((t⁻¹ * ⟨d, hd⟩ : ↥D) : A) := by
    simp
  rw [hdeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp ht) (Subgroup.mem_sup_right hO')

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD
