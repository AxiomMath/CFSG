module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreePairLift
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeNoSz
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def czLift (P' : Sylow 3 G) (z : G) (V : Subgroup (D1CzQuot 3 z)) : Subgroup G :=
  (((P' : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))) ⊓
    V.comap (QuotientGroup.mk' (primeComplementCore
      (G := Subgroup.centralizer ({z} : Set G)) 3))).map
    (Subgroup.centralizer ({z} : Set G)).subtype

omit [Finite G] in
theorem czLift_le {M : Subgroup G} {P' : Sylow 3 G} (hP'M : (P' : Subgroup G) ≤ M) {z : G}
    (V : Subgroup (D1CzQuot 3 z)) :
    czLift P' z V ≤ Subgroup.centralizer ({z} : Set G) ⊓ M := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.2, hP'M (Subgroup.mem_subgroupOf.mp ha.1)⟩

variable {M : Subgroup G} {P' : Sylow 3 G} {z : G} {Pbar : Sylow 3 (D1CzQuot 3 z)}
  {KC : Subgroup (D1CzQuot 3 z)} {T₁ : Sylow 3 KC} {n e : ℕ}

theorem exists_torus_czLift (hRC : D1ReducedCentralizer 3 P' M z Pbar KC)
    (hOB : primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3 ≤
      (Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf (Subgroup.centralizer ({z} : Set G)))
    (hNV : KC ⊓ Subgroup.normalizer ((((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC :
        Subgroup (D1CzQuot 3 z))) : Set (D1CzQuot 3 z)) ≤
      ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)))
    (hT₁ : (T₁ : Subgroup KC).map KC.subtype = (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)
    (hTF : OneLieTorusFacts 3 KC T₁ n e) :
    ∃ φ : Multiplicative (GaloisField 3 n) ≃*
        czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)),
      ∀ μ : (GaloisField 3 n)ˣ, ∃ t ∈ Subgroup.centralizer ({z} : Set G) ⊓ M,
        ∀ a : Multiplicative (GaloisField 3 n), t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ e * Multiplicative.toAdd a)) := by
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set O := primeComplementCore (G := C) 3 with hOdef
  set mk := QuotientGroup.mk' O with hmk
  have hOC := primeComplementCore_coprime (G := C) 3
  set V : Subgroup (D1CzQuot 3 z) := (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC with hV
  set Zc : Subgroup (D1CzQuot 3 z) := centerOf V with hZc
  set U : Subgroup C := (P' : Subgroup G).subgroupOf C with hU
  have hUp : IsPGroup 3 U := P'.isPGroup'.comap_subtype
  have hVU : V ≤ U.map mk := hRC.sylow_eq ▸ inf_le_left
  have hZV : Zc ≤ V := inf_le_left
  obtain ⟨ψ, hψinj, hψrange, hc⟩ := hTF.torus
  set ψ' : Multiplicative (GaloisField 3 n) →* D1CzQuot 3 z := KC.subtype.comp ψ with hψ'
  have hψ'inj : Function.Injective ψ' := KC.subtype_injective.comp hψinj
  have hψA : ψ'.range = (U ⊓ Zc.comap mk).map mk := by
    rw [map_mk_inf_comap_eq (hZV.trans hVU), hψ', MonoidHom.range_comp, hψrange]
    have h1 := map_subtype_centerOf (T₁ : Subgroup KC)
    rw [hT₁] at h1
    exact h1
  have hcm : ∀ μ : (GaloisField 3 n)ˣ, ∃ c ∈ ((C ⊓ M).subgroupOf C).map mk,
      ∀ a : Multiplicative (GaloisField 3 n), c * ψ' a * c⁻¹ =
        ψ' (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ e * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcN, hcact⟩ := hc μ
    have hcV : (c : D1CzQuot 3 z) ∈ KC ⊓ Subgroup.normalizer (V : Set (D1CzQuot 3 z)) := by
      have := coe_mem_normalizer_map hcN
      rwa [hT₁] at this
    refine ⟨c, hNV hcV, fun a => ?_⟩
    simp only [hψ', MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, hcact a]
  obtain ⟨φ, htor⟩ := exists_lift_mult Nat.prime_three O hOC (hUp.to_le inf_le_left) hOB ψ'
    hψ'inj hψA (fun μ => (μ : GaloisField 3 n) ^ e) (fun μ => pow_ne_zero _ μ.ne_zero) hcm
  let φG : Multiplicative (GaloisField 3 n) ≃* czLift P' z Zc :=
    φ.trans ((U ⊓ Zc.comap mk).equivMapOfInjective C.subtype C.subtype_injective)
  have hφG : ∀ a, (φG a : G) = ((φ a : C) : G) := fun a => rfl
  refine ⟨φG, fun μ => ?_⟩
  obtain ⟨t, htB, htact⟩ := htor μ
  refine ⟨t, Subgroup.mem_subgroupOf.mp htB, fun a => ?_⟩
  rw [hφG, hφG]
  have := congrArg (fun x : C => (x : G)) (htact a)
  simpa using this

theorem exists_pair_czLift (hRC : D1ReducedCentralizer 3 P' M z Pbar KC)
    (hOB : primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3 ≤
      (Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf (Subgroup.centralizer ({z} : Set G)))
    (hOodd : Odd (Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)))
    (hNV : KC ⊓ Subgroup.normalizer ((((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC :
        Subgroup (D1CzQuot 3 z))) : Set (D1CzQuot 3 z)) ≤
      ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)))
    (hT₁ : (T₁ : Subgroup KC).map KC.subtype = (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)
    (hTF : OneLieTorusFacts 3 KC T₁ n e) (hn2 : n = 2) :
    ∃ t : G, czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) ≤
        czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC) ∧
      IsPGroup 3 (czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) ∧
      Nat.card (czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) = 3 ^ 6 ∧
      (∀ x ∈ czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)),
        ∀ w ∈ czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC), x * w = w * x) ∧
      czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) ≤
        ⁅czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC),
          czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)⁆ ∧
      t ∈ Subgroup.centralizer ({z} : Set G) ⊓ M ∧
      t ∈ Subgroup.normalizer
        (czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC) : Set G) ∧
      t ∈ Subgroup.normalizer
        (czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) : Set G) ∧
      Nat.Coprime 6 (orderOf t) ∧
      (∃ u ∈ czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC),
        t * u * t⁻¹ * u⁻¹ ∉ czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC))) ∧
      ∀ Y : Subgroup G, czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) ≤ Y →
        Y ≤ czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC) →
        t ∈ Subgroup.normalizer (Y : Set G) →
        Y = czLift P' z (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) ∨
          Y = czLift P' z ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC) := by
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set O := primeComplementCore (G := C) 3 with hOdef
  set mk := QuotientGroup.mk' O with hmk
  have hOC := primeComplementCore_coprime (G := C) 3
  set V : Subgroup (D1CzQuot 3 z) := (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC with hV
  set Zc : Subgroup (D1CzQuot 3 z) := centerOf V with hZc
  set U : Subgroup C := (P' : Subgroup G).subgroupOf C with hU
  have hUp : IsPGroup 3 U := P'.isPGroup'.comap_subtype
  have hVU : V ≤ U.map mk := hRC.sylow_eq ▸ inf_le_left
  have hZV : Zc ≤ V := inf_le_left
  have hZcT : (centerOf (T₁ : Subgroup KC)).map KC.subtype = Zc := by
    rw [map_subtype_centerOf, hT₁]
  obtain ⟨hT6, hTder, -, hppd⟩ := hTF.pair hn2
  obtain ⟨c, hcN, hco, hc1⟩ := hppd 5 (by norm_num) (by norm_num)
    (fun k hk0 hk4 => by interval_cases k <;> norm_num)
  obtain ⟨⟨u, hu, hcu⟩, hcV⟩ := hc1 1 (by norm_num)
  simp only [pow_one] at hcu hcV
  have hc'V : (c : D1CzQuot 3 z) ∈ KC ⊓ Subgroup.normalizer (V : Set (D1CzQuot 3 z)) := by
    have := coe_mem_normalizer_map hcN
    rwa [hT₁] at this
  have hVder : ⁅V, V⁆ = Zc := by
    have h1 : (⁅(T₁ : Subgroup KC), (T₁ : Subgroup KC)⁆).map KC.subtype =
        (centerOf (T₁ : Subgroup KC)).map KC.subtype := congrArg _ hTder
    rw [Subgroup.map_commutator, hZcT, hT₁] at h1
    exact h1
  have hc'Z : (c : D1CzQuot 3 z) ∈ Subgroup.normalizer (Zc : Set (D1CzQuot 3 z)) := by
    rw [← hVder]
    exact mem_normalizer_commutator_of_mem_normalizer hc'V.2
  have hnt : ∃ v ∈ V, (c : D1CzQuot 3 z) * v * (c : D1CzQuot 3 z)⁻¹ * v⁻¹ ∉ Zc := by
    refine ⟨(u : D1CzQuot 3 z), by rw [← hT₁]; exact ⟨u, hu, rfl⟩, fun hmem => hcu ?_⟩
    rw [← hZcT] at hmem
    obtain ⟨v, hv, hve⟩ := hmem
    have : v = c * u * c⁻¹ * u⁻¹ := Subtype.ext (by simpa using hve)
    rw [← this]
    exact hv
  have hlay : ∀ Y' : Subgroup (D1CzQuot 3 z), Zc ≤ Y' → Y' ≤ V →
      (c : D1CzQuot 3 z) ∈ Subgroup.normalizer (Y' : Set (D1CzQuot 3 z)) → Y' = Zc ∨ Y' = V := by
    intro Y' h1 h2 h3
    rw [← hZcT] at h1 ⊢
    rw [← hT₁] at h2 ⊢
    exact eq_or_eq_of_map_subtype_layer KC hcV h1 h2 h3
  obtain ⟨t, htB, hmt, htW, htA, ⟨w, hw, hwnt⟩, hlayC⟩ := exists_lift_layer Nat.prime_three O hOC
    hUp hOB hZV hVU (hNV hc'V) hc'V.2 hc'Z hnt hlay
  have ht5 : t ^ 5 ∈ O := by
    have h1 : mk (t ^ 5) = 1 := by
      rw [map_pow, hmt, ← Subgroup.coe_pow, ← hco, pow_orderOf_eq_one, Subgroup.coe_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hA₀W₀ : U ⊓ Zc.comap mk ≤ U ⊓ V.comap mk := inf_le_inf_left _ (Subgroup.comap_mono hZV)
  refine ⟨(t : G), Subgroup.map_mono hA₀W₀, (hUp.to_le inf_le_left).map C.subtype, ?_, ?_, ?_,
    ⟨t.2, (Subgroup.mem_subgroupOf.mp htB).2⟩,
    Subgroup.le_normalizer_map C.subtype (Subgroup.mem_map_of_mem _ htW),
    Subgroup.le_normalizer_map C.subtype (Subgroup.mem_map_of_mem _ htA), ?_, ?_,
    fun Y hXY hYW htY => eq_or_eq_of_map_subtype_layer C hlayC hXY hYW htY⟩
  · change Nat.card ((U ⊓ V.comap mk).map C.subtype) = 3 ^ 6
    rw [Subgroup.card_map_of_injective C.subtype_injective,
      card_inf_comap_eq Nat.prime_three O hOC hUp hVU, ← hT₁,
      Subgroup.card_map_of_injective KC.subtype_injective, hT6]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨w', hw', rfl⟩
    exact congrArg Subtype.val (inf_comap_commute Nat.prime_three O hOC hUp (Z' := Zc) (V' := V)
      (fun a ha v hv => (Subgroup.mem_centralizer_iff.mp ha.2 v hv).symm) a ha w' hw')
  · change (U ⊓ Zc.comap mk).map C.subtype ≤
      ⁅(U ⊓ V.comap mk).map C.subtype, (U ⊓ V.comap mk).map C.subtype⁆
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono
      (inf_comap_le_commutator Nat.prime_three O hOC hUp (hZV.trans hVU) hVU hVder.ge)
  · rw [Subgroup.orderOf_coe]
    exact coprime_six_orderOf_of_pow_mem ht5 hOodd hOC
  · refine ⟨(w : G), Subgroup.mem_map_of_mem _ hw, ?_⟩
    rintro ⟨a, ha, hae⟩
    apply hwnt
    have : a = t * w * t⁻¹ * w⁻¹ := Subtype.ext (by simpa using hae)
    rw [← this]
    exact ha

variable {P : Sylow 3 G} {H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.exists_torus_pair_cz (hβ : KFactBeta) (hTor : KFactOneLieTorus)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hz : D1SmallCZElt 3 H R K z)
    (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z) :
    ∃ (n e : ℕ) (X : Subgroup G) (φ : Multiplicative (GaloisField 3 n) ≃* X),
      2 ≤ n ∧ (e = 1 ∨ (e = 2 ∧ 3 ≤ n)) ∧ X ≤ Subgroup.centralizer ({z} : Set G) ⊓ M ∧
      (∀ μ : (GaloisField 3 n)ˣ, ∃ t ∈ Subgroup.centralizer ({z} : Set G) ⊓ M,
        ∀ a : Multiplicative (GaloisField 3 n), t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ e * Multiplicative.toAdd a))) ∧
      (n = 2 → ∃ (W : Subgroup G) (t : G), X ≤ W ∧
        W ≤ Subgroup.centralizer ({z} : Set G) ⊓ M ∧ IsPGroup 3 W ∧ Nat.card W = 3 ^ 6 ∧
        (∀ x ∈ X, ∀ w ∈ W, x * w = w * x) ∧ X ≤ ⁅W, W⁆ ∧
        t ∈ Subgroup.centralizer ({z} : Set G) ⊓ M ∧ t ∈ Subgroup.normalizer (W : Set G) ∧
        t ∈ Subgroup.normalizer (X : Set G) ∧ Nat.Coprime 6 (orderOf t) ∧
        (∃ u ∈ W, t * u * t⁻¹ * u⁻¹ ∉ X) ∧
        ∀ Y : Subgroup G, X ≤ Y → Y ≤ W → t ∈ Subgroup.normalizer (Y : Set G) →
          Y = X ∨ Y = W) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨P', Pbar, KC, -, hP'M, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hmk
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  have hzK : mk ⟨z, hzC⟩ ∉ KC := hout KC hRC.comp
  obtain ⟨-, hs, hnab, hcat, hbig, hnc, T₁, hT₁, hTnc, hΓ⟩ :=
    hRC.red.exists_sylow_facts_of_not_mem hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp
      hRC.normal hzK hβ
  obtain ⟨n, e, hTF⟩ := hTor KC hs hnab hcat 3 (by norm_num) T₁ hTnc hΓ hbig
  have hzPbar : mk ⟨z, hzC⟩ ∈ (Pbar : Subgroup (D1CzQuot 3 z)) := by
    rw [hRC.sylow_eq]
    exact ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr (hRP' hz.1), rfl⟩
  have hzc : mk ⟨z, hzC⟩ ∈ Subgroup.centralizer (KC : Set (D1CzQuot 3 z)) :=
    Subgroup.mem_centralizer_iff.mpr fun k _ => Subgroup.mem_center_iff.mp hzZ k
  obtain ⟨hN, -⟩ := hRC.red.rankOne_principle hRC.comp hnc hzPbar hzK hzp hzc
  have hV1 : (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC ≠ ⊥ := fun hb => hnc (by rw [hb]; infer_instance)
  have hNV := hN _ le_rfl hV1
  have hcore : GLBPrimeCore 3 C ≤ M :=
    intersecting_local_primeCore_le 3 hp3 P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      (hd.cfg.ext.three_le_pRank.trans
        (pRank_mono 3 hp3 (le_inf (hd.le_centralizer_czElt hz) hd.cfg.ext.le_M)))
  have hOB : primeComplementCore (G := C) 3 ≤ (C ⊓ M).subgroupOf C := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hcore
  obtain ⟨φ, htor⟩ := exists_torus_czLift hRC hOB hNV hT₁ hTF
  refine ⟨n, e, _, φ, hTF.two_le, hTF.e_cases, czLift_le hP'M _, htor, fun hn2 => ?_⟩
  obtain ⟨t, ht⟩ := exists_pair_czLift hRC hOB (hd.odd_card_primeComplementCore_cz hz hSP)
    hNV hT₁ hTF hn2
  exact ⟨_, t, ht.1, czLift_le hP'M _, ht.2⟩

end CFSG.AGLEmbedding
