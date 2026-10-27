module

public import CFSG.CharacterTheory.Semidihedral.EscapingCentralizerStatement
public import CFSG.CharacterTheory.Semidihedral.EscapingCentralizerTwoPart

public noncomputable section

namespace CFSG.Semidihedral.EscapingCentralizer

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOddExtensions
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem fixed_image_sylow_of_card [Finite G] (i : G) (p f : ℕ) [Fact p.Prime]
    (hcard : ∀ S : Sylow p (FullRootSylowCentralizers.originalT0 i),
      Nat.card (FullRootSylowCentralizers.originalSylowImage i p S) = p ^ f)
    (Pi : Subgroup (H i)) (hPT : Pi ≤ FullRootSylowCentralizers.originalT0 i)
    (hPcard : Nat.card Pi = p ^ f) :
    ∃ S : Sylow p (FullRootSylowCentralizers.originalT0 i),
      FullRootSylowCentralizers.originalSylowImage i p S = Pi := by
  let T := FullRootSylowCentralizers.originalT0 i
  let P0 := Pi.subgroupOf T
  have hP0card : Nat.card P0 = p ^ f :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv).trans hPcard
  have hP0 : IsPGroup p P0 := IsPGroup.of_card hP0card
  obtain ⟨S, hS⟩ := hP0.exists_le_sylow
  have hScard : Nat.card (S : Subgroup T) = p ^ f := by
    have h := hcard S
    change Nat.card ((S : Subgroup T).map T.subtype) = p ^ f at h
    rwa [Subgroup.card_map_of_injective T.subtype_injective] at h
  have hEq : P0 = S := Subgroup.eq_of_le_of_card_ge hS (by rw [hScard, hP0card])
  refine ⟨S, ?_⟩
  change (S : Subgroup T).map T.subtype = Pi
  rw [← hEq]
  exact Subgroup.map_subgroupOf_eq_of_le hPT

theorem fixed_image_centralizer_facts [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (i : G) (hi : orderOf i = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (Pi : Subgroup (H i)) (hPT : Pi ≤ FullRootSylowCentralizers.originalT0 i)
    (hPcard : Nat.card Pi = p ^ f) :
    (∃ S : Sylow p ((localLayerPreimage i).map (nu i)),
      (S : Subgroup ((localLayerPreimage i).map (nu i))).map
        ((localLayerPreimage i).map (nu i)).subtype = Pi) ∧
    Subgroup.centralizer (Pi : Set (H i)) = Pi ⊔ Subgroup.zpowers (nu i (tInC i)) ∧
    Disjoint Pi (Subgroup.zpowers (nu i (tInC i))) ∧ orderOf (nu i (tInC i)) = 2 ∧
    nu i (tInC i) ∈ Subgroup.center (H i) ∧
    ∃ e : Pi × Subgroup.zpowers (nu i (tInC i)) ≃* Subgroup.centralizer (Pi : Set (H i)),
      ∀ x : Pi × Subgroup.zpowers (nu i (tInC i)), (e x : H i) = (x.1 : H i) * (x.2 : H i) := by
  let : Fact p.Prime := ⟨hp⟩
  have hall (S : Sylow p (FullRootSylowCentralizers.originalT0 i)) :=
    FullRootSylowCentralizers.original_simple_full_root_sylow_centralizer
      hGnonab n hn S0 f0 i hi hnonab hcentral hnc p f hp hpodd hf hq hmodel S
  have hcard (S : Sylow p (FullRootSylowCentralizers.originalT0 i)) :
      Nat.card (FullRootSylowCentralizers.originalSylowImage i p S) = p ^ f :=
    (hall S).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨S, hS⟩ := fixed_image_sylow_of_card i p f hcard Pi hPT hPcard
  obtain ⟨-, hzorder, hzcenter, -, -, -, -, hdisj, -, hcent, -, ⟨e, he, -⟩, -⟩ := hall S
  have hYq : (localLayerPreimage i).map (nu i) = FullRootSylowCentralizers.originalT0 i :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  subst hS
  refine ⟨?_, hcent, hdisj, hzorder, hzcenter, e, fun x => he x.1 x.2⟩
  rw [hYq]
  exact ⟨S, rfl⟩

theorem fixed_centralizer_no_centralizing_four [Finite G] (i : G) (Wi : Subgroup G)
    (hWC : Wi ≤ C i) {p f : ℕ} (hpodd : Odd p)
    (hcent : Nat.card (Subgroup.centralizer
      (((Wi.subgroupOf (C i)).map (nu i) : Subgroup (H i)) : Set (H i))) = p ^ f * 2) :
    ∃ hiK : i ∈ Subgroup.centralizer (Wi : Set G),
      ∀ Q : Subgroup (Subgroup.centralizer (Wi : Set G)), Nat.card Q = 4 →
        ¬ Q ≤ Subgroup.centralizer
          ({⟨i, hiK⟩} : Set (Subgroup.centralizer (Wi : Set G))) := by
  let K := Subgroup.centralizer (Wi : Set G)
  let Pi := (Wi.subgroupOf (C i)).map (nu i)
  have hiK : i ∈ K := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hWC hw)
  refine ⟨hiK, ?_⟩
  intro Q hQ hQC
  let Qa := Q.map K.subtype
  have hQa : Nat.card Qa = 4 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hQ]
  have hQaC : Qa ≤ C i := by
    rintro x ⟨q, hq, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  let Qc := Qa.subgroupOf (C i)
  have hQc : Nat.card Qc = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQaC).toEquiv).trans hQa
  have hNodd : Odd (Nat.card (N i)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C i))
  have hcop : Nat.Coprime 4 (Nat.card (N i)) := by
    have h := (Nat.coprime_two_left.mpr hNodd).pow_left 2
    norm_num at h
    exact h
  have hinj : Function.Injective ((nu i).comp Qc.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxN : (x : C i) ∈ N i := (QuotientGroup.eq_one_iff (N := N i) (x : C i)).mp hx
    have h1 : orderOf (x : C i) ∣ Nat.card (N i) := (N i).orderOf_dvd_natCard hxN
    have h2 : orderOf (x : C i) ∣ 4 := by
      rw [Subgroup.orderOf_coe, ← hQc]
      exact orderOf_dvd_natCard x
    have h3 : orderOf x = 1 := by
      rw [← Subgroup.orderOf_coe]
      exact Nat.eq_one_of_dvd_coprimes hcop h2 h1
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)
  have himage : Nat.card (Qc.map (nu i)) = 4 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
    rw [← h, hQc]
  have himage_le : Qc.map (nu i) ≤ Subgroup.centralizer (Pi : Set (H i)) := by
    rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro v ⟨w, hw, rfl⟩
    have hxK : (x : G) ∈ K := Subgroup.map_subtype_le Q (Subgroup.mem_subgroupOf.mp hx)
    have hcomm : (w : G) * (x : G) = (x : G) * (w : G) :=
      Subgroup.mem_centralizer_iff.mp hxK (w : G) (Subgroup.mem_subgroupOf.mp hw)
    rw [← map_mul, ← map_mul]
    exact congrArg (nu i) (Subtype.ext hcomm)
  have hdvd : 4 ∣ p ^ f * 2 := by
    rw [← hcent, ← himage]
    exact Subgroup.card_dvd_of_le himage_le
  have h2 : 2 ∣ p ^ f := by
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hpodd.pow) (even_iff_two_dvd.mpr h2)

theorem commutator_le_oddCore_of_index_two [Finite G] (K : Subgroup G) (i : G) (hiK : i ∈ K)
    (hindex : (CFSG.pPrimeCore 2 K).index = 2) :
    ⁅K, Subgroup.zpowers i⁆ ≤ (CFSG.pPrimeCore 2 K).map K.subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : Nat.card (K ⧸ CFSG.pPrimeCore 2 K) = 2 := hindex
  have hcyc : IsCyclic (K ⧸ CFSG.pPrimeCore 2 K) := isCyclic_of_prime_card hq2
  have hcomm : IsMulCommutative (K ⧸ CFSG.pPrimeCore 2 K) := IsCyclic.isMulCommutative
  apply original_odd_core_centrality_controls_subgroup_commutators K K le_rfl i hiK
  exact Subgroup.mem_center_iff.mpr fun g => hcomm.is_comm.comm g _

theorem trivial_odd_intersection_local_conclusions [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (i : G) (hi : orderOf i = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (Wi : Subgroup G) (hWC : Wi ≤ C i) (hWY : Wi ≤ (localLayerPreimage i).map (C i).subtype)
    (hWN : Wi ⊓ (N i).map (C i).subtype = ⊥) (hWcard : Nat.card Wi = p ^ f) :
    let Pi := (Wi.subgroupOf (C i)).map (nu i)
    let Yq := (localLayerPreimage i).map (nu i)
    let z := nu i (tInC i)
    let K := Subgroup.centralizer (Wi : Set G)
    Pi ≤ Yq ∧ Nat.card Pi = p ^ f ∧
    (∃ S : Sylow p Yq, (S : Subgroup Yq).map Yq.subtype = Pi) ∧
    Subgroup.centralizer (Pi : Set (H i)) = Pi ⊔ Subgroup.zpowers z ∧
    Disjoint Pi (Subgroup.zpowers z) ∧ orderOf z = 2 ∧ z ∈ Subgroup.center (H i) ∧
    (∃ e : Pi × Subgroup.zpowers z ≃* Subgroup.centralizer (Pi : Set (H i)),
      ∀ x : Pi × Subgroup.zpowers z, (e x : H i) = (x.1 : H i) * (x.2 : H i)) ∧
    (Nat.card K).factorization 2 = 1 ∧ (∀ S : Sylow 2 K, Nat.card (S : Subgroup K) = 2) ∧
    (∃ M : Subgroup K, M.Normal ∧ Odd (Nat.card M) ∧ M.index = 2 ∧
      M = CFSG.pPrimeCore 2 K) ∧
    ⁅K, Subgroup.zpowers i⁆ ≤ (CFSG.pPrimeCore 2 K).map K.subtype := by
  intro Pi Yq z K
  let Wc := Wi.subgroupOf (C i)
  have hWccard : Nat.card Wc = p ^ f :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv).trans hWcard
  have hinj : Function.Injective ((nu i).comp Wc.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxN : (x : C i) ∈ N i := (QuotientGroup.eq_one_iff (N := N i) (x : C i)).mp hx
    have hxbot : ((x : C i) : G) ∈ Wi ⊓ (N i).map (C i).subtype :=
      ⟨Subgroup.mem_subgroupOf.mp x.property, (x : C i), hxN, rfl⟩
    rw [hWN] at hxbot
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hxbot)))
  have hPcard : Nat.card Pi = p ^ f := by
    have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
    exact h.symm.trans hWccard
  have hYq : Yq = FullRootSylowCentralizers.originalT0 i :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hPY : Pi ≤ Yq := by
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp (hWY (Subgroup.mem_subgroupOf.mp hw))
    have hyw' : y = w := Subtype.ext hyw
    exact Subgroup.mem_map_of_mem (nu i) (hyw' ▸ hy)
  obtain ⟨hSyl, hcent, hdisj, hzorder, hzcenter, e, he⟩ :=
    fixed_image_centralizer_facts hGnonab n hn S0 f0 i hi hnonab hcentral hnc
      p f hp hpodd hf hq hmodel Pi (hPY.trans hYq.le) hPcard
  have hcentcard : Nat.card (Subgroup.centralizer (Pi : Set (H i))) = p ^ f * 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hPcard, Nat.card_zpowers, hzorder]
  obtain ⟨hiK, hfour⟩ := fixed_centralizer_no_centralizing_four i Wi hWC hpodd hcentcard
  have hik : orderOf (⟨i, hiK⟩ : K) = 2 := (Subgroup.orderOf_coe _).symm.trans hi
  have hSyl2 := sylow_two_card_eq_two_of_no_centralizing_four (⟨i, hiK⟩ : K) hik hfour
  obtain ⟨S2, -⟩ := (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup K)).exists_le_sylow
  obtain ⟨hfac, M, hMnormal, hModd, hMindex, hMeq⟩ :=
    odd_core_index_two_of_sylow_two_card_two S2 (hSyl2 S2)
  have hOindex : (CFSG.pPrimeCore 2 K).index = 2 := hMeq ▸ hMindex
  exact ⟨hPY, hPcard, hSyl, hcent, hdisj, hzorder, hzcenter, ⟨e, he⟩, hfac, hSyl2,
    ⟨M, hMnormal, hModd, hMindex, hMeq⟩,
    commutator_le_oddCore_of_index_two K i hiK hOindex⟩

theorem escaping_centralizer_conclusion_at
    [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t)
    (i : G) (hi : i = s ∨ i = t * s) :
    EscapingCentralizerConclusion t i (coveringOddSylowAmbient H W) ell p f := by
  let Wa := coveringOddSylowAmbient H W
  let Wi := localFixedGroup Wa i
  obtain ⟨hLift, U, hHall, -, -, hWC, hConcl, hinter, hnontriv⟩ :=
    original_escaping_fixed_factors_lie_in_actual_lift_and_hall
      hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape i hi
  obtain ⟨hJperf, hJnormal, -, hJsection, hJN, hYJN, -⟩ := hLift
  obtain ⟨-, -, -, -, hUmem, -, -, hUN, hUab, hUchar, hUhall, -⟩ := hHall
  obtain ⟨hWJU, hUK, -⟩ := hConcl
  have hYsection : (localLayerPreimage i).map (nu i) =
      (CFSG.generalizedFitting (Gamma i)).comap (barKappa i) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have htriv : Wi ⊓ U = ⊥ →
      EscapingTrivialFactorConclusion i Wa ell p f ∧
        ⁅Subgroup.centralizer (Wi : Set G), Subgroup.zpowers i⁆ ≤
          (CFSG.pPrimeCore 2 (Subgroup.centralizer (Wi : Set G))).map
            (Subgroup.centralizer (Wi : Set G)).subtype := by
    intro hF
    have hinter' : Wi ⊓ LocalProjectiveKernelQuotients.originalAmbientOddCore i = ⊥ :=
      hinter.trans hF
    obtain ⟨hellp, hWaEA, hWacard, hWiEA, hWicard⟩ :=
      original_escaping_trivial_odd_intersection_forces_defining_square_orders
        hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
        p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape i hi hinter'
    obtain ⟨-, -, -, -, hiorder, -, -, hsimple, hnonabi, hcentrali, hnci,
      -, -, -, -, hmodeli, -, -, -⟩ :=
      original_all_stationary_covers_produce_same_parameter_local_data
        hGnonab n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
        p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov i hi
    let : IsSimpleGroup (CFSG.generalizedFitting (Gamma i)) := hsimple
    have hWY : Wi ≤ (localLayerPreimage i).map (C i).subtype :=
      escaping_local_odd_sylow_fixed_factors_lie_in_original_layer_preimages
        hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
        p f hp hpodd hf (Nat.le_of_lt hq) hmodel hcov H hVH hJH hR hell hdiv W hVW hescape i hi
    obtain ⟨hPY, hPcard, hSyl, hcent, hdisj, hzorder, hzcenter, he, hfac, hSyl2, hM,
        hcomm⟩ :=
      trivial_odd_intersection_local_conclusions hGnonab n hn S0 f0 i hiorder
        hnonabi hcentrali hnci p f hp hpodd hf (Nat.le_of_lt hq) hmodeli
        Wi hWC hWY hinter' hWicard
    exact ⟨⟨hellp, hWaEA, hWacard, hWiEA, hWicard, hPY, hPcard, hSyl, hcent, hdisj,
      hzorder, hzcenter, he, hfac, hSyl2, hM⟩, hcomm⟩
  refine ⟨U, hUmem, hUN, hUab, hUchar, hUhall, hJperf, hJnormal, hJN, hYJN,
    hJsection.trans hYsection.symm, hWJU, hUK, ?_, fun hF => (htriv hF).1⟩
  by_cases hF : Wi ⊓ U = ⊥
  · exact (htriv hF).2
  · exact hnontriv hF

theorem escaping_eigensubgroup_centralizer_involution_is_central_modulo_odd_core
    [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hcov : allLocalPrimeStationaryCovers t s)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hJH : (localCentralizingLayer t).map (C t).subtype ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ Nat.card (CFSG.pPrimeCore 2 H))
    (W : Sylow ell (CFSG.pPrimeCore 2 H))
    (hVW : Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G))
    (hescape : ¬ coveringOddSylowAmbient H W ≤ C t) :
    ∀ i : G, i = s ∨ i = t * s →
      EscapingCentralizerConclusion t i (coveringOddSylowAmbient H W) ell p f :=
  fun i hi => escaping_centralizer_conclusion_at hGnonab hrecognition n hn S0 f0
    t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
    H hVH hJH hR hell hdiv W hVW hescape i hi

theorem escapingCentralizerStatement_holds
    : EscapingCentralizerStatement.{u} := by
  intro G _ _ _ hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts _ hnonab hcentral hnc
    p f hp hpodd hf hq hmodel hcov H hVH hJH hR ell hell hdiv W hVW hescape
  exact escaping_eigensubgroup_centralizer_involution_is_central_modulo_odd_core
    hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
    p f hp hpodd hf hq hmodel hcov H hVH hJH hR hell hdiv W hVW hescape

end CFSG.Semidihedral.EscapingCentralizer
