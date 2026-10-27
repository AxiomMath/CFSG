module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL7Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL7A
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL7Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshNormalizerE
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshCentralizerEq
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshIndexTwo

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

theorem l7Check_parts {α k : ℕ} (h : l7Check α k = true) :
    l7Fusion (nEnum α k) (goodTabs α k) (nwT α k eWord) (nwT α k uWord)
        (tenum (wgens α k eWords)).toList = true ∧
      l7Sylow (nwT α k cWord) (nwT α k eWord) (nwT α k uWord) (tenum (wgens α k eWords)).toList
        (tenum (wgens α k sWords)).toList = true ∧
      l7A (badTabs α k) (nwT α k cWord) (wgens α k aWords) (tenum (wgens α k eWords)).toList
        (tenum (wgens α k sWords)).toList = true ∧
      l7V (nEnum α k) (wgens α k vWords) = true ∧ ∀ c ∈ badChains α k, c.1 = [1, 1] := by
  unfold l7Check at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem factorization_two_pow_seven_mul : (2 ^ 7 * 1485 : ℕ).factorization 2 = 7 := by
  rw [Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

section Lemma7

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}

set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

theorem ESFacts.conj_c {E : NEmb e₀ d α k} (F : ESFacts E) {ℓ : G}
    (hℓ : ℓ ∈ normalizer (EG E : Set G)) : ℓ * cG e₀ * ℓ⁻¹ = cG e₀ := by
  have hgE := conj_mem_of_mem_normalizer hℓ
  have hinv := conj_inv_mem_of_mem_normalizer hℓ
  have hc'E : ℓ * cG e₀ * ℓ⁻¹ ∈ EG E := hgE _ F.cE
  have hcen : ∀ x ∈ EG E, (ℓ * cG e₀ * ℓ⁻¹) * x = x * (ℓ * cG e₀ * ℓ⁻¹) := by
    intro x hx
    have hx' : ℓ⁻¹ * x * ℓ ∈ EG E := hinv x hx
    have h := F.cSZ _ (F.ES hx')
    calc (ℓ * cG e₀ * ℓ⁻¹) * x = ℓ * (cG e₀ * (ℓ⁻¹ * x * ℓ)) * ℓ⁻¹ := by group
      _ = ℓ * ((ℓ⁻¹ * x * ℓ) * cG e₀) * ℓ⁻¹ := by rw [h]
      _ = x * (ℓ * cG e₀ * ℓ⁻¹) := by group
  rcases F.ZE _ hc'E hcen with h | h
  · exfalso
    apply cG_ne_one e₀
    have : cG e₀ = ℓ⁻¹ * (ℓ * cG e₀ * ℓ⁻¹) * ℓ := by group
    rw [this, h]; group
  · exact h

structure L7Out (E : NEmb e₀ d 1 k) : Prop where
  sylow : Nat.card (SG E) = 2 ^ (Nat.card G).factorization 2
  fusion : L7Fusion E
  fixes_c : ∀ ℓ ∈ normalizer (EG E : Set G), ℓ * cG e₀ * ℓ⁻¹ = cG e₀
  card : Nat.card (normalizer (EG E : Set G)) = 2 ^ 7 * 168
  fuse_u : ∃ ℓ ∈ normalizer (EG E : Set G), ℓ * e * ℓ⁻¹ = uG E
  fuse_ue : ∃ ℓ ∈ normalizer (EG E : Set G), ℓ * e * ℓ⁻¹ = uG E * e
  sq_u : uG E * uG E = 1
  gl : ∀ [((EG E).subgroupOf (normalizer (EG E : Set G))).Normal],
    Nonempty (↥(normalizer (EG E : Set G)) ⧸ (EG E).subgroupOf (normalizer (EG E : Set G)) ≃*
      GL (Fin 3) (ZMod 2))
  perf : ⁅normalizer (EG E : Set G), normalizer (EG E : Set G)⁆ = normalizer (EG E : Set G)
  zl : ∀ z ∈ normalizer (EG E : Set G),
    (∀ ℓ ∈ normalizer (EG E : Set G), ⁅z, ℓ⁆ ∈ EG E) → z ∈ EG E

theorem yosh7_model [Finite G] (hG : IsSimpleGroup G) (D : FusionData 1 k) (E : NEmb e₀ d 1 k)
    (he2 : orderOf e = 2) (hd : CentralSwap e₀ 1 d) (hue : ueCheck 1 k = true)
    (hes : esCheck 1 k = true) (hl7 : l7Check 1 k = true) : L7Out E := by
  obtain ⟨hfus, hsyl, hA, hV, hbad⟩ := l7Check_parts hl7
  have F := esFacts D E hue hes
  have Fu := l7Fusion_spec D E he2 hue hfus
  have Sy := l7Sylow_spec D E he2 hue hsyl
  have Ay := l7A_spec D E he2 hue hbad hA
  haveI := hG
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hee : e * e = 1 := mul_self_eq_one_of_orderOf_eq_two he2
  have hna : ∃ a b : G, a * b ≠ b * a := ⟨d, e, not_commute_d_e hd⟩
  have hfac : (Nat.card G).factorization 2 = 10 :=
    factorization_eq_ten hna hee (Nn e₀) (card_Nn e₀ he2 hd)
      (by rw [card_cent_e e₀]; norm_num) ((card_isConj_e D E he2).trans rfl)
  have hsylow : Nat.card (SG E) = 2 ^ (Nat.card G).factorization 2 := by
    rw [F.cardS, hfac]; norm_num
  have hcc : cG e₀ * cG e₀ = 1 := cG_sq e₀
  have hc1 : cG e₀ ≠ 1 := cG_ne_one e₀
  have hSle : SG E ≤ centralizer ({cG e₀} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (F.cSZ s hs)
  have hSyl_c : Nat.card (SG E) =
      2 ^ (Nat.card (centralizer ({cG e₀} : Set G))).factorization 2 :=
    card_eq_two_pow_of_le _ _ hSle hsylow
  have heE : e ∈ EG E := e_mem_EG D E he2 hue
  have hec : e * cG e₀ = cG e₀ * e := (cG_comm_e e₀).symm
  have hdN : d ∈ Nn e₀ := by
    have := gen5_d_mem (β := 1) e₀ he2 hd
    rwa [gen5_d] at this
  have hdL : d ∈ normalizer (EG E : Set G) :=
    mem_normalizer_of_conj_mem _ d (F.EN d hdN)
  have hTSyl : Nat.card (SG E ⊓ centralizer ({e} : Set G) : Subgroup G) =
      2 ^ (Nat.card (centralizer ({e} : Set G))).factorization 2 := by
    rw [Sy.cardT, card_cent_e e₀, factorization_two_pow_seven_mul]
    norm_num
  have hRuniq : ∀ D' : Subgroup G, D' ≤ SG E ⊓ centralizer ({e} : Set G) →
      Nat.card D' = Nat.card (EG E ⊓ centralizer ({e} : Set G) : Subgroup G) →
      (∀ y ∈ D', y * y = 1 ∨ y * y = cG e₀) →
      (∀ y ∈ D', ∀ z ∈ D', ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = cG e₀) →
      D' = EG E ⊓ centralizer ({e} : Set G) := by
    intro D' hD'T hD'card hsq hcomm
    refine index_two_unique (SG E ⊓ centralizer ({e} : Set G))
      (EG E ⊓ centralizer ({e} : Set G)) D' (cG e₀) (inf_le_inf_right _ F.ES) hD'T
      (by rw [Sy.cardT, Sy.cardR]) hD'card hsq hcomm ?_
    intro y hyT hyR hysq
    have := Sy.Runiq y hyT hyR hysq
    rwa [Sy.cardR]
  have fuse : ∀ x : G, x ∈ EG E → IsConj e x →
      Nat.card (SG E ⊓ centralizer ({x} : Set G) : Subgroup G) = 128 →
      Nat.card (EG E ⊓ centralizer ({x} : Set G) : Subgroup G) = 64 →
      ∃ ℓ ∈ normalizer (EG E : Set G), ℓ * x * ℓ⁻¹ = e ∨ ℓ * x * ℓ⁻¹ = e * cG e₀ := by
    intro x hxE hxconj hSx hEx
    have hxc : x ≠ cG e₀ := fun h =>
      not_isConj_e_of_isSq e₀ he2 (cG_isSq e₀) (h ▸ hxconj)
    obtain ⟨g, hg⟩ := isConj_iff.1 hxconj
    exact fuse_into_normalizer (cG e₀) e x (EG E) (SG E) (EG E ⊓ centralizer ({e} : Set G))
      (SG E ⊓ centralizer ({e} : Set G)) (SG E ⊓ centralizer ({x} : Set G)) hc1 F.cE F.ES
      F.cSZ hSyl_c F.sq F.comm
      (fun D' hD' hc hsq hcm => F.uniq D' hD' (by rw [hc, F.cardE]) hsq hcm) heE hec rfl
      (inf_le_inf_right _ F.ES)
      (fun y hy => mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2) hTSyl
      (by rw [Sy.cardT, Sy.cardR]) Sy.ZT Sy.ZR hRuniq (not_isSq_e e₀ he2) (cG_isSq e₀)
      ⟨d, hd.conj_e⟩ hxE hxc ⟨g⁻¹, by rw [← hg]; group⟩
      (fun y hy => mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2)
      (fun y hy => F.cSZ y (Subgroup.mem_inf.1 hy).1) (by rw [hSx, Sy.cardT])
      (fun y hy hyx => Subgroup.mem_inf.2 ⟨F.ES hy, mem_centralizer_singleton_iff.2 hyx⟩)
      (by rw [hEx, Sy.cardR])
  have hu2 : uG E * uG E = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (by rw [orderOf_isConj Fu.uConj, he2])
  obtain ⟨ℓu, hℓu, hu⟩ := fuse (uG E) Fu.uE Fu.uConj Sy.cardSu Sy.cardEu
  obtain ⟨ℓue, hℓue, hue'⟩ := fuse (uG E * e) Fu.ueE Fu.ueConj Sy.cardSue Sy.cardEue
  have hfu : ∃ ℓ ∈ normalizer (EG E : Set G), ℓ * e * ℓ⁻¹ = uG E :=
    exists_conj_of_fusion _ e (cG e₀) d (uG E) hdL hd.conj_e ⟨ℓu, hℓu, hu⟩
  have hfue : ∃ ℓ ∈ normalizer (EG E : Set G), ℓ * e * ℓ⁻¹ = uG E * e :=
    exists_conj_of_fusion _ e (cG e₀) d (uG E * e) hdL hd.conj_e ⟨ℓue, hℓue, hue'⟩
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, L = normalizer (EG E : Set G) := ⟨_, rfl⟩
  have hLmem : ∀ ℓ, ℓ ∈ L ↔ ℓ ∈ normalizer (EG E : Set G) := fun ℓ => by rw [hL]
  have hLE : ∀ ℓ ∈ L, ∀ x ∈ EG E, ℓ * x * ℓ⁻¹ ∈ EG E := fun ℓ hℓ =>
    conj_mem_of_mem_normalizer ((hLmem ℓ).1 hℓ)
  have hLc : ∀ ℓ ∈ L, ℓ * cG e₀ * ℓ⁻¹ = cG e₀ := fun ℓ hℓ => F.conj_c ((hLmem ℓ).1 hℓ)
  have hSL : SG E ≤ L := fun s hs =>
    (hLmem s).2 (mem_normalizer_of_conj_mem _ s (F.SN s hs))
  have hEL : EG E ≤ L := F.ES.trans hSL
  have hNL : Nn e₀ ≤ L := fun n hn =>
    (hLmem n).2 (mem_normalizer_of_conj_mem _ n (F.EN n hn))
  have hfu' : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = uG E := by
    obtain ⟨ℓ, hℓ, h⟩ := hfu
    exact ⟨ℓ, (hLmem ℓ).2 hℓ, h⟩
  have hfue' : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = uG E * e := by
    obtain ⟨ℓ, hℓ, h⟩ := hfue
    exact ⟨ℓ, (hLmem ℓ).2 hℓ, h⟩
  have horb : conjOrbit L e = {y : G | y ∈ EG E ∧ IsConj e y} := by
    refine Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨ℓ, hℓ, rfl⟩ := mem_conjOrbit.1 hy
      exact ⟨hLE ℓ hℓ e heE, isConj_iff.2 ⟨ℓ, rfl⟩⟩
    · obtain ⟨hyE, hyconj⟩ := hy
      rcases Fu.cover y hyE hyconj with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
      · exact mem_conjOrbit.2 ⟨n, hNL hn, rfl⟩
      · obtain ⟨ℓ, hℓ, hℓu⟩ := hfu'
        exact mem_conjOrbit.2 ⟨n * ℓ, L.mul_mem (hNL hn) hℓ, by rw [← hℓu]; group⟩
      · obtain ⟨ℓ, hℓ, hℓu⟩ := hfue'
        exact mem_conjOrbit.2 ⟨n * ℓ, L.mul_mem (hNL hn) hℓ, by rw [← hℓu]; group⟩
  have hLC : Nat.card (L ⊓ centralizer ({e} : Set G) : Subgroup G) = 384 := by
    have : L ⊓ centralizer ({e} : Set G) = HcG e₀ := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyL, hye⟩ := Subgroup.mem_inf.1 hy
        refine Subgroup.mem_inf.2 ⟨hye, mem_centralizer_singleton_iff.2 ?_⟩
        have := hLc y hyL
        rwa [mul_inv_eq_iff_eq_mul] at this
      · intro hy
        obtain ⟨hye, -⟩ := Subgroup.mem_inf.1 hy
        exact Subgroup.mem_inf.2 ⟨hNL (HcG_le_Nn e₀ hy), hye⟩
    rw [this]
    exact card_HcG e₀
  have hcardL : Nat.card L = 168 * Nat.card (EG E) := by
    have h := ncard_conjOrbit_mul_card L e
    rw [horb, hLC] at h
    have h56 : ({y : G | y ∈ EG E ∧ IsConj e y} : Set G).ncard = 56 := by
      rw [← Nat.card_coe_set_eq]
      exact Fu.card56
    rw [h56] at h
    rw [F.cardE, ← h]
  have hgen : ∀ y ∈ EG E, y ∈ Subgroup.closure {z : G | ∃ ℓ ∈ L, z = ℓ * e * ℓ⁻¹} := by
    intro y hy
    refine Subgroup.closure_mono ?_ (Fu.gen y hy)
    rintro z ⟨hzE, hzconj⟩
    have : z ∈ conjOrbit L e := by rw [horb]; exact ⟨hzE, hzconj⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_conjOrbit.1 this
    exact ⟨ℓ, hℓ, rfl⟩
  have hAmem : cG e₀ ∈ AG E ∧ v1G E ∈ AG E ∧ v2G E ∈ AG E ∧ d ∈ AG E := by
    rw [Ay.eq]
    exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
      Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩
  have hLA : ∀ ℓ ∈ L, ∀ a ∈ AG E, ℓ * a * ℓ⁻¹ ∈ AG E := by
    intro ℓ hℓ a ha
    have key : ∀ a ∈ Subgroup.closure ({cG e₀, v1G E, v2G E, d} : Set G),
        ℓ * a * ℓ⁻¹ ∈ AG E := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem g hg =>
        have hgA : g ∈ AG E := by
          rw [Ay.eq]; exact Subgroup.subset_closure hg
        have hgconj : IsConj (cG e₀) g := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl | rfl
          · exact Ay.gens.1
          · exact Ay.gens.2.1
          · exact Ay.gens.2.2.1
          · exact Ay.gens.2.2.2
        exact Ay.cls _ (hLE ℓ hℓ g (Ay.le hgA)) (hgconj.trans (isConj_iff.2 ⟨ℓ, rfl⟩))
      | one => simpa using (AG E).one_mem
      | mul x y _ _ hx hy =>
        have := (AG E).mul_mem hx hy
        simpa [mul_assoc] using this
      | inv x _ hx =>
        have := (AG E).inv_mem hx
        simpa [mul_assoc] using this
    exact key a (by rw [← Ay.eq]; exact ha)
  have hCe : ∀ y : G, (∀ a ∈ AG E, y * a = a * y) → y * e = e * y → Odd (orderOf y) → y = 1 := by
    intro y hyA hye hodd
    have hyc : y * cG e₀ = cG e₀ * y := hyA _ hAmem.1
    have hyN : y ∈ Nn e₀ := HcG_le_Nn e₀ (Subgroup.mem_inf.2
      ⟨mem_centralizer_singleton_iff.2 hye, mem_centralizer_singleton_iff.2 hyc⟩)
    exact eq_one_of_odd_orderOf_of_mul_self
      (l7V_spec D E he2 hV hyN hyc (hyA _ hAmem.2.1) (hyA _ hAmem.2.2.1) hye) hodd
  have hCA : ∀ y : G, (∀ a ∈ AG E, y * a = a * y) → y ∈ AG E :=
    centralizer_eq_of_fourGroup (AG E) (SG E) L e (uG E) Ay.comm (Ay.le.trans F.ES) hSL hLA
      hsylow Ay.hCS (hEL heE) (hEL Fu.uE) hee hu2 Fu.euComm hCe hfu' hfue'
  obtain ⟨hgl, hperf, hzl⟩ := normalizer_quotient_gl3 (EG E) (SG E) (AG E) L (cG e₀) e (uG E)
    (v1G E) (v2G E) d hL hsylow F.ES hSL F.cE F.comm hLc Ay.eq Ay.le Ay.card Ay.sq hLA hCA
    (fun y hy a ha => F.comm y hy a (Ay.le ha)) Ay.hSA hcardL heE Fu.uE hee hu2 Fu.euComm
    hfu' hfue' hgen
  subst hL
  refine ⟨hsylow, Fu, hLc, ?_, hfu, hfue, hu2, fun {_} => hgl, hperf, hzl⟩
  rw [hcardL, F.cardE]
  norm_num

end Lemma7

end CFSG.EvenSporadicStandard.M12Std.Yosh
