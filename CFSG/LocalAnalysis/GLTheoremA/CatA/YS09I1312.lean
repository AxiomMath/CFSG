module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I1312Lie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I1312Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I1312A8
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem i1312_q_eq {G : Type} [Group G] {p : ℕ} (I : Subgroup G) (a b : ↥I) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥I) a : PQuot p I) = QuotientGroup.mk' (GLAPPrimeCore p ↥I) b ↔
      (a : G)⁻¹ * (b : G) ∈ GLAPPrimeCoreOf p I := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    exact Subgroup.mem_map.2 ⟨a⁻¹ * b, h, by simp⟩
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
    have : y = a⁻¹ * b := Subtype.ext (by simpa using hyx)
    exact this ▸ hy

theorem i1312_barAut_mem {G : Type} [Group G] {p : ℕ} {I B S : Subgroup G} (hBN : B ≤ Subgroup.normalizer (I : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) {b : G} (hb : b ∈ B) (x : PQuot p I)
    (hx : x ∈ (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))) :
    barAut p I ⟨b, hBN hb⟩ x ∈ (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  show barAut p I ⟨b, hBN hb⟩ (QuotientGroup.mk y) ∈ _
  rw [barAut_mk]
  refine Subgroup.mem_map.2 ⟨I.normalizerMonoidHom ⟨b, hBN hb⟩ y, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf] at hy ⊢
  rw [chev_coe_normalizerMonoidHom]
  exact (Subgroup.mem_normalizer_iff.1 (hBS hb) (y : G)).1 hy

theorem i1312_comm_iff_fix {G : Type} [Group G] {p : ℕ} {I S : Subgroup G} (hSI : S ≤ I) {c : G}
    (hcN : c ∈ Subgroup.normalizer (I : Set G)) :
    (∀ s ∈ S, (⁅s, c⁆ : G) ∈ GLAPPrimeCoreOf p I) ↔
      ∀ x ∈ (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)),
        barAut p I ⟨c, hcN⟩ x = x := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyS : (y : G) ∈ S := Subgroup.mem_subgroupOf.1 hy
    show barAut p I ⟨c, hcN⟩ (QuotientGroup.mk y) = QuotientGroup.mk y
    rw [barAut_mk]
    have hmem : ((I.normalizerMonoidHom ⟨c, hcN⟩ y : ↥I) : G)⁻¹ * (y : G) ∈ GLAPPrimeCoreOf p I := by
      rw [chev_coe_normalizerMonoidHom]
      have e : (c * (y : G) * c⁻¹)⁻¹ * (y : G) = (⁅(y : G)⁻¹, c⁆)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (GLAPPrimeCoreOf p I).inv_mem (h _ (S.inv_mem hyS))
    exact (i1312_q_eq I _ _).2 hmem
  · intro h s hs
    have hsI : s ∈ I := hSI hs
    have hx : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨s⁻¹, I.inv_mem hsI⟩ : ↥I)) ∈
        (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) :=
      Subgroup.mem_map.2 ⟨⟨s⁻¹, I.inv_mem hsI⟩, Subgroup.mem_subgroupOf.2 (S.inv_mem hs), rfl⟩
    have h1 : barAut p I ⟨c, hcN⟩ (QuotientGroup.mk (⟨s⁻¹, I.inv_mem hsI⟩ : ↥I)) =
        QuotientGroup.mk (⟨s⁻¹, I.inv_mem hsI⟩ : ↥I) := h _ hx
    rw [barAut_mk] at h1
    have h2 := (i1312_q_eq I _ _).1 h1
    rw [chev_coe_normalizerMonoidHom] at h2
    have e : (c * (s⁻¹ : G) * c⁻¹)⁻¹ * s⁻¹ = (⁅s, c⁆ : G)⁻¹ := by
      rw [commutatorElement_def]
      group
    have h3 : (⁅s, c⁆ : G)⁻¹ ∈ GLAPPrimeCoreOf p I := by
      rw [← e]
      exact h2
    have h4 := (GLAPPrimeCoreOf p I).inv_mem h3
    simpa using h4

theorem i1312_card_Sbar_dvd {G : Type} [Group G] [Finite G] {p : ℕ} {I S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hS8 : Nat.card S ≤ 8) (hSI : S ≤ I) :
    Nat.card ↥((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))) ∣ 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSbarp : IsPGroup 2 ((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))) :=
    IsPGroup.map (i1312_isPGroup_subgroupOf hS2) _
  have hdvd : Nat.card ↥((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))) ∣
      Nat.card ↥(S.subgroupOf I) := Subgroup.card_map_dvd _ _
  have hSI_card : Nat.card ↥(S.subgroupOf I) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSI).toEquiv
  rw [hSI_card] at hdvd
  have hle : Nat.card ↥((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))) ≤ 8 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hS8
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hSbarp
  rw [hk] at hle ⊢
  have hk3 : k ≤ 3 := by
    by_contra h
    push_neg at h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  exact (Nat.pow_dvd_pow 2 hk3).trans (by norm_num)

theorem i1312_part2 {G : Type} [Group G] [Finite G] {p : ℕ} {I B S : Subgroup G} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hBel : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (I : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hSI : S ≤ I) (hS2 : IsPGroup 2 S)
    (hS8 : Nat.card S ≤ 8) :
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ Nat.card B ≤ p * Nat.card B₀ ∧
      ∀ c ∈ B₀, (⁅S, Subgroup.zpowers c⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hom0 : ↥B →* MulAut (PQuot p I) := (barAut p I).comp (Subgroup.inclusion hBN)
  have hinv : ∀ b : ↥B,
      ((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))).map (hom0 b).toMonoidHom =
        (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) := by
    intro b
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact i1312_barAut_mem hBN hBS b.2 x hx
    · exact (Subgroup.card_map_of_injective (f := (hom0 b).toMonoidHom)
        (MulEquiv.injective _)).symm.le
  have hcommB : ∀ x y : ↥B, x * y = y * x := fun x y => hBel.1.is_comm.comm x y
  obtain ⟨K, hKcard, hKtriv⟩ := i1312_exists_ker_card_le hp hp3 (isPGroup_of_isElemAbelian hBel) hcommB
    (i1312_card_Sbar_dvd (p := p) hS2 hS8 hSI)
    (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism hom0
      ((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))) hinv)
  refine ⟨K.map B.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hKcard
  · have hall : ∀ c ∈ K.map B.subtype, ∀ s ∈ S, (⁅s, c⁆ : G) ∈ GLAPPrimeCoreOf p I := by
      rintro _ ⟨k, hk, rfl⟩ s hs
      have hfix : ∀ x ∈ (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)),
          barAut p I ⟨(k : G), hBN k.2⟩ x = x := by
        intro x hx
        have h3 := congrArg (fun f : MulAut ↥((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))) =>
          ((f ⟨x, hx⟩ : ↥((S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)))) :
            PQuot p I)) (hKtriv k hk)
        simp only [CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism,
          CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_apply, hom0,
          MulAut.one_apply] at h3
        exact h3
      exact (i1312_comm_iff_fix hSI (hBN k.2)).2 hfix s hs
    intro c hc
    refine Subgroup.commutator_le.2 fun s hs t ht => ?_
    exact hall t (Subgroup.zpowers_le.2 hc ht) s hs

theorem i1312_part1 {G : Type} [Group G] [Finite G] {p : ℕ} {X I B S : Subgroup G}
    (hL : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQConstrained 2) (hA8 : I1312Alt8Constrained)
    (hp : p.Prime) (hp2 : p ≠ 2) (hI : GLAPComponent p X I) (hch : IsChevSimple 2 (PSimple p I))
    (hBel : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (I : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hSI : S ≤ I) (hS2 : IsPGroup 2 S)
    (hSO : ¬ S ≤ GLAPPrimeCoreOf p I)
    (hmax : ∀ S' : Subgroup G, S ≤ S' → S' ≤ I → IsPGroup 2 S' →
      B ≤ Subgroup.normalizer (S' : Set G) → ¬ S' ≤ GLAPPrimeCoreOf p I → S' = S)
    {c : G} (hc : c ∈ B) (hcS : (⁅S, Subgroup.zpowers c⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p I) :
    CentMod p I c := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hI
  have hperf : commutator (PQuot p I) = ⊤ := hq.1
  have hsimple : IsSimpleGroup (PSimple p I) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hcore0 : GLAPPrimeCore p (PQuot p I) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot (G := ↥I) hp
  have hZodd : Odd (Nat.card (Subgroup.center (PQuot p I))) := odd_card_center hp hp2 hcore0
  have hZcop : Nat.Coprime (Nat.card (Subgroup.center (PQuot p I))) 2 :=
    Nat.coprime_two_right.2 hZodd
  have hcN : c ∈ Subgroup.normalizer (I : Set G) := hBN hc
  have hcp : c ^ p = 1 := hBel.2 c hc
  have hcomm : ∀ s ∈ S, (⁅s, c⁆ : G) ∈ GLAPPrimeCoreOf p I :=
    fun s hs => hcS (Subgroup.commutator_mem_commutator hs (Subgroup.mem_zpowers c))
  have hfix := (i1312_comm_iff_fix (p := p) hSI hcN).1 hcomm
  have hαp : (barAut p I ⟨c, hcN⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hcp)
    rw [this, map_one]
  set Sbar : Subgroup (PQuot p I) := (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I))
    with hSbar
  have hSbarp : IsPGroup 2 Sbar := IsPGroup.map (i1312_isPGroup_subgroupOf hS2) _
  have hSbar_ne : Sbar ≠ ⊥ := by
    intro hbot
    apply hSO
    intro s hs
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) (⟨s, hSI hs⟩ : ↥I)) ∈ Sbar :=
      Subgroup.mem_map.2 ⟨⟨s, hSI hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 := (i1312_q_eq I ⟨s, hSI hs⟩ 1).1 (by rw [hmem, map_one])
    simpa using (GLAPPrimeCoreOf p I).inv_mem h1
  have hQc : ¬ Sbar ≤ Subgroup.center (PQuot p I) := by
    intro hle
    apply hSbar_ne
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxZ : x ∈ Subgroup.center (PQuot p I) := hle hx
    obtain ⟨k, hk⟩ := hSbarp ⟨x, hx⟩
    have h1 : orderOf x ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card (Subgroup.center (PQuot p I)) := by
      rw [show orderOf x = orderOf (⟨x, hxZ⟩ : Subgroup.center (PQuot p I)) from
        Subgroup.orderOf_coe (⟨x, hxZ⟩ : Subgroup.center (PQuot p I))]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center (PQuot p I))) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZodd)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hTfix : ∀ t ∈ pCoreOf 2 (Subgroup.normalizer (Sbar : Set (PQuot p I))),
      barAut p I ⟨c, hcN⟩ t = t := fun t ht =>
    hfix t (i1312_pCore_le_Sbar hp hp3 hBN (isPGroup_of_isElemAbelian hBel) hBS hSI hS2 hSO hmax ht)
  have hα1 : barAut p I ⟨c, hcN⟩ = 1 := by
    by_cases hIC : CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar 2 (PSimple p I)
    · exact CFSG.HardMathSupport.Solomon.Coordinator.YS08.lieQConstrained_aut_central_cover hL hsimple
        hnab hIC hZcop hperf hSbarp hQc (barAut p I ⟨c, hcN⟩) hpcop hαp hfix hTfix
    · have hsmall := chevTwo_small_cases (PSimple p I) hch hIC
      rcases hsmall with h5 | h6 | h8 | h7
      · obtain ⟨e⟩ := h5
        exact small_aut_eq_one_of_iso e oddInner_alt5 hinv_alt5 hperf hsimple hZcop
          (barAut p I ⟨c, hcN⟩) p hodd hαp Sbar hSbarp hSbar_ne hfix
      · obtain ⟨e⟩ := h6
        exact small_aut_eq_one_of_iso e oddInner_alt6 hinv_alt6 hperf hsimple hZcop
          (barAut p I ⟨c, hcN⟩) p hodd hαp Sbar hSbarp hSbar_ne hfix
      · obtain ⟨e⟩ := h8
        exact hA8 (PQuot p I) Sbar (barAut p I ⟨c, hcN⟩) p hperf hsimple hnab ⟨e⟩ hZcop hSbarp hQc
          hpcop hαp hfix hTfix
      · obtain ⟨e⟩ := h7
        exact small_aut_eq_one_of_iso e oddInner_psl27 hinv_psl27 hperf hsimple hZcop
          (barAut p I ⟨c, hcN⟩) p hodd hαp Sbar hSbarp hSbar_ne hfix
  exact (chev_barAut_eq_one_iff_centMod hcN).1 hα1

theorem i1312At_of_alt8 (hL : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQConstrained 2) (hA8 : I1312Alt8Constrained) (G : Type) [Group G] [Finite G]
    (p : ℕ) : I1312At G p := by
  unfold I1312At
  intro hp hp2 X I B S hI hch hBel hBN hS hS2 hBS hSO hmax
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  exact ⟨fun c hc hcS => i1312_part1 hL hA8 hp hp2 hI hch hBel hBN hBS hS hS2 hSO hmax hc hcS,
    fun hS8 => i1312_part2 hp hp3 hBel hBN hBS hS hS2 hS8⟩

theorem i1312At_given_alt8
    (hA8 : I1312Alt8Constrained) : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I1312At G p :=
  fun G _ _ p => i1312At_of_alt8 CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrained_two_holds hA8 G p

end CFSG.LocalAnalysis.GLTheoremA
