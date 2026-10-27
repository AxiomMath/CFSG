module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

section Core

variable {G : Type} [Group G] [Finite G]

theorem rank_le_twoLocal_of_normalizes_pre {X K : Subgroup G} (hKX : K ≤ X)
    {U₀ : Subgroup (barOf 3 K)} (hU₀ : U₀ ≠ ⊥) (hU₀2 : IsPGroup 2 ↥U₀) {T : Subgroup G}
    (hTel : IsElemAbelian 3 T) (hTX : T ≤ X) (hTN : T ≤ Subgroup.normalizer (c25Pre K U₀ : Set G))
    {j : ℕ} (hj : Nat.card T = 3 ^ j) : j ≤ GLATwoLocalRank 3 ↥X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup G := c25Pre K U₀ with hP
  have hPcop : ¬ 3 ∣ Nat.card P := c25_not_dvd_card_pre hU₀2
  have hPK : P ≤ K := c25Pre_le U₀
  let φ : ↥T →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hTN)
  let _inst : MulDistribMulAction ↥T ↥P := MulDistribMulAction.compHom ↥P φ
  obtain ⟨S₂, hS₂⟩ := c25_exists_invariant_sylow (A := ↥T) (P := ↥P)
    (c25_isPGroup_of_elemAbelian hTel) hPcop
  set U : Subgroup G := (S₂ : Subgroup ↥P).map P.subtype with hU
  have hUP : U ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hU2 : IsPGroup 2 ↥U :=
    (S₂.isPGroup').of_equiv ((S₂ : Subgroup ↥P).equivMapOfInjective P.subtype P.subtype_injective)
  have hU1 : U ≠ ⊥ := by
    intro hUb
    have h2 : 2 ∣ Nat.card P := c25_two_dvd_card_pre hU₀2 hU₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard : Nat.card (S₂ : Subgroup ↥P) = 1 := by
      have h6 : Nat.card ↥U = Nat.card ↥(S₂ : Subgroup ↥P) :=
        Subgroup.card_map_of_injective P.subtype_injective
      rw [← h6, hUb, Subgroup.card_bot]
    have h3 := S₂.card_eq_multiplicity
    rw [hcard] at h3
    have h4 : 0 < (Nat.card P).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have : 2 ^ (Nat.card P).factorization 2 = 1 := h3.symm
    have h5 : 2 ≤ 2 ^ (Nat.card P).factorization 2 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h4
    omega
  have hTU : T ≤ Subgroup.normalizer (U : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    have hφ : ∀ (t' : ↥T) (x : ↥P), (((φ t') x : ↥P) : G) = (t' : G) * (x : G) * (t' : G)⁻¹ :=
      fun _ _ => rfl
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hS₂ ⟨t, ht⟩ x hx
      exact ⟨φ ⟨t, ht⟩ • x, this, hφ ⟨t, ht⟩ x⟩
    · rintro ⟨y, hy, hyg⟩
      have hg : g ∈ P := by
        have h1 : t * g * t⁻¹ ∈ P := hyg ▸ y.2
        have h2 := (Subgroup.mem_normalizer_iff.1 (hTN ht) g).2 h1
        exact h2
      have := hS₂ ⟨t, ht⟩⁻¹ y hy
      refine ⟨_, this, ?_⟩
      show (((⟨t, ht⟩⁻¹ : ↥T) : G)) * (y : G) * (((⟨t, ht⟩⁻¹ : ↥T) : G))⁻¹ = g
      have hyg' : (y : G) = t * g * t⁻¹ := hyg
      rw [hyg']
      show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g
      group
  have hUX : U ≤ X := hUP.trans (hPK.trans hKX)
  have hUX1 : U.subgroupOf X ≠ ⊥ := by
    intro h
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hUX hu⟩ : ↥X) ∈ U.subgroupOf X := Subgroup.mem_subgroupOf.2 hu
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hUX2 : IsPGroup 2 ↥(U.subgroupOf X) := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUX).symm
  have hTXel : IsElemAbelian 3 (T.subgroupOf X) := c25_isElemAbelian_subgroupOf X hTel
  have hTXcard : Nat.card (T.subgroupOf X) = 3 ^ j :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv).trans hj
  have hTXN : T.subgroupOf X ≤ Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hTU (Subgroup.mem_subgroupOf.1 ht)) (x : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h1
  have hj' : j ≤ CFSG.Open.pRank 3 (Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hTXN hTXel hTXcard
  exact c25_le_twoLocal hUX1 hUX2 hj'

end Core

section Main

variable {G : Type} [Group G] [Finite G]

theorem rkY_of_ambient {I B : Subgroup G} (hrk : GLATwoLocalRank 3 ↥(I ⊔ B) ≤ 4)
    (hB : IsElemAbelian 3 B) {c : G} (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hcI : c ∈ Subgroup.centralizer (I : Set G)) : RkY (barOf 3 I) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro U hU hU2 E hEN hE
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have hcI' : ∀ i ∈ I, i * c = c * i := fun i hi => Subgroup.mem_centralizer_iff.1 hcI i hi
  obtain ⟨m, hm⟩ := (c25_isPGroup_of_elemAbelian hE).exists_card_eq
  let f : ↥I →* barOf 3 I := QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hfker : ¬ 3 ∣ Nat.card f.ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨S, hSel, hSmap, hScard⟩ := c25_exists_elemAbelian_lift_hom f hfs hfker hE
  set Sh : Subgroup G := S.map I.subtype with hSh
  have hShel : IsElemAbelian 3 Sh := c25_isElemAbelian_map _ hSel
  have hShcard : Nat.card Sh = 3 ^ m := by
    rw [hSh, Subgroup.card_map_of_injective I.subtype_injective, hScard, hm]
  have hShI : Sh ≤ I := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hShψ : ∀ (s : G) (hs : s ∈ Sh),
      (QuotientGroup.mk (⟨s, hShI hs⟩ : ↥I) : barOf 3 I) ∈ E := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hSmap]
    exact ⟨s, hs, rfl⟩
  have hbcent : c ∈ Subgroup.centralizer (Sh : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcI' h (hShI hh)
  set T : Subgroup G := Subgroup.zpowers c ⊔ Sh with hT
  have hTel : IsElemAbelian 3 T := c25_isElemAbelian_sup_zpowers hShel hc3 hbcent
  obtain ⟨j, hj⟩ := (c25_isPGroup_of_elemAbelian hTel).exists_card_eq
  have hShT : Sh ≤ T := le_sup_right
  have hmj : m ≤ j := by
    have h1 := Subgroup.card_dvd_of_le hShT
    rw [hShcard, hj] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have hTN : T ≤ Subgroup.normalizer (c25Pre I U : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      have hpre := c25Pre_le (K := I) U
      have hcP : c ∈ Subgroup.centralizer (c25Pre I U : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => hcI' h (hpre hh)
      exact Subgroup.centralizer_le_normalizer (c25Pre I U : Set G) hcP
    · intro s hs
      exact c25_mem_normalizer_pre (hShI hs) (hEN (hShψ s hs))
  have hTX : T ≤ I ⊔ B := sup_le (by rw [Subgroup.zpowers_le]; exact (le_sup_right : B ≤ I ⊔ B) hcB)
    (hShI.trans le_sup_left)
  have hjle : j ≤ 4 :=
    (rank_le_twoLocal_of_normalizes_pre le_sup_left hU hU2 hTel hTX hTN hj).trans hrk
  refine ⟨?_, fun hEZ => ?_⟩
  · calc Nat.card E = 3 ^ m := hm
      _ ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (hmj.trans hjle)
  ·
    have hcSh : c ∉ Sh := by
      intro hcS
      obtain ⟨s, hsS, hsc⟩ := hcS
      have hsE : (QuotientGroup.mk s : barOf 3 I) ∈ E := by
        rw [← hSmap]
        exact ⟨s, hsS, rfl⟩
      have hscen : (QuotientGroup.mk s : barOf 3 I) ∈ Subgroup.center (barOf 3 I) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective y
        show QuotientGroup.mk i * QuotientGroup.mk s = QuotientGroup.mk s * QuotientGroup.mk i
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        show (i : G) * (s : G) = (s : G) * (i : G)
        have : (s : G) = c := hsc
        rw [this]
        exact hcI' i i.2
      have hbot : (QuotientGroup.mk s : barOf 3 I) ∈ E ⊓ Subgroup.center (barOf 3 I) :=
        ⟨hsE, hscen⟩
      rw [hEZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hbot
      have hcore : c ∈ GLAPPrimeCoreOf 3 I := ⟨s, hbot, hsc⟩
      exact hc1 (c25_eq_one_of_mem_core hcore (a := 1) (by rw [pow_one]; exact hc3))
    have hjm : j ≠ m := by
      intro hjm
      have hle : T ≤ Sh := by
        refine (Subgroup.eq_of_le_of_card_ge hShT ?_).symm.le
        rw [hShcard, hj, hjm]
      exact hcSh (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
    have hm3 : m ≤ 3 := by omega
    calc Nat.card E = 3 ^ m := hm
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hm3

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
