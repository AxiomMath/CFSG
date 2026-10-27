module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldY

public section

open CFSG.Open CFSG.Goldschmidt Subgroup CFSG.ABGLocalTools

namespace CFSG.GH74.GLS.Th2.P412

@[expose] def GoldStmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X), A ≤ S →
    IsMulCommutative A →
    (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) →
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ goldschmidtOddCore M)
    CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      goldschmidtSimpleType (K ⧸ Subgroup.center K)

section Aux

variable {M : Type} [Group M]

theorem goldschmidtOddCore_characteristic : (goldschmidtOddCore M).Characteristic := by
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact CFSG.pPrimeCore_characteristic

theorem odd_card_goldschmidtOddCore [Finite M] : Odd (Nat.card (goldschmidtOddCore M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

theorem eq_one_of_mem_oddCore_of_isPGroup [Finite M] {g : M} (hg : g ∈ goldschmidtOddCore M)
    {P : Subgroup M} (hP : IsPGroup 2 ↥P) (hgP : g ∈ P) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨g, hgP⟩
  have h1 : orderOf g = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have h2 : Odd (orderOf g) :=
    Odd.of_dvd_nat odd_card_goldschmidtOddCore (Subgroup.orderOf_dvd_natCard _ hg)
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 h2) (h1 ▸ Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
  exact h1

theorem eq_one_of_mem_oddCore_of_sq [Finite M] {g : M} (hg : g ∈ goldschmidtOddCore M)
    (h : g * g = 1) : g = 1 := by
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  have hodd : Odd (orderOf g) :=
    Odd.of_dvd_nat odd_card_goldschmidtOddCore (Subgroup.orderOf_dvd_natCard _ hg)
  have h1 : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

end Aux


section Action

variable {X : Type} [Group X] (M : Subgroup X) [M.Normal]

theorem map_oddCore_conjNormal (g : X) :
    (goldschmidtOddCore ↥M).map (MulAut.conjNormal (H := M) g).toMonoidHom =
      goldschmidtOddCore ↥M :=
  Subgroup.characteristic_iff_map_eq.1 goldschmidtOddCore_characteristic _

noncomputable def psiAut (g : X) :
    (↥M ⧸ goldschmidtOddCore ↥M) ≃* (↥M ⧸ goldschmidtOddCore ↥M) :=
  QuotientGroup.congr (goldschmidtOddCore ↥M) (goldschmidtOddCore ↥M)
    (MulAut.conjNormal g) (map_oddCore_conjNormal M g)

theorem psiAut_mk (g : X) (m : ↥M) :
    psiAut M g (QuotientGroup.mk m) = QuotientGroup.mk (MulAut.conjNormal g m) :=
  QuotientGroup.congr_mk _ _ _ _ m

theorem map_pCore_psiAut (g : X) :
    (CFSG.Open.pCore 2 (↥M ⧸ goldschmidtOddCore ↥M)).map (psiAut M g).toMonoidHom =
      CFSG.Open.pCore 2 (↥M ⧸ goldschmidtOddCore ↥M) :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCore_map_eq 2 (psiAut M g)

end Action

theorem card_map_eq_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (hinj : ∀ a ∈ K, ∀ b ∈ K, f a = f b → a = b) : Nat.card (K.map f) = Nat.card K := by
  have h1 : Nat.card (K.map f) = ((K.map f : Subgroup H) : Set H).ncard :=
    Nat.card_coe_set_eq _
  have h2 : Nat.card K = (K : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, h2, Subgroup.coe_map]
  exact Set.InjOn.ncard_image (fun a ha b hb hab => hinj a ha b hb hab)

theorem gold_analysis
    (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b)
    {X : Type} [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X)
    (hAS : A ≤ (S : Subgroup X))
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAsq : ∀ a ∈ A, a * a = 1)
    (hA4 : Nat.card A = 4)
    (hclosed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    (htrans : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ g : X, g⁻¹ * a * g = b) :
    (∃ Q : Subgroup X, Q.Normal ∧ A ≤ Q ∧
        ∃ Nn : Subgroup X, Nn.Normal ∧ Odd (Nat.card Nn) ∧ Q ≤ A ⊔ Nn) ∨
      ((S : Subgroup X) ⊓ Subgroup.normalClosure (A : Set X) = A) ∨
      (64 ≤ Nat.card ↥((S : Subgroup X) ⊓ Subgroup.normalClosure (A : Set X)) ∧
        ∀ s ∈ (S : Subgroup X) ⊓ Subgroup.normalClosure (A : Set X), s * s = 1 → s ∈ A) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAab : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩
  obtain ⟨hlay0, hbar0, hcomp0⟩ := hGold X S A hAS hAab hclosed
  set M : Subgroup X := Subgroup.normalClosure (A : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.subset_normalClosure
  set O : Subgroup ↥M := goldschmidtOddCore ↥M with hO
  set π : ↥M →* ↥M ⧸ O := QuotientGroup.mk' O with hπ
  set U : Subgroup (↥M ⧸ O) := CFSG.Open.pCore 2 (↥M ⧸ O) with hU
  have hlay : U ⊔ goldschmidtLayer (↥M ⧸ O) = ⊤ := hlay0
  have hcomp : ∀ K : Subgroup (↥M ⧸ O), IsComponentOf K ⊤ →
      goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K) := hcomp0
  set Ab : Subgroup (↥M ⧸ O) := (A.subgroupOf M).map π with hAb
  have hbar : Ab = U ⊔ Subgroup.closure {t | t ∈ ((S : Subgroup X).subgroupOf M).map π ⊓
      goldschmidtLayer (↥M ⧸ O) ∧ t ^ 2 = 1} := hbar0
  have hmemAb : ∀ x, x ∈ Ab ↔ ∃ (a : X) (ha : a ∈ A), π ⟨a, hAM ha⟩ = x := by
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨(m : X), hm, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hAM ha⟩, ha, rfl⟩
  have hπA_one : ∀ (a : X) (ha : a ∈ A), π ⟨a, hAM ha⟩ = 1 → a = 1 := by
    intro a ha h1
    have hO1 : (⟨a, hAM ha⟩ : ↥M) ∈ O := (QuotientGroup.eq_one_iff _).1 h1
    have := eq_one_of_mem_oddCore_of_sq hO1 (Subtype.ext (hAsq a ha))
    exact congrArg Subtype.val this
  have hUAb : U ≤ Ab := by
    rw [hbar]
    exact le_sup_left
  have hconj : ∀ (g : X) (a : X) (ha : a ∈ A) (hb : g * a * g⁻¹ ∈ A),
      psiAut M g (π ⟨a, hAM ha⟩) = π ⟨g * a * g⁻¹, hAM hb⟩ := by
    intro g a ha hb
    simp only [hπ, QuotientGroup.mk'_apply]
    rw [psiAut_mk]
    congr 1
  have hUinv : ∀ (g : X) (u : ↥M ⧸ O), u ∈ U → psiAut M g u ∈ U := by
    intro g u hu
    have := Subgroup.mem_map_of_mem (psiAut M g).toMonoidHom hu
    rwa [hU, map_pCore_psiAut] at this
  have hdich : ∀ (a : X) (ha : a ∈ A), a ≠ 1 → π ⟨a, hAM ha⟩ ∈ U →
      ∀ (b : X) (hb : b ∈ A), π ⟨b, hAM hb⟩ ∈ U := by
    intro a ha ha1 haU b hb
    by_cases hb1 : b = 1
    · subst hb1
      have : (⟨1, hAM hb⟩ : ↥M) = 1 := rfl
      rw [this, map_one]
      exact U.one_mem
    · obtain ⟨g, hg⟩ := htrans a ha b hb ha1 hb1
      have hgb : g⁻¹ * a * g⁻¹⁻¹ = b := by simpa using hg
      have hgA : g⁻¹ * a * g⁻¹⁻¹ ∈ A := by rw [hgb]; exact hb
      have h1 := hconj g⁻¹ a ha hgA
      have h2 : (⟨g⁻¹ * a * g⁻¹⁻¹, hAM hgA⟩ : ↥M) = ⟨b, hAM hb⟩ := Subtype.ext hgb
      rw [h2] at h1
      rw [← h1]
      exact hUinv _ _ haU
  by_cases hcase : ∃ (a : X) (ha : a ∈ A), a ≠ 1 ∧ π ⟨a, hAM ha⟩ ∈ U
  ·
    left
    obtain ⟨a, ha, ha1, haU⟩ := hcase
    have hAbU : Ab ≤ U := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := (hmemAb x).1 hx
      exact hdich a ha ha1 haU b hb
    set Q : Subgroup X := (U.comap π).map M.subtype with hQ
    set Nn : Subgroup X := O.map M.subtype with hNn
    refine ⟨Q, ?_, ?_, Nn, ?_, ?_, ?_⟩
    · refine ⟨fun n hn g => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hn
      refine ⟨MulAut.conjNormal g m, ?_, ?_⟩
      · have h1 : psiAut M g (π m) = π (MulAut.conjNormal g m) := by
          simp only [hπ, QuotientGroup.mk'_apply]; exact psiAut_mk M g m
        show π (MulAut.conjNormal g m) ∈ U
        rw [← h1]
        exact hUinv g _ hm
      · simp [MulAut.conjNormal_apply]
    · intro a ha
      exact ⟨⟨a, hAM ha⟩, hAbU ((hmemAb _).2 ⟨a, ha, rfl⟩), rfl⟩
    · refine ⟨fun n hn g => ?_⟩
      obtain ⟨o, ho, rfl⟩ := hn
      refine ⟨MulAut.conjNormal g o, ?_, ?_⟩
      · have := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := M) g).toMonoidHom ho
        rwa [hO, map_oddCore_conjNormal] at this
      · simp [MulAut.conjNormal_apply]
    · rw [hNn, Subgroup.card_map_of_injective M.subtype_injective]
      exact odd_card_goldschmidtOddCore
    · rintro q ⟨m, hm, rfl⟩
      have hmAb : π m ∈ Ab := hUAb hm
      obtain ⟨a, ha, hma⟩ := (hmemAb _).1 hmAb
      have h1 : (⟨a, hAM ha⟩ : ↥M)⁻¹ * m ∈ O := QuotientGroup.eq.1 hma
      have : (m : X) = a * (((⟨a, hAM ha⟩ : ↥M)⁻¹ * m : ↥M) : X) := by simp
      show (m : X) ∈ A ⊔ Nn
      rw [this]
      exact Subgroup.mul_mem_sup ha ⟨_, h1, rfl⟩
  ·
    right
    push Not at hcase
    have hU_bot : U = ⊥ := by
      refine eq_bot_iff.2 fun u hu => ?_
      obtain ⟨a, ha, rfl⟩ := (hmemAb u).1 (hUAb hu)
      by_cases ha1 : a = 1
      · subst ha1
        have : (⟨1, hAM ha⟩ : ↥M) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      · exact absurd hu (hcase a ha ha1)
    have hSyl : IsSylowOf 2 (S : Subgroup X) ⊤ :=
      (isSylowOf_iff).2 ⟨le_top, S.isPGroup', by
        rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
    have hSylM : IsSylowOf 2 ((S : Subgroup X) ⊓ M) M :=
      hSyl.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.2 hMn).ge
    obtain ⟨Qs, hQs⟩ := hSylM.exists_sylow_eq_subgroupOf
    rw [Subgroup.inf_subgroupOf_right] at hQs
    have hQsP : IsPGroup 2 ↥((S : Subgroup X).subgroupOf M) := by
      rw [← hQs]; exact Qs.isPGroup'
    let Ts : Sylow 2 (↥M ⧸ O) := Sylow.mapSurjective (QuotientGroup.mk'_surjective O) Qs
    have hTs : (Ts : Subgroup (↥M ⧸ O)) = ((S : Subgroup X).subgroupOf M).map π := by
      rw [Sylow.coe_mapSurjective, hQs]
    have hinjS : ∀ x ∈ (S : Subgroup X).subgroupOf M, ∀ y ∈ (S : Subgroup X).subgroupOf M,
        π x = π y → x = y := by
      intro x hx y hy hxy
      have h1 : x⁻¹ * y ∈ O := QuotientGroup.eq.1 hxy
      have h2 : x⁻¹ * y ∈ (S : Subgroup X).subgroupOf M :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
      have := eq_one_of_mem_oddCore_of_isPGroup h1 hQsP h2
      exact (inv_mul_eq_one.1 this)
    have hinjA : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, π x = π y → x = y := by
      intro x hx y hy hxy
      have h1 : x⁻¹ * y ∈ O := QuotientGroup.eq.1 hxy
      have h2 : (((x⁻¹ * y : ↥M)) : X) ∈ A := by
        have : (((x⁻¹ * y : ↥M)) : X) = (x : X)⁻¹ * (y : X) := by simp
        rw [this]
        exact A.mul_mem (A.inv_mem hx) hy
      have h3 := eq_one_of_mem_oddCore_of_sq h1 (Subtype.ext (hAsq _ h2))
      exact (inv_mul_eq_one.1 h3)
    have hAbcard : Nat.card Ab = 4 := by
      rw [hAb, card_map_eq_of_injOn π _ hinjA]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hA4
    have hlay' : goldschmidtLayer (↥M ⧸ O) = ⊤ := by
      rw [hU_bot, bot_sup_eq] at hlay
      exact hlay
    have hbar' : Ab = Omega1 (Ts : Subgroup (↥M ⧸ O)) := by
      rw [hbar, hU_bot, bot_sup_eq, hlay', inf_top_eq, hTs]
      rfl
    have hVcomm : IsMulCommutative (Omega1 (Ts : Subgroup (↥M ⧸ O))) := by
      rw [← hbar', hAb]
      have : IsMulCommutative (A.subgroupOf M) :=
        ⟨⟨fun a b => Subtype.ext (Subtype.ext (hAcomm _ a.2 _ b.2))⟩⟩
      exact isMulCommutative_map this π
    have hY := sylow_card_of_layer hN11a hN11b hU_bot
      (goldschmidtOddCore_quotient_eq_bot (↥M)) hlay' hcomp Ts (by rw [← hbar']; exact hAbcard)
      hVcomm
    have hcardSM : Nat.card ↥((S : Subgroup X) ⊓ M) = Nat.card (Ts : Subgroup (↥M ⧸ O)) := by
      rw [hTs, card_map_eq_of_injOn π _ hinjS]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm.trans
        (by rw [Subgroup.inf_subgroupOf_right])
    have hAle : A ≤ (S : Subgroup X) ⊓ M := le_inf hAS hAM
    rcases hY with h4 | h64
    · left
      have : Nat.card ↥((S : Subgroup X) ⊓ M) ≤ Nat.card A := by rw [hcardSM, h4, hA4]
      exact (Subgroup.eq_of_le_of_card_ge hAle this).symm
    · right
      refine ⟨by rw [hcardSM, h64], ?_⟩
      intro s hs hs2
      obtain ⟨hsS, hsM⟩ := hs
      have hsx : (⟨s, hsM⟩ : ↥M) ∈ (S : Subgroup X).subgroupOf M := hsS
      have hπs : π ⟨s, hsM⟩ ∈ Omega1 (Ts : Subgroup (↥M ⧸ O)) := by
        refine Subgroup.subset_closure ⟨?_, ?_⟩
        · rw [hTs]; exact ⟨_, hsx, rfl⟩
        · rw [sq, ← map_mul]
          have : (⟨s, hsM⟩ : ↥M) * ⟨s, hsM⟩ = 1 := Subtype.ext hs2
          rw [this, map_one]
      rw [← hbar'] at hπs
      obtain ⟨a, ha, haπ⟩ := (hmemAb _).1 hπs
      have haS : (⟨a, hAM ha⟩ : ↥M) ∈ (S : Subgroup X).subgroupOf M := hAS ha
      have := hinjS _ haS _ hsx haπ
      have h2 : a = s := congrArg Subtype.val this
      rw [← h2]
      exact ha

end CFSG.GH74.GLS.Th2.P412
