module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldX

public section

open CFSG.Open CFSG.Goldschmidt CFSG.ABGLocalTools Subgroup CFSG.GH74.GLS.Th2.P412

namespace CFSG.OddStandard.SmallF3.Omega

theorem gold_dichotomy (hGold : GoldStmt) {X : Type} [Group X] [Finite X] (S : Sylow 2 X)
    (V : Subgroup X) (hVS : V ≤ (S : Subgroup X))
    (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVsq : ∀ a ∈ V, a * a = 1)
    (hclosed : ∀ a ∈ V, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ V)
    (hirr : ∀ U : Subgroup X, U ≤ V →
      (∀ g ∈ normalizer (V : Set X), ∀ u ∈ U, g⁻¹ * u * g ∈ U) → U = ⊥ ∨ U = V) :
    (∃ Nn : Subgroup X, Nn.Normal ∧ Odd (Nat.card Nn) ∧ (V ⊔ Nn).Normal) ∨
      (goldschmidtLayer (↥(Subgroup.normalClosure (V : Set X)) ⧸
          goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X))) = ⊤ ∧
        CFSG.Open.pCore 2 (↥(Subgroup.normalClosure (V : Set X)) ⧸
          goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X))) = ⊥ ∧
        (∀ K : Subgroup (↥(Subgroup.normalClosure (V : Set X)) ⧸
            goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X))), IsComponentOf K ⊤ →
          goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K)) ∧
        (∃ Ts : Sylow 2 (↥(Subgroup.normalClosure (V : Set X)) ⧸
            goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X))),
          (Ts : Subgroup (↥(Subgroup.normalClosure (V : Set X)) ⧸
              goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X)))) =
            ((S : Subgroup X).subgroupOf (Subgroup.normalClosure (V : Set X))).map
              (QuotientGroup.mk' (goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X)))) ∧
          (V.subgroupOf (Subgroup.normalClosure (V : Set X))).map
              (QuotientGroup.mk' (goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X)))) =
            Omega1 (Ts : Subgroup (↥(Subgroup.normalClosure (V : Set X)) ⧸
              goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X)))) ) ∧
        (∀ x ∈ (S : Subgroup X).subgroupOf (Subgroup.normalClosure (V : Set X)),
          ∀ y ∈ (S : Subgroup X).subgroupOf (Subgroup.normalClosure (V : Set X)),
            QuotientGroup.mk' (goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X))) x =
              QuotientGroup.mk' (goldschmidtOddCore ↥(Subgroup.normalClosure (V : Set X))) y →
            x = y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVab : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩⟩
  obtain ⟨hlay0, hbar0, hcomp0⟩ := hGold X S V hVS hVab hclosed
  set M : Subgroup X := Subgroup.normalClosure (V : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hVM : V ≤ M := Subgroup.subset_normalClosure
  set O : Subgroup ↥M := goldschmidtOddCore ↥M with hO
  set π : ↥M →* ↥M ⧸ O := QuotientGroup.mk' O with hπ
  set U : Subgroup (↥M ⧸ O) := CFSG.Open.pCore 2 (↥M ⧸ O) with hU
  have hlay : U ⊔ goldschmidtLayer (↥M ⧸ O) = ⊤ := hlay0
  have hcomp : ∀ K : Subgroup (↥M ⧸ O), IsComponentOf K ⊤ →
      goldschmidtSimpleType (↥K ⧸ Subgroup.center ↥K) := hcomp0
  set Vb : Subgroup (↥M ⧸ O) := (V.subgroupOf M).map π with hVb
  have hbar : Vb = U ⊔ Subgroup.closure {t | t ∈ ((S : Subgroup X).subgroupOf M).map π ⊓
      goldschmidtLayer (↥M ⧸ O) ∧ t ^ 2 = 1} := hbar0
  have hmemVb : ∀ x, x ∈ Vb ↔ ∃ (a : X) (ha : a ∈ V), π ⟨a, hVM ha⟩ = x := by
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨(m : X), hm, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hVM ha⟩, ha, rfl⟩
  have hπV_one : ∀ (a : X) (ha : a ∈ V), π ⟨a, hVM ha⟩ = 1 → a = 1 := by
    intro a ha h1
    have hO1 : (⟨a, hVM ha⟩ : ↥M) ∈ O := (QuotientGroup.eq_one_iff _).1 h1
    have := eq_one_of_mem_oddCore_of_sq hO1 (Subtype.ext (hVsq a ha))
    exact congrArg Subtype.val this
  have hUVb : U ≤ Vb := by
    rw [hbar]
    exact le_sup_left
  have hconj : ∀ (g : X) (a : X) (ha : a ∈ V) (hb : g * a * g⁻¹ ∈ V),
      psiAut M g (π ⟨a, hVM ha⟩) = π ⟨g * a * g⁻¹, hVM hb⟩ := by
    intro g a ha hb
    simp only [hπ, QuotientGroup.mk'_apply]
    rw [psiAut_mk]
    congr 1
  have hUinv : ∀ (g : X) (u : ↥M ⧸ O), u ∈ U → psiAut M g u ∈ U := by
    intro g u hu
    have := Subgroup.mem_map_of_mem (psiAut M g).toMonoidHom hu
    rwa [hU, map_pCore_psiAut] at this
  set W0 : Subgroup X := V ⊓ (U.comap π).map M.subtype with hW0
  have hW0V : W0 ≤ V := inf_le_left
  have hW0norm : ∀ g ∈ normalizer (V : Set X), ∀ u ∈ W0, g⁻¹ * u * g ∈ W0 := by
    intro g hg u hu
    have huV : u ∈ V := hW0V hu
    have hug : g⁻¹ * u * g ∈ V :=
      (Subgroup.mem_set_normalizer_iff''.1 hg u).1 huV
    have huQ : u ∈ (U.comap π).map M.subtype := (Subgroup.mem_inf.1 hu).2
    obtain ⟨m, hmU, hmv⟩ := Subgroup.mem_map.1 huQ
    refine Subgroup.mem_inf.2 ⟨hug, ?_⟩
    refine Subgroup.mem_map.2 ⟨MulAut.conjNormal (H := M) g⁻¹ m, ?_, ?_⟩
    · rw [Subgroup.mem_comap]
      have h1 : psiAut M g⁻¹ (π m) = π (MulAut.conjNormal (H := M) g⁻¹ m) := by
        simp only [hπ, QuotientGroup.mk'_apply]
        exact psiAut_mk M g⁻¹ m
      rw [← h1]
      exact hUinv g⁻¹ (π m) hmU
    · have hmv' : (m : X) = u := hmv
      show ((MulAut.conjNormal (H := M) g⁻¹ m : ↥M) : X) = g⁻¹ * u * g
      rw [MulAut.conjNormal_apply, inv_inv, hmv']
  have hdich : W0 = ⊥ ∨ W0 = V := hirr W0 hW0V hW0norm
  rcases hdich with hW0bot | hW0eqV
  ·
    right
    have hU_bot : U = ⊥ := by
      refine eq_bot_iff.2 fun u hu => ?_
      have huVb : u ∈ Vb := hUVb hu
      obtain ⟨a, ha, hma⟩ := (hmemVb u).1 huVb
      have haW0 : a ∈ W0 := by
        refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
        refine Subgroup.mem_map.2 ⟨⟨a, hVM ha⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap, hπ, hma]
        exact hu
      rw [hW0bot] at haW0
      have ha1 : a = 1 := Subgroup.mem_bot.1 haW0
      have he1 : (⟨a, hVM ha⟩ : ↥M) = 1 := Subtype.ext ha1
      rw [← hma, he1]
      exact map_one π
    have hU_bot' : CFSG.Open.pCore 2 (↥M ⧸ O) = ⊥ := by
      rw [← hU]
      exact hU_bot
    have hlay' : goldschmidtLayer (↥M ⧸ O) = ⊤ := by
      rw [hU_bot, bot_sup_eq] at hlay
      exact hlay
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
    have hVb_eq_Omega : Vb = Omega1 (Ts : Subgroup (↥M ⧸ O)) := by
      rw [hbar, hU_bot, bot_sup_eq, hlay', inf_top_eq, hTs]
      rfl
    refine ⟨hlay', hU_bot', hcomp, ⟨Ts, hTs, hVb_eq_Omega⟩, hinjS⟩
  ·
    left
    have hVleQ : V ≤ (U.comap π).map M.subtype := by
      rw [← hW0eqV, hW0]
      exact inf_le_right
    have hVbU : Vb ≤ U := by
      intro x hx
      obtain ⟨a, ha, hax⟩ := (hmemVb x).1 hx
      have haQ : a ∈ (U.comap π).map M.subtype := hVleQ ha
      obtain ⟨m, hmU, hmv⟩ := Subgroup.mem_map.1 haQ
      have hmeq : (⟨a, hVM ha⟩ : ↥M) = m := Subtype.ext hmv.symm
      rw [← hax, hmeq]
      exact hmU
    have hVb_eq_U : Vb = U := le_antisymm hVbU hUVb
    set Q : Subgroup X := (U.comap π).map M.subtype with hQ
    set Nn : Subgroup X := O.map M.subtype with hNn
    have hQnormal : Q.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
      refine Subgroup.mem_map.2 ⟨MulAut.conjNormal (H := M) g m, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        have h1 : psiAut M g (π m) = π (MulAut.conjNormal (H := M) g m) := by
          simp only [hπ, QuotientGroup.mk'_apply]
          exact psiAut_mk M g m
        rw [← h1]
        exact hUinv g (π m) hm
      · simp [MulAut.conjNormal_apply]
    have hNn_normal : Nn.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.1 hn
      refine Subgroup.mem_map.2 ⟨MulAut.conjNormal (H := M) g o, ?_, ?_⟩
      · have hmem := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := M) g).toMonoidHom ho
        rw [map_oddCore_conjNormal] at hmem
        exact hmem
      · simp [MulAut.conjNormal_apply]
    have hNn_odd : Odd (Nat.card Nn) := by
      rw [hNn, Subgroup.card_map_of_injective M.subtype_injective]
      exact odd_card_goldschmidtOddCore
    have hNnQ : Nn ≤ Q := by
      rintro n ⟨o, ho, rfl⟩
      refine Subgroup.mem_map.2 ⟨o, ?_, rfl⟩
      have hone : (o : ↥M ⧸ O) = 1 := (QuotientGroup.eq_one_iff o).2 ho
      rw [Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply, hone]
      exact U.one_mem
    have hQle : Q ≤ V ⊔ Nn := by
      rintro q ⟨m, hm, rfl⟩
      have hmU : π m ∈ U := hm
      have hmVb : π m ∈ Vb := hVb_eq_U ▸ hmU
      obtain ⟨a, ha, hma⟩ := (hmemVb _).1 hmVb
      have h1 : (⟨a, hVM ha⟩ : ↥M)⁻¹ * m ∈ O := QuotientGroup.eq.1 hma
      have h2 : (m : X) = a * (((⟨a, hVM ha⟩ : ↥M)⁻¹ * m : ↥M) : X) := by simp
      show (m : X) ∈ V ⊔ Nn
      rw [h2]
      exact Subgroup.mul_mem_sup ha ⟨_, h1, rfl⟩
    have hsup : V ⊔ Nn = Q := le_antisymm (sup_le hVleQ hNnQ) hQle
    exact ⟨Nn, hNn_normal, hNn_odd, hsup ▸ hQnormal⟩

end CFSG.OddStandard.SmallF3.Omega
