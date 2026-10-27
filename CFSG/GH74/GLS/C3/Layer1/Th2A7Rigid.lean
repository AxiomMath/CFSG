module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64A
public import CFSG.GH74.GLS.C3.Layer1.St1P720Top
public import CFSG.GH74.GLS.C3.Layer1.EvenSelBasic
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18

public section

namespace CFSG.GH74.GLS.Th2.A7Inv

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2 CFSG.GorensteinWalter
open scoped commutatorElement

theorem card_A7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem isSimple_A7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem nonab_A7 : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  by_contra h
  have h : ∀ a b : alternatingGroup (Fin 7), a * b = b * a := fun a b =>
    by_contra fun hne => h ⟨a, b, hne⟩
  have hc : center (alternatingGroup (Fin 7)) = ⊤ := by
    rw [eq_top_iff']
    intro a
    rw [Subgroup.mem_center_iff]
    intro b
    exact h b a
  have hb : center (alternatingGroup (Fin 7)) = ⊥ := alternatingGroup.center_eq_bot (by norm_num)
  have h1 : Nat.card (alternatingGroup (Fin 7)) = 1 := by
    rw [← Subgroup.card_top (G := alternatingGroup (Fin 7)), ← hc, hb, Subgroup.card_bot]
  rw [card_A7] at h1
  omega

theorem not_isSolvable_A7 : ¬ Group.IsSolvable (alternatingGroup (Fin 7)) := by
  intro h
  have := isSimple_A7
  obtain ⟨a, b, hab⟩ := nonab_A7
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr h a b)

theorem false_of_div_a7 {q : ℕ} (h : q * (q ^ 2 - 1) / 2 = 2520) : False := by
  have hq18 : q < 18 := by
    by_contra hge
    push Not at hge
    have h1 : 18 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
    have h2 : 323 ≤ q ^ 2 - 1 := by omega
    have h3 := Nat.mul_le_mul hge h2
    omega
  interval_cases q <;> omega

theorem false_of_simple_surj {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (f : S →* alternatingGroup (Fin 7)) (hf : Function.Surjective f) {q : ℕ}
    (hq : Nat.card S = q * (q ^ 2 - 1) / 2) : False := by
  have hA7 := isSimple_A7
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp h
    have h1 : Nat.card S = Nat.card (alternatingGroup (Fin 7)) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩)
    rw [card_A7, hq] at h1
    exact false_of_div_a7 h1
  · obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 7))
    obtain ⟨s, rfl⟩ := hf a
    apply ha
    have : s ∈ f.ker := by rw [h]; trivial
    exact this

theorem not_involved_A7_L2 {F : Type} [Field F] [Finite F]
    (hF : L2Field F) {K : Type} [Group K] [Finite K] (e : K ≃* L2 F) (M : Subgroup K)
    (ψ : ↥M →* alternatingGroup (Fin 7)) (hψ : Function.Surjective ψ) : False := by
  have hns : ¬ Group.IsSolvable ↥M := fun h =>
    not_isSolvable_A7 (Group.isSolvable_of_surjective (f := ψ) hψ)
  have hcard : 2520 ≤ Nat.card ↥M := by
    have := Nat.card_le_card_of_surjective ψ hψ
    rwa [card_A7] at this
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcharF : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hq)
  have hringF : ringChar F = p := ringChar.eq F p
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := hpodd
    omega
  rcases ivk_1_8_i F hF K e M hns with ⟨F₀, _, _, hchar, -, hM⟩ | ⟨F₀, _, _, h5, ⟨e5⟩⟩
  · have : Fintype F₀ := Fintype.ofFinite F₀
    have hch₀ : CharP F₀ p := by
      have h1 : ringChar F₀ = p := hchar.trans hringF
      rw [← h1]
      exact ringChar.charP F₀
    obtain ⟨m, -, hm⟩ := FiniteField.card F₀ p
    have hcard₀ : Nat.card F₀ = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
    have hodd₀ : IsOddPrimePower (Nat.card F₀) := ⟨p, m, hp, hpodd, m.pos, hcard₀⟩
    have hoddq : Odd (Nat.card F₀) := by rw [hcard₀]; exact hpodd.pow
    have hq3 : 3 ≤ Nat.card F₀ := by
      rw [hcard₀]
      exact hp3.trans (Nat.le_self_pow m.pos.ne' p)
    have hq3' : Nat.card F₀ = 3 ∨ 3 < Nat.card F₀ := by omega
    rcases hM with hM | hM
    · obtain ⟨eM⟩ := hM
      have hMcard : Nat.card ↥M = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) / 2 := by
        rw [Nat.card_congr (eM.trans (L2.equivPSL F₀)).toEquiv, psl2_card_formula F₀ hodd₀]
      rcases hq3' with h3 | hgt
      · rw [h3] at hMcard
        norm_num at hMcard
        omega
      · have : IsSimpleGroup ↥M := isSimpleGroup_of_l2 ⟨hoddq, hgt⟩ eM
        exact false_of_simple_surj ψ hψ hMcard
    · obtain ⟨eM⟩ := hM
      have hMcard : Nat.card ↥M = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
        rw [Nat.card_congr eM.toEquiv, pgl2_card_formula F₀]
      rcases hq3' with h3 | hgt
      · rw [h3] at hMcard
        norm_num at hMcard
        omega
      · obtain ⟨eC⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three F₀ hodd₀ hgt eM
        have hsC : IsSimpleGroup ↥(_root_.commutator ↥M) := by
          have : IsSimpleGroup (PSL2 F₀) :=
            Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
          exact eC.isSimpleGroup
        have hCcard : Nat.card ↥(_root_.commutator ↥M) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) / 2 := by
          rw [Nat.card_congr eC.toEquiv, psl2_card_formula F₀ hodd₀]
        have hCn : ((_root_.commutator ↥M).map ψ).Normal :=
          Subgroup.Normal.map inferInstance ψ hψ
        have htop : (_root_.commutator ↥M).map ψ = ⊤ := by
          have hA7 := isSimple_A7
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((_root_.commutator ↥M).map ψ) with h | h
          · exfalso
            obtain ⟨a, b, hab⟩ := nonab_A7
            obtain ⟨m₁, rfl⟩ := hψ a
            obtain ⟨m₂, rfl⟩ := hψ b
            apply hab
            have h1 : ⁅m₁, m₂⁆ ∈ _root_.commutator ↥M :=
              Subgroup.commutator_mem_commutator (Subgroup.mem_top m₁) (Subgroup.mem_top m₂)
            have h2 : ψ ⁅m₁, m₂⁆ ∈ (_root_.commutator ↥M).map ψ := ⟨_, h1, rfl⟩
            rw [h, Subgroup.mem_bot, map_commutatorElement] at h2
            exact commutatorElement_eq_one_iff_mul_comm.mp h2
          · exact h
        have hfC : Function.Surjective (ψ.comp (_root_.commutator ↥M).subtype) := by
          intro a
          have : a ∈ (_root_.commutator ↥M).map ψ := by rw [htop]; trivial
          obtain ⟨c, hc, rfl⟩ := this
          exact ⟨⟨c, hc⟩, rfl⟩
        exact false_of_simple_surj (ψ.comp (_root_.commutator ↥M).subtype) hfC hCcard
  · have hodd5 : IsOddPrimePower (Nat.card F₀) := ⟨5, 1, by norm_num, by decide, le_rfl, by rw [h5]; norm_num⟩
    have hMcard : Nat.card ↥M = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) / 2 := by
      rw [Nat.card_congr (e5.trans (L2.equivPSL F₀)).toEquiv, psl2_card_formula F₀ hodd5]
    rw [h5] at hMcard
    norm_num at hMcard
    omega

open CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.EvenSelP CFSG CFSG.ABGLocalTools

section Step

variable {G : Type} [Group G] [Finite G]

theorem a7_step_false {z u : G} {J H : Subgroup G}
    (hlt : PumpUpLT 2 z J u H) (hJ : Nonempty (kBar J ≃* alternatingGroup (Fin 7)))
    (hH : HasL2Model (kBar H) Odd) : False := by
  obtain ⟨p, f, hp, hf, hodd, hLie⟩ := hH
  have hpodd : Odd p := hodd.of_dvd_nat (dvd_pow_self p (by omega))
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  obtain ⟨F, _, _, eF, hF, -⟩ := exists_l2Field_of_lieModel' hp hp2 hLie
  have hu : orderOf u = 2 := hlt.2.1.1
  have hJc : IsPCompIn 2 (centralizer ({z} : Set G)) J := hlt.1.2.2
  have hHc : IsPCompIn 2 (centralizer ({u} : Set G)) H := hlt.2.1.2.2
  have hzY : z ∈ centralizer ({u} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ⟩ := PumpCalc.exists_isLam hu hJc hlt.2.2.2.1
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({u} : Set G) := hΛ.le.trans inf_le_right
  obtain ⟨φ, hφs, -, -⟩ := exists_phi hΛJ hΛY hΛ.cover
  obtain ⟨eA⟩ := hJ
  obtain ⟨eb⟩ := PumpCalc.kBar_equiv_bar hHc
  let eK : ↥(PumpCalc.bar u H) ≃* L2 F := eb.symm.trans eF
  by_cases hzH : z ∈ normalizer (H : Set G)
  · have hle := PumpCalc.bar_le_of_stable hlt hΛ hzH
    let eM := Subgroup.subgroupOfEquivOfLe hle
    refine A7Inv.not_involved_A7_L2 hF eK ((PumpCalc.bar u Λ).subgroupOf (PumpCalc.bar u H))
      ((eA.toMonoidHom.comp φ).comp eM.toMonoidHom) ?_
    exact (eA.surjective.comp hφs).comp eM.surjective
  · have hA7 := A7Inv.isSimple_A7
    have hJs : IsSimpleGroup (kBar J) := eA.isSimpleGroup
    obtain ⟨eq⟩ := PumpCalc.kBar_equiv_quotient_of_diag hlt hΛ hzY hzH hJs
    have hsK : IsSimpleGroup ↥(PumpCalc.bar u H) := isSimpleGroup_of_l2 hF eK
    have hcen : center ↥(PumpCalc.bar u H) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥(PumpCalc.bar u H)) with h | h
      · exact h
      · exfalso
        have h1 : Nat.card (alternatingGroup (Fin 7)) =
            Nat.card (↥(PumpCalc.bar u H) ⧸ center ↥(PumpCalc.bar u H)) :=
          Nat.card_congr (eA.symm.trans eq).toEquiv
        have h2 : Nat.card (↥(PumpCalc.bar u H) ⧸ center ↥(PumpCalc.bar u H)) =
            (center ↥(PumpCalc.bar u H)).index := rfl
        rw [h2, h, Subgroup.index_top, A7Inv.card_A7] at h1
        omega
    let e1 : (↥(PumpCalc.bar u H) ⧸ center ↥(PumpCalc.bar u H)) ≃* ↥(PumpCalc.bar u H) :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    let eAK : alternatingGroup (Fin 7) ≃* ↥(PumpCalc.bar u H) := eA.symm.trans (eq.trans e1)
    let eT : ↥(⊤ : Subgroup ↥(PumpCalc.bar u H)) ≃* ↥(PumpCalc.bar u H) := Subgroup.topEquiv
    exact A7Inv.not_involved_A7_L2 hF eK ⊤ (eAK.symm.toMonoidHom.comp eT.toMonoidHom)
      (eAK.symm.surjective.comp eT.surjective)

end Step

end CFSG.GH74.GLS.Th2.A7Inv

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1

theorem b_a7_rigid_step_of
    (hA7C2 : B_A7_notC2) (h720 : B_ivk_7_20) (hL34 : B_gen4_noL34_elem) : B_a7_rigid_step := by
  intro G _ _ hG z J u H hlt hJ
  have hJc : IsPCompIn 2 (centralizer ({z} : Set G)) J := hlt.1.2.2
  have hJU2 : InU2 (kBar J) := ⟨isQuasisimple_hat hJc, Or.inr (Or.inl hJ)⟩
  have hJnC2 : ¬ InC2 (kBar J) := fun h => hA7C2 (E2.inC2_of_mulEquiv hJ.some h)
  have hlong : LongPumpUp 2 z J u H := ⟨hlt.1, Relation.ReflTransGen.single hlt⟩
  obtain ⟨hHU2, hHnC2⟩ := h720 G hG z J u H ⟨hlt.1.1, hJc⟩ hJU2 hJnC2 hlong
  have hno := hL34 G hG.gen4 u H hlt.2.1.1 hlt.2.1.2.2
  obtain ⟨hbad, -, -⟩ := bad_of_inU2_not_inC2 hHU2 hHnC2 hno
  rcases hbad with ⟨p, f, hp, hf, ⟨hodd, -⟩, hLie⟩ | hA7
  · exact (Th2.A7Inv.a7_step_false hlt hJ ⟨p, f, hp, hf, hodd, hLie⟩).elim
  · exact hA7

end CFSG.GH74.GLS
