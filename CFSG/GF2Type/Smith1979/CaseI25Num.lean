module

public import CFSG.GF2Type.Smith1979.CaseI25Alt
public import CFSG.GF2Type.Smith1979.CaseI25Core
public import CFSG.GF2Type.Smith1979.CaseI25Filter
public import CFSG.GF2Type.Smith1979.CaseI25Layer
public import CFSG.GF2Type.Smith1979.CaseI25Split

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open CFSG.Open CFSG.ComponentClassification

section Generic

theorem card_dvd_quotient_center_of_le {A : Type*} [Group A] (B : Subgroup A) (E : Subgroup B)
    (P : Subgroup A) (hP : P ≤ E.map B.subtype) [IsSimpleGroup P] (hperf : Group.IsPerfect P) :
    Nat.card P ∣ Nat.card (E ⧸ center E) := by
  let e : E ≃* E.map B.subtype := E.equivMapOfInjective B.subtype B.subtype_injective
  let ψ : P →* E := e.symm.toMonoidHom.comp (Subgroup.inclusion hP)
  have hψ : Function.Injective ψ := e.symm.injective.comp (Subgroup.inclusion_injective hP)
  let φ : P →* E ⧸ center E := (QuotientGroup.mk' (center E)).comp ψ
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have hc : ∀ x : P, ψ x ∈ center E := fun x => by
        have hx : x ∈ φ.ker := h ▸ mem_top x
        exact (QuotientGroup.eq_one_iff (ψ x)).mp hx
      haveI : IsMulCommutative P := ⟨⟨fun x y => hψ (by
        have h1 := Subgroup.mem_center_iff.mp (hc x) (ψ y)
        rw [map_mul, map_mul]
        exact h1.symm)⟩⟩
      haveI := hperf
      exact not_subsingleton P Group.IsPerfect.subsingleton_of_isMulCommutative
  exact Subgroup.card_dvd_of_injective φ ((MonoidHom.ker_eq_bot_iff φ).mp hker)

theorem two_dvd_index_of_not_mem {B : Type*} [Group B] (E : Subgroup B) [E.Normal] {t : B}
    (ht2 : t * t = 1) (htE : t ∉ E) : 2 ∣ E.index := by
  have hne : (QuotientGroup.mk t : B ⧸ E) ≠ 1 := fun h => htE ((QuotientGroup.eq_one_iff t).mp h)
  have hsq : (QuotientGroup.mk t : B ⧸ E) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, ht2]
    rfl
  have h2 := orderOf_eq_prime hsq hne
  rw [Subgroup.index_eq_card, ← h2]
  exact orderOf_dvd_natCard _

theorem false_of_alternating {E : Type*} [Group E] {n : ℕ} (hn : n = 10 ∨ n = 11)
    (e : E ⧸ center E ≃* alternatingGroup (Fin n)) (hZ3 : ∀ z ∈ center E, z ^ 3 = 1)
    (K : Subgroup E) (hK2 : ∀ x ∈ K, x * x = 1) (hKc : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hKcard : Nat.card K = 16) (hconj : ∀ a ∈ K, a ≠ 1 → ∀ b ∈ K, b ≠ 1 → IsConj a b) :
    False := by
  let f : E →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf1 : ∀ x ∈ K, f x = 1 → x = 1 := by
    intro x hx hfx
    have h1 : QuotientGroup.mk' (center E) x = 1 := by
      apply e.injective
      simpa [f] using hfx
    have hxc : x ∈ center E := (QuotientGroup.eq_one_iff x).mp h1
    have h3 := hZ3 x hxc
    have h2 := hK2 x hx
    calc x = x * x * x := by rw [h2, one_mul]
      _ = x ^ 3 := (pow_three' x).symm
      _ = 1 := h3
  let g : K →* alternatingGroup (Fin n) := f.comp K.subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hf1 a.1 a.2 ha)
  refine no_conj_elemAbelian_sixteen_alt_isConj hn g.range ?_ ?_ ?_ ?_
  · rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hK2 a.1 a.2)
    rw [this, map_one]
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg g (Subtype.ext (hKc a.1 a.2 b.1 b.2))
  · rw [← hKcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ ha hb
    have ha' : a.1 ≠ 1 := fun h => ha (by rw [show a = 1 from Subtype.ext h, map_one])
    have hb' : b.1 ≠ 1 := fun h => hb (by rw [show b = 1 from Subtype.ext h, map_one])
    exact f.map_isConj (hconj a.1 a.2 ha' b.1 b.2 hb')

theorem false_of_alternating_of_le {A : Type*} [Group A] (B : Subgroup A) (E : Subgroup B)
    {n : ℕ} (hn : n = 10 ∨ n = 11) (e : E ⧸ center E ≃* alternatingGroup (Fin n))
    (hZ3 : ∀ z ∈ center E, z ^ 3 = 1) (K N : Subgroup A) (hKN : K ≤ N)
    (hNE : N ≤ E.map B.subtype) (hK2 : ∀ x ∈ K, x * x = 1)
    (hKc : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hKcard : Nat.card K = 16)
    (hconj : ∀ a ∈ K, a ≠ 1 → ∀ b ∈ K, b ≠ 1 → ∃ n ∈ N, n * a * n⁻¹ = b) : False := by
  let f : E →* A := B.subtype.comp E.subtype
  have hfinj : Function.Injective f := B.subtype_injective.comp Subtype.val_injective
  have hrange : f.range = E.map B.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hKf : K ≤ f.range := by
    rw [hrange]
    exact hKN.trans hNE
  refine false_of_alternating hn e hZ3 (K.comap f) ?_ ?_ ?_ ?_
  · intro x hx
    apply hfinj
    rw [map_mul, map_one]
    exact hK2 _ hx
  · intro x hx y hy
    apply hfinj
    rw [map_mul, map_mul]
    exact hKc _ hx _ hy
  · rw [← Subgroup.card_map_of_injective hfinj, Subgroup.map_comap_eq, inf_of_le_right hKf]
    exact hKcard
  · intro a ha ha1 b hb hb1
    have hfa : f a ≠ 1 := fun h => ha1 (hfinj (by rw [h, map_one]))
    have hfb : f b ≠ 1 := fun h => hb1 (hfinj (by rw [h, map_one]))
    obtain ⟨m, hm, hmab⟩ := hconj (f a) ha hfa (f b) hb hfb
    obtain ⟨c, hc⟩ : m ∈ f.range := by
      rw [hrange]
      exact hNE hm
    refine isConj_iff.mpr ⟨c, hfinj ?_⟩
    rw [map_mul, map_mul, map_inv, hc]
    exact hmab

end Generic

section Orthogonal

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isPlusType_q (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1)
    (h6 : finrank (ZMod 2) (Vt S g t) = 6) (h12 : finrank (ZMod 2) S.Qt = 12) :
    CFSG.GroupTheory.WeirSylow.IsPlusType S.q :=
  ⟨Vt S g t, by omega, fun _ hx => q_eq_zero_of_mem_Vt H ht1 hx⟩

theorem card_O_eq (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1)
    (h6 : finrank (ZMod 2) (Vt S g t) = 6) (h12 : finrank (ZMod 2) S.Qt = 12) :
    Nat.card S.O = orthPlus12Ord := by
  have hplus := isPlusType_q H ht1 h6 h12
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
    (Q := S.q) S.q_nondegenerate (m := 5) (by omega) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  exact eq_orthPlus12Ord_of_formula (q := Nat.card (ZMod 2)) (by simp) h

end Orthogonal

section Context

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] def PerfectInLayer (S : Setting G) : Prop :=
  ∀ P : Subgroup S.O, P ≤ S.Mbar → ⁅P, P⁆ = P →
    P ≤ (timmesfeldLayer S.Mbar).map S.Mbar.subtype

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

omit hCE H hNo C ht ht1 hVQ hΩ hN h6 in
theorem pow_three_of_mem_center (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    {z : timmesfeldLayer S.Mbar} (hz : z ∈ center (timmesfeldLayer S.Mbar)) : z ^ 3 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp
    ((Subgroup.orderOf_dvd_natCard _ hz).trans (card_center_layer_dvd hodd))

theorem not_mem_layer (hΔ : (Delta S g t).ncard = 6) :
    (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar) ∉ timmesfeldLayer S.Mbar := by
  intro h
  have hP : (timmesfeldLayer S.Mbar).map S.Mbar.subtype ≤ S.Mbar := map_subtype_le _
  have hEperf : ⁅timmesfeldLayer S.Mbar, timmesfeldLayer S.Mbar⁆ = timmesfeldLayer S.Mbar :=
    Subgroup.isPerfect_iff.mp (Layer.perfect S.Mbar)
  have hperf : ⁅(timmesfeldLayer S.Mbar).map S.Mbar.subtype,
      (timmesfeldLayer S.Mbar).map S.Mbar.subtype⁆ =
      (timmesfeldLayer S.Mbar).map S.Mbar.subtype := by
    rw [← Subgroup.map_commutator, hEperf]
  refine conj_not_mem_of_perfect hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hP hperf
    (x := 1) (one_mem _) ?_
  rw [one_mul, inv_one, mul_one]
  exact ⟨_, h, rfl⟩

theorem dvd_card_layer_quotient_25920 (hperf : PerfectInLayer S)
    (hΔ : (Delta S g t).ncard = 6) :
    25920 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := by
  obtain ⟨-, -, -, -, hper, -, -, hsimple, hcard⟩ :=
    Rbar_split hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have hR := hperf ⁅Rbar S g t, Rbar S g t⁆ ((Subgroup.commutator_le_self _).trans Rbar_le_Mbar)
    hper
  haveI := hsimple
  have h := card_dvd_quotient_center_of_le S.Mbar (timmesfeldLayer S.Mbar) _ hR
    (Subgroup.isPerfect_iff.mpr hper)
  rwa [hcard] at h

theorem card_layer_quotient_dvd_orthPlus12 :
    Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣ orthPlus12Ord := by
  have hw : S.width = 6 := by
    rw [width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ, h6]
  have h12 : finrank (ZMod 2) S.Qt = 12 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  rw [← card_O_eq H ht1 h6 h12]
  have h1 : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣
      Nat.card (timmesfeldLayer S.Mbar) :=
    ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup (center (timmesfeldLayer S.Mbar))⟩
  exact h1.trans ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _))

theorem two_pow_seven_dvd_card_layer_quotient (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hperf : PerfectInLayer S) (hΔ : (Delta S g t).ncard = 6) :
    2 ^ 7 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := by
  obtain ⟨hM, hper, -, hcard, -⟩ := perfect_core_N hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have hN'E := hperf _ hM hper
  have h1 : Nat.card ↥(⁅NLbar S g, NLbar S g⁆) ∣ Nat.card (timmesfeldLayer S.Mbar) := by
    have h := Subgroup.card_dvd_of_le hN'E
    rwa [Subgroup.card_map_of_injective S.Mbar.subtype_injective] at h
  rw [hcard, Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (timmesfeldLayer S.Mbar))] at h1
  rcases (Nat.dvd_prime Nat.prime_three).mp (card_center_layer_dvd hodd) with h | h <;>
    rw [h] at h1 <;> omega

theorem not_two_pow_nine_dvd_card_layer_quotient (hΔ : (Delta S g t).ncard = 6) :
    ¬ 2 ^ 9 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := by
  intro h9
  have hE9 : 2 ^ 9 ∣ Nat.card (timmesfeldLayer S.Mbar) :=
    h9.trans ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (timmesfeldLayer S.Mbar))⟩
  haveI : (timmesfeldLayer S.Mbar).Normal := Layer.normal S.Mbar
  have htt : (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar) * ⟨t, S.Lbar_le_Mbar g ht⟩ = 1 :=
    Subtype.ext (mul_self_of_mem_Lbar S H.conj_mem ht)
  have h2 : 2 ∣ (timmesfeldLayer S.Mbar).index :=
    two_dvd_index_of_not_mem _ htt (not_mem_layer hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ)
  have h10 : 2 ^ 10 ∣ Nat.card S.Mbar := by
    rw [← Subgroup.card_mul_index (timmesfeldLayer S.Mbar)]
    have h := mul_dvd_mul hE9 h2
    rwa [← pow_succ] at h
  obtain ⟨T, hT, -, -, hTcard⟩ := exists_sylow_two_card hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have hle := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h10
  have hc := hT.card_eq
  rcases hTcard with h | h <;> rw [hc] at h <;>
    have := Nat.pow_right_injective le_rfl h <;> omega

theorem E_numerics (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) (hperf : PerfectInLayer S)
    (hΔ : (Delta S g t).ncard = 6) :
    25920 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∧
      Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣ orthPlus12Ord ∧
      2 ^ 7 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∧
      ¬ 2 ^ 9 ∣ Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) :=
  ⟨dvd_card_layer_quotient_25920 hCE H hNo C ht ht1 hVQ hΩ hN h6 hperf hΔ,
    card_layer_quotient_dvd_orthPlus12 hCE H hNo C ht ht1 hVQ hΩ hN h6,
    two_pow_seven_dvd_card_layer_quotient hCE H hNo C ht ht1 hVQ hΩ hN h6 hodd hperf hΔ,
    not_two_pow_nine_dvd_card_layer_quotient hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ⟩

theorem not_nonempty_mulEquiv_alternating (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hperf : PerfectInLayer S) (hΔ : (Delta S g t).ncard = 6) {n : ℕ} (hn : n = 10 ∨ n = 11) :
    ¬ Nonempty (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar) ≃*
      alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  obtain ⟨hM, hper, -, -, -, htrans, -⟩ := perfect_core_N hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine false_of_alternating_of_le S.Mbar (timmesfeldLayer S.Mbar) hn e
    (fun z hz => pow_three_of_mem_center hodd hz) (Kbar S g t) ⁅NLbar S g, NLbar S g⁆
    (Kbar_le_commutator_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ) (hperf _ hM hper) ?_ ?_ ?_ ?_
  · exact fun x hx => mul_self_of_mem_Lbar S H.conj_mem (Kbar_le_Lbar ht hx)
  · exact fun x hx y hy => Lbar_comm S H.conj_mem (Kbar_le_Lbar ht hx) (Kbar_le_Lbar ht hy)
  · rw [card_Kbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ]
    norm_num
  · exact htrans

end Context

end Case25

end CFSG.GF2Type.Smith1979
