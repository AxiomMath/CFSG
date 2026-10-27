module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JDh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Odd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec12J_B_le_D {t : G} {L S : Subgroup G} (hbd : Sec10BData t L S) :
    secB S L ≤ secM t S L ⊓ L :=
  le_inf (le_sup_left.trans (Subgroup.le_normalizer (H := secA t S L))) hbd.1

theorem sec12J_B_card {t : G} {L S : Subgroup G} (hbd : Sec10BData t L S) :
    Nat.card ((secB S L).subgroupOf (secM t S L ⊓ L)) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sec12J_B_le_D hbd)).toEquiv]
  exact hbd.2.1

theorem sec12J_alt1_key [Finite G] {t : G} {L S V : Subgroup G} (hbd : Sec10BData t L S)
    {φN : ↥(secN V) →* WrZ2 ↥(secM t S L ⊓ L)}
    (hker : φN.ker = (oddCoreIn (secN V)).subgroupOf (secN V)) {F : Subgroup G}
    (hFN : F ≤ secN V) (hF : IsElemAbelian 2 F) (hcard : 128 < Nat.card F) :
    (F.subgroupOf (secN V)).map φN =
      sec12W_base ((secB S L).subgroupOf (secM t S L ⊓ L)) := by
  have hD : ∀ {P : Subgroup ↥(secM t S L ⊓ L)}, IsElemAbelian 2 P →
      Nat.card P ≤ 16 ∧ (Nat.card P = 16 → P = (secB S L).subgroupOf (secM t S L ⊓ L)) :=
    fun hP => sec12D_elemAb hbd hP
  have hW : ∀ {X : Subgroup (WrZ2 ↥(secM t S L ⊓ L))}, IsElemAbelian 2 X →
      Nat.card X ≤ 128 ∨
        X = sec12W_base ((secB S L).subgroupOf (secM t S L ⊓ L)) :=
    fun hX => sec12W_elemAb ((secB S L).subgroupOf (secM t S L ⊓ L)) (sec12J_B_card hbd)
      (fun P hP => (hD hP).1) (fun P hP h => (hD hP).2 h) hX
  have hF'' : IsElemAbelian 2 (F.subgroupOf (secN V)) := hF.subgroupOf _
  have hinf : (F.subgroupOf (secN V)) ⊓ φN.ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgF : g ∈ F.subgroupOf (secN V) := (Subgroup.mem_inf.mp hg).1
    have hgk : g ∈ φN.ker := (Subgroup.mem_inf.mp hg).2
    rw [hker, Subgroup.mem_subgroupOf] at hgk
    have hodd := sec10L104_odd_orderOf hgk
    have h2 : (g : G) ^ 2 = 1 := hF.2 _ (Subgroup.mem_subgroupOf.mp hgF)
    have hdvd : orderOf (g : G) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h1 : orderOf (g : G) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subgroup.mem_bot.mpr (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hc := sec12J_card_inf_ker_mul φN (F.subgroupOf (secN V))
  rw [hinf, Subgroup.card_bot, one_mul] at hc
  have hsub : Nat.card (F.subgroupOf (secN V)) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  rcases hW (hF''.map φN) with h | h
  · rw [hc, hsub] at h
    omega
  · exact h

theorem sec12J_main_alt1 [Finite G] {t : G} {L S V : Subgroup G} (hbd : Sec10BData t L S)
    (hV : IsElemAb2 V 8)
    (hC : ∀ g ∈ centralizer (V : Set G), (∃ m : ℕ, g ^ (2 ^ m) = 1) → g ∈ V)
    (hO : oddCoreIn (secN V) ≤ centralizer (V : Set G))
    (hΩ : Sec128Alt1 t S L V) {F : Subgroup G} (hFN : F ≤ secN V) (hF : IsElemAbelian 2 F) :
    F ≤ V ∨ Nat.card F ≤ 128 := by
  obtain ⟨φN, -, hker⟩ := hΩ
  by_cases hcard : Nat.card F ≤ 128
  · exact Or.inr hcard
  · left
    push Not at hcard
    have hVN : V ≤ secN V := Subgroup.le_normalizer (H := V)
    have hVcard : 128 < Nat.card V := by
      rw [hV.2]
      norm_num
    have hkF := sec12J_alt1_key hbd hker hFN hF hcard
    have hkV := sec12J_alt1_key hbd hker hVN hV.1 hVcard
    intro x hx
    have hxN : x ∈ secN V := hFN hx
    have hmem : φN ⟨x, hxN⟩ ∈ (F.subgroupOf (secN V)).map φN :=
      Subgroup.mem_map_of_mem φN (Subgroup.mem_subgroupOf.mpr hx)
    rw [hkF, ← hkV] at hmem
    obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hmem
    have h1 : (⟨x, hxN⟩ : ↥(secN V))⁻¹ * v ∈ φN.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvx, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h1
    have h2 : x⁻¹ * (v : G) ∈ centralizer (V : Set G) := hO h1
    have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    have h3 : (v : G) ∈ centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hV.1.comm hh hvV
    have h4 : x⁻¹ ∈ centralizer (V : Set G) := by
      have := Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ h3)
      simpa using this
    have h5 : x ∈ centralizer (V : Set G) := by
      simpa using Subgroup.inv_mem _ h4
    exact hC x h5 ⟨1, by simpa using hF.2 x hx⟩

end CFSG.OddStandard.SmallF3.Omega
