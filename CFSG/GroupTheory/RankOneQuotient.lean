module

public import CFSG.Timmesfeld.RankOne.Defs
public import CFSG.CGT.Timmesfeld75.L2Defs
public import Certificates.Certificate43
import CFSG.Timmesfeld.RankOne.Lift
import CFSG.Timmesfeld.Opposite.Moufang
import CFSG.GroupTheory.CardMapInfKer
import CFSG.CGT.Timmesfeld75.Sec3TwelveAlg
import CFSG.CGT.Timmesfeld75.NormalClosure
import CFSG.RankThree.GF2n.Tim77Prop24TwoL2
import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Sec5
import CFSG.Timmesfeld.RankOne

public section

namespace CFSG

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {G : Type*} [Group G]

private theorem map_mk_conjSubgroup_eq {H R K : Subgroup G} [(R.subgroupOf H).Normal]
    (hHR : H ≤ Subgroup.normalizer (R : Set G)) (hKH : K ≤ H) {r : G} (hr : r ∈ R)
    (hrK : conjSubgroup r K ≤ H) :
    ((conjSubgroup r K).subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) =
      (K.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) := by
  ext z
  constructor
  · rintro ⟨⟨x, hxH⟩, hx, rfl⟩
    have hx' : r⁻¹ * x * r ∈ K := by
      simpa [mem_conjSubgroup] using (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨⟨r⁻¹ * x * r, hKH hx'⟩, hx', ?_⟩
    change ((⟨r⁻¹ * x * r, hKH hx'⟩ : H) : ↥H ⧸ R.subgroupOf H) =
      ((⟨x, hxH⟩ : H) : ↥H ⧸ R.subgroupOf H)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (r⁻¹ * x * r)⁻¹ * x ∈ R
    have hdiv : (r⁻¹ * x * r)⁻¹ * x = r⁻¹ * (x⁻¹ * r * x) := by group
    rw [hdiv]
    exact R.mul_mem (R.inv_mem hr)
      (by simpa using (Subgroup.mem_normalizer_iff.mp (hHR (H.inv_mem hxH)) r).mp hr)
  · rintro ⟨⟨k, hkH⟩, hk, rfl⟩
    have hkK : k ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hrkH : r * k * r⁻¹ ∈ H :=
      hrK (Subgroup.mem_map_of_mem (MulAut.conj r).toMonoidHom hkK)
    refine ⟨⟨r * k * r⁻¹, hrkH⟩, Subgroup.mem_map_of_mem (MulAut.conj r).toMonoidHom hkK, ?_⟩
    change ((⟨r * k * r⁻¹, hrkH⟩ : H) : ↥H ⧸ R.subgroupOf H) =
      ((⟨k, hkH⟩ : H) : ↥H ⧸ R.subgroupOf H)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (r * k * r⁻¹)⁻¹ * k ∈ R
    have hdiv : (r * k * r⁻¹)⁻¹ * k = r * (k⁻¹ * r⁻¹ * k) := by group
    rw [hdiv]
    have hkR : k⁻¹ * r⁻¹ * k ∈ R := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hHR (H.inv_mem hkH)) r⁻¹).mp
        (R.inv_mem hr)
    exact R.mul_mem hr hkR

private theorem conjSubgroup_map_mk_eq {H R K₁ K₂ : Subgroup G} [(R.subgroupOf H).Normal]
    (hHR : H ≤ Subgroup.normalizer (R : Set G)) (hK₁ : K₁ ≤ H) (hK₂ : K₂ ≤ H) {x y r : G}
    (hx : x ∈ H) (hy : y ∈ H) (hr : r ∈ R)
    (hxy : conjSubgroup x K₂ = conjSubgroup r (conjSubgroup y K₁)) :
    conjSubgroup (QuotientGroup.mk' (R.subgroupOf H) ⟨y, hy⟩)
        ((K₁.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H))) =
      conjSubgroup (QuotientGroup.mk' (R.subgroupOf H) ⟨x, hx⟩)
        ((K₂.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H))) := by
  rw [← map_subgroupOf_conjSubgroup_of_mem H R K₁ hy,
    ← map_subgroupOf_conjSubgroup_of_mem H R K₂ hx, hxy]
  refine (map_mk_conjSubgroup_eq hHR ?_ hr ?_).symm
  · exact conjSubgroup_le_of_le_of_mem hK₁ hy
  · rw [← hxy]
    exact conjSubgroup_le_of_le_of_mem hK₂ hx

private theorem map_mk_eq_iff {H R : Subgroup G} [(R.subgroupOf H).Normal] {x y : ↥H} :
    QuotientGroup.mk' (R.subgroupOf H) x = QuotientGroup.mk' (R.subgroupOf H) y ↔
      (x : G)⁻¹ * (y : G) ∈ R := by
  change ((x : ↥H) : ↥H ⧸ R.subgroupOf H) = ((y : ↥H) : ↥H ⧸ R.subgroupOf H) ↔
    (x : G)⁻¹ * (y : G) ∈ R
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

private theorem map_mk_eq_one_iff {H R : Subgroup G} [(R.subgroupOf H).Normal] {x : ↥H} :
    QuotientGroup.mk' (R.subgroupOf H) x = 1 ↔ (x : G) ∈ R := by
  change ((x : ↥H) : ↥H ⧸ R.subgroupOf H) = 1 ↔ (x : G) ∈ R
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem map_mk_ne {P₁ P₂ R : Subgroup G}
    [(R.subgroupOf (P₁ ⊔ P₂)).Normal] (hP₁ : P₁ ≠ ⊥)
    (hne : ∀ p ∈ P₁, p ≠ 1 → ∀ u ∈ P₂, u⁻¹ * p ∉ R) :
    (P₁.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))) ≠
      (P₂.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))) := by
  intro hAB
  obtain ⟨p, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP₁
  let pH : ↥(P₁ ⊔ P₂) := ⟨(p : G), Subgroup.mem_sup_left p.2⟩
  have hpbar : QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)) pH ∈
      (P₁.subgroupOf (P₁ ⊔ P₂)).map
        (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr p.2)
  rw [hAB] at hpbar
  obtain ⟨u, hu, hpu⟩ := Subgroup.mem_map.mp hpbar
  have hu₂ : (u : G) ∈ P₂ := Subgroup.mem_subgroupOf.mp hu
  have hRmem : (u : G)⁻¹ * (p : G) ∈ R := map_mk_eq_iff.mp hpu
  exact hne (p : G) p.2 (fun h => hp1 (Subtype.ext h)) (u : G) hu₂ hRmem

private theorem map_mk_moufang {P₁ P₂ R : Subgroup G}
    [(R.subgroupOf (P₁ ⊔ P₂)).Normal] (hR : P₁ ⊔ P₂ ≤ Subgroup.normalizer (R : Set G))
    (hP₁R : P₁ ⊓ R = ⊥) (hP₂R : P₂ ⊓ R = ⊥)
    (hMouf : ∀ p ∈ P₁, p ≠ 1 → ∃ u ∈ P₂, u ≠ 1 ∧ ∃ r ∈ R,
      conjSubgroup p P₂ = conjSubgroup r (conjSubgroup u P₁))
    (hMouf' : ∀ u ∈ P₂, u ≠ 1 → ∃ p ∈ P₁, p ≠ 1 ∧ ∃ r ∈ R,
      conjSubgroup u P₁ = conjSubgroup r (conjSubgroup p P₂)) :
    (∀ a ∈ (P₁.subgroupOf (P₁ ⊔ P₂)).map
        (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))), a ≠ 1 →
      ∃ b ∈ (P₂.subgroupOf (P₁ ⊔ P₂)).map
          (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))),
        b ≠ 1 ∧
          ((P₁.subgroupOf (P₁ ⊔ P₂)).map
              (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))).map
              (MulAut.conj b).toMonoidHom =
            ((P₂.subgroupOf (P₁ ⊔ P₂)).map
              (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))).map
              (MulAut.conj a).toMonoidHom) ∧
    (∀ b ∈ (P₂.subgroupOf (P₁ ⊔ P₂)).map
        (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))), b ≠ 1 →
      ∃ a ∈ (P₁.subgroupOf (P₁ ⊔ P₂)).map
          (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))),
        a ≠ 1 ∧
          ((P₂.subgroupOf (P₁ ⊔ P₂)).map
              (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))).map
              (MulAut.conj a).toMonoidHom =
            ((P₁.subgroupOf (P₁ ⊔ P₂)).map
              (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))).map
              (MulAut.conj b).toMonoidHom) := by
  let H := P₁ ⊔ P₂
  let mk := QuotientGroup.mk' (R.subgroupOf H)
  have hP₁H : P₁ ≤ H := le_sup_left
  have hP₂H : P₂ ≤ H := le_sup_right
  constructor
  · intro a ha ha1
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    have hp1 : (p : G) ≠ 1 := by
      intro hp_eq
      apply ha1
      exact (map_mk_eq_one_iff (H := H) (R := R)).mpr
        (by simpa [hp_eq] using R.one_mem)
    obtain ⟨u, hu₂, hu1, r, hr, hxy⟩ := hMouf (p : G) (Subgroup.mem_subgroupOf.mp hp) hp1
    have huH : u ∈ H := hP₂H hu₂
    have hbB : mk ⟨u, huH⟩ ∈ (P₂.subgroupOf H).map mk :=
      Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hu₂)
    have hb1 : mk ⟨u, huH⟩ ≠ 1 := by
      intro h1
      have huR : u ∈ R := (map_mk_eq_one_iff (H := H) (R := R)).mp h1
      have huinf : u ∈ P₂ ⊓ R := Subgroup.mem_inf.mpr ⟨hu₂, huR⟩
      rw [hP₂R] at huinf
      exact hu1 (Subgroup.mem_bot.mp huinf)
    refine ⟨mk ⟨u, huH⟩, hbB, hb1, ?_⟩
    exact conjSubgroup_map_mk_eq hR hP₁H hP₂H
      (hP₁H (Subgroup.mem_subgroupOf.mp hp)) huH hr hxy
  · intro b hb hb1
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hb
    have hu1 : (u : G) ≠ 1 := by
      intro hu_eq
      apply hb1
      exact (map_mk_eq_one_iff (H := H) (R := R)).mpr
        (by simpa [hu_eq] using R.one_mem)
    obtain ⟨p, hp, hp1, r, hr, hxy⟩ := hMouf' (u : G) (Subgroup.mem_subgroupOf.mp hu) hu1
    have hpH : p ∈ H := hP₁H hp
    have haA : mk ⟨p, hpH⟩ ∈ (P₁.subgroupOf H).map mk :=
      Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hp)
    have ha1 : mk ⟨p, hpH⟩ ≠ 1 := by
      intro h1
      have hpR : p ∈ R := (map_mk_eq_one_iff (H := H) (R := R)).mp h1
      have hinf : p ∈ P₁ ⊓ R := Subgroup.mem_inf.mpr ⟨hp, hpR⟩
      rw [hP₁R] at hinf
      exact hp1 (Subgroup.mem_bot.mp hinf)
    refine ⟨mk ⟨p, hpH⟩, haA, ha1, ?_⟩
    exact conjSubgroup_map_mk_eq hR hP₂H hP₁H
      (hP₂H (Subgroup.mem_subgroupOf.mp hu)) hpH hr hxy

private theorem isElemAbRankOne_map_mk {P₁ P₂ R : Subgroup G}
    [(R.subgroupOf (P₁ ⊔ P₂)).Normal] (hR : P₁ ⊔ P₂ ≤ Subgroup.normalizer (R : Set G))
    (hcomm : ∀ p ∈ P₁, ∀ p' ∈ P₁, p * p' = p' * p) (hsq : ∀ p ∈ P₁, p * p = 1)
    (hP₁R : P₁ ⊓ R = ⊥) (hP₂R : P₂ ⊓ R = ⊥) (hP₁ : P₁ ≠ ⊥)
    (hne : ∀ p ∈ P₁, p ≠ 1 → ∀ u ∈ P₂, u⁻¹ * p ∉ R)
    (hMouf : ∀ p ∈ P₁, p ≠ 1 → ∃ u ∈ P₂, u ≠ 1 ∧ ∃ r ∈ R,
      conjSubgroup p P₂ = conjSubgroup r (conjSubgroup u P₁))
    (hMouf' : ∀ u ∈ P₂, u ≠ 1 → ∃ p ∈ P₁, p ≠ 1 ∧ ∃ r ∈ R,
      conjSubgroup u P₁ = conjSubgroup r (conjSubgroup p P₂)) :
    CFSG.Timmesfeld.IsElemAbRankOne
      ((P₁.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))))
      ((P₂.subgroupOf (P₁ ⊔ P₂)).map (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))) := by
  classical
  let H := P₁ ⊔ P₂
  let mk := QuotientGroup.mk' (R.subgroupOf H)
  haveI : (R.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hR
  have hP₁H : P₁ ≤ H := le_sup_left
  have hP₂H : P₂ ≤ H := le_sup_right
  have hmem (Q : Subgroup G) (hQ : Q ≤ H) {x : G} (hx : x ∈ Q) :
      mk ⟨x, hQ hx⟩ ∈ (Q.subgroupOf H).map mk :=
    Subgroup.mem_map_of_mem mk (Subgroup.mem_subgroupOf.mpr hx)
  have hmouf := map_mk_moufang hR hP₁R hP₂R hMouf hMouf'
  refine ⟨?_, map_mk_ne hP₁ hne, ?_, ?_, hmouf.1, hmouf.2⟩
  · rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hP₁H hP₂H, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · intro a ha a' ha'
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp ha'
    show mk p * mk p' = mk p' * mk p
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext (hcomm p (Subgroup.mem_subgroupOf.mp hp) p'
      (Subgroup.mem_subgroupOf.mp hp')))
  · intro a ha
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    exact (map_mk_eq_one_iff (H := H) (R := R)).mpr (by
      rw [Subgroup.coe_mul, hsq p (Subgroup.mem_subgroupOf.mp hp)]
      exact R.one_mem)

section GenericFinite

variable {G : Type} [Group G] [Finite G]

theorem exists_hom_SL2_of_moufang_quot {P₁ P₂ R : Subgroup G}
    (hR : P₁ ⊔ P₂ ≤ Subgroup.normalizer (R : Set G))
    (hcomm : ∀ p ∈ P₁, ∀ p' ∈ P₁, p * p' = p' * p) (hsq : ∀ p ∈ P₁, p * p = 1)
    (hP₁R : P₁ ⊓ R = ⊥) (hP₂R : P₂ ⊓ R = ⊥)
    (hne : ∀ p ∈ P₁, p ≠ 1 → ∀ u ∈ P₂, u⁻¹ * p ∉ R)
    (hMouf : ∀ p ∈ P₁, p ≠ 1 → ∃ u ∈ P₂, u ≠ 1 ∧ ∃ r ∈ R,
      conjSubgroup p P₂ = conjSubgroup r (conjSubgroup u P₁))
    (hMouf' : ∀ u ∈ P₂, u ≠ 1 → ∃ p ∈ P₁, p ≠ 1 ∧ ∃ r ∈ R,
      conjSubgroup u P₁ = conjSubgroup r (conjSubgroup p P₂)) (hq : 4 ≤ Nat.card P₁) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card P₁ = 2 ^ n ∧
      ∃ φ : ↥(P₁ ⊔ P₂) →* SL(2, GaloisField 2 n), Function.Surjective φ ∧
        φ.ker = R.subgroupOf (P₁ ⊔ P₂) ∧
        (P₁.subgroupOf (P₁ ⊔ P₂)).map φ = utri (GaloisField 2 n) ∧
        (P₂.subgroupOf (P₁ ⊔ P₂)).map φ = ltri (GaloisField 2 n) := by
  classical
  haveI : (R.subgroupOf (P₁ ⊔ P₂)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hR
  have hP₁ne : P₁ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P₁ = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hrank := isElemAbRankOne_map_mk hR hcomm hsq hP₁R hP₂R hP₁ne hne hMouf hMouf'
  have hcardπ : Nat.card ((P₁.subgroupOf (P₁ ⊔ P₂)).map
      (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))) = Nat.card P₁ := by
    have hker : ((P₁.subgroupOf (P₁ ⊔ P₂)) ⊓
        (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))).ker) = ⊥ := by
      rw [show (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))).ker = R.subgroupOf (P₁ ⊔ P₂)
        from QuotientGroup.ker_mk' (R.subgroupOf (P₁ ⊔ P₂)), Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hxP : (x : G) ∈ P₁ := Subgroup.mem_subgroupOf.mp hx.1
      have hxR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hx.2
      have hxbot : (x : G) ∈ P₁ ⊓ R := Subgroup.mem_inf.mpr ⟨hxP, hxR⟩
      rw [hP₁R] at hxbot
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    have h1 := card_map_eq_card_of_inf_ker_eq_bot
      (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))) hker
    have h2 : Nat.card ↥(P₁.subgroupOf (P₁ ⊔ P₂)) = Nat.card ↥P₁ :=
      CFSG.Timmesfeld.card_subgroupOf_of_le le_sup_left
    exact h1.trans h2
  have hq' : 4 ≤ Nat.card ((P₁.subgroupOf (P₁ ⊔ P₂)).map
      (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))) := by
    rw [hcardπ]
    exact hq
  obtain ⟨n, hn2, hncard, φ₀, hφA, hφB⟩ :=
    CFSG.Timmesfeld.rankOne_mulEquiv_SL2 hrank hq'
  refine ⟨n, hn2, hcardπ ▸ hncard,
    φ₀.toMonoidHom.comp (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂))), ?_, ?_, ?_, ?_⟩
  · exact φ₀.surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (R.subgroupOf (P₁ ⊔ P₂)))
      φ₀.toMonoidHom φ₀.injective, QuotientGroup.ker_mk']
  · rw [← Subgroup.map_map, hφA, CFSG.RankThree.GF2n.Tim77.utri_eq_upperUnipotent]
  · rw [← Subgroup.map_map, hφB, CFSG.RankThree.GF2n.Tim81.Sec2.ltri_eq_lowerUnipotent]

end GenericFinite

end CFSG

namespace CFSG.Timmesfeld

open CFSG.CGT.Timmesfeld75

private theorem IsElemAbRankOne.ker_le_normalizer_of_map_ne {X Y : Type*} [Group X]
    [Group Y] {A B : Subgroup X} (h : IsElemAbRankOne A B) {π : X →* Y}
    (hAB : A.map π ≠ B.map π) : π.ker ≤ Subgroup.normalizer (A : Set X) := by
  intro n hn
  by_contra hN
  have hne : A.map (MulAut.conj n).toMonoidHom ≠ A := by
    intro hfix
    exact hN (RankOne.map_conj_eq_self_iff.mp hfix)
  obtain ⟨a, ha, heq⟩ := h.exists_eq_of_map_conj_ne hne
  have h1 : (A.map (MulAut.conj n).toMonoidHom).map π =
      (B.map (MulAut.conj a).toMonoidHom).map π := congrArg (Subgroup.map π) heq
  rw [RankOne.map_map_conj, RankOne.map_map_conj, show π n = 1 from hn,
    RankOne.map_conj_one] at h1
  have h2 : B.map π = (A.map π).map (MulAut.conj (π a)⁻¹).toMonoidHom :=
    RankOne.map_conj_eq_iff.mp h1.symm
  have h3 : (A.map π).map (MulAut.conj (π a)⁻¹).toMonoidHom = A.map π :=
    RankOne.map_conj_of_mem ((A.map π).inv_mem (Subgroup.mem_map_of_mem π ha))
  exact hAB (h3 ▸ h2).symm

private theorem IsElemAbRankOne.odd_card_normalizer_inf' {X : Type*} [Group X] [Finite X]
    {A B : Subgroup X} (h : IsElemAbRankOne A B) :
    Odd (Nat.card (Subgroup.normalizer (A : Set X) ⊓
      Subgroup.normalizer (B : Set X) : Subgroup X)) := by
  obtain ⟨X', instGroupX', instFintypeX', ⟨e⟩⟩ :=
    (Finite.exists_type_univ_nonempty_mulEquiv (G := X) :
      ∃ (X' : Type) (_ : Group X') (_ : Fintype X'), Nonempty (X ≃* X'))
  letI := instGroupX'
  letI := instFintypeX'
  have h' : IsElemAbRankOne (A.map e.toMonoidHom) (B.map e.toMonoidHom) :=
    h.map e.surjective (by
      rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective]
      exact bot_le)
  have hodd := h'.odd_card_normalizer_inf
  have hmap : (Subgroup.normalizer (A : Set X) ⊓
      Subgroup.normalizer (B : Set X) : Subgroup X).map e.toMonoidHom =
      (Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup X') : Set X') ⊓
        Subgroup.normalizer ((B.map e.toMonoidHom : Subgroup X') : Set X') : Subgroup X') := by
    rw [Subgroup.map_inf _ _ _ e.injective, Subgroup.map_equiv_normalizer_eq,
      Subgroup.map_equiv_normalizer_eq]
  have hcard : Nat.card (Subgroup.normalizer (A : Set X) ⊓
      Subgroup.normalizer (B : Set X) : Subgroup X) = Nat.card (Subgroup.normalizer
        ((A.map e.toMonoidHom : Subgroup X') : Set X') ⊓
        Subgroup.normalizer ((B.map e.toMonoidHom : Subgroup X') : Set X') : Subgroup X') := by
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
  rw [hcard]
  exact hodd

theorem IsElemAbRankOne.ker_eq_bot_of_isPGroup {X Y : Type*} [Group X] [Finite X] [Group Y]
    {A B : Subgroup X} (h : IsElemAbRankOne A B) {π : X →* Y} (hAB : A.map π ≠ B.map π)
    (hker : IsPGroup 2 π.ker) : π.ker = ⊥ := by
  have hA : π.ker ≤ Subgroup.normalizer (A : Set X) :=
    h.ker_le_normalizer_of_map_ne hAB
  have hB : π.ker ≤ Subgroup.normalizer (B : Set X) :=
    h.symm.ker_le_normalizer_of_map_ne hAB.symm
  have hle : π.ker ≤ (Subgroup.normalizer (A : Set X) ⊓
      Subgroup.normalizer (B : Set X) : Subgroup X) := le_inf hA hB
  have hodd : Odd (Nat.card (Subgroup.normalizer (A : Set X) ⊓
      Subgroup.normalizer (B : Set X) : Subgroup X)) := h.odd_card_normalizer_inf'
  have hoddker : Odd (Nat.card π.ker) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker
  have hk0 : k = 0 := by
    cases k with
    | zero => rfl
    | succ k =>
      exfalso
      have hEven : Even (2 ^ (k + 1)) := by
        rw [pow_succ]
        exact Even.mul_left (show Even (2 : ℕ) from even_two_mul 1) _
      exact (Nat.not_even_iff_odd.mpr (hk ▸ hoddker)) hEven
  rw [← Subgroup.card_eq_one, hk, hk0, pow_zero]

end CFSG.Timmesfeld
