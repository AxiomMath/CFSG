module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPSylowN
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open CFSG Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_mul_commutator_le {X Y : Type*} [Group X] [Finite X] [Group Y] (ψ : X →* Y)
    (D : Subgroup X) (Zh : Subgroup Y) (hZD : Zh ≤ D.map ψ)
    (hab : ∀ a ∈ D, ∀ b ∈ D, ψ a * ψ b = ψ b * ψ a) :
    Nat.card Zh * Nat.card (_root_.commutator D) ≤ Nat.card D := by
  let ψD : D →* Y := ψ.comp D.subtype
  have hker : _root_.commutator D ≤ ψD.ker := by
    unfold _root_.commutator
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hab a a.2 b b.2)
  have hrange : ψD.range = D.map ψ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  haveI : Finite ψD.range := Finite.of_surjective ψD.rangeRestrict ψD.rangeRestrict_surjective
  have h1 : Nat.card ψD.ker * Nat.card ψD.range = Nat.card D := Subgroup.card_ker_mul_card_range ψD
  have h2 : Nat.card Zh ≤ Nat.card ψD.range := Subgroup.card_le_of_le (hZD.trans hrange.ge)
  have h3 : Nat.card (_root_.commutator D) ≤ Nat.card ψD.ker := Subgroup.card_le_of_le hker
  calc Nat.card Zh * Nat.card (_root_.commutator D) ≤ Nat.card ψD.range * Nat.card ψD.ker :=
        Nat.mul_le_mul h2 h3
    _ = Nat.card D := by rw [mul_comm]; exact h1

theorem exists_D {X : Type*} [Group X] [Finite X] {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2)
    (R : Subgroup X) [R.Normal] (H ZE : Subgroup X) (Zh : Subgroup (X ⧸ R)) {y : X}
    (hZEc : ∀ z ∈ ZE, ∀ h ∈ H, h * z = z * h)
    (hmaxN : ∀ S : Subgroup X, S ≤ H ⊓ R → IsPGroup f S → S ≤ ZE)
    (hZab : ∀ a ∈ Zh, ∀ b ∈ Zh, a * b = b * a) (hZexp : ∀ a ∈ Zh, a ^ f = 1)
    (hyf : y ^ f = 1) (hyH : y ∈ normalizer (H : Set X))
    (hyZ : ∀ a : X ⧸ R, QuotientGroup.mk' R y * a * (QuotientGroup.mk' R y)⁻¹ ∈ Zh ↔ a ∈ Zh)
    (hlift : ∀ z ∈ Zh, ∃ h ∈ H, h ^ f = 1 ∧ QuotientGroup.mk' R h = z) :
    ∃ D : Subgroup X, (∀ d ∈ D, d ^ f = 1) ∧
      (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧
      y ∈ normalizer (D : Set X) ∧ Zh ≤ D.map (QuotientGroup.mk' R) ∧
      ∀ a ∈ D, QuotientGroup.mk' R a ∈ Zh := by
  classical
  set π := QuotientGroup.mk' R with hπ
  let Zp : Subgroup X := H ⊓ Zh.comap π
  have hmemZ : ∀ x : X, x ∈ Zp ↔ x ∈ H ∧ π x ∈ Zh := fun x => Iff.rfl
  have hyZp : y ∈ normalizer (Zp : Set X) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    have h1 := Subgroup.mem_normalizer_iff.mp hyH x
    have h2 := hyZ (π x)
    rw [← map_inv, ← map_mul, ← map_mul] at h2
    exact and_congr h1 h2.symm
  obtain ⟨S, hSZ, hSp, hSmax, hyS⟩ := exists_sylow_normalized_of_mem_normalizer Zp hyf hyZp
  have hSH : ∀ s ∈ S, s ∈ H := fun s hs => ((hmemZ s).mp (hSZ hs)).1
  have hSZh : ∀ s ∈ S, π s ∈ Zh := fun s hs => ((hmemZ s).mp (hSZ hs)).2
  have hSc : ∀ s ∈ S, π s = 1 → ∀ c ∈ S, c * s = s * c := by
    intro s hs hπs c hc
    have hsR : s ∈ R := (QuotientGroup.eq_one_iff s).mp hπs
    have hQ : S ⊓ (H ⊓ R) ≤ ZE := hmaxN _ inf_le_right hSp.to_inf_left
    have hsZE : s ∈ ZE := hQ ⟨hs, hSH s hs, hsR⟩
    exact hZEc s hsZE c (hSH c hc)
  have hπcomm : ∀ a ∈ S, ∀ b ∈ S, π ⁅a, b⁆ = 1 := by
    intro a ha b hb
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hZab _ (hSZh a ha) _ (hSZh b hb))
  have hcommS : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ S := by
    intro a ha b hb
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hΦ : frattini ↥S ≤ center ↥S := by
    refine frattini_le_of_commutator_pow_mem (p := f) (center ↥S) (fun a b => ?_) (fun a => ?_)
    · rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hSc _ (hcommS a a.2 b b.2) (hπcomm a a.2 b b.2) c c.2)
    · rw [Subgroup.mem_center_iff]
      intro c
      have h1 : π ((a : X) ^ f) = 1 := by
        rw [map_pow]
        exact hZexp _ (hSZh a a.2)
      exact Subtype.ext (hSc _ (S.pow_mem a.2 f) h1 c c.2)
  obtain ⟨-, -, -, hset, -, -⟩ := central_frattini_odd_power_map hf2 hSp hΦ
  let D : Subgroup X := (omega₁ (G := ↥S) (p := f)).map S.subtype
  have hDmem : ∀ d : X, d ∈ D ↔ d ∈ S ∧ d ^ f = 1 := by
    intro d
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : s ∈ ((omega₁ (G := ↥S) (p := f) : Subgroup ↥S) : Set ↥S) := hs
      rw [hset] at hs'
      exact ⟨s.2, by simpa using congrArg Subtype.val (show s ^ f = 1 from hs')⟩
    · rintro ⟨hdS, hdf⟩
      refine ⟨⟨d, hdS⟩, ?_, rfl⟩
      have h1 : (⟨d, hdS⟩ : ↥S) ∈ ((omega₁ (G := ↥S) (p := f) : Subgroup ↥S) : Set ↥S) := by
        rw [hset]
        exact Subtype.ext (by simpa using hdf)
      exact h1
  refine ⟨D, fun d hd => ((hDmem d).mp hd).2, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb c hc
    have hc' := ((hDmem c).mp hc).1
    exact (hSc _ (hcommS a ((hDmem a).mp ha).1 b ((hDmem b).mp hb).1)
      (hπcomm a ((hDmem a).mp ha).1 b ((hDmem b).mp hb).1) c hc').symm
  · refine Subgroup.mem_normalizer_iff.mpr fun d => ?_
    show d ∈ D ↔ y * d * y⁻¹ ∈ D
    rw [hDmem d, hDmem (y * d * y⁻¹)]
    have hS' : d ∈ S ↔ y * d * y⁻¹ ∈ S := Subgroup.mem_normalizer_iff.mp hyS d
    have hpow : (y * d * y⁻¹) ^ f = y * d ^ f * y⁻¹ := conj_pow
    refine and_congr hS' ?_
    rw [hpow]
    constructor
    · intro h2
      rw [h2]
      simp
    · intro h3
      calc d ^ f = y⁻¹ * (y * d ^ f * y⁻¹) * y := by group
        _ = 1 := by rw [h3]; simp
  · intro z hz
    obtain ⟨h, hh, hhf, hhz⟩ := hlift z hz
    have hhZp : h ∈ Zp := (hmemZ h).mpr ⟨hh, by rw [hhz]; exact hz⟩
    obtain ⟨g, hg, hgS⟩ := exists_conj_mem_of_isPGroup Zp S hSZ hSp hSmax hhZp hhf
    refine ⟨g⁻¹ * h * g, (hDmem _).mpr ⟨hgS, ?_⟩, ?_⟩
    · have h1 := conj_pow (a := g⁻¹) (b := h) (i := f)
      rw [inv_inv, hhf] at h1
      simpa using h1
    · have hgZ : π g ∈ Zh := ((hmemZ g).mp hg).2
      have hc : π g * z = z * π g := hZab _ hgZ _ hz
      show π (g⁻¹ * h * g) = z
      rw [map_mul, map_mul, map_inv, hhz, mul_assoc, ← hc, inv_mul_cancel_left]
  · intro a ha
    exact hSZh a ((hDmem a).mp ha).1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
