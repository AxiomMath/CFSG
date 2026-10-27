module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

public section

namespace CFSG.OddStandard.AltStdSmall

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_of_relIndex_two {S R : Subgroup G} (hRidx : R.relIndex S = 2) :
    ⁅S, S⁆ ≤ R := by
  rw [commutator_le]
  intro a ha b hb
  have hidx : (R.subgroupOf S).index = 2 := hRidx
  set a' : S := ⟨a, ha⟩
  set b' : S := ⟨b, hb⟩
  have h : ⁅a', b'⁆ ∈ R.subgroupOf S := by
    rw [commutatorElement_def, mul_mem_iff_of_index_two hidx, mul_mem_iff_of_index_two hidx,
      mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
    tauto
  have := mem_subgroupOf.1 h
  simpa [a', b', commutatorElement_def] using this

theorem conj_mem_commutator_of_mem_normalizer {S : Subgroup G} {x : G}
    (hx : x ∈ normalizer (S : Set G)) {w : G} (hw : w ∈ ⁅S, S⁆) : x * w * x⁻¹ ∈ ⁅S, S⁆ := by
  have hle : ⁅S, S⁆ ≤ (⁅S, S⁆).comap (MulAut.conj x).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_comap]
    show x * ⁅a, b⁆ * x⁻¹ ∈ ⁅S, S⁆
    have e : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hx a).1 ha)
      ((mem_normalizer_iff.1 hx b).1 hb)
  exact hle hw

variable [Finite G]

theorem conj_mem_center_of_mem_normalizer {S : Subgroup G} {z x : G} (hzS : z ∈ S)
    (hSz : S ≤ centralizer ({z} : Set G)) (hx : x ∈ normalizer (S : Set G)) :
    x⁻¹ * z * x ∈ S ∧ ∀ s ∈ S, x⁻¹ * z * x * s = s * (x⁻¹ * z * x) := by
  have hx' : x⁻¹ ∈ normalizer (S : Set G) := inv_mem hx
  refine ⟨?_, fun s hs => ?_⟩
  · have := (mem_normalizer_iff.1 hx' z).1 hzS
    simpa using this
  · have h1 : x * s * x⁻¹ ∈ S := (mem_normalizer_iff.1 hx s).1 hs
    have h2 : x * s * x⁻¹ * z = z * (x * s * x⁻¹) := mem_centralizer_singleton_iff.1 (hSz h1)
    calc x⁻¹ * z * x * s = x⁻¹ * (z * (x * s * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * s * x⁻¹ * z) * x := by rw [h2]
      _ = s * (x⁻¹ * z * x) := by group

theorem two_dvd_index_of_center_inf [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {S R : Subgroup G} {z y : G} (hS : IsPGroup 2 S) (hzS : z ∈ S) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hSz : S ≤ centralizer ({z} : Set G)) (hRS : R ≤ S) (hRidx : R.relIndex S = 2)
    (hzR : z ∉ R) (hZ : ∀ w ∈ R, (∀ s ∈ S, w * s = s * w) → w = 1 ∨ w = y)
    (hyD : y ∈ ⁅S, S⁆) : 2 ∣ S.index := by
  by_contra hodd
  obtain ⟨g, hgR, -, hgC⟩ :=
    CFSG.ComponentClassification.HarrisLit.HarrisEnd.exists_extremal_conj_of_relIndex_two hnab hS hodd hRS hRidx hzS hzR hz2
  have hle : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨c, hc, rfl⟩
    have := (hgC c ⟨hc, hSz hc⟩).1
    simpa [MulAut.conj_apply] using this
  have hcard : Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have heq : S.map (MulAut.conj g⁻¹).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hcen : ∀ s ∈ S, g⁻¹ * z * g * s = s * (g⁻¹ * z * g) := by
    intro s hs
    rw [← heq] at hs
    obtain ⟨c, hc, rfl⟩ := hs
    have h1 := mem_centralizer_singleton_iff.1 (hgC c ⟨hc, hSz hc⟩).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
    exact h1.symm
  rcases hZ _ hgR hcen with h1 | h1
  · apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  ·
    have hgN : g ∈ normalizer (S : Set G) := by
      rw [mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        have hs' : s ∈ S.map (MulAut.conj g⁻¹).toMonoidHom := by rw [heq]; exact hs
        obtain ⟨c, hc, hcs⟩ := hs'
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hcs
        rw [← hcs]
        simpa [mul_assoc] using hc
      · intro hs
        have : g⁻¹ * (g * s * g⁻¹) * g ∈ S.map (MulAut.conj g⁻¹).toMonoidHom :=
          ⟨g * s * g⁻¹, hs, by simp⟩
        rw [heq] at this
        simpa [mul_assoc] using this
    have hzD : z ∈ ⁅S, S⁆ := by
      have := conj_mem_commutator_of_mem_normalizer hgN hyD
      rw [← h1] at this
      simpa [mul_assoc] using this
    exact hzR (commutator_le_of_relIndex_two hRidx hzD)

theorem exists_normalizer_conj_mul [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {S R : Subgroup G} {z y : G} (hS : IsPGroup 2 S) (hzS : z ∈ S) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hSz : S ≤ centralizer ({z} : Set G))
    (hSmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ centralizer ({z} : Set G) → P = S)
    (hRS : R ≤ S) (hRidx : R.relIndex S = 2) (hzR : z ∉ R)
    (hZ : ∀ w ∈ R, (∀ s ∈ S, w * s = s * w) → w = 1 ∨ w = y) (hyD : y ∈ ⁅S, S⁆) :
    2 ∣ S.index ∧ ∃ x ∈ normalizer (S : Set G), x ∉ S ∧ x⁻¹ * z * x = z * y ∧
      ∃ P : Sylow 2 G, S ≤ P ∧ x ∈ (P : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := two_dvd_index_of_center_inf hnab hS hzS hz2 hz1 hSz hRS hRidx hzR hZ hyD
  refine ⟨hidx, ?_⟩
  obtain ⟨P, hSP⟩ := hS.exists_le_sylow
  have hne : S.subgroupOf (P : Subgroup G) ≠ ⊤ := by
    intro htop
    have hPS : (P : Subgroup G) ≤ S := by
      intro x hx
      have : (⟨x, hx⟩ : P) ∈ S.subgroupOf (P : Subgroup G) := by rw [htop]; trivial
      exact mem_subgroupOf.1 this
    have : S = P := le_antisymm hSP hPS
    exact P.not_dvd_index (this ▸ hidx)
  have hnil : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := P) _ (lt_of_le_of_ne le_top hne)
  obtain ⟨⟨x, hxP⟩, hxN, hxS⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : x ∈ normalizer (S : Set G) := by
    have : (⟨x, hxP⟩ : P) ∈ (normalizer (S : Set G)).subgroupOf (P : Subgroup G) := by
      rw [subgroupOf_normalizer_eq hSP]
      exact hxN
    exact mem_subgroupOf.1 this
  have hxS' : x ∉ S := fun h => hxS (mem_subgroupOf.2 h)
  refine ⟨x, hxN', hxS', ?_, P, hSP, hxP⟩
  obtain ⟨hwS, hwc⟩ := conj_mem_center_of_mem_normalizer hzS hSz hxN'
  set w := x⁻¹ * z * x with hw
  have hzinv : z⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
  have hidx2 : (R.subgroupOf S).index = 2 := hRidx
  by_cases hwR : w ∈ R
  · exfalso
    rcases hZ w hwR hwc with h1 | h1
    · apply hz1
      calc z = x * w * x⁻¹ := by rw [hw]; group
        _ = 1 := by rw [h1]; group
    · have hzD : z ∈ ⁅S, S⁆ := by
        have := conj_mem_commutator_of_mem_normalizer hxN' hyD
        rw [← h1, hw] at this
        simpa [mul_assoc] using this
      exact hzR (commutator_le_of_relIndex_two hRidx hzD)
  ·
    have hwzR : w * z ∈ R := by
      have h := (mul_mem_iff_of_index_two hidx2 (a := ⟨w, hwS⟩) (b := ⟨z, hzS⟩)).2
        ⟨fun h => absurd (mem_subgroupOf.1 h) hwR, fun h => absurd (mem_subgroupOf.1 h) hzR⟩
      exact mem_subgroupOf.1 h
    have hwzc : ∀ s ∈ S, w * z * s = s * (w * z) := by
      intro s hs
      have h1 := mem_centralizer_singleton_iff.1 (hSz hs)
      rw [mul_assoc, ← h1, ← mul_assoc, hwc s hs, mul_assoc]
    rcases hZ _ hwzR hwzc with h1 | h1
    · exfalso
      have hwz : w = z := by
        calc w = w * z * z⁻¹ := by group
          _ = z := by rw [h1, one_mul, hzinv]
      have hxC : x ∈ centralizer ({z} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc x * z = x * w := by rw [hwz]
          _ = z * x := by rw [hw]; group
      have hP' := hSmax ((P : Subgroup G) ⊓ centralizer ({z} : Set G))
        (P.isPGroup'.to_le inf_le_left) (le_inf hSP hSz) inf_le_right
      exact hxS' (hP' ▸ ⟨hxP, hxC⟩)
    ·
      have hyz : y * z = z * y := by
        have : y ∈ R := h1 ▸ hwzR
        exact mem_centralizer_singleton_iff.1 (hSz (hRS this))
      calc w = w * z * z⁻¹ := by group
        _ = z * y := by rw [h1, hzinv, hyz]

end CFSG.OddStandard.AltStdSmall
