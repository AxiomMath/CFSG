module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.ComponentClassification.GSThmB.QPUAlt

open CFSG Subgroup Equiv Equiv.Perm

theorem isPComponent_map_of_injective {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (φ : X →* Y) (hφ : Function.Injective φ) [φ.range.Normal] {L : Subgroup X}
    (hL : IsPComponent 2 L) : IsPComponent 2 (L.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := MonoidHom.ofInjective hφ
  have h1 := CatalogueBAlternating.pComponent_of_normal_subgroup 2 φ.range (L.map e.toMonoidHom)
    (CatalogueBAlternating.pComponent_map_equiv 2 e L hL)
  have h2 : (L.map e.toMonoidHom).map φ.range.subtype = L.map φ := by
    rw [map_map]
    rfl
  rwa [h2] at h1

variable {n : ℕ}

theorem isPComponent_centralizer_alternating {s : alternatingGroup (Fin n)} (hs : s * s = 1)
    {P : Subgroup (alternatingGroup (Fin n))}
    (hPs : P ≤ centralizer ({s} : Set (alternatingGroup (Fin n))))
    (hP : IsPComponent 2 (P.subgroupOf (centralizer ({s} : Set (alternatingGroup (Fin n)))))) :
    5 ≤ Nat.card {x : Fin n // (s : Perm (Fin n)) x = x} ∧ IsSimpleGroup P ∧
      Even (Nat.card P) ∧
      ∀ a b c : Fin n, (s : Perm (Fin n)) a = a → (s : Perm (Fin n)) b = b →
        (s : Perm (Fin n)) c = c → a ≠ b → a ≠ c → b ≠ c →
        ∃ x ∈ P, ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = swap a b * swap a c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : Perm (Fin n) := (s : Perm (Fin n)) with hτ
  set Q : Subgroup (Perm (Fin n)) := zpowers τ with hQ
  set C := centralizer ({s} : Set (alternatingGroup (Fin n))) with hC
  have hττ : τ * τ = 1 := by
    have h := congrArg Subtype.val hs
    simpa using h
  have hpow : ∀ k : ℤ, τ ^ k = 1 ∨ τ ^ k = τ := by
    intro k
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, hττ, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hττ, one_zpow, one_mul, zpow_one]
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rcases hpow k with h | h
    · simp [h]
    · simp [h, pow_two, hττ]
  set N := normalizer (Q : Set (Perm (Fin n))) with hN
  have hcN : ∀ g : Perm (Fin n), τ * g = g * τ → g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQ, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  have hCm : ∀ x : C, τ * ((x : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ((x : alternatingGroup (Fin n)) : Perm (Fin n)) * τ := fun x =>
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.2)).symm
  let ι : C →* N := ((alternatingGroup (Fin n)).subtype.comp C.subtype).codRestrict N
    fun x => hcN _ (hCm x)
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : Perm (Fin n))) hxy))
  have hrange : ι.range = (alternatingGroup (Fin n)).subgroupOf N := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (x : alternatingGroup (Fin n)).2
    · intro y hy
      have hyA : (y : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hy
      have hyτ : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ = τ := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rcases hpow k with h | h
        · rw [h] at hk
          have h1 : τ = 1 := by
            rw [eq_comm, mul_inv_eq_one, mul_eq_left] at hk
            exact hk
          rw [h1, mul_one, mul_inv_cancel]
        · rw [← hk, h]
      have hcomm : s * ⟨y, hyA⟩ = ⟨y, hyA⟩ * s := by
        apply Subtype.ext
        change τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ
        calc τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin n)) * τ := by group
      exact ⟨⟨⟨y, hyA⟩, mem_centralizer_singleton_iff.mpr hcomm.symm⟩, Subtype.ext rfl⟩
  have : ι.range.Normal := by
    rw [hrange]
    infer_instance
  have hL₁ : IsPComponent 2 ((P.subgroupOf C).map ι) := isPComponent_map_of_injective ι hι hP
  obtain ⟨hdeg, hLeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ2 _ hL₁
  have hval : ∀ x : C, ((ι x : N) : Perm (Fin n)) = ((x : alternatingGroup (Fin n)) : Perm _) :=
    fun _ => rfl
  have hfix : ∀ x : Fin n, x ∈ MulAction.fixedPoints Q (Fin n) ↔ τ x = x := by
    intro x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hx
      exact hx ⟨τ, mem_zpowers τ⟩
    · rintro hx ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact Perm.zpow_apply_eq_self_of_apply_eq_self hx k
  let eΩ : MulAction.fixedPoints Q (Fin n) ≃ {x : Fin n // τ x = x} := Equiv.subtypeEquivRight hfix
  refine ⟨Nat.card_congr eΩ ▸ hdeg, ?_⟩
  have hsA : IsSimpleGroup (alternatingGroup (MulAction.fixedPoints Q (Fin n))) :=
    alternatingGroup.isSimpleGroup hdeg
  let eP : P ≃* (P.subgroupOf C).map ι :=
    ((subgroupOfEquivOfLe hPs).symm.trans ((P.subgroupOf C).equivMapOfInjective ι hι))
  let eA : (P.subgroupOf C).map ι ≃* alternatingGroup (MulAction.fixedPoints Q (Fin n)) :=
    (MulEquiv.subgroupCongr hLeq).trans
      ((alternatingGroup (MulAction.fixedPoints Q (Fin n))).equivMapOfInjective _
        (CatalogueBAlternating.fixedPointsNormalizerHom_injective Q)).symm
  refine ⟨(eP.trans eA).isSimpleGroup, ?_, ?_⟩
  · rw [Nat.card_congr (eP.trans eA).toEquiv]
    have : Nontrivial (MulAction.fixedPoints Q (Fin n)) := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    have h2 := two_mul_nat_card_alternatingGroup (α := MulAction.fixedPoints Q (Fin n))
    rw [Nat.card_perm] at h2
    have h4 : 4 ∣ (Nat.card (MulAction.fixedPoints Q (Fin n))).factorial :=
      Nat.dvd_factorial (by norm_num) (by omega)
    rw [even_iff_two_dvd]
    omega
  intro a b c ha hb hc hab hac hbc
  have ha' := (hfix a).mpr ha
  have hb' := (hfix b).mpr hb
  have hc' := (hfix c).mpr hc
  set σ : Perm (MulAction.fixedPoints Q (Fin n)) :=
    swap ⟨a, ha'⟩ ⟨b, hb'⟩ * swap ⟨a, ha'⟩ ⟨c, hc'⟩ with hσ
  have hσA : σ ∈ alternatingGroup (MulAction.fixedPoints Q (Fin n)) := by
    rw [mem_alternatingGroup, hσ, map_mul, sign_swap (by simpa using hab),
      sign_swap (by simpa using hac)]
    rfl
  have hmem : (CatalogueBAlternating.fixedPointsNormalizerHom Q σ) ∈ (P.subgroupOf C).map ι := by
    rw [hLeq]
    exact ⟨σ, hσA, rfl⟩
  obtain ⟨x, hx, hxσ⟩ := hmem
  refine ⟨x, (mem_subgroupOf.mp hx), ?_⟩
  have h1 := congrArg Subtype.val hxσ
  rw [hval, CatalogueBAlternating.fixedPointsNormalizerHom_coe] at h1
  rw [h1]
  ext y
  by_cases hy : y ∈ MulAction.fixedPoints Q (Fin n)
  · rw [Perm.ofSubtype_apply_of_mem _ hy, hσ]
    simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def, Subtype.mk.injEq]
    split_ifs <;> simp_all
  · rw [Perm.ofSubtype_apply_of_not_mem _ hy]
    have hya : y ≠ a := fun h => hy (h ▸ ha')
    have hyb : y ≠ b := fun h => hy (h ▸ hb')
    have hyc : y ≠ c := fun h => hy (h ▸ hc')
    simp [swap_apply_of_ne_of_ne hya hyc, swap_apply_of_ne_of_ne hya hyb]

end CFSG.ComponentClassification.GSThmB.QPUAlt
