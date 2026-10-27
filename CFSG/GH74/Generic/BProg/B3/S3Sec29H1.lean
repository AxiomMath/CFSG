module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29H

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29H1

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def bAct {B J : Subgroup G} (hBN : B ≤ normalizer (J : Set G))
    (e : kBar J ≃* alternatingGroup (Fin 7)) : ↥B →* Equiv.Perm (Fin 7) :=
  (GLS.Th2.Obs.a7Act J e).comp (Subgroup.inclusion hBN)

@[expose] noncomputable def pre {B J : Subgroup G} (hBN : B ≤ normalizer (J : Set G))
    (e : kBar J ≃* alternatingGroup (Fin 7)) (X : Subgroup (Equiv.Perm (Fin 7))) : Subgroup G :=
  (X.comap (bAct hBN e)).map B.subtype

omit [Finite G] in
theorem mem_pre {B J : Subgroup G} {hBN : B ≤ normalizer (J : Set G)}
    {e : kBar J ≃* alternatingGroup (Fin 7)} {X : Subgroup (Equiv.Perm (Fin 7))} {g : G} :
    g ∈ pre hBN e X ↔ ∃ hg : g ∈ B, GLS.Th2.Obs.a7Act J e ⟨g, hBN hg⟩ ∈ X := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.2, hb⟩
  · rintro ⟨hg, hX⟩
    exact ⟨⟨g, hg⟩, hX, rfl⟩

omit [Finite G] in
theorem pre_le {B J : Subgroup G} (hBN : B ≤ normalizer (J : Set G))
    (e : kBar J ≃* alternatingGroup (Fin 7)) (X : Subgroup (Equiv.Perm (Fin 7))) :
    pre hBN e X ≤ B := Subgroup.map_subtype_le _

omit [Finite G] in
theorem range_bAct {B J : Subgroup G} (hBN : B ≤ normalizer (J : Set G))
    (e : kBar J ≃* alternatingGroup (Fin 7)) :
    (bAct hBN e).range = (B.subgroupOf (normalizer (J : Set G))).map (GLS.Th2.Obs.a7Act J e) := by
  ext σ
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, hBN b.2⟩, b.2, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

theorem two_mul_card_pre {B J : Subgroup G} (hBN : B ≤ normalizer (J : Set G))
    (e : kBar J ≃* alternatingGroup (Fin 7)) {F' : Subgroup (Equiv.Perm (Fin 7))}
    (hF'R : F' ≤ (bAct hBN e).range) (h2 : 2 * Nat.card ↥F' = Nat.card ↥(bAct hBN e).range) :
    2 * Nat.card ↥(pre hBN e F') = Nat.card ↥B := by
  have hc : Nat.card ↥(pre hBN e F') = Nat.card ↥(F'.comap (bAct hBN e)) :=
    Subgroup.card_map_of_injective B.subtype_injective
  have hidx : (F'.comap (bAct hBN e)).index = 2 := by
    rw [Subgroup.index_comap]
    have h1 := Subgroup.card_mul_index (F'.subgroupOf (bAct hBN e).range)
    have h3 : Nat.card ↥(F'.subgroupOf (bAct hBN e).range) = Nat.card ↥F' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF'R).toEquiv
    rw [h3] at h1
    have hpos : 0 < Nat.card ↥F' := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [Subgroup.relIndex, h1, ← h2, mul_comm])
  have h4 := Subgroup.card_mul_index (F'.comap (bAct hBN e))
  rw [hidx] at h4
  rw [hc, ← h4, mul_comm]

omit [Finite G] in
theorem mem_core_of_a7Act_eq_one {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7)) {k : G}
    (hk : k ∈ J) (h1 : GLS.Th2.Obs.a7Act J e ⟨k, Subgroup.le_normalizer hk⟩ = 1) :
    k ∈ pPrimeCoreOf 2 J := by
  rw [GLS.Th2.Obs.a7Act_of_mem e hk] at h1
  have h2 : e (QuotientGroup.mk (⟨k, hk⟩ : ↥J)) = 1 := Subtype.ext h1
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
  exact ⟨⟨k, hk⟩, h2, rfl⟩

omit [Finite G] in
theorem a7Act_eq_one_of_mem_core {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7)) {k : G}
    (hk : k ∈ pPrimeCoreOf 2 J) :
    GLS.Th2.Obs.a7Act J e ⟨k, Subgroup.le_normalizer (TwoThin.pPrimeCoreOf_le J hk)⟩ = 1 := by
  obtain ⟨k', hk', rfl⟩ := hk
  change GLS.Th2.Obs.a7Act J e ⟨(k' : G), Subgroup.le_normalizer k'.2⟩ = 1
  rw [GLS.Th2.Obs.a7Act_of_mem e k'.2]
  have h2 : (QuotientGroup.mk (⟨(k' : G), k'.2⟩ : ↥J) : kBar J) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hk'
  rw [h2, map_one]
  rfl

theorem exists_v {J P : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7))
    (hPN : P ≤ normalizer (J : Set G)) (hP : IsPGroup 2 ↥P) {u : Equiv.Perm (Fin 7)}
    (hu : u ∈ alternatingGroup (Fin 7)) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hPu : ∀ p (hp : p ∈ P), GLS.Th2.Obs.a7Act J e ⟨p, hPN hp⟩ * u =
      u * GLS.Th2.Obs.a7Act J e ⟨p, hPN hp⟩) :
    ∃ v : G, ∃ hv : v ∈ J, v * v = 1 ∧ v ≠ 1 ∧ (∀ p ∈ P, p * v = v * p) ∧
      GLS.Th2.Obs.a7Act J e ⟨v, Subgroup.le_normalizer hv⟩ = u := by
  classical
  obtain ⟨j₀, hj₀⟩ := QuotientGroup.mk_surjective (e.symm ⟨u, hu⟩)
  have hj₀J : (j₀ : G) ∈ J := j₀.2
  have he₀ : GLS.Th2.Obs.a7Act J e ⟨(j₀ : G), Subgroup.le_normalizer hj₀J⟩ = u := by
    rw [GLS.Th2.Obs.a7Act_of_mem e hj₀J]
    have : (QuotientGroup.mk (⟨(j₀ : G), hj₀J⟩ : ↥J) : kBar J) = e.symm ⟨u, hu⟩ := hj₀
    rw [this, MulEquiv.apply_symm_apply]
  set N := pPrimeCoreOf 2 J with hNdef
  have hNodd : Odd (Nat.card ↥N) := TwoThin.card_pPrimeCoreOf_odd J
  have hPN' : P ≤ normalizer (N : Set G) := fun p hp =>
    TwoThin.mem_normalizer_pPrimeCoreOf (hPN hp)
  have hgN : (j₀ : G) ∈ normalizer (N : Set G) :=
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hj₀J)
  have hg2 : (j₀ : G) * j₀ ∈ N := by
    refine mem_core_of_a7Act_eq_one e (J.mul_mem hj₀J hj₀J) ?_
    have : (⟨(j₀ : G) * j₀, Subgroup.le_normalizer (J.mul_mem hj₀J hj₀J)⟩ :
        ↥(normalizer (J : Set G))) = ⟨(j₀ : G), Subgroup.le_normalizer hj₀J⟩ *
          ⟨(j₀ : G), Subgroup.le_normalizer hj₀J⟩ := rfl
    rw [this, map_mul, he₀, hu2]
  have hg : ∀ p ∈ P, (j₀ : G)⁻¹ * (p * j₀ * p⁻¹) ∈ N := by
    intro p hp
    have hpj : p * (j₀ : G) * p⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hPN hp) _).1 hj₀J
    have hk : (j₀ : G)⁻¹ * (p * j₀ * p⁻¹) ∈ J := J.mul_mem (J.inv_mem hj₀J) hpj
    refine mem_core_of_a7Act_eq_one e hk ?_
    have : (⟨(j₀ : G)⁻¹ * (p * j₀ * p⁻¹), Subgroup.le_normalizer hk⟩ :
        ↥(normalizer (J : Set G))) = (⟨(j₀ : G), Subgroup.le_normalizer hj₀J⟩)⁻¹ *
          (⟨p, hPN hp⟩ * ⟨(j₀ : G), Subgroup.le_normalizer hj₀J⟩ * (⟨p, hPN hp⟩)⁻¹) := rfl
    rw [this, map_mul, map_inv, map_mul, map_mul, map_inv, he₀, hPu p hp]
    group
  obtain ⟨w, hwN, hww, hwP⟩ := S3Sec29H.exists_inv_fixed_mem_coset hP hNodd hPN' hgN hg2 hg
  have hwJ : w ∈ J := by
    have : w = (j₀ : G) * ((j₀ : G)⁻¹ * w) := by group
    rw [this]
    exact J.mul_mem hj₀J (TwoThin.pPrimeCoreOf_le J hwN)
  have hwu : GLS.Th2.Obs.a7Act J e ⟨w, Subgroup.le_normalizer hwJ⟩ = u := by
    have : (⟨w, Subgroup.le_normalizer hwJ⟩ : ↥(normalizer (J : Set G))) =
        ⟨(j₀ : G), Subgroup.le_normalizer hj₀J⟩ *
          ⟨(j₀ : G)⁻¹ * w, Subgroup.le_normalizer (TwoThin.pPrimeCoreOf_le J hwN)⟩ :=
      Subtype.ext (by simp)
    rw [this, map_mul, he₀, a7Act_eq_one_of_mem_core e hwN, mul_one]
  refine ⟨w, hwJ, hww, fun hw1 => hu1 ?_, hwP, hwu⟩
  rw [← hwu]
  have : (⟨w, Subgroup.le_normalizer hwJ⟩ : ↥(normalizer (J : Set G))) = 1 :=
    Subtype.ext hw1
  rw [this, map_one]

end S3Sec29H1

end CFSG.GH74.Generic.BProg.B3
