module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.AutModelNoSig

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.SmallOddCore
open scoped Pointwise

theorem noSig_conj {S : Type*} [Group S] {p : ℕ} {E : Subgroup (MulAut S)} (c : MulAut S)
    (hE : NoSig p E) : NoSig p (E.map (MulAut.conj c).toMonoidHom) := by
  intro T hTcop hET
  set T0 : Subgroup (MulAut S) := T.map (MulAut.conj c⁻¹).toMonoidHom with hT0
  have hcard : Nat.card T0 = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  have hmem : ∀ y : MulAut S, y ∈ T0 ↔ c * y * c⁻¹ ∈ T := by
    intro y
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ht
    · intro hy
      exact ⟨c * y * c⁻¹, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hnorm : E ≤ Subgroup.normalizer (T0 : Set (MulAut S)) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    have h1 := Subgroup.mem_normalizer_iff.1 (hET ⟨f, hf, rfl⟩) (c * y * c⁻¹)
    have h2 : (MulAut.conj c).toMonoidHom f * (c * y * c⁻¹) * ((MulAut.conj c).toMonoidHom f)⁻¹ =
        c * (f * y * f⁻¹) * c⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h2] at h1
    exact h1
  have hT0bot : T0 = ⊥ := hE T0 (hcard ▸ hTcop) hnorm
  rw [hT0, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c⁻¹).injective] at hT0bot
  exact hT0bot


theorem hom_mem_of_pow_eq_one {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut ↥P} (hα : α ^ p = 1) : h.hom α ∈ P := by
  have hxR : h.hom α ∈ R := h.elt_mem α
  have hpow : (h.hom α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  have hodd : Odd (Nat.card (Subgroup.zpowers (⟨h.hom α, hxR⟩ : ↥R))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · rw [h1]
      exact odd_one
    · rw [h1]
      exact hp.odd_of_ne_two hp2
  have hPnorm : (P.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.conj_mem g g.2 n hn⟩
  have hRP : Nat.card R ≤ 2 * Nat.card (P.subgroupOf R) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv]
    exact hidx
  have hle := odd_card_map_le_of_index_le_two (P.subgroupOf R) hRP hodd
  exact Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_zpowers _))

theorem noSig_conj_iff {S : Type*} [Group S] {p : ℕ} {E : Subgroup (MulAut S)} (c : MulAut S) :
    NoSig p (E.map (MulAut.conj c).toMonoidHom) ↔ NoSig p E := by
  refine ⟨fun h => ?_, noSig_conj c⟩
  have := noSig_conj (p := p) c⁻¹ h
  have heq : (E.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = E := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨c * x * c⁻¹, ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  rwa [heq] at this

theorem noSig_planes_of_autModel_rank {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup M} (hsyl : ∃ S : Sylow p ↥P, (S : Subgroup ↥P) = Q.subgroupOf P)
    (hA : ∀ E : Subgroup M, E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 2 →
      PFree p (R ⊓ Subgroup.centralizer (E : Set M) : Subgroup M))
    (hB : ∀ y ∈ P, orderOf y = p →
      RankOK p (R ⊓ Subgroup.centralizer ({y} : Set M) : Subgroup M)) :
    ∀ Ê : Subgroup (MulAut ↥P), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê := by
  intro Ê hÊ hÊ2
  haveI : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center ↥P = ⊥ := autModel_center_eq_bot h
  have hinj : Function.Injective (MulAut.conj : ↥P →* MulAut ↥P) :=
    conj_injective_of_center_bot_sg hcen
  have hÊP : ∀ α ∈ Ê, h.hom α ∈ P := fun α hα =>
    hom_mem_of_pow_eq_one h hidx hp hp2 (hÊ.2 α hα)
  set Q2 : Subgroup ↥P := (Ê.map h.hom).subgroupOf P with hQ2def
  have hÊeq : Ê = Q2.map (MulAut.conj : ↥P →* MulAut ↥P) := by
    ext α
    constructor
    · intro hα
      refine ⟨⟨h.hom α, hÊP α hα⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 ⟨α, hα, rfl⟩
      · apply h.hom_injective
        rw [autModel_hom_conj h]
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨β, hβ, hβa⟩ := Subgroup.mem_subgroupOf.1 ha
      have : MulAut.conj a = β := by
        apply h.hom_injective
        rw [autModel_hom_conj h]
        exact hβa.symm
      rw [this]
      exact hβ
  have hQ2el : IsElemAbelian p Q2 :=
    isElemAbelian_of_map_injective' hinj (hÊeq ▸ hÊ)
  have hQ2card : Nat.card Q2 = p ^ 2 := by
    rw [← hÊ2, hÊeq, Subgroup.card_map_of_injective hinj]
  obtain ⟨S1, hS1⟩ := hsyl
  obtain ⟨S', hS'⟩ := hQ2el.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P S' S1
  set E'P : Subgroup ↥P := MulAut.conj g • Q2 with hE'P
  have hE'Q : E'P ≤ Q.subgroupOf P := by
    rw [← hS1, ← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hS'
  have hE'Pmap : E'P = Q2.map (MulAut.conj g).toMonoidHom := rfl
  have hE'Pcard : Nat.card E'P = p ^ 2 := by
    rw [hE'Pmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hQ2card
  have hE'Pel : IsElemAbelian p E'P := by
    rw [hE'Pmap]
    exact hQ2el.map _
  have hNE' : NoSig p (E'P.map (MulAut.conj : ↥P →* MulAut ↥P)) := by
    refine noSig_of_autModel_rank h hp E'P hE'Pel hE'Pcard ?_ ?_
    · refine hA _ ?_ ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact Subgroup.mem_subgroupOf.1 (hE'Q ha)
      · exact hE'Pel.map _
      · rw [Subgroup.card_map_of_injective P.subtype_injective, hE'Pcard]
    · intro y hy hy1
      have hyP : (y : M) ∈ P := y.2
      have hyord : orderOf (y : M) = p := by
        have : y ^ p = 1 := hE'Pel.2 y hy
        have hy1' : (y : M) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
        exact orderOf_eq_prime (by rw [← Subgroup.coe_pow, this]; rfl) hy1'
      exact hB (y : M) hyP hyord
  have hcc : ∀ a0 : ↥P, (MulAut.conj (MulAut.conj g : MulAut ↥P)).toMonoidHom (MulAut.conj a0) =
      MulAut.conj (g * a0 * g⁻¹) := by
    intro a0
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  have hconj : E'P.map (MulAut.conj : ↥P →* MulAut ↥P) =
      Ê.map (MulAut.conj (MulAut.conj g : MulAut ↥P)).toMonoidHom := by
    ext β
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : a ∈ (MulAut.conj g • Q2 : Subgroup ↥P) := ha
      rw [Subgroup.mem_smul_pointwise_iff_exists] at ha'
      obtain ⟨a0, ha0, rfl⟩ := ha'
      refine ⟨MulAut.conj a0, ?_, ?_⟩
      · rw [hÊeq]
        exact ⟨a0, ha0, rfl⟩
      · rw [hcc]
        rfl
    · rintro ⟨_, hmem, rfl⟩
      rw [hÊeq] at hmem
      obtain ⟨a0, ha0, rfl⟩ := hmem
      refine ⟨g * a0 * g⁻¹, ?_, (hcc a0).symm⟩
      have : g * a0 * g⁻¹ ∈ (MulAut.conj g • Q2 : Subgroup ↥P) :=
        (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨a0, ha0, rfl⟩
      exact this
  rw [hconj] at hNE'
  exact (noSig_conj_iff (MulAut.conj g)).1 hNE'


theorem noSig_planes_of_autModel {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup M} (hsyl : ∃ S : Sylow p ↥P, (S : Subgroup ↥P) = Q.subgroupOf P)
    (hA : ∀ E : Subgroup M, E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 2 →
      PFree p (R ⊓ Subgroup.centralizer (E : Set M) : Subgroup M))
    (hB : ∀ y ∈ P, orderOf y = p → ∀ q k : ℕ, q.Prime → q ≠ p → 0 < k →
      q ^ k ∣ Nat.card (R ⊓ Subgroup.centralizer ({y} : Set M) : Subgroup M) →
        q ^ k % p ≠ 1) :
    ∀ Ê : Subgroup (MulAut ↥P), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê :=
  noSig_planes_of_autModel_rank h hidx hp hp2 hsyl hA fun y hy hord =>
    rankOK_of_primePowOK (hB y hy hord)

theorem card_inf_centralizer_conj {M : Type*} [Group M] [Finite M] (B : Subgroup M) {g : M}
    (hg : g ∈ B) (y' : M) :
    Nat.card (B ⊓ Subgroup.centralizer ({g * y' * g⁻¹} : Set M) : Subgroup M) =
      Nat.card (B ⊓ Subgroup.centralizer ({y'} : Set M) : Subgroup M) := by
  have hmap : (B ⊓ Subgroup.centralizer ({y'} : Set M)).map (MulAut.conj g).toMonoidHom =
      B ⊓ Subgroup.centralizer ({g * y' * g⁻¹} : Set M) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyB, hyC⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using B.mul_mem (B.mul_mem hg hyB) (B.inv_mem hg)
      · have hyC' : y * y' = y' * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
        show (MulAut.conj g).toMonoidHom y ∈ Subgroup.centralizer ({g * y' * g⁻¹} : Set M)
        rw [Subgroup.mem_centralizer_singleton_iff]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc g * y * g⁻¹ * (g * y' * g⁻¹) = g * (y * y') * g⁻¹ := by group
          _ = g * (y' * y) * g⁻¹ := by rw [hyC']
          _ = g * y' * g⁻¹ * (g * y * g⁻¹) := by group
    · rintro ⟨hxB, hxC⟩
      refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      · exact B.mul_mem (B.mul_mem (B.inv_mem hg) hxB) hg
      · have hxC' : x * (g * y' * g⁻¹) = (g * y' * g⁻¹) * x :=
          Subgroup.mem_centralizer_singleton_iff.1 hxC
        show g⁻¹ * x * g ∈ Subgroup.centralizer ({y'} : Set M)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g⁻¹ * x * g * y' = g⁻¹ * (x * (g * y' * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y' * g⁻¹) * x) * g := by rw [hxC']
          _ = y' * (g⁻¹ * x * g) := by group
  rw [← hmap]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end CFSG.HardMathSupport.Dickson.I271
