module

public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.AGLEmbedding

section Filter

variable {A : Type*} [Group A]

@[expose] def ThreeFilter (I : Subgroup A) : Prop :=
  ∃ D E : Subgroup A, D.Normal ∧ I ≤ D ∧ D ≤ E ∧ (∀ d ∈ D, ∃ k : ℕ, d ^ 3 ^ k ∈ I) ∧
    (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ D) ∧ ∀ (a : A) (k : ℕ), a ^ 3 ^ k ∈ E → a ∈ E

theorem ThreeFilter.comap {A' : Type*} [Group A'] {I' : Subgroup A'} (h : ThreeFilter I')
    (φ : A →* A') : ThreeFilter (I'.comap φ) := by
  obtain ⟨D, E, hDn, hID, hDE, hDI, hcomm, hE⟩ := h
  refine ⟨D.comap φ, E.comap φ, hDn.comap φ, Subgroup.comap_mono hID,
    Subgroup.comap_mono hDE, fun d hd => ?_, fun x hx y hy => ?_, fun a k ha => ?_⟩
  · obtain ⟨k, hk⟩ := hDI (φ d) hd
    exact ⟨k, by simpa [map_pow] using hk⟩
  · simpa using hcomm (φ x) hx (φ y) hy
  · exact hE (φ a) k (by simpa [map_pow] using ha)

theorem le_sup_sylow_of_pGroup [Finite A] {I M : Subgroup A} [I.Normal] [M.Normal]
    (h3 : ∀ m ∈ M, ∃ k : ℕ, m ^ 3 ^ k ∈ I) (S : Sylow 3 A) : M ≤ I ⊔ (S : Subgroup A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj := QuotientGroup.mk'_surjective I
  have hMp : IsPGroup 3 (M.map (QuotientGroup.mk' I)) := by
    rintro ⟨y, m, hm, rfl⟩
    obtain ⟨k, hk⟩ := h3 m hm
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk' I m) ^ 3 ^ k = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have : (M.map (QuotientGroup.mk' I)).Normal := Subgroup.Normal.map ‹_› _ hsurj
  have hle := hMp.le_sylow_of_normal (S.mapSurjective hsurj)
  intro m hm
  obtain ⟨s, hs, hsm⟩ := hle ⟨m, hm, rfl⟩
  have hker : m * s⁻¹ ∈ I := by
    rw [← QuotientGroup.ker_mk' I, MonoidHom.mem_ker, map_mul, map_inv, ← hsm, mul_inv_cancel]
  have hm' : m = (m * s⁻¹) * s := by group
  rw [hm']
  exact Subgroup.mul_mem_sup hker hs

def threeElementSubgroup {D E : Subgroup A} [D.Normal] (hDE : D ≤ E)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ D)
    (hE : ∀ (a : A) (k : ℕ), a ^ 3 ^ k ∈ E → a ∈ E) : Subgroup A where
  carrier := {a | ∃ k : ℕ, a ^ 3 ^ k ∈ D}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    have ha : a ∈ E := hE a k (hDE hk)
    have hb : b ∈ E := hE b l (hDE hl)
    have hab : Commute (QuotientGroup.mk' D a) (QuotientGroup.mk' D b) := by
      have h1 : (QuotientGroup.mk' D) (a * b * a⁻¹ * b⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (hcomm a ha b hb)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    refine ⟨k + l, (QuotientGroup.eq_one_iff _).1 ?_⟩
    change (QuotientGroup.mk' D) ((a * b) ^ 3 ^ (k + l)) = 1
    have hak : (QuotientGroup.mk' D a) ^ 3 ^ k = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hk
    have hbl : (QuotientGroup.mk' D b) ^ 3 ^ l = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hl
    rw [map_pow, map_mul, hab.mul_pow, pow_add, pow_mul, hak, one_pow, mul_comm (3 ^ k),
      pow_mul, hbl, one_pow, mul_one]
  inv_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rw [inv_pow]; exact inv_mem hk⟩

theorem ThreeFilter.normal_sup_sylow [Finite A] {I : Subgroup A} [I.Normal] (h : ThreeFilter I)
    (S : Sylow 3 A) : (I ⊔ (S : Subgroup A)).Normal := by
  obtain ⟨D, E, hDn, hID, hDE, hDI, hcomm, hE⟩ := h
  have hMmem : ∀ m, m ∈ threeElementSubgroup hDE hcomm hE ↔ ∃ k : ℕ, m ^ 3 ^ k ∈ D :=
    fun m => Iff.rfl
  have hMn : (threeElementSubgroup hDE hcomm hE).Normal := by
    refine ⟨fun a ha g => (hMmem _).2 ?_⟩
    obtain ⟨k, hk⟩ := (hMmem a).1 ha
    exact ⟨k, by rw [conj_pow]; exact hDn.conj_mem _ hk g⟩
  have h1 : threeElementSubgroup hDE hcomm hE ≤ I ⊔ (S : Subgroup A) := by
    refine le_sup_sylow_of_pGroup (fun m hm => ?_) S
    obtain ⟨k, hk⟩ := (hMmem m).1 hm
    obtain ⟨j, hj⟩ := hDI _ hk
    exact ⟨k + j, by rwa [← pow_mul, ← pow_add] at hj⟩
  have h2 : I ⊔ (S : Subgroup A) ≤ threeElementSubgroup hDE hcomm hE := by
    refine sup_le (fun i hi => (hMmem i).2 ⟨0, by simpa using hID hi⟩) fun s hs => ?_
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    refine (hMmem s).2 ⟨k, ?_⟩
    have : s ^ 3 ^ k = 1 := congrArg Subtype.val hk
    rw [this]
    exact one_mem D
  have hM : threeElementSubgroup hDE hcomm hE = I ⊔ (S : Subgroup A) := le_antisymm h1 h2
  rw [← hM]
  exact hMn

end Filter

section Quotient

variable {A : Type*} [Group A]

theorem pow_mem_normal_of_relIndex_dvd {I D : Subgroup A} [I.Normal] {n : ℕ}
    (h : I.relIndex D ∣ n) {d : A} (hd : d ∈ D) : d ^ n ∈ I := by
  obtain ⟨c, rfl⟩ := h
  have h1 : (⟨d, hd⟩ : D) ^ I.relIndex D ∈ I.subgroupOf D :=
    Subgroup.pow_index_mem (I.subgroupOf D) (⟨d, hd⟩ : D)
  rw [pow_mul]
  exact Subgroup.pow_mem _ (by simpa [Subgroup.mem_subgroupOf] using h1) c

theorem mem_of_pow_mem_of_coprime_index {E : Subgroup A} [E.Normal] {n : ℕ}
    (hn : Nat.Coprime n E.index) {a : A} (ha : a ^ n ∈ E) : a ∈ E := by
  have h1 : (QuotientGroup.mk a : A ⧸ E) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 ha
  have h2 : orderOf (QuotientGroup.mk a : A ⧸ E) ∣ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk a : A ⧸ E) ∣ E.index := orderOf_dvd_natCard _
  have h4 : orderOf (QuotientGroup.mk a : A ⧸ E) = 1 :=
    Nat.eq_one_of_dvd_one (hn.gcd_eq_one ▸ Nat.dvd_gcd h2 h3)
  exact (QuotientGroup.eq_one_iff a).1 (orderOf_eq_one_iff.1 h4)

theorem commutator_mem_of_cyclic_quotient {D E : Subgroup A} [D.Normal] {g : A}
    (hg : ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D) : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ D := by
  have hpow : ∀ x ∈ E, ∃ k : ℤ, (QuotientGroup.mk' D) x = ((QuotientGroup.mk' D) g) ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := hg x hx
    have h1 : (QuotientGroup.mk' D) (g ^ k * x) = 1 := (QuotientGroup.eq_one_iff _).2 hk
    rw [map_mul, map_zpow] at h1
    exact ⟨-k, by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_right h1⟩
  intro x hx y hy
  obtain ⟨i, hi⟩ := hpow x hx
  obtain ⟨j, hj⟩ := hpow y hy
  refine (QuotientGroup.eq_one_iff _).1 ?_
  change (QuotientGroup.mk' D) (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hi, hj]
  exact commutatorElement_eq_one_iff_mul_comm.2 ((Commute.refl _).zpow_zpow i j)

end Quotient

section Cover

open CFSG.ComponentClassification

theorem kOutNormalSylow_three_of_filter {K P : Type} [Group K] [Finite K] [Group P]
    [Group.IsPerfect K] (e : K ⧸ Subgroup.center K ≃* P) (h : ThreeFilter (inner P)) :
    KOutNormalSylow 3 K := by
  set ι : MulAut K →* MulAut P :=
    (MulAut.congr e).toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom K)
  have hinj : Function.Injective ι :=
    (MulAut.congr e).injective.comp (PerfectAutomorphisms.centerQuotientHom_injective K)
  have hI : inner K = (inner P).comap ι := by
    ext a
    constructor
    · intro ha
      have h1 := centerQuotient_inner_le ha
      rw [← inner_map_congr e]
      exact ⟨_, h1, rfl⟩
    · intro ha
      rw [Subgroup.mem_comap, ← inner_map_congr e] at ha
      obtain ⟨b, hb, hba⟩ := ha
      have h1 : PerfectAutomorphisms.centerQuotientHom K a ∈ inner (K ⧸ Subgroup.center K) := by
        rw [← (MulAut.congr e).injective hba]
        exact hb
      obtain ⟨x, hx⟩ := h1
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
      exact ⟨y, PerfectAutomorphisms.centerQuotientHom_injective K
        ((centerQuotient_conj y).trans hx)⟩
  intro S
  have hK : ThreeFilter (inner K) := hI ▸ h.comap ι
  exact hK.normal_sup_sylow S

end Cover

end CFSG.LocalAnalysis.RankThreeTheoremC
