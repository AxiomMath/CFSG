module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Core

variable {G : Type} [Group G] [Finite G]

theorem mem_primeCoreOf_iff {p : ℕ} {L : Subgroup G} (x : ↥L) :
    (x : G) ∈ GLAPPrimeCoreOf p L ↔ x ∈ GLAPPrimeCore p ↥L :=
  ⟨fun ⟨c', hc', hv⟩ => by
    have : c' = x := Subtype.ext hv
    rwa [this] at hc', fun h => ⟨x, h, rfl⟩⟩

theorem normalizer_le_normalizer_primeCoreOf (p : ℕ) (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
  normalizer_le_normalizer_glaPPrimeCoreOf p L

@[expose] def conjL (L : Subgroup G) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    MulAut ↥L where
  toFun x := ⟨b⁻¹ * x * b, by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (L : Set G)).inv_mem hb)
      (x : G)).1 x.2
    simpa using this⟩
  invFun x := ⟨b * x * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb (x : G)).1 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjL_apply (L : Subgroup G) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : ((conjL L b hb x : ↥L) : G) = b⁻¹ * x * b := rfl

theorem conjL_core (L : Subgroup G) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    (GLAPPrimeCore 3 ↥L).map (conjL L b hb).toMonoidHom = GLAPPrimeCore 3 ↥L := by
  have hN := Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_primeCoreOf 3 L hb)
  have hN' := Subgroup.mem_normalizer_iff.1
    (normalizer_le_normalizer_primeCoreOf 3 L ((Subgroup.normalizer (L : Set G)).inv_mem hb))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : (x : G) ∈ GLAPPrimeCoreOf 3 L := (mem_primeCoreOf_iff x).2 hx
    have h2 := (hN' x).1 h1
    rw [← mem_primeCoreOf_iff]
    simpa [conjL_apply] using h2
  · intro hy
    refine ⟨(conjL L b hb).symm y, ?_, MulEquiv.apply_symm_apply _ _⟩
    have h1 : (y : G) ∈ GLAPPrimeCoreOf 3 L := (mem_primeCoreOf_iff y).2 hy
    have h2 := (hN y).1 h1
    show (conjL L b hb).symm y ∈ GLAPPrimeCore 3 ↥L
    rw [← mem_primeCoreOf_iff]
    exact h2

@[expose] noncomputable def barAut (L : Subgroup G) (b : G)
    (hb : b ∈ Subgroup.normalizer (L : Set G)) : MulAut (PQuot 3 L) :=
  QuotientGroup.congr (GLAPPrimeCore 3 ↥L) (GLAPPrimeCore 3 ↥L) (conjL L b hb)
    (conjL_core L b hb)

theorem barAut_mk (L : Subgroup G) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    barAut L b hb (QuotientGroup.mk x) = QuotientGroup.mk (conjL L b hb x) := rfl

theorem barAut_pow_three (L : Subgroup G) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hb3 : b ^ 3 = 1) : barAut L b hb ^ 3 = 1 := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have h3 : ((barAut L b hb ^ 3) (QuotientGroup.mk x) : PQuot 3 L) =
      barAut L b hb (barAut L b hb (barAut L b hb (QuotientGroup.mk x))) := rfl
  rw [h3, barAut_mk, barAut_mk, barAut_mk]
  show (QuotientGroup.mk _ : PQuot 3 L) = QuotientGroup.mk x
  congr 1
  apply Subtype.ext
  simp only [conjL_apply]
  have hb3' : b * b * b = 1 := by
    have : b ^ 3 = b * b * b := by rw [pow_succ, pow_two]
    rw [← this]
    exact hb3
  calc b⁻¹ * (b⁻¹ * (b⁻¹ * (x : G) * b) * b) * b = (b * b * b)⁻¹ * x * (b * b * b) := by group
    _ = x := by rw [hb3']; simp

theorem inducesInnerMod_of_inner {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (h : barAut L b hb ∈ inner (PQuot 3 L)) :
    InducesInnerMod 3 L b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨((l'⁻¹ : ↥L) : G), (l'⁻¹ : ↥L).2, fun y hy => ?_⟩
  have h1 := congrArg (fun α : MulAut (PQuot 3 L) => α (QuotientGroup.mk ⟨y, hy⟩)) hc
  simp only [MulAut.conj_apply, barAut_mk] at h1
  have h2 : (QuotientGroup.mk (conjL L b hb ⟨y, hy⟩) : PQuot 3 L) =
      QuotientGroup.mk (l' * ⟨y, hy⟩ * l'⁻¹) := by
    rw [← h1]
    rfl
  have h3 := (QuotientGroup.eq (s := GLAPPrimeCore 3 ↥L)).1 h2.symm
  rw [← mem_primeCoreOf_iff] at h3
  simpa [conjL_apply, mul_assoc] using h3

theorem forall_cube_inner_of_card_outer {M : Type*} [Group M]
    (hne : ¬ 3 ∣ Nat.card (Outer M)) (α : MulAut M) (hα : α ^ 3 = 1) : α ∈ inner M := by
  have h1 : orderOf (QuotientGroup.mk α : Outer M) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hα]
    rfl
  have h2 := orderOf_dvd_natCard (QuotientGroup.mk α : Outer M)
  have h3 : orderOf (QuotientGroup.mk α : Outer M) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hne
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)


theorem eq_one_of_mem_primeCore_of_pow_three {K : Subgroup G} {y : ↥K}
    (hy : y ∈ GLAPPrimeCore 3 ↥K) (hy3 : y ^ 3 = 1) : y = 1 := by
  have hdvd1 : orderOf (⟨y, hy⟩ : GLAPPrimeCore 3 ↥K) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hy3
  have hdvd2 := orderOf_dvd_natCard (⟨y, hy⟩ : GLAPPrimeCore 3 ↥K)
  have hcop := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)
  have h1 : orderOf (⟨y, hy⟩ : GLAPPrimeCore 3 ↥K) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
  have := orderOf_eq_one_iff.1 h1
  exact congrArg Subtype.val this

@[expose] noncomputable def piOf (L : Subgroup G) {M : Type*} [Group M] (e : PQuot 3 L ≃* M) :
    ↥L →* M :=
  e.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))

theorem piOf_ker (L : Subgroup G) {M : Type*} [Group M] (e : PQuot 3 L ≃* M) :
    (piOf L e).ker = GLAPPrimeCore 3 ↥L := by
  unfold piOf
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

theorem piOf_surjective (L : Subgroup G) {M : Type*} [Group M] (e : PQuot 3 L ≃* M) :
    Function.Surjective (piOf L e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem isElemAbelian_subgroupOf {p : ℕ} {E L : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf L) := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have h := mul_comm' (⟨(a : G), a.2⟩ : E) ⟨(b : G), b.2⟩
    exact congrArg (fun z : ↥E => (z : G)) h
  · apply Subtype.ext
    have := hE.2 (x : G) hx
    simpa using this

theorem map_le_normalizer_map {K : Subgroup G} {M : Type*} [Group M] (π : ↥K →* M)
    {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    (A.subgroupOf K).map π ≤ Subgroup.normalizer (((B.subgroupOf K).map π : Subgroup M) : Set M) := by
  have hn : ∀ x ∈ A.subgroupOf K, ∀ y : ↥K, y ∈ B.subgroupOf K ↔ x * y * x⁻¹ ∈ B.subgroupOf K := by
    intro x hx y
    have hxE : (x : G) ∈ A := hx
    exact (Subgroup.mem_normalizer_iff.1 (hAB hxE)) (y : G)
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨x * t * x⁻¹, (hn x hx t).1 ht, by simp⟩
  · rintro ⟨t, ht, hty⟩
    refine ⟨x⁻¹ * t * x, ?_, ?_⟩
    · have := (hn x⁻¹ ((A.subgroupOf K).inv_mem hx) t).1 ht
      simpa using this
    · have : π x * y * (π x)⁻¹ = π t := hty.symm
      calc π (x⁻¹ * t * x) = (π x)⁻¹ * π t * π x := by simp
        _ = (π x)⁻¹ * (π x * y * (π x)⁻¹) * π x := by rw [this]
        _ = y := by group

theorem rankFine_transport {L : Subgroup G} {M : Type*} [Group M] (e : PQuot 3 L ≃* M) {B : ℕ}
    (h : ∀ E T : Subgroup M, IsElemAbelian 3 E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set M) → Nat.card E ≤ B) :
    ∀ E T : Subgroup G, E ≤ L → IsElemAbelian 3 E → T ≤ L → IsPGroup 2 T →
      ¬ T ≤ GLAPPrimeCoreOf 3 L → E ≤ Subgroup.normalizer (T : Set G) → Nat.card E ≤ B := by
  intro E T hEL hE hTL hT hTN hET
  set π := piOf L e with hπ
  have hker := piOf_ker L e
  let E' : Subgroup ↥L := E.subgroupOf L
  let T' : Subgroup ↥L := T.subgroupOf L
  have hE' : IsElemAbelian 3 E' := isElemAbelian_subgroupOf hE
  have hT' : IsPGroup 2 T' := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hinj : Function.Injective (π.comp E'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : ↥L) ∈ π.ker := hx
    rw [hker] at hxk
    have hx3 : (x : ↥L) ^ 3 = 1 := hE'.2 x x.2
    exact Subtype.ext (eq_one_of_mem_primeCore_of_pow_three hxk hx3)
  have hcard : Nat.card E = Nat.card (E'.map π) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv).symm.trans
      (card_eq_of_injective_comp_subtype π hinj)
  rw [hcard]
  refine h _ _ (CFSG.SectionRank.isElemAbelian_map hE' π) (hT'.map π) ?_ ?_
  ·
    intro hbot
    apply hTN
    intro t ht
    have htL : t ∈ L := hTL ht
    have hmem : (⟨t, htL⟩ : ↥L) ∈ T' := ht
    have : π ⟨t, htL⟩ ∈ T'.map π := Subgroup.mem_map_of_mem π hmem
    rw [hbot, Subgroup.mem_bot] at this
    have hk : (⟨t, htL⟩ : ↥L) ∈ π.ker := this
    rw [hker] at hk
    exact (mem_primeCoreOf_iff ⟨t, htL⟩).2 hk
  · exact map_le_normalizer_map π hET

end Core

end CFSG.LocalAnalysis.GLTheoremA.CatB
