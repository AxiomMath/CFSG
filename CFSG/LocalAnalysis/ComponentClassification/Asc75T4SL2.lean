module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Tools

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped MatrixGroups Pointwise commutatorElement

theorem isSimpleGroup_sl2 {n : ℕ} (hn : 2 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  have : IsSimpleGroup PSL(2, GaloisField 2 n) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.isSimpleGroup

theorem card_sl2 {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [← Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).toEquiv]
  exact CFSG.Walter.psl2_even_card hn

theorem factorization_two_pow_mul_odd (n : ℕ) {m : ℕ} (hm : Odd m) :
    (2 ^ n * m).factorization 2 = n := by
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply, Nat.Prime.factorization_pow
    Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
      (even_iff_two_dvd.mpr h)), add_zero]

theorem odd_four_pow_sub_one {n : ℕ} (hn : n ≠ 0) : Odd ((2 ^ n) ^ 2 - 1) := by
  have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  rw [Nat.odd_sub this]
  simp [Nat.even_pow, hn]

theorem map_eq_prod_of_perfect {H E S : Type*} [Group H] [CommGroup E] [Group S]
    [IsSimpleGroup S] (f : H →* E × S) (hf : Function.Surjective f) {N : Subgroup H}
    (hN : N.Normal) (hperf : ⁅N.map f, N.map f⁆ = N.map f) (hne : N.map f ≠ ⊥) :
    N.map f = (⊥ : Subgroup E).prod ⊤ := by
  set P := N.map f
  have hPn : P.Normal := hN.map f hf
  have hfst : ∀ x ∈ P, x.1 = 1 := by
    have h1 : P.map (MonoidHom.fst E S) = ⊥ := by
      rw [← hperf, Subgroup.map_commutator, commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [mem_centralizer_iff]
      intro y _
      exact mul_comm y x
    intro x hx
    have : x.1 ∈ P.map (MonoidHom.fst E S) := ⟨x, hx, rfl⟩
    rwa [h1, mem_bot] at this
  have hsnd : P.map (MonoidHom.snd E S) = ⊤ := by
    have hsn : (P.map (MonoidHom.snd E S)).Normal :=
      hPn.map _ fun s => ⟨(1, s), rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map (MonoidHom.snd E S)) with h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have h2 : x.2 ∈ P.map (MonoidHom.snd E S) := ⟨x, hx, rfl⟩
      rw [h, mem_bot] at h2
      exact Prod.ext (hfst x hx) h2
    · exact h
  apply le_antisymm
  · intro x hx
    exact mem_prod.mpr ⟨hfst x hx, mem_top _⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hsnd ▸ (mem_top x.2 : x.2 ∈ (⊤ : Subgroup S))
    have hx1 : x.1 = 1 := (mem_prod.mp hx).1
    have : y = x := Prod.ext (by rw [hfst y hy, hx1]) hyx
    rw [← this]
    exact hy

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem pow_two_pow_eq_one_of_mem_closure {A : Type*} [CommGroup A] {s : Set A}
    (hs : ∀ x ∈ s, ∃ k : ℕ, x ^ (2 ^ k) = 1) {x : A} (hx : x ∈ closure s) :
    ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  induction hx using closure_induction with
  | mem x hx => exact hs x hx
  | one => exact ⟨0, one_pow _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [mul_pow, pow_add, pow_mul, ha, one_pow, one_mul, mul_comm, pow_mul, hb, one_pow]
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by rw [inv_pow, ha, inv_one]⟩

theorem commutator_oUpperTwoPrime_eq {C : Subgroup G} (hs : IsSemisimpleQ C) :
    ⁅oUpperTwoPrime C, oUpperTwoPrime C⁆ = oUpperTwoPrime C := by
  set L := oUpperTwoPrime C with hL
  have hLC : L ≤ C := oUpperTwoPrime_le C
  set D' := ⁅L, L⁆
  have hDL : D' ≤ L := commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hCD : C ≤ D' ⊔ oddCoreIn C := by
    set π := QuotientGroup.mk' (CFSG.Assembly.oddCore C)
    have hperf : ⁅(⊤ : Subgroup (C ⧸ CFSG.Assembly.oddCore C)),
        (⊤ : Subgroup (C ⧸ CFSG.Assembly.oddCore C))⁆ = ⊤ := by
      have h := CFSG.LocalCores.layer_perfect (G := C ⧸ CFSG.Assembly.oddCore C)
      rwa [show CFSG.layer (C ⧸ CFSG.Assembly.oddCore C) = ⊤ from hs] at h
    have hLtop : (L.subgroupOf C).map π = ⊤ := by
      have h1 := le_oUpperTwoPrime_sup_oddCoreIn hs
      rw [eq_top_iff]
      intro z _
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ z
      have hc : (c : G) ∈ (L : Set G) * (oddCoreIn C : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right L _ (hLC.trans
          (normalIn_le_normalizer (oddCoreIn_normalIn C)))]
        exact h1 c.2
      obtain ⟨l, hl, o, ho, hlo⟩ := Set.mem_mul.mp hc
      obtain ⟨hoC, ho'⟩ := mem_oddCoreIn_iff.mp ho
      refine ⟨⟨l, hLC hl⟩, hl, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : (⟨l, hLC hl⟩ : C)⁻¹ * c = ⟨o, hoC⟩ := Subtype.ext (by
        simp only [coe_mul, coe_inv]
        rw [← hlo]
        group)
      rw [this]
      exact ho'
    have hDsub : D'.subgroupOf C = ⁅L.subgroupOf C, L.subgroupOf C⁆ := by
      apply map_injective C.subtype_injective
      rw [Subgroup.map_commutator, map_subtype_subgroupOf_of_le hLC,
        map_subtype_subgroupOf_of_le (hDL.trans hLC)]
    have hDtop : (D'.subgroupOf C).map π = ⊤ := by
      rw [hDsub, Subgroup.map_commutator, hLtop, hperf]
    intro c hc
    have hcm : π ⟨c, hc⟩ ∈ (D'.subgroupOf C).map π := hDtop ▸ mem_top _
    rw [← mem_comap, comap_map_eq, QuotientGroup.ker_mk'] at hcm
    have h2 := mem_map_of_mem C.subtype hcm
    rw [Subgroup.map_sup, map_subtype_subgroupOf_of_le (hDL.trans hLC)] at h2
    exact h2
  have hDN : L ≤ normalizer (D' : Set G) := by
    intro l hl
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hl)]
  have hDn : (D'.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hDL).mpr hDN
  set q := QuotientGroup.mk' (D'.subgroupOf L)
  have h2 : ∀ z : L ⧸ D'.subgroupOf L, ∃ k : ℕ, z ^ (2 ^ k) = 1 := by
    let _ : CommGroup (L ⧸ D'.subgroupOf L) :=
      { (inferInstance : Group (L ⧸ D'.subgroupOf L)) with
        mul_comm := fun a b => by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
          rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq, mem_subgroupOf]
          have : (((x * y)⁻¹ * (y * x) : L) : G) = ⁅((y : G))⁻¹, ((x : G))⁻¹⁆ := by
            simp only [commutatorElement_def, coe_mul, coe_inv, inv_inv]
            group
          rw [this]
          exact commutator_mem_commutator (inv_mem y.2) (inv_mem x.2) }
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hx : x ∈ (closure {y : L | ∃ k : ℕ, y ^ (2 ^ k) = 1} : Subgroup L) := by
      have h3 : L ≤ (closure {y : L | ∃ k : ℕ, y ^ (2 ^ k) = 1}).map L.subtype := by
        rw [MonoidHom.map_closure, hL, oUpperTwoPrime, closure_le]
        intro y hy
        obtain ⟨k, hk⟩ := hy.2
        exact subset_closure ⟨⟨y, subset_closure hy⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
      obtain ⟨y, hy, hyx⟩ := h3 x.2
      rwa [show y = x from Subtype.ext hyx] at hy
    have hq : q x ∈ (closure {y : L | ∃ k : ℕ, y ^ (2 ^ k) = 1}).map q := mem_map_of_mem q hx
    rw [MonoidHom.map_closure] at hq
    refine pow_two_pow_eq_one_of_mem_closure ?_ hq
    rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hodd : Odd (Nat.card (L ⧸ D'.subgroupOf L)) := by
    have hsurj : Function.Surjective (q.comp ((oddCoreIn C).subgroupOf L).subtype) := by
      intro z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ z
      have hl : (l : G) ∈ (D' : Set G) * (oddCoreIn C : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right D' _ ((hDL.trans hLC).trans
          (normalIn_le_normalizer (oddCoreIn_normalIn C)))]
        exact hCD (hLC l.2)
      obtain ⟨d, hd, o, ho, hdo⟩ := Set.mem_mul.mp hl
      have hoL : o ∈ L := by
        have : o = d⁻¹ * l := by rw [← hdo]; group
        rw [this]
        exact mul_mem (inv_mem (hDL hd)) l.2
      refine ⟨⟨⟨o, hoL⟩, ho⟩, ?_⟩
      simp only [MonoidHom.comp_apply, coe_subtype]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      have : (((⟨o, hoL⟩ : L)⁻¹ * l : L) : G) = o⁻¹ * d * o⁻¹⁻¹ := by
        simp only [coe_mul, coe_inv, inv_inv]
        rw [← hdo]
        group
      rw [this]
      exact (mem_normalizer_iff.mp (hDN (inv_mem hoL)) d).mp hd
    have h1 := Subgroup.card_dvd_of_surjective hsurj
    have h3 : Nat.card ((oddCoreIn C).subgroupOf L) ∣ Nat.card (oddCoreIn C) := by
      rw [← card_map_of_injective L.subtype_injective, subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
    exact (odd_card_oddCoreIn C).of_dvd_nat (h1.trans h3)
  refine le_antisymm hDL fun l hl => ?_
  obtain ⟨k, hk⟩ := h2 (q ⟨l, hl⟩)
  have h4 : orderOf (q ⟨l, hl⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
      (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_natCard _)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at h4
  exact h4

section Case3

variable {H : Type} [Group H] [Finite H]

theorem factorization_two_eq_of_dvd {m d : ℕ} (hm : m ≠ 0) (hd : d ≠ 0)
    (h1 : 2 ^ d.factorization 2 ∣ m) (h2 : m ∣ d) : m.factorization 2 = d.factorization 2 := by
  refine le_antisymm ?_ ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm).mp h1)
  exact (Nat.factorization_le_iff_dvd hm hd).mpr h2 2

omit [Finite H] in
theorem oUpperTwoPrime_mono {X Z : Subgroup H} (h : X ≤ Z) :
    oUpperTwoPrime X ≤ oUpperTwoPrime Z :=
  closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem odd_card_oddCoreIn_subgroupOf (Y V : Subgroup H) :
    Odd (Nat.card ((oddCoreIn Y).subgroupOf V)) := by
  have h1 : Nat.card ((oddCoreIn Y).subgroupOf V) ∣ Nat.card (oddCoreIn Y) := by
    rw [← card_map_of_injective V.subtype_injective, subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  exact (odd_card_oddCoreIn Y).of_dvd_nat h1

theorem factorization_eq_of_surjective {Y T : Subgroup H} (hTY : T ⊓ Y = ⊥)
    (hTN : T ≤ normalizer (Y : Set H))
    (hTcard : Nat.card T = 2 ^ (Nat.card Y).factorization 2) {n : ℕ} (hn : n ≠ 0)
    (φ : oUpperTwoPrime (Y ⊔ T) →*
      Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = (oddCoreIn Y).subgroupOf (oUpperTwoPrime (Y ⊔ T))) :
    (Nat.card Y).factorization 2 = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerodd : Odd (Nat.card φ.ker) := hker ▸ odd_card_oddCoreIn_subgroupOf Y _
  have hYT : Nat.card (Y ⊔ T : Subgroup H) = Nat.card Y * Nat.card T :=
    AschbacherTheorem3.card_sup_of_le_normalizer hTN (by rw [inf_comm]; exact hTY)
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (Y ⊔ T)
  have hPV : P ≤ oUpperTwoPrime (Y ⊔ T) := fun x hx => by
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨x, hx⟩
    exact subset_closure ⟨hP.le hx, k, by simpa using congrArg Subtype.val hk⟩
  have hVcard : Nat.card (oUpperTwoPrime (Y ⊔ T)) =
      Nat.card (Multiplicative (Fin n → ZMod 2) ×
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  have hEcard : Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_pi]
    simp
  have hVfac : (Nat.card (oUpperTwoPrime (Y ⊔ T))).factorization 2 = 2 * n := by
    rw [hVcard, Nat.card_prod, hEcard, card_sl2 hn,
      show 2 ^ n * (2 ^ n * ((2 ^ n) ^ 2 - 1)) * Nat.card φ.ker =
        2 ^ (2 * n) * (((2 ^ n) ^ 2 - 1) * Nat.card φ.ker) by ring]
    exact factorization_two_pow_mul_odd _ ((odd_four_pow_sub_one hn).mul hkerodd)
  have hVeq : (Nat.card (oUpperTwoPrime (Y ⊔ T))).factorization 2 =
      (Nat.card (Y ⊔ T : Subgroup H)).factorization 2 :=
    factorization_two_eq_of_dvd Nat.card_pos.ne' Nat.card_pos.ne'
      (hP.card_eq ▸ card_dvd_of_le hPV) (card_dvd_of_le (oUpperTwoPrime_le _))
  rw [hVfac, hYT, hTcard, Nat.factorization_mul Nat.card_pos.ne' (by positivity),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hVeq
  omega

theorem range_comp_inclusion_eq_prod {Y C T : Subgroup H} (hCY : NormalIn C Y)
    (hTC : T ≤ normalizer (C : Set H)) (hs : IsSemisimpleQ C) (hCe : Even (Nat.card C))
    {n : ℕ} (hn : 2 ≤ n)
    (φ : oUpperTwoPrime (Y ⊔ T) →*
      Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = (oddCoreIn Y).subgroupOf (oUpperTwoPrime (Y ⊔ T)))
    (hLV : oUpperTwoPrime C ≤ oUpperTwoPrime (Y ⊔ T)) :
    (φ.comp (inclusion hLV)).range = (⊥ : Subgroup (Multiplicative (Fin n → ZMod 2))).prod ⊤ ∧
      (φ.comp (inclusion hLV)).ker = (oddCoreIn C).subgroupOf (oUpperTwoPrime C) := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    isSimpleGroup_sl2 hn
  set L := oUpperTwoPrime C with hL
  have hLC : L ≤ C := oUpperTwoPrime_le C
  have hYTN : Y ⊔ T ≤ normalizer (C : Set H) := sup_le (normalIn_le_normalizer hCY) hTC
  have hVN : oUpperTwoPrime (Y ⊔ T) ≤ normalizer (L : Set H) := (oUpperTwoPrime_le _).trans
    (hYTN.trans (normalizer_le_normalizer_oUpperTwoPrime C))
  have hNn : (L.subgroupOf (oUpperTwoPrime (Y ⊔ T))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLV).mpr hVN
  set β := φ.comp (inclusion hLV)
  have hβker : β.ker = (oddCoreIn C).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, mem_subgroupOf,
      mem_subgroupOf]
    show (x : H) ∈ oddCoreIn Y ↔ (x : H) ∈ oddCoreIn C
    rw [← inf_oddCoreIn_eq hCY]
    exact ⟨fun h => ⟨hLC x.2, h⟩, fun h => h.2⟩
  have hrange : β.range = (L.subgroupOf (oUpperTwoPrime (Y ⊔ T))).map φ := by
    rw [MonoidHom.range_comp, inclusion_range]
  have hLp : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact commutator_oUpperTwoPrime_eq hs
  have hperf : ⁅β.range, β.range⁆ = β.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hLp]
  have hne : β.range ≠ ⊥ := by
    intro hbot
    have h1 : β.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [MonoidHom.mem_ker]
      have : β x ∈ β.range := ⟨x, rfl⟩
      rwa [hbot, mem_bot] at this
    have hLO : L ≤ oddCoreIn C := by
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ (oddCoreIn C).subgroupOf L := hβker ▸ (h1 ▸ mem_top _)
      exact this
    have hCO : C ≤ oddCoreIn C :=
      (le_oUpperTwoPrime_sup_oddCoreIn hs).trans (sup_le hLO le_rfl)
    exact Nat.not_even_iff_odd.mpr ((odd_card_oddCoreIn C).of_dvd_nat (card_dvd_of_le hCO)) hCe
  exact ⟨hrange.trans (map_eq_prod_of_perfect φ hφ hNn (hrange ▸ hperf) (hrange ▸ hne)), hβker⟩

omit [Finite H] in
theorem snd_comp_of_range_eq_prod {L E S : Type*} [Group L] [Group E] [Group S]
    (β : L →* E × S) (hβ : β.range = (⊥ : Subgroup E).prod ⊤) :
    Function.Surjective ((MonoidHom.snd E S).comp β) ∧
      ((MonoidHom.snd E S).comp β).ker = β.ker := by
  have h1 : ∀ x, (β x).1 = 1 := fun x => by
    have hx : β x ∈ β.range := ⟨x, rfl⟩
    rw [hβ] at hx
    exact (mem_prod.mp hx).1
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨x, hx⟩ : ((1 : E), s) ∈ β.range := hβ ▸ mem_prod.mpr ⟨one_mem _, mem_top s⟩
    exact ⟨x, by rw [MonoidHom.comp_apply, hx]; rfl⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h2 => Prod.ext (h1 x) h2, fun h2 => by rw [h2]; rfl⟩

omit [Finite H] in
theorem snd_eq_one_of_commute {E S : Type*} [Group E] [Group S] (hS : center S = ⊥) {x : E × S}
    (hx : ∀ s : S, x * (1, s) = (1, s) * x) : x.2 = 1 := by
  have : x.2 ∈ center S := mem_center_iff.mpr fun s => by
    have := congrArg Prod.snd (hx s)
    simpa using this.symm
  rwa [hS, mem_bot] at this

end Case3

end CFSG.ComponentClassification.Asc75T4
