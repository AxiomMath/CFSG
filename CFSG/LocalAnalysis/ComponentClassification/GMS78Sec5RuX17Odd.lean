module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCentG

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {y d : G}

theorem isPGroup_centralizer_inf_centralizer
    (hS : SzR G L T R 1 y d)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    {e : G} (he : e ∈ T ⊓ centralizer (L : Set G)) (he1 : e ≠ 1) {a : G} (haL : a ∈ L)
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    IsPGroup 2 (centralizer ({e} : Set G) ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨x, hxe, hxa⟩
  rw [hCe e he he1] at hxe
  obtain ⟨t, ht, l, hl, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer
    (inf_le_right.trans hS.sec3.centralizer_le_normalizer) hxe
  have htl : t * l = l * t := (mem_centralizer_iff.mp ht.2 l hl).symm
  have hta : t * a = a * t := (mem_centralizer_iff.mp ht.2 a haL).symm
  have hla : l * a = a * l := by
    have h1 : (t * l) * a = a * (t * l) := mem_centralizer_singleton_iff.mp hxa
    calc l * a = t⁻¹ * ((t * l) * a) := by group
      _ = t⁻¹ * (a * (t * l)) := by rw [h1]
      _ = t⁻¹ * (a * t) * l := by group
      _ = t⁻¹ * (t * a) * l := by rw [hta]
      _ = a * l := by group
  obtain ⟨k, hk⟩ := hCL a haL ha1 ha2 ⟨l, hl, mem_centralizer_singleton_iff.mpr hla⟩
  obtain ⟨j, hj⟩ := (hS.isR.isPGroup.to_le hS.T_le) ⟨t, ht.1⟩
  have hk' : l ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hj' : t ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  refine ⟨j + k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [(Commute.mul_pow htl), pow_add, pow_mul, hj', one_pow, one_mul, mul_comm (2 ^ j),
    pow_mul, hk', one_pow]

omit [Finite G] in
theorem eq_one_of_odd_of_pow_two {x : G} (hx : Odd (orderOf x)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rw [hj, pow_succ] at hx
    exact absurd hx (Nat.not_odd_iff_even.mpr (even_two.mul_left _))

theorem eq_bot_of_odd_of_le_centralizer
    (hS : SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    {F₁ D : Subgroup G} (hF₁A : F₁ ≤ gmsA L T) (hF₁1 : F₁ ≠ ⊥)
    (hDF : D ≤ centralizer (F₁ : Set G)) (hDodd : ¬ 2 ∣ Nat.card D)
    (hDn : T ⊓ centralizer (L : Set G) ≤ normalizer (D : Set G)) : D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨a, haF⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF₁1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haA := hF₁A haF
  have haL : a ∈ L := haA.1.2
  obtain ⟨-, hA2, -⟩ := hS.facts.sylow hS.sec3
  have ha2 : a ^ 2 = 1 := hA2 a haA
  set N := normalizer (D : Set G) with hN
  set D' := D.subgroupOf N with hD'
  have hfix : ∀ e (he : e ∈ T ⊓ centralizer (L : Set G)), e ≠ 1 →
      ∀ x ∈ D', (⟨e, hDn he⟩ : N) * x = x * ⟨e, hDn he⟩ → x = 1 := by
    intro e he he1 x hx hxe
    apply Subtype.ext
    have hxD : ((x : N) : G) ∈ D := hx
    have hxe' : ((x : N) : G) ∈ centralizer ({e} : Set G) :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxe).symm
    have hxa : ((x : N) : G) ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hDF hxD) a haF)).symm
    obtain ⟨k, hk⟩ := hS.isPGroup_centralizer_inf_centralizer hCe hCL he he1 haL ha1' ha2
      ⟨_, hxe', hxa⟩
    have hk' : ((x : N) : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf ((x : N) : G)) := by
      have h1 : orderOf ((x : N) : G) ∣ Nat.card D :=
        (Subgroup.orderOf_coe (⟨_, hxD⟩ : D)).symm ▸ orderOf_dvd_natCard _
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      exact hDodd ((even_iff_two_dvd.mp hev).trans h1)
    exact eq_one_of_odd_of_pow_two hodd hk'
  have hT₀el := hS.sec3.isElemAbelian_T₀ hS.foundation
  obtain ⟨u, hu, w, hw, hu1, hw1, huw⟩ := exists_two_ne_one_of_four_le_card h4.ge
  have huw' : u * w ∈ T ⊓ centralizer (L : Set G) := mul_mem hu hw
  have huw1 : u * w ≠ 1 := by
    intro h
    apply huw
    have hw2 : w * w = 1 := by rw [← sq]; exact hT₀el.2 w hw
    calc u = u * w * w := by rw [mul_assoc, hw2, mul_one]
      _ = w := by rw [h, one_mul]
  have hinv : ∀ e (he : e ∈ T ⊓ centralizer (L : Set G)),
      (⟨e, hDn he⟩ : N) * ⟨e, hDn he⟩ = 1 := fun e he =>
    Subtype.ext (by rw [coe_mul, ← sq]; exact hT₀el.2 e he)
  have hD'bot : D' = ⊥ := by
    have h := eq_bot_of_fixedPointFree_of_four (D := D') (hinv u hu) (hinv w hw)
      (hfix u hu hu1) (hfix w hw hw1) ?_
    · exact h
    · intro x hx hxe
      exact hfix (u * w) huw' huw1 x hx (by simpa [mul_assoc] using hxe)
  rw [eq_bot_iff]
  intro x hx
  have hxN : x ∈ N := le_normalizer hx
  have : (⟨x, hxN⟩ : N) ∈ D' := hx
  rw [hD'bot, mem_bot] at this
  rw [mem_bot]
  exact congrArg Subtype.val this

theorem mem_normalizer_map_of_characteristic {K : Subgroup G} {D : Subgroup K}
    [D.Characteristic] {t : G} (ht : t ∈ normalizer (K : Set G)) :
    t ∈ normalizer ((D.map K.subtype : Subgroup G) : Set G) := by
  have hconj : ∀ k : K, t * (k : G) * t⁻¹ ∈ K := fun k => (mem_normalizer_iff.mp ht k).mp k.2
  have hconj' : ∀ k : K, t⁻¹ * (k : G) * t ∈ K := fun k => by
    have := (mem_normalizer_iff.mp (inv_mem ht) k).mp k.2
    simpa using this
  set φ : K ≃* K :=
    { toFun := fun k => ⟨t * k * t⁻¹, hconj k⟩
      invFun := fun k => ⟨t⁻¹ * k * t, hconj' k⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) } with hφ
  have hfix := characteristic_iff_comap_eq.mp (inferInstance : D.Characteristic) φ.symm
  refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨φ k, ?_, rfl⟩
  have : φ k ∈ D.comap φ.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]
    simpa using hk
  rwa [hfix] at this

theorem eq_of_odd_index
    (hS : SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    {F₁ K : Subgroup G} (hF₁A : F₁ ≤ gmsA L T) (hF₁1 : F₁ ≠ ⊥) (hF₁K : F₁ ≤ K)
    (hKC : K ≤ centralizer (F₁ : Set G))
    (hKn : T ⊓ centralizer (L : Set G) ≤ normalizer (K : Set G)) (hodd : ¬ 2 ∣ F₁.relIndex K) :
    K = F₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := F₁.subgroupOf K with hP
  have hP2 : IsPGroup 2 P :=
    ((hS.isR.isPGroup.to_le hS.T_le).to_le (hF₁A.trans gmsA_le_T)).comap_subtype
  have hPidx : ¬ 2 ∣ P.index := hodd
  set PS : Sylow 2 K := hP2.toSylow hPidx with hPS
  have hPSc : (PS : Subgroup K) = P := IsPGroup.toSylow_coe hP2 hPidx
  have hNC : normalizer (PS : Set K) ≤ centralizer (PS : Set K) := by
    intro k _
    rw [mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ P := by rw [← hPSc]; exact hp
    exact Subtype.ext (mem_centralizer_iff.mp (hKC k.2) p hp')
  obtain ⟨D, -, hD2, -, -, hDchar, -, hDP, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement PS hNC
  have hD'odd : ¬ 2 ∣ Nat.card (D.map K.subtype) := by
    rw [card_map_of_injective K.subtype_injective]
    exact hD2
  have hD'bot : D.map K.subtype = ⊥ :=
    hS.eq_bot_of_odd_of_le_centralizer h4 hCe hCL hF₁A hF₁1
      ((map_subtype_le D).trans hKC) hD'odd
      (fun t ht => mem_normalizer_map_of_characteristic (hKn ht))
  have hDbot : D = ⊥ := (map_eq_bot_iff_of_injective D K.subtype_injective).mp hD'bot
  have hPtop : (PS : Subgroup K) = ⊤ := by rw [← hDP, hDbot, bot_sup_eq]
  refine le_antisymm (fun x hx => ?_) hF₁K
  have : (⟨x, hx⟩ : K) ∈ (PS : Subgroup K) := by rw [hPtop]; exact mem_top _
  rw [hPSc] at this
  exact this

theorem oddCore_centralizer_quotient_eq_bot
    (hS : SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    {F₁ : Subgroup G} (hF₁A : F₁ ≤ gmsA L T) (hF₁1 : F₁ ≠ ⊥)
    [(F₁.subgroupOf (centralizer (F₁ : Set G))).Normal] :
    CFSG.oddCore (centralizer (F₁ : Set G) ⧸ F₁.subgroupOf (centralizer (F₁ : Set G))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (F₁ : Set G) with hC
  have hF₁C : F₁ ≤ C := fun x hx => mem_centralizer_iff.mpr fun b hb => by
    have hxA := hF₁A hx
    have hbA := hF₁A hb
    exact mem_centralizer_iff.mp hxA.2 b hbA.1
  set π := QuotientGroup.mk' (F₁.subgroupOf C) with hπ
  set O := CFSG.oddCore (C ⧸ F₁.subgroupOf C) with hO
  have hOodd : ¬ 2 ∣ Nat.card O := by
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := O) 2 h2
    have := CFSG.Adapters.odd_orderOf_of_mem_oddCore x.2
    rw [Subgroup.orderOf_coe, hx] at this
    exact absurd this (by decide)
  have hπF : ∀ x (hx : x ∈ F₁), π ⟨x, hF₁C hx⟩ = 1 := fun x hx =>
    (QuotientGroup.eq_one_iff _).mpr (show (⟨x, hF₁C hx⟩ : C) ∈ F₁.subgroupOf C from hx)
  set K := (O.comap π).map C.subtype with hK
  have hF₁K : F₁ ≤ K := fun x hx =>
    ⟨⟨x, hF₁C hx⟩, show π ⟨x, hF₁C hx⟩ ∈ O by rw [hπF x hx]; exact one_mem _, rfl⟩
  have hKC : K ≤ C := map_subtype_le _
  have hKn : T ⊓ centralizer (L : Set G) ≤ normalizer (K : Set G) := by
    intro t ht
    have htC : t ∈ C := mem_centralizer_iff.mpr fun b hb =>
      mem_centralizer_iff.mp ht.2 b (hF₁A hb).1.2
    refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨⟨t, htC⟩ * c * ⟨t, htC⟩⁻¹, ?_, by simp⟩
    show π (⟨t, htC⟩ * c * ⟨t, htC⟩⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact (CFSG.oddCore_normal _).conj_mem _ hc _
  have hidx : F₁.relIndex K = Nat.card O := by
    set F₁' := F₁.subgroupOf C with hF₁'
    have e1 := (O.comap π).index_mul_card
    have e2 := O.index_mul_card
    have e3 := F₁'.card_eq_card_quotient_mul_card_subgroup
    have e4 : (O.comap π).index = O.index :=
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
    have e5 := relIndex_mul_card F₁ K
    rw [inf_eq_left.mpr hF₁K] at e5
    have e6 : Nat.card K = Nat.card (O.comap π) := card_map_of_injective C.subtype_injective
    have e7 : Nat.card F₁' = Nat.card F₁ := Nat.card_congr (subgroupOfEquivOfLe hF₁C).toEquiv
    have hpos : 0 < O.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hF₁pos : 0 < Nat.card F₁ := Nat.card_pos
    rw [e4] at e1
    have e8 : Nat.card (O.comap π) = Nat.card O * Nat.card F₁ := by
      have : O.index * Nat.card (O.comap π) = O.index * (Nat.card O * Nat.card F₁) := by
        rw [e1, e3, ← e2, e7]
        ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    rw [e6, e8] at e5
    exact Nat.eq_of_mul_eq_mul_right hF₁pos e5
  have hKF := hS.eq_of_odd_index h4 hCe hCL hF₁A hF₁1 hF₁K hKC hKn (by rw [hidx]; exact hOodd)
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (F₁.subgroupOf C) q
  have hcK : (c : G) ∈ K := ⟨c, hq, rfl⟩
  rw [hKF] at hcK
  rw [mem_bot]
  exact (QuotientGroup.eq_one_iff _).mpr hcK

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
