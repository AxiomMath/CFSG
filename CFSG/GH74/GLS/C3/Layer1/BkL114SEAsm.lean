module

public import CFSG.GH74.GLS.C3.Layer1.BkSEAbs
public import CFSG.GH74.GLS.C3.Layer1.BkL114SE
public import CFSG.GH74.GLS.C3.Layer1.BkW5Coord

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools

section GLevel
open CFSG.GH74.GLS
section ZV

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem z_commutes_T (h : IsAConfigW n x K T Q S a) {t : G} (ht : t ∈ T) :
    (a * x * a⁻¹) * t = t * (a * x * a⁻¹) := by
  have hinv : a⁻¹ * t * a ∈ T := by
    have := (mem_normalizer_iff.1 (inv_mem h.a_mem.2.1) t).1 ht
    simpa using this
  have hx : (a⁻¹ * t * a) * x = x * (a⁻¹ * t * a) :=
    mem_centralizer_singleton_iff.1 (h.T_le_C hinv)
  calc (a * x * a⁻¹) * t = a * (x * (a⁻¹ * t * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * t * a) * x) * a⁻¹ := by rw [hx]
    _ = t * (a * x * a⁻¹) := by group

theorem z_ne_x (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a) : a * x * a⁻¹ ≠ x := by
  intro hzx
  have haC : a ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [hzx]
  have hSle : S ≤ centralizer ({x} : Set G) := by
    rw [hS]
    exact sup_le h.T_le_C (zpowers_le.2 haC)
  have := h.sylowT.eq_of_le h.T_lt_S.le hSle h.sylowS.isPGroup
  exact h.T_lt_S.ne this.symm

theorem v_sq (h : IsAConfigW n x K T Q S a) (hz : a * x * a⁻¹ ∈ T ⊓ K) :
    (x * (a * x * a⁻¹)) * (x * (a * x * a⁻¹)) = 1 := by
  have hxx : x * x = 1 := by rw [← sq]; exact h.x_sq
  have hzx : (a * x * a⁻¹) * x = x * (a * x * a⁻¹) :=
    mem_centralizer_singleton_iff.1 (h.K_le_C hz.2)
  have hzz : (a * x * a⁻¹) * (a * x * a⁻¹) = 1 := by
    calc (a * x * a⁻¹) * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  calc (x * (a * x * a⁻¹)) * (x * (a * x * a⁻¹))
      = x * ((a * x * a⁻¹) * x) * (a * x * a⁻¹) := by group
    _ = x * (x * (a * x * a⁻¹)) * (a * x * a⁻¹) := by rw [hzx]
    _ = (x * x) * ((a * x * a⁻¹) * (a * x * a⁻¹)) := by group
    _ = 1 := by rw [hxx, hzz]; group

theorem v_orderOf (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) : orderOf (x * (a * x * a⁻¹)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxx : x * x = 1 := by rw [← sq]; exact h.x_sq
  refine orderOf_eq_prime (by rw [sq]; exact v_sq h hz) ?_
  intro hv
  have hzx := z_ne_x h hS
  apply hzx
  have h1 : a * x * a⁻¹ = x⁻¹ := by
    have := congrArg (fun y => x⁻¹ * y) hv
    simpa using this
  rw [h1]
  exact inv_eq_of_mul_eq_one_right hxx

theorem v_mem_T (h : IsAConfigW n x K T Q S a) (hz : a * x * a⁻¹ ∈ T ⊓ K) :
    x * (a * x * a⁻¹) ∈ T :=
  T.mul_mem h.x_mem_T hz.1

theorem v_central_S (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) : ∀ s ∈ S, s * (x * (a * x * a⁻¹)) = (x * (a * x * a⁻¹)) * s := by
  have hxx : x * x = 1 := by rw [← sq]; exact h.x_sq
  have hzx : (a * x * a⁻¹) * x = x * (a * x * a⁻¹) :=
    mem_centralizer_singleton_iff.1 (h.K_le_C hz.2)
  have hT : ∀ t ∈ T, t * (x * (a * x * a⁻¹)) = (x * (a * x * a⁻¹)) * t := by
    intro t ht
    have h1 : t * x = x * t := mem_centralizer_singleton_iff.1 (h.T_le_C ht)
    have h2 := z_commutes_T h ht
    calc t * (x * (a * x * a⁻¹)) = (t * x) * (a * x * a⁻¹) := by group
      _ = (x * t) * (a * x * a⁻¹) := by rw [h1]
      _ = x * (t * (a * x * a⁻¹)) := by group
      _ = x * ((a * x * a⁻¹) * t) := by rw [h2]
      _ = (x * (a * x * a⁻¹)) * t := by group
  have ha2 : (a * a) * x = x * (a * a) := by
    have := h.T_le_C (by rw [← sq]; exact h.a_mem.2.2.2 : a * a ∈ T)
    exact mem_centralizer_singleton_iff.1 this
  have hza : a * (a * x * a⁻¹) * a⁻¹ = x := by
    calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [mul_inv_eq_iff_eq_mul]; exact ha2
  have ha : a * (x * (a * x * a⁻¹)) = (x * (a * x * a⁻¹)) * a := by
    have : a * (x * (a * x * a⁻¹)) * a⁻¹ = x * (a * x * a⁻¹) := by
      calc a * (x * (a * x * a⁻¹)) * a⁻¹
          = (a * x * a⁻¹) * (a * (a * x * a⁻¹) * a⁻¹) := by group
        _ = (a * x * a⁻¹) * x := by rw [hza]
        _ = x * (a * x * a⁻¹) := hzx
    calc a * (x * (a * x * a⁻¹)) = (a * (x * (a * x * a⁻¹)) * a⁻¹) * a := by group
      _ = (x * (a * x * a⁻¹)) * a := by rw [this]
  have hSle : S ≤ centralizer ({x * (a * x * a⁻¹)} : Set G) := by
    rw [hS]
    refine sup_le (fun t ht => ?_) (zpowers_le.2 ?_)
    · exact mem_centralizer_singleton_iff.2 (hT t ht)
    · exact mem_centralizer_singleton_iff.2 ha
  intro s hs
  exact mem_centralizer_singleton_iff.1 (hSle hs)

end ZV

end GLevel

section GLevel2

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

omit [Finite G] in
theorem card_centralizer_conj' (c g : G) :
    Nat.card (centralizer ({c⁻¹ * g * c} : Set G)) = Nat.card (centralizer ({g} : Set G)) := by
  have h : (centralizer ({g} : Set G)).map (MulAut.conj c⁻¹).toMonoidHom =
      centralizer ({c⁻¹ * g * c} : Set G) := by
    ext y
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨d, hd, rfl⟩
      calc c⁻¹ * d * c * (c⁻¹ * g * c) = c⁻¹ * (d * g) * c := by group
        _ = c⁻¹ * (g * d) * c := by rw [hd]
        _ = _ := by group
    · intro hc
      refine ⟨c * y * c⁻¹, ?_, by group⟩
      calc c * y * c⁻¹ * g = c * (y * (c⁻¹ * g * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * g * c) * y) * c⁻¹ := by rw [hc]
        _ = _ := by group
  rw [← h, card_map_of_injective (MulAut.conj c⁻¹).injective]

omit [Finite G] in
theorem card_centralizer_of_isConj' {x y : G} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have := card_centralizer_conj' c⁻¹ x
  rw [inv_inv] at this
  exact this.symm

theorem not_isConj_x_v (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) : ¬ IsConj x (x * (a * x * a⁻¹)) := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSle : S ≤ centralizer ({x * (a * x * a⁻¹)} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (v_central_S h hS hz s hs)
  have hSv : IsSylowOf 2 S (centralizer ({x * (a * x * a⁻¹)} : Set G)) :=
    h.sylowS.of_le hSle le_top
  have hcard := card_centralizer_of_isConj' hc
  have hS1 := hSv.card_eq
  have hT1 := h.sylowT.card_eq
  rw [← hcard] at hS1
  have hST : Nat.card S ≤ Nat.card T := by rw [hS1, hT1]
  exact h.T_lt_S.ne (Subgroup.eq_of_le_of_card_ge h.T_lt_S.le hST)

theorem card_S_le_two_mul (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a) :
    Nat.card S ≤ 2 * Nat.card T := by
  have haN : a ∈ normalizer (T : Set G) := h.a_mem.2.1
  have hc1 : ∀ t ∈ T, a⁻¹ * t * a ∈ T := by
    intro t ht
    have := (mem_normalizer_iff.1 (inv_mem haN) t).1 ht
    simpa using this
  have ha2 : a * a ∈ T := by rw [← sq]; exact h.a_mem.2.2.2
  let X : Subgroup G :=
    { carrier := {g | g ∈ T ∨ a⁻¹ * g ∈ T}
      mul_mem' := by
        rintro g₁ g₂ (h1 | h1) (h2 | h2)
        · exact Or.inl (T.mul_mem h1 h2)
        · refine Or.inr ?_
          have : a⁻¹ * (g₁ * g₂) = (a⁻¹ * g₁ * a) * (a⁻¹ * g₂) := by group
          rw [this]
          exact T.mul_mem (hc1 g₁ h1) h2
        · refine Or.inr ?_
          have : a⁻¹ * (g₁ * g₂) = (a⁻¹ * g₁) * g₂ := by group
          rw [this]
          exact T.mul_mem h1 h2
        · refine Or.inl ?_
          have : g₁ * g₂ = (a * a) * (a⁻¹ * (a⁻¹ * g₁) * a) * (a⁻¹ * g₂) := by group
          rw [this]
          exact T.mul_mem (T.mul_mem ha2 (hc1 _ h1)) h2
      one_mem' := Or.inl T.one_mem
      inv_mem' := by
        rintro g (h1 | h1)
        · exact Or.inl (T.inv_mem h1)
        · refine Or.inr ?_
          have : a⁻¹ * g⁻¹ = (a⁻¹ * (a⁻¹ * g)⁻¹ * a) * (a⁻¹ * a⁻¹) := by group
          rw [this]
          refine T.mul_mem (hc1 _ (T.inv_mem h1)) ?_
          have := T.inv_mem ha2
          rwa [mul_inv_rev] at this }
  have hSX : S ≤ X := by
    rw [hS]
    refine sup_le (fun t ht => Or.inl ht) (zpowers_le.2 ?_)
    exact Or.inr (by simp)
  have hX : Nat.card X ≤ 2 * Nat.card T := by
    classical
    let f : X → T × Bool := fun g =>
      if hg : g.1 ∈ T then (⟨g.1, hg⟩, false)
      else (⟨a⁻¹ * g.1, (g.2 : g.1 ∈ T ∨ a⁻¹ * g.1 ∈ T).resolve_left hg⟩, true)
    have hf : Function.Injective f := by
      intro g₁ g₂ hfg
      by_cases h1 : g₁.1 ∈ T <;> by_cases h2 : g₂.1 ∈ T <;> simp [f, h1, h2] at hfg <;>
        exact hfg
    calc Nat.card X ≤ Nat.card (T × Bool) := Nat.card_le_card_of_injective f hf
      _ = 2 * Nat.card T := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]
  exact (Subgroup.card_le_of_le hSX).trans hX

theorem alt_two_part_five : (Nat.card (alternatingGroup (Fin (5 + 4)))).factorization 2 = 6 := by
  have h : Nat.card (alternatingGroup (Fin (5 + 4))) = 2 ^ 6 * 2835 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 2835 by norm_num)]

theorem alt_two_part_seven : (Nat.card (alternatingGroup (Fin (7 + 4)))).factorization 2 = 7 := by
  have h : Nat.card (alternatingGroup (Fin (7 + 4))) = 2 ^ 7 * 155925 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 155925 by norm_num)]

theorem card_S_le (hn : n = 5 ∨ n = 7) (h : IsAConfigW n x K T Q S a)
    (hS : S = T ⊔ zpowers a) :
    Nat.card S ≤ 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
  have h2 := card_S_le_two_mul h hS
  rcases hn with rfl | rfl
  · rw [alt_two_part_five]
    have := W5.card_T h
    norm_num
    omega
  · rw [alt_two_part_seven]
    have := card_T_le_sixtyfour_of_aconfigW_seven h
    norm_num
    omega

end GLevel2

section GLevel3

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

omit [Finite G] in
theorem mem_normalizer_pPrimeCoreOf' {X : Subgroup G} {c : G} (hc : c ∈ X) :
    c ∈ normalizer ((pPrimeCoreOf 2 X : Subgroup G) : Set G) := by
  have hN : (pPrimeCore 2 ↥X).Normal := inferInstance
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * a' * ⟨c, hc⟩⁻¹, hN.conj_mem a' ha' ⟨c, hc⟩, rfl⟩
  · intro ha
    obtain ⟨a', ha', hae⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩⁻¹ * a' * ⟨c, hc⟩, ?_, ?_⟩
    · simpa using hN.conj_mem a' ha' ⟨c, hc⟩⁻¹
    · have : (a' : G) = c * a * c⁻¹ := hae
      show (c⁻¹ * (a' : G) * c) = a
      rw [this]
      group

omit [Finite G] in
theorem centralizer_le_NW (x : G) : centralizer ({x} : Set G) ≤ NW x := fun _ hc =>
  mem_normalizer_pPrimeCoreOf' hc

omit [Finite G] in
theorem W_le_NW (x : G) : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤ NW x := by
  intro w hw
  obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hw
  exact centralizer_le_NW x u.2

theorem mem_pPrimeCore_of_mem_W {x w : G}
    (hw : w ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G))) :
    (⟨w, W_le_NW x hw⟩ : ↥(NW x)) ∈ pPrimeCore 2 ↥(NW x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := pPrimeCoreOf 2 (centralizer ({x} : Set G)) with hWdef
  have hnorm : (W.subgroupOf (NW x)).Normal := by
    refine ⟨fun k hk m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have hm : (m : G) ∈ normalizer (W : Set G) := m.2
    exact (mem_normalizer_iff.1 hm (k : G)).1 hk
  have hcard : Nat.Coprime 2 (Nat.card (W.subgroupOf (NW x))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (W_le_NW x)).toEquiv]
    unfold pPrimeCoreOf
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact pPrimeCore_coprime_card
  exact le_pPrimeCore_of_normal_coprime hnorm hcard (Subgroup.mem_subgroupOf.2 hw)

theorem commutator_mem_W (h : IsAConfigW n x K T Q S a) {k q : G} (hk : k ∈ K) (hq : q ∈ Q) :
    ⁅k, q⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq' : q ∈ centralizerSection K (pPrimeCoreOf 2 K) := (h.Q_le_CxK hq).2
  have h1 : ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := hq'.2.2 k hk
  have hKnorm : (K.subgroupOf (centralizer ({x} : Set G))).Normal := by
    refine ⟨fun k hk c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact h.normalInC c c.2 k hk
  exact pPrimeCoreOf_le_of_normal 2 h.K_le_C hKnorm h1

theorem piO_comm_of_commutator_mem {M : Type} [Group M] {a b : M}
    (hab : ⁅a, b⁆ ∈ pPrimeCore 2 M) : piO M a * piO M b = piO M b * piO M a := by
  have h1 : piO M ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hab
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

omit [Finite G] in
theorem mem_of_conj_conj {N : Subgroup G} {y : G} (hy : centralizer ({y} : Set G) ≤ N) {t : G}
    {c d g : G} (hcN : c ∈ N) (hdN : d ∈ N) (hc : c * y * c⁻¹ = t)
    (hd : d * y * d⁻¹ = g⁻¹ * t * g) : g ∈ N := by
  have hm : d⁻¹ * g⁻¹ * c ∈ centralizer ({y} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc d⁻¹ * g⁻¹ * c * y = (d⁻¹ * g⁻¹ * c * y * c⁻¹ * g * d) * (d⁻¹ * g⁻¹ * c) := by group
      _ = (d⁻¹ * (g⁻¹ * (c * y * c⁻¹) * g) * d) * (d⁻¹ * g⁻¹ * c) := by group
      _ = (d⁻¹ * (g⁻¹ * t * g) * d) * (d⁻¹ * g⁻¹ * c) := by rw [hc]
      _ = (d⁻¹ * (d * y * d⁻¹) * d) * (d⁻¹ * g⁻¹ * c) := by rw [hd]
      _ = y * (d⁻¹ * g⁻¹ * c) := by group
  have h2 := hy hm
  have : g = c * (d⁻¹ * g⁻¹ * c)⁻¹ * d⁻¹ := by group
  rw [this]
  exact N.mul_mem (N.mul_mem hcN (N.inv_mem h2)) (N.inv_mem hdN)

theorem exists_conj_mem_of_isSylowOf {M : Type*} [Group M] [Finite M] {P : Subgroup M}
    (hP : IsSylowOf 2 P ⊤) {t : M} (ht : t * t = 1) : ∃ g : M, g * t * g⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ P.index := by
    have := (isSylowOf_iff.1 hP).2.2
    rwa [Subgroup.relIndex_top_right] at this
  let PS : Sylow 2 M := hP.isPGroup.toSylow hidx
  have h2 : IsPGroup 2 (Subgroup.zpowers t) := by
    have hd : Nat.card (Subgroup.zpowers t) = orderOf t := Nat.card_zpowers t
    have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ht)
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [hd, h1]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [hd, h1]; simp)
  obtain ⟨R, hR⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M R PS
  refine ⟨g, ?_⟩
  have hmem : g * t * g⁻¹ ∈ (PS : Subgroup M) := by
    rw [← hg]
    exact ⟨t, hR (Subgroup.mem_zpowers t), by simp [MulAut.conj_apply]⟩
  rwa [IsPGroup.toSylow_coe] at hmem

end GLevel3

section Assembly

open scoped commutatorElement

abbrev NWbar {G : Type} [Group G] (x : G) : Type _ := ↥(NW x) ⧸ pPrimeCore 2 ↥(NW x)

@[expose] def toNWbar {G : Type} [Group G] (x : G) (K : Subgroup G) : Subgroup (NWbar x) :=
  (K.subgroupOf (NW x)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(NW x)))

@[expose] def B_ivk_7_3_A57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({5, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfigW n x K T Q S a → S = T ⊔ zpowers a →
      a * x * a⁻¹ ∈ T ⊓ K → a ∈ NW x → pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥ →
        ∃ (H : Subgroup (NWbar x)) (e : ↥H ≃* alternatingGroup (Fin (n + 4))), H.IsSubnormal ∧
          toNWbar x K ≤ H ∧ ((toNWbar x K).subgroupOf H).map e.toMonoidHom = stdAlt n

theorem orderOf_conj_eq {G : Type*} [Group G] (c t : G) : orderOf (c * t * c⁻¹) = orderOf t :=
  (SemiconjBy.orderOf_eq c (by change c * t = c * t * c⁻¹ * c; group)).symm

end Assembly

end CFSG.GH74.GLS.C3.Layer1.Bk
