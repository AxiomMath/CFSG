module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Lemmas

variable {G : Type*} [Group G]

theorem comm_mul_left {x y b t : G} (hx : x * t = t * x)
    (hcx : x * b * x⁻¹ * b⁻¹ = 1 ∨ x * b * x⁻¹ * b⁻¹ = t)
    (hcy : y * b * y⁻¹ * b⁻¹ = 1 ∨ y * b * y⁻¹ * b⁻¹ = t) :
    (x * y) * b * (x * y)⁻¹ * b⁻¹ = (x * b * x⁻¹ * b⁻¹) * (y * b * y⁻¹ * b⁻¹) := by
  have h1 : (x * y) * b * (x * y)⁻¹ * b⁻¹ =
      x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group
  have h2 : x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ = y * b * y⁻¹ * b⁻¹ := by
    rcases hcy with h | h
    · rw [h]; group
    · rw [h, hx, mul_inv_cancel_right]
  rw [h1, h2]
  rcases hcx with h | h <;> rcases hcy with h' | h' <;> rw [h, h'] <;> simp

variable [Finite G]

theorem card_le_two_mul_card_inf_centralizer {K : Subgroup G} {b t : G} (ht2 : t * t = 1)
    (hc : ∀ k ∈ K, k * b * k⁻¹ * b⁻¹ = 1 ∨ k * b * k⁻¹ * b⁻¹ = t)
    (htK : ∀ k ∈ K, k * t = t * k) :
    Nat.card K ≤ 2 * Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by
  have hmem : ∀ k : K, (k : G) * b * (k : G)⁻¹ * b⁻¹ ∈ zpowers t := by
    intro k
    rcases hc k k.2 with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers t
  let f : K →* zpowers t :=
    MonoidHom.mk' (fun k => ⟨(k : G) * b * (k : G)⁻¹ * b⁻¹, hmem k⟩) (fun k k' => by
      apply Subtype.ext
      exact comm_mul_left (htK k k.2) (hc k k.2) (hc k' k'.2))
  have hker : Nat.card f.ker ≤ Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨(k.1 : G), k.1.2, ?_⟩) ?_
    · have h1 : (k.1 : G) * b * (k.1 : G)⁻¹ * b⁻¹ = 1 := congrArg Subtype.val k.2
      change (k.1 : G) ∈ centralizer ({b} : Set G)
      rw [mem_centralizer_singleton_iff]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    · intro a a' h
      have h' := congrArg (fun y : ↥(K ⊓ centralizer ({b} : Set G)) => (y : G)) h
      exact Subtype.ext (Subtype.ext h')
  have hrange : Nat.card f.range ≤ 2 := by
    calc Nat.card f.range ≤ Nat.card (zpowers t) := Subgroup.card_le_card_group _
      _ = orderOf t := Nat.card_zpowers t
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact ht2)
  have hK := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at hK
  calc Nat.card K = Nat.card f.ker * Nat.card f.range := hK.symm
    _ ≤ Nat.card f.ker * 2 := Nat.mul_le_mul_left _ hrange
    _ ≤ 2 * Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by omega


theorem two_mul_card_le_cent {U : Subgroup G} {t : G} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = t)
    (hcen : ∀ u ∈ U, u * t = t * u) (H : Subgroup G) (htH : t ∈ H) (hHU : H ≤ U) :
    2 * Nat.card U ≤ Nat.card ↥(U ⊓ centralizer (H : Set G)) * Nat.card H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hordt : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  suffices h : ∀ n : ℕ, ∀ H : Subgroup G, Nat.card H = n → t ∈ H → H ≤ U →
      2 * Nat.card U ≤ Nat.card ↥(U ⊓ centralizer (H : Set G)) * Nat.card H from h _ H rfl htH hHU
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn htH hHU
    by_cases hzt : H ≤ zpowers t
    · have hC : U ⊓ centralizer (H : Set G) = U := by
        apply inf_of_le_left
        intro u hu
        rw [mem_centralizer_iff]
        intro h hh
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (hzt hh)
        exact ((Commute.zpow_left (show Commute t u from (hcen u hu).symm) k).eq)
      have hH2 : 2 ≤ Nat.card H := by
        calc 2 = Nat.card (zpowers t) := by rw [Nat.card_zpowers, hordt]
          _ ≤ Nat.card H := Subgroup.card_le_of_le (zpowers_le.2 htH)
      rw [hC]
      exact Nat.mul_comm 2 _ ▸ Nat.mul_le_mul_left _ hH2
    · have hlt : zpowers t < H := lt_of_le_of_ne (zpowers_le.2 htH) (fun h => hzt h.symm.le)
      obtain ⟨H', ⟨hH'1, hH'2⟩, hmax⟩ := (wellFounded_gt (α := Subgroup G)).has_min
        {K : Subgroup G | zpowers t ≤ K ∧ K < H} ⟨zpowers t, le_rfl, hlt⟩
      obtain ⟨b, hbH, hbH'⟩ := IsConcreteLE.exists_of_lt hH'2
      have hH''le : H' ⊔ zpowers b ≤ H := sup_le hH'2.le (zpowers_le.2 hbH)
      have hH'' : H' ⊔ zpowers b = H := by
        by_contra hne
        exact hmax (H' ⊔ zpowers b) ⟨hH'1.trans le_sup_left, lt_of_le_of_ne hH''le hne⟩
          (lt_of_le_of_ne le_sup_left (fun h => hbH' (h ▸ mem_sup_right (mem_zpowers b))))
      have htH' : t ∈ H' := zpowers_le.1 hH'1
      have hH'U : H' ≤ U := hH'2.le.trans hHU
      have hcardlt : Nat.card H' < n := hn ▸ Subgroup.card_lt_of_lt hH'2
      have hIH := ih _ hcardlt H' rfl htH' hH'U
      have hbU : b ∈ U := hHU hbH
      have hK := card_le_two_mul_card_inf_centralizer (K := U ⊓ centralizer (H' : Set G)) (b := b)
        ht2 (fun k hk => hcomm k (mem_inf.1 hk).1 b hbU) (fun k hk => hcen k (mem_inf.1 hk).1)
      have hle : (U ⊓ centralizer (H' : Set G)) ⊓ centralizer ({b} : Set G) ≤
          U ⊓ centralizer (H : Set G) := by
        intro x hx
        obtain ⟨⟨hxU, hxH'⟩, hxb⟩ := mem_inf.1 hx |>.imp_left mem_inf.1
        refine mem_inf.2 ⟨hxU, ?_⟩
        rw [mem_centralizer_iff]
        have hHx : H ≤ centralizer ({x} : Set G) := by
          rw [← hH'']
          refine sup_le (fun h' hh' => ?_) (zpowers_le.2 ?_)
          · rw [mem_centralizer_singleton_iff]
            exact mem_centralizer_iff.1 hxH' h' hh'
          · rw [mem_centralizer_singleton_iff]
            exact (mem_centralizer_singleton_iff.1 hxb).symm
        intro h hh
        exact mem_centralizer_singleton_iff.1 (hHx hh)
      have hcard2 := Subgroup.card_le_of_le hle
      have hdvd := Subgroup.card_dvd_of_le hH'2.le
      obtain ⟨m, hm⟩ := hdvd
      have hpos : 0 < Nat.card H' := Nat.card_pos
      have hm2 : 2 ≤ m := by
        by_contra hlt2
        have : m ≤ 1 := by omega
        have : Nat.card H' * m ≤ Nat.card H' * 1 := Nat.mul_le_mul_left _ this
        omega
      have hH2 : 2 * Nat.card H' ≤ Nat.card H := by
        rw [hm]; nlinarith
      calc 2 * Nat.card U ≤ Nat.card ↥(U ⊓ centralizer (H' : Set G)) * Nat.card H' := hIH
        _ ≤ (2 * Nat.card ↥((U ⊓ centralizer (H' : Set G)) ⊓ centralizer ({b} : Set G))) *
              Nat.card H' := Nat.mul_le_mul_right _ hK
        _ ≤ (2 * Nat.card ↥(U ⊓ centralizer (H : Set G))) * Nat.card H' :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcard2)
        _ = Nat.card ↥(U ⊓ centralizer (H : Set G)) * (2 * Nat.card H') := by ring
        _ ≤ Nat.card ↥(U ⊓ centralizer (H : Set G)) * Nat.card H :=
            Nat.mul_le_mul_left _ hH2


@[expose] def mulHom (S E : Subgroup G) (h : S ≤ centralizer (E : Set G)) : ↥S × ↥E →* G where
  toFun p := (p.1 : G) * p.2
  map_one' := by simp
  map_mul' p q := by
    have hc : (q.1 : G) * p.2 = p.2 * q.1 := (mem_centralizer_iff.1 (h q.1.2) p.2 p.2.2).symm
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    calc (p.1 : G) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by simp only [mul_assoc]
      _ = p.1 * (p.2 * q.1) * q.2 := by rw [hc]
      _ = (p.1 * p.2) * (q.1 * q.2) := by simp only [mul_assoc]

omit [Finite G] in
theorem mulHom_apply (S E : Subgroup G) (h : S ≤ centralizer (E : Set G)) (p : ↥S × ↥E) :
    mulHom S E h p = (p.1 : G) * p.2 := rfl

omit [Finite G] in
theorem range_mulHom_le (S E : Subgroup G) (h : S ≤ centralizer (E : Set G)) :
    (mulHom S E h).range ≤ S ⊔ E := by
  rintro _ ⟨p, rfl⟩
  exact mul_mem_sup p.1.2 p.2.2

omit [Finite G] in
theorem card_ker_mul_card_range (S E : Subgroup G) (h : S ≤ centralizer (E : Set G)) :
    Nat.card (mulHom S E h).ker * Nat.card (mulHom S E h).range = Nat.card S * Nat.card E := by
  have hK := Subgroup.card_mul_index (mulHom S E h).ker
  rw [Subgroup.index_ker, Nat.card_prod] at hK
  exact hK

theorem card_ker_mulHom_le {S E : Subgroup G} {t : G} (hSE : S ≤ centralizer (E : Set G))
    (hcenter : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t) (ht2 : t * t = 1) :
    Nat.card (mulHom S E hSE).ker ≤ 2 := by
  have hmem : ∀ p : (mulHom S E hSE).ker, ((p.1.2 : E) : G) ∈ zpowers t := by
    intro p
    have h1 : (p.1.1 : G) * p.1.2 = 1 := p.2
    have he : ((p.1.2 : E) : G) = ((p.1.1 : S) : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hcen : ∀ f ∈ E, f * ((p.1.2 : E) : G) = ((p.1.2 : E) : G) * f := by
      intro f hf
      rw [he]
      have hs : ((p.1.1 : S) : G)⁻¹ ∈ centralizer (E : Set G) := inv_mem (hSE p.1.1.2)
      exact mem_centralizer_iff.1 hs f hf
    rcases hcenter (p.1.2 : G) p.1.2.2 hcen with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers t
  calc Nat.card (mulHom S E hSE).ker ≤ Nat.card (zpowers t) := by
        refine Nat.card_le_card_of_injective (fun p => ⟨(p.1.2 : G), hmem p⟩) ?_
        intro a a' h
        have h' := congrArg (fun y : ↥(zpowers t) => (y : G)) h
        have h1 : (a.1.1 : G) * a.1.2 = 1 := a.2
        have h2 : (a'.1.1 : G) * a'.1.2 = 1 := a'.2
        have hE' : (a.1.2 : G) = (a'.1.2 : G) := h'
        have hS' : (a.1.1 : G) = (a'.1.1 : G) := by
          rw [eq_inv_of_mul_eq_one_left h1, eq_inv_of_mul_eq_one_left h2, hE']
        exact Subtype.ext (Prod.ext (Subtype.ext hS') (Subtype.ext hE'))
    _ = orderOf t := Nat.card_zpowers t
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact ht2)

theorem card_sup_ge {S E : Subgroup G} {t : G} (hSE : S ≤ centralizer (E : Set G))
    (hcenter : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t) (ht2 : t * t = 1)
    (hS : Nat.card S = 8) (hE : Nat.card E = 32) : 128 ≤ Nat.card ↥(S ⊔ E) := by
  have hK := card_ker_mul_card_range S E hSE
  have hker := card_ker_mulHom_le hSE hcenter ht2
  have hr : Nat.card (mulHom S E hSE).range ≤ Nat.card ↥(S ⊔ E) :=
    Subgroup.card_le_of_le (range_mulHom_le S E hSE)
  rw [hS, hE] at hK
  nlinarith

omit [Finite G] in
theorem sup_le_range_mulHom (S E : Subgroup G) (h : S ≤ centralizer (E : Set G)) :
    S ⊔ E ≤ (mulHom S E h).range := by
  intro x hx
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (Subgroup.le_centralizer_iff.1 h) hx
  exact ⟨(⟨s, hs⟩, ⟨e, he⟩), rfl⟩

theorem card_sup_eq {S E : Subgroup G} {t : G} (hSE : S ≤ centralizer (E : Set G))
    (hcenter : ∀ y ∈ E, (∀ f ∈ E, f * y = y * f) → y = 1 ∨ y = t) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htS : t ∈ S) (htE : t ∈ E)
    (hS : Nat.card S = 8) (hE : Nat.card E = 32) : Nat.card ↥(S ⊔ E) = 128 := by
  have hK := card_ker_mul_card_range S E hSE
  have hker := card_ker_mulHom_le hSE hcenter ht2
  have hne : (mulHom S E hSE).ker ≠ ⊥ := by
    intro h
    have hmem : ((⟨t, htS⟩ : S), (⟨t, htE⟩ : E)) ∈ (mulHom S E hSE).ker := by
      rw [MonoidHom.mem_ker]; exact ht2
    rw [h, Subgroup.mem_bot] at hmem
    exact ht1 (congrArg (fun p : ↥S × ↥E => (p.1 : G)) hmem)
  have h2 : 2 ≤ Nat.card (mulHom S E hSE).ker :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hr1 : Nat.card ↥(S ⊔ E) ≤ Nat.card (mulHom S E hSE).range :=
    Subgroup.card_le_of_le (sup_le_range_mulHom S E hSE)
  have hr2 : Nat.card (mulHom S E hSE).range ≤ Nat.card ↥(S ⊔ E) :=
    Subgroup.card_le_of_le (range_mulHom_le S E hSE)
  have hk : Nat.card (mulHom S E hSE).ker = 2 := le_antisymm hker h2
  rw [hS, hE, hk] at hK
  omega

omit [Finite G] in
theorem dihedral_comm {S : Subgroup G} {t : G} (htS : t ∈ S) (ht1 : t ≠ 1)
    (htc : ∀ s ∈ S, s * t = t * s) (φ : S ≃* DihedralGroup 4) :
    ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ = 1 ∨ s * s' * s⁻¹ * s'⁻¹ = t := by
  have hD : ∀ a b : DihedralGroup 4,
      a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = DihedralGroup.r 2 := by decide
  have hZ : ∀ c : DihedralGroup 4, c ≠ 1 → (∀ a : DihedralGroup 4, a * c = c * a) →
      c = DihedralGroup.r 2 := by decide
  have hφt : φ ⟨t, htS⟩ = DihedralGroup.r 2 := by
    refine hZ _ (fun h => ht1 ?_) (fun a => ?_)
    · have := φ.injective (h.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    · obtain ⟨s, rfl⟩ := φ.surjective a
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext (htc s s.2))
  intro s hs s' hs'
  have h := hD (φ ⟨s, hs⟩) (φ ⟨s', hs'⟩)
  have hφ : φ (⟨s, hs⟩ * ⟨s', hs'⟩ * ⟨s, hs⟩⁻¹ * ⟨s', hs'⟩⁻¹) =
      φ ⟨s, hs⟩ * φ ⟨s', hs'⟩ * (φ ⟨s, hs⟩)⁻¹ * (φ ⟨s', hs'⟩)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [← hφ] at h
  rcases h with h | h
  · left
    have := φ.injective (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  · right
    have := φ.injective (h.trans hφt.symm)
    exact congrArg Subtype.val this

omit [Finite G] in
theorem comm_sup {S E : Subgroup G} {t : G} (hSE : S ≤ centralizer (E : Set G)) (ht2 : t * t = 1)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ = 1 ∨ s * s' * s⁻¹ * s'⁻¹ = t)
    (hE : ∀ e ∈ E, ∀ e' ∈ E, e * e' * e⁻¹ * e'⁻¹ = 1 ∨ e * e' * e⁻¹ * e'⁻¹ = t) :
    ∀ u ∈ S ⊔ E, ∀ v ∈ S ⊔ E, u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = t := by
  have hES : E ≤ centralizer (S : Set G) := fun e he => mem_centralizer_iff.2 fun s hs =>
    (mem_centralizer_iff.1 (hSE hs) e he).symm
  intro u hu v hv
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hES hu
  obtain ⟨s', hs', e', he', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hES hv
  have key := map_commutatorElement (mulHom S E hSE) (⟨s, hs⟩, ⟨e, he⟩) (⟨s', hs'⟩, ⟨e', he'⟩)
  simp only [mulHom_apply, commutatorElement_def, Prod.mk_mul_mk, Prod.inv_mk] at key
  have e1 : ((⟨s, hs⟩ * ⟨s', hs'⟩ * ⟨s, hs⟩⁻¹ * ⟨s', hs'⟩⁻¹ : S) : G) = s * s' * s⁻¹ * s'⁻¹ := rfl
  have e2 : ((⟨e, he⟩ * ⟨e', he'⟩ * ⟨e, he⟩⁻¹ * ⟨e', he'⟩⁻¹ : E) : G) = e * e' * e⁻¹ * e'⁻¹ := rfl
  rw [e1, e2] at key
  rw [← key]
  rcases hS s hs s' hs' with h | h <;> rcases hE e he e' he' with h' | h' <;> rw [h, h'] <;>
    simp [ht2]

omit [Finite G] in
theorem central_sup {S E : Subgroup G} {t : G} (hSE : S ≤ centralizer (E : Set G)) (htE : t ∈ E)
    (htc : ∀ e ∈ E, e * t = t * e) : ∀ u ∈ S ⊔ E, u * t = t * u := by
  have hES : E ≤ centralizer (S : Set G) := fun e he => mem_centralizer_iff.2 fun s hs =>
    (mem_centralizer_iff.1 (hSE hs) e he).symm
  intro u hu
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hES hu
  have hts : t * s = s * t := mem_centralizer_iff.1 (hSE hs) t htE
  calc s * e * t = s * (e * t) := mul_assoc _ _ _
    _ = s * (t * e) := by rw [htc e he]
    _ = (s * t) * e := (mul_assoc _ _ _).symm
    _ = (t * s) * e := by rw [hts]
    _ = t * (s * e) := mul_assoc _ _ _

theorem mem_of_maximal {S E : Subgroup G} {t : G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (ht2 : t * t = 1) (htE : t ∈ E) (htc : ∀ e ∈ E, e * t = t * e) : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSt : S ≤ centralizer (zpowers t : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (mem_centralizer_iff.1 (hSC hs) t htE) k).eq
  set ρ := mulHom S (zpowers t) hSt with hρ
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hS2
  obtain ⟨b, hb⟩ : ∃ b, Nat.card (zpowers t) = 2 ^ b := by
    rw [Nat.card_zpowers]
    have h2 : orderOf t ∣ 2 ^ 1 := by
      simpa using orderOf_dvd_of_pow_eq_one (show t ^ 2 = 1 by rw [pow_two]; exact ht2)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact ⟨m, hm⟩
  have hP : IsPGroup 2 (↥S × ↥(zpowers t)) :=
    IsPGroup.of_card (n := a + b) (by rw [Nat.card_prod, ha, hb, pow_add])
  have hP' : IsPGroup 2 ρ.range :=
    hP.of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
  have hle : ρ.range ≤ centralizer (E : Set G) := by
    rintro _ ⟨p, rfl⟩
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 p.2.2
    have h1 : e * (p.1 : G) = (p.1 : G) * e := mem_centralizer_iff.1 (hSC p.1.2) e he
    have h2 : e * (p.2 : G) = (p.2 : G) * e := by
      rw [← hk]; exact (Commute.zpow_right (htc e he) k).eq
    rw [mulHom_apply]
    calc e * ((p.1 : G) * p.2) = ((p.1 : G) * p.2) * e := by
          rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
      _ = _ := rfl
  have hSR : S ≤ ρ.range := fun s hs =>
    ⟨(⟨s, hs⟩, 1), by show s * ((1 : ↥(zpowers t)) : G) = s; simp⟩
  have heq := hSmax ρ.range hP' hle hSR
  have htR : t ∈ ρ.range :=
    ⟨(1, ⟨t, mem_zpowers t⟩), by show ((1 : ↥S) : G) * t = t; simp⟩
  rwa [heq] at htR


end Lemmas

theorem eight_le_card_cent_of_mem {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G} {Q : Sylow 2 G} {x β : G} {B : Subgroup G}
    (hconf : Rest6Config L z t T₀ E Q x β B) (hW : WFacts L t E) {S : Subgroup G}
    (hSC : S ≤ centralizer (E : Set G)) (htS : t ∈ S)
    (hD8 : Nonempty (S ≃* DihedralGroup 4)) {E₀ : Subgroup G} (hE₀ : E₀ ≤ S ⊔ E)
    (hiso : Nonempty (E ≃* E₀)) :
    8 ≤ Nat.card ↥((S ⊔ E) ⊓ centralizer (E₀ : Set G)) := by
  have hE := hconf.econfig
  have hcfg := hconf.cfg
  have ht2 : t * t = 1 := hcfg.t_sq
  have ht1 : t ≠ 1 := hcfg.t_ne
  have htc : ∀ e ∈ E, e * t = t * e := fun e he => hcfg.t_central e (hE.le he)
  have htE : t ∈ E := hE.t_mem
  obtain ⟨φ⟩ := hD8
  have hSt : ∀ s ∈ S, s * t = t * s := fun s hs => (mem_centralizer_iff.1 (hSC hs) t htE).symm
  have hScard : Nat.card S = 8 := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hSc := dihedral_comm htS ht1 hSt φ
  have hU := comm_sup hSC ht2 hSc hE.comm
  have hcenU := central_sup hSC htE htc
  have hcard := card_sup_ge hSC hE.center ht2 hScard hW.card_E
  obtain ⟨ψ⟩ := hiso
  have hE₀card : Nat.card E₀ = 32 := by
    rw [← hW.card_E]; exact (Nat.card_congr ψ.toEquiv).symm
  have htE₀ : t ∈ E₀ := by
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hE.nonab
    have hxy : (ψ ⟨e₁, he₁⟩ : G) * (ψ ⟨e₂, he₂⟩ : G) ≠ (ψ ⟨e₂, he₂⟩ : G) * (ψ ⟨e₁, he₁⟩ : G) := by
      intro h
      apply hne
      have h1 : ψ ⟨e₁, he₁⟩ * ψ ⟨e₂, he₂⟩ = ψ ⟨e₂, he₂⟩ * ψ ⟨e₁, he₁⟩ := Subtype.ext h
      have h2 : (⟨e₁, he₁⟩ * ⟨e₂, he₂⟩ : E) = ⟨e₂, he₂⟩ * ⟨e₁, he₁⟩ :=
        ψ.injective (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    have hx : (ψ ⟨e₁, he₁⟩ : G) ∈ E₀ := (ψ ⟨e₁, he₁⟩).2
    have hy : (ψ ⟨e₂, he₂⟩ : G) ∈ E₀ := (ψ ⟨e₂, he₂⟩).2
    rcases hU _ (hE₀ hx) _ (hE₀ hy) with h | h
    · exfalso
      apply hxy
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
      exact h
    · rw [← h]
      exact E₀.mul_mem (E₀.mul_mem (E₀.mul_mem hx hy) (E₀.inv_mem hx)) (E₀.inv_mem hy)
  have key := two_mul_card_le_cent ht2 ht1 hU hcenU E₀ htE₀ hE₀
  rw [hE₀card] at key
  omega

theorem eight_le_card_cent_of_equiv {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G} {Q : Sylow 2 G} {x β : G} {B : Subgroup G}
    (hconf : Rest6Config L z t T₀ E Q x β B) (hW : WFacts L t E) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hD8 : Nonempty (S ≃* DihedralGroup 4)) {E₀ : Subgroup G} (hE₀ : E₀ ≤ S ⊔ E)
    (hiso : Nonempty (E ≃* E₀)) :
    8 ≤ Nat.card ↥((S ⊔ E) ⊓ centralizer (E₀ : Set G)) :=
  eight_le_card_cent_of_mem hconf hW hSC
    (mem_of_maximal hS2 hSC hSmax hconf.cfg.t_sq hconf.econfig.t_mem
      fun e he => hconf.cfg.t_central e (hconf.econfig.le he)) hD8 hE₀ hiso

end CFSG.EvenSporadicStandard.Fin76b
