module

public import CFSG.LargeExtraspecial.S8CBFSect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup
open scoped commutatorElement Pointwise

@[expose] def NormalTwoDatum {S : Type*} [Group S] (s : S) : Prop :=
  ∃ Q : Subgroup S, Q ≤ centralizer ({s} : Set S) ∧
    (∀ c ∈ centralizer ({s} : Set S), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧
    ∀ P : Subgroup S, P ≤ centralizer ({s} : Set S) → IsPGroup 2 P → ⁅P, P⁆ ≤ Q

theorem invCentSectAbelianSylow_of_normalTwoDatum {S : Type*} [Group S] [Finite S]
    (h : ∀ s : S, orderOf s = 2 → NormalTwoDatum s) : InvCentSectAbelianSylow S :=
  invCentSectAbelianSylow_of_commutator_le h

theorem NormalTwoDatum.of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T) {s : S}
    (h : NormalTwoDatum (e s)) : NormalTwoDatum s := by
  obtain ⟨Q, hQC, hQn, hQ2, hPQ⟩ := h
  have hC : ∀ x : S, x ∈ centralizer ({s} : Set S) ↔ e x ∈ centralizer ({e s} : Set T) := by
    intro x
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      e.injective.eq_iff]
  refine ⟨Q.comap e.toMonoidHom, fun q hq => (hC q).mpr (hQC hq), fun c hc q hq => ?_,
    hQ2.comap_of_injective _ e.injective, fun P hP hP2 => ?_⟩
  · change e (c * q * c⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact hQn _ ((hC c).mp hc) _ hq
  · have hPe : P.map e.toMonoidHom ≤ centralizer ({e s} : Set T) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hC x).mp (hP hx)
    have h1 := hPQ _ hPe (hP2.map _)
    rw [← map_commutator] at h1
    exact (map_le_iff_le_comap).mp h1

theorem commutator_le_of_card_eq_sixty_mul {G : Type*} [Group G] [Finite G] {C Q P : Subgroup G}
    (hQC : Q ≤ C) (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q)
    (hcard : Nat.card C = 60 * Nat.card Q) (hPC : P ≤ C) (hP2 : IsPGroup 2 P) :
    ⁅P, P⁆ ≤ Q := by
  have := Fact.mk Nat.prime_two
  have hCN : C ≤ normalizer (Q : Set G) := fun c hc =>
    mem_normalizer_iff''.mpr fun q => by
      constructor
      · intro hq
        have := hQn c⁻¹ (inv_mem hc) q hq
        simpa using this
      · intro hq
        have h1 := hQn c hc _ hq
        have e : c * (c⁻¹ * q * c) * c⁻¹ = q := by group
        rwa [e] at h1
  set H : Subgroup G := P ⊔ Q with hH
  have hHC : H ≤ C := sup_le hPC hQC
  have hQH : Q ≤ H := le_sup_right
  have hH2 : IsPGroup 2 H := hP2.to_sup_of_normal_right' hQ2 (hPC.trans hCN)
  have hHN : H ≤ normalizer (Q : Set G) := hHC.trans hCN
  have hn : (Q.subgroupOf H).Normal := by
    constructor
    intro q hq h
    rw [mem_subgroupOf] at hq ⊢
    have := hQn h (hHC h.2) q hq
    simpa using this
  have hQcard : Nat.card (Q.subgroupOf H) = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv
  have hHcard : Nat.card H = Nat.card (↥H ⧸ Q.subgroupOf H) * Nat.card Q := by
    rw [← hQcard]
    exact card_eq_card_quotient_mul_card_subgroup _
  have hdvd : Nat.card (↥H ⧸ Q.subgroupOf H) ∣ 60 := by
    have h1 : Nat.card H ∣ Nat.card C := card_dvd_of_le hHC
    rw [hHcard, hcard] at h1
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h1
  have hq2 : IsPGroup 2 (↥H ⧸ Q.subgroupOf H) := hH2.to_quotient _
  have hle4 : Nat.card (↥H ⧸ Q.subgroupOf H) ≤ 4 := by
    obtain ⟨k, hk⟩ := hq2.exists_card_eq
    rw [hk] at hdvd ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 hk3).trans hdvd
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hcomm : ∀ a b : ↥H ⧸ Q.subgroupOf H, a * b = b * a := by
    obtain ⟨k, hk⟩ := hq2.exists_card_eq
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    interval_cases k
    · have : Subsingleton (↥H ⧸ Q.subgroupOf H) :=
        (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact fun a b => Subsingleton.elim _ _
    · have : IsCyclic (↥H ⧸ Q.subgroupOf H) := isCyclic_of_prime_card (p := 2) (by simpa using hk)
      exact fun a b => (IsCyclic.isMulCommutative.is_comm.comm a b)
    · have hc : IsMulCommutative (↥H ⧸ Q.subgroupOf H) :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hk)
      exact fun a b => hc.is_comm.comm a b
  rw [commutator_le]
  intro a ha b hb
  have haH : a ∈ H := le_sup_left (a := P) ha
  have hbH : b ∈ H := le_sup_left (a := P) hb
  have h1 : (QuotientGroup.mk' (Q.subgroupOf H)) ⁅(⟨a, haH⟩ : H), ⟨b, hbH⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  have e2 : ((⁅(⟨a, haH⟩ : H), ⟨b, hbH⟩⁆ : H) : G) = ⁅a, b⁆ :=
    map_commutatorElement H.subtype _ _
  rwa [e2] at h1

section Ambient

variable {G : Type*} [Group G]

@[expose] def RelNormalTwoDatum (H : Subgroup G) (τ : G) : Prop :=
  ∃ Q : Subgroup G, Q ≤ H ⊓ centralizer ({τ} : Set G) ∧
    (∀ c ∈ H ⊓ centralizer ({τ} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧
    ∀ P : Subgroup G, P ≤ H ⊓ centralizer ({τ} : Set G) → IsPGroup 2 P → ⁅P, P⁆ ≤ Q

theorem inf_centralizer_conj_eq_map (H : Subgroup G) {g : G} (hg : g ∈ H) (t : G) :
    H ⊓ centralizer ({g * t * g⁻¹} : Set G) =
      (H ⊓ centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨g⁻¹ * x * g, ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩, by group⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxt]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hy, hyt⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg), ?_⟩
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hyt]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

theorem RelNormalTwoDatum.conj {H : Subgroup G} {t g : G} (hg : g ∈ H)
    (h : RelNormalTwoDatum H t) : RelNormalTwoDatum H (g * t * g⁻¹) := by
  obtain ⟨Q, hQC, hQn, hQ2, hPQ⟩ := h
  rw [RelNormalTwoDatum, inf_centralizer_conj_eq_map H hg t]
  refine ⟨Q.map (MulAut.conj g).toMonoidHom, map_mono hQC, ?_, hQ2.map _, fun P hP hP2 => ?_⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨q, hq, rfl⟩
    refine ⟨c * q * c⁻¹, hQn c hc q hq, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · let e := (MulAut.conj g).toMonoidHom
    have hP' : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ H ⊓ centralizer ({t} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hP hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group]
    have h1 := hPQ _ hP' (hP2.map _)
    have h2 := map_mono (f := e) h1
    rw [map_commutator, map_map] at h2
    have hid : e.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp only [e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rwa [hid, map_id] at h2

theorem normalTwoDatum_of_rel {H : Subgroup G} {s : H} (h : RelNormalTwoDatum H (s : G)) :
    NormalTwoDatum s := by
  obtain ⟨Q, hQC, hQn, hQ2, hPQ⟩ := h
  have hC : ∀ x : H, x ∈ centralizer ({s} : Set H) ↔
      (x : G) ∈ H ⊓ centralizer ({(s : G)} : Set G) := by
    intro x
    rw [mem_centralizer_singleton_iff, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun hx => ⟨x.2, congrArg Subtype.val hx⟩, fun hx => Subtype.ext hx.2⟩
  refine ⟨Q.subgroupOf H, fun q hq => (hC q).mpr (hQC (mem_subgroupOf.mp hq)), ?_,
    hQ2.comap_subtype, fun P hP hP2 => ?_⟩
  · intro c hc q hq
    rw [mem_subgroupOf] at hq ⊢
    simpa using hQn c ((hC c).mp hc) q hq
  · have hP' : P.map H.subtype ≤ H ⊓ centralizer ({(s : G)} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hC x).mp (hP hx)
    have h1 := hPQ _ hP' (hP2.map _)
    rw [← map_commutator] at h1
    intro x hx
    rw [mem_subgroupOf]
    exact h1 ⟨x, hx, rfl⟩

theorem normalizes_of_mul_eq {C Q L : Subgroup G}
    (hC : (C : Set G) = (Q : Set G) * (L : Set G)) (hLN : L ≤ normalizer (Q : Set G)) :
    ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
  intro c hc q hq
  have hc' : c ∈ (Q : Set G) * (L : Set G) := by
    rw [← hC]
    exact hc
  obtain ⟨q₀, hq₀, l, hl, rfl⟩ := hc'
  have hlq : l * q * l⁻¹ ∈ Q := (mem_normalizer_iff.mp (hLN hl) q).mp hq
  have : q₀ * l * q * (q₀ * l)⁻¹ = q₀ * (l * q * l⁻¹) * q₀⁻¹ := by group
  rw [this]
  exact Q.mul_mem (Q.mul_mem hq₀ hlq) (Q.inv_mem hq₀)

theorem normal_subgroupOf_of_normalizes {C Q : Subgroup G}
    (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) : (Q.subgroupOf C).Normal := by
  constructor
  intro q hq c
  rw [mem_subgroupOf] at hq ⊢
  simpa using hQn c c.2 q hq

theorem exists_mulEquiv_quotient_of_mul_eq {C Q L : Subgroup G} [(Q.subgroupOf C).Normal]
    (hC : (C : Set G) = (Q : Set G) * (L : Set G)) (hLC : L ≤ C)
    (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hQL : Q ⊓ L = ⊥) :
    ∃ e : L ≃* ↥C ⧸ Q.subgroupOf C,
      ∀ l : L, e l = QuotientGroup.mk' (Q.subgroupOf C) (Subgroup.inclusion hLC l) := by
  let f : L →* ↥C ⧸ Q.subgroupOf C :=
    (QuotientGroup.mk' (Q.subgroupOf C)).comp (Subgroup.inclusion hLC)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    have h1 : Subgroup.inclusion hLC l ∈ Q.subgroupOf C := (QuotientGroup.eq_one_iff _).mp hl
    rw [mem_subgroupOf] at h1
    have h2 : (l : G) ∈ Q ⊓ L := mem_inf.mpr ⟨h1, l.2⟩
    rw [hQL, mem_bot] at h2
    exact mem_bot.mpr (Subtype.ext h2)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hc : (c : G) ∈ (Q : Set G) * (L : Set G) := hC ▸ c.2
    obtain ⟨q, hq, l, hl, hql⟩ := hc
    refine ⟨⟨l, hl⟩, ?_⟩
    change QuotientGroup.mk' _ (Subgroup.inclusion hLC ⟨l, hl⟩) = QuotientGroup.mk' _ c
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    have := hQn l⁻¹ (C.inv_mem (hLC hl)) q hq
    simp only [coe_mul, coe_inv, Subgroup.coe_inclusion]
    rw [← hql]
    simpa [mul_assoc] using this
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun l => rfl⟩

theorem commutator_le_of_mul_eq {C Q L P : Subgroup G}
    (hC : (C : Set G) = (Q : Set G) * (L : Set G)) (hLC : L ≤ C)
    (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hQL : Q ⊓ L = ⊥)
    (hL : ∀ A : Subgroup G, A ≤ L → IsPGroup 2 A → ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hPC : P ≤ C) (hP2 : IsPGroup 2 P) : ⁅P, P⁆ ≤ Q := by
  have := normal_subgroupOf_of_normalizes hQn
  obtain ⟨e, -⟩ := exists_mulEquiv_quotient_of_mul_eq hC hLC hQn hQL
  rw [commutator_le]
  intro a ha b hb
  let A : Subgroup G :=
    (((P.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C))).map e.symm.toMonoidHom).map
      L.subtype
  have hA2 : IsPGroup 2 A := ((hP2.comap_subtype (K := C)).map _ |>.map _).map _
  have hAL : A ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let x : ↥C ⧸ Q.subgroupOf C := QuotientGroup.mk' _ ⟨a, hPC ha⟩
  let y : ↥C ⧸ Q.subgroupOf C := QuotientGroup.mk' _ ⟨b, hPC hb⟩
  have hxA : ((e.symm x : L) : G) ∈ A :=
    ⟨e.symm x, ⟨x, ⟨⟨a, hPC ha⟩, mem_subgroupOf.mpr ha, rfl⟩, rfl⟩, rfl⟩
  have hyA : ((e.symm y : L) : G) ∈ A :=
    ⟨e.symm y, ⟨y, ⟨⟨b, hPC hb⟩, mem_subgroupOf.mpr hb, rfl⟩, rfl⟩, rfl⟩
  have hxy : e.symm x * e.symm y = e.symm y * e.symm x :=
    Subtype.ext (hL A hAL hA2 _ hxA _ hyA)
  have hxy' : x * y = y * x := by
    have := congrArg e hxy
    simpa using this
  have h1 : (QuotientGroup.mk' (Q.subgroupOf C)) ⁅(⟨a, hPC ha⟩ : C), ⟨b, hPC hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hxy'
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  have e2 : ((⁅(⟨a, hPC ha⟩ : C), ⟨b, hPC hb⟩⁆ : C) : G) = ⁅a, b⁆ :=
    map_commutatorElement C.subtype _ _
  rwa [e2] at h1

end Ambient

end CFSG.LargeExtraspecial.S8
