module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransSylow

public section

namespace CFSG.EvenSporadicStandard.M24Std.Trans

open Subgroup

variable {G : Type} [Group G] {L A : Subgroup G} {z : G}

theorem lam_mem_M {t : G} (ht : t ∈ egLam A z) : t ∈ egM A z := (mem_inf.1 ht).1

theorem lam_comm {t a : G} (ht : t ∈ egLam A z) (ha : a ∈ A) : t * a = a * t :=
  ((mem_centralizer_iff.1 (mem_inf.1 ht).2) a ha).symm

theorem eq_one_of_mul_self_of_pow_five {u : G} (h2 : u * u = 1) (h5 : u ^ 5 = 1) : u = 1 := by
  calc u = u ^ 5 * (u * u)⁻¹ * (u * u)⁻¹ := by group
    _ = 1 := by rw [h5, h2]; group

variable [Finite G]

section Main

variable (hs : LocalSetting G L z) (hAL : A ≤ L) (hF : SextetFacts L A)
  (hcase : ¬ egM A z ≤ centralizer ({z} : Set G))
include hs hAL hF hcase

theorem conj_mem_A {m a : G} (hm : m ∈ egM A z) (ha : a ∈ A) : m * a * m⁻¹ ∈ A := by
  obtain ⟨n, hn, hna⟩ := exists_conj_eq hs hAL hF hcase a ha
  obtain ⟨a₁, ha₁, h₁⟩ := conj_eq hs hAL hm
  obtain ⟨a₂, ha₂, h₂⟩ := conj_eq hs hAL (mul_mem hm hn)
  have ha' : a = z * (n * z * n⁻¹) := by
    rw [hna, ← mul_assoc, mul_self_z hs, one_mul]
  have e1 : m * a * m⁻¹ = (m * z * m⁻¹) * ((m * n) * z * (m * n)⁻¹) := by
    rw [ha']
    group
  have e2 : z * a₁ * (z * a₂) = a₁ * a₂ := by
    calc z * a₁ * (z * a₂) = z * (a₁ * z) * a₂ := by group
      _ = z * (z * a₁) * a₂ := by rw [comm_z hs (hAL ha₁)]
      _ = (z * z) * a₁ * a₂ := by group
      _ = a₁ * a₂ := by rw [mul_self_z hs, one_mul]
  rw [e1, h₁, h₂, e2]
  exact mul_mem ha₁ ha₂

theorem M_le_normalizer_A : egM A z ≤ normalizer (A : Set G) := fun m hm =>
  mem_normalizer_iff.2 fun a => ⟨conj_mem_A hs hAL hF hcase hm, fun h => by
    have := conj_mem_A hs hAL hF hcase (inv_mem hm) h
    rwa [show m⁻¹ * (m * a * m⁻¹) * m⁻¹⁻¹ = a by group] at this⟩

omit hcase in
theorem trans_of_exists (hne : ∃ t ∈ egLam A z, t * z ≠ z * t) :
    ∀ a ∈ A, ∃ t ∈ egLam A z, t * z * t⁻¹ = z * a := by
  set T : Set G := {a | a ∈ A ∧ ∃ t ∈ egLam A z, t * z * t⁻¹ = z * a} with hTdef
  have hTA : T ⊆ A := fun a ha => ha.1
  have h1 : (1 : G) ∈ T := ⟨one_mem A, 1, one_mem _, by group⟩
  have hmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := by
    rintro a ⟨ha, t₁, ht₁, h₁⟩ b ⟨hb, t₂, ht₂, h₂⟩
    refine ⟨mul_mem ha hb, t₁ * t₂, mul_mem ht₁ ht₂, ?_⟩
    have hc : t₁ * b = b * t₁ := lam_comm ht₁ hb
    calc t₁ * t₂ * z * (t₁ * t₂)⁻¹ = t₁ * (t₂ * z * t₂⁻¹) * t₁⁻¹ := by group
      _ = t₁ * z * b * t₁⁻¹ := by rw [h₂]; group
      _ = t₁ * z * t₁⁻¹ * (t₁ * b * t₁⁻¹) := by group
      _ = z * (a * b) := by rw [h₁, hc]; group
  have hinv : ∀ n ∈ egNL L A, ∀ a ∈ T, n * a * n⁻¹ ∈ T := by
    rintro n hn a ⟨ha, t, ht, hta⟩
    have hnA := NL_normalizes hn
    have hnM := mem_M_of_mem_NL hs hAL hn
    refine ⟨(mem_normalizer_iff.1 hnA a).1 ha, n * t * n⁻¹,
      mem_inf.2 ⟨mul_mem (mul_mem hnM (lam_mem_M ht)) (inv_mem hnM), ?_⟩, ?_⟩
    · rw [mem_centralizer_iff]
      intro b hb
      have hb' : n⁻¹ * b * n ∈ A := by
        have := (mem_normalizer_iff.1 (inv_mem hnA) b).1 hb
        rwa [inv_inv] at this
      have hc := lam_comm ht hb'
      calc b * (n * t * n⁻¹) = n * ((n⁻¹ * b * n) * t) * n⁻¹ := by group
        _ = n * (t * (n⁻¹ * b * n)) * n⁻¹ := by rw [hc]
        _ = n * t * n⁻¹ * b := by group
    · have hnz : n * z = z * n := comm_z hs (NL_mem hn)
      have hz' : n⁻¹ * z * n = z := by rw [mul_assoc, ← hnz]; group
      calc n * t * n⁻¹ * z * (n * t * n⁻¹)⁻¹ = n * t * (n⁻¹ * z * n) * t⁻¹ * n⁻¹ := by group
        _ = n * (t * z * t⁻¹) * n⁻¹ := by rw [hz']; group
        _ = n * (z * a) * n⁻¹ := by rw [hta]
        _ = z * (n * a * n⁻¹) := by rw [← mul_assoc n z a, hnz]; group
  have hsinv : ∀ a ∈ T, a⁻¹ ∈ T := by
    intro a ha
    rw [inv_eq_of_mul_eq_one_right (hF.elem.2 a ha.1)]
    exact ha
  let Ts : Subgroup G :=
    { carrier := T
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := h1
      inv_mem' := fun {a} ha => hsinv a ha }
  have hTs : Ts ≤ A := fun a ha => hTA ha
  have hdvd : T.ncard ∣ 64 := by
    rw [← hF.card_A, ← Nat.card_coe_set_eq]
    exact Subgroup.card_dvd_of_le hTs
  rcases invariant_cases hF T hTA h1 hinv with hT | hT | hT | hT
  · exfalso
    obtain ⟨t, ht, htz⟩ := hne
    obtain ⟨a, ha, hta⟩ := conj_eq hs hAL (lam_mem_M ht)
    have haT : a ∈ T := ⟨ha, t, ht, hta⟩
    rw [hT, Set.mem_singleton_iff] at haT
    rw [haT, mul_one] at hta
    apply htz
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [hta]
  · rw [hT] at hdvd
    exact absurd hdvd (by decide)
  · rw [hT] at hdvd
    exact absurd hdvd (by decide)
  · intro a ha
    obtain ⟨-, t, ht, hta⟩ := hT ha
    exact ⟨t, ht, hta⟩

theorem exists_lam_not_comm
    (hpure : ∀ (S : Subgroup G) (r : G), r ∈ normalizer (A : Set G) → orderOf r = 5 →
      Nat.card {a : A | r * (a : G) * r⁻¹ = a} = 4 → IsPGroup 2 S →
      S ≤ normalizer (A : Set G) → S ≤ normalizer (zpowers r : Set G) →
      Nat.card S ≤ 8 * Nat.card (S ⊓ centralizer (A : Set G) : Subgroup G)) :
    ∃ t ∈ egLam A z, t * z ≠ z * t := by
  by_contra H
  push Not at H
  obtain ⟨r, hrN, hr5, hfix, Q, hQN, hQr, hQ⟩ := hF.five
  have hrL : r ∈ L := NL_mem hrN
  have hrM : r ∈ egM A z := mem_M_of_mem_NL hs hAL hrN
  have hrz : r * z = z * r := comm_z hs hrL
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Cs : Set G := {c | c ∈ A ∧ r * c * r⁻¹ = c} with hCs
  have hCs4 : Cs.ncard = 4 := by
    have : Cs = Subtype.val '' {a : A | r * (a : G) * r⁻¹ = a} := by
      ext x
      constructor
      · rintro ⟨hx, hrx⟩
        exact ⟨⟨x, hx⟩, hrx, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, ha⟩
    rw [this, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq, hfix]
  have hPz : ∀ w ∈ zpowers r, w * z = z * w := by
    intro w hw
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    exact Commute.zpow_left hrz j
  set K : Subgroup G := egM A z ⊓ normalizer (zpowers r : Set G) with hK
  have horbit : {x | ∃ k ∈ K, x = k * z * k⁻¹} = (fun c => z * c) '' Cs := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hkM, hkP⟩ := mem_inf.1 hk
      obtain ⟨a, ha, hka⟩ := conj_eq hs hAL hkM
      refine ⟨a, ⟨ha, ?_⟩, hka.symm⟩
      have hw : k⁻¹ * r * k ∈ zpowers r := by
        have := (mem_normalizer_iff.1 (inv_mem hkP) r).1 (mem_zpowers r)
        rwa [inv_inv] at this
      have hc := hPz _ hw
      have h3 : r * (k * z * k⁻¹) = k * z * k⁻¹ * r := by
        calc r * (k * z * k⁻¹) = k * ((k⁻¹ * r * k) * z) * k⁻¹ := by group
          _ = k * (z * (k⁻¹ * r * k)) * k⁻¹ := by rw [hc]
          _ = k * z * k⁻¹ * r := by group
      rw [hka] at h3
      have h4 : z * (r * a) = z * (a * r) := by
        calc z * (r * a) = r * z * a := by rw [hrz]; group
          _ = r * (z * a) := by group
          _ = z * a * r := h3
          _ = z * (a * r) := by group
      rw [mul_left_cancel h4]
      group
    · rintro ⟨c, ⟨hc, hrc⟩, rfl⟩
      obtain ⟨m, hm, hmz⟩ := exists_conj_eq hs hAL hF hcase c hc
      have hrc' : r * c = c * r := by
        calc r * c = r * c * r⁻¹ * r := by group
          _ = c * r := by rw [hrc]
      have hzc : r * (z * c) = z * c * r := by
        calc r * (z * c) = r * z * c := by group
          _ = z * (r * c) := by rw [hrz]; group
          _ = z * (c * r) := by rw [hrc']
          _ = z * c * r := by group
      have hr'z : m⁻¹ * r * m * z = z * (m⁻¹ * r * m) := by
        calc m⁻¹ * r * m * z = m⁻¹ * (r * (m * z * m⁻¹)) * m := by group
          _ = m⁻¹ * ((m * z * m⁻¹) * r) * m := by rw [hmz, hzc]
          _ = z * (m⁻¹ * r * m) := by group
      have hr'M : m⁻¹ * r * m ∈ egM A z := mul_mem (mul_mem (inv_mem hm) hrM) hm
      have hr'o : orderOf (m⁻¹ * r * m) = 5 := by
        have := (MulAut.conj m⁻¹).orderOf_eq r
        simp only [MulAut.conj_apply, inv_inv] at this
        rw [this, hr5]
      have hr'L : m⁻¹ * r * m ∈ L := by
        have hg : m⁻¹ * r * m ∈ centralizer ({z} : Set G) :=
          mem_centralizer_singleton_iff.2 hr'z
        rw [hs.centralizer_eq] at hg
        obtain ⟨l, hl, b, hb, hlb⟩ := exists_mul_of_mem_sup_of_le_centralizer hs.z_central hg
        rcases eq_one_or_eq_of_mul_self (mul_self_z hs) hb with hb1 | hbz
        · rw [hlb, hb1, mul_one]
          exact hl
        · exfalso
          have h5 : (m⁻¹ * r * m) ^ 5 = 1 := by rw [← hr'o]; exact pow_orderOf_eq_one _
          rw [hlb, hbz, Commute.mul_pow (comm_z hs hl) 5] at h5
          have hz5 : z ^ 5 = z := by
            have h2 : z ^ 2 = 1 := by rw [pow_two]; exact mul_self_z hs
            calc z ^ 5 = (z ^ 2) ^ 2 * z := by rw [← pow_mul, ← pow_succ]
              _ = z := by rw [h2, one_pow, one_mul]
          rw [hz5] at h5
          apply z_not_mem hs
          rw [eq_inv_of_mul_eq_one_right h5]
          exact L.inv_mem (L.pow_mem hl 5)
      have hr'N : m⁻¹ * r * m ∈ egNL L A := mem_NL_of_mem_M hs hAL hr'M hr'L
      obtain ⟨d, hd, hdr⟩ := exists_conj_mem_zpowers (not_dvd_card_NL hs) hrN hr'N hr5 hr'o
      refine ⟨m * d⁻¹, mem_inf.2 ⟨mul_mem hm (inv_mem (mem_M_of_mem_NL hs hAL hd)), ?_⟩, ?_⟩
      · have h6 : (m * d⁻¹)⁻¹ * r * (m * d⁻¹)⁻¹⁻¹ ∈ zpowers r := by
          have : (m * d⁻¹)⁻¹ * r * (m * d⁻¹)⁻¹⁻¹ = d * (m⁻¹ * r * m) * d⁻¹ := by group
          rw [this]
          exact hdr
        have := inv_mem (mem_normalizer_zpowers h6)
        rwa [inv_inv] at this
      · have hdz : d⁻¹ * z = z * d⁻¹ := comm_z hs (L.inv_mem (NL_mem hd))
        calc z * c = m * z * m⁻¹ := hmz.symm
          _ = m * d⁻¹ * z * (m * d⁻¹)⁻¹ := by rw [mul_assoc m d⁻¹ z, hdz]; group
  have hKc := J4Std.card_inf_centralizer_mul_ncard K z
  rw [horbit, Set.ncard_image_of_injective _ (mul_right_injective z), hCs4] at hKc
  have hzr : z * r * z⁻¹ ∈ zpowers r := by
    rw [show z * r * z⁻¹ = r by rw [← hrz]; group]
    exact mem_zpowers r
  have hzK : z ∈ K := mem_inf.2 ⟨mem_M_of_mem_V z_mem_V, mem_normalizer_zpowers hzr⟩
  have hQK : Q ≤ K ⊓ centralizer ({z} : Set G) := fun q hq =>
    mem_inf.2 ⟨mem_inf.2 ⟨mem_M_of_mem_NL hs hAL (hQN hq), hQr hq⟩,
      mem_centralizer_singleton_iff.2 (comm_z hs (NL_mem (hQN hq)))⟩
  have hzKC : zpowers z ≤ K ⊓ centralizer ({z} : Set G) :=
    zpowers_le.2 (mem_inf.2 ⟨hzK, mem_centralizer_singleton_iff.2 rfl⟩)
  have hQz : Nat.card (Q ⊔ zpowers z : Subgroup G) = 32 := by
    have hQL : Q ≤ L := fun q hq => NL_mem (hQN hq)
    have e := mulEquivProdSup (hs.z_central.trans (centralizer_le (SetLike.coe_subset_coe.2 hQL)))
      (hs.disjoint.mono_left hQL)
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, hs.order_z, hQ]
  have h32 : 32 ∣ Nat.card (K ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    rw [← hQz]
    exact Subgroup.card_dvd_of_le (sup_le hQK hzKC)
  have h128 : 2 ^ 7 ∣ Nat.card K := by
    rw [← hKc]
    obtain ⟨j, hj⟩ := h32
    rw [hj]
    exact ⟨j, by ring⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := Sylow.exists_subgroup_card_pow_prime 2 h128
  have hSc : Nat.card (S'.map K.subtype) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hS']
  have hSK : S'.map K.subtype ≤ K := Subgroup.map_subtype_le S'
  have hSA : S'.map K.subtype ≤ normalizer (A : Set G) := fun s hs' =>
    M_le_normalizer_A hs hAL hF hcase (mem_inf.1 (hSK hs')).1
  have hSr : S'.map K.subtype ≤ normalizer (zpowers r : Set G) := fun s hs' =>
    (mem_inf.1 (hSK hs')).2
  have hb := hpure _ r (NL_normalizes hrN) hr5 hfix (IsPGroup.of_card hSc) hSA hSr
  have hsub : ((S'.map K.subtype ⊓ centralizer (A : Set G) : Subgroup G) : Set G) ⊆
      Cs ∪ (fun c => c * z) '' Cs := by
    intro t ht
    obtain ⟨htS, htC⟩ := mem_inf.1 ht
    obtain ⟨htM, htP⟩ := mem_inf.1 (hSK htS)
    have htL : t ∈ egLam A z := mem_inf.2 ⟨htM, htC⟩
    have htV : t ∈ egV A z := mem_V_of_comm hs hAL hF.cent (H t htL) fun a ha => lam_comm htL ha
    have hu1 : t * r * t⁻¹ * r⁻¹ = 1 := by
      have huV : t * r * t⁻¹ * r⁻¹ ∈ egV A z := by
        have h1 : r * t⁻¹ * r⁻¹ ∈ egV A z := (mem_normalizer_iff.1 hrM t⁻¹).1 (inv_mem htV)
        rw [show t * r * t⁻¹ * r⁻¹ = t * (r * t⁻¹ * r⁻¹) by group]
        exact mul_mem htV h1
      have huP : t * r * t⁻¹ * r⁻¹ ∈ zpowers r :=
        mul_mem ((mem_normalizer_iff.1 htP r).1 (mem_zpowers r)) (inv_mem (mem_zpowers r))
      have hdvd5 : orderOf (t * r * t⁻¹ * r⁻¹) ∣ 5 := hr5 ▸ orderOf_dvd_of_mem_zpowers huP
      exact eq_one_of_mul_self_of_pow_five (mul_self_of_mem_V hs hAL hF.elem huV)
        (orderOf_dvd_iff_pow_eq_one.1 hdvd5)
    have htr : t * r = r * t := by
      calc t * r = t * r * t⁻¹ * r⁻¹ * (r * t) := by group
        _ = r * t := by rw [hu1, one_mul]
    obtain ⟨a, ha, h | h⟩ := mem_V hs hAL htV
    · refine Or.inl ⟨by rw [h]; exact ha, ?_⟩
      calc r * t * r⁻¹ = t * r * r⁻¹ := by rw [htr]
        _ = t := by group
    · refine Or.inr ⟨a, ⟨ha, ?_⟩, h.symm⟩
      rw [h] at htr
      have h7 : a * r * z = r * a * z := by
        calc a * r * z = a * (r * z) := by group
          _ = a * (z * r) := by rw [hrz]
          _ = a * z * r := by group
          _ = r * (a * z) := htr
          _ = r * a * z := by group
      rw [← mul_right_cancel h7]
      group
  have hcard8 : Nat.card (S'.map K.subtype ⊓ centralizer (A : Set G) : Subgroup G) ≤ 8 := by
    calc Nat.card (S'.map K.subtype ⊓ centralizer (A : Set G) : Subgroup G)
        = ((S'.map K.subtype ⊓ centralizer (A : Set G) : Subgroup G) : Set G).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ (Cs ∪ (fun c => c * z) '' Cs).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Cs.ncard + ((fun c => c * z) '' Cs).ncard := Set.ncard_union_le _ _
      _ = 8 := by rw [Set.ncard_image_of_injective _ (mul_left_injective z), hCs4]
  rw [hSc] at hb
  have h64 : 2 ^ 7 ≤ 8 * 8 := le_trans hb (Nat.mul_le_mul_left 8 hcard8)
  norm_num at h64

theorem translationData_of_facts
    (hpure : ∀ (S : Subgroup G) (r : G), r ∈ normalizer (A : Set G) → orderOf r = 5 →
      Nat.card {a : A | r * (a : G) * r⁻¹ = a} = 4 → IsPGroup 2 S →
      S ≤ normalizer (A : Set G) → S ≤ normalizer (zpowers r : Set G) →
      Nat.card S ≤ 8 * Nat.card (S ⊓ centralizer (A : Set G) : Subgroup G)) :
    TranslationData A z :=
  ⟨fun _ hm => conj_eq hs hAL hm,
    trans_of_exists hs hAL hF (exists_lam_not_comm hs hAL hF hcase hpure)⟩

end Main

end CFSG.EvenSporadicStandard.M24Std.Trans
