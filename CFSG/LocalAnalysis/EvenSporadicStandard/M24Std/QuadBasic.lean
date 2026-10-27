module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Setting

public section

namespace CFSG.EvenSporadicStandard.M24Std

namespace Quad

open Subgroup

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {z : G}

theorem z_mul_self (hs : LocalSetting G L z) : z * z = 1 := by
  rw [← pow_two, ← hs.order_z, pow_orderOf_eq_one]

theorem z_inv (hs : LocalSetting G L z) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (z_mul_self hs)

theorem z_ne_one (hs : LocalSetting G L z) : z ≠ 1 := by
  intro h
  have := hs.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem z_not_mem (hs : LocalSetting G L z) : z ∉ L := by
  intro hz
  have : z ∈ L ⊓ zpowers z := ⟨hz, mem_zpowers z⟩
  rw [disjoint_iff.1 hs.disjoint] at this
  exact z_ne_one hs (mem_bot.1 this)

theorem comm_z (hs : LocalSetting G L z) {l : G} (hl : l ∈ L) : l * z = z * l :=
  mem_centralizer_iff.1 (hs.z_central (mem_zpowers z)) l hl

theorem exists_mem_L (hs : LocalSetting G L z) {q : G} (hq : q * z = z * q) :
    ∃ l ∈ L, q = l ∨ q = l * z := by
  have hq' : q ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact hq
  rw [hs.centralizer_eq] at hq'
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hs.z_central hq'
  rcases eq_one_or_eq_of_mul_self (z_mul_self hs) hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem mul_self_ne (hs : LocalSetting G L z) (g : G) : g * g ≠ z := by
  intro hg
  have hgc : g * z = z * g := by
    rw [← hg]
    group
  obtain ⟨l, hl, rfl | rfl⟩ := exists_mem_L hs hgc
  · exact z_not_mem hs (hg ▸ L.mul_mem hl hl)
  · apply z_not_mem hs
    have : z = l * l := by
      calc z = l * z * (l * z) := hg.symm
        _ = l * l * (z * z) := by
          rw [mul_assoc, ← mul_assoc z l z, ← comm_z hs hl]
          group
        _ = l * l := by rw [z_mul_self hs, mul_one]
    rw [this]
    exact L.mul_mem hl hl

theorem z_comm_A (hs : LocalSetting G L z) (hAL : A ≤ L) {a : G} (ha : a ∈ A) :
    z * a = a * z :=
  (comm_z hs (hAL ha)).symm

theorem mem_egV (hs : LocalSetting G L z) (hAL : A ≤ L) {x : G} (hx : x ∈ egV A z) :
    ∃ a ∈ A, x = a ∨ x = z * a := by
  have hle : zpowers z ≤ centralizer (A : Set G) := fun y hy =>
    mem_centralizer_iff.2 fun a ha => mem_centralizer_iff.1 (hs.z_central hy) a (hAL ha)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hx
  rcases eq_one_or_eq_of_mul_self (z_mul_self hs) hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr (comm_z hs (hAL ha))⟩

omit [Finite G] in
theorem z_mem_egV : z ∈ egV A z := mem_sup_right (mem_zpowers z)

omit [Finite G] in
theorem le_egV : A ≤ egV A z := le_sup_left

omit [Finite G] in
theorem z_mem_egM : z ∈ egM A z := le_normalizer z_mem_egV

theorem z_mem_lam (hs : LocalSetting G L z) (hAL : A ≤ L) : z ∈ egLam A z :=
  ⟨z_mem_egM, mem_centralizer_iff.2 fun _ ha => comm_z hs (hAL ha)⟩

omit [Finite G] in
theorem le_lam (hF : SextetFacts L A) : A ≤ egLam A z := fun a ha =>
  ⟨le_normalizer (le_egV ha), mem_centralizer_iff.2 fun h hh => hF.elem.1 h hh a ha⟩

omit [Finite G] in
theorem lam_comm {t : G} (ht : t ∈ egLam A z) {a : G} (ha : a ∈ A) : t * a = a * t :=
  ((mem_centralizer_iff.1 ht.2) a ha).symm

theorem tau_mem (hs : LocalSetting G L z) (hAL : A ≤ L) (hT : TranslationData A z) {t : G}
    (ht : t ∈ egLam A z) : z * t * z⁻¹ * t⁻¹ ∈ A := by
  obtain ⟨a, ha, h⟩ := hT.conj t ht.1
  have hza : z * a = a * z := z_comm_A hs hAL ha
  have : z * t * z⁻¹ * t⁻¹ = a⁻¹ := by
    calc z * t * z⁻¹ * t⁻¹ = z * (t * z * t⁻¹)⁻¹ := by group
      _ = z * (z * a)⁻¹ := by rw [h]
      _ = a⁻¹ := by rw [hza]; group
  rw [this]
  exact A.inv_mem ha

omit [Finite G] in
theorem comm_of_tau_eq_one {t : G} (h : z * t * z⁻¹ * t⁻¹ = 1) : z * t = t * z := by
  calc z * t = (z * t * z⁻¹ * t⁻¹) * (t * z) := by group
    _ = t * z := by rw [h, one_mul]

theorem ker_tau (hs : LocalSetting G L z) (hAL : A ≤ L) (hF : SextetFacts L A) {t : G}
    (ht : t ∈ egLam A z) (htz : z * t = t * z) : t ∈ A ∨ z * t ∈ A := by
  obtain ⟨l, hl, rfl | rfl⟩ := exists_mem_L hs htz.symm
  · left
    exact hF.cent _ hl fun a ha => lam_comm ht ha
  · right
    have hlc : ∀ a ∈ A, l * a = a * l := by
      intro a ha
      have h1 : l * z * a = a * (l * z) := lam_comm ht ha
      have h2 : z * a = a * z := z_comm_A hs hAL ha
      have : l * a * z = a * l * z := by
        calc l * a * z = l * (a * z) := by group
          _ = l * (z * a) := by rw [h2]
          _ = l * z * a := by group
          _ = a * (l * z) := h1
          _ = a * l * z := by group
      exact mul_right_cancel this
    have hzl : z * (l * z) = l := by
      rw [← mul_assoc, ← comm_z hs hl, mul_assoc, z_mul_self hs, mul_one]
    rw [hzl]
    exact hF.cent l hl hlc

theorem surj_tau (hs : LocalSetting G L z) (hAL : A ≤ L) (hT : TranslationData A z) {a : G}
    (ha : a ∈ A) : ∃ t ∈ egLam A z, z * t * z⁻¹ * t⁻¹ = a := by
  obtain ⟨t, ht, h⟩ := hT.trans a⁻¹ (A.inv_mem ha)
  refine ⟨t, ht, ?_⟩
  have hza : z * a⁻¹ = a⁻¹ * z := z_comm_A hs hAL (A.inv_mem ha)
  calc z * t * z⁻¹ * t⁻¹ = z * (t * z * t⁻¹)⁻¹ := by group
    _ = z * (z * a⁻¹)⁻¹ := by rw [h]
    _ = a := by rw [hza]; group

theorem tau_mul (hs : LocalSetting G L z) (hAL : A ≤ L) (hT : TranslationData A z) {s t : G}
    (hs' : s ∈ egLam A z) (ht : t ∈ egLam A z) :
    z * (s * t) * z⁻¹ * (s * t)⁻¹ = (z * s * z⁻¹ * s⁻¹) * (z * t * z⁻¹ * t⁻¹) := by
  have h := lam_comm hs' (tau_mem hs hAL hT ht)
  calc z * (s * t) * z⁻¹ * (s * t)⁻¹
        = (z * s * z⁻¹ * s⁻¹) * (s * (z * t * z⁻¹ * t⁻¹)) * s⁻¹ := by group
    _ = (z * s * z⁻¹ * s⁻¹) * (z * t * z⁻¹ * t⁻¹) := by rw [h]; group

theorem nl_comm_z (hs : LocalSetting G L z) {n : G} (hn : n ∈ egNL L A) : n * z = z * n :=
  comm_z hs hn.2

omit [Finite G] in
theorem nl_conj_mem {n : G} (hn : n ∈ egNL L A) {a : G} (ha : a ∈ A) : n * a * n⁻¹ ∈ A :=
  (mem_normalizer_iff.1 hn.1 a).1 ha

theorem nl_le_egM (hs : LocalSetting G L z) (hAL : A ≤ L) {n : G} (hn : n ∈ egNL L A) :
    n ∈ egM A z := by
  have key : ∀ g ∈ egNL L A, ∀ h ∈ egV A z, g * h * g⁻¹ ∈ egV A z := by
    intro g hg h hh
    obtain ⟨a, ha, rfl | rfl⟩ := mem_egV hs hAL hh
    · exact le_egV (nl_conj_mem hg ha)
    · have : g * (z * a) * g⁻¹ = z * (g * a * g⁻¹) := by
        rw [← mul_assoc g z a, nl_comm_z hs hg]
        group
      rw [this]
      exact (egV A z).mul_mem z_mem_egV (le_egV (nl_conj_mem hg ha))
  refine mem_normalizer_iff.2 fun h => ⟨key n hn h, fun hh => ?_⟩
  have := key n⁻¹ ((egNL L A).inv_mem hn) _ hh
  simpa [mul_assoc] using this

theorem conj_mem_lam (hs : LocalSetting G L z) (hAL : A ≤ L) {n : G} (hn : n ∈ egNL L A)
    {t : G} (ht : t ∈ egLam A z) : n * t * n⁻¹ ∈ egLam A z := by
  have hnM := nl_le_egM hs hAL hn
  refine ⟨(egM A z).mul_mem ((egM A z).mul_mem hnM ht.1) ((egM A z).inv_mem hnM), ?_⟩
  refine mem_centralizer_iff.2 fun a ha => ?_
  have hb : n⁻¹ * a * n ∈ A := by
    have := nl_conj_mem ((egNL L A).inv_mem hn) ha
    simpa using this
  have h1 := lam_comm ht hb
  calc a * (n * t * n⁻¹) = n * ((n⁻¹ * a * n) * t) * n⁻¹ := by group
    _ = n * (t * (n⁻¹ * a * n)) * n⁻¹ := by rw [h1]
    _ = n * t * n⁻¹ * a := by group

omit [Finite G] in
theorem tau_conj {g t : G} (hg : g * z = z * g) :
    z * (g * t * g⁻¹) * z⁻¹ * (g * t * g⁻¹)⁻¹ = g * (z * t * z⁻¹ * t⁻¹) * g⁻¹ := by
  calc z * (g * t * g⁻¹) * z⁻¹ * (g * t * g⁻¹)⁻¹
        = (z * g) * t * (z * g)⁻¹ * (g * t⁻¹ * g⁻¹) := by group
    _ = (g * z) * t * (g * z)⁻¹ * (g * t⁻¹ * g⁻¹) := by rw [← hg]
    _ = g * (z * t * z⁻¹ * t⁻¹) * g⁻¹ := by group

theorem conj_mem_A (hs : LocalSetting G L z) (hAL : A ≤ L) {l : G} (hlM : l ∈ egM A z)
    (hlL : l ∈ L) {a : G} (ha : a ∈ A) : l * a * l⁻¹ ∈ A := by
  have hV : l * a * l⁻¹ ∈ egV A z := (mem_normalizer_iff.1 hlM a).1 (le_egV ha)
  have hL : l * a * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hlL (hAL ha)) (L.inv_mem hlL)
  obtain ⟨b, hb, h | h⟩ := mem_egV hs hAL hV
  · rw [h]
    exact hb
  · exfalso
    apply z_not_mem hs
    have : z = (l * a * l⁻¹) * b⁻¹ := by rw [h]; group
    rw [this]
    exact L.mul_mem hL (L.inv_mem (hAL hb))

theorem exists_decomp (hs : LocalSetting G L z) (hAL : A ≤ L) (hT : TranslationData A z)
    {m : G} (hm : m ∈ egM A z) :
    ∃ t ∈ egLam A z, ∃ l ∈ egNL L A, m = t * l ∨ m = t * l * z := by
  obtain ⟨a, ha, hma⟩ := hT.conj m hm
  obtain ⟨t, ht, hta⟩ := hT.trans a ha
  have hc : (t⁻¹ * m) * z = z * (t⁻¹ * m) := by
    calc (t⁻¹ * m) * z = t⁻¹ * (m * z * m⁻¹) * m := by group
      _ = t⁻¹ * (t * z * t⁻¹) * m := by rw [hma, hta]
      _ = z * (t⁻¹ * m) := by group
  have hlN : ∀ l ∈ L, l ∈ egM A z → l ∈ egNL L A := by
    intro l hlL hlM
    refine ⟨mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem_A hs hAL hlM hlL hh, ?_⟩, hlL⟩
    intro hh
    have := conj_mem_A hs hAL ((egM A z).inv_mem hlM) (L.inv_mem hlL) hh
    simpa [mul_assoc] using this
  have htM : t⁻¹ ∈ egM A z := (egM A z).inv_mem ht.1
  obtain ⟨l, hl, h | h⟩ := exists_mem_L hs hc
  · refine ⟨t, ht, l, hlN l hl ?_, Or.inl ?_⟩
    · rw [← h]
      exact (egM A z).mul_mem htM hm
    · rw [← h]
      group
  · refine ⟨t, ht, l, hlN l hl ?_, Or.inr ?_⟩
    · have : l = t⁻¹ * m * z⁻¹ := by rw [h]; group
      rw [this]
      exact (egM A z).mul_mem ((egM A z).mul_mem htM hm) ((egM A z).inv_mem z_mem_egM)
    · rw [mul_assoc t l z, ← h]
      group

theorem sq_mem (hs : LocalSetting G L z) (hAL : A ≤ L) (hF : SextetFacts L A)
    (hT : TranslationData A z) {s : G} (hs' : s ∈ egLam A z) : s * s ∈ A := by
  have hx := tau_mem hs hAL hT hs'
  have h1 : z * (s * s) * z⁻¹ * (s * s)⁻¹ = 1 := by
    rw [tau_mul hs hAL hT hs' hs']
    exact hF.elem.2 _ hx
  rcases ker_tau hs hAL hF ((egLam A z).mul_mem hs' hs') (comm_of_tau_eq_one h1) with h | h
  · exact h
  · exfalso
    obtain ⟨t, -, ht⟩ := hT.trans _ h
    apply mul_self_ne hs (t⁻¹ * s * t)
    have hss : s * s = z * (z * (s * s)) := by rw [← mul_assoc, z_mul_self hs, one_mul]
    calc t⁻¹ * s * t * (t⁻¹ * s * t) = t⁻¹ * (s * s) * t := by group
      _ = t⁻¹ * (z * (z * (s * s))) * t := by rw [← hss]
      _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [ht]
      _ = z := by group

theorem comm_mem (hs : LocalSetting G L z) (hAL : A ≤ L) (hF : SextetFacts L A)
    (hT : TranslationData A z) {s t : G} (hs' : s ∈ egLam A z) (ht : t ∈ egLam A z) :
    s * t * s⁻¹ * t⁻¹ ∈ A := by
  have h1 := sq_mem hs hAL hF hT ((egLam A z).mul_mem hs' ht)
  have h2 := sq_mem hs hAL hF hT hs'
  have h3 := sq_mem hs hAL hF hT ht
  have hc : t * (s * s) = (s * s) * t := lam_comm ht h2
  have hc' : t⁻¹ * (s * s)⁻¹ = (s * s)⁻¹ * t⁻¹ := by
    rw [← mul_inv_rev, ← hc, mul_inv_rev]
  have e : s * t * s⁻¹ * t⁻¹ = (s * t) * (s * t) * (s * s)⁻¹ * (t * t)⁻¹ := by
    calc s * t * s⁻¹ * t⁻¹ = (s * t) * (s * t) * (t⁻¹ * (s * s)⁻¹) * t⁻¹ := by group
      _ = (s * t) * (s * t) * ((s * s)⁻¹ * t⁻¹) * t⁻¹ := by rw [hc']
      _ = (s * t) * (s * t) * (s * s)⁻¹ * (t * t)⁻¹ := by group
  rw [e]
  exact A.mul_mem (A.mul_mem h1 (A.inv_mem h2)) (A.inv_mem h3)

end Quad

end CFSG.EvenSporadicStandard.M24Std
