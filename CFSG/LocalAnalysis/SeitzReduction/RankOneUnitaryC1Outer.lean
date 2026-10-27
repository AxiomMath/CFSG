module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Stage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_cartan_le_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ D : Subgroup G, D ≤ L ∧ D ≤ normalizer (szT₁ L T : Set G) ∧ szT₁ L T ⊓ D = ⊥ ∧
      (∀ y ∈ szT₁ L T, (∀ d ∈ D, y * d = d * y) → y = 1) ∧
      ∀ s ∈ T, ∃ n ∈ szT₁ L T, ∀ d ∈ D, (n⁻¹ * s) * d * (n⁻¹ * s)⁻¹ ∈ D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  obtain ⟨hT₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  set Dl := cartan (Q : Subgroup L) t₀ with hDl
  set Bl := borel (Q : Subgroup L) with hBl
  set D := Dl.map L.subtype with hD
  set B := Bl.map L.subtype with hBdef
  have hT₁ : (Q : Subgroup L).map L.subtype = szT₁ L T :=
    map_subtype_eq_of_mem_iff (szT₁_le_right L T) hmemQ
  have hmemB : ∀ x : G, x ∈ B ↔ x ∈ L ∧ x ∈ normalizer (szT₁ L T : Set G) := by
    intro x
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨l.2, mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
      · have hyL : y ∈ L := szT₁_le_right L T hy
        have := (mem_normalizer_iff.mp hl ⟨y, hyL⟩).mp ((hmemQ _).mpr hy)
        simpa using (hmemQ _).mp this
      · have hyL : y ∈ L := by
          have h1 : (l : G) * y * (l : G)⁻¹ ∈ L := szT₁_le_right L T hy
          have := mul_mem (mul_mem (inv_mem l.2) h1) l.2
          simpa [mul_assoc] using this
        have h1 : l * ⟨y, hyL⟩ * l⁻¹ ∈ (Q : Subgroup L) := (hmemQ _).mpr (by simpa using hy)
        exact (hmemQ _).mp ((mem_normalizer_iff.mp hl _).mpr h1)
    · rintro ⟨hxL, hxN⟩
      refine ⟨⟨x, hxL⟩, mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩, rfl⟩
      · have h1 := (mem_normalizer_iff.mp hxN y).mp ((hmemQ y).mp hy)
        exact (hmemQ _).mpr (by simpa using h1)
      · have h1 : x * (y : G) * x⁻¹ ∈ szT₁ L T := by simpa using (hmemQ _).mp hy
        exact (hmemQ y).mpr ((mem_normalizer_iff.mp hxN y).mpr h1)
  have hBN : B ≤ normalizer (szT₁ L T : Set G) := fun x hx => ((hmemB x).mp hx).2
  have hDB : D ≤ B := map_mono (cartan_le_borel _ _)
  have hT₁B : szT₁ L T ≤ B := fun y hy =>
    (hmemB y).mpr ⟨szT₁_le_right L T hy, Subgroup.le_normalizer hy⟩
  have hinf : szT₁ L T ⊓ D = ⊥ := by
    rw [← hT₁, hD, ← map_inf_eq _ _ _ L.subtype_injective, hc.inf_eq, Subgroup.map_bot]
  have hcardB : Nat.card B = Nat.card (szT₁ L T) * Nat.card D := by
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (cartan_le_borel (Q : Subgroup L) t₀)
    rw [inf_comm, hc.inf_eq, card_bot, mul_one, sup_comm, hc.sup_eq] at hprod
    have hBl' : Nat.card Bl = Nat.card (Q : Subgroup L) * Nat.card Dl := by
      rw [hBl, hDl, hprod, mul_comm]
    rw [hBdef, hD, card_map_of_injective L.subtype_injective,
      card_map_of_injective L.subtype_injective, ← hT₁,
      card_map_of_injective L.subtype_injective, hBl']
  have hDodd : Odd (Nat.card D) := by
    rw [hD, card_map_of_injective L.subtype_injective]
    exact hc.odd_card_cartan
  have hcop : Nat.Coprime (Nat.card (szT₁ L T)) (Nat.card D) := by
    rw [hT₁card, ← pow_mul]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hDodd)
  refine ⟨D, fun x hx => ((hmemB x).mp (hDB hx)).1, hDB.trans hBN, hinf, ?_, ?_⟩
  · intro y hy hyD
    have hyL : y ∈ L := szT₁_le_right L T hy
    set y' : L := ⟨y, hyL⟩ with hy'
    have hy'Q : y' ∈ (Q : Subgroup L) := (hmemQ y').mpr hy
    have hcomm : ∀ d ∈ Dl, d * y' = y' * d := fun d hd => Subtype.ext (by
      have := hyD (d : G) ⟨d, hd, rfl⟩
      simp only [coe_mul]
      exact this.symm)
    have hexists : ∀ z : L, ∃ z' ∈ rootCenter (Q : Subgroup L), z' ∉ ({1, z} : Set L) :=
      fun z => exists_mem_not_mem_of_ncard_lt (Set.toFinite _) (by
        rw [hc.card_center]
        calc ({1, z} : Set L).ncard ≤ ({z} : Set L).ncard + 1 := Set.ncard_insert_le 1 {z}
          _ = 2 := by rw [Set.ncard_singleton]
          _ < 2 ^ f := by omega)
    have hyZ : y' ∈ rootCenter (Q : Subgroup L) := by
      by_contra hyZ
      obtain ⟨z, hz, hz1⟩ := hexists 1
      obtain ⟨z', hz', hz'1⟩ := hexists z
      have hz1' : z ≠ 1 := fun h1 => hz1 (by simp [h1])
      have hz'1' : z' ≠ 1 := fun h1 => hz'1 (by simp [h1])
      have hz'z : z' ≠ z := fun h1 => hz'1 (by simp [h1])
      obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj hz hz1' hz' hz'1'
      have hd1 : d ≠ 1 := fun h1 => hz'z (by rw [hdz, h1]; group)
      exact hyZ (hB.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem hd hd1 hy'Q (by
        rw [hcomm d hd, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _))
    by_contra hy1
    have hy'1 : y' ≠ 1 := fun h1 => hy1 (congrArg Subtype.val h1)
    obtain ⟨z', hz', hz'1⟩ := hexists y'
    have hz'1' : z' ≠ 1 := fun h1 => hz'1 (by simp [h1])
    have hz'y : z' ≠ y' := fun h1 => hz'1 (by simp [h1])
    obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj hyZ hy'1 hz' hz'1'
    apply hz'y
    rw [hdz, mul_assoc, ← hcomm d hd, inv_mul_cancel_left]
  · intro s hs
    have hsL : s ∈ normalizer (L : Set G) := h.le_normalizer hs
    have hsT₁ := hTN₁ hs
    have hsB : ∀ x ∈ B, s * x * s⁻¹ ∈ B := by
      intro x hx
      obtain ⟨hxL, hxN⟩ := (hmemB x).mp hx
      exact (hmemB _).mpr ⟨(mem_normalizer_iff.mp hsL x).mp hxL,
        mul_mem (mul_mem hsT₁ hxN) (inv_mem hsT₁)⟩
    set Ds := D.map (MulAut.conj s).toMonoidHom with hDs
    have hDsB : Ds ≤ B := by
      rintro _ ⟨d, hd, rfl⟩
      exact hsB d (hDB hd)
    have hcardDs : Nat.card Ds = Nat.card D := card_map_of_injective (MulAut.conj s).injective
    set N := (szT₁ L T).subgroupOf B with hNdef
    set H := D.subgroupOf B with hHdef
    set K := Ds.subgroupOf B with hKdef
    have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hT₁B).mpr hBN
    have hcN : Nat.card N = Nat.card (szT₁ L T) :=
      Nat.card_congr (subgroupOfEquivOfLe hT₁B).toEquiv
    have hcH : Nat.card H = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv
    have hcK : Nat.card K = Nat.card D := by
      rw [← hcardDs]
      exact Nat.card_congr (subgroupOfEquivOfLe hDsB).toEquiv
    have hH : N.IsComplement' H :=
      isComplement'_of_coprime (by rw [hcN, hcH, ← hcardB]) (by rw [hcN, hcH]; exact hcop)
    have hK : N.IsComplement' K :=
      isComplement'_of_coprime (by rw [hcN, hcK, ← hcardB]) (by rw [hcN, hcK]; exact hcop)
    have hidx : N.index = Nat.card D := by
      have h1 := N.card_mul_index
      rw [hcN, hcardB] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    have hcop' : Nat.Coprime (Nat.card N) N.index := by rw [hcN, hidx]; exact hcop
    obtain ⟨n, hn⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      N H K hNn hH hK hcop'
    refine ⟨((n : B) : G), mem_subgroupOf.mp n.2, fun d hd => ?_⟩
    have h1 : (⟨s * d * s⁻¹, hDsB ⟨d, hd, rfl⟩⟩ : B) ∈ K := mem_subgroupOf.mpr ⟨d, hd, rfl⟩
    rw [hn] at h1
    obtain ⟨d', hd', hd'eq⟩ := h1
    have e := congrArg Subtype.val hd'eq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_mul, coe_inv] at e
    rw [show (((n : B) : G))⁻¹ * s * d * ((((n : B) : G))⁻¹ * s)⁻¹ =
      ((n : B) : G)⁻¹ * (s * d * s⁻¹) * ((n : B) : G) by group, ← e]
    simpa [mul_assoc] using mem_subgroupOf.mp hd'

theorem exists_sq_eq_t_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {s : G} (hs : s ∈ T)
    (hst : s ^ 2 * t ∈ szT₁ L T) (hsS : s ∉ szT₁ L T ⊔ zpowers t) :
    ∃ m ∈ T, m ^ 2 = t ∧ m ∉ szT₁ L T ⊔ zpowers t := by
  obtain ⟨D, hDL, hDN, hinf, hcent, hconj⟩ := h.exists_cartan_le_of_card_sylow hS2
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨n, hn, hnD⟩ := hconj s hs
  have hnT : n ∈ T := szT₁_le_left L T hn
  have hmT : n⁻¹ * s ∈ T := mul_mem (inv_mem hnT) hs
  have hmD : n⁻¹ * s ∈ normalizer (D : Set G) := by
    have hm' : (n⁻¹ * s)⁻¹ ∈ normalizer (D : Set G) :=
      mem_normalizer_of_forall_inv_mul_mul_mem fun d hd => by rw [inv_inv]; exact hnD d hd
    simpa using inv_mem hm'
  have htD : ∀ d ∈ D, t * d = d * t := fun d hd =>
    (mem_centralizer_iff.mp h.mem d (hDL hd)).symm
  have hy : (n⁻¹ * s) ^ 2 * t ∈ szT₁ L T := by
    have e : (n⁻¹ * s) ^ 2 * t = n⁻¹ * (s * n⁻¹ * s⁻¹) * (s ^ 2 * t) := by
      rw [sq, sq]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hn)
      ((mem_normalizer_iff.mp (hTN₁ hs) _).mp (inv_mem hn))) hst
  have hyD : ∀ d ∈ D, ((n⁻¹ * s) ^ 2 * t) * d = d * ((n⁻¹ * s) ^ 2 * t) := by
    intro d hd
    have h1 : ((n⁻¹ * s) ^ 2 * t) * d * ((n⁻¹ * s) ^ 2 * t)⁻¹ =
        (n⁻¹ * s) ^ 2 * d * ((n⁻¹ * s) ^ 2)⁻¹ := by
      calc ((n⁻¹ * s) ^ 2 * t) * d * ((n⁻¹ * s) ^ 2 * t)⁻¹ =
          (n⁻¹ * s) ^ 2 * (t * d) * t⁻¹ * ((n⁻¹ * s) ^ 2)⁻¹ := by group
        _ = (n⁻¹ * s) ^ 2 * d * ((n⁻¹ * s) ^ 2)⁻¹ := by rw [htD d hd]; group
    have hc : ((n⁻¹ * s) ^ 2 * t) * d * ((n⁻¹ * s) ^ 2 * t)⁻¹ * d⁻¹ ∈ szT₁ L T ⊓ D := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [show ((n⁻¹ * s) ^ 2 * t) * d * ((n⁻¹ * s) ^ 2 * t)⁻¹ * d⁻¹ =
          ((n⁻¹ * s) ^ 2 * t) * (d * ((n⁻¹ * s) ^ 2 * t)⁻¹ * d⁻¹) by group]
        exact mul_mem hy ((mem_normalizer_iff.mp (hDN hd) _).mp (inv_mem hy))
      · rw [h1]
        exact mul_mem ((mem_normalizer_iff.mp (pow_mem hmD 2) d).mp hd) (inv_mem hd)
    rw [hinf, mem_bot] at hc
    calc ((n⁻¹ * s) ^ 2 * t) * d =
        (((n⁻¹ * s) ^ 2 * t) * d * ((n⁻¹ * s) ^ 2 * t)⁻¹ * d⁻¹) * (d * ((n⁻¹ * s) ^ 2 * t)) := by
          group
      _ = d * ((n⁻¹ * s) ^ 2 * t) := by rw [hc, one_mul]
  have h1 : (n⁻¹ * s) ^ 2 * t = 1 := hcent _ hy hyD
  have htt : t * t = 1 := by rw [← sq]; exact h.sq_eq_one
  refine ⟨n⁻¹ * s, hmT, ?_, fun hmS => hsS ?_⟩
  · calc (n⁻¹ * s) ^ 2 = ((n⁻¹ * s) ^ 2 * t) * t⁻¹ := by group
      _ = t⁻¹ := by rw [h1, one_mul]
      _ = t := inv_eq_of_mul_eq_one_right htt
  · rw [show s = n * (n⁻¹ * s) by group]
    exact mul_mem (mem_sup_left hn) hmS

theorem conj_szA₁_of_sq_mem_centralizer_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {x : G} (hxT : x ∈ T) (hx2 : x ^ 2 ∈ centralizer (L : Set G))
    (hx : x ∉ szT₁ L T ⊔ zpowers t) : ∀ a ∈ szA₁ (szT₁ L T), x * a = a * x := by
  obtain ⟨-, -, -, hTN₁, -, -, hinner⟩ := h.start_of_card_sylow hS2
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  have hout : ¬ ∃ l ∈ L, ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹ := fun ⟨l, hl, hxl⟩ =>
    hx (hinner x hxT l hl hxl)
  set σ := L.normalizerMonoidHom ⟨x, h.le_normalizer hxT⟩ with hσdef
  have hσ : ∀ y : L, ((σ y : L) : G) = x * y * x⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hσ, hσ]
    have hxy : x * x * (y : G) = y * (x * x) := by
      rw [← sq]; exact (mem_centralizer_iff.mp hx2 y y.2).symm
    calc x * (x * (y : G) * x⁻¹) * x⁻¹ = (x * x * y) * (x * x)⁻¹ := by group
      _ = y := by rw [hxy]; group
  have hσout : ¬ ∃ g : L, ∀ y : L, σ y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hout ⟨g, g.2, fun y hy => ?_⟩
    have := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hσ] at this
    simpa using this
  have hσQ : ∀ y ∈ (Q : Subgroup L), σ y ∈ (Q : Subgroup L) := by
    intro y hy
    rw [hmemQ, hσ]
    exact (mem_normalizer_iff.mp (hTN₁ hxT) y).mp ((hmemQ y).mp hy)
  intro a ha
  have haL : a ∈ L := szT₁_le_right L T (szA₁_le _ ha)
  have h1 := (hB.fixed_iff_rootCenter_unitary Q σ hσσ hσout hσQ
    ((hmemQ ⟨a, haL⟩).mpr (szA₁_le _ ha))).mpr ((hmemZ ⟨a, haL⟩).mpr ha)
  have h2 := congrArg Subtype.val h1
  rw [hσ] at h2
  calc x * a = x * a * x⁻¹ * x := by group
    _ = a * x := by rw [h2]

end U3Start

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem conj_mul_inv_mem_szA₁_of_conj_szA₁ (hR : U3R2 G L T₁ R₂ t f)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {m : G} (hmR : ∀ r ∈ R₂, m * r * m⁻¹ ∈ R₂)
    (hmA : ∀ a ∈ szA₁ T₁, m * a = a * m) {r : G} (hr : r ∈ R₂) :
    m * r * m⁻¹ * r⁻¹ ∈ szA₁ T₁ := by
  have hr' := hmR r hr
  have hsq : (m * r * m⁻¹) ^ 2 = r ^ 2 := by
    have e : (m * r * m⁻¹) ^ 2 = m * r ^ 2 * m⁻¹ := by rw [sq, sq]; group
    rw [e, hmA _ (hR.sq_mem r hr), mul_inv_cancel_right]
  refine hR.mem_szA₁_of_sq_eq_one_of_inv hinv (mul_mem hr' (inv_mem hr)) ?_
  have hc : Commute (m * r * m⁻¹) r⁻¹ := hR.comm _ hr' _ (inv_mem hr)
  rw [hc.mul_pow, hsq, inv_pow, mul_inv_cancel]

theorem sq_comm_of_conj_szA₁ (hR : U3R2 G L T₁ R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    {m : G} (hmR : ∀ r ∈ R₂, m * r * m⁻¹ ∈ R₂) (hmA : ∀ a ∈ szA₁ T₁, m * a = a * m)
    {r : G} (hr : r ∈ R₂) : m ^ 2 * r = r * m ^ 2 := by
  have ha := hR.conj_mul_inv_mem_szA₁_of_conj_szA₁ hinv hmR hmA hr
  obtain ⟨a, haA, hm1⟩ : ∃ a ∈ szA₁ T₁, m * r * m⁻¹ = a * r := ⟨_, ha, by group⟩
  have hma : m * a * m⁻¹ = a := by rw [hmA a haA, mul_inv_cancel_right]
  have ha2 : a * a = 1 := by rw [← sq]; exact hR.sq_A₁ a haA
  have key : m ^ 2 * r * (m ^ 2)⁻¹ = r := by
    calc m ^ 2 * r * (m ^ 2)⁻¹ = m * (m * r * m⁻¹) * m⁻¹ := by rw [sq]; group
      _ = m * (a * r) * m⁻¹ := by rw [hm1]
      _ = (m * a * m⁻¹) * (m * r * m⁻¹) := by group
      _ = a * (a * r) := by rw [hma, hm1]
      _ = r := by rw [← mul_assoc, ha2, one_mul]
  calc m ^ 2 * r = (m ^ 2 * r * (m ^ 2)⁻¹) * m ^ 2 := by group
    _ = r * m ^ 2 := by rw [key]

end U3R2

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem false_of_sq_eq_t_of_inv (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) {m : G} (hmT : m ∈ T) (hm2 : m ^ 2 = t)
    (hmS : m ∉ szT₁ L T ⊔ zpowers t) (hmR : ∀ r ∈ R₂, m * r * m⁻¹ ∈ R₂) : False := by
  have hmA := h.conj_szA₁_of_sq_mem_centralizer_of_card_sylow hS2 hmT
    (by rw [hm2]; exact h.mem) hmS
  obtain ⟨r, hr, hr2⟩ := hne
  apply hr2
  have h1 : t * r = r * t := by rw [← hm2]; exact hR.sq_comm_of_conj_szA₁ hinv hmR hmA hr
  have h2 : r⁻¹ = r := by rw [← hinv r hr, h1, mul_inv_cancel_right]
  rw [sq]
  nth_rewrite 1 [← h2]
  exact inv_mul_cancel r

end U3Start

@[expose] def U3C1OuterNcycInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    (∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) → False

section Certificates

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem false_of_inv_of_no_outer_involution (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) (hT : ¬ T ≤ szT₁ L T ⊔ zpowers t)
    (hno : ∀ v ∈ T, v ^ 2 = 1 → v ∈ szT₁ L T ⊔ zpowers t) : False := by
  obtain ⟨x, hxT, hxS⟩ := IsConcreteLE.not_le_iff_exists.mp hT
  obtain ⟨j, hsS, hs2⟩ := StrongClosureMod.exists_pow_not_mem h.isPGroup hxT hxS
  have hsT : x ^ 2 ^ j ∈ T := pow_mem hxT _
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hs2
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
  · rw [hz1, mul_one] at hyz
    obtain ⟨v, hvT, hv2, hvS⟩ :=
      h.exists_outer_involution_of_card_sylow hS2 hsT (hyz ▸ hy) hsS
    exact hvS (hno v hvT hv2)
  · rw [hz1] at hyz
    have hst : (x ^ 2 ^ j) ^ 2 * t ∈ szT₁ L T := by
      rw [← hyz, mul_assoc, ← sq, h.sq_eq_one, mul_one]
      exact hy
    obtain ⟨m, hmT, hm2, hmS⟩ := h.exists_sq_eq_t_of_card_sylow hS2 hsT hst hsS
    have hTA := h.normalizer_le_normalizer_szA_of_card_sylow hS2
    obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
    have hmN : m ∈ normalizer (R₂ : Set G) := hNR (hTA (Subgroup.le_normalizer hmT))
    exact h.false_of_sq_eq_t_of_inv hS2 hR hinv hne hmT hm2 hmS fun r hr =>
      (mem_normalizer_iff.mp hmN r).mp hr

end U3Start

theorem u3C1OuterInput_of_ncyc (hN : U3C1OuterNcycInput) : U3C1OuterInput := by
  intro G _ _ L f t T R₂ h hS2 hR hinv hne hT
  by_cases hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t
  · exact hN G L f t T R₂ h hS2 hR hinv hne hv
  · exact h.false_of_inv_of_no_outer_involution hS2 hR hinv hne hT fun v hvT hv2 =>
      by_contra fun hvS => hv ⟨v, hvT, hv2, hvS⟩

end Certificates

end CFSG.SeitzReduction.RankOne
