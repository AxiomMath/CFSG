module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69Def

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem d8_exists : ∀ c d : DihedralGroup 4, (∀ x, x * c = c * x) → c * c = 1 → c ≠ 1 →
    d * d = 1 → d ≠ 1 → d ≠ c →
    ∃ a : DihedralGroup 4, a * a = 1 ∧ a * d = c * (d * a) ∧ a ≠ 1 ∧ a ≠ c ∧ a ≠ d ∧
      a ≠ d * c ∧ a * d ≠ 1 ∧ a * d ≠ c ∧ a * d ≠ d ∧ a * d ≠ d * c ∧ a * d ≠ a ∧
      a * d ≠ a * c := by
  decide

theorem d8_list : ∀ c d a : DihedralGroup 4, (∀ x, x * c = c * x) → c * c = 1 → c ≠ 1 →
    d * d = 1 → d ≠ 1 → d ≠ c → a * a = 1 → a * d = c * (d * a) →
    ∀ s : DihedralGroup 4, s = 1 ∨ s = c ∨ s = d ∨ s = d * c ∨ s = a ∨ s = a * c ∨
        s = a * d ∨ s = a * d * c := by
  decide

theorem d8_comm : ∀ c : DihedralGroup 4, (∀ x, x * c = c * x) → c * c = 1 → c ≠ 1 →
    ∀ a b : DihedralGroup 4, a * b = b * a ∨ a * b = c * (b * a) := by
  decide


theorem d8_center : ∀ c : DihedralGroup 4, (∀ x, x * c = c * x) → c * c = 1 → c ≠ 1 →
    ∀ x : DihedralGroup 4, (∀ y, y * x = x * y) → x = 1 ∨ x = c := by
  decide

structure Hyp69 {G : Type} [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G) (S : Subgroup G) : Prop where
  conf : Rest6Config L z t T₀ E Q x β B
  wf : WFacts L t E
  ef : EFacts69 E t
  S2 : IsPGroup 2 S
  SC : S ≤ centralizer (E : Set G)
  Smax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S
  zS : z ∈ S
  D8 : Nonempty (S ≃* DihedralGroup 4)
  BS : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b
  odd : ∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
    N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
    (N : Set (centralizer (E : Set G))) *
      (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) = Set.univ
  h67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t
  h68 : ∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
    ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹
  fus : ∃ e ∈ E, e * e = 1 ∧ e ≠ 1 ∧ e ≠ t ∧ ∃ g : G, g * z * g⁻¹ = z * e

structure AlphaSpec {G : Type*} [Group G] (S : Subgroup G) (z t α : G) : Prop where
  mem : α ∈ S
  sq : α * α = 1
  rel : α * z = t * (z * α)
  ne_one : α ≠ 1
  ne_t : α ≠ t
  ne_z : α ≠ z
  ne_zt : α ≠ z * t
  r_ne_one : α * z ≠ 1
  r_ne_t : α * z ≠ t
  r_ne_z : α * z ≠ z
  r_ne_zt : α * z ≠ z * t
  r_ne_a : α * z ≠ α
  r_ne_at : α * z ≠ α * t
  list : ∀ s ∈ S, s = 1 ∨ s = t ∨ s = z ∨ s = z * t ∨ s = α ∨ s = α * t ∨ s = α * z ∨
      s = α * z * t

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem t_mem_E : t ∈ E := h.conf.econfig.t_mem

theorem t_sq : t * t = 1 := h.conf.cfg.t_sq

theorem t_ne : t ≠ 1 := h.conf.cfg.t_ne

theorem z_sq : z * z = 1 := h.conf.cfg.z_sq

theorem z_ne : z ≠ 1 := h.conf.cfg.z_ne

theorem z_ne_t : z ≠ t := h.conf.cfg.z_ne_t

theorem S_comm_E : ∀ s ∈ S, ∀ e ∈ E, s * e = e * s := fun s hs e he =>
  (mem_centralizer_iff.1 (h.SC hs) e he).symm

theorem t_comm_S : ∀ s ∈ S, s * t = t * s := fun s hs => h.S_comm_E s hs t h.t_mem_E

theorem E_comm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e ∨ e * e' = t * (e' * e) := by
  intro e he e' he'
  rcases h.conf.econfig.comm e he e' he' with h1 | h1
  · left
    calc e * e' = (e * e' * e⁻¹ * e'⁻¹) * (e' * e) := by group
      _ = e' * e := by rw [h1, one_mul]
  · right
    calc e * e' = (e * e' * e⁻¹ * e'⁻¹) * (e' * e) := by group
      _ = t * (e' * e) := by rw [h1]

theorem t_mem_S : t ∈ S := by
  have hcfg := h.conf.cfg
  have hE := h.conf.econfig
  have htE : t ∈ E := hE.t_mem
  have hzE : zpowers t ≤ E := zpowers_le.2 htE
  have hzpC : zpowers t ≤ centralizer (E : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun e he => hcfg.t_central e (hE.le he)
  have hZ2 : IsPGroup 2 (zpowers t) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcfg.t_order]; norm_num)
  have hSn : S ≤ normalizer ((zpowers t : Subgroup G) : Set G) :=
    (h.SC.trans (centralizer_le hzE)).trans (centralizer_le_normalizer _)
  have hR2 : IsPGroup 2 (S ⊔ zpowers t : Subgroup G) := h.S2.to_sup_of_normal_right' hZ2 hSn
  have := h.Smax _ hR2 (sup_le h.SC hzpC) le_sup_left
  rw [← this]
  exact mem_sup_right (mem_zpowers t)

theorem tD8 : ∃ eS : S ≃* DihedralGroup 4, (∀ x, x * eS ⟨t, h.t_mem_S⟩ = eS ⟨t, h.t_mem_S⟩ * x) ∧
    eS ⟨t, h.t_mem_S⟩ * eS ⟨t, h.t_mem_S⟩ = 1 ∧ eS ⟨t, h.t_mem_S⟩ ≠ 1 := by
  obtain ⟨eS⟩ := h.D8
  refine ⟨eS, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := eS.surjective x
    rw [← map_mul, ← map_mul]
    exact congrArg eS (Subtype.ext (h.t_comm_S y y.2))
  · rw [← map_mul, ← map_one eS]
    exact congrArg eS (Subtype.ext h.t_sq)
  · intro h1
    apply h.t_ne
    have := eS.injective (h1.trans (map_one eS).symm)
    exact congrArg Subtype.val this

theorem S_comm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s ∨ s * s' = t * (s' * s) := by
  obtain ⟨eS, hc_cen, hc_sq, hc_ne⟩ := h.tD8
  intro s hs s' hs'
  have key := d8_comm _ hc_cen hc_sq hc_ne (eS ⟨s, hs⟩) (eS ⟨s', hs'⟩)
  have hinj : ∀ x y : DihedralGroup 4, ((eS.symm x : S) : G) = ((eS.symm y : S) : G) → x = y :=
    fun x y hxy => eS.symm.injective (Subtype.ext hxy)
  rcases key with h1 | h1
  · left
    have := congrArg (fun x => ((eS.symm x : S) : G)) h1
    simpa [map_mul, Subgroup.coe_mul] using this
  · right
    have := congrArg (fun x => ((eS.symm x : S) : G)) h1
    simpa [map_mul, Subgroup.coe_mul] using this

theorem exists_alpha : ∃ α, AlphaSpec S z t α := by
  obtain ⟨eS, hc_cen, hc_sq, hc_ne⟩ := h.tD8
  set c : DihedralGroup 4 := eS ⟨t, h.t_mem_S⟩ with hc
  have htS := h.t_mem_S
  set d : DihedralGroup 4 := eS ⟨z, h.zS⟩ with hd
  have hc_cen : ∀ x, x * c = c * x := by
    intro x
    obtain ⟨y, rfl⟩ := eS.surjective x
    rw [hc, ← map_mul, ← map_mul]
    exact congrArg eS (Subtype.ext (h.t_comm_S y y.2))
  have hc_sq : c * c = 1 := by
    rw [hc, ← map_mul, ← map_one eS]
    exact congrArg eS (Subtype.ext h.t_sq)
  have hc_ne : c ≠ 1 := by
    intro h1
    apply h.t_ne
    have := eS.injective (h1.trans (map_one eS).symm)
    exact congrArg Subtype.val this
  have hd_sq : d * d = 1 := by
    rw [hd, ← map_mul, ← map_one eS]
    exact congrArg eS (Subtype.ext h.z_sq)
  have hd_ne : d ≠ 1 := by
    intro h1
    apply h.z_ne
    have := eS.injective (h1.trans (map_one eS).symm)
    exact congrArg Subtype.val this
  have hdc : d ≠ c := by
    intro h1
    apply h.z_ne_t
    have := eS.injective h1
    exact congrArg Subtype.val this
  obtain ⟨a, ha2, had, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    d8_exists c d hc_cen hc_sq hc_ne hd_sq hd_ne hdc
  have hlist := d8_list c d a hc_cen hc_sq hc_ne hd_sq hd_ne hdc ha2 had
  let ι : DihedralGroup 4 → G := fun x => ((eS.symm x : S) : G)
  have ι_mul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => by
    simp [ι, map_mul, Subgroup.coe_mul]
  have ι_inj : ∀ x y, ι x = ι y → x = y := fun x y hxy =>
    eS.symm.injective (Subtype.ext hxy)
  have ι_c : ι c = t := by simp [ι, hc]
  have ι_d : ι d = z := by simp [ι, hd]
  have ι_one : ι 1 = 1 := by simp [ι]
  have ι_mem : ∀ x, ι x ∈ S := fun x => (eS.symm x).2
  have ne_of : ∀ x y, x ≠ y → ι x ≠ ι y := fun x y hxy hh => hxy (ι_inj x y hh)
  refine ⟨ι a, ⟨ι_mem a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [← ι_mul, ha2, ι_one]
  · rw [← ι_d, ← ι_c, ← ι_mul, ← ι_mul, ← ι_mul, had]
  · rw [← ι_one]; exact ne_of _ _ h1
  · rw [← ι_c]; exact ne_of _ _ h2
  · rw [← ι_d]; exact ne_of _ _ h3
  · rw [← ι_d, ← ι_c, ← ι_mul]; exact ne_of _ _ h4
  · rw [← ι_d, ← ι_mul, ← ι_one]; exact ne_of _ _ h5
  · rw [← ι_d, ← ι_mul, ← ι_c]; exact ne_of _ _ h6
  · rw [← ι_d, ← ι_mul]; exact ne_of _ _ h7
  · rw [← ι_d, ← ι_c, ← ι_mul, ← ι_mul]; exact ne_of _ _ h8
  · rw [← ι_d, ← ι_mul]; exact ne_of _ _ h9
  · rw [← ι_d, ← ι_c, ← ι_mul, ← ι_mul]; exact ne_of _ _ h10
  · intro s hs
    have hx := hlist (eS ⟨s, hs⟩)
    have hs' : ι (eS ⟨s, hs⟩) = s := by simp [ι]
    rw [← hs']
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx
    · left; rw [hx, ι_one]
    · right; left; rw [hx, ι_c]
    · right; right; left; rw [hx, ι_d]
    · right; right; right; left; rw [hx, ι_mul, ι_d, ι_c]
    · right; right; right; right; left; rw [hx]
    · right; right; right; right; right; left; rw [hx, ι_mul, ι_c]
    · right; right; right; right; right; right; left; rw [hx, ι_mul, ι_d]
    · right; right; right; right; right; right; right; rw [hx, ι_mul, ι_mul, ι_d, ι_c]


theorem t_comm_E : ∀ e ∈ E, e * t = t * e := fun e he =>
  h.conf.cfg.t_central e (h.conf.econfig.le he)

theorem anti_of_eq_t_mul {a b : G} (hab : a * b = t * (b * a)) : a * b ≠ b * a := by
  intro h1
  rw [h1] at hab
  have : t = 1 := by
    have h2 : (1 : G) * (b * a) = t * (b * a) := by rw [one_mul]; exact hab
    exact (mul_right_cancel h2).symm
  exact h.t_ne this

theorem comm_iff {s s' e e' : G} (hs : s ∈ S) (hs' : s' ∈ S) (he : e ∈ E) (he' : e' ∈ E) :
    (s * e) * (s' * e') = (s' * e') * (s * e) ↔ (s * s' = s' * s ↔ e * e' = e' * e) := by
  have hX1 : (s * e) * (s' * e') = (s * s') * (e * e') := by
    calc (s * e) * (s' * e') = s * (e * s') * e' := by group
      _ = s * (s' * e) * e' := by rw [← h.S_comm_E s' hs' e he]
      _ = (s * s') * (e * e') := by group
  have hX2 : (s' * e') * (s * e) = (s' * s) * (e' * e) := by
    calc (s' * e') * (s * e) = s' * (e' * s) * e := by group
      _ = s' * (s * e') * e := by rw [← h.S_comm_E s hs e' he']
      _ = (s' * s) * (e' * e) := by group
  rw [hX1, hX2]
  have hts : ∀ a b : G, a * t = t * a → a * (t * b) = t * (a * b) := fun a b hab => by
    rw [← mul_assoc, hab, mul_assoc]
  have hSS : (s' * s) * t = t * (s' * s) := h.t_comm_S _ (mul_mem hs' hs)
  have hEE : (e' * e) * t = t * (e' * e) := h.t_comm_E _ (mul_mem he' he)
  have htX : ∀ X : G, t * X ≠ X := fun X hX => by
    apply h.t_ne
    have := congrArg (· * X⁻¹) hX
    simpa using this
  have hcomm : (s' * s) * (e' * e) = t * ((s' * s) * (e' * e)) → False := fun hh =>
    htX _ hh.symm
  rcases h.S_comm s hs s' hs' with h1 | h1 <;> rcases h.E_comm e he e' he' with h2 | h2
  · exact iff_of_true (by rw [h1, h2]) ⟨fun _ => h2, fun _ => h1⟩
  · have hne : e * e' ≠ e' * e := h.anti_of_eq_t_mul h2
    refine iff_of_false ?_ ?_
    · intro hL
      rw [h1, h2] at hL
      have : (s' * s) * (t * (e' * e)) = t * ((s' * s) * (e' * e)) := by
        calc (s' * s) * (t * (e' * e)) = ((s' * s) * t) * (e' * e) := by group
          _ = (t * (s' * s)) * (e' * e) := by rw [hSS]
          _ = t * ((s' * s) * (e' * e)) := by group
      rw [this] at hL
      exact htX _ hL
    · intro hR
      exact hne (hR.1 h1)
  · have hne : s * s' ≠ s' * s := h.anti_of_eq_t_mul h1
    refine iff_of_false ?_ ?_
    · intro hL
      rw [h1, h2] at hL
      have : (t * (s' * s)) * (e' * e) = t * ((s' * s) * (e' * e)) := by group
      rw [this] at hL
      exact htX _ hL
    · intro hR
      exact hne (hR.2 h2)
  · refine iff_of_true ?_ ⟨fun hh => absurd hh (h.anti_of_eq_t_mul h1),
      fun hh => absurd hh (h.anti_of_eq_t_mul h2)⟩
    rw [h1, h2]
    calc (t * (s' * s)) * (t * (e' * e)) = t * (((s' * s) * t) * (e' * e)) := by group
      _ = t * ((t * (s' * s)) * (e' * e)) := by rw [hSS]
      _ = (t * t) * ((s' * s) * (e' * e)) := by group
      _ = (s' * s) * (e' * e) := by rw [h.t_sq, one_mul]


theorem S_inf_E {s : G} (hs : s ∈ S) (hsE : s ∈ E) : s = 1 ∨ s = t :=
  h.conf.econfig.center s hsE (fun f hf => (h.S_comm_E s hs f hf).symm)

theorem odd_mem_L {n : G} (hn : n ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf n)) :
    n ∈ L := by
  have hcfg := h.conf.cfg
  rw [hcfg.cent_eq] at hn
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 hcfg.z_cent) hn
  rcases mem_zpowers_sq_eq_one hcfg.z_sq hc with hc1 | hc1
  · subst hc1
    simpa using ha
  · subst hc1
    exfalso
    obtain ⟨k, hk⟩ := hodd
    have hcomm : Commute a c := hcfg.z_comm_of_mem_A ha
    have hz2 : c ^ 2 = 1 := by rw [pow_two]; exact hcfg.z_sq
    have h1 : (a * c) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    have hcpow : c ^ (2 * k + 1) = c := by rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [hcomm.mul_pow, hcpow] at h1
    have h3 : c = (a ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1
    exact hcfg.z_not_mem_A (by rw [h3]; exact inv_mem (pow_mem ha _))


theorem center_S {c : G} (hcS : c ∈ S) (hc : ∀ s ∈ S, c * s = s * c) : c = 1 ∨ c = t := by
  obtain ⟨eS, hc_cen, hc_sq, hc_ne⟩ := h.tD8
  have hx : ∀ y, y * eS ⟨c, hcS⟩ = eS ⟨c, hcS⟩ * y := by
    intro y
    obtain ⟨u, rfl⟩ := eS.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg eS (Subtype.ext (hc u u.2).symm)
  rcases d8_center _ hc_cen hc_sq hc_ne _ hx with h1 | h1
  · left
    have := eS.injective (h1.trans (map_one eS).symm)
    exact congrArg Subtype.val this
  · right
    have := eS.injective h1
    exact congrArg Subtype.val this

theorem cent_U {c : G} (hc : ∀ u ∈ S ⊔ E, c * u = u * c) : c = 1 ∨ c = t := by
  obtain ⟨N, hNn, hNodd, hNS, hNprod⟩ := h.odd
  have hcCE : c ∈ centralizer (E : Set G) :=
    mem_centralizer_iff.2 fun e he => (hc e (mem_sup_right he)).symm
  have hmem : (⟨c, hcCE⟩ : ↥(centralizer (E : Set G))) ∈
      (N : Set ↥(centralizer (E : Set G))) *
        (S.subgroupOf (centralizer (E : Set G)) : Set ↥(centralizer (E : Set G))) := by
    rw [hNprod]; exact Set.mem_univ _
  obtain ⟨n', hn', s', hs', hns⟩ := Set.mem_mul.1 hmem
  have hcns : (n' : G) * (s' : G) = c := congrArg Subtype.val hns
  have hs : (s' : G) ∈ S := mem_subgroupOf.1 hs'
  have hn_odd : Odd (orderOf (n' : G)) := by
    rw [Subgroup.orderOf_coe]; exact (hNodd n').1 hn'
  set n : G := (n' : G) with hn_def
  set s : G := (s' : G) with hs_def
  let zc : ↥(centralizer (E : Set G)) := ⟨z, h.SC h.zS⟩
  have hcz : c * z = z * c := hc z (mem_sup_left h.zS)
  have hm1 : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' ∈ N :=
    mul_mem (hNn.conj_mem _ (inv_mem hn') _) hn'
  have hmG : z⁻¹ * n⁻¹ * z * n = z⁻¹ * s * z * s⁻¹ := by
    have h1 : n * s * z = z * (n * s) := by rw [hcns]; exact hcz
    calc z⁻¹ * n⁻¹ * z * n = z⁻¹ * (n⁻¹ * (z * (n * s)) * s⁻¹) := by group
      _ = z⁻¹ * (n⁻¹ * (n * s * z) * s⁻¹) := by rw [h1]
      _ = z⁻¹ * s * z * s⁻¹ := by group
  have hmS : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' ∈ S.subgroupOf (centralizer (E : Set G)) := by
    rw [mem_subgroupOf]
    have : (((zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' : ↥(centralizer (E : Set G))) : G) =
        z⁻¹ * n⁻¹ * z * n := by
      simp [zc, hn_def]
    rw [this, hmG]
    exact mul_mem (mul_mem (mul_mem (inv_mem h.zS) hs) h.zS) (inv_mem hs)
  have hm_one : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' = 1 := by
    have : (zc⁻¹ * n'⁻¹ * zc⁻¹⁻¹) * n' ∈ N ⊓ S.subgroupOf (centralizer (E : Set G)) :=
      ⟨hm1, hmS⟩
    rw [hNS, mem_bot] at this
    exact this
  have hmG1 : z⁻¹ * n⁻¹ * z * n = 1 := by
    have := congrArg (fun y : ↥(centralizer (E : Set G)) => (y : G)) hm_one
    simpa [zc, hn_def] using this
  have hnz : z * n = n * z := by
    have h1 : n⁻¹ * z * n = z := by
      have : z⁻¹ * (n⁻¹ * z * n) = 1 := by rw [← hmG1]; group
      exact (inv_mul_eq_one.1 this).symm
    calc z * n = n * (n⁻¹ * z * n) := by group
      _ = n * z := by rw [h1]
  have hsz : s * z = z * s := by
    have h1 : z⁻¹ * s * z * s⁻¹ = 1 := by rw [← hmG, hmG1]
    have h2 : z⁻¹ * s * z = s := by
      have := congrArg (· * s) h1
      simpa using this
    calc s * z = z * (z⁻¹ * s * z) := by group
      _ = z * s := by rw [h2]
  have hnL : n ∈ L := h.odd_mem_L (mem_centralizer_singleton_iff.2 hnz.symm) hn_odd
  have hn1 : n = 1 := by
    rcases h.wf.cent n hnL (fun e he => (mem_centralizer_iff.1 n'.2 e he).symm) with h1 | h1
    · exact h1
    · exfalso
      rw [h1, h.conf.cfg.t_order] at hn_odd
      exact absurd hn_odd (by decide)
  have hcs : c = s := by rw [← hcns, hn1, one_mul]
  have hcS : c ∈ S := hcs ▸ hs
  exact h.center_S hcS (fun u hu => hc u (mem_sup_left hu))



end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
