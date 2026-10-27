module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Hyp

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem OuterConfig.t_order' {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T : Subgroup G}
    (h : OuterConfig G A z t T) : orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.t_sq) h.t_ne

structure OHyp69 {G : Type} [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G)
    (B : Subgroup G) (β : G) (S : Subgroup G) : Prop where
  oe : OuterE G L z t T E
  wf : WFacts L t E
  ef : EFacts69 E t
  ob : OuterB L t B β
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
  cU : ∀ c : G, (∀ u ∈ S ⊔ E, c * u = u * c) → c = 1 ∨ c = t

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem t_mem_E : t ∈ E := h.oe.econfig.t_mem

theorem t_sq : t * t = 1 := h.oe.cfg.t_sq

theorem t_ne : t ≠ 1 := h.oe.cfg.t_ne

theorem z_sq : z * z = 1 := h.oe.cfg.z_sq

theorem z_ne : z ≠ 1 := h.oe.cfg.z_ne

theorem z_ne_t : z ≠ t := h.oe.cfg.z_ne_t

theorem S_comm_E : ∀ s ∈ S, ∀ e ∈ E, s * e = e * s := fun s hs e he =>
  (mem_centralizer_iff.1 (h.SC hs) e he).symm

theorem t_comm_S : ∀ s ∈ S, s * t = t * s := fun s hs => h.S_comm_E s hs t h.t_mem_E

theorem E_comm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e ∨ e * e' = t * (e' * e) := by
  intro e he e' he'
  rcases h.oe.econfig.comm e he e' he' with h1 | h1
  · left
    calc e * e' = (e * e' * e⁻¹ * e'⁻¹) * (e' * e) := by group
      _ = e' * e := by rw [h1, one_mul]
  · right
    calc e * e' = (e * e' * e⁻¹ * e'⁻¹) * (e' * e) := by group
      _ = t * (e' * e) := by rw [h1]

theorem t_mem_S : t ∈ S := by
  have hcfg := h.oe.cfg
  have hE := h.oe.econfig
  have htE : t ∈ E := hE.t_mem
  have hzE : zpowers t ≤ E := zpowers_le.2 htE
  have hzpC : zpowers t ≤ centralizer (E : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun e he => hcfg.t_central e (h.oe.E_le_T he)
  have hZ2 : IsPGroup 2 (zpowers t) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcfg.t_order']; norm_num)
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

theorem t_comm_E : ∀ e ∈ E, e * t = t * e := fun e he =>
  h.oe.cfg.t_central e (h.oe.E_le_T he)

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

theorem odd_mem_L {n : G} (hn : n ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf n)) :
    n ∈ L := h.oe.cfg.odd_mem_A hn hodd

theorem cent_U {c : G} (hc : ∀ u ∈ S ⊔ E, c * u = u * c) : c = 1 ∨ c = t := h.cU c hc

theorem S_inf_E {s : G} (hs : s ∈ S) (hsE : s ∈ E) : s = 1 ∨ s = t :=
  h.oe.econfig.center s hsE (fun f hf => (h.S_comm_E s hs f hf).symm)

end OHyp69

namespace OuterS8Hyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (h : OuterS8Hyp G L z t T E Q x B β S)

include h in
theorem exists_fus : ∃ e ∈ E, e * e = 1 ∧ e ≠ 1 ∧ e ≠ t ∧ ∃ g : G, g * z * g⁻¹ = z * e := by
  have hE := h.outerE.econfig
  have hcfg := h.outerE.cfg
  have hex : ∃ e ∈ E, e * e = 1 ∧ e ≠ 1 ∧ e ≠ t := by
    by_contra hno
    push_neg at hno
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hE.nonab
    apply hne
    have hle : E ≤ zpowers t := by
      rw [hE.gen]
      refine (closure_le (zpowers t)).2 fun e he => ?_
      have h1 : e = t := hno e he.1 he.2.1 he.2.2
      rw [h1]
      exact mem_zpowers t
    obtain ⟨k₁, hk₁⟩ := mem_zpowers_iff.1 (hle he₁)
    obtain ⟨k₂, hk₂⟩ := mem_zpowers_iff.1 (hle he₂)
    rw [← hk₁, ← hk₂, ← zpow_add, ← zpow_add, add_comm]
  obtain ⟨e, heE, he2, he1, het⟩ := hex
  obtain ⟨c, hcL, hc⟩ := hE.conj e heE he2 he1
  refine ⟨e, heE, he2, he1, het, c * x, ?_⟩
  have hcz : c * z = z * c := hcfg.z_comm_of_mem_A hcL
  have hczi : c⁻¹ * z = z * c⁻¹ := by
    have := hcfg.z_comm_of_mem_A (inv_mem hcL : c⁻¹ ∈ L)
    exact this
  calc c * x * z * (c * x)⁻¹ = c * (x * z * x⁻¹) * c⁻¹ := by group
    _ = c * (z * t) * c⁻¹ := by rw [h.x_z]
    _ = z * (c * t * c⁻¹) := by
        calc c * (z * t) * c⁻¹ = (c * z) * t * c⁻¹ := by group
          _ = (z * c) * t * c⁻¹ := by rw [hcz]
          _ = z * (c * t * c⁻¹) := by group
    _ = z * e := by rw [← hc]

end OuterS8Hyp

end CFSG.EvenSporadicStandard.Fin76b
