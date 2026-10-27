module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineSplit
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineTwoLayers

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem outer_comm_facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {v : G} (hvT : v ∈ T)
    (hv2 : v ^ 2 = 1) (hv : v ∉ szT₁ L T ⊔ zpowers t) :
    (∀ y ∈ szT₁ L T, y * v * y⁻¹ * v⁻¹ ∈ szA₁ (szT₁ L T) →
      ∃ w ∈ szT₁ L T, y = w * v * w⁻¹ * v⁻¹) ∧
      ∃ y ∈ szT₁ L T, y * v * y⁻¹ * v⁻¹ ∉ szA₁ (szT₁ L T) := by
  classical
  obtain ⟨-, -, -, hTN₁, -, -, hinner⟩ := h.start_of_card_sylow hS2
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hout : ¬ ∃ l ∈ L, ∀ y ∈ L, v * y * v⁻¹ = l * y * l⁻¹ := fun ⟨l, hl, hvl⟩ =>
    hv (hinner v hvT l hl hvl)
  set σ := L.normalizerMonoidHom ⟨v, h.le_normalizer hvT⟩ with hσdef
  have hσ : ∀ y : L, ((σ y : L) : G) = v * y * v⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hσ, hσ]
    calc v * (v * (y : G) * v⁻¹) * v⁻¹ = (v * v) * y * (v * v)⁻¹ := by group
      _ = y := by rw [hvv]; group
  have hσout : ¬ ∃ g : L, ∀ y : L, σ y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hout ⟨g, g.2, fun y hy => ?_⟩
    have := congrArg Subtype.val (hg ⟨y, hy⟩)
    rw [hσ] at this
    simpa using this
  have hσQ : ∀ y ∈ (Q : Subgroup L), σ y ∈ (Q : Subgroup L) := by
    intro y hy
    rw [hmemQ, hσ]
    exact (mem_normalizer_iff.mp (hTN₁ hvT) y).mp ((hmemQ y).mp hy)
  have hfix : ∀ {y : L}, y ∈ (Q : Subgroup L) → (σ y = y ↔ y ∈ rootCenter (Q : Subgroup L)) :=
    fun hy => hB.fixed_iff_rootCenter_unitary Q σ hσσ hσout hσQ hy
  obtain ⟨-, -, hWcard, -, -, -, -, -, hWiff⟩ := hB.lemma_3_4_d5_unitary Q σ hσσ hσout hσQ
  have htrans : ∀ y : L, (y : G) ∈ szT₁ L T →
      (y : G) * v * (y : G)⁻¹ * v⁻¹ ∈ szA₁ (szT₁ L T) →
        y⁻¹ * σ y ∈ rootCenter (Q : Subgroup L) := by
    intro y hy hyv
    refine (hmemZ _).mpr ?_
    have h1 : (y : G)⁻¹ * (v * y * v⁻¹) = (y : G)⁻¹ * (y * v * (y : G)⁻¹ * v⁻¹)⁻¹ * y := by group
    have h2 := (mem_normalizer_iff.mp (normalizer_le_normalizer_inf_centralizer (szT₁ L T)
      (Subgroup.le_normalizer (inv_mem hy))) _).mp (inv_mem hyv)
    rw [inv_inv] at h2
    simp only [coe_mul, coe_inv, hσ]
    rw [h1]
    exact h2
  refine ⟨fun y hy hyv => ?_, ?_⟩
  ·
    have hcinj : ∀ x ∈ ((Q : Subgroup L) : Set L), ∀ z ∈ ((Q : Subgroup L) : Set L),
        autComm σ x = autComm σ z → x * z⁻¹ ∈ rootCenter (Q : Subgroup L) := by
      intro x hx z hz hxz
      have h1 : σ x = x * (z⁻¹ * σ z) := by
        calc σ x = x * (x⁻¹ * σ x) := by group
          _ = x * (z⁻¹ * σ z) := by rw [show x⁻¹ * σ x = z⁻¹ * σ z from hxz]
      have h2 : σ (x * z⁻¹) = x * z⁻¹ := by
        rw [map_mul, map_inv, h1]
        group
      exact (hfix (mul_mem hx (inv_mem hz))).mp h2
    have hsub : autComm σ '' ((Q : Subgroup L) : Set L) ⊆
        (commutatorAut (Q : Subgroup L) σ : Set L) := fun _ hx => subset_closure hx
    have hlow : ((2 ^ f) ^ 2 : ℕ) ≤ (autComm σ '' ((Q : Subgroup L) : Set L)).ncard := by
      have h1 := ncard_le_mul_ncard_image (T := ((Q : Subgroup L) : Set L))
        (Z := rootCenter (Q : Subgroup L)) (autComm σ) hcinj
      have h2 : ((Q : Subgroup L) : Set L).ncard = (2 ^ f) ^ 3 := by
        rw [← Nat.card_coe_set_eq]
        exact hc.card_eq
      rw [h2, hc.card_center] at h1
      have h3 : 0 < 2 ^ f := by positivity
      have : 2 ^ f * (2 ^ f) ^ 2 ≤ 2 ^ f * (autComm σ '' ((Q : Subgroup L) : Set L)).ncard := by
        calc 2 ^ f * (2 ^ f) ^ 2 = (2 ^ f) ^ 3 := by ring
          _ ≤ _ := h1
      exact Nat.le_of_mul_le_mul_left this h3
    have heq : autComm σ '' ((Q : Subgroup L) : Set L) =
        (commutatorAut (Q : Subgroup L) σ : Set L) :=
      Set.eq_of_subset_of_ncard_le hsub (by
        have hW' : ((commutatorAut (Q : Subgroup L) σ : Subgroup L) : Set L).ncard =
            (2 ^ f) ^ 2 := by
          rw [← Nat.card_coe_set_eq]; exact hWcard
        rw [hW']; exact hlow) (Set.toFinite _)
    have hyL : y ∈ L := szT₁_le_right L T hy
    have hyW : (⟨y, hyL⟩ : L) ∈ ((commutatorAut (Q : Subgroup L) σ : Subgroup L) : Set L) :=
      (hWiff _ ((hmemQ _).mpr hy)).mp (htrans ⟨y, hyL⟩ hy hyv)
    rw [← heq] at hyW
    obtain ⟨w, hwQ, hw⟩ := hyW
    refine ⟨(w : G)⁻¹, inv_mem ((hmemQ w).mp hwQ), ?_⟩
    have := congrArg Subtype.val hw
    simp only [autComm, coe_mul, coe_inv, hσ] at this
    rw [← this]
    group
  · by_contra hall
    push Not at hall
    have hle : (Q : Subgroup L) ≤ commutatorAut (Q : Subgroup L) σ := fun y hyQ =>
      (hWiff y hyQ).mp (htrans y ((hmemQ y).mp hyQ) (hall _ ((hmemQ y).mp hyQ)))
    have h1 := card_le_of_le hle
    rw [hc.card_eq, hWcard] at h1
    have h2 : (2 ^ f) ^ 2 < (2 ^ f) ^ 3 :=
      Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by have := h.two_le; omega)) (by norm_num)
    omega

theorem exists_eq_comm_of_outer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {v : G} (hvT : v ∈ T)
    (hv2 : v ^ 2 = 1) (hv : v ∉ szT₁ L T ⊔ zpowers t) {y : G} (hy : y ∈ szT₁ L T)
    (hyv : y * v * y⁻¹ * v⁻¹ ∈ szA₁ (szT₁ L T)) :
    ∃ w ∈ szT₁ L T, y = w * v * w⁻¹ * v⁻¹ :=
  (h.outer_comm_facts_of_card_sylow hS2 hvT hv2 hv).1 y hy hyv

theorem exists_comm_not_mem_of_outer_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1) (hv : v ∉ szT₁ L T ⊔ zpowers t) :
    ∃ y ∈ szT₁ L T, y * v * y⁻¹ * v⁻¹ ∉ szA₁ (szT₁ L T) :=
  (h.outer_comm_facts_of_card_sylow hS2 hvT hv2 hv).2

theorem mem_szT₁_of_mem_normalizer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxL : x ∈ L)
    (hxN : x ∈ normalizer (szT₁ L T : Set G)) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ szT₁ L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨Q, hQ⟩, -⟩ := h.start_of_card_sylow hS2
  set y : L := ⟨x, hxL⟩ with hy
  have hyN : y ∈ normalizer ((Q : Subgroup L) : Set L) := by
    rw [hQ]
    refine mem_normalizer_iff.mpr fun z => ?_
    simp only [mem_subgroupOf, coe_mul, coe_inv, hy]
    exact mem_normalizer_iff.mp hxN z
  have hyk : y ^ 2 ^ k = 1 := Subtype.ext (by simpa [hy] using hk)
  have hZ : IsPGroup 2 (zpowers y) := by
    have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hyk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hR := IsPGroup.to_sup_of_normal_left' Q.isPGroup' hZ (zpowers_le.mpr hyN)
  have heq := Q.is_maximal' hR le_sup_left
  have hyQ : y ∈ (Q : Subgroup L) := by
    rw [← heq]
    exact mem_sup_right (mem_zpowers y)
  rw [hQ] at hyQ
  exact mem_subgroupOf.mp hyQ

theorem comm_mem_of_outer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {v : G} (hvT : v ∈ T)
    (hv2 : v ^ 2 = 1) (hv : v ∉ szT₁ L T ⊔ zpowers t) {d : G} (hdL : d ∈ L)
    (hdN : d ∈ normalizer (szT₁ L T : Set G)) :
    v⁻¹ * d * v * d⁻¹ ∈ L ∧ v⁻¹ * d * v * d⁻¹ ∈ normalizer (szT₁ L T : Set G) ∧
      v⁻¹ * d * v * d⁻¹ ∈ centralizer (szA₁ (szT₁ L T) : Set G) := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, hvA, -, -⟩ := h.outer_facts_of_card_sylow hS2 hvT hv2 hv
  have hvL : v ∈ normalizer (L : Set G) := h.le_normalizer hvT
  refine ⟨mul_mem ((mem_normalizer_iff''.mp hvL d).mp hdL) (inv_mem hdL),
    mul_mem (mul_mem (mul_mem (inv_mem (hTN₁ hvT)) hdN) (hTN₁ hvT)) (inv_mem hdN), ?_⟩
  have hdA : d⁻¹ ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    normalizer_le_normalizer_inf_centralizer (szT₁ L T) (inv_mem hdN)
  refine mem_centralizer_iff.mpr fun a ha => ?_
  have ha' : d⁻¹ * a * d ∈ szA₁ (szT₁ L T) := by
    have := (mem_normalizer_iff.mp hdA a).mp ha
    rwa [inv_inv] at this
  have hva : v * a = a * v := hvA a ha
  have hva' : v * (d⁻¹ * a * d) = (d⁻¹ * a * d) * v := hvA _ ha'
  have hva'' : v⁻¹ * a = a * v⁻¹ := by
    calc v⁻¹ * a = v⁻¹ * (a * v) * v⁻¹ := by group
      _ = v⁻¹ * (v * a) * v⁻¹ := by rw [hva]
      _ = a * v⁻¹ := by group
  calc a * (v⁻¹ * d * v * d⁻¹) = v⁻¹ * a * d * v * d⁻¹ := by rw [hva'']; group
    _ = v⁻¹ * d * ((d⁻¹ * a * d) * v) * d⁻¹ := by group
    _ = v⁻¹ * d * (v * (d⁻¹ * a * d)) * d⁻¹ := by rw [hva']
    _ = v⁻¹ * d * v * d⁻¹ * a := by group

end U3Start

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem inv_mul_mem_of_rho_eq_rho (hR : U3R2 G L T₁ R₂ t f) {u w : G} (hu : u ∈ R₂) (hw : w ∈ R₂)
    (huw : u * t * u⁻¹ * t = w * t * w⁻¹ * t) : u⁻¹ * w ∈ szA₁ T₁ := by
  have h1 : u * t * u⁻¹ = w * t * w⁻¹ := by rw [hR.conj_t_eq u, hR.conj_t_eq w, huw]
  refine hR.rho_ker _ (mul_mem (inv_mem hu) hw) ?_
  calc u⁻¹ * w * t = u⁻¹ * (w * t * w⁻¹) * w := by group
    _ = u⁻¹ * (u * t * u⁻¹) * w := by rw [h1]
    _ = t * (u⁻¹ * w) := by group

theorem free_of_not_mem_centralizer (hR : U3R2 G L T₁ R₂ t f) {v d : G} (hvt : v * t = t * v)
    (hvR : v ∈ normalizer (R₂ : Set G)) (hvA : ∀ a ∈ szA₁ T₁, v * a = a * v)
    (hdt : d * t = t * d) (hdR : d ∈ normalizer (R₂ : Set G))
    (htr : ∀ b ∈ szA₁ T₁, ∀ b' ∈ szA₁ T₁, b ≠ 1 → b' ≠ 1 → ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b')
    (hc : v⁻¹ * d * v * d⁻¹ ∈ centralizer (R₂ : Set G)) (hv : v ∉ centralizer (R₂ : Set G)) :
    (∀ r ∈ R₂, v * r * v⁻¹ = r → r ∈ szA₁ T₁) ∧
      ∀ a ∈ szA₁ T₁, ∃ s ∈ R₂, s * v * s⁻¹ * v⁻¹ = a := by
  have hφA : ∀ r ∈ R₂, r * v * r⁻¹ * v⁻¹ ∈ szA₁ T₁ := by
    intro r hr
    have hvr : v * r * v⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hvR r).mp hr
    have h1 : v⁻¹ * t = t * v⁻¹ := by
      calc v⁻¹ * t = v⁻¹ * (t * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * t) * v⁻¹ := by rw [hvt]
        _ = t * v⁻¹ := by group
    have hρ : r * t * r⁻¹ * t = v * r * v⁻¹ * t * (v * r * v⁻¹)⁻¹ * t := by
      have := U3R2.rho_conj (D := v⁻¹) (u := r) h1
      simp only [inv_inv] at this
      rw [this, hvA _ (hR.rho_mem r hr), mul_inv_cancel_right]
    have h2 := hR.inv_mul_mem_of_rho_eq_rho hr hvr hρ
    have h3 : (r⁻¹ * (v * r * v⁻¹))⁻¹ ∈ szA₁ T₁ := inv_mem h2
    have e : r * v * r⁻¹ * v⁻¹ = r * (r⁻¹ * (v * r * v⁻¹))⁻¹ * r⁻¹ := by group
    rw [e, hR.comm r hr _ (hR.le h3), mul_inv_cancel_right]
    exact h3
  have hφ1 : ∀ r a : G, a ∈ szA₁ T₁ → (r * a) * v * (r * a)⁻¹ * v⁻¹ = r * v * r⁻¹ * v⁻¹ := by
    intro r a ha
    have h1 : a * v = v * a := (hvA a ha).symm
    calc (r * a) * v * (r * a)⁻¹ * v⁻¹ = r * (a * v) * a⁻¹ * r⁻¹ * v⁻¹ := by group
      _ = r * (v * a) * a⁻¹ * r⁻¹ * v⁻¹ := by rw [h1]
      _ = r * v * r⁻¹ * v⁻¹ := by group
  have hφd : ∀ r ∈ R₂, (d⁻¹ * r * d) * v * (d⁻¹ * r * d)⁻¹ * v⁻¹ =
      d⁻¹ * (r * v * r⁻¹ * v⁻¹) * d := by
    intro r hr
    have hcr : (v⁻¹ * d * v * d⁻¹) * r⁻¹ = r⁻¹ * (v⁻¹ * d * v * d⁻¹) :=
      (mem_centralizer_iff.mp hc r⁻¹ (inv_mem hr)).symm
    calc (d⁻¹ * r * d) * v * (d⁻¹ * r * d)⁻¹ * v⁻¹ =
        d⁻¹ * (r * v * ((v⁻¹ * d * v * d⁻¹) * r⁻¹) * (v⁻¹ * d * v * d⁻¹)⁻¹ * v⁻¹) * d := by
          group
      _ = d⁻¹ * (r * v * (r⁻¹ * (v⁻¹ * d * v * d⁻¹)) * (v⁻¹ * d * v * d⁻¹)⁻¹ * v⁻¹) * d := by
          rw [hcr]
      _ = d⁻¹ * (r * v * r⁻¹ * v⁻¹) * d := by group
  have hconj : ∀ n : ℕ, ∀ r ∈ R₂, (d ^ n)⁻¹ * r * d ^ n ∈ R₂ := fun n r hr =>
    (mem_normalizer_iff''.mp (pow_mem hdR n) r).mp hr
  have hφdn : ∀ n : ℕ, ∀ r ∈ R₂, ((d ^ n)⁻¹ * r * d ^ n) * v * ((d ^ n)⁻¹ * r * d ^ n)⁻¹ * v⁻¹ =
      (d ^ n)⁻¹ * (r * v * r⁻¹ * v⁻¹) * d ^ n := by
    intro n
    induction n with
    | zero => intro r _; simp
    | succ n ih =>
      intro r hr
      have e : (d ^ (n + 1))⁻¹ * r * d ^ (n + 1) = d⁻¹ * ((d ^ n)⁻¹ * r * d ^ n) * d := by
        rw [pow_succ]; group
      rw [e, hφd _ (hconj n r hr), ih r hr, pow_succ]
      group
  have hcomm_of : ∀ r : G, r * v * r⁻¹ * v⁻¹ = 1 → r * v = v * r := fun r hr => by
    calc r * v = (r * v * r⁻¹ * v⁻¹) * v * r := by group
      _ = v * r := by rw [hr, one_mul]
  refine ⟨fun r₀ hr₀ hr₀v => ?_, fun a ha => ?_⟩
  · by_contra hr₀A
    have hφr₀ : r₀ * v * r₀⁻¹ * v⁻¹ = 1 := by
      calc r₀ * v * r₀⁻¹ * v⁻¹ = r₀ * (v * r₀ * v⁻¹)⁻¹ := by group
        _ = 1 := by rw [hr₀v, mul_inv_cancel]
    apply hv
    refine mem_centralizer_iff.mpr fun r hr => hcomm_of r ?_
    by_cases hrA : r ∈ szA₁ T₁
    · have h1 := hφ1 1 r hrA
      rw [one_mul] at h1
      rw [h1]
      group
    · obtain ⟨n, hn⟩ := htr _ (hR.rho_mem r₀ hr₀) _ (hR.rho_mem r hr) (hR.rho_ne_one hr₀ hr₀A)
        (hR.rho_ne_one hr hrA)
      have hdn : d ^ n * t = t * d ^ n := (Commute.pow_left hdt n).eq
      have hρ := U3R2.rho_conj (D := d ^ n) (u := r₀) hdn
      rw [hn] at hρ
      have ha := hR.inv_mul_mem_of_rho_eq_rho (hconj n r₀ hr₀) hr hρ
      calc r * v * r⁻¹ * v⁻¹ =
          (((d ^ n)⁻¹ * r₀ * d ^ n) * (((d ^ n)⁻¹ * r₀ * d ^ n)⁻¹ * r)) * v *
            (((d ^ n)⁻¹ * r₀ * d ^ n) * (((d ^ n)⁻¹ * r₀ * d ^ n)⁻¹ * r))⁻¹ * v⁻¹ := by group
        _ = ((d ^ n)⁻¹ * r₀ * d ^ n) * v * ((d ^ n)⁻¹ * r₀ * d ^ n)⁻¹ * v⁻¹ := hφ1 _ _ ha
        _ = (d ^ n)⁻¹ * (r₀ * v * r₀⁻¹ * v⁻¹) * d ^ n := hφdn n r₀ hr₀
        _ = 1 := by rw [hφr₀]; group
  · by_cases ha1 : a = 1
    · exact ⟨1, one_mem _, by rw [ha1]; group⟩
    obtain ⟨r₀, hr₀, hr₀1⟩ : ∃ r₀ ∈ R₂, r₀ * v * r₀⁻¹ * v⁻¹ ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hv (mem_centralizer_iff.mpr fun r hr => hcomm_of r (hall r hr))
    obtain ⟨n, hn⟩ := htr _ (hφA r₀ hr₀) a ha hr₀1 ha1
    exact ⟨_, hconj n r₀ hr₀, by rw [hφdn n r₀ hr₀, hn]⟩

end U3R2

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem mem_centralizer_of_mem_borel_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {c : G} (hcL : c ∈ L)
    (hcN : c ∈ normalizer (szT₁ L T : Set G))
    (hcA : c ∈ centralizer (szA₁ (szT₁ L T) : Set G)) : c ∈ centralizer (R₂ : Set G) := by
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hcR : c ∈ normalizer (R₂ : Set G) := hNR (h.inf_normalizer_le_normalizer_szA ⟨hcL, hcN⟩)
  have hct : c * t = t * c := mem_centralizer_iff.mp h.mem c hcL
  have hcinvt : c⁻¹ * t = t * c⁻¹ := by
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
      _ = t * c⁻¹ := by group
  have hcAc : ∀ a ∈ szA₁ (szT₁ L T), c * a * c⁻¹ = a := fun a ha => by
    rw [← mem_centralizer_iff.mp hcA a ha, mul_inv_cancel_right]
  have hα : ∀ r ∈ R₂, r⁻¹ * (c * r * c⁻¹) ∈ szA₁ (szT₁ L T) := by
    intro r hr
    have hcr : c * r * c⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hcR r).mp hr
    refine hR.inv_mul_mem_of_rho_eq_rho hr hcr ?_
    have := U3R2.rho_conj (D := c⁻¹) (u := r) hcinvt
    simp only [inv_inv] at this
    rw [this, hcAc _ (hR.rho_mem r hr)]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcm2 : (c ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hcmT : c ^ m ∈ szT₁ L T :=
    h.mem_szT₁_of_mem_normalizer_of_card_sylow hS2 (pow_mem hcL m) (pow_mem hcN m) hcm2
  refine mem_centralizer_iff.mpr fun r hr => ?_
  have haA : r⁻¹ * (c * r * c⁻¹) ∈ szA₁ (szT₁ L T) := hα r hr
  have hcra : c * r * c⁻¹ = r * (r⁻¹ * (c * r * c⁻¹)) := by group
  have hcm := conj_pow_eq_mul_pow_of_conj hcra (hcAc _ haA) m
  have hcmr : c ^ m * r * (c ^ m)⁻¹ = r := by
    rw [hR.commT₁ _ hcmT r hr, mul_inv_cancel_right]
  have ham : (r⁻¹ * (c * r * c⁻¹)) ^ m = r⁻¹ * (c * r * c⁻¹) := by
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, hR.sq_A₁ _ haA, one_pow, one_mul]
  rw [hcmr, ham] at hcm
  have ha1 : r⁻¹ * (c * r * c⁻¹) = 1 := mul_eq_left.mp hcm.symm
  have hcr1 : c * r * c⁻¹ = r := by rw [hcra, ha1, mul_one]
  calc r * c = (c * r * c⁻¹) * c := by rw [hcr1]
    _ = c * r := by group

end Certificates

end U3Start


namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem mem_sup_of_comm_mem (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (htt : t * t = 1) {x : G} (hx : x ∈ U₁) (hxt : x * t * x⁻¹ * t⁻¹ ∈ R₂) :
    x ∈ szT₁ L T ⊔ R₂ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hr2 := hU.sq_R₂ _ hxt
  have htr : (x * t * x⁻¹ * t⁻¹) * t = t * (x * t * x⁻¹ * t⁻¹) := by
    have hinv : (x * t * x⁻¹ * t⁻¹)⁻¹ = x * t * x⁻¹ * t⁻¹ :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hr2)
    have h1 : ((x * t * x⁻¹ * t⁻¹) * t) * ((x * t * x⁻¹ * t⁻¹) * t) = 1 := by
      calc ((x * t * x⁻¹ * t⁻¹) * t) * ((x * t * x⁻¹ * t⁻¹) * t) = x * (t * t) * x⁻¹ := by
            group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    calc (x * t * x⁻¹ * t⁻¹) * t = ((x * t * x⁻¹ * t⁻¹) * t)⁻¹ :=
          (inv_eq_of_mul_eq_one_right h1).symm
      _ = t⁻¹ * (x * t * x⁻¹ * t⁻¹)⁻¹ := by rw [mul_inv_rev]
      _ = t * (x * t * x⁻¹ * t⁻¹) := by rw [hinv, htinv]
  obtain ⟨s, hs, hst⟩ := hR.rho_onto _ (hR.rho_ker _ hxt htr)
  have hst' : x * t * x⁻¹ = s * t * s⁻¹ := by
    calc x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
      _ = (s * t * s⁻¹ * t) * t := by rw [hst]
      _ = s * t * s⁻¹ * (t * t) := by group
      _ = s * t * s⁻¹ := by rw [htt, mul_one]
  have hsx : s⁻¹ * x ∈ szT₁ L T := by
    refine hU.mem_szT₁_of_commute hR (mul_mem (inv_mem (hU.le (mem_sup_right hs))) hx) ?_
    calc s⁻¹ * x * t = s⁻¹ * (x * t * x⁻¹) * x := by group
      _ = s⁻¹ * (s * t * s⁻¹) * x := by rw [hst']
      _ = t * (s⁻¹ * x) := by group
  have e : x = s * (s⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_right hs) (mem_sup_left hsx)

theorem exists_inv_comm_mul_mem (hU : U3U1Data G L f t T R₂ U₁) (hR : U3R2 G L (szT₁ L T) R₂ t f)
    {y : G} (hy : y ∈ szT₁ L T ⊔ R₂) : ∃ z ∈ U₁, (z * t * z⁻¹ * t⁻¹)⁻¹ * y ∈ R₂ := by
  obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hy
  obtain ⟨z, hz, r', hr', hzt⟩ := hU.transitive w hw
  refine ⟨z, hz, ?_⟩
  have e1 : z * t * z⁻¹ * t⁻¹ = r' * w := by rw [hzt]; group
  rw [e1, show (r' * w)⁻¹ * (w * r) = w⁻¹ * r'⁻¹ * w * r by group,
    show w⁻¹ * r'⁻¹ = r'⁻¹ * w⁻¹ from (hR.commT₁ _ (inv_mem hw) _ (inv_mem hr')),
    show r'⁻¹ * w⁻¹ * w * r = r'⁻¹ * r by group]
  exact mul_mem (inv_mem hr') hr

end U3U1Data

section Certificates


theorem u3SixNineFreeInput_holds : U3SixNineFreeInput := by
  intro G _ _ L f t T R₂ U₁ h hS2 hR hU v hvT hv2 hvS hvC u hu hu2
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hvR : v ∈ normalizer (R₂ : Set G) := hNR (hTA hvT)
  have htR : t ∈ normalizer (R₂ : Set G) := hNR (hTA htT)
  have hvU : v ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR hvT
  have htU : t ∈ normalizer (U₁ : Set G) := hU.le_normalizer h hS2 hR htT
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hvv : v * v = 1 := by rw [← sq, hv2]
  have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
  obtain ⟨-, hvA, -, -⟩ := h.outer_facts_of_card_sylow hS2 hvT hv2 hvS
  obtain ⟨d, k, hdL, hd⟩ := h.exists_u3RTorus_of_card_sylow hS2
  have hdR : d ∈ normalizer (R₂ : Set G) :=
    hNR (h.inf_normalizer_le_normalizer_szA ⟨hdL, hd.mem_normalizer_T₁⟩)
  obtain ⟨hcL, hcN, hcA⟩ :=
    h.comm_mem_of_outer_of_card_sylow hS2 hvT hv2 hvS hdL hd.mem_normalizer_T₁
  have hc := h.mem_centralizer_of_mem_borel_of_card_sylow hS2 hR hcL hcN hcA
  obtain ⟨hker, himg⟩ :=
    hR.free_of_not_mem_centralizer hvt hvR hvA hd.comm_t hdR hd.trans hc hvC
  have hfreeN : ∀ r ∈ R₂, v * r * v⁻¹ = r → ∃ s ∈ R₂, s * v * s⁻¹ * v⁻¹ = r :=
    fun r hr hrv => himg r (hker r hr hrv)
  have hNc : ∀ n ∈ R₂, ∀ x ∈ U₁, n * x = x * n := fun n hn x hx =>
    mem_centralizer_iff.mp (hU.le_centralizer hx) n hn
  have hM2 : ∀ x ∈ U₁, x * x ∈ R₂ := fun x hx => by rw [← sq]; exact hU.sq_mem x hx
  have htM : ∀ x ∈ U₁, t * x * t⁻¹ ∈ U₁ := fun x hx => (mem_normalizer_iff.mp htU x).mp hx
  have hvM : ∀ x ∈ U₁, v * x * v⁻¹ ∈ U₁ := fun x hx => (mem_normalizer_iff.mp hvU x).mp hx
  have htN : ∀ n ∈ R₂, t * n * t⁻¹ ∈ R₂ := fun n hn => (mem_normalizer_iff.mp htR n).mp hn
  have hvN : ∀ n ∈ R₂, v * n * v⁻¹ ∈ R₂ := fun n hn => (mem_normalizer_iff.mp hvR n).mp hn
  have hkerτ : ∀ x ∈ U₁, x * t * x⁻¹ * t⁻¹ ∈ R₂ → x ∈ szT₁ L T ⊔ R₂ :=
    fun x hx hxt => hU.mem_sup_of_comm_mem hR htt hx hxt
  have hsurjτ : ∀ y ∈ szT₁ L T ⊔ R₂, ∃ z ∈ U₁, (z * t * z⁻¹ * t⁻¹)⁻¹ * y ∈ R₂ :=
    fun y hy => hU.exists_inv_comm_mul_mem hR hy
  have hfreeH : ∀ y ∈ szT₁ L T ⊔ R₂, y * v * y⁻¹ * v⁻¹ ∈ R₂ →
      ∃ w ∈ szT₁ L T ⊔ R₂, (w * v * w⁻¹ * v⁻¹)⁻¹ * y ∈ R₂ := by
    intro y hy hyv
    obtain ⟨w₀, hw₀, r, hr, rfl⟩ := hR.mem_sup_iff.mp hy
    have hνr : r * v * r⁻¹ * v⁻¹ ∈ R₂ := by
      simpa [mul_assoc] using mul_mem hr (hvN _ (inv_mem hr))
    have hνw₀ : w₀ * v * w₀⁻¹ * v⁻¹ ∈ szT₁ L T ⊓ R₂ := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have := mul_mem hw₀ ((mem_normalizer_iff.mp (hTN₁ hvT) _).mp (inv_mem hw₀))
        simpa [mul_assoc] using this
      · have e : w₀ * v * w₀⁻¹ * v⁻¹ =
            (w₀ * (r * v * r⁻¹ * v⁻¹) * w₀⁻¹)⁻¹ * ((w₀ * r) * v * (w₀ * r)⁻¹ * v⁻¹) := by group
        rw [e]
        exact mul_mem (inv_mem (by
          rw [hR.commT₁ _ hw₀ _ hνr, mul_inv_cancel_right]; exact hνr)) hyv
    rw [hR.inf] at hνw₀
    obtain ⟨w₁, hw₁, hw₁eq⟩ := h.exists_eq_comm_of_outer_of_card_sylow hS2 hvT hv2 hvS hw₀ hνw₀
    refine ⟨w₁, mem_sup_left hw₁, ?_⟩
    rw [← hw₁eq, inv_mul_cancel_left]
    exact hr
  have hfreeM : ∀ x ∈ U₁, v * x * v⁻¹ * x⁻¹ ∈ R₂ →
      ∃ w ∈ U₁, (w * v * w⁻¹ * v⁻¹)⁻¹ * x ∈ R₂ := by
    intro x hx hxv
    have hxv' : x * v * x⁻¹ * v⁻¹ ∈ R₂ := by
      have := inv_mem hxv
      rwa [show (v * x * v⁻¹ * x⁻¹)⁻¹ = x * v * x⁻¹ * v⁻¹ by group] at this
    exact exists_comm_mem_of_free_layers (H := szT₁ L T ⊔ R₂) le_sup_right
      (sup_le (le_sup_left.trans hU.le) (le_sup_right.trans hU.le)) hNc hU.comm_mem hM2 htM hvM
      htN hvN htt hvv hvt.symm hkerτ hsurjτ hfreeH hx hxv'
  have hu2' : u * v * (u * v) = 1 := by rw [← sq]; exact hu2
  exact conj_of_free_series hvv hvR (le_sup_right.trans hU.le) (fun r hr => by
    rw [← sq]; exact hU.sq_R₂ r hr) hU.comm_mem hM2 hfreeN hfreeM hu hu2'

end Certificates

end CFSG.SeitzReduction.RankOne
