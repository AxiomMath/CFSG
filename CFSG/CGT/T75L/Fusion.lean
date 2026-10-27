module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIFinal2
public import CFSG.CGT.Timmesfeld75.Fusion

public section

namespace CFSG.CGT.T75L

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G} {a : G}

section Basic

variable [Finite G]

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.comm_iff_mem_normIn (h : Sec4Hyp T T₁ a T₂) {y : G}
    (hyN : y ∈ sec4N T T₁ T₂) (hyD : y ∈ classD T) (hyT : y ∉ T) {t : G} (ht : t ∈ T) :
    y * t = t * y ↔ t ∈ normIn T T₁ := by
  have hL : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({y} : Set G) := fun l hl =>
    ⟨normIn_le _ _ hl, Subgroup.mem_centralizer_singleton_iff.2
      (elemAbelian_mul_comm h.isElemAbelian_sec4N (normIn_le_sec4N_left hl) hyN)⟩
  refine ⟨fun hc => ?_, fun hl => (Subgroup.mem_centralizer_singleton_iff.1 (hL hl).2).symm⟩
  obtain ⟨g, t₀, ht₀, ht₀1, hyg⟩ := hyD
  have hU : IsWC (conjSubgroup g⁻¹ T) := h.pair.wc.conj g⁻¹
  have hyU : y ∈ conjSubgroup g⁻¹ T := by
    rw [mem_conjSubgroup, hyg]
    have e : (g⁻¹)⁻¹ * (g⁻¹ * t₀ * g) * g⁻¹ = t₀ := by group
    rw [e]
    exact ht₀
  have hy1 : y ≠ 1 := by
    intro h1
    apply ht₀1
    have : t₀ = g * y * g⁻¹ := by rw [hyg]; group
    rw [this, h1]
    group
  have hne : conjSubgroup g⁻¹ T ≠ T := fun heq => hyT (heq ▸ hyU)
  have hle : T ⊓ Subgroup.centralizer ({y} : Set G) ≤ normIn T (conjSubgroup g⁻¹ T) :=
    fun x hx => ⟨hx.1, hU.centralizer_le_normalizer hyU hy1 hx.2⟩
  have hcard : Nat.card (normIn T (conjSubgroup g⁻¹ T)) ≤ Nat.card (normIn T T₁) :=
    h.pair.card_normIn_le ⟨1, (conjSubgroup_one T).symm⟩ ⟨g⁻¹, rfl⟩ hne
  have heq : T ⊓ Subgroup.centralizer ({y} : Set G) = normIn T T₁ :=
    (Subgroup.eq_of_le_of_card_ge hL ((Subgroup.card_le_of_le hle).trans hcard)).symm
  rw [← heq]
  exact ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 hc.symm⟩

omit [Finite G] in
theorem conj_comm_iff {c e t : G} :
    (c * e * c⁻¹) * (c * t * c⁻¹) = (c * t * c⁻¹) * (c * e * c⁻¹) ↔ e * t = t * e := by
  constructor
  · intro hh
    have h1 : c * (e * t) * c⁻¹ = c * (t * e) * c⁻¹ := by
      calc c * (e * t) * c⁻¹ = (c * e * c⁻¹) * (c * t * c⁻¹) := by group
        _ = (c * t * c⁻¹) * (c * e * c⁻¹) := hh
        _ = c * (t * e) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  · intro hh
    calc (c * e * c⁻¹) * (c * t * c⁻¹) = c * (e * t) * c⁻¹ := by group
      _ = c * (t * e) * c⁻¹ := by rw [hh]
      _ = (c * t * c⁻¹) * (c * e * c⁻¹) := by group

omit [Finite G] in
theorem sec4E_subset_normD {e : G} (he : e ∈ sec4E T T₁ T₂) : e ∈ normD T := by
  obtain ⟨n, hn, d, hdD, hdR, rfl⟩ := he
  exact ⟨conj_mem_classD hdD n, (Subgroup.normalizer (T : Set G)).mul_mem
    ((Subgroup.normalizer (T : Set G)).mul_mem hn (sec4R_le_normalizer_left hdR))
    ((Subgroup.normalizer (T : Set G)).inv_mem hn)⟩

@[expose] def EClosure (T T₁ T₂ : Subgroup G) : Prop :=
  ∀ U : Subgroup G, IsPGroup 2 U → sec4R T T₁ T₂ ≤ U → U ≤ Subgroup.normalizer (T : Set G) →
    Subgroup.closure ((U : Set G) ∩ sec4E T T₁ T₂) = sec4R T T₁ T₂

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.comm_of_pGroup (h : Sec4Hyp T T₁ a T₂)
    (hE : EClosure T T₁ T₂) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVK : V ≤ Subgroup.normalizer (T : Set G)) {u v : G} (hu : u ∈ V) (hv : v ∈ V)
    (hue : u ∈ sec4E T T₁ T₂) (hve : v ∈ sec4E T T₁ T₂) (hu' : ∃ t ∈ T, u * t ≠ t * u)
    (hv' : ∃ t ∈ T, v * t ≠ t * v) :
    u * v = v * u ∧ ∀ t ∈ T, (u * t = t * u ↔ v * t = t * v) := by
  obtain ⟨U, hU2, hUK, hRU, c, hc, hcV⟩ := exists_pGroup_containing_conjSubgroup
    h.isPGroup_sec4R hV (fun d hd => sec4R_le_normalizer_left hd) hVK
  have hcl := hE U hU2 hRU hUK
  have key : ∀ {e : G}, e ∈ V → e ∈ sec4E T T₁ T₂ → (∃ t ∈ T, e * t ≠ t * e) →
      c * e * c⁻¹ ∈ sec4N T T₁ T₂ ∧ c * e * c⁻¹ ∈ classD T ∧ c * e * c⁻¹ ∉ T := by
    intro e heV hee het
    have hmemU : c * e * c⁻¹ ∈ U := hcV (conj_mem_conjSubgroup c heV)
    have hmemE : c * e * c⁻¹ ∈ sec4E T T₁ T₂ := sec4E_conj hee hc
    have hmemR : c * e * c⁻¹ ∈ sec4R T T₁ T₂ := by
      rw [← hcl]
      exact Subgroup.subset_closure ⟨hmemU, hmemE⟩
    have hND := sec4E_subset_normD hmemE
    have hnT : c * e * c⁻¹ ∉ T := by
      intro hT'
      obtain ⟨t, ht, hne⟩ := het
      apply hne
      have heT : e ∈ T := by
        have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hc) hT'
        simpa [mul_assoc] using this
      exact elemAbelian_mul_comm h.pair.wc.1 heT ht
    refine ⟨?_, hND.1, hnT⟩
    rcases h.mem_or_mem_sec4N_of_mem_sec4R hND hmemR with h1 | h1
    · exact absurd h1 hnT
    · exact h1
  obtain ⟨huN, huD, huT⟩ := key hu hue hu'
  obtain ⟨hvN, hvD, hvT⟩ := key hv hve hv'
  have hcomm : (c * u * c⁻¹) * (c * v * c⁻¹) = (c * v * c⁻¹) * (c * u * c⁻¹) :=
    elemAbelian_mul_comm h.isElemAbelian_sec4N huN hvN
  refine ⟨conj_comm_iff.1 hcomm, fun t ht => ?_⟩
  have hct : c * t * c⁻¹ ∈ T := conj_mem_of_mem_normalizer hc ht
  have h1 := h.comm_iff_mem_normIn huN huD huT hct
  have h2 := h.comm_iff_mem_normIn hvN hvD hvT hct
  have e1 : u * t = t * u ↔ (c * u * c⁻¹) * (c * t * c⁻¹) = (c * t * c⁻¹) * (c * u * c⁻¹) :=
    conj_comm_iff.symm
  have e2 : v * t = t * v ↔ (c * v * c⁻¹) * (c * t * c⁻¹) = (c * t * c⁻¹) * (c * v * c⁻¹) :=
    conj_comm_iff.symm
  rw [e1, e2, h1, h2]

end Basic

section Dihedral

variable {u v : G}

theorem dih_left (huu : u * u = 1) (hvv : v * v = 1) : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  rw [mul_inv_rev, hu, hv]
  calc u * (u * v) * u = (u * u) * v * u := by group
    _ = v * u := by rw [huu, one_mul]

theorem dih_right (huu : u * u = 1) (hvv : v * v = 1) : v * (u * v) * v⁻¹ = (u * v)⁻¹ := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  rw [mul_inv_rev, hu, hv]
  calc v * (u * v) * v = v * u * (v * v) := by group
    _ = v * u := by rw [hvv, mul_one]

theorem dih_left_pow (huu : u * u = 1) (hvv : v * v = 1) (n : ℕ) :
    u * (u * v) ^ n * u⁻¹ = ((u * v) ^ n)⁻¹ := by
  rw [← conj_pow, dih_left huu hvv, inv_pow]

theorem dih_comm_left (huu : u * u = 1) (hvv : v * v = 1) {n : ℕ}
    (hc : (u * v) ^ n * (u * v) ^ n = 1) :
    u * (u * v) ^ n = (u * v) ^ n * u := by
  have h1 : u * (u * v) ^ n * u⁻¹ = ((u * v) ^ n)⁻¹ := by
    rw [← conj_pow, dih_left huu hvv, inv_pow]
  have h2 : ((u * v) ^ n)⁻¹ = (u * v) ^ n := inv_eq_of_mul_eq_one_right hc
  rw [h2] at h1
  calc u * (u * v) ^ n = (u * (u * v) ^ n * u⁻¹) * u := by group
    _ = (u * v) ^ n * u := by rw [h1]

theorem dih_conj_v (huu : u * u = 1) (hvv : v * v = 1) (j : ℕ) :
    (u * v) ^ j * v * ((u * v) ^ j)⁻¹ = (u * v) ^ (2 * j) * v := by
  have h1 : v * ((u * v) ^ j)⁻¹ * v⁻¹ = (u * v) ^ j := by
    have : v * (u * v) ^ j * v⁻¹ = ((u * v) ^ j)⁻¹ := by
      rw [← conj_pow, dih_right huu hvv, inv_pow]
    have h3 := congrArg (fun z => z⁻¹) this
    simpa [mul_assoc] using h3
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  rw [hv] at h1
  have e : v * ((u * v) ^ j)⁻¹ = (v * ((u * v) ^ j)⁻¹ * v) * v := by
    rw [mul_assoc _ v v, hvv, mul_one]
  calc (u * v) ^ j * v * ((u * v) ^ j)⁻¹ = (u * v) ^ j * (v * ((u * v) ^ j)⁻¹) := by
        rw [mul_assoc]
    _ = (u * v) ^ j * ((v * ((u * v) ^ j)⁻¹ * v) * v) := by rw [← e]
    _ = (u * v) ^ j * ((u * v) ^ j * v) := by rw [h1]
    _ = (u * v) ^ (2 * j) * v := by rw [← mul_assoc, ← pow_add, two_mul]

end Dihedral

section LemmaC

variable [Finite G]

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.central_involution_centralizes
    (h : Sec4Hyp T T₁ a T₂) (hE : EClosure T T₁ T₂) {u v : G} (hu : u ∈ sec4E T T₁ T₂)
    (hv : v ∈ sec4E T T₁ T₂) (hu' : ∃ t ∈ T, u * t ≠ t * u) (hv' : ∃ t ∈ T, v * t ≠ t * v)
    (huu : u * u = 1) (hvv : v * v = 1) {k : ℕ}
    (hrn : (u * v) ^ (2 * k + 1) * (u * v) ^ (2 * k + 1) = 1) :
    (∀ t ∈ T, u * t = t * u → (u * v) ^ (2 * k + 1) * t = t * (u * v) ^ (2 * k + 1)) ∧
      (∀ t ∈ T, v * t = t * v → (u * v) ^ (2 * k + 1) * t = t * (u * v) ^ (2 * k + 1)) := by
  obtain ⟨c, hc⟩ : ∃ c, c = (u * v) ^ (2 * k + 1) := ⟨_, rfl⟩
  have hcomm : u * c = c * u := by
    rw [hc]
    exact dih_comm_left huu hvv hrn
  rw [← hc] at hrn ⊢
  have hKu := (sec4E_subset_normD hu).2
  have hKv := (sec4E_subset_normD hv).2
  have hKr : u * v ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).mul_mem hKu hKv
  have hδK : (u * v) ^ (k + 1) ∈ Subgroup.normalizer (T : Set G) := Subgroup.pow_mem _ hKr _
  have hKc : c ∈ Subgroup.normalizer (T : Set G) := by
    rw [hc]
    exact Subgroup.pow_mem _ hKr _
  have hcu : c * u = (u * v) ^ (k + 1) * v * ((u * v) ^ (k + 1))⁻¹ := by
    rw [dih_conj_v huu hvv, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hc]
    calc c * u = c * (u * (v * v)) := by rw [hvv, mul_one]
      _ = c * (u * v) * v := by group
  have hcE : c * u ∈ sec4E T T₁ T₂ := by
    rw [hcu]
    exact sec4E_conj hv hδK
  have hcu' : ∃ t ∈ T, (c * u) * t ≠ t * (c * u) := by
    obtain ⟨t₀, ht₀, hne⟩ := hv'
    refine ⟨(u * v) ^ (k + 1) * t₀ * ((u * v) ^ (k + 1))⁻¹, conj_mem_of_mem_normalizer hδK ht₀,
      fun hh => hne ?_⟩
    rw [hcu] at hh
    exact conj_comm_iff.1 hh
  have hV2 : IsPGroup 2 (Subgroup.zpowers u ⊔ Subgroup.zpowers c : Subgroup G) := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_two_zpowers_of_mul_self_eq_one huu)
      (isPGroup_two_zpowers_of_mul_self_eq_one hrn) ?_
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (show Commute c u from hcomm.symm) m).eq
  have hVK : (Subgroup.zpowers u ⊔ Subgroup.zpowers c : Subgroup G) ≤
      Subgroup.normalizer (T : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hKu) (Subgroup.zpowers_le.2 hKc)
  have huV : u ∈ (Subgroup.zpowers u ⊔ Subgroup.zpowers c : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hcuV : c * u ∈ (Subgroup.zpowers u ⊔ Subgroup.zpowers c : Subgroup G) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) huV
  have hB := h.comm_of_pGroup hE hV2 hVK huV hcuV hu hcE hu' hcu'
  have part1 : ∀ t ∈ T, u * t = t * u → c * t = t * c := by
    intro t ht htu
    have h1 : (c * u) * t = t * (c * u) := (hB.2 t ht).1 htu
    have h2 : (c * t) * u = (t * c) * u := by
      calc (c * t) * u = c * (t * u) := by rw [mul_assoc]
        _ = c * (u * t) := by rw [htu]
        _ = (c * u) * t := by rw [mul_assoc]
        _ = t * (c * u) := h1
        _ = (t * c) * u := by rw [mul_assoc]
    exact mul_right_cancel h2
  refine ⟨part1, fun t ht htv => ?_⟩
  have hδt : (u * v) ^ (k + 1) * t * ((u * v) ^ (k + 1))⁻¹ ∈ T :=
    conj_mem_of_mem_normalizer hδK ht
  have hcut : (c * u) * ((u * v) ^ (k + 1) * t * ((u * v) ^ (k + 1))⁻¹) =
      ((u * v) ^ (k + 1) * t * ((u * v) ^ (k + 1))⁻¹) * (c * u) := by
    rw [hcu]
    exact conj_comm_iff.2 htv
  have hut := (hB.2 _ hδt).2 hcut
  have hct := part1 _ hδt hut
  have hcδ : (u * v) ^ (k + 1) * c * ((u * v) ^ (k + 1))⁻¹ = c := by
    have : (u * v) ^ (k + 1) * c = c * (u * v) ^ (k + 1) := by
      rw [hc]
      exact ((Commute.refl (u * v)).pow_pow (k + 1) (2 * k + 1)).eq
    rw [this]
    group
  have hct' : ((u * v) ^ (k + 1) * c * ((u * v) ^ (k + 1))⁻¹) *
      ((u * v) ^ (k + 1) * t * ((u * v) ^ (k + 1))⁻¹) =
      ((u * v) ^ (k + 1) * t * ((u * v) ^ (k + 1))⁻¹) *
        ((u * v) ^ (k + 1) * c * ((u * v) ^ (k + 1))⁻¹) := by
    rw [hcδ]
    exact hct
  exact conj_comm_iff.1 hct'

end LemmaC

section LemmaF

variable [Finite G]

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.centralizes_of_odd (h : Sec4Hyp T T₁ a T₂)
    (hE : EClosure T T₁ T₂) {α β z : G} (hα : α * α = 1) (hβ : β * β = 1) (hz : z * z = 1)
    (hβE : β ∈ sec4E T T₁ T₂) (hzE : z ∈ sec4E T T₁ T₂) (hβ' : ∃ t ∈ T, β * t ≠ t * β)
    (hz' : ∃ t ∈ T, z * t ≠ t * z) (hαβ : α * β = β * α) (hzw : z * (α * β) = (α * β) * z)
    {j : ℕ} (hzα : (z * α) ^ (2 * j + 1) = 1) :
    ∀ t ∈ T, z * t = t * z → (α * β) * t = t * (α * β) := by
  have hww : (α * β) * (α * β) = 1 := by
    calc (α * β) * (α * β) = α * (β * α) * β := by group
      _ = α * (α * β) * β := by rw [hαβ]
      _ = (α * α) * (β * β) := by group
      _ = 1 := by rw [hα, hβ, one_mul]
  have hαw : α * (α * β) = (α * β) * α := by
    calc α * (α * β) = (α * α) * β := by group
      _ = β := by rw [hα, one_mul]
      _ = (α * β) * α := by
        calc β = β * (α * α) := by rw [hα, mul_one]
          _ = (β * α) * α := by group
          _ = (α * β) * α := by rw [hαβ]
  have hcomm : Commute (α * β) (α * z) := by
    have h1 : Commute (α * β) α := hαw.symm
    have h2 : Commute (α * β) z := hzw.symm
    exact h1.mul_right h2
  have hαz : (α * z) ^ (2 * j + 1) = 1 := by
    have : α * z = (z * α)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hα, inv_eq_of_mul_eq_one_right hz]
    rw [this, inv_pow, hzα, inv_one]
  have hβz : β * z = (α * β) * (α * z) := by
    calc β * z = (α * α) * (β * z) := by rw [hα, one_mul]
      _ = α * (α * β) * z := by group
      _ = α * (β * α) * z := by rw [hαβ]
      _ = (α * β) * (α * z) := by group
  have hpow : (β * z) ^ (2 * j + 1) = α * β := by
    rw [hβz, hcomm.mul_pow, hαz, mul_one]
    calc (α * β) ^ (2 * j + 1) = ((α * β) ^ 2) ^ j * (α * β) := by rw [pow_succ, pow_mul]
      _ = α * β := by rw [pow_two, hww, one_pow, one_mul]
  have hrn : (β * z) ^ (2 * j + 1) * (β * z) ^ (2 * j + 1) = 1 := by
    rw [hpow]
    exact hww
  have hC := h.central_involution_centralizes hE hβE hzE hβ' hz' hβ hz hrn
  rw [hpow] at hC
  exact hC.2

omit [Finite G] in
theorem exists_noncomm_conj {u δ : G} (hδ : δ ∈ Subgroup.normalizer (T : Set G))
    (hu : ∃ t ∈ T, u * t ≠ t * u) : ∃ t ∈ T, (δ * u * δ⁻¹) * t ≠ t * (δ * u * δ⁻¹) := by
  obtain ⟨t₀, ht₀, hne⟩ := hu
  exact ⟨δ * t₀ * δ⁻¹, conj_mem_of_mem_normalizer hδ ht₀, fun hh => hne (conj_comm_iff.1 hh)⟩

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.false_of_two_pow_dvd (h : Sec4Hyp T T₁ a T₂)
    (hE : EClosure T T₁ T₂) {x α : G} (hx : x * x = 1) (hα : α * α = 1)
    (hxE : x ∈ sec4E T T₁ T₂) (hαE : α ∈ sec4E T T₁ T₂) (hx' : ∃ t ∈ T, x * t ≠ t * x)
    (hα' : ∃ t ∈ T, α * t ≠ t * α) {e o : ℕ} (he : 2 ≤ e) (ho : Odd o)
    (hm : orderOf (x * α) = 2 ^ e * o) : False := by
  obtain ⟨j, hj⟩ := ho
  have hKx := (sec4E_subset_normD hxE).2
  have hKα := (sec4E_subset_normD hαE).2
  have hKr : x * α ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).mul_mem hKx hKα
  have hm0 : 0 < o := by omega
  have hpm : (x * α) ^ (2 ^ e * o) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hq : 2 ^ (e' + 1) * o = 2 * (2 ^ e' * o) := by ring
  have hqo : o ≤ 2 ^ e' * o := Nat.le_mul_of_pos_left o (Nat.two_pow_pos e')
  have hm2 : 2 * (2 ^ e' * o) = 2 ^ (e' + 1) * o := by ring
  set q := 2 ^ e' * o with hqdef
  set i := q - j with hi
  have h2i : 2 * i + o = 2 * q + 1 := by omega
  have hδK : (x * α) ^ i ∈ Subgroup.normalizer (T : Set G) := Subgroup.pow_mem _ hKr _
  have hyE : (x * α) ^ i * α * ((x * α) ^ i)⁻¹ ∈ sec4E T T₁ T₂ := sec4E_conj hαE hδK
  have hy' := exists_noncomm_conj hδK hα'
  rw [dih_conj_v hx hα] at hyE hy'
  have hkey : x * ((x * α) ^ (2 * i) * α) = (x * α) ^ o := by
    have h1 : x * (x * α) ^ (2 * i) * x⁻¹ = ((x * α) ^ (2 * i))⁻¹ := dih_left_pow hx hα _
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    rw [hxinv] at h1
    have h2 : x * (x * α) ^ (2 * i) = ((x * α) ^ (2 * i))⁻¹ * x := by
      calc x * (x * α) ^ (2 * i) = (x * (x * α) ^ (2 * i) * x) * x := by
            calc x * (x * α) ^ (2 * i) = x * (x * α) ^ (2 * i) * (x * x) := by rw [hx, mul_one]
              _ = (x * (x * α) ^ (2 * i) * x) * x := by group
        _ = ((x * α) ^ (2 * i))⁻¹ * x := by rw [h1]
    have h3 : (x * α) ^ (2 * i) * (x * α) ^ o = x * α := by
      rw [← pow_add, h2i, pow_succ, hm2, hpm, one_mul]
    calc x * ((x * α) ^ (2 * i) * α) = (x * (x * α) ^ (2 * i)) * α := by rw [mul_assoc]
      _ = (((x * α) ^ (2 * i))⁻¹ * x) * α := by rw [h2]
      _ = ((x * α) ^ (2 * i))⁻¹ * (x * α) := by rw [mul_assoc]
      _ = (x * α) ^ o := by
        rw [inv_mul_eq_iff_eq_mul]
        exact h3.symm
  set ρ := (x * α) ^ o with hρdef
  have hρpow : ρ ^ (2 ^ (e' + 1)) = 1 := by
    rw [hρdef, ← pow_mul, mul_comm, hpm]
  have hρinv : x * ρ * x⁻¹ = ρ⁻¹ := dih_left_pow hx hα o
  have hy_eq : (x * α) ^ (2 * i) * α = x * ρ := by
    calc (x * α) ^ (2 * i) * α = x * (x * ((x * α) ^ (2 * i) * α)) := by
          rw [← mul_assoc, hx, one_mul]
      _ = x * ρ := by rw [hkey]
  have hKρ : ρ ∈ Subgroup.normalizer (T : Set G) := Subgroup.pow_mem _ hKr _
  have hV2 : IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers ρ : Subgroup G) := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_two_zpowers_of_mul_self_eq_one hx)
      (IsPGroup.of_card_dvd_pow (n := e' + 1) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hρpow)) ?_
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conjSubgroup_eq
      (conjSubgroup_eq_of_le (conjSubgroup_le_of_forall_mem ?_))
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← conj_zpow, hρinv, inv_zpow]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers ρ) k)
  have hVK : (Subgroup.zpowers x ⊔ Subgroup.zpowers ρ : Subgroup G) ≤
      Subgroup.normalizer (T : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hKx) (Subgroup.zpowers_le.2 hKρ)
  have hxV : x ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers ρ : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyV : x * ρ ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers ρ : Subgroup G) :=
    Subgroup.mul_mem _ hxV (Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ))
  rw [hy_eq] at hyE hy'
  have hB := h.comm_of_pGroup hE hV2 hVK hxV hyV hxE hyE hx' hy'
  have hρρ : ρ * ρ = 1 := by
    have h1 : x * (x * ρ) = ρ := by rw [← mul_assoc, hx, one_mul]
    have h2 : (x * ρ) * x = ρ⁻¹ := by
      rw [← hρinv, inv_eq_of_mul_eq_one_right hx]
    rw [h1, h2] at hB
    exact mul_eq_one_iff_eq_inv.2 hB.1
  have hpow2 : (x * α) ^ (o + o) = 1 := by rw [pow_add]; exact hρρ
  have hdvd : 2 ^ (e' + 1) * o ∣ 2 * o := by
    rw [← hm, two_mul]
    exact orderOf_dvd_of_pow_eq_one hpow2
  have hdvd2 : 2 ^ (e' + 1) ∣ 2 := Nat.dvd_of_mul_dvd_mul_right hm0 hdvd
  have hle : 2 ^ (e' + 1) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
  have h4 : 2 ^ 2 ≤ 2 ^ (e' + 1) := Nat.pow_le_pow_right (by norm_num) he
  omega

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.centralizes_of_dihedral (h : Sec4Hyp T T₁ a T₂)
    (hE : EClosure T T₁ T₂) {x α β : G} (hx : x * x = 1) (hα : α * α = 1) (hβ : β * β = 1)
    (hxE : x ∈ sec4E T T₁ T₂) (hαE : α ∈ sec4E T T₁ T₂) (hβE : β ∈ sec4E T T₁ T₂)
    (hx' : ∃ t ∈ T, x * t ≠ t * x) (hα' : ∃ t ∈ T, α * t ≠ t * α)
    (hβ' : ∃ t ∈ T, β * t ≠ t * β) (hαβ : α * β = β * α) (hxw : x * (α * β) = (α * β) * x) :
    ∀ t ∈ T, x * t = t * x → (α * β) * t = t * (α * β) := by
  obtain ⟨e, o, ho, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x * α)).ne'
  have hpm := pow_orderOf_eq_one (x * α)
  rw [hm] at hpm
  rcases Nat.lt_or_ge e 2 with he | he
  · obtain ⟨j, hj⟩ := ho
    interval_cases e
    ·
      rw [pow_zero, one_mul, hj] at hpm
      exact h.centralizes_of_odd hE hα hβ hx hβE hxE hβ' hx' hαβ hxw hpm
    ·
      rw [pow_one, hj] at hpm
      have hrn : (x * α) ^ (2 * j + 1) * (x * α) ^ (2 * j + 1) = 1 := by
        rw [← pow_add]
        calc (x * α) ^ (2 * j + 1 + (2 * j + 1)) = (x * α) ^ (2 * (2 * j + 1)) := by
              congr 1; ring
          _ = 1 := hpm
      have hxc : x * (x * α) ^ (2 * j + 1) = (x * α) ^ (2 * j + 1) * x :=
        dih_comm_left hx hα hrn
      have hC := h.central_involution_centralizes hE hxE hαE hx' hα' hx hα hrn
      obtain ⟨c, hc⟩ : ∃ c, c = (x * α) ^ (2 * j + 1) := ⟨_, rfl⟩
      rw [← hc] at hrn hxc hC
      have hKx := (sec4E_subset_normD hxE).2
      have hKα := (sec4E_subset_normD hαE).2
      have hKr : x * α ∈ Subgroup.normalizer (T : Set G) :=
        (Subgroup.normalizer _).mul_mem hKx hKα
      have hδK : (x * α) ^ (j + 1) ∈ Subgroup.normalizer (T : Set G) :=
        Subgroup.pow_mem _ hKr _
      have hzz : (x * c) * (x * c) = 1 := by
        calc (x * c) * (x * c) = x * (c * x) * c := by group
          _ = x * (x * c) * c := by rw [hxc]
          _ = (x * x) * (c * c) := by group
          _ = 1 := by rw [hx, hrn, one_mul]
      have hzeq : (x * α) ^ (2 * (j + 1)) * α = x * c := by
        calc (x * α) ^ (2 * (j + 1)) * α = (x * α) ^ (2 * j + 1) * ((x * α) * α) := by
              rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, mul_assoc]
          _ = c * x := by
              rw [← hc, mul_assoc, hα, mul_one]
          _ = x * c := hxc.symm
      have hzE : x * c ∈ sec4E T T₁ T₂ := by
        rw [← hzeq, ← dih_conj_v hx hα (j + 1)]
        exact sec4E_conj hαE hδK
      have hz' : ∃ t ∈ T, (x * c) * t ≠ t * (x * c) := by
        have := exists_noncomm_conj hδK hα'
        rw [dih_conj_v hx hα, hzeq] at this
        exact this
      have hrw : (x * α) * (α * β) = (α * β) * (x * α) := by
        have hαw : α * (α * β) = (α * β) * α := by
          calc α * (α * β) = (α * α) * β := by group
            _ = β := by rw [hα, one_mul]
            _ = (α * β) * α := by
              calc β = β * (α * α) := by rw [hα, mul_one]
                _ = (β * α) * α := by group
                _ = (α * β) * α := by rw [hαβ]
        calc (x * α) * (α * β) = x * (α * (α * β)) := mul_assoc _ _ _
          _ = x * ((α * β) * α) := by rw [hαw]
          _ = (x * (α * β)) * α := (mul_assoc _ _ _).symm
          _ = ((α * β) * x) * α := by rw [hxw]
          _ = (α * β) * (x * α) := mul_assoc _ _ _
      have hcw : c * (α * β) = (α * β) * c := by
        rw [hc]
        exact (Commute.pow_left hrw (2 * j + 1)).eq
      have hzw : (x * c) * (α * β) = (α * β) * (x * c) := by
        calc (x * c) * (α * β) = x * (c * (α * β)) := mul_assoc _ _ _
          _ = x * ((α * β) * c) := by rw [hcw]
          _ = (x * (α * β)) * c := (mul_assoc _ _ _).symm
          _ = ((α * β) * x) * c := by rw [hxw]
          _ = (α * β) * (x * c) := mul_assoc _ _ _
      have hzα : ((x * c) * α) ^ (2 * j + 1) = 1 := by
        have h1 : (x * c) * α = (x * α) ^ (2 * j + 2) := by
          calc (x * c) * α = (c * x) * α := by rw [hxc]
            _ = c * (x * α) := mul_assoc _ _ _
            _ = (x * α) ^ (2 * j + 1) * (x * α) := by rw [hc]
            _ = (x * α) ^ (2 * j + 2) := (pow_succ _ _).symm
        rw [h1, ← pow_mul]
        have h2 : (2 * j + 2) * (2 * j + 1) = (2 * (2 * j + 1)) * (j + 1) := by ring
        rw [h2, pow_mul, hpm, one_pow]
      have hF := h.centralizes_of_odd hE hα hβ hzz hβE hzE hβ' hz' hαβ hzw hzα
      intro t ht htx
      apply hF t ht
      have hct := hC.1 t ht htx
      calc (x * c) * t = x * (c * t) := mul_assoc _ _ _
        _ = x * (t * c) := by rw [hct]
        _ = (x * t) * c := (mul_assoc _ _ _).symm
        _ = (t * x) * c := by rw [htx]
        _ = t * (x * c) := mul_assoc _ _ _
  · exact (h.false_of_two_pow_dvd hE hx hα hxE hαE hx' hα' he ho hm).elim

end LemmaF

end CFSG.CGT.T75L
