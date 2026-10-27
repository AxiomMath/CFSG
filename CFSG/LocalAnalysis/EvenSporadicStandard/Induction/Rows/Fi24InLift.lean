module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InBase
public import CFSG.Fischer.Aut.Complete

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

section Perfect

variable {G : Type} [Group G]

theorem fi24in_isPerfect_of_commutator_eq {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    Group.IsPerfect ↥K := by
  have h2 : (commutator ↥K).map K.subtype = (⊤ : Subgroup ↥K).map K.subtype := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      hK]
  exact Group.isPerfect_def.2 (Subgroup.map_injective K.subtype_injective h2)

theorem fi24in_commutator_le_of_card_le [Finite G] {K C : Subgroup G} (hKC : K ≤ C)
    (hcard : Nat.card C ≤ 2 * Nat.card K) : ⁅C, C⁆ ≤ K := by
  have hc : Nat.card ↥(K.subgroupOf C) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
  have hmul := (K.subgroupOf C).card_mul_index
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h0 : (K.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : (K.subgroupOf C).index ≤ 2 := by
    rw [hc] at hmul
    nlinarith
  rcases (by omega : (K.subgroupOf C).index = 1 ∨ (K.subgroupOf C).index = 2) with h1 | h1
  · rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact (Subgroup.commutator_le_self C).trans h1
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    have h3 : ⁅(⟨x, hx⟩ : ↥C), ⟨y, hy⟩⁆ ∈ commutator ↥C := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h4 := CFSG.Fischer.commutator_le_of_index_two h1 h3
    rw [Subgroup.mem_subgroupOf] at h4
    exact h4

theorem fi24in_le_of_perfect_of_card_le [Finite G] {K C P : Subgroup G} (hKC : K ≤ C)
    (hcard : Nat.card C ≤ 2 * Nat.card K) (hP : ⁅P, P⁆ = P) (hPC : P ≤ C) : P ≤ K :=
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hPC hPC
    _ ≤ K := fi24in_commutator_le_of_card_le hKC hcard

theorem fi24in_exists_conj_of_outTwo {K C : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hout : OutTwo (↥K ⧸ center ↥K)) (hKC : K ≤ C) (hNC : C ≤ normalizer (K : Set G))
    (hcent : ∀ z : G, (∀ k ∈ K, z * k = k * z) → z ∈ K) {σ : G} (hσ : σ ∈ C) (hσK : σ ∉ K)
    (α : MulAut ↥K) : ∃ y ∈ C, ∀ k : ↥K, ((α k : ↥K) : G) = y * k * y⁻¹ := by
  have : Group.IsPerfect ↥K := fi24in_isPerfect_of_commutator_eq hK
  set ρ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K with hρ
  have hρinj : Function.Injective ρ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥K
  have hρconj : ∀ x : ↥K, ρ (MulAut.conj x) = MulAut.conj ((x : ↥K) : ↥K ⧸ center ↥K) := by
    intro x
    ext q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    show CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)
      (QuotientGroup.mk' (center ↥K) k) = _
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
    simp [MulAut.conj_apply]
  set β : MulAut ↥K := K.normalizerMonoidHom ⟨σ, hNC hσ⟩ with hβ
  have hβk : ∀ k : ↥K, ((β k : ↥K) : G) = σ * k * σ⁻¹ := fun k => rfl
  rcases hout (ρ α) (ρ β) with ⟨l, hl⟩ | ⟨l, hl⟩ | ⟨l, hl⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective l
    have h1 : α = MulAut.conj x := hρinj (by rw [hl, hρconj])
    refine ⟨(x : G), hKC x.2, fun k => ?_⟩
    rw [h1]
    rfl
  · exfalso
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective l
    have h1 : β = MulAut.conj x := hρinj (by rw [hl, hρconj])
    apply hσK
    have h2 : (x : G)⁻¹ * σ ∈ K := by
      refine hcent _ fun k hk => ?_
      have := hβk ⟨k, hk⟩
      rw [h1] at this
      have e : (x : G) * k * (x : G)⁻¹ = σ * k * σ⁻¹ := this
      calc (x : G)⁻¹ * σ * k = (x : G)⁻¹ * (σ * k * σ⁻¹) * σ := by group
        _ = (x : G)⁻¹ * ((x : G) * k * (x : G)⁻¹) * σ := by rw [e]
        _ = k * ((x : G)⁻¹ * σ) := by group
    have := K.mul_mem x.2 h2
    rwa [mul_inv_cancel_left] at this
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective l
    have h1 : α⁻¹ * β = MulAut.conj x := hρinj (by rw [map_mul, map_inv, hl, hρconj])
    have h2 : α = β * MulAut.conj x⁻¹ := by
      calc α = β * (α⁻¹ * β)⁻¹ := by group
        _ = β * MulAut.conj x⁻¹ := by rw [h1, map_inv]
    refine ⟨σ * (x : G)⁻¹, C.mul_mem hσ (C.inv_mem (hKC x.2)), fun k => ?_⟩
    rw [h2]
    show ((β (MulAut.conj x⁻¹ k) : ↥K) : G) = _
    rw [hβk]
    simp [mul_assoc]

end Perfect

section Lift

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem fi24in_exists_involution_lift (hodd : Odd (Nat.card (center X))) {K : Subgroup X}
    {y : X ⧸ center X} (hy : y ∈ bar K) (hyy : y * y = 1) :
    ∃ v ∈ K, v * v = 1 ∧ (v : X ⧸ center X) = y := by
  obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
  set m := Nat.card (center X) with hm
  obtain ⟨j, hj⟩ := hodd
  have hkk : k * k ∈ center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hyy
  have hz : (k * k) ^ m = 1 := by
    have := pow_card_eq_one' (G := ↥(center X)) (x := ⟨k * k, hkk⟩)
    exact congrArg Subtype.val this
  have hk2 : (k ^ m) * (k ^ m) = 1 := by
    rw [← (Commute.refl k).mul_pow m]
    exact hz
  refine ⟨k ^ m, pow_mem hk m, hk2, ?_⟩
  rw [QuotientGroup.mk_pow, hj, pow_succ, pow_mul, sq, hyy, one_pow, one_mul]

omit [Finite X] in
theorem fi24in_centralizer_le_normalizer_of_bar (hodd : Odd (Nat.card (center X))) {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) {u : X} (hu : u * u = 1)
    (hN : centralizer ({(u : X ⧸ center X)} : Set (X ⧸ center X)) ≤
      normalizer (bar K : Set (X ⧸ center X))) :
    centralizer ({u} : Set X) ≤ normalizer (K : Set X) := fun _ hx =>
  mem_normalizer_of_mk_mem hK
    (hN ((mem_centralizer_singleton_iff_coe hodd hu).1 hx))

end Lift

section Quotient

theorem fi24in_exists_mulAut_of_surjective {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) (α : MulAut G) (h1 : ∀ x, π x = 1 → π (α x) = 1)
    (h2 : ∀ x, π (α x) = 1 → π x = 1) : ∃ α' : MulAut Q, ∀ x, α' (π x) = π (α x) := by
  have hmap : π.ker.map (α : G →* G) = π.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact h1 y hy
    · intro hx
      refine ⟨α.symm x, h2 _ (by simpa using hx), by simp⟩
  let e : G ⧸ π.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let c : G ⧸ π.ker ≃* G ⧸ π.ker := QuotientGroup.congr π.ker π.ker α hmap
  refine ⟨e.symm.trans (c.trans e), fun x => ?_⟩
  show e (c (e.symm (π x))) = π (α x)
  have : e.symm (π x) = (x : G ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

end Quotient

section AutCover

variable {X : Type} [Group X]

theorem fi24in_exists_conj_of_aut_cover [Finite X] (hodd : Odd (Nat.card (center X)))
    {K : Subgroup X} (hK : ⁅K, K⁆ = K) {u : X} (hu : u * u = 1)
    (hbase : Fi24InBase (X ⧸ center X) (u : X ⧸ center X) (bar K)) (α : MulAut ↥K) :
    ∃ y ∈ centralizer ({u} : Set X), ∀ k : ↥K, ((α k : ↥K) : X) = y * k * y⁻¹ := by
  have hperf : Group.IsPerfect ↥K := fi24in_isPerfect_of_commutator_eq hK
  let π : ↥K →* ↥(bar K) := ((QuotientGroup.mk' (center X)).comp K.subtype).codRestrict (bar K)
    (fun k => ⟨k, k.2, rfl⟩)
  have hπval : ∀ k : ↥K, ((π k : ↥(bar K)) : X ⧸ center X) = ((k : X) : X ⧸ center X) :=
    fun _ => rfl
  have hπ : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
    exact ⟨⟨k, hk⟩, Subtype.ext rfl⟩
  have hπ1 : ∀ x : ↥K, π x = 1 ↔ (x : X) ∈ center X := fun x => by
    rw [← QuotientGroup.eq_one_iff, ← hπval, Subtype.ext_iff]
    rfl
  have hodd' := hodd
  obtain ⟨j, hj⟩ := hodd'
  set m := Nat.card (center X) with hm
  have hum : (u : X ⧸ center X) ^ m = (u : X ⧸ center X) := by
    have hu1 : (u : X ⧸ center X) * (u : X ⧸ center X) = 1 := by
      rw [← QuotientGroup.mk_mul, hu]
      rfl
    rw [hj, pow_succ, pow_mul, sq, hu1, one_pow, one_mul]
  have hpres : ∀ β : MulAut ↥K, ∀ x : ↥K, π x = 1 → π (β x) = 1 := by
    intro β x hx
    have hxz : (x : X) ∈ center X := (hπ1 x).1 hx
    have hxc : ∀ k : ↥K, x * k = k * x := fun k =>
      Subtype.ext (Subgroup.mem_center_iff.1 hxz (k : X)).symm
    have hβc : ∀ k : ↥K, β x * k = k * β x := fun k => by
      have h1 := hxc (β.symm k)
      have h2 := congrArg β h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    have hxm : x ^ m = 1 := by
      apply Subtype.ext
      show (x : X) ^ m = 1
      exact congrArg Subtype.val (pow_card_eq_one' (G := ↥(center X)) (x := ⟨(x : X), hxz⟩))
    have hβm : (β x) ^ m = 1 := by rw [← map_pow, hxm, map_one]
    have hcomm : ∀ k ∈ bar K, ((π (β x) : ↥(bar K)) : X ⧸ center X) * k =
        k * ((π (β x) : ↥(bar K)) : X ⧸ center X) := by
      intro k hk
      obtain ⟨k0, hk0, rfl⟩ := mem_bar.1 hk
      rw [hπval, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg (QuotientGroup.mk (s := center X)) (congrArg Subtype.val (hβc ⟨k0, hk0⟩))
    rcases hbase.cent _ hcomm with h1 | h1
    · exact Subtype.ext h1
    · exfalso
      have h3 : ((π (β x) : ↥(bar K)) : X ⧸ center X) ^ m = 1 := by
        rw [← Subgroup.coe_pow, ← map_pow, hβm, map_one]
        rfl
      rw [h1, hum] at h3
      exact hbase.u_ne_one h3
  obtain ⟨αb, hαb⟩ := fi24in_exists_mulAut_of_surjective π hπ α (hpres α) (fun x hx => by
    simpa using hpres α⁻¹ (α x) hx)
  obtain ⟨yb, hyb, hind⟩ := hbase.induced αb
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective yb
  have hy₀u : y₀ ∈ centralizer ({u} : Set X) := (mem_centralizer_singleton_iff_coe hodd hu).2 hyb
  have hy₀N : y₀ ∈ normalizer (K : Set X) :=
    fi24in_centralizer_le_normalizer_of_bar hodd hK hu hbase.centralizer_le_normalizer hy₀u
  refine ⟨y₀, hy₀u, ?_⟩
  set β₀ : MulAut ↥K := K.normalizerMonoidHom ⟨y₀, hy₀N⟩ with hβ₀
  have hβ₀k : ∀ k : ↥K, ((β₀ k : ↥K) : X) = y₀ * k * y₀⁻¹ := fun k => rfl
  have hβ₀inv : ∀ k : ↥K, ((β₀⁻¹ k : ↥K) : X) = y₀⁻¹ * k * y₀ := fun k => by
    have h1 : ((β₀ (β₀⁻¹ k) : ↥K) : X) = (k : X) := by rw [MulAut.apply_inv_self]
    rw [hβ₀k] at h1
    calc ((β₀⁻¹ k : ↥K) : X) = y₀⁻¹ * (y₀ * ((β₀⁻¹ k : ↥K) : X) * y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * k * y₀ := by rw [h1]
  have hcen : ∀ k : ↥K, k⁻¹ * (β₀⁻¹ * α) k ∈ center ↥K := by
    intro k
    have hz : ((k⁻¹ * (β₀⁻¹ * α) k : ↥K) : X) ∈ center X := by
      have h1 : π (k⁻¹ * (β₀⁻¹ * α) k) = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_one]
        show (((k⁻¹ * (β₀⁻¹ * α) k : ↥K) : X) : X ⧸ center X) = 1
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, hβ₀inv, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv]
        have h2 := hind (π k)
        rw [hαb, hπval, hπval] at h2
        have h3 : ((α k : ↥K) : X ⧸ center X) =
            (y₀ : X ⧸ center X) * (k : X ⧸ center X) * (y₀ : X ⧸ center X)⁻¹ := h2
        rw [h3]
        group
      exact (hπ1 _).1 h1
    exact Subgroup.mem_center_iff.2 fun k' => Subtype.ext
      (Subgroup.mem_center_iff.1 hz (k' : X))
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (G := ↥K) (β₀⁻¹ * α).toMonoidHom hcen
  intro k
  have h1 : (β₀⁻¹ * α) k = k := congrArg (fun f : ↥K →* ↥K => f k) hid
  have h2 : α k = β₀ k := by
    have := congrArg β₀ h1
    rw [MulAut.mul_apply, MulAut.apply_inv_self] at this
    exact this
  rw [h2, hβ₀k]

end AutCover

section Generate

variable {X : Type} [Group X]

theorem fi24in_sup_conj_eq_top {K : Subgroup X}
    (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X)) {g : X}
    (h : bar K ⊔ (bar K).map (MulAut.conj (g : X ⧸ center X)).toMonoidHom =
      (⊤ : Subgroup (X ⧸ center X))) :
    K ⊔ K.map (MulAut.conj g).toMonoidHom = (⊤ : Subgroup X) := by
  set M := K ⊔ K.map (MulAut.conj g).toMonoidHom with hM
  have hbarM : bar M = (⊤ : Subgroup (X ⧸ center X)) := by
    rw [hM]
    unfold bar
    rw [Subgroup.map_sup, Cover.map_map_conj]
    exact h
  have hMZ : M ⊔ center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : (x : X ⧸ center X) ∈ bar M := hbarM ▸ Subgroup.mem_top _
    obtain ⟨m, hm, z, hz, rfl⟩ := mem_bar_iff_exists_mem_mul.1 this
    exact (mem_sup_central le_rfl).2 ⟨m, hm, z, hz, rfl⟩
  rw [eq_top_iff]
  calc (⊤ : Subgroup X) = ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := hX.symm
    _ = ⁅M ⊔ center X, M ⊔ center X⁆ := by rw [hMZ]
    _ ≤ ⁅M, M⁆ := commutator_sup_central_le le_rfl
    _ ≤ M := Subgroup.commutator_le_self M

end Generate

section Data

variable {G : Type} [Group G] [Finite G]

theorem fi24in_base_of_data {J K : Subgroup G} {a : G} (ha : a ∈ J) (hKJ : K ≤ J) (haK : a ∈ K)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hKa : ∀ k ∈ K, k * a = a * k)
    (hcard : Nat.card (centralizer ({a} : Set G) ⊓ J : Subgroup G) = 2 * Nat.card K)
    (hperf : ⁅K, K⁆ = K) (hcent : ∀ z ∈ J, (∀ ℓ ∈ K, z * ℓ = ℓ * z) → z = 1 ∨ z = a)
    (hout : OutTwo (↥(K.subgroupOf J) ⧸ center ↥(K.subgroupOf J))) (houtJ : OutTwo ↥J) :
    Fi24InBase ↥J (⟨a, ha⟩ : ↥J) (K.subgroupOf J) := by
  have hCeq : centralizer ({(⟨a, ha⟩ : ↥J)} : Set ↥J) =
      (centralizer ({a} : Set G) ⊓ J).subgroupOf J := by
    ext x
    rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨congrArg Subtype.val h, x.2⟩
    · rintro ⟨h, -⟩
      exact Subtype.ext h
  have hKle : K.subgroupOf J ≤ centralizer ({(⟨a, ha⟩ : ↥J)} : Set ↥J) := fun k hk =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (hKa _ (Subgroup.mem_subgroupOf.1 hk)))
  have hcardK : Nat.card ↥(K.subgroupOf J) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv
  have hcardC : Nat.card (centralizer ({(⟨a, ha⟩ : ↥J)} : Set ↥J)) =
      2 * Nat.card ↥(K.subgroupOf J) := by
    rw [hCeq, hcardK, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : _ ≤ J)).toEquiv
  have hperf' : ⁅K.subgroupOf J, K.subgroupOf J⁆ = K.subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKJ, hperf]
  have haK' : (⟨a, ha⟩ : ↥J) ∈ K.subgroupOf J := Subgroup.mem_subgroupOf.2 haK
  have hcent' : ∀ z : ↥J, (∀ k ∈ K.subgroupOf J, z * k = k * z) → z = 1 ∨ z = ⟨a, ha⟩ := by
    intro z hz
    rcases hcent z z.2 (fun ℓ hℓ => congrArg Subtype.val
      (hz ⟨ℓ, hKJ hℓ⟩ (Subgroup.mem_subgroupOf.2 hℓ))) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  exact
  { u_sq := Subtype.ext ha2
    u_ne_one := fun h => ha1 (congrArg Subtype.val h)
    u_mem := haK'
    le_centralizer := hKle
    card_le := hcardC.le
    perfect := hperf'
    cent := hcent'
    induced := by
      intro α
      have hpos : 0 < Nat.card ↥(K.subgroupOf J) := Nat.card_pos
      obtain ⟨σ, hσC, hσK⟩ :
          ∃ σ ∈ centralizer ({(⟨a, ha⟩ : ↥J)} : Set ↥J), σ ∉ K.subgroupOf J := by
        by_contra hcon
        push Not at hcon
        have hle : centralizer ({(⟨a, ha⟩ : ↥J)} : Set ↥J) ≤ K.subgroupOf J := hcon
        have := Subgroup.card_le_of_le hle
        omega
      exact fi24in_exists_conj_of_outTwo hperf' hout hKle
        (fi24in_le_normalizer_of_card_le hKle hcardC.le)
        (fun z hz => by
          rcases hcent' z hz with h | h
          · rw [h]
            exact one_mem _
          · rw [h]
            exact haK')
        hσC hσK α
    outTwo := houtJ }

end Data

namespace Fi24InBase

variable {Y : Type} [Group Y] [Finite Y] {uY : Y} {KY : Subgroup Y}

theorem le_of_perfect_le_centralizer (h : Fi24InBase Y uY KY) {P : Subgroup Y} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ centralizer ({uY} : Set Y)) : P ≤ KY :=
  fi24in_le_of_perfect_of_card_le h.le_centralizer h.card_le hP hPC

end Fi24InBase

section Equiv

theorem fi24in_card_subgroupOf {G : Type} [Group G] {J K : Subgroup G} (h : K ≤ J) :
    Nat.card ↥(K.subgroupOf J) = Nat.card ↥K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem fi24in_base_of_equiv {Y Z : Type} [Group Y] [Group Z] [Finite Z] (e : Y ≃* Z) {a₀ : Z}
    {K₀ : Subgroup Z} (hbase : Fi24InBase Z a₀ K₀) {uY : Y} {KY : Subgroup Y} (c : Z)
    (hc : e uY = c * a₀ * c⁻¹) (hKu : ∀ k ∈ KY, k * uY = uY * k) (hKp : ⁅KY, KY⁆ = KY)
    (hcard : Nat.card K₀ ≤ Nat.card KY) : Fi24InBase Y uY KY := by
  let f : Y ≃* Z := e.trans (MulAut.conj c⁻¹)
  have hfu : f uY = a₀ := by
    show c⁻¹ * e uY * c⁻¹⁻¹ = a₀
    rw [hc]
    group
  set P : Subgroup Z := KY.map f.toMonoidHom with hP
  have hPc : P ≤ centralizer ({a₀} : Set Z) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff]
    show f k * a₀ = a₀ * f k
    rw [← hfu, ← map_mul, ← map_mul, hKu k hk]
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hKp]
  have hPK : P ≤ K₀ := hbase.le_of_perfect_le_centralizer hPperf hPc
  have hPcard : Nat.card P = Nat.card KY := Subgroup.card_map_of_injective f.injective
  have hPeq : P = K₀ := Subgroup.eq_of_le_of_card_ge hPK (by rw [hPcard]; exact hcard)
  have h := Fi24InBase.of_mulEquiv f.symm hbase
  have h1 : f.symm a₀ = uY := by
    rw [← hfu]
    exact f.symm_apply_apply uY
  have h2 : K₀.map f.symm.toMonoidHom = KY := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hPeq] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      simpa using hk
    · intro hx
      refine ⟨f x, ?_, by simp⟩
      rw [← hPeq]
      exact ⟨x, hx, rfl⟩
  rwa [h1, h2] at h

end Equiv

end CFSG.EvenSporadicStandard.Induction
