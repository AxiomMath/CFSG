module

public import CFSG.Certificates.Kernel.P1Model.Facts

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.SmallOddCore

variable {n : ℕ}

theorem conj_inv_conj_eq {G : Type*} [Group G] (d x : G) : d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x := by
  group

theorem repFacts_conj {A₀ Aut : Subgroup (Equiv.Perm (Fin n))} {d t : Equiv.Perm (Fin n)}
    (hd : d ∈ normalizer (A₀ : Set (Equiv.Perm (Fin n)))) (hdA : d ∈ Aut)
    (h : RepFacts A₀ Aut t) : RepFacts A₀ Aut (d * t * d⁻¹) := by
  set f := (MulAut.conj d).toMonoidHom
  have hfi : Function.Injective f := (MulAut.conj d).injective
  have hfa : ∀ x, f x = d * x * d⁻¹ := fun x => rfl
  have hC := inf_centralizer_conj_of_mem_normalizer A₀ hd t
  rcases h with ⟨K, hle, hnorm, hcard, ⟨a, ha⟩, hfive⟩ | ⟨hout, hno⟩ |
      ⟨L, hle, hnorm, hcard, ⟨a, ha⟩, hodd, ⟨e⟩, hconfig⟩
  · refine RepFacts.small (K.map f) ?_ ?_ ?_ ⟨a, ?_⟩ ?_
    · rw [hC]
      exact map_mono hle
    · rw [hC]
      exact map_conj_le_normalizer hnorm d
    · rw [card_map_of_injective hfi]
      exact hcard
    · rw [hC, relIndex_map_map_of_injective _ _ hfi]
      exact ha
    · rw [hC, card_map_of_injective hfi]
      exact hfive
  · refine RepFacts.noA6 (fun hm => hout ?_) (fun L hL hcard hN => ?_)
    · have h1 := (mem_normalizer_iff.mp (inv_mem hd) _).mp hm
      rwa [conj_inv_conj_eq] at h1
    · have hC' := inf_centralizer_conj_of_mem_normalizer A₀ (inv_mem hd) (d * t * d⁻¹)
      rw [conj_inv_conj_eq] at hC'
      refine hno (L.map (MulAut.conj d⁻¹).toMonoidHom) ?_ ?_ ?_
      · rw [hC']
        exact map_mono hL
      · rw [card_map_of_injective (MulAut.conj d⁻¹).injective]
        exact hcard
      · rw [hC']
        exact map_conj_le_normalizer hN d⁻¹
  · refine RepFacts.a6 (L.map f) ?_ ?_ ?_ ⟨a, ?_⟩ ?_
      ⟨(L.equivMapOfInjective f hfi).symm.trans e⟩ ?_
    · rw [hC]
      exact map_mono hle
    · rw [hC]
      exact map_conj_le_normalizer hnorm d
    · rw [card_map_of_injective hfi]
      exact hcard
    · rw [hC, relIndex_map_map_of_injective _ _ hfi]
      exact ha
    · rw [hC, ← map_oddPart_of_injective f hfi]
      exact map_mono hodd
    · rintro v hv hv2 hvt ⟨_, ⟨l, hl, rfl⟩, hl2, hl8⟩
      rw [hfa] at hl2 hl8
      have hv₀ : d⁻¹ * v * d ∈ Aut := mul_mem (mul_mem (inv_mem hdA) hv) hdA
      have hv₀t : d⁻¹ * v * d * t = t * (d⁻¹ * v * d) := by
        calc d⁻¹ * v * d * t = d⁻¹ * (v * (d * t * d⁻¹)) * d := by group
          _ = d⁻¹ * ((d * t * d⁻¹) * v) * d := by rw [hvt]
          _ = t * (d⁻¹ * v * d) := by group
      have hl2' : orderOf l = 2 := by
        have e1 : l = d⁻¹ * (d * l * d⁻¹) * d := by group
        rw [e1, orderOf_conj_inv, hl2]
      have hl8' : orderOf (d⁻¹ * v * d * l) = 8 := by
        have e1 : d⁻¹ * v * d * l = d⁻¹ * (v * (d * l * d⁻¹)) * d := by group
        rw [e1, orderOf_conj_inv, hl8]
      have h1 := hconfig _ hv₀ (by rw [orderOf_conj_inv, hv2]) hv₀t ⟨l, hl, hl2', hl8'⟩
      have h2 := a6Normal_conj hd h1
      rwa [show d * (d⁻¹ * v * d) * d⁻¹ = v by group] at h2

theorem mem_range_T_of_mem_normalizer {P : Type*} [Group P] (M : AutModel P n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ normalizer (M.π.range : Set (Equiv.Perm (Fin n)))) :
    σ ∈ M.T.range := by
  set e := MonoidHom.ofInjective M.inj
  have hmap : M.π.range.map (MulAut.conj σ).toMonoidHom = M.π.range :=
    mem_normalizer_iff_map_conj_eq.mp hσ
  let c : M.π.range ≃* M.π.range :=
    (M.π.range.equivMapOfInjective _ (MulAut.conj σ).injective).trans
      (MulEquiv.subgroupCongr hmap)
  let α : MulAut P := (e.trans c).trans e.symm
  refine ⟨α, (M.eq_T (α := α) fun g => ?_).symm⟩
  change σ * M.π g * σ⁻¹ = M.π (e.symm (c (e g)))
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem ncard_mul_card_inf_centralizer {G : Type*} [Group G] [Finite G] (H : Subgroup G) (t : G)
    {X : Set G} (hX : ∀ x, x ∈ X ↔ ∃ h ∈ H, x = h * t * h⁻¹) :
    X.ncard * Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = Nat.card H := by
  letI : MulAction H G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp H.subtype)
  have hs : ∀ (h : H) (x : G), h • x = (h : G) * x * (h : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit H t = X := by
    ext x
    rw [MulAction.mem_orbit_iff, hX]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, hs h t⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hs _ t⟩
  have hstab : Nat.card (MulAction.stabilizer H t) =
      Nat.card ↥(H ⊓ centralizer ({t} : Set G)) := by
    have e : MulAction.stabilizer H t = (H ⊓ centralizer ({t} : Set G)).subgroupOf H := by
      ext h
      rw [MulAction.mem_stabilizer_iff, hs, mem_subgroupOf, mem_inf,
        mem_centralizer_singleton_iff]
      constructor
      · intro e
        refine ⟨h.2, ?_⟩
        calc (h : G) * t = (h : G) * t * (h : G)⁻¹ * h := by group
          _ = t * h := by rw [e]
      · rintro ⟨-, e⟩
        rw [e]
        group
    rw [e]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hstab, ← horb, ← MulAction.index_stabilizer]
  exact (MulAction.stabilizer H t).index_mul_card

theorem exists_eq_conj_of_reps {G : Type*} [Group G] [Finite G] {ng N : ℕ} (g : ℕ → G)
    (t : G) (c : ℕ → G) (hcl : ∀ i < N, ∀ k < ng, ∃ j < N, g k * c i * (g k)⁻¹ = c j)
    (hroot : ∃ i < N, c i = t) :
    ∀ h ∈ closure (g '' {k | k < ng}), ∃ i < N, c i = h * t * h⁻¹ := by
  set X : Set G := {x | ∃ i < N, c i = x}
  have hall : ∀ h ∈ closure (g '' {k | k < ng}), ∀ y ∈ X, h * y * h⁻¹ ∈ X := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rintro y ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hcl i hi k hk
      exact ⟨j, hj, e.symm⟩
    | one =>
      intro y hy
      rw [one_mul, inv_one, mul_one]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := CFSG.KC.OrbGroup.surj_of_mapsTo (fun z => a * z * a⁻¹)
        (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  intro h hh
  obtain ⟨i, hi, e⟩ := hroot
  exact hall h hh t ⟨i, hi, e⟩

theorem card_inf_centralizer_of_reps {G : Type*} [Group G] [Finite G] {ng N : ℕ} (g : ℕ → G)
    (t : G) (c : ℕ → G)
    (hreach : ∀ i < N, ∃ h ∈ closure (g '' {k | k < ng}), c i = h * t * h⁻¹)
    (hcl : ∀ i < N, ∀ k < ng, ∃ j < N, g k * c i * (g k)⁻¹ = c j)
    (hroot : ∃ i < N, c i = t) (hinj : ∀ i < N, ∀ j < N, c i = c j → i = j) :
    N * Nat.card ↥(closure (g '' {k | k < ng}) ⊓ centralizer ({t} : Set G)) =
      Nat.card (closure (g '' {k | k < ng})) := by
  classical
  set X : Set G := {x | ∃ i < N, c i = x}
  have hall : ∀ h ∈ closure (g '' {k | k < ng}), ∀ y ∈ X, h * y * h⁻¹ ∈ X := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rintro y ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hcl i hi k hk
      exact ⟨j, hj, e.symm⟩
    | one =>
      intro y hy
      rw [one_mul, inv_one, mul_one]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := CFSG.KC.OrbGroup.surj_of_mapsTo (fun z => a * z * a⁻¹)
        (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  have hX : ∀ x, x ∈ X ↔ ∃ h ∈ closure (g '' {k | k < ng}), x = h * t * h⁻¹ := by
    intro x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hreach i hi
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨i, hi, e⟩ := hroot
      exact hall h hh t ⟨i, hi, e⟩
  have himg : X = c '' (Finset.range N : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by simpa using hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by simpa using hi, rfl⟩
  have hio : Set.InjOn c (Finset.range N : Set ℕ) :=
    fun i hi j hj e => hinj i (by simpa using hi) j (by simpa using hj) e
  have hN : X.ncard = N := by
    rw [himg, hio.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  rw [← hN]
  exact ncard_mul_card_inf_centralizer _ t hX

theorem mem_sup_zpowers_of_sq_mem {G : Type*} [Group G] {H : Subgroup G} {u : G}
    (hu : u ∈ normalizer (H : Set G)) (hu2 : u * u ∈ H) {b : G} :
    b ∈ H ⊔ zpowers u ↔ b ∈ H ∨ b * u⁻¹ ∈ H := by
  constructor
  · intro hb
    have hle : zpowers u ≤ normalizer (H : Set G) := by
      rw [zpowers_le]
      exact hu
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left H _ hle] at hb
    obtain ⟨k, hk, y, hy, rfl⟩ := hb
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    change k * u ^ j ∈ H ∨ k * u ^ j * u⁻¹ ∈ H
    have h2 : u ^ (2 : ℤ) ∈ H := by
      rw [zpow_two]
      exact hu2
    have hj : u ^ j = (u ^ (2 : ℤ)) ^ (j / 2) * u ^ (j % 2) := by
      rw [← zpow_mul, ← zpow_add]
      congr 1
      omega
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left
      rw [hj, h0, zpow_zero, mul_one]
      exact mul_mem hk (zpow_mem h2 _)
    · right
      rw [hj, h1, zpow_one, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
      exact mul_mem hk (zpow_mem h2 _)
  · rintro (hb | hb)
    · exact mem_sup_left hb
    · have e : b = b * u⁻¹ * u := by group
      rw [e]
      exact mul_mem (mem_sup_left hb) (mem_sup_right (mem_zpowers u))

theorem card_sup_zpowers_of_sq_mem {G : Type} [Group G] [Finite G] {H : Subgroup G} {u : G}
    (hu : u ∈ normalizer (H : Set G)) (hu2 : u * u ∈ H) (huH : u ∉ H) :
    Nat.card ↥(H ⊔ zpowers u) = 2 * Nat.card H := by
  have h2 : H.relIndex (H ⊔ zpowers u) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨u, mem_sup_right (mem_zpowers u), fun b hb => ?_⟩
    have hbu : b ∈ H ∨ b * u ∈ H := by
      rcases (mem_sup_zpowers_of_sq_mem hu hu2).1 hb with h | h
      · exact Or.inl h
      · right
        have e : b * u = b * u⁻¹ * (u * u) := by group
        rw [e]
        exact mul_mem h hu2
    rcases hbu with hbH | hbu
    · refine Or.inr ⟨hbH, fun hba => huH ?_⟩
      have := mul_mem (inv_mem hbH) hba
      simpa using this
    · refine Or.inl ⟨hbu, fun hbH => huH ?_⟩
      have := mul_mem (inv_mem hbH) hbu
      simpa using this
  have h3 := relIndex_mul_card_of_le (le_sup_left : H ≤ H ⊔ zpowers u)
  rw [h2] at h3
  exact h3.symm

end CFSG.ComponentClassification.HarrisLit.P1
