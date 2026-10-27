module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Elem
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace GL83.PiGen

open Equiv Equiv.Perm CFSG.Open GL83.CompFam

section Shift

variable {p : ℕ} [Fact p.Prime] {j : ℕ}

@[expose] def shiftEquiv (u : Fin j → ZMod p) : Perm (Fin j × ZMod p) where
  toFun x := (x.1, x.2 + u x.1)
  invFun x := (x.1, x.2 - u x.1)
  left_inv x := by simp
  right_inv x := by simp

theorem shiftEquiv_apply (u : Fin j → ZMod p) (x : Fin j × ZMod p) :
    shiftEquiv u x = (x.1, x.2 + u x.1) := rfl

@[expose] def shiftHom : Multiplicative (Fin j → ZMod p) →* Perm (Fin j × ZMod p) where
  toFun u := shiftEquiv (Multiplicative.toAdd u)
  map_one' := by
    ext x <;> simp [shiftEquiv_apply]
  map_mul' u v := by
    ext x <;> simp [shiftEquiv_apply, add_comm, add_left_comm]

theorem shiftHom_injective : Function.Injective (shiftHom (p := p) (j := j)) := by
  intro u v h
  have : ∀ i : Fin j, Multiplicative.toAdd u i = Multiplicative.toAdd v i := by
    intro i
    have := congrArg (fun σ : Perm (Fin j × ZMod p) => (σ (i, 0)).2) h
    simpa [shiftHom, shiftEquiv_apply] using this
  exact Multiplicative.toAdd.injective (funext this)

end Shift

section Points

variable {Ω : Type*} [Fintype Ω]

theorem nonempty_fin_four_embedding (hn : 4 ≤ Fintype.card Ω) : Nonempty (Fin 4 ↪ Ω) :=
  Function.Embedding.nonempty_of_card_le (by simpa using hn)

theorem exists_blocks {p j : ℕ} [Fact p.Prime] (f : Fin 4 ↪ Ω)
    (hj : j * p + 4 ≤ Fintype.card Ω) :
    ∃ e : (Fin j × ZMod p) ↪ Ω, ∀ x, e x ∉ Set.range f := by
  classical
  have hcard : Fintype.card {x : Ω // x ∉ Set.range f} = Fintype.card Ω - 4 := by
    rw [Fintype.card_subtype_compl, Fintype.card_range]
    simp
  obtain ⟨g⟩ : Nonempty ((Fin j × ZMod p) ↪ {x : Ω // x ∉ Set.range f}) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [hcard]
      simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
      omega)
  exact ⟨g.trans (Function.Embedding.subtype _), fun x => (g x).2⟩

end Points

section Klein

@[expose] def kx : Perm (Fin 4) := swap 0 1 * swap 2 3

@[expose] def ky : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def kt : Perm (Fin 4) := swap 0 2 * swap 0 1

@[expose] def kV : Subgroup (Perm (Fin 4)) := Subgroup.zpowers kx ⊔ Subgroup.zpowers ky

theorem kx_comm_ky : kx * ky = ky * kx := by decide

theorem kx_sq' : kx ^ 2 = 1 := by decide

theorem ky_sq' : ky ^ 2 = 1 := by decide

theorem kt_cube : kt ^ 3 = 1 := by decide

theorem kx_ne_one : kx ≠ 1 := by decide

theorem sign_kx : kx ∈ alternatingGroup (Fin 4) := mem_alternatingGroup.2 (by decide)

theorem sign_ky : ky ∈ alternatingGroup (Fin 4) := mem_alternatingGroup.2 (by decide)

theorem sign_kt : kt ∈ alternatingGroup (Fin 4) := mem_alternatingGroup.2 (by decide)

theorem kt_kx : kt * kx * kt⁻¹ = kx * ky := by decide

theorem kt_ky : kt * ky * kt⁻¹ = kx := by decide

theorem kV_le_alt : kV ≤ alternatingGroup (Fin 4) :=
  sup_le ((Subgroup.zpowers_le).2 sign_kx) ((Subgroup.zpowers_le).2 sign_ky)

theorem isElemAbelian_kV : IsElemAbelian 2 kV := by
  refine isElemAbelian_sup (isElemAbelian_zpowers kx_sq') (isElemAbelian_zpowers ky_sq') ?_
  intro h hh k hk
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact ((Commute.zpow_zpow (show Commute kx ky from kx_comm_ky) m n)).eq

theorem kt_mem_normalizer : kt ∈ Subgroup.normalizer (kV : Set (Perm (Fin 4))) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hc : ∀ h ∈ Subgroup.zpowers kx, ∀ k ∈ Subgroup.zpowers ky, h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((Commute.zpow_zpow (show Commute kx ky from kx_comm_ky) m l)).eq
  obtain ⟨h, hh, k, hk, rfl⟩ := (mem_sup_of_commute hc).1 hn
  have e1 : kt * (h * k) * kt⁻¹ = (kt * h * kt⁻¹) * (kt * k * kt⁻¹) := by group
  have hkx : kx ∈ kV := Subgroup.mem_sup_left (Subgroup.mem_zpowers kx)
  have hky : ky ∈ kV := Subgroup.mem_sup_right (Subgroup.mem_zpowers ky)
  rw [e1]
  refine Subgroup.mul_mem _ ?_ ?_
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow, kt_kx]
    exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ hkx hky) m
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [← conj_zpow, kt_ky]
    exact Subgroup.zpow_mem _ hkx m

theorem kt_zpow_cases (m : ℤ) : kt ^ m = 1 ∨ kt ^ m = kt ∨ kt ^ m = kt ^ 2 := by
  have hord : orderOf kt = 3 := orderOf_eq_prime kt_cube (by decide)
  rw [← zpow_mod_orderOf, hord]
  have h3 : m % ((3 : ℕ) : ℤ) = 0 ∨ m % ((3 : ℕ) : ℤ) = 1 ∨ m % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] <;> simp

theorem eq_one_of_mem_zpowers_kt {κ : Perm (Fin 4)} (hκ : κ ∈ Subgroup.zpowers kt)
    (h0 : κ 0 = 0) : κ = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hκ
  rcases kt_zpow_cases m with h | h | h
  · exact h
  · rw [h] at h0
    exact absurd h0 (by decide)
  · rw [h] at h0
    exact absurd h0 (by decide)

end Klein

section Main

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem mem_alternatingGroup_of_pow_eq_one {m : ℕ} (hm : Odd m) {σ : Perm Ω} (h : σ ^ m = 1) :
    σ ∈ alternatingGroup Ω := by
  rw [mem_alternatingGroup]
  have h1 : (Perm.sign σ) ^ m = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, hm.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem exists_klein_elem {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (hn : 4 ≤ Fintype.card Ω) :
    ∃ V E₀ : Subgroup (Perm Ω), V ≤ alternatingGroup Ω ∧ V ≠ ⊥ ∧ IsElemAbelian 2 V ∧
      E₀ ≤ alternatingGroup Ω ∧ IsElemAbelian p E₀ ∧
      E₀ ≤ Subgroup.normalizer (V : Set (Perm Ω)) ∧
      p ^ ((Fintype.card Ω - 4) / p + if p = 3 then 1 else 0) ≤ Nat.card E₀ := by
  classical
  have hp := (Fact.out : p.Prime)
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨f⟩ := nonempty_fin_four_embedding hn
  set j := (Fintype.card Ω - 4) / p with hj
  have hjp : j * p + 4 ≤ Fintype.card Ω := by
    have h := Nat.div_mul_le_self (Fintype.card Ω - 4) p
    rw [← hj] at h
    omega
  obtain ⟨e, he⟩ := exists_blocks (p := p) (j := j) f hjp
  let ι : Perm (Fin 4) →* Perm Ω := Equiv.Perm.extendDomainHom f.toEquivRange
  let Φ : Multiplicative (Fin j → ZMod p) →* Perm Ω :=
    (Equiv.Perm.extendDomainHom e.toEquivRange).comp shiftHom
  have hι : Function.Injective ι := Equiv.Perm.extendDomainHom_injective _
  have hΦ : Function.Injective Φ :=
    (Equiv.Perm.extendDomainHom_injective _).comp shiftHom_injective
  have hdisj : ∀ u σ, Perm.Disjoint (Φ u) (ι σ) := by
    intro u σ x
    by_cases hx : x ∈ Set.range f
    · left
      have hxe : x ∉ Set.range e := by
        rintro ⟨y, rfl⟩
        exact he y hx
      exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hxe
    · right
      exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hx
  have hcomm : ∀ u σ, Φ u * ι σ = ι σ * Φ u := fun u σ => (hdisj u σ).commute.eq
  set V : Subgroup (Perm Ω) := kV.map ι with hV
  set E₁ : Subgroup (Perm Ω) := Φ.range with hE₁
  have hVA : V ≤ alternatingGroup Ω := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [mem_alternatingGroup, show ι σ = σ.extendDomain f.toEquivRange from rfl,
      Perm.sign_extendDomain]
    exact mem_alternatingGroup.1 (kV_le_alt hσ)
  have hVne : V ≠ ⊥ := by
    intro h
    have : ι kx ∈ V := ⟨kx, Subgroup.mem_sup_left (Subgroup.mem_zpowers kx), rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact kx_ne_one (hι (by rw [this, map_one]))
  have hVel : IsElemAbelian 2 V := CFSG.SectionRank.isElemAbelian_map isElemAbelian_kV ι
  have hcard1 : Nat.card E₁ = p ^ j := by
    rw [hE₁, ← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hpow : ∀ u : Multiplicative (Fin j → ZMod p), u ^ p = 1 := by
    intro u
    rw [← ofAdd_toAdd u, ← ofAdd_nsmul]
    have : p • Multiplicative.toAdd u = 0 := by
      ext i
      simp
    rw [this]
    rfl
  have hE₁el : IsElemAbelian p E₁ := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [← map_pow, hpow, map_one]
  have hE₁A : E₁ ≤ alternatingGroup Ω := by
    rintro _ ⟨u, rfl⟩
    exact mem_alternatingGroup_of_pow_eq_one hpodd (by rw [← map_pow, hpow, map_one])
  have hE₁N : E₁ ≤ Subgroup.normalizer (V : Set (Perm Ω)) := by
    rintro _ ⟨u, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨σ, hσ, rfl⟩ := hn
    rw [hcomm u σ, mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨σ, hσ, rfl⟩
  by_cases hp3' : p = 3
  · have hp3'' : p = 3 := hp3'
    set t : Perm Ω := ι kt with ht
    have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, kt_cube, map_one]
    have htA : t ∈ alternatingGroup Ω := mem_alternatingGroup_of_pow_eq_one (by decide) ht3
    have htN : t ∈ Subgroup.normalizer (V : Set (Perm Ω)) :=
      Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι kt_mem_normalizer)
    have hcE : ∀ h ∈ E₁, ∀ k ∈ Subgroup.zpowers t, h * k = k * h := by
      intro h hh k hk
      obtain ⟨u, rfl⟩ := hh
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact ((Commute.zpow_right (show Commute (Φ u) t from hcomm u kt) m)).eq
    have hι0 : ∀ κ : Perm (Fin 4), ι κ (f 0) = f (κ 0) := fun κ =>
      Equiv.Perm.viaFintypeEmbedding_apply_image κ f 0
    have hinf : E₁ ⊓ Subgroup.zpowers t = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨⟨u, rfl⟩, hxt⟩ := hx
      have hxz : Φ u ∈ (Subgroup.zpowers kt).map ι := by
        rw [MonoidHom.map_zpowers]
        exact hxt
      obtain ⟨κ, hκ, hκu⟩ := hxz
      have hfix : Φ u (f 0) = f 0 := by
        have hxe : f 0 ∉ Set.range e := by
          rintro ⟨y, hy⟩
          exact he y ⟨0, hy.symm⟩
        exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hxe
      have h1 : f (κ 0) = f 0 := by rw [← hι0, hκu, hfix]
      have h2 : κ 0 = 0 := f.injective h1
      have h3 : κ = 1 := eq_one_of_mem_zpowers_kt hκ h2
      rw [← hκu, h3, map_one]
      exact Subgroup.one_mem _
    have hordt : orderOf t = 3 := orderOf_eq_prime ht3 (by
      intro h1
      have : kt = 1 := hι (by rw [← ht, h1, map_one])
      exact absurd this (by decide))
    refine ⟨V, E₁ ⊔ Subgroup.zpowers t, hVA, hVne, hVel,
      sup_le hE₁A ((Subgroup.zpowers_le).2 htA),
      isElemAbelian_sup hE₁el (by rw [hp3'']; exact isElemAbelian_zpowers ht3) hcE,
      sup_le hE₁N ((Subgroup.zpowers_le).2 htN), ?_⟩
    have h1 : (if p = 3 then 1 else 0) = 1 := by simp [hp3'']
    rw [card_sup_of_commute_of_inf_eq_bot hcE hinf, hcard1, Nat.card_zpowers, hordt, h1,
      pow_succ, hp3'']
  · refine ⟨V, E₁, hVA, hVne, hVel, hE₁A, hE₁el, hE₁N, ?_⟩
    have h0 : (if p = 3 then 1 else 0) = 0 := by simp [hp3']
    rw [h0, add_zero, hcard1]

end Main

end GL83.PiGen
