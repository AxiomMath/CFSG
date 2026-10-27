module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndFieldBasic
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LieType.Chevalley.DiagramFixedModelSchreier
public import CFSG.LieType.Chevalley.ExceptionalSmallRankSchreier
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.OuterAutomorphisms

section General

variable {G : Type*} [Group G]

theorem card_centralizer_dvd_two_mul_card_mulAut [Finite G] {L : Subgroup G} {C : Type*}
    [Group C] (e : L ≃* C) {t : G} (ht : orderOf t = 2)
    (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    Nat.card (centralizer ({t} : Set G)) ∣ 2 * Nat.card (MulAut C) := by
  rw [E6Pilot.card_eq_two_mul_card_range e ht hKt hN le_rfl (mem_centralizer_singleton_iff.2 rfl)]
  exact Nat.mul_dvd_mul_left 2 (Subgroup.card_subgroup_dvd_card _)

theorem inf_centralizer_eq_map_eqLocus {M : Subgroup G} {X : Type*} [Group X] (e : M ≃* X)
    {t : G} (htM : t ∈ normalizer (M : Set G)) :
    M ⊓ centralizer ({t} : Set G) =
      ((normalizerMulAut e ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id X)).map
        (M.subtype.comp e.symm.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨hxM, hxt⟩
    refine ⟨e ⟨x, hxM⟩, ?_, by simp⟩
    change normalizerMulAut e ⟨t, htM⟩ (e ⟨x, hxM⟩) = e ⟨x, hxM⟩
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_normalizerMulAut_apply, MulEquiv.symm_apply_apply]
    have hxt' := mem_centralizer_singleton_iff.1 hxt
    change t * x * t⁻¹ = x
    calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [hxt']
      _ = x := by group
  · rintro ⟨b, hb, rfl⟩
    have hb' : normalizerMulAut e ⟨t, htM⟩ b = b := hb
    have h2 := congrArg (fun y => ((e.symm y : M) : G)) hb'
    simp only [coe_symm_normalizerMulAut_apply] at h2
    refine mem_inf.2 ⟨(e.symm b).2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    change ((e.symm b : M) : G) * t = t * (e.symm b : M)
    calc ((e.symm b : M) : G) * t = t * (e.symm b : M) * t⁻¹ * t := by rw [h2]
      _ = t * (e.symm b : M) := by group

theorem map_eqLocus_eq_of_conj {X : Type*} [Group X] {α η φ : MulAut X}
    (h : φ * α * φ⁻¹ = η) :
    (α.toMonoidHom.eqLocus (MonoidHom.id X)).map φ.toMonoidHom =
      η.toMonoidHom.eqLocus (MonoidHom.id X) := by
  subst h
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : α y = y := hy
    change (φ * α * φ⁻¹) (φ y) = φ y
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hy']
  · intro hx
    have hx' : (φ * α * φ⁻¹) x = x := hx
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply] at hx'
    refine ⟨φ.symm x, ?_, MulEquiv.apply_symm_apply _ _⟩
    change α (φ.symm x) = φ.symm x
    apply φ.injective
    rw [hx', MulEquiv.apply_symm_apply]

theorem exists_injective_eq_range_of_swap {M₁ M₂ : Subgroup G}
    (h₁₂ : M₂ ≤ centralizer (M₁ : Set G)) (hdisj : M₁ ⊓ M₂ = ⊥) {t : G} (ht2 : t * t = 1)
    (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) :
    ∃ φ : M₁ →* G, Function.Injective φ ∧
      (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = φ.range := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h12 : ∀ x ∈ M₁, t * x * t⁻¹ ∈ M₂ := fun x hx => by
    rw [← hswap]
    exact ⟨x, hx, rfl⟩
  have h21 : ∀ y ∈ M₂, t * y * t⁻¹ ∈ M₁ := fun y hy => by
    rw [← hswap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have e : t * ((MulAut.conj t).toMonoidHom x) * t⁻¹ = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htinv]
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht2, one_mul, mul_one]
    rw [e]
    exact hx
  have hcomm : ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (h₁₂ hb)) a ha
  let φ : M₁ →* G :=
    { toFun := fun x => (x : G) * (t * x * t⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        have h := hcomm y y.2 (t * x * t⁻¹) (h12 x x.2)
        simp only [Subgroup.coe_mul]
        calc (x : G) * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by
              group
          _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [h]
          _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group }
  have hφ : ∀ x : M₁, φ x = (x : G) * (t * x * t⁻¹) := fun _ => rfl
  refine ⟨φ, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hφ] at hx
    have hx1 : (x : G) = (t * x * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have hxM₂ : (x : G) ∈ M₂ := by
      rw [hx1]
      exact inv_mem (h12 x x.2)
    have hbot : (x : G) ∈ M₁ ⊓ M₂ := mem_inf.2 ⟨x.2, hxM₂⟩
    rw [hdisj, mem_bot] at hbot
    exact (Subgroup.mem_bot).2 (Subtype.ext hbot)
  · ext g
    constructor
    · rintro ⟨hg, hgt⟩
      have hM₁N : M₁ ≤ normalizer (M₂ : Set G) :=
        (le_centralizer_iff.1 h₁₂).trans (centralizer_le_normalizer _)
      have hg' : g ∈ ((M₁ ⊔ M₂ : Subgroup G) : Set G) := hg
      rw [coe_mul_of_left_le_normalizer_right M₁ M₂ hM₁N] at hg'
      obtain ⟨a, ha, b, hb, rfl⟩ := hg'
      have hgt' : t * (a * b) * t⁻¹ = a * b := by
        have := mem_centralizer_singleton_iff.1 hgt
        calc t * (a * b) * t⁻¹ = (a * b) * t * t⁻¹ := by rw [this]
          _ = a * b := by group
      have hsplit : t * (a * b) * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹) := by
        rw [hcomm _ (h21 b hb) _ (h12 a ha)]
        group
      rw [hsplit] at hgt'
      have hmem : a⁻¹ * (t * b * t⁻¹) ∈ M₁ ⊓ M₂ := by
        refine mem_inf.2 ⟨mul_mem (inv_mem ha) (h21 b hb), ?_⟩
        have e : a⁻¹ * (t * b * t⁻¹) = b * (t * a * t⁻¹)⁻¹ := by
          calc a⁻¹ * (t * b * t⁻¹) =
                a⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
            _ = a⁻¹ * (a * b) * (t * a * t⁻¹)⁻¹ := by rw [hgt']
            _ = b * (t * a * t⁻¹)⁻¹ := by group
        rw [e]
        exact mul_mem hb (inv_mem (h12 a ha))
      rw [hdisj, mem_bot] at hmem
      have hb' : b = t * a * t⁻¹ := by
        have e1 : t * b * t⁻¹ = a := by
          calc t * b * t⁻¹ = a * (a⁻¹ * (t * b * t⁻¹)) := by group
            _ = a := by rw [hmem, mul_one]
        calc b = t⁻¹ * (t * b * t⁻¹) * t := by group
          _ = t⁻¹ * a * t := by rw [e1]
          _ = t * a * t⁻¹ := by rw [htinv]
      exact ⟨⟨a, ha⟩, by rw [hφ, hb']⟩
    · rintro ⟨x, rfl⟩
      refine mem_inf.2 ⟨mul_mem (mem_sup_left x.2) (mem_sup_right (h12 x x.2)), ?_⟩
      have h12' : t * x * t ∈ M₂ := by simpa [htinv] using h12 x x.2
      have h := hcomm x x.2 (t * x * t) h12'
      rw [mem_centralizer_singleton_iff, hφ, htinv]
      calc (x : G) * (t * x * t) * t = ((t * x * t) * x) * t := by rw [h]
        _ = t * ((x : G) * (t * x * t)) := by group

theorem commutator_monoidHom_range_eq_of_isPerfect {H : Type*} [Group H] [Group.IsPerfect H]
    (ψ : H →* G) : ⁅ψ.range, ψ.range⁆ = ψ.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

end General

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem four_mul_lt_two_pow_two_mul {f : ℕ} (hf : 2 ≤ f) : 4 * f < 2 ^ (2 * f) := by
  induction f, hf using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
    omega

omit [Finite G] in
theorem isSolvable_outer_of_mulEquiv_F4 {K : Type} [Field K] [Finite K]
    (e : L ≃* adjointGroup .F4 K) : Group.IsSolvable (Outer L) :=
  ⟨⟨5, derivedSeries_outer_eq_bot_of_mulEquiv e
    ((exceptional_ordinary_small_rank_Schreier .F4 K).2 (Or.inl rfl))⟩⟩

theorem card_mulAut_F4 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) :
    Nat.card (MulAut (adjointGroup .F4 K)) = Nat.card (adjointGroup .F4 K) * (2 * f) := by
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have hbij : Function.Bijective (fun gk : adjointGroup ReeTag.F4.tag K × Fin (2 * f) =>
      MulAut.conj gk.1 * ReeTag.F4.finiteExceptionalAut K ^ (gk.2 : ℕ)) := by
    refine ⟨fun a b hab => ?_, fun α => ?_⟩
    · obtain ⟨c, -, hc⟩ := hNF (MulAut.conj a.1 * ReeTag.F4.finiteExceptionalAut K ^ (a.2 : ℕ))
      exact (hc a rfl).trans (hc b hab).symm
    · obtain ⟨gk, hgk, -⟩ := hNF α
      exact ⟨gk, hgk.symm⟩
  have h := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, Nat.card_fin] at h
  exact h.symm

theorem card_centralizer_dvd_F4 (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    Nat.card (centralizer ({t} : Set G)) ∣ 4 * f * CFSG.Open.ordF4 (2 ^ f) := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have hf := one_le_of_natCard_eq_two_pow hK
  have hc : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have h := card_centralizer_dvd_two_mul_card_mulAut e ht
    (centralizer_le_normalizer_of_standard hset.standard htC ht) hKt
  rw [card_mulAut_F4 hf K hK, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK] at h
  calc _ ∣ _ := h
    _ = 4 * f * CFSG.Open.ordF4 (2 ^ f) := by ring

theorem not_two_pow_dvd_card_centralizer_F4 (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ¬ 2 ^ (26 * f) ∣ Nat.card (centralizer ({t} : Set G)) := by
  intro h
  have h1 := h.trans (card_centralizer_dvd_F4 hset hK e htC ht hKt)
  obtain ⟨r, hr, hrF⟩ := (CFSG.Timmesfeld.Orders.profile_ordF4 (by omega : 1 ≤ f)).two
  rw [hrF] at h1
  have h2 : 2 ^ (2 * f) ∣ 4 * f * r := by
    have e1 : 2 ^ (26 * f) = 2 ^ (f * 24) * 2 ^ (2 * f) := by rw [← pow_add]; ring_nf
    have e2 : 4 * f * (2 ^ (f * 24) * r) = 2 ^ (f * 24) * (4 * f * r) := by ring
    rw [e1, e2] at h1
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).1 h1
  have hcop : Nat.Coprime (2 ^ (2 * f)) r :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hr)
  have h3 : 2 ^ (2 * f) ∣ 4 * f := hcop.dvd_of_dvd_mul_right h2
  have h4 : 2 ^ (2 * f) ≤ 4 * f := Nat.le_of_dvd (by omega) h3
  have h5 := four_mul_lt_two_pow_two_mul hf
  omega

end Standard

end CFSG.SeitzReduction.F4Pilot
