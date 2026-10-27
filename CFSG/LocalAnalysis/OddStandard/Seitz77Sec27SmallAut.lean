module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Defs
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.GH74.KGroups.Generic6
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.KGroups

theorem card_mulAut_alternating_five_dvd :
    Nat.card (MulAut (alternatingGroup (Fin 5))) ∣ 120 := by
  have hsurj : Function.Surjective
      (MulAut.conjNormal : Equiv.Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5))) := by
    intro f
    obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation (n := 5) (Or.inl rfl) f
    refine ⟨σ, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [MulAut.conjNormal_apply, hσ]
  have h := Subgroup.card_dvd_of_surjective hsurj
  have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  rwa [hc] at h

theorem Local27.nonempty_equiv {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (c : Local27 N X t) :
    Nonempty (↥X ≃* alternatingGroup (Fin 5)) :=
  CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ c.model

theorem Local27.card_X {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (c : Local27 N X t) : Nat.card ↥X = 60 := by
  obtain ⟨e⟩ := c.nonempty_equiv
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem Local27.five_dvd_centralizer {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (c : Local27 N X t) :
    5 ∣ Nat.card ↥(centralizer ({t} : Set N)) := by
  have hle : X ≤ centralizer ({t} : Set N) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact c.t_cent x hx
  have h := Subgroup.card_dvd_of_le hle
  rw [c.card_X] at h
  exact (by norm_num : 5 ∣ 60).trans h

theorem Local27.centralizer_le_normalizer {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (c : Local27 N X t) : centralizer ({t} : Set N) ≤ normalizer (X : Set N) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => c.X_normal g hg x hx, fun hx => ?_⟩
  have h := c.X_normal g⁻¹ ((centralizer ({t} : Set N)).inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem Local27.padicValNat_centralizer_le {N : Type} [Group N] [Finite N] {X : Subgroup N}
    {t : N} (c : Local27 N X t) :
    padicValNat 2 (Nat.card ↥(centralizer ({t} : Set N))) ≤ 4 := by
  set D := centralizer ({t} : Set N) with hD
  have hDX : D ≤ normalizer (X : Set N) := c.centralizer_le_normalizer
  let φ : ↥D →* MulAut ↥X := (normalizerMonoidHom X).comp (Subgroup.inclusion hDX)
  have hφ : ∀ (k : ↥D) (x : ↥X), ((φ k x : ↥X) : N) = (k : N) * x * (k : N)⁻¹ := fun k x => rfl
  have hker : Nat.card φ.ker = Nat.card ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N)) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1 : N), k.1.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
        invFun := fun q => ⟨⟨(q.1 : N), (Subgroup.mem_inf.1 q.2).1⟩, ?_⟩
        left_inv := fun k => by ext; rfl
        right_inv := fun q => by ext; rfl }
    · have h := congrArg (fun a : MulAut ↥X => ((a ⟨x, hx⟩ : ↥X) : N)) (MonoidHom.mem_ker.1 k.2)
      simp only [hφ, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    · rw [MonoidHom.mem_ker]
      ext ⟨x, hx⟩
      have h := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 q.2).2 x hx
      rw [hφ, MulAut.one_apply]
      show (q.1 : N) * x * (q.1 : N)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact h.symm
  have hrange : Nat.card φ.range ∣ 120 := by
    obtain ⟨e⟩ := c.nonempty_equiv
    have h1 : Nat.card φ.range ∣ Nat.card (MulAut ↥X) := Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (MulAut ↥X) = Nat.card (MulAut (alternatingGroup (Fin 5))) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    rw [h2] at h1
    exact h1.trans card_mulAut_alternating_five_dvd
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hpos1 : 0 < Nat.card φ.ker := Nat.card_pos
  have hpos2 : 0 < Nat.card φ.range := Nat.card_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 (Nat.card ↥D) = padicValNat 2 (Nat.card φ.ker) +
      padicValNat 2 (Nat.card φ.range) := by
    rw [← hmul]
    exact padicValNat.mul hpos1.ne' hpos2.ne'
  have hk : padicValNat 2 (Nat.card φ.ker) = 1 := by rw [hker]; exact c.cent_two
  have hr : padicValNat 2 (Nat.card φ.range) ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h16 : 2 ^ 4 ∣ Nat.card φ.range := (padicValNat_dvd_iff_le hpos2.ne').2 hlt
    have := h16.trans hrange
    revert this
    norm_num
  omega

theorem exists_embedding_of_model {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (o : OneComp27 N X t) {G : Type} [Group G] (M : AutModel ↥(layer N) G) (hPA : M.P ≤ M.A) :
    ∃ ρ : N →* G, Function.Injective ρ ∧ (∀ n, ρ n ∈ M.A) ∧ (layer N).map ρ = M.P := by
  have hch : (layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (layer N).Normal := inferInstance
  have key : ∀ (x : N) (hx : x ∈ layer N),
      M.actHom (layer N) x = ((M.e ⟨x, hx⟩ : M.P) : G) := by
    intro x hx
    have hsx := M.actHom_spec (layer N) x
    have hAx := M.actHom_mem (layer N) x
    generalize M.actHom (layer N) x = σ at hsx hAx ⊢
    generalize hτ : ((M.e ⟨x, hx⟩ : M.P) : G) = τ
    have hτA : τ ∈ M.A := hτ ▸ hPA (M.e ⟨x, hx⟩).2
    have h1 : τ⁻¹ * σ = 1 := by
      refine M.centralizer_trivial (M.A.mul_mem (M.A.inv_mem hτA) hAx) ?_
      intro y hy
      obtain ⟨z, hz⟩ := M.e.surjective ⟨y, hy⟩
      have hyz : y = ((M.e z : M.P) : G) := (congrArg Subtype.val hz).symm
      have hs := hsx z
      have hc : (MulAut.conjNormal x z : ↥(layer N)) = ⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [hc, map_mul, map_mul, map_inv] at hs
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ] at hs
      have hs' : σ * ((M.e z : M.P) : G) = τ * ((M.e z : M.P) : G) * τ⁻¹ * σ := by
        rw [hs]
        group
      rw [hyz]
      calc τ⁻¹ * σ * ((M.e z : M.P) : G) = τ⁻¹ * (σ * ((M.e z : M.P) : G)) := by group
        _ = τ⁻¹ * (τ * ((M.e z : M.P) : G) * τ⁻¹ * σ) := by rw [hs']
        _ = ((M.e z : M.P) : G) * (τ⁻¹ * σ) := by group
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  refine ⟨M.actHom (layer N), M.actHom_injective (layer N) o.cent_bot,
    M.actHom_mem (layer N), ?_⟩
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [key x hx]
    exact (M.e ⟨x, hx⟩).2
  · intro hg
    obtain ⟨y, hy⟩ := M.e.surjective ⟨g, hg⟩
    exact ⟨y, y.2, by rw [key y y.2]; exact congrArg Subtype.val hy⟩

@[expose] def centralizerEmbedding {N G : Type*} [Group N] [Group G] (ρ : N →* G) (A : Subgroup G)
    (hA : ∀ n, ρ n ∈ A) (t : N) :
    ↥(centralizer ({t} : Set N)) →* ↥(centralizer ({ρ t} : Set G) ⊓ A) where
  toFun x := ⟨ρ x, Subgroup.mem_inf.2 ⟨by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have h := Subgroup.mem_centralizer_iff.1 x.2 t (Set.mem_singleton t)
    rw [← map_mul, ← map_mul, h], hA x⟩⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem centralizerEmbedding_injective {N G : Type*} [Group N] [Group G] (ρ : N →* G)
    (hρ : Function.Injective ρ) (A : Subgroup G) (hA : ∀ n, ρ n ∈ A) (t : N) :
    Function.Injective (centralizerEmbedding ρ A hA t) := by
  intro a b hab
  have h : ρ a = ρ b := congrArg Subtype.val hab
  exact Subtype.ext (hρ h)

theorem centralizerEmbedding_surjective {N G : Type*} [Group N] [Group G] (ρ : N →* G)
    (hρ : Function.Injective ρ) (A : Subgroup G) (hA : ∀ n, ρ n ∈ A) (t : N)
    (hr : ρ.range = A) : Function.Surjective (centralizerEmbedding ρ A hA t) := by
  rintro ⟨a, ha⟩
  obtain ⟨hac, haA⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨n, rfl⟩ : a ∈ ρ.range := hr ▸ haA
  refine ⟨⟨n, ?_⟩, Subtype.ext rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  have h := Subgroup.mem_centralizer_iff.1 hac (ρ t) (Set.mem_singleton _)
  exact hρ (by rw [map_mul, map_mul]; exact h)

theorem false_of_census_index_two {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (c : Local27 N X t) {G : Type} [Group G] [Finite G] (ρ : N →* G)
    (hρ : Function.Injective ρ) (A P : Subgroup G) (hA : ∀ n, ρ n ∈ A)
    (hP : (layer N).map ρ = P) (hcard : Nat.card A = 2 * Nat.card P)
    (hcens : ρ t * ρ t = 1 → ρ t ≠ 1 →
      5 ∣ Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ A) →
        ρ t ∉ P ∧ 2 ^ 5 ∣ Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ A)) : False := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [c.t_order, sq] at this
  have ht1 : t ≠ 1 := by
    intro h
    have := c.t_order
    rw [h, orderOf_one] at this
    omega
  have ht'2 : ρ t * ρ t = 1 := by rw [← map_mul, ht2, map_one]
  have ht'1 : ρ t ≠ 1 := fun h => ht1 (hρ (by rw [h, map_one]))
  have hdvd : Nat.card ↥(centralizer ({t} : Set N)) ∣
      Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ A) :=
    Subgroup.card_dvd_of_injective _ (centralizerEmbedding_injective ρ hρ A hA t)
  obtain ⟨htP, h32⟩ := hcens ht'2 ht'1 (c.five_dvd_centralizer.trans hdvd)
  have hrA : ρ.range ≤ A := by
    rintro _ ⟨n, rfl⟩
    exact hA n
  have hPr : P ≤ ρ.range := by
    rw [← hP]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hr : ρ.range = A := by
    have h1 : Nat.card P ∣ Nat.card ρ.range := Subgroup.card_dvd_of_le hPr
    have h2 : Nat.card ρ.range ∣ Nat.card A := Subgroup.card_dvd_of_le hrA
    obtain ⟨m, hm⟩ := h1
    have hpos : 0 < Nat.card P := Nat.card_pos
    rw [hm, hcard] at h2
    have hm2 : m ∣ 2 := by
      rw [mul_comm 2] at h2
      exact Nat.dvd_of_mul_dvd_mul_left hpos h2
    rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with h | h
    · exfalso
      rw [h, mul_one] at hm
      have hle : ρ.range ≤ P :=
        Subgroup.eq_of_le_of_card_ge hPr (by rw [hm]) ▸ le_refl _
      exact htP (hle ⟨t, rfl⟩)
    · exact Subgroup.eq_of_le_of_card_ge hrA (by rw [hcard, hm, h, mul_comm])
  have hbij := Equiv.ofBijective _ ⟨centralizerEmbedding_injective ρ hρ A hA t,
    centralizerEmbedding_surjective ρ hρ A hA t hr⟩
  have heq : Nat.card ↥(centralizer ({t} : Set N)) =
      Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ A) := Nat.card_congr hbij
  rw [← heq] at h32
  have hpos : 0 < Nat.card ↥(centralizer ({t} : Set N)) := Nat.card_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv := (padicValNat_dvd_iff_le hpos.ne').1 h32
  have := c.padicValNat_centralizer_le
  omega

theorem four_dvd_card_of_commuting_involutions {B : Type*} [Group B] [Finite B] (a b : B)
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : a * b = b * a) : 4 ∣ Nat.card B := by
  classical
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : a * b ≠ 1 := by
    intro h
    exact hab (by rw [← hbi]; exact eq_inv_of_mul_eq_one_left h)
  have h2 : a * b ≠ a := by
    intro h
    exact hb1 (by simpa using h)
  have h3 : a * b ≠ b := by
    intro h
    exact ha1 (by simpa using h)
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [← mul_assoc, ← hc, mul_assoc, hb, mul_one]
  have e3 : (a * b) * a = b := by rw [hc, mul_assoc, ha, mul_one]
  have e4 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : (a * b) * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
  have e6 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right e5
  have hba : b * a = a * b := hc.symm
  let S : Finset B := {1, a, b, a * b}
  let K : Subgroup B :=
    { carrier := ↑S
      mul_mem' := by
        intro x y hx hy
        simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
          simp [hx, hy, ha, hb, hba, e1, e2, e3, e4, e5]
      one_mem' := by simp [S]
      inv_mem' := by
        intro x hx
        simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢
        rcases hx with hx | hx | hx | hx <;> simp [hx, hai, hbi, e6] }
  have hS : S.card = 4 := by
    simp [S, Finset.card_insert_of_notMem, ha1.symm, hb1.symm, h1.symm, hab, h2.symm, h3.symm]
  have hK : Nat.card K = 4 := by
    rw [← hS]
    exact Nat.subtype_card S (fun x => Iff.rfl)
  rw [← hK]
  exact Subgroup.card_subgroup_dvd_card K

theorem card_centralizer_eq_range {N G : Type*} [Group N] [Group G] (ρ : N →* G)
    (hρ : Function.Injective ρ) (t : N) :
    Nat.card ↥(centralizer ({t} : Set N)) =
      Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ ρ.range) :=
  Nat.card_congr (Equiv.ofBijective _
    ⟨centralizerEmbedding_injective ρ hρ ρ.range (fun n => ⟨n, rfl⟩) t,
      centralizerEmbedding_surjective ρ hρ ρ.range (fun n => ⟨n, rfl⟩) t rfl⟩)

theorem eq_or_eq_of_index_two {G : Type*} [Group G] [Finite G] {K P R : Subgroup G}
    (hPK : P ≤ K) (hKR : K ≤ R) (hcard : Nat.card R = 2 * Nat.card P) : K = P ∨ K = R := by
  have h1 : Nat.card P ∣ Nat.card K := Subgroup.card_dvd_of_le hPK
  have h2 : Nat.card K ∣ Nat.card R := Subgroup.card_dvd_of_le hKR
  obtain ⟨m, hm⟩ := h1
  have hpos : 0 < Nat.card P := Nat.card_pos
  rw [hm, hcard] at h2
  have hm2 : m ∣ 2 := by
    rw [mul_comm 2] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hpos h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with h | h
  · left
    rw [h, mul_one] at hm
    exact (Subgroup.eq_of_le_of_card_ge hPK (by rw [hm])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge hKR (by rw [hcard, hm, h, mul_comm])

theorem false_of_census_J2 {N : Type} [Group N] [Finite N] {X : Subgroup N} {t : N}
    (c : Local27 N X t) {G : Type} [Group G] [Finite G]
    (ρ : N →* G) (hρ : Function.Injective ρ) (R P : Subgroup G) (hR : ∀ n, ρ n ∈ R)
    (hP : (layer N).map ρ = P) (hcard : Nat.card R = 2 * Nat.card P)
    (hcens₁ : ∀ s ∈ R, s * s = 1 → s ≠ 1 →
      5 ∣ Nat.card ↥(centralizer ({s} : Set G) ⊓ R) →
        s ∈ P ∧ 2 ^ 5 ∣ Nat.card ↥(centralizer ({s} : Set G) ⊓ R))
    (hcens₂ : ∀ s ∈ P, s * s = 1 → s ≠ 1 →
      5 ∣ Nat.card ↥(centralizer ({s} : Set G) ⊓ P) →
        2 ^ 5 ∣ Nat.card ↥(centralizer ({s} : Set G) ⊓ P) ∨
          ∃ u ∈ P, u * u = 1 ∧ u ≠ 1 ∧ u ≠ s ∧
            centralizer ({s} : Set G) ⊓ P ≤ centralizer ({u} : Set G)) : False := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [c.t_order, sq] at this
  have ht1 : t ≠ 1 := by
    intro h
    have := c.t_order
    rw [h, orderOf_one] at this
    omega
  have ht'2 : ρ t * ρ t = 1 := by rw [← map_mul, ht2, map_one]
  have ht'1 : ρ t ≠ 1 := fun h => ht1 (hρ (by rw [h, map_one]))
  have hdvd : Nat.card ↥(centralizer ({t} : Set N)) ∣
      Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ R) :=
    Subgroup.card_dvd_of_injective _ (centralizerEmbedding_injective ρ hρ R hR t)
  have h5N := c.five_dvd_centralizer
  obtain ⟨htP, h32⟩ := hcens₁ (ρ t) (hR t) ht'2 ht'1 (h5N.trans hdvd)
  have hrA : ρ.range ≤ R := by
    rintro _ ⟨n, rfl⟩
    exact hR n
  have hPr : P ≤ ρ.range := by
    rw [← hP]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hpos : 0 < Nat.card ↥(centralizer ({t} : Set N)) := Nat.card_pos
  have hv := c.padicValNat_centralizer_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_eq_of_index_two hPr hrA hcard with hrP | hrR
  · have heq : Nat.card ↥(centralizer ({t} : Set N)) =
        Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ P) := by
      rw [card_centralizer_eq_range ρ hρ t, hrP]
    rcases hcens₂ (ρ t) htP ht'2 ht'1 (heq ▸ h5N) with h32' | ⟨u, huP, hu2, hu1, hut, huc⟩
    · rw [← heq] at h32'
      have := (padicValNat_dvd_iff_le hpos.ne').1 h32'
      omega
    · obtain ⟨n₀, hn₀⟩ : u ∈ ρ.range := hrP ▸ huP
      have hcomm : ∀ d ∈ centralizer ({t} : Set N), d * n₀ = n₀ * d := by
        intro d hd
        have hd' : ρ d ∈ centralizer ({ρ t} : Set G) ⊓ P := by
          refine Subgroup.mem_inf.2 ⟨?_, hrP ▸ ⟨d, rfl⟩⟩
          rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
            Subgroup.mem_centralizer_singleton_iff.1 hd]
        have h := Subgroup.mem_centralizer_singleton_iff.1 (huc hd')
        apply hρ
        rw [map_mul, map_mul, hn₀]
        exact h
      have htt : t ∈ centralizer ({t} : Set N) := Subgroup.mem_centralizer_singleton_iff.2 rfl
      have hXt : ∀ x ∈ X, x ∈ centralizer ({t} : Set N) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.2 (c.t_cent x hx)
      have htB : t ∈ centralizer ({t} : Set N) ⊓ centralizer (X : Set N) :=
        Subgroup.mem_inf.2 ⟨htt, Subgroup.mem_centralizer_iff.2 fun x hx => c.t_cent x hx⟩
      have hn₀B : n₀ ∈ centralizer ({t} : Set N) ⊓ centralizer (X : Set N) :=
        Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm t htt).symm,
          Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x (hXt x hx)⟩
      have hn₀2 : n₀ * n₀ = 1 := hρ (by rw [map_mul, hn₀, hu2, map_one])
      have hn₀1 : n₀ ≠ 1 := fun h => hu1 (by rw [← hn₀, h, map_one])
      have hn₀t : n₀ ≠ t := fun h => hut (by rw [← hn₀, h])
      have h4 := four_dvd_card_of_commuting_involutions
        (⟨t, htB⟩ : ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N))) ⟨n₀, hn₀B⟩
        (Subtype.ext ht2) (Subtype.ext hn₀2) (fun h => ht1 (congrArg Subtype.val h))
        (fun h => hn₀1 (congrArg Subtype.val h))
        (fun h => hn₀t (congrArg Subtype.val h).symm)
        (Subtype.ext (hcomm t htt))
      have hBpos : 0 < Nat.card ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N)) :=
        Nat.card_pos
      have := (padicValNat_dvd_iff_le hBpos.ne' (p := 2) (n := 2)).1 (by simpa using h4)
      have h1 := c.cent_two
      omega
  · have heq : Nat.card ↥(centralizer ({t} : Set N)) =
        Nat.card ↥(centralizer ({ρ t} : Set G) ⊓ R) := by
      rw [card_centralizer_eq_range ρ hρ t, hrR]
    rw [← heq] at h32
    have := (padicValNat_dvd_iff_le hpos.ne').1 h32
    omega

end CFSG.OddStandard.Seitz77
