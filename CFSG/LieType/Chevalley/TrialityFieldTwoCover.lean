module

public import CFSG.LieType.Chevalley.TrialityFieldTwoRelations
public import CFSG.LocalAnalysis.ComponentInitial.EvenPairingCover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSylow

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityFieldTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Chevalley.TrialityCover
  CFSG.LieType.Chevalley.TwistedE6Cover CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem commute_of_mem_closure_of_commute {X : Set G} (hX : ∀ x ∈ X, ∀ y ∈ X, Commute x y)
    {a b : G} (ha : a ∈ Subgroup.closure X) (hb : b ∈ Subgroup.closure X) : Commute a b := by
  have h1 : ∀ x ∈ X, ∀ b ∈ Subgroup.closure X, Commute x b := by
    intro x hx b hb
    induction hb using Subgroup.closure_induction with
    | mem y hy => exact hX x hx y hy
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx b hb
  | one => exact Commute.one_left b
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem card_closure_singleton_le {y : G} (hy : y * y = 1) :
    Nat.card (Subgroup.closure ({y} : Set G)) ≤ 2 := by
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy))

theorem card_closure_union_le [Finite G] {X Y : Set G} {q : ℕ}
    (hX : Nat.card (Subgroup.closure X) ≤ q) (hinv : ∀ x ∈ X, x * x = 1)
    (hconj : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Subgroup.closure Y) :
    Nat.card (Subgroup.closure (X ∪ Y)) ≤ q * Nat.card (Subgroup.closure Y) := by
  rw [Subgroup.closure_union]
  have hN : Subgroup.closure X ≤ Subgroup.normalizer (Subgroup.closure Y : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    have hfwd : ∀ h ∈ Subgroup.closure Y, x * h * x⁻¹ ∈ Subgroup.closure Y := fun h hh =>
      LinearCover.conj_mem_closure (hconj x hx) hh
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hinv x hx)
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd h, fun hh => ?_⟩
    have h' := hfwd _ hh
    rwa [hxinv, show x * (x * h * x) * x = (x * x) * h * (x * x) by group, hinv x hx, one_mul,
      mul_one] at h'
  exact LinearCover.card_sup_le_of_conj_mem hX fun x hx h hh =>
    (Subgroup.mem_normalizer_iff.1 (hN hx) h).1 hh

end Generic

namespace TwoCover

variable
    {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type*} [Group E] {D : TwoCover K E}

namespace Lifts

variable
    (L : D.Lifts)

def homA
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) :
    Multiplicative K →* E where
  toFun c := A.A c.toAdd
  map_one' := A_zero A
  map_mul' a b := A.add a.toAdd b.toAdd

theorem card_closure_range_le
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) :
    Nat.card (Subgroup.closure (Set.range A.A)) ≤ Nat.card K := by
  have hle : Subgroup.closure (Set.range A.A) ≤ (homA A).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  have : Finite (homA A).range := Finite.of_surjective _ (homA A).rangeRestrict_surjective
  calc Nat.card (Subgroup.closure (Set.range A.A)) ≤ Nat.card (homA A).range :=
        Subgroup.card_le_of_le hle
    _ ≤ Nat.card (Multiplicative K) :=
        Nat.card_le_card_of_surjective _ (homA A).rangeRestrict_surjective
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

abbrev genD : Set E :=
  Set.range L.L3.A ∪ ({⁅L.L0.A 1, L.L3.A 1⁆} ∪ {⁅L.L2.A 1, L.L3.A 1⁆})

abbrev Dg : Subgroup E :=
  Subgroup.closure L.genD

theorem A3_mem_Dg (c : K) : L.L3.A c ∈ L.Dg :=
  Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem Y5_mem_Dg : ⁅L.L0.A 1, L.L3.A 1⁆ ∈ L.Dg :=
  Subgroup.subset_closure (Or.inr (Or.inl rfl))

theorem Y6_mem_Dg : ⁅L.L2.A 1, L.L3.A 1⁆ ∈ L.Dg :=
  Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem genD_comm
    : ∀ x ∈ L.genD, ∀ y ∈ L.genD, Commute x y := by
  have h35 : ∀ c, Commute (L.L3.A c) ⁅L.L0.A 1, L.L3.A 1⁆ := fun c =>
    (L.comm3 4 (by decide) _ (L.b5_mem 1 1) c).symm
  have h36 : ∀ c, Commute (L.L3.A c) ⁅L.L2.A 1, L.L3.A 1⁆ := fun c =>
    (L.comm3 5 (by decide) _ (L.b6_mem 1 1) c).symm
  have h56 := L.lift_comm_five_six _ _ (L.b5_mem 1 1) (L.b6_mem 1 1)
  rintro x (⟨c, rfl⟩ | rfl | rfl) y (⟨d, rfl⟩ | rfl | rfl)
  · exact A_comm L.L3 c d
  · exact h35 c
  · exact h36 c
  · exact (h35 d).symm
  · exact Commute.refl _
  · exact h56
  · exact (h36 d).symm
  · exact h56.symm
  · exact Commute.refl _

theorem Dg_comm {x y : E} (hx : x ∈ L.Dg) (hy : y ∈ L.Dg) : Commute x y :=
  commute_of_mem_closure_of_commute L.genD_comm hx hy

theorem conj_mem_Dg {x : E} (hx : ∀ c, x * L.L3.A c * x⁻¹ ∈ L.Dg)
    (h5 : x * ⁅L.L0.A 1, L.L3.A 1⁆ * x⁻¹ ∈ L.Dg) (h6 : x * ⁅L.L2.A 1, L.L3.A 1⁆ * x⁻¹ ∈ L.Dg)
    {d : E} (hd : d ∈ L.Dg) : x * d * x⁻¹ ∈ L.Dg := by
  refine LinearCover.conj_mem_closure ?_ hd
  rintro _ (⟨c, rfl⟩ | rfl | rfl)
  · exact hx c
  · exact h5
  · exact h6

theorem conj_mem_Dg_of_comm {x : E} (hx : ∀ c, x * L.L3.A c * x⁻¹ ∈ L.Dg)
    (h5 : Commute x ⁅L.L0.A 1, L.L3.A 1⁆) (h6 : Commute x ⁅L.L2.A 1, L.L3.A 1⁆) {d : E}
    (hd : d ∈ L.Dg) : x * d * x⁻¹ ∈ L.Dg :=
  L.conj_mem_Dg hx (by rw [h5.eq, mul_inv_cancel_right]; exact L.Y5_mem_Dg)
    (by rw [h6.eq, mul_inv_cancel_right]; exact L.Y6_mem_Dg) hd

theorem conj_A0_mem_Dg (s : K) {d : E} (hd : d ∈ L.Dg) : L.L0.A s * d * (L.L0.A s)⁻¹ ∈ L.Dg := by
  refine L.conj_mem_Dg_of_comm (fun c => ?_) (L.comm0 4 (Or.inl rfl) _ (L.b5_mem 1 1) s).symm
    (L.comm0 5 (Or.inr rfl) _ (L.b6_mem 1 1) s).symm hd
  rw [show L.L0.A s * L.L3.A c * (L.L0.A s)⁻¹ = ⁅L.L0.A s, L.L3.A c⁆ * L.L3.A c by
    rw [commutatorElement_def]; group]
  refine mul_mem ?_ (L.A3_mem_Dg c)
  rcases L.b5_cases s c with h | h <;> rw [h]
  · exact one_mem _
  · exact L.Y5_mem_Dg

theorem conj_A2_mem_Dg (t : K) {d : E} (hd : d ∈ L.Dg) : L.L2.A t * d * (L.L2.A t)⁻¹ ∈ L.Dg := by
  refine L.conj_mem_Dg_of_comm (fun c => ?_) (L.comm2 4 (by decide) _ (L.b5_mem 1 1) t).symm
    (L.comm2 5 (by decide) _ (L.b6_mem 1 1) t).symm hd
  rw [show L.L2.A t * L.L3.A c * (L.L2.A t)⁻¹ = ⁅L.L2.A t, L.L3.A c⁆ * L.L3.A c by
    rw [commutatorElement_def]; group]
  refine mul_mem ?_ (L.A3_mem_Dg c)
  rcases L.b6_cases t c with h | h <;> rw [h]
  · exact one_mem _
  · exact L.Y6_mem_Dg

theorem conj_torus_mem_Dg
    {g : E} {p : Kˣ × (trialityFixedField K D.σ.toRingHom)ˣ}
    (hg : D.η g = torusX D.σ D.hσ p) {d : E} (hd : d ∈ L.Dg) : g * d * g⁻¹ ∈ L.Dg := by
  refine L.conj_mem_Dg (fun c => ?_) ?_ ?_ hd
  · rw [L.L3.torus g p hg c]
    exact L.A3_mem_Dg _
  · rw [D.torus_conj_long (by decide) g _ p hg (L.b5_mem 1 1)]
    exact L.Y5_mem_Dg
  · rw [D.torus_conj_long (by decide) g _ p hg (L.b6_mem 1 1)]
    exact L.Y6_mem_Dg

theorem exists_Dg_of_heightSeries_three
    (y : E)
    (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 3) :
    ∃ d ∈ L.Dg, D.η d = D.η y := by
  set Z : Subgroup (ModGL TwistTag.D4.tag K) :=
    (L.Dg.map D.η).map (graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom).subtype with hZ
  have hle : Subgroup.closure {g | ∃ j : Fin 6, 3 ≤ height (trialityRoot j) ∧
      g ∈ trialityGroup D.σ j} ≤ Z := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨j, hj, hg⟩
    have hgΓ := trialityGroup_le_graphFixedRootGroup D.σ j hg
    have key : ∃ d ∈ L.Dg, D.η d = ⟨g, hgΓ⟩ := by
      rcases height_trialityRoot_ge_three j hj with rfl | rfl | rfl
      · obtain ⟨c, hc⟩ := exists_trialityOrbitProd_eq' (Or.inr (Or.inr rfl)) hg
        exact ⟨L.L3.A c, L.A3_mem_Dg c, Subtype.ext ((coe_map_A L.L3 c).trans hc)⟩
      · rcases D.long_cases (Or.inr (Or.inl rfl)) (g := ⟨g, hgΓ⟩) hg with h | h
        · exact ⟨1, one_mem _, by rw [map_one, h]⟩
        · exact ⟨_, L.Y5_mem_Dg, L.map_Y5.trans h.symm⟩
      · rcases D.long_cases (Or.inr (Or.inr rfl)) (g := ⟨g, hgΓ⟩) hg with h | h
        · exact ⟨1, one_mem _, by rw [map_one, h]⟩
        · exact ⟨_, L.Y6_mem_Dg, L.map_Y6.trans h.symm⟩
    obtain ⟨d, hd, hdg⟩ := key
    exact ⟨D.η d, ⟨d, hd, rfl⟩, by rw [hdg]; rfl⟩
  have hyΓ : (D.η y : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K 3 ⊓ twistedFixedGroup TwistTag.D4 K D.σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨hy, graphFixedRootGroup_le _ _ _ (D.η y).2⟩
  obtain ⟨_, ⟨d, hd, rfl⟩, hdy⟩ := hle (heightSeries_inf_le_closure D.σ 3 hyΓ)
  exact ⟨d, hd, Subtype.ext hdy⟩

abbrev Sg : Subgroup E :=
  (L.Dg.map D.η).comap D.η

theorem Dg_le_Sg : L.Dg ≤ L.Sg := fun d hd => ⟨d, hd, rfl⟩

theorem Sg_comm
    : ∀ x ∈ L.Sg, ∀ y ∈ L.Sg, x * y = y * x := by
  intro x hx y hy
  obtain ⟨d, hd, hdx⟩ := hx
  obtain ⟨d', hd', hdy⟩ := hy
  have h1 : Commute x d' := D.commute_of_map_eq hdx (L.Dg_comm hd hd')
  exact (D.commute_of_map_eq hdy h1.symm).symm.eq

theorem Sg_sq
    : ∀ x ∈ L.Sg, x ^ 2 ∈ L.Dg := by
  intro x hx
  obtain ⟨d, hd, hdx⟩ := hx
  have hc := D.map_inv_mul_eq_one hdx
  have hx' : x = d * (d⁻¹ * x) := by group
  rw [hx', ((D.commute_of_map_eq_one hc d).symm).mul_pow, D.sq _ hc, mul_one]
  exact pow_mem hd 2

theorem rho_conj
    {ρ : E → ZMod 2} (hρ : ∀ x ∈ L.Sg, ∀ y ∈ L.Sg, ρ (x * y) = ρ x + ρ y)
    (hρD : ∀ d ∈ L.Dg, ρ d = 0) {x : E} (hx : ∀ d ∈ L.Dg, x * d * x⁻¹ ∈ L.Dg) {q : E}
    (hq : q ∈ L.Sg) : x * q * x⁻¹ ∈ L.Sg ∧ ρ (x * q * x⁻¹) = ρ q := by
  obtain ⟨d, hd, hdq⟩ := hq
  have hc := D.map_inv_mul_eq_one hdq
  have hcom := (D.commute_of_map_eq_one hc x⁻¹).eq
  have e : x * q * x⁻¹ = (x * d * x⁻¹ * d⁻¹) * q :=
    calc x * q * x⁻¹ = x * d * ((d⁻¹ * q) * x⁻¹) := by group
      _ = x * d * (x⁻¹ * (d⁻¹ * q)) := by rw [hcom]
      _ = (x * d * x⁻¹ * d⁻¹) * q := by group
  have hm : x * d * x⁻¹ * d⁻¹ ∈ L.Dg := mul_mem (hx d hd) (inv_mem hd)
  have hqS : q ∈ L.Sg := ⟨d, hd, hdq⟩
  rw [e]
  exact ⟨mul_mem (L.Dg_le_Sg hm) hqS, by rw [hρ _ (L.Dg_le_Sg hm) _ hqS, hρD _ hm, zero_add]⟩

omit [Finite K] [CharP K 2] in
theorem orbitProd_mem_heightSeries
    (σ' : K →+* K) (c : K) :
    (trialityOrbitProd K σ' (trialityRoot 0) c : ModGL TwistTag.D4.tag K) ∈
        heightSeries TwistTag.D4.tag K 1 ∧
      (trialityOrbitProd K σ' (trialityRoot 2) c : ModGL TwistTag.D4.tag K) ∈
        heightSeries TwistTag.D4.tag K 2 := by
  obtain ⟨m0, m1, m2⟩ := orbit_zero_mem
  obtain ⟨n0, n1, n2⟩ := orbit_two_mem
  rw [coe_trialityOrbitProd, coe_trialityOrbitProd]
  exact ⟨mul_mem (mul_mem (pinnedX_mem_heightSeries m0 _) (pinnedX_mem_heightSeries m1 _))
      (pinnedX_mem_heightSeries m2 _),
    mul_mem (mul_mem (pinnedX_mem_heightSeries n0 _) (pinnedX_mem_heightSeries n1 _))
      (pinnedX_mem_heightSeries n2 _)⟩

theorem commutator_A0_A2_mem_Sg
    (s t : K) : ⁅L.L0.A s, L.L2.A t⁆ ∈ L.Sg := by
  refine L.exists_Dg_of_heightSeries_three _ ?_
  rw [map_commutatorElement, coe_commutatorElement_sub, coe_map_A, coe_map_A]
  exact commutator_heightSeries_le K 1 2 (Subgroup.commutator_mem_commutator
    (orbitProd_mem_heightSeries D.σ.toRingHom s).1 (orbitProd_mem_heightSeries D.σ.toRingHom t).2)

theorem commutator_A0_A2_mem
    (s t : K) : ⁅L.L0.A s, L.L2.A t⁆ ∈ L.Dg := by
  by_contra hne
  obtain ⟨ρ, hρ, hρD, hρc⟩ := EvenCoverPairing.exists_zmod_two_functional L.Dg_le_Sg L.Sg_comm
    L.Sg_sq (L.commutator_A0_A2_mem_Sg s t) hne
  have hK3 : Nat.card K = 2 ^ 3 := by rw [D.hK]; norm_num
  have hF := form_eq_zero_of_chars (k := K) (f := 3) (by norm_num) hK3
    (fun p => rootChar K (trialityRoot 0) (torusParam D.σ p))
    (fun p => rootChar K (trialityRoot 2) (torusParam D.σ p)) ?_
    (fun s t => ρ ⁅L.L0.A s, L.L2.A t⁆) ?_ ?_ ?_
  · exact hρc (hF s t)
  · intro i j hi hj
    obtain ⟨p, hp⟩ := exists_weight_zero_pow_ne_one D.σ (n := 3) le_rfl hK3 i j hi hj
    refine ⟨p, ?_⟩
    obtain ⟨w0, -, w2, -⟩ := weights_two D.σ D.hσ D.hk p
    show rootChar K (trialityRoot 0) (torusParam D.σ p) ^ 2 ^ i *
      rootChar K (trialityRoot 2) (torusParam D.σ p) ^ 2 ^ j ≠ 1
    rwa [w2, ← w0]
  · intro c₁ c₂ d
    show ρ ⁅L.L0.A (c₁ + c₂), L.L2.A d⁆ = ρ ⁅L.L0.A c₁, L.L2.A d⁆ + ρ ⁅L.L0.A c₂, L.L2.A d⁆
    rw [L.L0.add, commutatorElement_mul_left']
    obtain ⟨hmem, hρeq⟩ := L.rho_conj hρ hρD (fun d hd => L.conj_A0_mem_Dg c₁ hd)
      (L.commutator_A0_A2_mem_Sg c₂ d)
    rw [hρ _ hmem _ (L.commutator_A0_A2_mem_Sg c₁ d), hρeq, add_comm]
  · intro c d₁ d₂
    show ρ ⁅L.L0.A c, L.L2.A (d₁ + d₂)⁆ = ρ ⁅L.L0.A c, L.L2.A d₁⁆ + ρ ⁅L.L0.A c, L.L2.A d₂⁆
    rw [L.L2.add, commutatorElement_mul_right']
    obtain ⟨hmem, hρeq⟩ := L.rho_conj hρ hρD (fun d hd => L.conj_A2_mem_Dg d₁ hd)
      (L.commutator_A0_A2_mem_Sg c d₂)
    rw [hρ _ (L.commutator_A0_A2_mem_Sg c d₁) _ hmem, hρeq]
  · intro p c d
    obtain ⟨g, hg⟩ := D.surj (torusX D.σ D.hσ p)
    show ρ ⁅L.L0.A ((rootChar K (trialityRoot 0) (torusParam D.σ p) : K) * c),
      L.L2.A ((rootChar K (trialityRoot 2) (torusParam D.σ p) : K) * d)⁆ = ρ ⁅L.L0.A c, L.L2.A d⁆
    rw [← L.L0.torus g p hg c, ← L.L2.torus g p hg d, ← conj_commutatorElement']
    exact (L.rho_conj hρ hρD (fun d hd => L.conj_torus_mem_Dg hg hd)
      (L.commutator_A0_A2_mem_Sg c d)).2

theorem conj_A0_A2 (s t : K) : L.L0.A s * L.L2.A t * (L.L0.A s)⁻¹ =
    ⁅L.L0.A s, L.L2.A t⁆ * L.L2.A t := by
  rw [commutatorElement_def]
  group

section Y2

variable
    {Y2 : E} (hY2 : D.η Y2 = longX D.σ 1 (Or.inl rfl))
include hY2

theorem commutator_Y2_A0_mem_Sg
    (s : K) : (L.L2.A s)⁻¹ * ⁅Y2, L.L0.A s⁆ ∈ L.Sg := by
  refine L.exists_Dg_of_heightSeries_three _ ?_
  rw [map_mul, map_inv, map_commutatorElement, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_commutatorElement_sub, coe_map_A, coe_map_A, hY2, coe_longX, OneMemClass.coe_one]
  exact commutator_orbitProd_mem_three s

theorem commutator_Y2_A0_mem
    (s : K) : (L.L2.A s)⁻¹ * ⁅Y2, L.L0.A s⁆ ∈ L.Dg := by
  by_contra hne
  obtain ⟨ρ, hρ, hρD, hρc⟩ := EvenCoverPairing.exists_zmod_two_functional L.Dg_le_Sg L.Sg_comm
    L.Sg_sq (L.commutator_Y2_A0_mem_Sg hY2 s) hne
  have hS := L.commutator_Y2_A0_mem_Sg hY2
  have hconj2 : ∀ s' : K, ∀ d ∈ L.Dg, (L.L2.A s')⁻¹ * d * (L.L2.A s')⁻¹⁻¹ ∈ L.Dg := by
    intro s' d hd
    rw [inv_inv, A_inv L.L2 s']
    have h := L.conj_A2_mem_Dg s' hd
    rwa [A_inv L.L2 s'] at h
  have hadd : ∀ s₁ s₂ : K, ρ ((L.L2.A (s₁ + s₂))⁻¹ * ⁅Y2, L.L0.A (s₁ + s₂)⁆) =
      ρ ((L.L2.A s₁)⁻¹ * ⁅Y2, L.L0.A s₁⁆) + ρ ((L.L2.A s₂)⁻¹ * ⁅Y2, L.L0.A s₂⁆) := by
    intro s₁ s₂
    have e : (L.L2.A (s₁ + s₂))⁻¹ * ⁅Y2, L.L0.A (s₁ + s₂)⁆ =
        ((L.L2.A s₂)⁻¹ * (((L.L2.A s₁)⁻¹ * ⁅Y2, L.L0.A s₁⁆) * ⁅L.L0.A s₁, L.L2.A s₂⁆) *
          (L.L2.A s₂)⁻¹⁻¹) *
        (L.L0.A s₁ * ((L.L2.A s₂)⁻¹ * ⁅Y2, L.L0.A s₂⁆) * (L.L0.A s₁)⁻¹) := by
      rw [L.L2.add, L.L0.add]
      simp only [commutatorElement_def]
      group
    have hq : ((L.L2.A s₁)⁻¹ * ⁅Y2, L.L0.A s₁⁆) * ⁅L.L0.A s₁, L.L2.A s₂⁆ ∈ L.Sg :=
      mul_mem (hS s₁) (L.Dg_le_Sg (L.commutator_A0_A2_mem s₁ s₂))
    obtain ⟨h1, h1'⟩ := L.rho_conj hρ hρD (hconj2 s₂) hq
    obtain ⟨h2, h2'⟩ := L.rho_conj hρ hρD (fun d hd => L.conj_A0_mem_Dg s₁ hd) (hS s₂)
    rw [e, hρ _ h1 _ h2, h1', h2', hρ _ (hS s₁) _ (L.Dg_le_Sg (L.commutator_A0_A2_mem s₁ s₂)),
      hρD _ (L.commutator_A0_A2_mem s₁ s₂), add_zero]
  have h7 : 1 < Nat.card Kˣ := by rw [Nat.card_units, D.hK]; norm_num
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 h7
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : Kˣ)
  have hsq : a₀ ^ 2 ≠ 1 := sq_ne_one_of_odd (odd_card_units_of_charTwo K) ha₀
  have hr : ((a₀ ^ 2 : Kˣ) : K) ≠ 1 := fun h => hsq (Units.ext h)
  have hinv : ∀ s' : K, ρ ((L.L2.A (((a₀ ^ 2 : Kˣ) : K) * s'))⁻¹ *
      ⁅Y2, L.L0.A (((a₀ ^ 2 : Kˣ) : K) * s')⁆) = ρ ((L.L2.A s')⁻¹ * ⁅Y2, L.L0.A s'⁆) := by
    intro s'
    obtain ⟨g, hg⟩ := D.surj (torusX D.σ D.hσ (a₀, 1))
    obtain ⟨w0, -, w2, -⟩ := weights_two D.σ D.hσ D.hk (a₀, 1)
    dsimp only at w0 w2
    have h0 := L.L0.torus g (a₀, 1) hg s'
    have h2 := L.L2.torus g (a₀, 1) hg s'
    rw [w0] at h0
    rw [w2] at h2
    have hY := D.torus_conj_long (Or.inl rfl) g Y2 (a₀, 1) hg (Y2_mem hY2)
    have e : (L.L2.A (((a₀ ^ 2 : Kˣ) : K) * s'))⁻¹ * ⁅Y2, L.L0.A (((a₀ ^ 2 : Kˣ) : K) * s')⁆ =
        g * ((L.L2.A s')⁻¹ * ⁅Y2, L.L0.A s'⁆) * g⁻¹ := by
      rw [← h0, ← h2]
      conv_lhs => rw [← hY]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (L.rho_conj hρ hρD (fun d hd => L.conj_torus_mem_Dg hg hd) (hS s')).2
  have hzero := param_form_eq_zero_right
    (fun (_ : K) (s' : K) => ρ ((L.L2.A s')⁻¹ * ⁅Y2, L.L0.A s'⁆)) (fun _ d₁ d₂ => hadd d₁ d₂) hr
    (fun _ s' => hinv s') 0 s
  exact hρc hzero

end Y2

section Tower

abbrev genP (Y2 : E) : Set E :=
  Set.range L.L0.A ∪ ({Y2} ∪ (Set.range L.L2.A ∪ L.genD))

variable
    {Y2 : E} (hY2 : D.η Y2 = longX D.σ 1 (Or.inl rfl))
include hY2

theorem card_closure_genP_le
    [Finite E] : Nat.card (Subgroup.closure (L.genP Y2)) ≤ 4096 := by
  have h56 := L.lift_comm_five_six _ _ (L.b5_mem 1 1) (L.b6_mem 1 1)
  have hK8 : Nat.card K = 8 := D.hK
  have c6 := card_closure_singleton_le L.Y6_mul_self
  have c5 := card_closure_union_le (card_closure_singleton_le L.Y5_mul_self)
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact L.Y5_mul_self)
    (fun x hx y hy => by
      rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy, h56.eq, mul_inv_cancel_right]
      exact Subgroup.subset_closure rfl)
  have c4 := card_closure_union_le (Y := {⁅L.L0.A 1, L.L3.A 1⁆} ∪ {⁅L.L2.A 1, L.L3.A 1⁆})
    (card_closure_range_le L.L3) (fun x hx => by obtain ⟨c, rfl⟩ := hx; exact A_mul_self L.L3 c)
    (fun x hx y hy => by
      obtain ⟨c, rfl⟩ := hx
      rcases hy with rfl | rfl
      · rw [(L.comm3 4 (by decide) _ (L.b5_mem 1 1) c).symm.eq, mul_inv_cancel_right]
        exact Subgroup.subset_closure (Or.inl rfl)
      · rw [(L.comm3 5 (by decide) _ (L.b6_mem 1 1) c).symm.eq, mul_inv_cancel_right]
        exact Subgroup.subset_closure (Or.inr rfl))
  have c3 := card_closure_union_le (Y := L.genD) (card_closure_range_le L.L2)
    (fun x hx => by obtain ⟨c, rfl⟩ := hx; exact A_mul_self L.L2 c)
    (fun x hx y hy => by
      obtain ⟨t, rfl⟩ := hx
      exact L.conj_A2_mem_Dg t (Subgroup.subset_closure hy))
  have hsub3 : L.Dg ≤ Subgroup.closure (Set.range L.L2.A ∪ L.genD) :=
    Subgroup.closure_mono Set.subset_union_right
  have c2 := card_closure_union_le (X := {Y2}) (Y := Set.range L.L2.A ∪ L.genD)
    (card_closure_singleton_le (L.Y2_mul_self hY2))
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact L.Y2_mul_self hY2)
    (fun x hx y hy => by
      rw [Set.mem_singleton_iff.1 hx]
      rcases hy with ⟨t, rfl⟩ | ⟨u, rfl⟩ | rfl | rfl
      · rw [(L.Y2_comm2 hY2 t).eq, mul_inv_cancel_right]
        exact Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
      · rw [(L.Y2_comm3 hY2 u).eq, mul_inv_cancel_right]
        exact hsub3 (L.A3_mem_Dg u)
      · rw [L.Y2_conj_Y5 hY2]
        exact mul_mem (hsub3 L.Y6_mem_Dg) (hsub3 L.Y5_mem_Dg)
      · rw [(L.Y2_comm_Y6 hY2).eq, mul_inv_cancel_right]
        exact hsub3 L.Y6_mem_Dg)
  have hsub2 : Subgroup.closure (Set.range L.L2.A ∪ L.genD) ≤
      Subgroup.closure ({Y2} ∪ (Set.range L.L2.A ∪ L.genD)) :=
    Subgroup.closure_mono Set.subset_union_right
  have c1 := card_closure_union_le (X := Set.range L.L0.A) (Y := {Y2} ∪ (Set.range L.L2.A ∪ L.genD))
    (card_closure_range_le L.L0) (fun x hx => by obtain ⟨c, rfl⟩ := hx; exact A_mul_self L.L0 c)
    (fun x hx y hy => by
      obtain ⟨s, rfl⟩ := hx
      rcases hy with rfl | ⟨t, rfl⟩ | hy
      · have hg := L.commutator_Y2_A0_mem hY2 s
        have e : L.L0.A s * y * (L.L0.A s)⁻¹ =
            ((L.L2.A s)⁻¹ * ⁅y, L.L0.A s⁆)⁻¹ * (L.L2.A s)⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (mul_mem (inv_mem (hsub2 (hsub3 hg)))
          (inv_mem (hsub2 (Subgroup.subset_closure (Or.inl ⟨s, rfl⟩)))))
          (Subgroup.subset_closure (Or.inl rfl))
      · rw [L.conj_A0_A2]
        exact mul_mem (hsub2 (hsub3 (L.commutator_A0_A2_mem s t)))
          (hsub2 (Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)))
      · exact hsub2 (hsub3 (L.conj_A0_mem_Dg s (Subgroup.subset_closure hy))))
  calc Nat.card (Subgroup.closure (L.genP Y2)) ≤ 8 * Nat.card
        (Subgroup.closure ({Y2} ∪ (Set.range L.L2.A ∪ L.genD))) := hK8 ▸ c1
    _ ≤ 8 * (2 * (8 * (8 * (2 * 2)))) := by
        refine Nat.mul_le_mul_left 8 (c2.trans (Nat.mul_le_mul_left 2 ?_))
        refine (hK8 ▸ c3).trans (Nat.mul_le_mul_left 8 ?_)
        refine (hK8 ▸ c4).trans (Nat.mul_le_mul_left 8 ?_)
        exact c5.trans (Nat.mul_le_mul_left 2 c6)
    _ = 4096 := by norm_num

theorem graphFixedPosUnipotent_le_map :
    graphFixedPosUnipotent TwistTag.D4 K D.σ.toRingHom ≤
      ((Subgroup.closure (L.genP Y2)).map D.η).map
        (graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom).subtype := by
  obtain ⟨-, -, -, -, -, -, hbij, -⟩ :=
    even_triality_positive_orbit_parametrization K D.σ (toRingHom_pow_three D.σ D.hσ)
  intro u hu
  obtain ⟨⟨a, b, c, d, e, f⟩, -, rfl⟩ := hbij.surjOn hu
  have hZ : ∀ y ∈ Subgroup.closure (L.genP Y2), (D.η y : ModGL TwistTag.D4.tag K) ∈
      ((Subgroup.closure (L.genP Y2)).map D.η).map
        (graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom).subtype :=
    fun y hy => ⟨D.η y, ⟨y, hy, rfl⟩, rfl⟩
  have hgen : ∀ y ∈ L.genP Y2, (D.η y : ModGL TwistTag.D4.tag K) ∈
      ((Subgroup.closure (L.genP Y2)).map D.η).map
        (graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom).subtype :=
    fun y hy => hZ y (Subgroup.subset_closure hy)
  have hlong : ∀ (l : Fin 6) (hl : l = 1 ∨ l = 4 ∨ l = 5) (y : E), y ∈ L.genP Y2 →
      D.η y = longX D.σ l hl → ∀ e : trialityFixedField K D.σ.toRingHom,
        pinnedX TwistTag.D4.tag K (trialityRoot l) e ∈
          ((Subgroup.closure (L.genP Y2)).map D.η).map
            (graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom).subtype := by
    intro l hl y hy hyl e
    rcases fixedField_eq_zero_or_one D.σ D.hk e with rfl | rfl
    · rw [ZeroMemClass.coe_zero, pinnedX_zero]
      exact one_mem _
    · have h := hgen y hy
      rwa [hyl, coe_longX] at h
  simp only [Subgroup.coe_mul]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_
  · have h := hgen _ (Or.inl ⟨a, rfl⟩)
    rwa [coe_map_A] at h
  · exact hlong 1 (Or.inl rfl) Y2 (Or.inr (Or.inl rfl)) hY2 b
  · have h := hgen _ (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))
    rwa [coe_map_A] at h
  · have h := hgen _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩))))
    rwa [coe_map_A] at h
  · exact hlong 4 (Or.inr (Or.inl rfl)) _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      L.map_Y5 e
  · exact hlong 5 (Or.inr (Or.inr rfl)) _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      L.map_Y6 f

end Tower

end Lifts

theorem ker_eq_bot
    [Finite E] [Group.IsPerfect E] (D : TwoCover K E) : D.η.ker = ⊥ := by
  obtain ⟨L⟩ := D.nonempty_lifts
  obtain ⟨Y2, hY2⟩ := D.surj (longX D.σ 1 (Or.inl rfl))
  obtain ⟨-, -, -, -, -, -, -, hUcard, P, hP⟩ :=
    even_triality_positive_orbit_parametrization K D.σ (toRingHom_pow_three D.σ D.hσ)
  set P₀ := Subgroup.closure (L.genP Y2) with hP₀
  have hS : (P : Subgroup (graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom)) ≤ P₀.map D.η := by
    intro u hu
    rw [hP, Subgroup.mem_subgroupOf] at hu
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 (L.graphFixedPosUnipotent_le_map hY2 hu)
    rwa [show y = u from Subtype.ext hyu] at hy
  have hScard : Nat.card P = 4096 := by
    rw [hP, card_subgroupOf_of_le (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K
      D.σ.toRingHom), hUcard, D.hK, D.hk]
    norm_num
  have hinj : ∀ z ∈ P₀, D.η z = 1 → z = 1 := by
    let g : P₀ → P₀.map D.η := fun m => ⟨D.η m, Subgroup.mem_map_of_mem D.η m.2⟩
    have hg : Function.Surjective g := by
      rintro ⟨y, m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    have : Finite (P₀.map D.η) := Finite.of_surjective _ hg
    have hcard : Nat.card P₀ ≤ Nat.card (P₀.map D.η) :=
      calc Nat.card P₀ ≤ 4096 := L.card_closure_genP_le hY2
        _ = Nat.card P := hScard.symm
        _ ≤ Nat.card (P₀.map D.η) := Subgroup.card_le_of_le hS
    intro z hz hz1
    have h1 := (hg.bijective_of_nat_card_le hcard).1 (a₁ := ⟨z, hz⟩) (a₂ := ⟨1, one_mem _⟩)
      (Subtype.ext (show D.η z = D.η 1 by rw [hz1, map_one]))
    exact congrArg Subtype.val h1
  have h2 : IsPGroup 2 D.η.ker := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact D.sq g g.2)⟩
  exact LinearCover.ker_eq_bot_of_sylow_le_map D.η D.surj D.central h2 P P₀ hS hinj

end TwoCover

end CFSG.LieType.Chevalley.TrialityFieldTwo

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley TrialityCover TrialityFieldTwo
  CFSG.LocalAnalysis.ComponentInitial

theorem triality_field_two_central_two_cover_trivial
    {E : Type*} {J : Type} [Group E] [Group J]
    [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hJ : LieModel J .trialityD4 0 2 1) : η.ker = ⊥ ∧ Function.Bijective η := by
  have hX : TwistedChevalleyModel J .D4 (2 ^ 1) := by
    rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
    · exact absurd hc (by decide)
    · exact hX.2
    · exact absurd hr (by decide)
    · exact absurd hs (by decide)
  obtain ⟨K, _, _, _, σ, hσ, hq, hK, hk, ⟨e⟩⟩ := triality_model le_rfl hX
  set η' : E →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot : η'.ker = ⊥ := UnitaryOddCover.ker_eq_bot_of_sq_reduction
    (fun θ' hθ' hC' hsq => TwoCover.ker_eq_bot ⟨σ, hσ, fun c => by rw [hq]; norm_num, by
      rw [hK]; norm_num, by rw [hk]; norm_num, θ', hθ', hC', hsq⟩)
    η' (e.surjective.comp hη) (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LieType.Chevalley
