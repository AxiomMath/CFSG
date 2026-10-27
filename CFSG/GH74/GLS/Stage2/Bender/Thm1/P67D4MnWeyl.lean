module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4WeylCases
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Abstract

variable {Y : Type*} [Group Y]

theorem mnWeyl_inv_mul_mul_mem {T : Subgroup Y} {m : Y} (hm3 : m ^ 3 ∈ T)
    (hmn : ∀ t ∈ T, m * t * m⁻¹ ∈ T) {t : Y} (ht : t ∈ T) : m⁻¹ * t * m ∈ T := by
  have h1 : (m ^ 3)⁻¹ * t * m ^ 3 ∈ T := mul_mem (mul_mem (inv_mem hm3) ht) hm3
  have h2 := hmn _ (hmn _ h1)
  have e : m⁻¹ * t * m = m * (m * ((m ^ 3)⁻¹ * t * m ^ 3) * m⁻¹) * m⁻¹ := by group
  rw [e]
  exact h2

theorem mnWeyl_sup_le_normalizer {T : Subgroup Y} {m : Y} (hm3 : m ^ 3 ∈ T)
    (hmn : ∀ t ∈ T, m * t * m⁻¹ ∈ T) :
    T ⊔ Subgroup.zpowers m ≤ Subgroup.normalizer (T : Set Y) := by
  refine sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 ?_)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hmn h, fun hh => ?_⟩
  have := mnWeyl_inv_mul_mul_mem hm3 hmn hh
  simpa [mul_assoc] using this

theorem mnWeyl_conj_mem {T : Subgroup Y} {m : Y} (hm3 : m ^ 3 ∈ T)
    (hmn : ∀ t ∈ T, m * t * m⁻¹ ∈ T) {x : Y} (hx : x ∈ T ⊔ Subgroup.zpowers m) {t : Y}
    (ht : t ∈ T) : x * t * x⁻¹ ∈ T ∧ x⁻¹ * t * x ∈ T := by
  have hxn := mnWeyl_sup_le_normalizer hm3 hmn hx
  refine ⟨(Subgroup.mem_normalizer_iff.1 hxn t).1 ht, ?_⟩
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hxn) t).1 ht
  rwa [inv_inv] at this

theorem mnWeyl_exists_zpow_mul_mem {T : Subgroup Y} {m : Y} (hmT : m ∉ T) (hm3 : m ^ 3 ∈ T)
    (hmn : ∀ t ∈ T, m * t * m⁻¹ ∈ T) {n v : Y} (hn : n ∈ T ⊔ Subgroup.zpowers m)
    (hv : v ∈ T ⊔ Subgroup.zpowers m) (hvT : v ∉ T) : ∃ j : ℤ, n * v ^ j ∈ T := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := T ⊔ Subgroup.zpowers m with hN
  have hmN : m ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers m)
  have : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (mnWeyl_sup_le_normalizer hm3 hmn)
  let π : N →* N ⧸ T.subgroupOf N := QuotientGroup.mk' (T.subgroupOf N)
  have hπ : ∀ x : N, π x = 1 ↔ (x : Y) ∈ T := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set a₀ : N ⧸ T.subgroupOf N := π ⟨m, hmN⟩ with ha₀
  have ha₀1 : a₀ ≠ 1 := fun h => hmT ((hπ _).1 h)
  have ha₀3 : a₀ ^ 3 = 1 := by
    rw [ha₀, ← map_pow]
    exact (hπ _).2 hm3
  have hgen : ∀ x : N, π x ∈ Subgroup.zpowers a₀ := by
    have hle : N ≤ ((Subgroup.zpowers a₀).comap π).map N.subtype := by
      refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.2 ?_)
      · refine ⟨⟨t, Subgroup.mem_sup_left ht⟩, ?_, rfl⟩
        change π ⟨t, Subgroup.mem_sup_left ht⟩ ∈ Subgroup.zpowers a₀
        rw [(hπ ⟨t, Subgroup.mem_sup_left ht⟩).2 ht]
        exact one_mem _
      · exact ⟨⟨m, hmN⟩, Subgroup.mem_comap.2 (Subgroup.mem_zpowers _), rfl⟩
    intro x
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hall : ∀ q : N ⧸ T.subgroupOf N, q ∈ Subgroup.zpowers a₀ := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (T.subgroupOf N) q
    exact hgen x
  have hcard : Nat.card (N ⧸ T.subgroupOf N) = 3 :=
    (orderOf_eq_card_of_forall_mem_zpowers hall).symm.trans (orderOf_eq_prime ha₀3 ha₀1)
  have hvπ : π ⟨v, hv⟩ ≠ 1 := fun h => hvT ((hπ _).1 h)
  have htop : Subgroup.zpowers (π ⟨v, hv⟩) = ⊤ := zpowers_eq_top_of_prime_card hcard hvπ
  have hnmem : π ⟨n, hn⟩ ∈ Subgroup.zpowers (π ⟨v, hv⟩) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hnmem
  refine ⟨-k, (hπ (⟨n, hn⟩ * ⟨v, hv⟩ ^ (-k))).1 ?_⟩
  rw [map_mul, map_zpow, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]

theorem mnWeyl_inv_mul_apply_mem {T : Subgroup Y} {m : Y} (hm3 : m ^ 3 ∈ T)
    (hmn : ∀ t ∈ T, m * t * m⁻¹ ∈ T) (D : MulAut Y) (hDm : D m = m)
    (hDT : ∀ t ∈ T, D t ∈ T) {x : Y} (hx : x ∈ T ⊔ Subgroup.zpowers m) : x⁻¹ * D x ∈ T := by
  let S : Subgroup Y :=
    { carrier := {x | x ∈ T ⊔ Subgroup.zpowers m ∧ x⁻¹ * D x ∈ T}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, ?_⟩
        have h1 : b⁻¹ * (a⁻¹ * D a) * b ∈ T := (mnWeyl_conj_mem hm3 hmn hb.1 ha.2).2
        have e : (a * b)⁻¹ * D (a * b) = (b⁻¹ * (a⁻¹ * D a) * b) * (b⁻¹ * D b) := by
          simp only [mul_inv_rev, map_mul, mul_assoc]
          simp
        rw [e]
        exact mul_mem h1 hb.2
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, ?_⟩
        have h1 : a * (a⁻¹ * D a)⁻¹ * a⁻¹ ∈ T :=
          (mnWeyl_conj_mem hm3 hmn ha.1 (inv_mem ha.2)).1
        have e : (a⁻¹)⁻¹ * D a⁻¹ = a * (a⁻¹ * D a)⁻¹ * a⁻¹ := by
          simp [mul_assoc]
        rw [e]
        exact h1 }
  have hle : T ⊔ Subgroup.zpowers m ≤ S := by
    refine sup_le (fun t ht => ⟨Subgroup.mem_sup_left ht, ?_⟩) (Subgroup.zpowers_le.2 ?_)
    · exact mul_mem (inv_mem ht) (hDT t ht)
    · refine ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers m), ?_⟩
      rw [hDm, inv_mul_cancel]
      exact one_mem _
  exact (hle hx).2

end Abstract

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4Minus_weyl_cases {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (T' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (m' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hm'T : m' ∉ T') (hm'3 : m' ^ 3 ∈ T') (hm'n : ∀ t ∈ T', m' * t * m'⁻¹ ∈ T')
    (hm'δ : fieldActor (t := TwistTag.D4) σ σ m' = m')
    (hTδ : ∀ t ∈ T', fieldActor (t := TwistTag.D4) σ σ t ∈ T')
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hVe : IsElementaryAbelian 3 V) (hVc : Nat.card V = 9)
    (hV0 : ∀ x ∈ V, ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      g ∈ T' ⊔ Subgroup.zpowers m' ∧ (δ = 1 ∨ δ = σ ∨ δ = σ⁻¹) ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    (∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∃ t ∈ T', (φ = MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ ∨
          φ⁻¹ = MulAut.conj t * fieldActor (t := TwistTag.D4) σ σ)) ∨
    (∃ (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      v ∈ T' ∧ v ≠ 1 ∧ v ^ 3 = 1 ∧ MulAut.conj v ∈ V ∧
      n ∈ T' ⊔ Subgroup.zpowers m' ∧ n ∉ T' ∧ (δ = σ ∨ δ = σ⁻¹) ∧
      MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ ∈ V ∧
      (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v) := by
  classical
  obtain ⟨-, -, ⟨Θ, hΘ, -, hΘker, -⟩, hcyc, hcard, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 :=
    ringEquiv_ne_one_of_pow (Nat.one_lt_pow (by omega) hp.one_lt) hK σ hσ
  have hD3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := d4_fieldActor_pow_three K hK σ hσ
  have hDinv : fieldActor (t := TwistTag.D4) σ σ⁻¹ =
      fieldActor (t := TwistTag.D4) σ σ * fieldActor (t := TwistTag.D4) σ σ := by
    have h1 : fieldActor (t := TwistTag.D4) σ σ⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ :=
      map_inv (fieldActorHom (t := TwistTag.D4) σ) σ
    rw [h1]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact hD3
  have hstab : ∀ δ : K ≃+* K, (δ = σ ∨ δ = σ⁻¹) →
      fieldActor (t := TwistTag.D4) σ δ m' = m' ∧
        ∀ t ∈ T', fieldActor (t := TwistTag.D4) σ δ t ∈ T' := by
    intro δ hδ
    rcases hδ with h | h
    · rw [h]
      exact ⟨hm'δ, hTδ⟩
    · rw [h, hDinv]
      exact ⟨by rw [MulAut.mul_apply, hm'δ, hm'δ], fun t ht => by
        rw [MulAut.mul_apply]
        exact hTδ _ (hTδ t ht)⟩
  have := hVe
  have hV3 : ∀ x ∈ V, x ^ 3 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_isElementaryAbelian (p := 3) hx hy
  have hinn : ∀ x : MulAut 𝒞[K, σ],
      x ∈ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ↔ Θ x = 1 := fun x => by
    rw [← hΘker, MonoidHom.mem_ker]
  have hΘform : ∀ (g : 𝒞[K, σ]) (δ : K ≃+* K),
      Θ (MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ) = δ := fun g δ => hΘ _ g δ rfl
  by_cases hc1 : ∃ x ∈ V, x ∉ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ∧
      ∃ g : 𝒞[K, σ], g ∈ T' ∧
        ∃ δ : K ≃+* K, x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ
  · left
    obtain ⟨x, hxV, hxout, g, hgT, δ, hx⟩ := hc1
    have hΘx : Θ x = δ := by rw [hx]; exact hΘform g δ
    have hδ1 : δ ≠ 1 := fun h => hxout ((hinn x).2 (by rw [hΘx, h]))
    have hδ3 : δ ^ 3 = 1 := by rw [← hΘx, ← map_pow, hV3 x hxV, map_one]
    rcases eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3 with h | h
    · rw [h] at hx
      exact ⟨x, hxV, hxout, g, hgT, Or.inl hx⟩
    · rw [h] at hx
      refine ⟨x, hxV, hxout, fieldActor (t := TwistTag.D4) σ σ g⁻¹, hTδ _ (inv_mem hgT),
        Or.inr ?_⟩
      rw [hx]
      exact inv_conj_mul_hom_inv (fieldActorHom (t := TwistTag.D4) σ) g σ
  · right
    push Not at hc1
    obtain ⟨e, heV, heout⟩ := hout
    obtain ⟨n, δ, hnN, hδ, hen⟩ := hV0 e heV
    have hnT : n ∉ T' := fun h => hc1 e heV heout n h δ hen
    have hΘe : Θ e = δ := by rw [hen]; exact hΘform n δ
    have hδ1 : δ ≠ 1 := fun h => heout ((hinn e).2 (by rw [hΘe, h]))
    have hδσ : δ = σ ∨ δ = σ⁻¹ := hδ.resolve_left hδ1
    obtain ⟨ι, hιV, hι1, hΘι⟩ :=
      exists_ker_of_card_nine Θ V hVc hV3 heV (by rw [hΘe]; exact hδ1)
    obtain ⟨v, hv⟩ := (hinn ι).2 hΘι
    have hv1 : v ≠ 1 := fun h => hι1 (by rw [← hv, h, map_one])
    have hv3 : v ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hv, hV3 ι hιV, map_one]
    have hvN : v ∈ T' ⊔ Subgroup.zpowers m' := by
      obtain ⟨g', δ', hg'N, -, hιg'⟩ := hV0 ι hιV
      have hδ' : δ' = 1 := (hΘ ι g' δ' hιg').symm.trans hΘι
      rw [hδ', fieldActor_one, mul_one] at hιg'
      have : v = g' := hinj (hv.trans hιg')
      rw [this]
      exact hg'N
    by_cases hvT : v ∈ T'
    · refine ⟨v, n, δ, hvT, hv1, hv3, by rw [hv]; exact hιV, hnN, hnT, hδσ,
        by rw [← hen]; exact heV, ?_⟩
      rw [← hen]
      have h := hVcomm e heV ι hιV
      rw [← hv] at h
      have h1 : e * MulAut.conj v = MulAut.conj (e v) * e := mulAut_mul_conj e v
      rw [h] at h1
      exact (hinj (mul_right_cancel h1)).symm
    · exfalso
      obtain ⟨j, hj⟩ := mnWeyl_exists_zpow_mul_mem hm'T hm'3 hm'n hnN hvN hvT
      obtain ⟨hDm, hDT⟩ := hstab δ hδσ
      have hg'' : n * fieldActor (t := TwistTag.D4) σ δ (v ^ j) ∈ T' := by
        have h1 := mnWeyl_inv_mul_apply_mem hm'3 hm'n (fieldActor (t := TwistTag.D4) σ δ) hDm
          hDT (zpow_mem hvN j)
        have e : n * fieldActor (t := TwistTag.D4) σ δ (v ^ j) =
            (n * v ^ j) * ((v ^ j)⁻¹ * fieldActor (t := TwistTag.D4) σ δ (v ^ j)) := by
          rw [mul_assoc, mul_inv_cancel_left]
        rw [e]
        exact mul_mem hj h1
      have hee : e * ι ^ j = MulAut.conj (n * fieldActor (t := TwistTag.D4) σ δ (v ^ j)) *
          fieldActor (t := TwistTag.D4) σ δ := by
        rw [hen, ← hv, ← map_zpow]
        exact conj_mul_hom_mul_conj (fieldActorHom (t := TwistTag.D4) σ) n (v ^ j) δ
      have hΘ' : Θ (e * ι ^ j) = δ := by rw [hee]; exact hΘform _ δ
      exact hc1 (e * ι ^ j) (mul_mem heV (zpow_mem hιV j))
        (fun h => hδ1 (hΘ'.symm.trans ((hinn _).1 h))) _ hg'' δ hee

end CFSG.GH74.GLS.Stage2.Bender.Thm1
