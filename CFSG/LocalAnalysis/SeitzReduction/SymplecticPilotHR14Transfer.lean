module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueReduce
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueBasic

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem le_spGlobal_of_injective_commute (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (φ : spGlobal e →* G) (hφ : Function.Injective φ)
    (hφt : ∀ x : spGlobal e, (x : G) * t = t * x → φ x * t = t * φ x) :
    φ.range ≤ spGlobal e := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  have hSpP : Group.IsPerfect (StatedSp n K) := isPerfect_statedSp_of_charTwo hn
  have hLP : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLsP : Group.IsPerfect (L.subgroupOf (spGlobal e)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLS).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hLφP : Group.IsPerfect ((L.subgroupOf (spGlobal e)).map φ) :=
    Group.IsPerfect.ofSurjective (f := φ.subgroupMap _) (φ.subgroupMap_surjective _)
  have hLφt : (L.subgroupOf (spGlobal e)).map φ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    refine hφt x ?_
    have hx' : (x : G) ∈ L := hx
    exact mem_centralizer_iff.1 htC (x : G) hx'
  have hLφL : (L.subgroupOf (spGlobal e)).map φ ≤ L :=
    std_perfect_le hset.standardSetting hOut htC ht (Subgroup.isPerfect_iff.mp hLφP) hLφt
  let α : L →* L :=
    { toFun := fun x => ⟨φ ⟨x, hLS x.2⟩, hLφL ⟨⟨x, hLS x.2⟩, x.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        change φ ⟨1, _⟩ = 1
        exact φ.map_one
      map_mul' := fun x y => by
        apply Subtype.ext
        change φ (⟨(x : G), hLS x.2⟩ * ⟨(y : G), hLS y.2⟩) = φ ⟨x, _⟩ * φ ⟨y, _⟩
        exact φ.map_mul _ _ }
  have hαinj : Function.Injective α := by
    intro x y hxy
    have h1 : φ ⟨x, hLS x.2⟩ = φ ⟨y, hLS y.2⟩ := congrArg Subtype.val hxy
    have h2 := congrArg Subtype.val (hφ h1)
    exact Subtype.ext h2
  let αE : L ≃* L := MulEquiv.ofBijective α hαinj.bijective_of_finite
  obtain ⟨s, σ, hβ⟩ := exists_eq_conj_mul_fieldSp hn ((e.symm.trans αE).trans e)
  set l : G := ((e.symm s : L) : G) with hl
  have hlS : l ∈ spGlobal e := hLS (e.symm s).2
  have hkey : ∀ x : StatedSp n K, φ ⟨((e.symm x : L) : G), hLS (e.symm x).2⟩ =
      l * ((e.symm (fieldSp n K σ x) : L) : G) * l⁻¹ := by
    intro x
    have h1 := congrArg (fun γ : MulAut (StatedSp n K) => γ x) hβ
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 : αE (e.symm x) = e.symm (s * fieldSp n K σ x * s⁻¹) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    have h3 := congrArg Subtype.val h2
    rw [map_mul, map_mul, map_inv] at h3
    exact h3
  have hpiece : ∀ (j : Fin n) (y : G) (hy : y ∈ pieceCore e ({j} : Finset (Fin n))),
      ∀ hyS : y ∈ spGlobal e, φ ⟨y, hyS⟩ ∈ spGlobal e := by
    intro j y hy hyS
    set T := leviTorusSp K ({j} : Finset (Fin n)) with hT
    have hPle : pieceCore e ({j} : Finset (Fin n)) ≤ spGlobal e := by
      rw [spGlobal_def]
      exact le_iSup (fun i : Fin n => pieceCore e ({i} : Finset (Fin n))) j
    set P := pieceCore e ({j} : Finset (Fin n)) with hP
    set Q : Subgroup G := ((P.subgroupOf (spGlobal e)).map φ).map (MulAut.conj l⁻¹).toMonoidHom
      with hQ
    have hPP : Group.IsPerfect P :=
      Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore _)
    have hPsP : Group.IsPerfect (P.subgroupOf (spGlobal e)) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPle).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hPφP : Group.IsPerfect ((P.subgroupOf (spGlobal e)).map φ) :=
      Group.IsPerfect.ofSurjective (f := φ.subgroupMap _) (φ.subgroupMap_surjective _)
    have hQP : Group.IsPerfect Q :=
      Group.IsPerfect.ofSurjective (f := (MulAut.conj l⁻¹).toMonoidHom.subgroupMap _)
        (MonoidHom.subgroupMap_surjective _ _)
    have hQc : Q ≤ centralizer (modelToG e T : Set G) := by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hz' : (z : G) ∈ P := hz
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hh
      have hx' : fieldSp n K σ⁻¹ x ∈ T := fieldSp_mem_leviTorusSp σ⁻¹ hx
      have hσ : fieldSp n K σ (fieldSp n K σ⁻¹ x) = x := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      have hk := hkey (fieldSp n K σ⁻¹ x)
      rw [hσ] at hk
      have hzc : (z : G) * ((e.symm (fieldSp n K σ⁻¹ x) : L) : G) =
          ((e.symm (fieldSp n K σ⁻¹ x) : L) : G) * (z : G) := by
        have := mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ hz')
          _ ((mem_modelToG e).2 ⟨_, hx', rfl⟩)
        exact this.symm
      have hφc : φ z * φ ⟨((e.symm (fieldSp n K σ⁻¹ x) : L) : G), hLS (e.symm _).2⟩ =
          φ ⟨((e.symm (fieldSp n K σ⁻¹ x) : L) : G), hLS (e.symm _).2⟩ * φ z := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hzc
      rw [hk] at hφc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc ((e.symm x : L) : G) * (l⁻¹ * φ z * l) =
          l⁻¹ * ((l * ((e.symm x : L) : G) * l⁻¹) * φ z) * l := by group
        _ = l⁻¹ * (φ z * (l * ((e.symm x : L) : G) * l⁻¹)) * l := by rw [hφc]
        _ = l⁻¹ * φ z * l * ((e.symm x : L) : G) := by group
    have hQle : Q ≤ P :=
      F4Pilot.le_centralizerPerfectCore (Subgroup.isPerfect_iff.mp hQP) hQc
    have hmem : l⁻¹ * φ ⟨y, hyS⟩ * l ∈ Q := by
      refine ⟨φ ⟨y, hyS⟩, ⟨⟨y, hyS⟩, hy, rfl⟩, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h1 : l⁻¹ * φ ⟨y, hyS⟩ * l ∈ spGlobal e := hPle (hQle hmem)
    have h2 : φ ⟨y, hyS⟩ = l * (l⁻¹ * φ ⟨y, hyS⟩ * l) * l⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hlS h1) (inv_mem hlS)
  have hall : spGlobal e ≤ ((spGlobal e).comap φ).map (spGlobal e).subtype := by
    conv_lhs => rw [spGlobal_def]
    refine iSup_le fun j => ?_
    intro y hy
    have hyS : y ∈ spGlobal e := by
      rw [spGlobal_def]
      exact le_iSup (fun i : Fin n => pieceCore e ({i} : Finset (Fin n))) j hy
    exact ⟨⟨y, hyS⟩, hpiece j y hy hyS, rfl⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨a, ha, haz⟩ := hall z.2
  have : a = z := Subtype.ext haz
  rw [← this]
  exact ha

theorem mem_normalizer_of_conj_mulAut (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (htN : t ∈ normalizer (spGlobal e : Set G)) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) (β : MulAut (spGlobal e))
    (hβ : β * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
      (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β) :
    g ∈ normalizer (spGlobal e : Set G) := by
  let φ : (spGlobal e) →* G := (MulAut.conj g).toMonoidHom.comp ((spGlobal e).subtype.comp β.toMonoidHom)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : g * ((β x : (spGlobal e)) : G) * g⁻¹ = g * ((β y : (spGlobal e)) : G) * g⁻¹ := hxy
    have h2 : ((β x : (spGlobal e)) : G) = ((β y : (spGlobal e)) : G) := by
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    exact β.injective (Subtype.ext h2)
  have hφt : ∀ x : (spGlobal e), (x : G) * t = t * x → φ x * t = t * φ x := by
    intro x hx
    have hfix : (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ x = x := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * (x : G) * t⁻¹ = x
      rw [← hx, mul_inv_cancel_right]
    have h1 := congrArg (fun γ : MulAut (spGlobal e) => γ x) hβ
    simp only [MulAut.mul_apply] at h1
    rw [hfix] at h1
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    change ((β x : (spGlobal e)) : G) = (g⁻¹ * t * g) * ((β x : (spGlobal e)) : G) * (g⁻¹ * t * g)⁻¹ at h2
    change g * ((β x : (spGlobal e)) : G) * g⁻¹ * t = t * (g * ((β x : (spGlobal e)) : G) * g⁻¹)
    have h3 : ((β x : (spGlobal e)) : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * ((β x : (spGlobal e)) : G) := by
      calc ((β x : (spGlobal e)) : G) * (g⁻¹ * t * g) =
          ((g⁻¹ * t * g) * ((β x : (spGlobal e)) : G) * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by rw [← h2]
        _ = (g⁻¹ * t * g) * ((β x : (spGlobal e)) : G) := by group
    calc g * ((β x : (spGlobal e)) : G) * g⁻¹ * t = g * (((β x : (spGlobal e)) : G) * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * ((β x : (spGlobal e)) : G)) * g⁻¹ := by rw [h3]
      _ = t * (g * ((β x : (spGlobal e)) : G) * g⁻¹) := by group
  have hle := le_spGlobal_of_injective_commute hset hn hKc hf e ht hKt φ hφ hφt
  have hconj : ∀ y ∈ (spGlobal e), g * y * g⁻¹ ∈ (spGlobal e) := by
    intro y hy
    refine hle ⟨β.symm ⟨y, hy⟩, ?_⟩
    change g * ((β (β.symm ⟨y, hy⟩) : (spGlobal e)) : G) * g⁻¹ = g * y * g⁻¹
    rw [MulEquiv.apply_symm_apply]
  have hmap : (spGlobal e).map (MulAut.conj g).toMonoidHom ≤ (spGlobal e) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hconj y hy
  have hcard : Nat.card ((spGlobal e).map (MulAut.conj g).toMonoidHom) = Nat.card (spGlobal e) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : (spGlobal e).map (MulAut.conj g).toMonoidHom = (spGlobal e) :=
    Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm)
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hconj h hh
  · intro hh
    rw [← heq] at hh
    obtain ⟨y, hy, hyh⟩ := hh
    have : y = h := by
      change g * y * g⁻¹ = g * h * g⁻¹ at hyh
      simpa using hyh
    exact this ▸ hy

end Transfer

@[expose] def SpGraphStandardClassInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ (htN : t ∈ normalizer (spGlobal e : Set G)) (g : G)
        (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
        ∃ β : MulAut (spGlobal e), β * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
          (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β

theorem spOmegaRowUniqueInput_of_standardClass {κ : Sp2mKind}
    (h : SpGraphStandardClassInput κ) : SpOmegaRowUniqueInput κ := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  obtain ⟨β, hβ⟩ := h G L hset n f K hn hKc hf e t ht hKt hroot hglob htN g hg
  exact mem_normalizer_of_conj_mulAut hset (by omega) hKc hf e ht hKt htN hg β hβ

end CFSG.SeitzReduction.SymplecticPilot
