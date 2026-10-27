module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Layer
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectStd
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section SignGroup

variable (k : Type) [Field k]

@[expose] def e6SignDiagonalGroup : Subgroup (ModGL TwistTag.E6.tag k) where
  carrier := {y | ∃ b : Fin (Tag.rank .F4) → kˣ, (∀ j, b j = 1 ∨ b j = -1) ∧
    y = rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}
  mul_mem' := by
    rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
    refine ⟨b * b', fun i => ?_, (rootDiagUnit_mul _ _).symm⟩
    rcases hb i with h | h <;> rcases hb' i with h' | h' <;> simp [h, h']
  one_mem' := ⟨1, fun _ => Or.inl rfl, rootDiagUnit_one.symm⟩
  inv_mem' := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨b⁻¹, fun i => ?_, ?_⟩
    · rcases hb i with h | h <;> simp [h]
    · rw [rootDiagUnit_inv]
      rfl

theorem rootDiagUnit_mul_self_of_sign {b : Fin (Tag.rank .F4) → kˣ} (hb : ∀ j, b j = 1 ∨ b j = -1) :
    rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) *
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) = 1 := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_one (τ := TwistTag.E6.tag) (K := k)]
  congr 1
  funext l
  rcases hb (orbitMap l) with h | h <;> simp [h]

end SignGroup

section RootChar

variable {k : Type} [Field k]

theorem rootChar_orbitMap_aux (b : Fin (Tag.rank .F4) → kˣ) (v : Fin (Tag.rank .E6) → ℤ) :
    rootChar (τ := Tag.E6) (fun l => b (orbitMap l)) v =
      ∏ m, b m ^ CFSG.LieType.Steinberg.orbitSum orbitMap v m := by
  classical
  unfold rootChar CFSG.LieType.Steinberg.orbitSum
  rw [← Finset.prod_fiberwise Finset.univ orbitMap (fun l => b (orbitMap l) ^ v l)]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Finset.prod_congr rfl (g := fun l => b m ^ v l) (fun l hl => by
    rw [(Finset.mem_filter.1 hl).2])]
  exact (CFSG.LieType.Steinberg.Adjoint.zpow_finset_sum (b m) _ v).symm

theorem rootChar_orbitMap (b : Fin (Tag.rank .F4) → kˣ) (v : Fin (Tag.rank .E6) → ℤ) :
    rootChar (τ := TwistTag.E6.tag) (fun l => b (orbitMap l)) v =
      ∏ m, b m ^ CFSG.LieType.Steinberg.orbitSum orbitMap v m :=
  rootChar_orbitMap_aux b v

theorem rootChar_orbitMap_eq_one {b : Fin (Tag.rank .F4) → kˣ} {j : Fin (Tag.rank .F4)}
    (hb : b j = 1) {v : Fin (Tag.rank .E6) → ℤ}
    (hv : ∀ m, m ≠ j → CFSG.LieType.Steinberg.orbitSum orbitMap v m = 0) :
    rootChar (τ := TwistTag.E6.tag) (fun l => b (orbitMap l)) v = 1 := by
  rw [rootChar_orbitMap]
  refine Finset.prod_eq_one fun m _ => ?_
  by_cases hm : m = j
  · rw [hm, hb, one_zpow]
  · rw [hv m hm, zpow_zero]

end RootChar

section Generic

variable {τ : Tag} {K : Type} [Field K]

theorem pinnedX_mul_rootDiagUnit_of_rootChar_eq_one (a : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h : rootChar a α = 1) (c : K) :
    pinnedX τ K α c * rootDiagUnit τ a = rootDiagUnit τ a * pinnedX τ K α c := by
  have h2 := rootDiagUnit_conj_pinnedX a hα c
  rw [h, Units.val_one, one_mul] at h2
  calc pinnedX τ K α c * rootDiagUnit τ a
      = (rootDiagUnit τ a * pinnedX τ K α c * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by
        rw [h2]
    _ = rootDiagUnit τ a * pinnedX τ K α c := by group

end Generic

section Phi

variable (p e : ℕ) [Fact p.Prime]

@[expose] noncomputable def twistedE6PhiAmbient :
    e6Data_valid.minGroup (GaloisField p (2 * e)) →*
      ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * e))) :=
  (baseChangeGL
      (algebraMap (GaloisField p (2 * e)) (AlgebraicClosure (GaloisField p (2 * e))))).comp
    ((adjointGroup TwistTag.E6.tag (GaloisField p (2 * e))).subtype.comp
      (CFSG.LieType.Steinberg.Isogeny.e6IsogenyT (GaloisField p (2 * e))))

theorem twistedE6Phi_eq_ambient (g : twistedE6Group p e) :
    twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) g =
      twistedE6PhiAmbient p e (g : e6Data_valid.minGroup (GaloisField p (2 * e))) := rfl

theorem twistedE6PhiAmbient_xm {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (d : GaloisField p (2 * e)) :
    twistedE6PhiAmbient p e (e6Data_valid.xm (GaloisField p (2 * e)) α d) =
      pinnedX TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * e))) α
        (algebraMap (GaloisField p (2 * e)) (AlgebraicClosure (GaloisField p (2 * e)))
          (e6Sign α * d)) := by
  show baseChangeGL (algebraMap (GaloisField p (2 * e)) (AlgebraicClosure (GaloisField p (2 * e))))
    ((CFSG.LieType.Steinberg.Isogeny.e6IsogenyT (GaloisField p (2 * e))
      (e6Data_valid.xm (GaloisField p (2 * e)) α d) :
        ↥(adjointGroup TwistTag.E6.tag (GaloisField p (2 * e)))) :
          ModGL TwistTag.E6.tag (GaloisField p (2 * e))) = _
  have h1 := coe_e6Isogeny_xm (K := GaloisField p (2 * e)) hα d
  have h2 := baseChangeGL_pinnedX (algebraMap (GaloisField p (2 * e))
    (AlgebraicClosure (GaloisField p (2 * e)))) (τ := TwistTag.E6.tag) α (↑(e6Sign α) * d)
  exact (congrArg (baseChangeGL (algebraMap (GaloisField p (2 * e))
    (AlgebraicClosure (GaloisField p (2 * e))))) h1).trans h2

theorem twistedE6PhiAmbient_rootGroup_commute {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    {b : Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ}
    (hb : rootChar (τ := TwistTag.E6.tag) (fun l => b (orbitMap l)) α = 1)
    {g : e6Data_valid.minGroup (GaloisField p (2 * e))}
    (hg : g ∈ e6Data_valid.rootGroup (GaloisField p (2 * e)) α) :
    twistedE6PhiAmbient p e g * rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) * twistedE6PhiAmbient p e g := by
  obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField p (2 * e))).1 hg
  rw [twistedE6PhiAmbient_xm p e hα]
  exact pinnedX_mul_rootDiagUnit_of_rootChar_eq_one (τ := TwistTag.E6.tag) _ hα hb _

theorem twistedE6Phi_commute_of_sign (j : Fin (Tag.rank .F4)) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : ∀ m, m ≠ j → β m = 0)
    {b : Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ} (hb : b j = 1)
    {g : twistedE6Group p e}
    (hg : g ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) β) :
    twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) g *
        rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) *
        twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) g := by
  have hgen : ∀ α : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 α →
      (∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum orbitMap α = c • β) →
      e6Data_valid.rootGroup (GaloisField p (2 * e)) α ≤ (Subgroup.centralizer
        {rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}).comap
          (twistedE6PhiAmbient p e) := by
    intro α hα hc g' hg'
    obtain ⟨c, -, hαc⟩ := hc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact twistedE6PhiAmbient_rootGroup_commute p e hα
      (rootChar_orbitMap_eq_one hb fun m hm => by rw [hαc]; simp [hβ m hm]) hg'
  have hg' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1
  have hle : (⨆ α ∈ {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum orbitMap α = c • β),
        e6Data_valid.rootGroup (GaloisField p (2 * e)) α) ≤ (Subgroup.centralizer
          {rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}).comap
            (twistedE6PhiAmbient p e) :=
    iSup₂_le fun α hα => iSup_le fun hc => hgen α hα hc
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg')

end Phi

section RankOne

variable (p e : ℕ) [Fact p.Prime]

noncomputable abbrev e6RankOne (j : Fin (Tag.rank .F4)) : Subgroup (twistedE6Group p e) :=
  CFSG.LieType.CurtisTits.rankOne (twistedE6Datum p e).rootGroup j

theorem twistedE6_rankOne_perfect (he : 1 ≤ e) (h4 : 4 ≤ p ^ e) (j : Fin (Tag.rank .F4)) :
    e6RankOne p e j ≤ ⁅e6RankOne p e j, e6RankOne p e j⁆ := by
  have hθ := frobQ_frobQ p e he
  have h4F : 4 ≤ Nat.card
      (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField (frobQ p e)) := by
    rw [CFSG.ClassicalInvolution.WeakCT.card_fixedField_frobQ p e he]
    exact h4
  have h4K : 4 ≤ Nat.card (GaloisField p (2 * e)) := by
    rw [card_galoisField_two_mul' p e he]
    calc 4 ≤ p ^ e := h4
      _ ≤ (p ^ e) ^ TwistTag.E6.order := Nat.le_self_pow (by decide) _
  fin_cases j
  · have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_zero (frobQ p e)
    have hr := fundPerfect_range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4F)
      (CFSG.ClassicalInvolution.WeakCT.nodeHom0 (frobQ p e))
    rw [← h] at hr
    exact hr
  · have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_one (frobQ p e)
    have hr := fundPerfect_range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4F)
      (CFSG.ClassicalInvolution.WeakCT.nodeHom1 (frobQ p e))
    rw [← h] at hr
    exact hr
  · have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_two (frobQ p e) hθ
    have hr := fundPerfect_range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4K)
      (CFSG.ClassicalInvolution.WeakCT.nodeHom2 (frobQ p e) hθ)
    rw [← h] at hr
    exact hr
  · have h := CFSG.ClassicalInvolution.WeakCT.rankOne_twistedE6_three (frobQ p e) hθ
    have hr := fundPerfect_range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4K)
      (CFSG.ClassicalInvolution.WeakCT.nodeHom3 (frobQ p e) hθ)
    rw [← h] at hr
    exact hr

end RankOne

section Layers

variable (p e : ℕ) [Fact p.Prime]

theorem twistedE6Phi_rankOne_commute (j : Fin (Tag.rank .F4))
    {b : Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ} (hb : b j = 1)
    {g : twistedE6Group p e} (hg : g ∈ e6RankOne p e j) :
    twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) g *
        rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) *
        twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) g := by
  have hle : e6RankOne p e j ≤ (Subgroup.centralizer
      {rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))}).comap
        (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e)))) := by
    have hsing : ∀ m : Fin (Tag.rank .F4), m ≠ j →
        (Pi.single j (1 : ℤ) : Fin (Tag.rank .F4) → ℤ) m = 0 := fun m hm =>
      Pi.single_eq_of_ne hm 1
    have hnsing : ∀ m : Fin (Tag.rank .F4), m ≠ j →
        (-Pi.single j (1 : ℤ) : Fin (Tag.rank .F4) → ℤ) m = 0 := fun m hm => by
      simp [Pi.single_eq_of_ne hm]
    refine sup_le (fun g' hg' => ?_) (fun g' hg' => ?_)
    · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact twistedE6Phi_commute_of_sign p e j hsing hb hg'
    · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact twistedE6Phi_commute_of_sign p e j hnsing hb hg'
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem twistedE6_rankOne_le_centralizer (he : 1 ≤ e) (h4 : 4 ≤ p ^ e) (j : Fin (Tag.rank .F4))
    {s : twistedE6Group p e} {b : Fin (Tag.rank .F4) →
      (AlgebraicClosure (GaloisField p (2 * e)))ˣ}
    (hΦ : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))) (hb : b j = 1) :
    e6RankOne p e j ≤ Subgroup.centralizer ({s} : Set (twistedE6Group p e)) := by
  have hperf := twistedE6_rankOne_perfect p e he h4 j
  have hc : ∀ r ∈ e6RankOne p e j, ⁅s, r⁆ ∈ Subgroup.center (twistedE6Group p e) := by
    intro r hr
    refine ker_twistedE6Phi_le_center p e (AlgebraicClosure (GaloisField p (2 * e))) ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hΦ]
    have h := twistedE6Phi_rankOne_commute p e j hb hr
    calc rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)) *
          twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r *
          (rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))⁻¹ *
          (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r)⁻¹
        = (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r *
          rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))) *
          (rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l)))⁻¹ *
          (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) r)⁻¹ := by rw [h]
      _ = 1 := by group
  intro r hr
  exact Subgroup.mem_centralizer_singleton_iff.2
    (CFSG.ClassicalInvolution.RouteD.Exotic.commutes_of_commutator_mem_center hperf hc r hr).symm

theorem twistedE6_rankOne_le_iSup_components (hp2 : p ≠ 2) (he : 1 ≤ e) (h5 : 5 ≤ p ^ e)
    (j : Fin (Tag.rank .F4)) {s : twistedE6Group p e}
    {b : Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ}
    (hb' : ∀ i, b i = 1 ∨ b i = -1)
    (hΦ : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s =
      rootDiagUnit TwistTag.E6.tag (fun l => b (orbitMap l))) (hj : b j = 1) :
    e6RankOne p e j ≤ ⨆ (Q : Subgroup (twistedE6Group p e))
      (_ : CFSG.Open.IsComponentOf Q
        (Subgroup.centralizer ({s} : Set (twistedE6Group p e)))), Q := by
  refine twistedE6_le_iSup_components p e hp2 he (by omega) ?_
    (twistedE6_rankOne_perfect p e he (by omega) j)
    (twistedE6_rankOne_le_centralizer p e he (by omega) j hΦ hj)
  rw [hΦ]
  exact rootDiagUnit_mul_self_of_sign _ hb'

theorem twistedE6_toralLayers (hp2 : p ≠ 2) (he : 1 ≤ e) (h5 : 5 ≤ p ^ e)
    (j : Fin (Tag.rank .F4)) {s₁ s₂ : twistedE6Group p e}
    (h₁ : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s₁ ∈
      e6SignDiagonalGroup (AlgebraicClosure (GaloisField p (2 * e))))
    (h₂ : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s₂ ∈
      e6SignDiagonalGroup (AlgebraicClosure (GaloisField p (2 * e)))) :
    ∃ s ∈ ({s₁, s₂, s₁ * s₂} : Set (twistedE6Group p e)),
      e6RankOne p e j ≤ ⨆ (Q : Subgroup (twistedE6Group p e))
        (_ : CFSG.Open.IsComponentOf Q
          (Subgroup.centralizer ({s} : Set (twistedE6Group p e)))), Q := by
  obtain ⟨b₁, hb₁, e₁⟩ := h₁
  obtain ⟨b₂, hb₂, e₂⟩ := h₂
  by_cases hj₁ : b₁ j = 1
  · exact ⟨s₁, Or.inl rfl, twistedE6_rankOne_le_iSup_components p e hp2 he h5 j hb₁ e₁ hj₁⟩
  by_cases hj₂ : b₂ j = 1
  · exact ⟨s₂, Or.inr (Or.inl rfl),
      twistedE6_rankOne_le_iSup_components p e hp2 he h5 j hb₂ e₂ hj₂⟩
  have h1 : b₁ j = -1 := (hb₁ j).resolve_left hj₁
  have h2 : b₂ j = -1 := (hb₂ j).resolve_left hj₂
  refine ⟨s₁ * s₂, Or.inr (Or.inr rfl), twistedE6_rankOne_le_iSup_components p e hp2 he h5 j
    (b := b₁ * b₂) (fun i => ?_) ?_ ?_⟩
  · rcases hb₁ i with h | h <;> rcases hb₂ i with h' | h' <;> simp [h, h']
  · have : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) (s₁ * s₂) =
        twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s₁ *
          twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) s₂ :=
      map_mul (twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e)))) s₁ s₂
    rw [this, e₁, e₂, ← rootDiagUnit_mul]
    rfl
  · simp [h1, h2]

end Layers

end CFSG.ClassicalInvolution.ModelFacts
