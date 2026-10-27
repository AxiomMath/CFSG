module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly

theorem stOrderBody_of_action {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {H : Type} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) (hZ : Odd (Nat.card Z)) (ρ : (K ≃+* K) →* MulAut H)
    (good : (K ≃+* K) → Prop) (hgood : ∀ σ, good σ → ∀ n : ℕ, good (σ ^ n)) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hordH : twoPart (Nat.card H) ^ v = 2 ^ (m * u))
    (hfix : ∀ σ, good σ → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (fixNum (ρ σ)) ^ v = 2 ^ (e * u))
    {p : ℕ} (hp : p.Prime) (hred : ∀ σ : K ≃+* K, ∃ n : ℕ, ¬ p ∣ n ∧ good (σ ^ n))
    (I F : Set (MulAut (H ⧸ Z)))
    (hF : ∀ f ∈ F, ∃ σ : K ≃+* K, ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ σ x)) :
    StOrderBody p (H ⧸ Z) I F := by
  intro f hf hord
  obtain ⟨σ, hσ⟩ := hF f hf
  exact stOrder_core_red hm hK Z hZc hZ ρ good hgood hu hv hordH hfix hp hred f σ hσ hord

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

abbrev fixF (σ : K ≃+* K) : Subfield K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)

theorem mem_fixF {σ : K ≃+* K} {x : K} : x ∈ fixF σ ↔ σ x = x := Iff.rfl

theorem exists_descend (σ : K ≃+* K) (h : GL ι K)
    (hf : Matrix.GeneralLinearGroup.map σ.toRingHom h = h) :
    ∃ A : GL ι (fixF σ), Matrix.GeneralLinearGroup.map (fixF σ).subtype A = h := by
  have hent : ∀ i j, σ ((h : Matrix ι ι K) i j) = (h : Matrix ι ι K) i j := by
    intro i j
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i j) hf
    simpa [coe_glMap] using this
  let N : Matrix ι ι (fixF σ) := Matrix.of fun i j => ⟨(h : Matrix ι ι K) i j, hent i j⟩
  have hN : N.map (fixF σ).subtype = (h : Matrix ι ι K) := by
    ext i j; rfl
  have hdet : N.det ≠ 0 := by
    intro h0
    have h1 : (fixF σ).subtype N.det = (h : Matrix ι ι K).det := by
      rw [← hN]
      exact (RingHom.map_det (fixF σ).subtype N)
    rw [h0, map_zero] at h1
    have hu : IsUnit (h : Matrix ι ι K).det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    rw [← h1] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero N hdet, ?_⟩
  ext i j
  exact congrArg (fun M : Matrix ι ι K => M i j) hN

theorem glMap_subtype_injective (σ : K ≃+* K) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) (fixF σ).subtype) := by
  intro A B hAB
  ext i j
  have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i j) hAB
  exact this

theorem glMap_subtype_fixed (σ : K ≃+* K) (A : GL ι (fixF σ)) :
    Matrix.GeneralLinearGroup.map σ.toRingHom
        (Matrix.GeneralLinearGroup.map (fixF σ).subtype A) =
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A := by
  ext i j
  have h : σ ((A i j : fixF σ) : K) = ((A i j : fixF σ) : K) := (A i j).2
  simpa [coe_glMap] using h

theorem card_fixed_eq_of_iff (σ : K ≃+* K) (H : Subgroup (GL ι K)) (Hk : Subgroup (GL ι (fixF σ)))
    (hiff : ∀ A : GL ι (fixF σ),
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ H ↔ A ∈ Hk) :
    Nat.card {h : H // Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K) = h} =
      Nat.card Hk := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun A : Hk => (⟨⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype A, (hiff A).2 A.2⟩,
      glMap_subtype_fixed σ A.1⟩ : {h : H // Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K) = h}))
    ⟨?_, ?_⟩)
  · intro A B hAB
    apply Subtype.ext
    exact glMap_subtype_injective σ (congrArg (fun h => ((h.1 : H) : GL ι K)) hAB)
  · rintro ⟨⟨h, hh⟩, hfix⟩
    obtain ⟨A, hA⟩ := exists_descend σ h hfix
    have hAk : A ∈ Hk := (hiff A).1 (hA ▸ hh)
    exact ⟨⟨A, hAk⟩, Subtype.ext (Subtype.ext hA)⟩

@[expose] noncomputable def matAct (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H) :
    (K ≃+* K) →* MulAut H where
  toFun σ :=
    { toFun := fun h => ⟨Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K), hH σ h h.2⟩
      invFun := fun h => ⟨Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom (h : GL ι K), hH σ⁻¹ h h.2⟩
      left_inv := fun h => Subtype.ext (by
        change Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom
          (Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K)) = h
        rw [← glMap_mul, inv_mul_cancel, glMap_one])
      right_inv := fun h => Subtype.ext (by
        change Matrix.GeneralLinearGroup.map σ.toRingHom
          (Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom (h : GL ι K)) = h
        rw [← glMap_mul, mul_inv_cancel, glMap_one])
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun h => Subtype.ext (glMap_one (h : GL ι K))
  map_mul' := fun a b => MulEquiv.ext fun h => Subtype.ext (glMap_mul a b (h : GL ι K))

theorem matAct_coe (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (σ : K ≃+* K) (h : H) :
    ((matAct H hH σ h : H) : GL ι K) = Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K) :=
  rfl

theorem fixNum_matAct (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (σ : K ≃+* K) :
    fixNum (matAct H hH σ) =
      Nat.card {h : H // Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K) = h} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun h => by
    rw [← Subtype.coe_inj]; rfl)

theorem matField_spec (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    {f : MulAut (LargeEvenProj H)} (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk H)) :
    ∃ σ : K ≃+* K, ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (matAct H hH σ x) := by
  obtain ⟨σ, hσ⟩ := hf
  refine ⟨σ, fun x => ?_⟩
  exact hσ x (matAct H hH σ x) (by
    show ((matAct H hH σ x : H) : GL ι K).val = (x : GL ι K).val.map σ
    rw [matAct_coe]
    rfl)

section Fixed

theorem one_le_of_card_fixed [Finite K] {σ : K ≃+* K} {e : ℕ} (he : Nat.card {x : K // σ x = x} = 2 ^ e) :
    1 ≤ e := by
  have : Nontrivial {x : K // σ x = x} :=
    ⟨⟨⟨0, map_zero σ⟩, ⟨1, map_one σ⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  have h1 : 1 < Nat.card {x : K // σ x = x} := Finite.one_lt_card
  rw [he] at h1
  by_contra h0
  have : e = 0 := by omega
  rw [this] at h1
  simp at h1

theorem card_fixF {σ : K ≃+* K} : Nat.card (fixF σ) = Nat.card {x : K // σ x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixF)

end Fixed

theorem mem_closure_iff_of_mul_closed {G : Type*} [Group G] [Finite G] (S : Set G)
    (h1 : (1 : G) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {g : G} :
    g ∈ Subgroup.closure S ↔ g ∈ S := by
  refine ⟨fun hg => ?_, fun hg => Subgroup.subset_closure hg⟩
  have hpow : ∀ x ∈ S, ∀ n : ℕ, x ^ n ∈ S := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  let T : Subgroup G :=
    { carrier := S
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := h1
      inv_mem' := fun {x} hx => by
        have hpos : 0 < orderOf x := orderOf_pos x
        have h1' : x⁻¹ = x ^ (orderOf x - 1) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [h1']
        exact hpow x hx _ }
  exact (Subgroup.closure_le T).2 (fun x hx => hx) hg

section Scalars

theorem scalars_subgroupOf_le_center (H : Subgroup (GL ι K)) :
    (CFSG.Open.StatedScalars ι K).subgroupOf H ≤ Subgroup.center H := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hz' : (z : GL ι K) ∈ (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K).range := hz
  obtain ⟨c, hc⟩ := hz'
  apply Subtype.ext
  show (g : GL ι K) * (z : GL ι K) = (z : GL ι K) * (g : GL ι K)
  rw [← hc]
  exact (Matrix.GeneralLinearGroup.scalar_commute c (g : GL ι K)).symm

theorem scalars_subgroupOf_odd [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (H : Subgroup (GL ι K)) :
    Odd (Nat.card ((CFSG.Open.StatedScalars ι K).subgroupOf H)) := by
  have h1 : Nat.card ((CFSG.Open.StatedScalars ι K).subgroupOf H) ∣
      Nat.card (CFSG.Open.StatedScalars ι K) := by
    have e : Nat.card (((CFSG.Open.StatedScalars ι K).subgroupOf H).map H.subtype) =
        Nat.card ((CFSG.Open.StatedScalars ι K).subgroupOf H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← e]
    exact Subgroup.card_dvd_of_le (by
      rintro _ ⟨z, hz, rfl⟩
      exact hz)
  have h2 : Nat.card (CFSG.Open.StatedScalars ι K) ∣ Nat.card Kˣ :=
    Subgroup.card_range_dvd (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K)
  have h3 : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  exact Odd.of_dvd_nat h3 (h1.trans h2)

end Scalars

theorem stOrderBody_of_matrix [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (good : (K ≃+* K) → Prop) (hgood : ∀ σ, good σ → ∀ n : ℕ, good (σ ^ n))
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hordH : twoPart (Nat.card H) ^ v = 2 ^ (m * u))
    (hfix : ∀ σ, good σ → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (Nat.card {h : H // Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL ι K) = h}) ^ v =
        2 ^ (e * u))
    {p : ℕ} (hp : p.Prime) (hred : ∀ σ : K ≃+* K, ∃ n : ℕ, ¬ p ∣ n ∧ good (σ ^ n))
    (I : Set (MulAut (LargeEvenProj H))) :
    StOrderBody p (LargeEvenProj H) I (LargeEvenMatFieldImage (LargeEvenProjMk H)) := by
  intro f hf hord
  obtain ⟨σ, hσ⟩ := matField_spec H hH hf
  exact stOrder_core_red hm hK ((CFSG.Open.StatedScalars ι K).subgroupOf H)
    (scalars_subgroupOf_le_center H) (scalars_subgroupOf_odd hm hK H) (matAct H hH) good hgood hu hv
    hordH (fun σ hσ e he => by rw [fixNum_matAct]; exact hfix σ hσ e he) hp hred f σ hσ hord

end Mat

end FQ

end CFSG.LocalAnalysis.GLTheoremA
