module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

section Cubes

theorem exists_cube_mul_or {G : Type*} [Group G] [IsCyclic G] {u v : G}
    (hu : ∀ w : G, w ^ 3 ≠ u) (hv : ∀ w : G, w ^ 3 ≠ v) :
    (∃ w : G, w ^ 3 = u * v⁻¹) ∨ ∃ w : G, w ^ 3 = u * v := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ v)
  have hcube : ∀ k : ℤ, k % 3 = 0 → ∃ w : G, w ^ 3 = γ ^ k := fun k hk => ⟨γ ^ (k / 3), by
    rw [← zpow_natCast, ← zpow_mul, show ((3 : ℕ) : ℤ) = 3 from rfl,
      Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hk)]⟩
  have hi : i % 3 ≠ 0 := fun h => by
    obtain ⟨w, hw⟩ := hcube i h
    exact hu w hw
  have hj : j % 3 ≠ 0 := fun h => by
    obtain ⟨w, hw⟩ := hcube j h
    exact hv w hw
  have hi' : i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj' : j % 3 = 1 ∨ j % 3 = 2 := by omega
  have h' : (i - j) % 3 = 0 ∨ (i + j) % 3 = 0 := by
    rw [Int.sub_emod, Int.add_emod]
    rcases hi' with h1 | h1 <;> rcases hj' with h2 | h2 <;> rw [h1, h2] <;> norm_num
  rcases h' with h | h
  · left
    rw [← zpow_neg, ← zpow_add, ← sub_eq_add_neg]
    exact hcube _ h
  · right
    rw [← zpow_add]
    exact hcube _ h

end Cubes

section Det

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

@[expose] def IsInnerMat (π : Bool) (q : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K) : Prop :=
  ∃ l ∈ slPi π 3 q K, ∃ z ∈ StatedScalars (Fin 3) K, y = l * z

@[expose] noncomputable def detRoot (hK : PiField π p f K) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) : ↥(rootsOfUnity (qSubPi π (p ^ f)) K) :=
  ⟨Matrix.GeneralLinearGroup.det y, det_mem_rootsOfUnity hK hy⟩

theorem isInnerMat_of_detRoot (hK : PiField π p f K) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) {μ : ↥(rootsOfUnity (qSubPi π (p ^ f)) K)}
    (hμ : μ ^ 3 = detRoot hK hy) : IsInnerMat π (p ^ f) K y := by
  have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = ((μ : Kˣ) : K) ^ 3 := by
    have h := congrArg (fun w : ↥(rootsOfUnity (qSubPi π (p ^ f)) K) => ((w : Kˣ) : K)) hμ
    simp only [detRoot, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply] at h
    exact h.symm
  obtain ⟨l, hl, ⟨z, hz⟩, -⟩ := exists_inner_of_det_eq_cube hK hy
    ((scalar_mem_glPi_iff hK _).2 μ.2) hdet
  exact ⟨l, hl, _, ⟨z, rfl⟩, hz⟩

theorem inner_or_of_det (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {y y' : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) (hy' : y' ∈ glPi π 3 (p ^ f) K)
    (hny : ¬ IsInnerMat π (p ^ f) K y) :
    IsInnerMat π (p ^ f) K y' ∨ IsInnerMat π (p ^ f) K (y' * y⁻¹) ∨
      IsInnerMat π (p ^ f) K (y' * y) := by
  have := hK.finite
  have hN : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  haveI := rootsOfUnity.isCyclic K (qSubPi π (p ^ f))
  by_cases hc : ∃ μ, μ ^ 3 = detRoot hK hy'
  · obtain ⟨μ, hμ⟩ := hc
    exact Or.inl (isInnerMat_of_detRoot hK hy' hμ)
  push Not at hc
  have hv : ∀ μ, μ ^ 3 ≠ detRoot hK hy := fun μ hμ => hny (isInnerMat_of_detRoot hK hy hμ)
  have e1 : detRoot hK (mul_mem hy' (inv_mem hy)) = detRoot hK hy' * (detRoot hK hy)⁻¹ :=
    Subtype.ext (by simp [detRoot])
  have e2 : detRoot hK (mul_mem hy' hy) = detRoot hK hy' * detRoot hK hy :=
    Subtype.ext (by simp [detRoot])
  rcases exists_cube_mul_or hc hv with ⟨w, hw⟩ | ⟨w, hw⟩
  · exact Or.inr (Or.inl (isInnerMat_of_detRoot hK (mul_mem hy' (inv_mem hy)) (hw.trans e1.symm)))
  · exact Or.inr (Or.inr (isInnerMat_of_detRoot hK (mul_mem hy' hy) (hw.trans e2.symm)))

end Det

section Lifts

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem IsLiftAt.inv {g : X} {y : GL (Fin 3) K} (hg : IsLiftAt ν g y) :
    IsLiftAt ν g⁻¹ y⁻¹ := by
  refine ⟨inv_mem hg.mem, fun s t ht => ?_⟩
  have h := hg.act t s (by rw [ht]; group)
  rw [← h]
  group

theorem IsLiftAt.inv_mul_mem_centralizer (M : LModel L π p f K ν) {g : X} {y : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) {s : ↥(slPi π 3 (p ^ f) K)} {z : GL (Fin 3) K}
    (hz : z ∈ StatedScalars (Fin 3) K) (hy : y = s * z) :
    ((ν s : ↥L) : X)⁻¹ * g ∈ centralizer (L : Set X) := by
  have h := (isLiftAt_of_mem M s).inv.mul M hg
  rw [hy, inv_mul_cancel_left] at h
  exact mem_centralizer_of_isLiftAt M h hz

theorem IsLiftAt.exists_of_isInnerMat (M : LModel L π p f K ν) {g : X} {y : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) (hin : IsInnerMat π (p ^ f) K y) :
    ∃ l ∈ L, l⁻¹ * g ∈ centralizer (L : Set X) := by
  obtain ⟨l, hl, z, hz, rfl⟩ := hin
  exact ⟨_, (ν ⟨l, hl⟩).2, hg.inv_mul_mem_centralizer M (s := ⟨l, hl⟩) hz rfl⟩

theorem IsLiftAt.pow_three_mul (M : LModel L π p f K ν) {x : X} {y : GL (Fin 3) K}
    (hx : IsLiftAt ν x y) (hx3 : x ^ 3 = 1) (s : ↥(slPi π 3 (p ^ f) K)) :
    ∃ t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = ((s : GL (Fin 3) K) * y) ^ 3 * (y ^ 3)⁻¹ ∧
      (((ν s : ↥L) : X) * x) ^ 3 = ((ν t : ↥L) : X) := by
  set s₁ := M.conjBy hx.mem s
  set s₂ := M.conjBy hx.mem s₁
  refine ⟨s * s₁ * s₂, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, s₂, s₁, M.coe_conjBy]
    rw [pow_three, pow_three]
    group
  · have h1 : x * ((ν s : ↥L) : X) * x⁻¹ = ((ν s₁ : ↥L) : X) :=
      hx.act s s₁ (M.coe_conjBy hx.mem s)
    have h2 : x * ((ν s₁ : ↥L) : X) * x⁻¹ = ((ν s₂ : ↥L) : X) :=
      hx.act s₁ s₂ (M.coe_conjBy hx.mem s₁)
    have e : (((ν s : ↥L) : X) * x) ^ 3 = ((ν s : ↥L) : X) * (x * ((ν s : ↥L) : X) * x⁻¹) *
        (x * (x * ((ν s : ↥L) : X) * x⁻¹) * x⁻¹) * x ^ 3 := by
      rw [pow_three, pow_three]
      group
    rw [e, h1, h2, hx3, mul_one, map_mul, map_mul]
    rfl

theorem IsLiftAt.inv_mul_mem_centralizer_of_isLiftAt (M : LModel L π p f K ν) {a b : X}
    {t : GL (Fin 3) K} (ha : IsLiftAt ν a t) (hb : IsLiftAt ν b t) :
    a⁻¹ * b ∈ centralizer (L : Set X) := by
  have h := ha.inv.mul M hb
  rw [inv_mul_cancel] at h
  exact mem_centralizer_of_isLiftAt M h (one_mem _)

end Lifts

section Rank

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

@[expose] def liftGroup (M : LModel L π p f K ν) (A : Subgroup X) : Subgroup (GL (Fin 3) K) where
  carrier := {t | ∃ a ∈ A, IsLiftAt ν a t}
  one_mem' := ⟨1, one_mem _, isLiftAt_one_of_mem_centralizer (one_mem _)⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, hat⟩ ⟨b, hb, hbt⟩
    exact ⟨a * b, mul_mem ha hb, hat.mul M hbt⟩
  inv_mem' := by
    rintro _ ⟨a, ha, hat⟩
    exact ⟨a⁻¹, inv_mem ha, hat.inv⟩

theorem LModel.card_le_nine_of_isLiftAt [Finite X] (M : LModel L π p f K ν) {A : Subgroup X}
    (hA : IsElemAbelian 3 A) (hAC : ∀ a ∈ A, a ∈ centralizer (L : Set X) → a = 1)
    (hlift : ∀ a ∈ A, ∃ y, IsLiftAt ν a y) : Nat.card A ≤ 9 := by
  have := M.piField.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  set T := liftGroup M A
  have hscal : ∀ {t : GL (Fin 3) K}, IsLiftAt ν 1 t → t ∈ StatedScalars (Fin 3) K := by
    intro t ht
    have h := (isLiftAt_one_of_mem_centralizer (ν := ν) (one_mem (centralizer (L : Set X)))
      ).inv_mul_mem_zPi M ht
    rw [inv_one, one_mul] at h
    exact mem_statedScalars_of_mem_zPi M.piField M.modThree hτ hτ1 h
  have hTH : T ≤ glPi π 3 (p ^ f) K := by
    rintro t ⟨a, -, hat⟩
    exact hat.mem
  have h3 : ∀ t ∈ T, t ^ 3 ∈ StatedScalars (Fin 3) K := by
    rintro t ⟨a, ha, hat⟩
    have h := hat.pow M 3
    rw [hA.2 a ha] at h
    exact hscal h
  have hc : ∀ t ∈ T, ∀ u ∈ T, t * u * t⁻¹ * u⁻¹ ∈ StatedScalars (Fin 3) K := by
    rintro t ⟨a, ha, hat⟩ u ⟨b, hb, hbu⟩
    have h := ((hat.mul M hbu).mul M hat.inv).mul M hbu.inv
    rw [show a * b * a⁻¹ * b⁻¹ = 1 by rw [hA.comm ha hb]; group] at h
    exact hscal h
  have hR := card_le_nine_mul_of_commute_mod M.piField M.modThree hTH h3 hc
  choose ℓ hℓ using fun a : ↥A => hlift a a.2
  have hmem : ∀ (a : ↥A) (z : ↥(T ⊓ StatedScalars (Fin 3) K)), ℓ a * z ∈ T := fun a z =>
    ⟨a, a.2, (hℓ a).mul_scalar (hTH (Subgroup.mem_inf.1 z.2).1) (Subgroup.mem_inf.1 z.2).2⟩
  have hinj : Function.Injective
      (fun az : ↥A × ↥(T ⊓ StatedScalars (Fin 3) K) => (⟨ℓ az.1 * az.2, hmem az.1 az.2⟩ : ↥T)) := by
    rintro ⟨a, z⟩ ⟨b, w⟩ h
    have h' : ℓ a * z = ℓ b * w := congrArg Subtype.val h
    have ha := (hℓ a).mul_scalar (hTH (Subgroup.mem_inf.1 z.2).1) (Subgroup.mem_inf.1 z.2).2
    have hb := (hℓ b).mul_scalar (hTH (Subgroup.mem_inf.1 w.2).1) (Subgroup.mem_inf.1 w.2).2
    rw [h'] at ha
    have hab : (a : X) = b := by
      have hc' := ha.inv_mul_mem_centralizer_of_isLiftAt M hb
      have := hAC _ (mul_mem (inv_mem a.2) b.2) hc'
      exact (inv_mul_eq_one.1 this)
    have hab' : a = b := Subtype.ext hab
    subst hab'
    refine Prod.ext rfl (Subtype.ext ?_)
    exact mul_left_cancel h'
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at h1
  have hpos : 0 < Nat.card ↥(T ⊓ StatedScalars (Fin 3) K) := Nat.card_pos
  have := Nat.le_of_mul_le_mul_right (h1.trans hR) hpos
  exact this

end Rank

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
