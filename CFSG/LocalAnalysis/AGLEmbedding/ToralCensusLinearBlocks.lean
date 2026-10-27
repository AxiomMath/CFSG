module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)

@[expose] def cutBlock {n : ℕ} {K : Type*} (g : Matrix (Fin n) (Fin n) K) (a b : ℕ)
    (hb : b ≤ n) : Matrix (Fin (b - a)) (Fin (b - a)) K :=
  fun i j => g ⟨a + i, by omega⟩ ⟨a + j, by omega⟩

@[expose] def IsConsecutiveCut (n : ℕ) (I : Set ℕ) (a b : ℕ) : Prop :=
  a < b ∧ b ≤ n ∧ (a = 0 ∨ a ∈ I) ∧ (b = n ∨ b ∈ I) ∧ ∀ c ∈ I, ¬ (a < c ∧ c < b)

namespace ToralCensus

variable {K : Type*} [Field K] {n : ℕ}

omit [Field K] in
theorem cutBlock_apply (g : Matrix (Fin n) (Fin n) K) {a b : ℕ} (hb : b ≤ n)
    (i j : Fin (b - a)) :
    cutBlock g a b hb i j = g ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ :=
  rfl

theorem single_mem_flagSpace_of_lt {d : ℕ} {l : Fin n} (hl : (l : ℕ) < d) :
    (Pi.single l 1 : Fin n → K) ∈ flagSpace n K d :=
  mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _

theorem apply_eq_zero_of_mem_stabilizer_flagSpace {d : ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ stabilizer (flagSpace n K d)) {k l : Fin n} (hl : (l : ℕ) < d)
    (hk : d ≤ (k : ℕ)) : (x : Matrix (Fin n) (Fin n) K) k l = 0 := by
  have hc : (x : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single l 1 ∈ flagSpace n K d :=
    (mem_stabilizer.mp hx) ▸ ⟨_, single_mem_flagSpace_of_lt hl, rfl⟩
  simpa [Matrix.mulVec_single_one] using mem_flagSpace.mp hc k hk

theorem apply_eq_zero_of_mem_flagStabilizer {I : Set ℕ} {d : ℕ} (hd : d = 0 ∨ d ∈ I)
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ flagStabilizer n K I) {k l : Fin n}
    (hl : (l : ℕ) < d) (hk : d ≤ (k : ℕ)) : (x : Matrix (Fin n) (Fin n) K) k l = 0 := by
  rcases hd with rfl | hd
  · omega
  · exact apply_eq_zero_of_mem_stabilizer_flagSpace (mem_flagStabilizer.mp hx d hd) hl hk

theorem cutBlock_mul {I : Set ℕ} {a b : ℕ} (h : IsConsecutiveCut n I a b)
    {x y : SpecialLinearGroup (Fin n) K} (hx : x ∈ flagStabilizer n K I)
    (hy : y ∈ flagStabilizer n K I) :
    cutBlock ((x * y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b h.2.1 =
      cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 *
        cutBlock (y : Matrix (Fin n) (Fin n) K) a b h.2.1 := by
  obtain ⟨hab, hbn, ha, hb, -⟩ := h
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  rw [cutBlock_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [cutBlock_apply]
  symm
  refine Fintype.sum_of_injective (fun k : Fin (b - a) => (⟨a + k, by omega⟩ : Fin n))
    (fun k₁ k₂ hk => Fin.ext (by simpa using congrArg Fin.val hk))
    (fun k : Fin (b - a) => (x : Matrix (Fin n) (Fin n) K) ⟨a + i, by omega⟩ ⟨a + k, by omega⟩ *
      (y : Matrix (Fin n) (Fin n) K) ⟨a + k, by omega⟩ ⟨a + j, by omega⟩)
    (fun k : Fin n => (x : Matrix (Fin n) (Fin n) K) ⟨a + i, by omega⟩ k *
      (y : Matrix (Fin n) (Fin n) K) k ⟨a + j, by omega⟩) (fun k hk => ?_)
    fun _ => rfl
  by_cases hka : (k : ℕ) < a
  · rw [apply_eq_zero_of_mem_flagStabilizer ha hx hka (by simp), zero_mul]
  by_cases hkb : b ≤ (k : ℕ)
  · rcases hb with rfl | hb
    · exact absurd k.isLt (by omega)
    · rw [apply_eq_zero_of_mem_flagStabilizer (Or.inr hb) hy (by simp; omega) hkb, mul_zero]
  · exact absurd ⟨⟨(k : ℕ) - a, by omega⟩, Fin.ext (by simp; omega)⟩ hk

@[expose] def cutBlockHom {I : Set ℕ} {a b : ℕ} (h : IsConsecutiveCut n I a b) :
    flagStabilizer n K I →* Matrix (Fin (b - a)) (Fin (b - a)) K where
  toFun x := cutBlock ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b h.2.1
  map_one' := by
    ext i j
    simp [cutBlock, Matrix.one_apply, Fin.ext_iff]
  map_mul' x y := cutBlock_mul h x.2 y.2

theorem cutBlockHom_apply {I : Set ℕ} {a b : ℕ} (h : IsConsecutiveCut n I a b)
    (x : flagStabilizer n K I) :
    cutBlockHom h x =
      cutBlock ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b h.2.1 :=
  rfl

theorem det_cutBlock_eq_one_of_mem_commutator {I : Set ℕ} {a b : ℕ}
    (h : IsConsecutiveCut n I a b) {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ ⁅flagStabilizer n K I, flagStabilizer n K I⁆) :
    (cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1).det = 1 := by
  obtain ⟨x', hx', rfl⟩ :=
    LinearThreeKit.commutator_le_map_ker (detMonoidHom.comp (cutBlockHom h)) hx
  exact hx'

theorem eq_one_of_det_eq_one_of_eq_one {m : ℕ} (hm : m = 1) {M : Matrix (Fin m) (Fin m) K}
    (h : M.det = 1) : M = 1 := by
  subst hm
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.one_apply_eq]
  rwa [Matrix.det_unique] at h

theorem map_eq_one_of_perfect_of_card_two {G : Type*} [Group G] {m : ℕ} (hm : m = 2)
    (hK : Nat.card K = 2) (f : G →* Matrix (Fin m) (Fin m) K) {V : Subgroup G}
    (hV : ⁅V, V⁆ = V) {x : G} (hx : x ∈ V) : f x = 1 := by
  subst hm
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Group.IsSolvable (GL (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
      (Or.inl hK)
  set ψ : G →* GL (Fin 2) K := f.toHomUnits with hψ
  have hW : V.map ψ = ⊥ := by
    by_contra hne
    have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [← Subgroup.map_commutator, hV] at hlt
    exact lt_irrefl _ hlt
  have h1 : ψ x = 1 := (Subgroup.mem_bot).mp (hW ▸ Subgroup.mem_map_of_mem ψ hx)
  have h2 := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) h1
  simpa [hψ] using h2

theorem perfect_subgroupOf_of_le {G : Type*} [Group G] {H P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPH : P ≤ H) : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hPH, hP]

end ToralCensus

theorem gradedPerfectSL_holds :
    ∀ (K : Type) [Field K] (n : ℕ) (I : Set ℕ),
      ∀ x ∈ perfectJoin (LinearFlag.flagStabilizer n K I), ∀ a b : ℕ,
        ∀ h : IsConsecutiveCut n I a b,
          (cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1).det = 1 ∧
            ((b - a = 1 ∨ (b - a = 2 ∧ Nat.card K = 2)) →
              cutBlock (x : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1) := by
  intro K _ n I x hx a b h
  have hxJ : x ∈ flagStabilizer n K I := perfectJoin_le _ hx
  have hxc : x ∈ ⁅flagStabilizer n K I, flagStabilizer n K I⁆ := by
    rw [← perfectJoin_perfect] at hx
    exact Subgroup.commutator_mono (perfectJoin_le _) (perfectJoin_le _) hx
  have hdet := ToralCensus.det_cutBlock_eq_one_of_mem_commutator h hxc
  refine ⟨hdet, fun hsize => ?_⟩
  rcases hsize with h1 | ⟨h2, hK⟩
  · exact ToralCensus.eq_one_of_det_eq_one_of_eq_one h1 hdet
  · exact ToralCensus.map_eq_one_of_perfect_of_card_two h2 hK (ToralCensus.cutBlockHom h)
      (ToralCensus.perfect_subgroupOf_of_le (perfectJoin_perfect _) (perfectJoin_le _))
      (x := ⟨x, hxJ⟩) (by rwa [Subgroup.mem_subgroupOf])

end CFSG.AGLEmbedding
