module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp

public section

namespace CFSG.SectionRank.QTK.Insp443

theorem perm3_perfect_eq_bot {P : Subgroup (Equiv.Perm (Fin 3))} (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  have hA : P ≤ alternatingGroup (Fin 3) := by
    rw [← hP]
    calc ⁅P, P⁆ ≤ commutator (Equiv.Perm (Fin 3)) := Subgroup.commutator_mono le_top le_top
      _ ≤ Equiv.Perm.sign.ker := Abelianization.commutator_subset_ker _
      _ = alternatingGroup (Fin 3) := rfl
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := alternatingGroup (Fin 3))
  rw [← hP, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hA hx⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hA hy⟩)
  have h1 : (⟨y, hA hy⟩ : alternatingGroup (Fin 3)) * ⟨x, hA hx⟩ =
      ⟨x, hA hx⟩ * ⟨y, hA hy⟩ := by
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  exact congrArg Subtype.val h1

section Perm3

variable {G : Type} [Group G] {W : Subgroup G} {A : Fin 3 → Subgroup G}
  (hinj : Function.Injective A)
  (hperm : ∀ g ∈ Subgroup.normalizer (W : Set G), ∀ i, ∃ j,
    (A i).map (MulAut.conj g).toMonoidHom = A j)

@[expose] noncomputable def sig3 (g : ↥(Subgroup.normalizer (W : Set G))) (i : Fin 3) : Fin 3 :=
  Classical.choose (hperm g g.2 i)

theorem sig3_spec (g : ↥(Subgroup.normalizer (W : Set G))) (i : Fin 3) :
    (A i).map (MulAut.conj (g : G)).toMonoidHom = A (sig3 hperm g i) :=
  Classical.choose_spec (hperm g g.2 i)

include hinj in
theorem sig3_eq {g : ↥(Subgroup.normalizer (W : Set G))} {i j : Fin 3}
    (h : (A i).map (MulAut.conj (g : G)).toMonoidHom = A j) : sig3 hperm g i = j :=
  hinj (by rw [← sig3_spec hperm g i, h])

theorem map_conj_mul3 (a b : G) (K : Subgroup G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

include hinj in
theorem sig3_mul (g h : ↥(Subgroup.normalizer (W : Set G))) (i : Fin 3) :
    sig3 hperm (g * h) i = sig3 hperm g (sig3 hperm h i) := by
  apply sig3_eq hinj
  rw [Subgroup.coe_mul, map_conj_mul3, sig3_spec hperm h i, sig3_spec hperm g]

include hinj in
theorem sig3_one (i : Fin 3) : sig3 hperm 1 i = i := by
  apply sig3_eq hinj
  rw [Subgroup.coe_one]
  convert Subgroup.map_id (A i)
  ext x
  simp

@[expose] noncomputable def psi3 : ↥(Subgroup.normalizer (W : Set G)) →* Equiv.Perm (Fin 3) where
  toFun g :=
    { toFun := sig3 hperm g
      invFun := sig3 hperm g⁻¹
      left_inv := fun i => by rw [← sig3_mul hinj, inv_mul_cancel, sig3_one hinj]
      right_inv := fun i => by rw [← sig3_mul hinj, mul_inv_cancel, sig3_one hinj] }
  map_one' := Equiv.ext fun i => sig3_one hinj hperm i
  map_mul' g h := Equiv.ext fun i => sig3_mul hinj hperm g h i

include hinj hperm in
theorem le_normalizer_of_perm3 {L : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hL : ⁅L, L⁆ = L) (i : Fin 3) : L ≤ Subgroup.normalizer (A i : Set G) := by
  let φ : ↥L →* Equiv.Perm (Fin 3) := (psi3 hinj hperm).comp (Subgroup.inclusion hLW)
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range φ)
  have hbot := perm3_perfect_eq_bot hperf
  intro l hl
  have h1 : φ ⟨l, hl⟩ = 1 := by
    have : φ ⟨l, hl⟩ ∈ φ.range := ⟨_, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h2 : sig3 hperm (Subgroup.inclusion hLW ⟨l, hl⟩) i = i := by
    have := congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) h1
    simpa [φ, psi3] using this
  have h3 := sig3_spec hperm (Subgroup.inclusion hLW ⟨l, hl⟩) i
  rw [h2] at h3
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3

end Perm3

end CFSG.SectionRank.QTK.Insp443

end
