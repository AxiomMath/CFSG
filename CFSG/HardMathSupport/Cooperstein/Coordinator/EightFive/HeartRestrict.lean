module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.HeartFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {m n : ℕ}

theorem eq_top_of_pairEW_mem (Y : AddSubgroup (altHeart n))
    (h : ∀ a b : Fin n, a ≠ b → (pairEW a b : altHeart n) ∈ Y) : Y = ⊤ := by
  have key := mk_mem_of_pairs (Y.comap (heartEquivAlt n).toAddMonoidHom) fun x y hxy => by
    change heartEquivAlt n (QuotientAddGroup.mk (pairE x y)) ∈ Y
    rw [heartEquivAlt_mk]
    have he : (⟨(pairE x y).1, by rw [← evenSub_eq]; exact (pairE x y).2⟩ : evenWeight n) =
        pairEW x y :=
      Subtype.ext (funext fun p => by
        rw [pairEW_apply]
        simp [pairE, pairVec, Pi.single_apply])
    rw [he]
    exact h x y hxy
  rw [eq_top_iff]
  intro z _
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk_surjective ((heartEquivAlt n).symm z)
  have hz := key f
  change heartEquivAlt n (QuotientAddGroup.mk f) ∈ Y at hz
  rwa [hf, AddEquiv.apply_symm_apply] at hz

theorem altHeart_hom_ext {X : Type*} [AddCommGroup X] {f g : altHeart n →+ X}
    (h : ∀ a b : Fin n, a ≠ b → f (pairEW a b : altHeart n) = g (pairEW a b : altHeart n)) :
    f = g := by
  have htop := eq_top_of_pairEW_mem (AddMonoidHom.eqLocus f g) h
  exact AddMonoidHom.ext fun z => (show z ∈ AddMonoidHom.eqLocus f g from htop ▸ trivial)

theorem sum_comp_embedding (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (y : Fin n → ZMod 2) :
    ∑ i, y (ι i) = ∑ p, y p - y ω := by
  classical
  have hmap : Finset.univ.map ι = Finset.univ.erase ω := by
    ext p
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact hι p
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ω), add_sub_cancel_right, ← hmap,
    Finset.sum_map]

@[expose] noncomputable def restrictCoord (ι : Fin m ↪ Fin n) (ω : Fin n) :
    altHeart n →+ (Fin m → ZMod 2) :=
  { toFun := fun v i => altHeartCoord ω v (ι i)
    map_zero' := by ext i; simp
    map_add' := fun v w => by ext i; simp }

theorem restrictCoord_mem (ι : Fin m ↪ Fin n) {ω : Fin n} (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω)
    (hmn : m + 1 = n) (hn : Even n) (v : altHeart n) : restrictCoord ι ω v ∈ evenWeight m := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  have h : ∑ i, restrictCoord ι ω (y : altHeart n) i = 0 := by
    have key : ∑ i, restrictCoord ι ω (y : altHeart n) i =
        ∑ i, (y : Fin n → ZMod 2) (ι i) - ∑ _i : Fin m, (y : Fin n → ZMod 2) ω :=
      Finset.sum_sub_distrib _ _
    rw [key, sum_comp_embedding ι hι, sum_evenWeight y, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hn' : ((m : ℕ) : ZMod 2) = 1 := by
      rw [ZMod.natCast_eq_one_iff_odd]
      obtain ⟨k, hk⟩ := hn
      exact ⟨k - 1, by omega⟩
    rw [hn', one_mul, zero_sub, neg_sub_left, zmod2_add_self, neg_zero]
  simpa [evenWeight] using h

@[expose] noncomputable def heartRestrictHom (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n) (hn : Even n) :
    altHeart n →+ altHeart m :=
  (QuotientAddGroup.mk' (evenWeightOnes m)).comp
    ((restrictCoord ι ω).codRestrict (evenWeight m) (restrictCoord_mem ι hι hmn hn))

theorem heartRestrictHom_apply (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n) (hn : Even n) (v : altHeart n) :
    heartRestrictHom ι hι hmn hn v =
      ((⟨restrictCoord ι ω v, restrictCoord_mem ι hι hmn hn v⟩ : evenWeight m) : altHeart m) :=
  rfl

theorem heartRestrictHom_altAct (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n) (hn : Even n)
    (σ : alternatingGroup (Fin m)) (v : altHeart n) :
    heartRestrictHom ι hι hmn hn (altAct (altLift ι σ : Perm (Fin n)) v) =
      altAct (σ : Perm (Fin m)) (heartRestrictHom ι hι hmn hn v) := by
  have hω : (altLift ι σ : Perm (Fin n)) ω = ω :=
    altLift_apply_of_notMem ι σ (fun h => (hι ω).1 h rfl)
  rw [heartRestrictHom_apply, heartRestrictHom_apply, altAct_mk]
  congr 1
  refine Subtype.ext (funext fun i => ?_)
  change altHeartCoord ω (altAct _ v) (ι i) = altHeartCoord ω v (ι ((σ : Perm (Fin m))⁻¹ i))
  rw [altHeartCoord_altAct hω]
  have h : ((altLift ι σ : Perm (Fin n)))⁻¹ (ι i) = ι ((σ : Perm (Fin m))⁻¹ i) := by
    rw [Perm.inv_eq_iff_eq, altLift_apply_apply, perm_apply_inv_apply]
  rw [h]

theorem heartRestrictHom_injective (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n) (hn : Even n) :
    Function.Injective (heartRestrictHom ι hι hmn hn) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  rw [heartRestrictHom_apply, QuotientAddGroup.eq_zero_iff] at hv
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hv
  have hc' : ∀ i, restrictCoord ι ω v i = c := hc
  have hsum := sum_evenWeight
    (⟨restrictCoord ι ω v, restrictCoord_mem ι hι hmn hn v⟩ : evenWeight m)
  change ∑ i, restrictCoord ι ω v i = 0 at hsum
  simp only [hc', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm : ((m : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_one_iff_odd]
    obtain ⟨k, hk⟩ := hn
    exact ⟨k - 1, by omega⟩
  rw [hm, one_mul] at hsum
  apply altHeartCoord_injective ω
  rw [map_zero]
  funext p
  by_cases hp : p = ω
  · rw [hp, altHeartCoord_self, Pi.zero_apply]
  · obtain ⟨i, rfl⟩ := (hι p).2 hp
    have := hc i
    rw [hsum] at this
    exact this

theorem heartRestrictHom_surjective (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n) (hn : Even n) :
    Function.Surjective (heartRestrictHom ι hι hmn hn) := by
  classical
  intro w
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
  have hωι : ω ∉ Set.range ι := fun h => (hι ω).1 h rfl
  set y : Fin n → ZMod 2 := Function.extend ι (x : Fin m → ZMod 2) 0 with hy
  have hyι : ∀ i, y (ι i) = (x : Fin m → ZMod 2) i := fun i => ι.injective.extend_apply _ _ i
  have hyω : y ω = 0 := by
    rw [hy, Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => hωι ⟨i, hi⟩), Pi.zero_apply]
  have hyE : y ∈ evenWeight n := by
    have h : ∑ p, y p = 0 := by
      have h1 := sum_comp_embedding ι hι y
      rw [hyω, sub_zero] at h1
      rw [← h1]
      simp only [hyι]
      exact sum_evenWeight x
    simpa [evenWeight] using h
  refine ⟨((⟨y, hyE⟩ : evenWeight n) : altHeart n), ?_⟩
  rw [heartRestrictHom_apply]
  congr 1
  refine Subtype.ext (funext fun i => ?_)
  change y (ι i) - y ω = _
  rw [hyι, hyω, sub_zero]

@[expose] noncomputable def heartRestrict (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n) (hn : Even n) :
    altHeart n ≃+ altHeart m :=
  AddEquiv.ofBijective (heartRestrictHom ι hι hmn hn)
    ⟨heartRestrictHom_injective ι hι hmn hn, heartRestrictHom_surjective ι hι hmn hn⟩

theorem heartRestrict_altAct (ι : Fin m ↪ Fin n) {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) (hmn : m + 1 = n) (hn : Even n)
    (σ : alternatingGroup (Fin m)) (v : altHeart n) :
    heartRestrict ι hι hmn hn (altAct (altLift ι σ : Perm (Fin n)) v) =
      altAct (σ : Perm (Fin m)) (heartRestrict ι hι hmn hn v) :=
  heartRestrictHom_altAct ι hι hmn hn σ v

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
