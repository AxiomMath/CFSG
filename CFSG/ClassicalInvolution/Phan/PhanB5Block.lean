module

public import CFSG.ClassicalInvolution.Phan.PhanB4Inf

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] {Y : Type} [Group Y]
  (S : PhanFamilyB3 C G) (E : PhanFamilyB3 C Y)

@[expose] noncomputable def Lsup (J : Set (Fin 3)) : Subgroup G := ⨆ j ∈ J, (S.ι j).range

@[expose] noncomputable def parab (J : Set (Fin 3)) : Subgroup G := torusSub S ⊔ Lsup S J

variable {S E}

theorem ι_mem_Lsup {J : Set (Fin 3)} {j : Fin 3} (hj : j ∈ J) (A : Su K p f 2) :
    S.ι j A ∈ Lsup S J :=
  (le_iSup₂ (f := fun j _ => (S.ι j).range) j hj) ⟨A, rfl⟩

theorem torusSub_le_parab (J : Set (Fin 3)) : torusSub S ≤ parab S J := le_sup_left

theorem Lsup_le_parab (J : Set (Fin 3)) : Lsup S J ≤ parab S J := le_sup_right

theorem Lsup_empty : Lsup S (∅ : Set (Fin 3)) = ⊥ := by simp [Lsup]

theorem Lsup_singleton (i : Fin 3) : Lsup S {i} = (S.ι i).range := by simp [Lsup]

theorem Lsup_pair (a b : Fin 3) : Lsup S {a, b} = (S.ι a).range ⊔ (S.ι b).range := by
  exact iSup_pair (f := fun j => (S.ι j).range)

theorem Lsup_mono {J J' : Set (Fin 3)} (h : J ⊆ J') : Lsup S J ≤ Lsup S J' :=
  iSup₂_le fun j hj => le_iSup₂ (f := fun j _ => (S.ι j).range) j (h hj)

theorem parab_mono {J J' : Set (Fin 3)} (h : J ⊆ J') : parab S J ≤ parab S J' :=
  sup_le_sup_left (Lsup_mono h) _

theorem torusSub_le_normalizer_range (j : Fin 3) :
    torusSub S ≤ Subgroup.normalizer ((S.ι j).range : Set G) := by
  have key : ∀ t : Fin 3 → normOne (unitaryInvolution K p f), ∀ x ∈ (S.ι j).range,
      mTor S t * x * (mTor S t)⁻¹ ∈ (S.ι j).range := by
    rintro t _ ⟨A, rfl⟩
    rw [mTor_conj_ι (hK := hK)]
    exact ⟨_, rfl⟩
  rintro _ ⟨t, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t x, fun hx => ?_⟩
  have := key t⁻¹ _ hx
  rw [map_inv] at this
  simpa [mul_assoc] using this

theorem torusSub_le_normalizer_Lsup (J : Set (Fin 3)) :
    torusSub S ≤ Subgroup.normalizer (Lsup S J : Set G) :=
  le_normalizer_iSup₂ _ J _ (torusSub_le_normalizer_range)

@[expose] def IsBlockHom (J : Set (Fin 3)) (φN : Lsup S J →* Y) : Prop :=
  ∀ (j : Fin 3) (hj : j ∈ J) (A : Su K p f 2), φN ⟨S.ι j A, ι_mem_Lsup hj A⟩ = E.ι j A

section Exists

@[expose] noncomputable def rangeHom (hg : GoodFamily S) (E : PhanFamilyB3 C Y) (i : Fin 3) :
    (S.ι i).range →* Y :=
  (E.ι i).comp (MonoidHom.ofInjective (hg.inj i)).symm.toMonoidHom

theorem rangeHom_apply (hg : GoodFamily S) (i : Fin 3) (x : (S.ι i).range) (A : Su K p f 2)
    (h : (x : G) = S.ι i A) : rangeHom hg E i x = E.ι i A := by
  obtain ⟨x, hx⟩ := x
  subst h
  simp only [rangeHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ofInjective_symm_apply_self]

variable (hg : GoodFamily S)

theorem exists_blockHom_empty : ∃ φN : Lsup S (∅ : Set (Fin 3)) →* Y, IsBlockHom (E := E) ∅ φN :=
  ⟨1, fun _ hj => absurd hj (by simp)⟩

include hg in
theorem exists_blockHom_singleton (i : Fin 3) :
    ∃ φN : Lsup S {i} →* Y, IsBlockHom (E := E) {i} φN := by
  refine ⟨(rangeHom hg E i).comp
    (MulEquiv.subgroupCongr (Lsup_singleton (S := S) i)).toMonoidHom, ?_⟩
  intro j hj A
  obtain rfl : j = i := hj
  exact rangeHom_apply hg j _ A rfl

include hg in
theorem exists_blockHom_zero_one :
    ∃ φN : Lsup S {0, 1} →* Y, IsBlockHom (E := E) {0, 1} φN := by
  have hle : Lsup S {0, 1} ≤ S.θ.range := by
    refine iSup₂_le fun j hj => ?_
    rcases hj with hj | hj
    · subst hj
      rintro _ ⟨A, rfl⟩
      exact ⟨embSUid (unitaryInvolution K p f) 2 A, (ι_zero S A).symm⟩
    · obtain rfl : j = 1 := hj
      rintro _ ⟨A, rfl⟩
      exact ⟨embSUid (unitaryInvolution K p f) 0 A, (ι_one_θ S A).symm⟩
  let ψ : Lsup S {0, 1} →* Y :=
    ((E.θ).comp (MonoidHom.ofInjective hg.θ_injective).symm.toMonoidHom).comp
      (Subgroup.inclusion hle)
  have hψ : ∀ (x : Lsup S {0, 1}) (B : Su K p f 3), (x : G) = S.θ B → ψ x = E.θ B := by
    intro x B hxB
    obtain ⟨x, hx⟩ := x
    subst hxB
    exact congrArg E.θ (ofInjective_symm_apply_self hg.θ_injective B _)
  refine ⟨ψ, fun j hj A => ?_⟩
  rcases hj with hj | hj
  · subst hj
    exact (hψ _ (embSUid (unitaryInvolution K p f) 2 A) (ι_zero S A)).trans (ι_zero E A).symm
  · obtain rfl : j = 1 := hj
    exact (hψ _ (embSUid (unitaryInvolution K p f) 0 A) (ι_one_θ S A)).trans (ι_one_θ E A).symm

include hg in
theorem exists_blockHom_one_two :
    ∃ φN : Lsup S {1, 2} →* Y, IsBlockHom (E := E) {1, 2} φN := by
  have hle : Lsup S {1, 2} ≤ S.ϑ.range := by
    refine iSup₂_le fun j hj => ?_
    rcases hj with hj | hj
    · subst hj
      rintro _ ⟨A, rfl⟩
      exact ⟨C.ℓ A, (ι_one_ϑ S A).symm⟩
    · obtain rfl : j = 2 := hj
      rintro _ ⟨A, rfl⟩
      exact ⟨C.s A, (ι_two S A).symm⟩
  let ψ : Lsup S {1, 2} →* Y :=
    ((E.ϑ).comp (MonoidHom.ofInjective hg.ϑ_injective).symm.toMonoidHom).comp
      (Subgroup.inclusion hle)
  have hψ : ∀ (x : Lsup S {1, 2}) (B : StatedSp 2 F), (x : G) = S.ϑ B → ψ x = E.ϑ B := by
    intro x B hxB
    obtain ⟨x, hx⟩ := x
    subst hxB
    exact congrArg E.ϑ (ofInjective_symm_apply_self hg.ϑ_injective B _)
  refine ⟨ψ, fun j hj A => ?_⟩
  rcases hj with hj | hj
  · subst hj
    exact (hψ _ (C.ℓ A) (ι_one_ϑ S A)).trans (ι_one_ϑ E A).symm
  · obtain rfl : j = 2 := hj
    exact (hψ _ (C.s A) (ι_two S A)).trans (ι_two E A).symm

theorem range_commute_zero_two : ∀ x ∈ (S.ι 0).range, ∀ y ∈ (S.ι 2).range, x * y = y * x := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact S.comm A B

theorem range_le_normalizer_zero_two :
    (S.ι 2).range ≤ Subgroup.normalizer ((S.ι 0).range : Set G) :=
  le_trans (fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
    range_commute_zero_two x hx y hy) (Subgroup.centralizer_le_normalizer _)

include hg in
theorem exists_blockHom_zero_two :
    ∃ φN : Lsup S {0, 2} →* Y, IsBlockHom (E := E) {0, 2} φN := by
  have hcomm := range_commute_zero_two (S := S)
  have hNT := range_le_normalizer_zero_two (S := S)
  obtain ⟨φ, hφ1, hφ2⟩ := exists_hom_sup_of_normalizes hNT (rangeHom hg E 0) (rangeHom hg E 2)
    (fun g hN hT => by
      have hg1 : g ∈ (S.ι 0).range ⊓ (S.ι 2).range := ⟨hN, hT⟩
      rw [hg.disj 0 2 (by decide), Subgroup.mem_bot] at hg1
      subst hg1
      have e1 : (⟨1, hN⟩ : (S.ι 0).range) = 1 := rfl
      have e2 : (⟨1, hT⟩ : (S.ι 2).range) = 1 := rfl
      rw [e1, e2, map_one, map_one])
    (fun t n => by
      obtain ⟨_, B, rfl⟩ := t
      obtain ⟨_, A, rfl⟩ := n
      have hc : conjAutOfNormalizer hNT ⟨S.ι 2 B, B, rfl⟩ ⟨S.ι 0 A, A, rfl⟩ =
          ⟨S.ι 0 A, A, rfl⟩ := by
        refine Subtype.ext ?_
        rw [coe_conjAutOfNormalizer]
        exact mul_inv_eq_iff_eq_mul.2 (hcomm _ ⟨A, rfl⟩ _ ⟨B, rfl⟩).symm
      rw [hc, rangeHom_apply hg 2 _ B rfl, rangeHom_apply hg 0 _ A rfl]
      exact mul_inv_eq_iff_eq_mul.2 (E.comm A B).symm)
  refine ⟨φ.comp (MulEquiv.subgroupCongr (Lsup_pair (S := S) 0 2).symm).symm.toMonoidHom, ?_⟩
  intro j hj A
  rcases hj with hj | hj
  · subst hj
    exact (hφ1 ⟨S.ι 0 A, A, rfl⟩).trans (rangeHom_apply hg 0 _ A rfl)
  · obtain rfl : j = 2 := hj
    exact (hφ2 ⟨S.ι 2 A, A, rfl⟩).trans (rangeHom_apply hg 2 _ A rfl)

theorem exists_blockHom_swap {a b : Fin 3}
    (h : ∃ φN : Lsup S {a, b} →* Y, IsBlockHom (E := E) {a, b} φN) :
    ∃ φN : Lsup S {b, a} →* Y, IsBlockHom (E := E) {b, a} φN := by
  obtain ⟨φN, hφN⟩ := h
  have hpair : Lsup S {b, a} = Lsup S {a, b} := by rw [Set.pair_comm]
  refine ⟨φN.comp (MulEquiv.subgroupCongr hpair).toMonoidHom, ?_⟩
  intro j hj A
  exact hφN j (by rwa [Set.pair_comm]) A

include hg in
theorem exists_blockHom {J : Set (Fin 3)} (hJ : J.encard ≤ 2) :
    ∃ φN : Lsup S J →* Y, IsBlockHom (E := E) J φN := by
  rcases hJ.lt_or_eq with h | h
  · have h1 : J.encard ≤ 1 := by
      have : (2 : ℕ∞) = 1 + 1 := by norm_num
      rw [this] at h
      exact (ENat.lt_add_one_iff (by simp)).1 h
    rcases Set.encard_le_one_iff_eq.1 h1 with rfl | ⟨a, rfl⟩
    · exact exists_blockHom_empty
    · exact exists_blockHom_singleton hg a
  · obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.1 h
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | skip
    · exact exists_blockHom_zero_one hg
    · exact exists_blockHom_zero_two hg
    · exact exists_blockHom_swap (a := 0) (b := 1) (exists_blockHom_zero_one hg)
    · exact exists_blockHom_one_two hg
    · exact exists_blockHom_swap (a := 0) (b := 2) (exists_blockHom_zero_two hg)
    · exact exists_blockHom_swap (a := 1) (b := 2) (exists_blockHom_one_two hg)

end Exists

end CFSG.ClassicalInvolution.PhanB3
