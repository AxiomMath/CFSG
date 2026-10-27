module

public import CFSG.ClassicalInvolution.Phan.PhanB6Agree

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] {Y : Type} [Group Y]
  {S : PhanFamilyB3 C G} (E : PhanFamilyB3 C Y)

@[expose] noncomputable def phiT (hinj : Function.Injective (mTor S)) : torusSub S →* Y :=
  (mTor E).comp (MonoidHom.ofInjective hinj).symm.toMonoidHom

theorem phiT_apply (hinj : Function.Injective (mTor S)) (x : torusSub S)
    (t : Fin 3 → normOne (unitaryInvolution K p f)) (h : (x : G) = mTor S t) :
    phiT E hinj x = mTor E t := by
  obtain ⟨x, hx⟩ := x
  subst h
  exact congrArg (mTor E) (ofInjective_symm_apply_self hinj t hx)

@[expose] def IsPhi (J : Set (Fin 3)) (φ : parab S J →* Y) : Prop :=
  (∀ t : Fin 3 → normOne (unitaryInvolution K p f),
      φ ⟨mTor S t, torusSub_le_parab J (mTor_mem_torusSub S t)⟩ = mTor E t) ∧
    ∀ (j : Fin 3) (hj : j ∈ J) (A : Su K p f 2),
      φ ⟨S.ι j A, Lsup_le_parab J (ι_mem_Lsup hj A)⟩ = E.ι j A

theorem conj_relation (hinj : Function.Injective (mTor S)) {J : Set (Fin 3)}
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (E := E) J φN) (t : torusSub S) (n : Lsup S J) :
    phiT E hinj t * φN n * (phiT E hinj t)⁻¹ =
      φN (conjAutOfNormalizer (torusSub_le_normalizer_Lsup J) t n) := by
  let S₀ : Set G := ⋃ j ∈ J, ((S.ι j).range : Set G)
  have hSH : S₀ ⊆ Lsup S J := fun y hy => by
    obtain ⟨j, hj, hy'⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨A, rfl⟩ := hy'
    exact ι_mem_Lsup hj A
  have hSN : Subgroup.closure {x : Lsup S J | (x : G) ∈ S₀} = ⊤ :=
    closure_eq_top_of_le_closure hSH (iSup₂_le fun j hj y hy =>
      Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨j, hj, hy⟩))
  have hST : Subgroup.closure (Set.univ : Set (torusSub S)) = ⊤ := Subgroup.closure_univ
  refine forall_conj_of_gens (torusSub_le_normalizer_Lsup J) φN (phiT E hinj) hSN hST ?_ t n
  intro t' _ x hx
  obtain ⟨j, hj, A, hA⟩ : ∃ j ∈ J, ∃ A, S.ι j A = (x : G) := by
    obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨j, hj, hy⟩
  have hx' : x = ⟨S.ι j A, ι_mem_Lsup hj A⟩ := Subtype.ext hA.symm
  obtain ⟨_, τ, rfl⟩ := t'
  have e1 : phiT E hinj ⟨mTor S τ, mTor_mem_torusSub S τ⟩ = mTor E τ :=
    phiT_apply E hinj _ τ rfl
  have e2 : (conjAutOfNormalizer (torusSub_le_normalizer_Lsup J)
      ⟨mTor S τ, mTor_mem_torusSub S τ⟩ x : Lsup S J) =
      ⟨S.ι j (conjDiag hK ![rho j τ, 1] A), ι_mem_Lsup hj _⟩ := by
    refine Subtype.ext ?_
    rw [coe_conjAutOfNormalizer, hx']
    exact mTor_conj_ι S τ j A
  rw [e1, e2, hx', hφ j hj A, hφ j hj, mTor_conj_ι E τ j A]

theorem isPhi_unique {J : Set (Fin 3)} {φ₁ φ₂ : parab S J →* Y} (h₁ : IsPhi E J φ₁)
    (h₂ : IsPhi E J φ₂) : φ₁ = φ₂ := by
  let S₀ : Set G := (torusSub S : Set G) ∪ ⋃ j ∈ J, ((S.ι j).range : Set G)
  have hSH : S₀ ⊆ parab S J := by
    rintro x (hx | hx)
    · exact torusSub_le_parab J hx
    · obtain ⟨j, hj, A, rfl⟩ := Set.mem_iUnion₂.1 hx
      exact Lsup_le_parab J (ι_mem_Lsup hj A)
  have hle : parab S J ≤ Subgroup.closure S₀ :=
    sup_le (fun x hx => Subgroup.subset_closure (Or.inl hx))
      (iSup₂_le fun j hj y hy => Subgroup.subset_closure (Or.inr (Set.mem_iUnion₂.2 ⟨j, hj, hy⟩)))
  refine hom_ext_of_le_closure φ₁ φ₂ hSH hle ?_
  rintro x (hx | hx)
  · obtain ⟨τ, rfl⟩ := hx
    exact (h₁.1 τ).trans (h₂.1 τ).symm
  · obtain ⟨j, hj, A, rfl⟩ := Set.mem_iUnion₂.1 hx
    exact (h₁.2 j hj A).trans (h₂.2 j hj A).symm

theorem isPhi_restrict {J J' : Set (Fin 3)} (h : J' ⊆ J) {φ : parab S J →* Y}
    (hφ : IsPhi E J φ) : IsPhi E J' (φ.comp (Subgroup.inclusion (parab_mono h))) :=
  ⟨fun τ => hφ.1 τ, fun j hj A => hφ.2 j (h hj) A⟩

variable (hq : 3 ≤ p ^ f) (hg : GoodFamily S) (h2K : (2 : K) ≠ 0)

include hK hq hg h2K in
theorem exists_isPhi {J : Set (Fin 3)} (hJ : J.encard ≤ 2) :
    ∃ φ : parab S J →* Y, IsPhi E J φ := by
  obtain ⟨φN, hφN⟩ := exists_blockHom (E := E) hg hJ
  have hinj := hg.mTor_injective h2K
  obtain ⟨φ, h1, h2'⟩ := exists_hom_sup_of_normalizes' (torusSub_le_normalizer_Lsup J) φN
    (phiT E hinj)
    (fun g hN hT => by
      obtain ⟨τ, rfl⟩ := id hT
      rw [phiT_apply E hinj ⟨mTor S τ, hT⟩ τ rfl]
      exact hφN.agree hq hg h2K hJ τ hN)
    (conj_relation E hinj hφN)
  refine ⟨φ, fun τ => ?_, fun j hj A => ?_⟩
  · exact (h2' ⟨mTor S τ, mTor_mem_torusSub S τ⟩).trans (phiT_apply E hinj _ τ rfl)
  · exact (h1 ⟨S.ι j A, ι_mem_Lsup hj A⟩).trans (hφN j hj A)

include hK hq hg h2K in
theorem exists_phi_family :
    ∃ φ : ∀ J : Set (Fin 3), J.encard ≤ 2 → (parab S J →* Y),
      (∀ J (hJ : J.encard ≤ 2), IsPhi E J (φ J hJ)) ∧
      ∀ (J J' : Set (Fin 3)) (hJ : J.encard ≤ 2) (hJ' : J'.encard ≤ 2), J' ⊆ J →
        ∀ (g : G) (hgJ' : g ∈ parab S J') (hgJ : g ∈ parab S J),
          φ J' hJ' ⟨g, hgJ'⟩ = φ J hJ ⟨g, hgJ⟩ := by
  choose φ hφ using fun (J : Set (Fin 3)) (hJ : J.encard ≤ 2) =>
    exists_isPhi E hq hg h2K hJ
  refine ⟨φ, hφ, fun J J' hJ hJ' h g hgJ' hgJ => ?_⟩
  have := isPhi_unique E (hφ J' hJ') (isPhi_restrict E h (hφ J hJ))
  exact DFunLike.congr_fun this ⟨g, hgJ'⟩

end CFSG.ClassicalInvolution.PhanB3
