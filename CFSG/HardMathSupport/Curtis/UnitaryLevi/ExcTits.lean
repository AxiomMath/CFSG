module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoxeterKernel
public import CFSG.LieType.Chevalley.ChevalleySplitBN

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

theorem conj_inv_eq_aux {G : Type*} [Group G] (n z : G) :
    n⁻¹ * z * n = (n ^ 2)⁻¹ * (n * z * n⁻¹) * n ^ 2 := by
  group

theorem conj_mul_aux {G : Type*} [Group G] (n a b : G) :
    n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by
  group

theorem conj_inv_aux {G : Type*} [Group G] (n a : G) : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by
  group

variable (τ : Tag) (K : Type) [Field K]

@[expose] noncomputable def monoι : ↥(monomialSub τ K) →* ModGL τ K :=
  (adjointGroup τ K).subtype.comp (monomialSub τ K).subtype

theorem monoι_injective : Function.Injective (monoι τ K) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem monoι_weylRep (i : Fin τ.rank) : monoι τ K (weylRep τ K i) = weylElt τ K i 1 := rfl

theorem weylRep_sq (i : Fin τ.rank) :
    monoι τ K (weylRep τ K i ^ 2) = torusElt τ K i (-1) := by
  rw [map_pow, monoι_weylRep, weylElt_one_sq]

theorem weylRep_sq_sq (i : Fin τ.rank) : (weylRep τ K i ^ 2) ^ 2 = 1 := by
  apply monoι_injective
  rw [map_pow, weylRep_sq, sq, ← torusElt_mul, map_one]
  simp [torusElt_one]

theorem weylRep_sq_comm (i j : Fin τ.rank) :
    weylRep τ K i ^ 2 * weylRep τ K j ^ 2 = weylRep τ K j ^ 2 * weylRep τ K i ^ 2 := by
  apply monoι_injective
  rw [map_mul, map_mul, weylRep_sq, weylRep_sq]
  exact torusElt_mul_comm i j _ _


@[expose] noncomputable def Z0 : Subgroup ↥(monomialSub τ K) :=
  Subgroup.closure (Set.range fun i => weylRep τ K i ^ 2)

@[expose] noncomputable def What : Subgroup ↥(monomialSub τ K) :=
  Subgroup.closure (Set.range (weylRep τ K))

theorem weylRep_sq_mem_Z0 (i : Fin τ.rank) : weylRep τ K i ^ 2 ∈ Z0 τ K :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem weylRep_mem_What (i : Fin τ.rank) : weylRep τ K i ∈ What τ K :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem Z0_le_What : Z0 τ K ≤ What τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact pow_mem (weylRep_mem_What τ K i) 2

theorem weylRep_conj_sq (j i : Fin τ.rank) :
    weylRep τ K j * weylRep τ K i ^ 2 * (weylRep τ K j)⁻¹ ∈ Z0 τ K := by
  have key : weylRep τ K j * weylRep τ K i ^ 2 * (weylRep τ K j)⁻¹ =
      weylRep τ K i ^ 2 * (if Even (τ.cartan i j) then 1 else weylRep τ K j ^ 2) := by
    apply monoι_injective
    rw [map_mul, map_mul, map_inv, map_mul, weylRep_sq, monoι_weylRep,
      weylElt_one_mul_torusElt_mul_inv]
    congr 1
    split_ifs with h
    · rw [Even.neg_one_zpow (by simpa using h), torusElt_one, map_one]
    · rw [Odd.neg_one_zpow (by simpa using (Int.not_even_iff_odd.1 h)), weylRep_sq]
  rw [key]
  refine mul_mem (weylRep_sq_mem_Z0 τ K i) ?_
  split_ifs
  · exact one_mem _
  · exact weylRep_sq_mem_Z0 τ K j

theorem Z0_conj_gen (j : Fin τ.rank) {z : ↥(monomialSub τ K)} (hz : z ∈ Z0 τ K) :
    weylRep τ K j * z * (weylRep τ K j)⁻¹ ∈ Z0 τ K ∧
      (weylRep τ K j)⁻¹ * z * weylRep τ K j ∈ Z0 τ K := by
  have h1 : ∀ z ∈ Z0 τ K, weylRep τ K j * z * (weylRep τ K j)⁻¹ ∈ Z0 τ K := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact weylRep_conj_sq τ K j i
    | one => simpa using one_mem (Z0 τ K)
    | mul a b _ _ ha hb =>
      rw [conj_mul_aux]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [conj_inv_aux]
      exact inv_mem ha
  refine ⟨h1 z hz, ?_⟩
  rw [conj_inv_eq_aux]
  exact mul_mem (mul_mem (inv_mem (weylRep_sq_mem_Z0 τ K j)) (h1 z hz))
    (weylRep_sq_mem_Z0 τ K j)

theorem Z0_conj_What {g : ↥(monomialSub τ K)} (hg : g ∈ What τ K) {z : ↥(monomialSub τ K)}
    (hz : z ∈ Z0 τ K) : g * z * g⁻¹ ∈ Z0 τ K := by
  have : ∀ z ∈ Z0 τ K, g * z * g⁻¹ ∈ Z0 τ K ∧ g⁻¹ * z * g ∈ Z0 τ K := by
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact fun z hz => Z0_conj_gen τ K j hz
    | one => exact fun z hz => by simpa using And.intro hz hz
    | mul a b _ _ ha hb =>
      intro z hz
      refine ⟨?_, ?_⟩
      · have := (ha _ ((hb z hz).1)).1
        simpa [mul_assoc] using this
      · have := (hb _ ((ha z hz).2)).2
        simpa [mul_assoc] using this
    | inv a _ ha =>
      intro z hz
      simpa using (ha z hz).symm
  exact (this z hz).1

theorem Z0_comm {a b : ↥(monomialSub τ K)} (ha : a ∈ Z0 τ K) (hb : b ∈ Z0 τ K) :
    a * b = b * a := by
  have hcomm : ∀ x ∈ Set.range (fun i => weylRep τ K i ^ 2),
      x ∈ Subgroup.centralizer (Set.range (fun i => weylRep τ K i ^ 2)) := by
    rintro _ ⟨i, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    exact (weylRep_sq_comm τ K j i)
  have h1 : Z0 τ K ≤ Subgroup.centralizer (Set.range (fun i => weylRep τ K i ^ 2)) :=
    (Subgroup.closure_le _).2 hcomm
  have h2 := h1 ha
  rw [← Subgroup.centralizer_closure] at h2
  exact (Subgroup.mem_centralizer_iff.1 h2 b hb).symm

theorem Z0_sq {z : ↥(monomialSub τ K)} (hz : z ∈ Z0 τ K) : z ^ 2 = 1 := by
  induction hz using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact weylRep_sq_sq τ K i
  | one => simp
  | mul a b ha hb ha2 hb2 =>
    rw [(show Commute a b from Z0_comm τ K ha hb).mul_pow, ha2, hb2, one_mul]
  | inv a ha ha2 => simp [inv_pow, ha2]


section Kernel


theorem Z0_le_ker : Z0 τ K ≤ (monomialSubHom (τ := τ) (K := K)).ker := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  have h := (coxeterSystem τ).simple_mul_simple_self i
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_pow, monomialSubHom_weylRep, sq]
  exact h

theorem What_ker_le_Z0 {x : ↥(monomialSub τ K)} (hx : x ∈ What τ K)
    (h : monomialSubHom (τ := τ) (K := K) x = 1) : x ∈ Z0 τ K := by
  classical
  let f : Fin τ.rank → ↥(What τ K) := fun i => ⟨weylRep τ K i, weylRep_mem_What τ K i⟩
  let Z : Subgroup ↥(What τ K) := (Z0 τ K).subgroupOf (What τ K)
  haveI : Z.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := Z0_conj_What τ K g.2 hn
    simpa using this⟩
  let π : ↥(What τ K) →* WeylGroup τ := (monomialSubHom (τ := τ) (K := K)).comp (What τ K).subtype
  have hcoe : ∀ (a b : Fin τ.rank) (m : ℕ),
      ((((CoxeterSystem.alternatingWord a b m).map f).prod : ↥(What τ K)) : ↥(monomialSub τ K)) =
        ((CoxeterSystem.alternatingWord a b m).map (weylRep τ K)).prod := fun a b m => by
    rw [← (What τ K).subtype_apply, map_list_prod, List.map_map]
    rfl
  have hbr : ∀ i j, ((CoxeterSystem.alternatingWord i j
        ((coxeterMatrix (isFiniteType_cartan τ)) i j)).map f).prod *
      (((CoxeterSystem.alternatingWord j i
        ((coxeterMatrix (isFiniteType_cartan τ)) i j)).map f).prod)⁻¹ ∈ Z := by
    intro i j
    have hM : (coxeterMatrix (isFiniteType_cartan τ)) i j =
        TauCeti.coxeterOrder (τ.cartan i j * τ.cartan j i) := by
      simp [coxeterMatrix]
    have heq : ((CoxeterSystem.alternatingWord i j
        ((coxeterMatrix (isFiniteType_cartan τ)) i j)).map f).prod =
        ((CoxeterSystem.alternatingWord j i
        ((coxeterMatrix (isFiniteType_cartan τ)) i j)).map f).prod := by
      apply Subtype.ext
      rw [hcoe, hcoe]
      apply monoι_injective
      rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
      rw [hM]
      exact prod_alternatingWord_weylElt τ K i j
    rw [heq, mul_inv_cancel]
    exact one_mem _
  have hgen : Subgroup.closure (Set.range f) = ⊤ := by
    have hr : Set.range f = (Subtype.val ⁻¹' Set.range (weylRep τ K) : Set ↥(What τ K)) := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    rw [hr]
    exact Subgroup.closure_closure_coe_preimage (k := Set.range (weylRep τ K))
  have key := ker_le_of_coxeter (coxeterSystem τ) f Z
    (fun i => by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact weylRep_sq_mem_Z0 τ K i)
    hbr hgen π (fun i => monomialSubHom_weylRep i)
    (fun g hg => by
      rw [Subgroup.mem_subgroupOf] at hg
      exact Z0_le_ker τ K hg)
  have := key (show (⟨x, hx⟩ : ↥(What τ K)) ∈ π.ker from h)
  rwa [Subgroup.mem_subgroupOf] at this

section Lift

variable [Finite K]

theorem What_surj (w : WeylGroup τ) : ∃ a ∈ What τ K, monomialSubHom (τ := τ) (K := K) a = w := by
  have : (⊤ : Subgroup (WeylGroup τ)) ≤ (What τ K).map (monomialSubHom (τ := τ) (K := K)) := by
    rw [← (coxeterSystem τ).subgroup_closure_range_simple]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨weylRep τ K i, weylRep_mem_What τ K i, monomialSubHom_weylRep i⟩
  obtain ⟨a, ha, h⟩ := this (Subgroup.mem_top w)
  exact ⟨a, ha, h⟩

theorem exists_lift (Q : Subgroup (WeylGroup τ)) (hQ : IsPGroup 3 Q) :
    ∃ C : Subgroup ↥(monomialSub τ K), C ≤ What τ K ∧
      (∀ x ∈ C, ∀ y ∈ C, monomialSubHom (τ := τ) (K := K) x = monomialSubHom (τ := τ) (K := K) y →
        x = y) ∧
      (∀ q ∈ Q, ∃ c ∈ C, monomialSubHom (τ := τ) (K := K) c = q) ∧
      ∀ c ∈ C, monomialSubHom (τ := τ) (K := K) c ∈ Q :=
  exists_lift_of_ker_two (monomialSubHom (τ := τ) (K := K)) (What τ K) (Z0 τ K)
    (Z0_le_What τ K) (fun z hz => Z0_sq τ K hz)
    (fun x hx h => What_ker_le_Z0 τ K hx h) (Z0_le_ker τ K)
    (fun g hg z hz => Z0_conj_What τ K hg hz) Q hQ (fun q _ => What_surj τ K q)

end Lift

end Kernel


end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
