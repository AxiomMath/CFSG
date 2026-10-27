module

public import CFSG.Open.FischerExistenceUniquenessMilestoneDefs
public import CFSG.Fischer.HermitianEquiv

public section

namespace CFSG.Fischer

open CFSG.Open CFSG.Blueprint.Fischer Matrix

variable {X : Type} [Group X]

theorem pair_iff (E : Set X) : Pair X E ↔ Finite X ∧ fischerEUIsPair E := by
  unfold Pair fischerEUIsPair
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩

theorem fischerEULocalSet_eq (E : Set X) (e : X) : fischerEULocalSet E e = LocalClass E e := rfl

theorem fischerEULocalGroup_eq (E : Set X) (e : X) :
    fischerEULocalGroup E e = LocalGroup E e := rfl

theorem hermitian_one (x y : V) : hermitian 1 x y = fischerEUHerm x y := by
  unfold hermitian fischerEUHerm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Ne.symm hji]
  · simp

theorem SU_one_eq : SU (1 : Matrix (Fin 6) (Fin 6) K) = fischerEUSU := by
  unfold SU fischerEUSU
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, hermitian_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← Matrix.GeneralLinearGroup.val_det_apply, h1]; rfl, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, h1]; rfl), h2⟩

noncomputable def psuOpenEquiv : PSU (1 : Matrix (Fin 6) (Fin 6) K) ≃* fischerEUPSU :=
  quotientCenterCongr (MulEquiv.subgroupCongr SU_one_eq)

theorem psuOpenEquiv_mk (u : SU (1 : Matrix (Fin 6) (Fin 6) K)) :
    psuOpenEquiv (QuotientGroup.mk u) =
      QuotientGroup.mk (MulEquiv.subgroupCongr SU_one_eq u) :=
  quotientCenterCongr_mk _ _

theorem psuOpenEquiv_image :
    psuOpenEquiv '' Transvections 1 = fischerEUTransvections := by
  ext q
  constructor
  · rintro ⟨_, ⟨u, rfl, v, hv0, hviso, hact⟩, rfl⟩
    refine ⟨MulEquiv.subgroupCongr SU_one_eq u, v, hv0, by rw [← hermitian_one]; exact hviso,
      fun x => ?_, psuOpenEquiv_mk u⟩
    rw [← hermitian_one]
    exact hact x
  · rintro ⟨A, v, hv0, hviso, hact, rfl⟩
    refine ⟨QuotientGroup.mk ((MulEquiv.subgroupCongr SU_one_eq).symm A),
      ⟨(MulEquiv.subgroupCongr SU_one_eq).symm A, rfl, v, hv0, by rw [hermitian_one]; exact hviso,
        fun x => ?_⟩, ?_⟩
    · rw [hermitian_one]
      exact hact x
    · rw [psuOpenEquiv_mk, MulEquiv.apply_symm_apply]

theorem fischerEULocalClass_eq' (E : Set X) (e : X) :
    fischerEULocalClass E e = LocalImages E e := by
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩

theorem F22.typeF22_open {E : Set X} (h : F22 X E) : fischerEUTypeF22 E := by
  obtain ⟨-, e, he, H, hH, iso, himg⟩ := h
  obtain ⟨iso1, himg1⟩ := exists_psu_equiv hH
  let ψ : LocalQuotient E e ≃* fischerEUPSU := (iso.trans iso1.symm).trans psuOpenEquiv
  have hψ : ψ '' LocalImages E e = fischerEUTransvections := by
    rw [← psuOpenEquiv_image]
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨iso1.symm (iso q), ?_, rfl⟩
      have : iso q ∈ iso1 '' Transvections 1 := by rw [himg1, ← himg]; exact ⟨q, hq, rfl⟩
      obtain ⟨t, ht, hte⟩ := this
      rw [← hte, MulEquiv.symm_apply_apply]
      exact ht
    · rintro ⟨t, ht, rfl⟩
      have : iso1 t ∈ iso '' LocalImages E e := by rw [himg, ← himg1]; exact ⟨t, ht, rfl⟩
      obtain ⟨q, hq, hqe⟩ := this
      refine ⟨q, hq, ?_⟩
      show psuOpenEquiv (iso1.symm (iso q)) = psuOpenEquiv t
      rw [hqe, MulEquiv.symm_apply_apply]
  exact ⟨e, he, ψ, by rw [fischerEULocalClass_eq']; exact hψ⟩

theorem F22_of_typeF22_open {E : Set X} (hP : Pair X E) (h : fischerEUTypeF22 E) : F22 X E := by
  obtain ⟨e, he, φ, himg⟩ := h
  let ψ : LocalQuotient E e ≃* PSU (1 : Matrix (Fin 6) (Fin 6) K) := φ.trans psuOpenEquiv.symm
  have hψ : ψ '' LocalImages E e = Transvections 1 := by
    rw [fischerEULocalClass_eq'] at himg
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      have : φ q ∈ psuOpenEquiv '' Transvections 1 := by
        rw [psuOpenEquiv_image, ← himg]; exact ⟨q, hq, rfl⟩
      obtain ⟨t, ht, hte⟩ := this
      show psuOpenEquiv.symm (φ q) ∈ _
      rw [← hte, MulEquiv.symm_apply_apply]
      exact ht
    · intro hy
      have : psuOpenEquiv y ∈ φ '' LocalImages E e := by
        rw [himg, ← psuOpenEquiv_image]; exact ⟨y, hy, rfl⟩
      obtain ⟨q, hq, hqe⟩ := this
      refine ⟨q, hq, ?_⟩
      show psuOpenEquiv.symm (φ q) = y
      rw [hqe, MulEquiv.symm_apply_apply]
  exact ⟨hP, e, he, 1, isNondegenerateHermitian_one, ψ, hψ⟩

theorem typeF22_open_iff {E : Set X} (hP : Pair X E) : fischerEUTypeF22 E ↔ F22 X E :=
  ⟨F22_of_typeF22_open hP, F22.typeF22_open⟩

theorem F23.typeF23_open {E : Set X} (h : F23 X E) : fischerEUTypeF23 E := by
  obtain ⟨-, e, he, h22⟩ := h
  refine ⟨e, he, ?_, ?_⟩
  · rw [fischerEULocalClass_eq']
    exact ((pair_iff _).1 h22.1).2
  · rw [fischerEULocalClass_eq']
    exact F22.typeF22_open h22

end CFSG.Fischer
