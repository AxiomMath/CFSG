module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

section Aut

variable {Y : Type} [Group Y]

theorem innAut_normal' : (innAut Y).Normal :=
  ⟨fun _ hψ φ => mul_mul_inv_mem_innAut φ hψ⟩

theorem conj_apply_eq_mul_mul_inv (φ : MulAut Y) (y : Y) :
    MulAut.conj (φ y) = φ * MulAut.conj y * φ⁻¹ := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem conj_injective_of_center_eq_bot (hZ : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  rw [← hZ, mem_center_iff]
  intro g
  have := congrArg (fun φ : MulAut Y => φ g) hy
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc g * y = y * g * y⁻¹ * y := by rw [this]
    _ = y * g := by group

theorem centralizer_innAut_eq_bot (hZ : center Y = ⊥) :
    centralizer (innAut Y : Set (MulAut Y)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [mem_bot]
  ext y
  rw [MulAut.one_apply]
  have h1 : φ * MulAut.conj y = MulAut.conj y * φ :=
    (mem_centralizer_iff.mp hφ (MulAut.conj y) ⟨y, rfl⟩).symm
  have h2 : MulAut.conj (φ y) = MulAut.conj y := by
    rw [conj_apply_eq_mul_mul_inv, h1, mul_inv_cancel_right]
  exact conj_injective_of_center_eq_bot hZ h2

end Aut

section Odd

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} [E.Normal]

theorem pPrimeCore_eq_bot_of_harris34 (h34 : Harris81Lemma34Input) (hE : IsQuasisimple ↥E)
    (hZ : IsPGroup 2 ↥(center ↥E)) {τ : G} (hτ : orderOf τ = 2) (hτE : ⁅E, zpowers τ⁆ = E)
    {K : Subgroup G} (hK : IsTwoComponentIn K (E ⊓ centralizer {τ}))
    (hKZ : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : HarrisF p (↥E ⧸ center ↥E))
    (hKm : ∃ p' f' : ℕ, Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p' f') :
    pPrimeCore 2 ↥K = ⊥ := by
  have : IsSimpleGroup (↥E ⧸ center ↥E) := hE.2.1
  have hZY : center (↥E ⧸ center ↥E) = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hE.2.2).2
  have hinj := conj_injective_of_center_eq_bot hZY
  let eI : (↥E ⧸ center ↥E) ≃* ↥(innAut (↥E ⧸ center ↥E)) := MonoidHom.ofInjective hinj
  have : (innAut (↥E ⧸ center ↥E)).Normal := innAut_normal'
  have : IsSimpleGroup ↥(innAut (↥E ⧸ center ↥E)) := eI.symm.isSimpleGroup
  have hIna : ∃ a b : ↥(innAut (↥E ⧸ center ↥E)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hE.2.2
    exact ⟨eI a, eI b, fun h => hab (eI.injective (by rw [map_mul, map_mul, h]))⟩
  have hFstar : Open.genFittingFStar (MulAut (↥E ⧸ center ↥E)) = innAut (↥E ⧸ center ↥E) :=
    ClassicalInvolution.genFittingFStar_eq_of_normal_simple _ hIna (centralizer_innAut_eq_bot hZY)
  have hιC : ∀ y : ↥(fixedPoints (quotCenterConj E τ)),
      MulAut.conj (y : ↥E ⧸ center ↥E) ∈ centralizer ({quotCenterConj E τ} : Set _) := by
    intro y
    rw [mem_centralizer_singleton_iff]
    have h := conj_apply_eq_mul_mul_inv (quotCenterConj E τ) (y : ↥E ⧸ center ↥E)
    rw [show quotCenterConj E τ (y : ↥E ⧸ center ↥E) = y from y.2] at h
    calc MulAut.conj (y : ↥E ⧸ center ↥E) * quotCenterConj E τ =
          quotCenterConj E τ * MulAut.conj (y : ↥E ⧸ center ↥E) * (quotCenterConj E τ)⁻¹ *
            quotCenterConj E τ := by rw [← h]
      _ = quotCenterConj E τ * MulAut.conj (y : ↥E ⧸ center ↥E) := by group
  let ι : ↥(fixedPoints (quotCenterConj E τ)) →*
      ↥(centralizer ({quotCenterConj E τ} : Set (MulAut (↥E ⧸ center ↥E)))) :=
    (MulAut.conj.comp (fixedPoints (quotCenterConj E τ)).subtype).codRestrict _ hιC
  have hιinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))
  have hιn : ι.range.Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨y, rfl⟩ := hn
    have hc : (c : MulAut (↥E ⧸ center ↥E)) * quotCenterConj E τ =
        quotCenterConj E τ * c := mem_centralizer_singleton_iff.mp c.2
    have hcy : (c : MulAut (↥E ⧸ center ↥E)) (y : ↥E ⧸ center ↥E) ∈
        fixedPoints (quotCenterConj E τ) := by
      rw [mem_fixedPoints]
      calc quotCenterConj E τ ((c : MulAut (↥E ⧸ center ↥E)) (y : ↥E ⧸ center ↥E)) =
            ((quotCenterConj E τ) * c) (y : ↥E ⧸ center ↥E) := rfl
        _ = (c * quotCenterConj E τ) (y : ↥E ⧸ center ↥E) := by rw [hc]
        _ = (c : MulAut (↥E ⧸ center ↥E)) (quotCenterConj E τ y) := rfl
        _ = (c : MulAut (↥E ⧸ center ↥E)) (y : ↥E ⧸ center ↥E) := by rw [show
            quotCenterConj E τ (y : ↥E ⧸ center ↥E) = y from y.2]
    refine ⟨⟨_, hcy⟩, Subtype.ext ?_⟩
    exact conj_apply_eq_mul_mul_inv _ _
  have hχinj : Function.Injective (ι.comp (toFixedQuot hK.1)) :=
    hιinj.comp (toFixedQuot_injective hZ hK.1 hKZ)
  set J := (ι.comp (toFixedQuot hK.1)).range.map
    (centralizer ({quotCenterConj E τ} : Set (MulAut (↥E ⧸ center ↥E)))).subtype with hJdef
  let eKJ : ↥K ≃* ↥J := (MonoidHom.ofInjective hχinj).trans
    ((ι.comp (toFixedQuot hK.1)).range.equivMapOfInjective _ (subtype_injective _))
  have hJC : J ≤ centralizer ({quotCenterConj E τ} : Set (MulAut (↥E ⧸ center ↥E))) :=
    map_subtype_le _
  have hsub : J.subgroupOf (centralizer ({quotCenterConj E τ} : Set (MulAut (↥E ⧸ center ↥E)))) =
      (toFixedQuot hK.1).range.map ι := by
    rw [hJdef, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _),
      MonoidHom.range_comp]
  have hJsub : (J.subgroupOf
      (centralizer ({quotCenterConj E τ} : Set (MulAut (↥E ⧸ center ↥E))))).IsSubnormal := by
    rw [hsub]
    exact isSubnormal_map_of_range_normal ι hιn (isSubnormal_range_toFixedQuot hK)
  have hJ2 : IsTwoComponentIn J (centralizer {quotCenterConj E τ}) :=
    ⟨hJC, hJsub, isTwoQuasisimple_of_mulEquiv eKJ hK.2.2⟩
  have hJm : ∃ p' f' : ℕ, Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p' f' := by
    obtain ⟨p', f', hm⟩ := hKm
    exact ⟨p', f', GSThmB.OddQuot.lieModel_of_equiv
      (QuotientGroup.congr _ _ eKJ (pPrimeCore_map_iso 2 eKJ)) hm⟩
  have hOJ := h34 (MulAut (↥E ⧸ center ↥E)) p hp hp2 (by rw [hFstar]; infer_instance)
    (by rw [hFstar]; exact harrisF_of_mulEquiv eI hF) J
    ⟨quotCenterConj E τ, orderOf_quotCenterConj hE hτ hτE, hJ2⟩ hJm
  have hmap := pPrimeCore_map_iso 2 eKJ
  rw [hOJ] at hmap
  exact (map_eq_bot_iff_of_injective _ eKJ.injective).mp hmap

end Odd

end CFSG.ComponentClassification.HarrisLit
