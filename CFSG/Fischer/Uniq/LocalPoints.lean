module

public import CFSG.Fischer.TransvectionPoints
public import CFSG.Fischer.HermitianEquiv

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X}

theorem F22.exists_psu_one (hF : F22 X E) {e : X} (he : e ∈ E) :
    ∃ j : LocalQuotient E e ≃* PSU (1 : Matrix (Fin 6) (Fin 6) K),
      j '' LocalImages E e = Transvections 1 := by
  obtain ⟨H, hH, iso, himg⟩ := F22_local hF he
  obtain ⟨iso1, himg1⟩ := exists_psu_equiv hH
  refine ⟨iso.trans iso1.symm, ?_⟩
  rw [MulEquiv.coe_trans, Set.image_comp, himg, ← himg1]
  exact iso1.toEquiv.symm_image_image _

theorem tvPsu_ne_one
    (m : Fin 693) : tvPsu m ≠ 1 := by
  intro h
  apply tvP_ne_one m
  rw [← psuT46_tvPsu, h, map_one]
  rfl

theorem one_notMem_transvections :
    (1 : PSU (1 : Matrix (Fin 6) (Fin 6) K)) ∉ Transvections 1 := by
  rw [transvections_eq]
  rintro ⟨m, hm⟩
  exact tvPsu_ne_one m hm

theorem F22.exists_localPoints
    (hF : F22 X E) {e : X} (he : e ∈ E) :
    ∃ χ : LocalClass E e ≃ Fin 693,
      (∀ f g : LocalClass E e, (f : X) * g = g * f ↔ hermStd (uVec (χ f)) (uVec (χ g)) = 0) ∧
      ∀ (f g : LocalClass E e) (h : (f : X) * g * f ∈ LocalClass E e),
        χ ⟨_, h⟩ = tvP (χ f) (χ g) := by
  have hP : Pair X E := hF.1
  obtain ⟨j, hj⟩ := F22.exists_psu_one hF he
  have hmem : ∀ f : LocalClass E e, ∃ m, j (starImage E e f) = tvPsu m := by
    intro f
    have : j (starImage E e f) ∈ Transvections 1 := by
      rw [← hj, ← range_starImage]
      exact ⟨_, ⟨f, rfl⟩, rfl⟩
    exact exists_tvPsu _ this
  have hone : (1 : LocalQuotient E e) ∉ LocalImages E e := by
    intro h1
    apply one_notMem_transvections
    rw [← hj]
    exact ⟨1, h1, map_one j⟩
  have hinj := Pair.starImage_injective_of_one_notMem hP hone
  let χ0 : LocalClass E e → Fin 693 := fun f => Classical.choose (hmem f)
  have hχ0 : ∀ f, j (starImage E e f) = tvPsu (χ0 f) := fun f => Classical.choose_spec (hmem f)
  have hbij : Function.Bijective χ0 := by
    constructor
    · intro f g hfg
      apply hinj
      apply j.injective
      rw [hχ0, hχ0, hfg]
    · intro m
      have : tvPsu m ∈ j '' LocalImages E e := by rw [hj]; exact tvPsu_mem m
      obtain ⟨q, hq, hqm⟩ := this
      rw [← range_starImage] at hq
      obtain ⟨f, rfl⟩ := hq
      exact ⟨f, tvPsu_injective ((hχ0 f).symm.trans hqm)⟩
  let χ := Equiv.ofBijective χ0 hbij
  have hχ : ∀ f, j (starImage E e f) = tvPsu (χ f) := hχ0
  refine ⟨χ, fun f g => ?_, fun f g h => ?_⟩
  · have h1 : (f : X) * g = g * f ↔
        starImage E e f * starImage E e g = starImage E e g * starImage E e f := by
      rw [← commute_iff_eq, ← commute_iff_eq]
      exact (Pair.starImage_commute_iff hP f g).symm
    rw [h1, ← tvP_comm_iff]
    constructor
    · intro hc
      have := congrArg (fun q => (psuT46 (j q) : Equiv.Perm (Fin 693))) hc
      simp only [map_mul, Subgroup.coe_mul, hχ, psuT46_tvPsu] at this
      exact this
    · intro hc
      apply j.injective
      apply psuT46.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul, hχ, psuT46_tvPsu]
      exact hc
  · apply tvP_injective
    rw [← tvP_conj, ← psuT46_tvPsu, ← psuT46_tvPsu, ← psuT46_tvPsu, ← hχ, ← hχ, ← hχ]
    rw [starImage_conj f g h, map_mul, map_mul, map_mul, map_mul]
    rfl

end CFSG.Fischer
