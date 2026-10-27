module

public import CFSG.FeitThompson.Local.GeneralLinearReductionKernel
import CFSG.FeitThompson.Local.GeneralLinearReductionSurjective
import CFSG.FeitThompson.Foundations.CoprimeAbelianNormalComplements

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Pullback

variable {A G Q : Type*} [Group A] [Group G] [Group Q]

def homPullback (φ : A →* Q) (π : G →* Q) : Subgroup (A × G) :=
  (φ.comp (MonoidHom.fst A G)).eqLocus (π.comp (MonoidHom.snd A G))

@[simp] lemma mem_homPullback_iff {φ : A →* Q} {π : G →* Q} {x : A × G} :
    x ∈ homPullback φ π ↔ φ x.1 = π x.2 := Iff.rfl

def homPullbackFst (φ : A →* Q) (π : G →* Q) : homPullback φ π →* A :=
  (MonoidHom.fst A G).comp (homPullback φ π).subtype

def homPullbackSnd (φ : A →* Q) (π : G →* Q) : homPullback φ π →* G :=
  (MonoidHom.snd A G).comp (homPullback φ π).subtype

@[simp] lemma homPullbackFst_apply (φ : A →* Q) (π : G →* Q) (x : homPullback φ π) :
    homPullbackFst φ π x = (x : A × G).1 := (rfl)

@[simp] lemma homPullbackSnd_apply (φ : A →* Q) (π : G →* Q) (x : homPullback φ π) :
    homPullbackSnd φ π x = (x : A × G).2 := (rfl)

lemma comp_homPullbackSnd (φ : A →* Q) (π : G →* Q) :
    π.comp (homPullbackSnd φ π) = φ.comp (homPullbackFst φ π) := by
  ext x
  exact (mem_homPullback_iff.1 x.2).symm

lemma homPullbackFst_surjective (φ : A →* Q) {π : G →* Q} (hπ : Function.Surjective π) :
    Function.Surjective (homPullbackFst φ π) := by
  intro a
  obtain ⟨g, hg⟩ := hπ (φ a)
  exact ⟨⟨(a, g), mem_homPullback_iff.2 hg.symm⟩, by rw [homPullbackFst_apply]⟩

private lemma fst_eq_one_of_mem_ker {φ : A →* Q} {π : G →* Q}
    {x : (homPullbackFst φ π).ker} : ((x : homPullback φ π) : A × G).1 = 1 := by
  have := x.2
  rwa [MonoidHom.mem_ker, homPullbackFst_apply] at this

noncomputable def kerHomPullbackFstMulEquiv (φ : A →* Q) (π : G →* Q) :
    (homPullbackFst φ π).ker ≃* π.ker := by
  refine MulEquiv.ofBijective
    (((homPullbackSnd φ π).comp (homPullbackFst φ π).ker.subtype).codRestrict π.ker ?_) ?_
  · intro x
    have h1 : φ ((x : homPullback φ π) : A × G).1 = π (((x : homPullback φ π) : A × G).2) :=
      mem_homPullback_iff.1 (x : homPullback φ π).2
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      homPullbackSnd_apply]
    rw [← h1, fst_eq_one_of_mem_ker, map_one]
  · constructor
    · intro x y hxy
      simp only [MonoidHom.codRestrict_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, Subtype.mk.injEq, homPullbackSnd_apply] at hxy
      exact Subtype.ext (Subtype.ext (Prod.ext
        (by rw [fst_eq_one_of_mem_ker, fst_eq_one_of_mem_ker]) hxy))
    · rintro ⟨g, hg⟩
      have hmem : ((1 : A), g) ∈ homPullback φ π := by
        rw [mem_homPullback_iff, MonoidHom.mem_ker] at *
        rw [map_one, hg]
      refine ⟨⟨⟨_, hmem⟩, ?_⟩, ?_⟩
      · rw [MonoidHom.mem_ker, homPullbackFst_apply]
      · exact Subtype.ext (by simp [homPullbackSnd_apply])

@[simp] lemma coe_kerHomPullbackFstMulEquiv (φ : A →* Q) (π : G →* Q)
    (x : (homPullbackFst φ π).ker) :
    ((kerHomPullbackFstMulEquiv φ π x : π.ker) : G) = ((x : homPullback φ π) : A × G).2 := (rfl)

end Pullback

section Lift

variable {A G Q : Type*} [Group A] [Group G] [Group Q]

theorem exists_monoidHom_lift_of_coprime [Finite A] (φ : A →* Q) {π : G →* Q}
    (hπ : Function.Surjective π) (hab : IsMulCommutative π.ker)
    (hcop : (Nat.card π.ker).Coprime (Nat.card A)) :
    ∃ ψ : A →* G, π.comp ψ = φ := by
  set f := homPullbackFst φ π
  have hfsurj : Function.Surjective f := homPullbackFst_surjective φ hπ
  have hequiv : f.ker ≃* π.ker := kerHomPullbackFstMulEquiv φ π
  have : IsMulCommutative f.ker :=
    ⟨⟨fun a b => hequiv.injective (by rw [map_mul, map_mul]; exact hab.is_comm.comm _ _)⟩⟩
  have hindex : f.ker.index = Nat.card A := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hfsurj, Subgroup.card_top]
  have hcard : Nat.card f.ker = Nat.card π.ker := Nat.card_congr hequiv.toEquiv
  set q := QuotientGroup.quotientKerEquivOfSurjective f hfsurj
  have hqapply : ∀ x : homPullback φ π, q (x : _ ⧸ f.ker) = f x := fun _ => rfl
  have : Finite (homPullback φ π ⧸ f.ker) := Finite.of_equiv A q.symm.toEquiv
  obtain ⟨t, ht⟩ := exists_monoidHom_section_of_coprime_index (A := f.ker)
    (by rw [hcard, hindex]; exact hcop)
  refine ⟨(homPullbackSnd φ π).comp (t.comp q.symm.toMonoidHom), ?_⟩
  ext a
  have h1 : f (t (q.symm a)) = a := by rw [← hqapply, ht, MulEquiv.apply_symm_apply]
  calc π ((homPullbackSnd φ π) (t (q.symm a)))
      = φ (f (t (q.symm a))) := DFunLike.congr_fun (comp_homPullbackSnd φ π) _
    _ = φ a := by rw [h1]

end Lift

section Representation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p e : ℕ}

lemma glPowReduction_eq_map :
    glPowReduction ι p e
      = Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e))) := by
  ext g i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun (coe_glPowReduction g) i) j

theorem glPowReduction_surjective (hp : p.Prime) (he : 1 ≤ e) :
    Function.Surjective (glPowReduction ι p e) := by
  rw [glPowReduction_eq_map]
  exact generalLinearGroup_map_castHom_surjective hp (by omega)

variable {A : Type*} [Group A]

theorem exists_monoidHom_glPowReduction_comp_eq [Finite A] (hp : p.Prime) (he : 1 ≤ e)
    (hA : ¬ p ∣ Nat.card A) (ρ : A →* GL ι (ZMod (p ^ e))) :
    ∃ ρ₁ : A →* GL ι (ZMod (p ^ (e + 1))), (glPowReduction ι p e).comp ρ₁ = ρ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine exists_monoidHom_lift_of_coprime ρ (glPowReduction_surjective hp he)
    (isMulCommutative_ker_glPowReduction he) ?_
  rw [nat_card_ker_glPowReduction he]
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hA)

theorem exists_monoidHom_castHom_entry_eq [Finite A] (hp : p.Prime) (he : 1 ≤ e)
    (hA : ¬ p ∣ Nat.card A) (ρ : A →* GL ι (ZMod (p ^ e))) :
    ∃ ρ₁ : A →* GL ι (ZMod (p ^ (e + 1))), ∀ (a : A) (i j : ι),
      ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e)) (ρ₁ a i j) = ρ a i j := by
  obtain ⟨ρ₁, hρ₁⟩ := exists_monoidHom_glPowReduction_comp_eq (ι := ι) hp he hA ρ
  refine ⟨ρ₁, fun a i j => ?_⟩
  have h : glPowReduction ι p e (ρ₁ a) = ρ a := DFunLike.congr_fun hρ₁ a
  calc ZMod.castHom (pow_dvd_pow p e.le_succ) (ZMod (p ^ e)) (ρ₁ a i j)
      = glPowReduction ι p e (ρ₁ a) i j := by
        rw [glPowReduction_eq_map, Matrix.GeneralLinearGroup.map_apply]
    _ = ρ a i j := by rw [h]

end Representation

end CFSG.FeitThompson
