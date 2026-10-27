module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenMoore
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup CFSG.Sporadic.SchreierLemmas

section Asm

variable {G : Type*} [Group G] {n : ℕ}

structure RootFamily.IsWLift (ψ : RootFamily G n) (z : G)
    (ι : alternatingGroup (Fin n) →* G) : Prop where
  agree : ψ.Agree
  diag : ∀ (S : Finset (Fin n)) (hS : S.card = 3) (x : ↥(altSub Sᶜ)),
    ψ S hS x * (z * ψ S hS x * z⁻¹) =
      ι (Subgroup.inclusion (altSub_le_alternatingGroup Sᶜ) x)
  comm : ∀ (S : Finset (Fin n)) (hS : S.card = 3) (x y : ↥(altSub Sᶜ)),
    ψ S hS x * (z * ψ S hS y * z⁻¹) = (z * ψ S hS y * z⁻¹) * ψ S hS x

theorem exists_wlift_of_rootFamily (hn : 10 ≤ n) {ψ : RootFamily G n} {z : G}
    {ι : alternatingGroup (Fin n) →* G} (h : ψ.IsWLift z ι) (hι : Function.Injective ι) :
    ∃ Ψ : alternatingGroup (Fin n) →* G,
      (∀ x, Ψ x * (z * Ψ x * z⁻¹) = ι x) ∧
      (∀ x y, Ψ x * (z * Ψ y * z⁻¹) = (z * Ψ y * z⁻¹) * Ψ x) ∧ Function.Injective Ψ := by
  obtain ⟨Ψ, hΨ⟩ := exists_hom_of_rootFamily hn h.agree
  set gens : Set ℕ := Set.Icc 1 (n - 2) with hgens
  have hgen : ∀ i ∈ gens, ∀ j ∈ gens,
      Ψ (mooreCycle n i) * (z * Ψ (mooreCycle n j) * z⁻¹) =
        (z * Ψ (mooreCycle n j) * z⁻¹) * Ψ (mooreCycle n i) := by
    intro i hi j hj
    obtain ⟨S, hS, hSi, hSj⟩ := exists_root_avoiding_two hn i j
    rw [hΨ i hi S hS hSi, hΨ j hj S hS hSj]
    exact h.comm S hS _ _
  have hdiag : ∀ i ∈ gens,
      Ψ (mooreCycle n i) * (z * Ψ (mooreCycle n i) * z⁻¹) = ι (mooreCycle n i) := by
    intro i hi
    obtain ⟨S, hS, hSi, -⟩ := exists_root_avoiding_two hn i i
    rw [hΨ i hi S hS hSi, h.diag S hS]
    rfl
  have htop := closure_mooreCycle (show 3 ≤ n by omega)
  have hall1 : ∀ j ∈ gens, ∀ y, Ψ y * (z * Ψ (mooreCycle n j) * z⁻¹) =
      (z * Ψ (mooreCycle n j) * z⁻¹) * Ψ y := by
    intro j hj y
    have hle : Subgroup.closure (mooreCycle n '' gens) ≤
        (Subgroup.centralizer ({z * Ψ (mooreCycle n j) * z⁻¹} : Set G)).comap Ψ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hgen i hi j hj)
    have hy : y ∈ (Subgroup.centralizer ({z * Ψ (mooreCycle n j) * z⁻¹} : Set G)).comap Ψ :=
      hle (by rw [hgens, htop]; exact Subgroup.mem_top y)
    exact mem_centralizer_singleton_iff.1 hy
  have hall : ∀ x y, Ψ x * (z * Ψ y * z⁻¹) = (z * Ψ y * z⁻¹) * Ψ x := by
    intro x y
    have hle : Subgroup.closure (mooreCycle n '' gens) ≤
        (Subgroup.centralizer ({Ψ x} : Set G)).comap
          ((MulAut.conj z).toMonoidHom.comp Ψ) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have := hall1 j hj x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact this.symm
    have hy : y ∈ (Subgroup.centralizer ({Ψ x} : Set G)).comap
        ((MulAut.conj z).toMonoidHom.comp Ψ) :=
      hle (by rw [hgens, htop]; exact Subgroup.mem_top y)
    have := mem_centralizer_singleton_iff.1 hy
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    exact this.symm
  let Φ : alternatingGroup (Fin n) →* G :=
    MonoidHom.mk' (fun x => Ψ x * (z * Ψ x * z⁻¹)) (fun x y => by
      have hc := hall y x
      calc Ψ (x * y) * (z * Ψ (x * y) * z⁻¹)
          = Ψ x * (Ψ y * (z * Ψ x * z⁻¹)) * (z * Ψ y * z⁻¹) := by
            simp only [map_mul]; group
        _ = Ψ x * ((z * Ψ x * z⁻¹) * Ψ y) * (z * Ψ y * z⁻¹) := by rw [hc]
        _ = (Ψ x * (z * Ψ x * z⁻¹)) * (Ψ y * (z * Ψ y * z⁻¹)) := by group)
  have hΦ : Φ = ι := hom_ext_mooreCycle (show 3 ≤ n by omega) (fun i hi => hdiag i hi)
  refine ⟨Ψ, fun x => by simpa [Φ] using DFunLike.congr_fun hΦ x, hall, ?_⟩
  intro x y hxy
  apply hι
  have h1 := DFunLike.congr_fun hΦ x
  have h2 := DFunLike.congr_fun hΦ y
  simp only [Φ, MonoidHom.mk'_apply] at h1 h2
  rw [← h1, ← h2, hxy]

end Asm

section Pair

variable {G : Type} [Group G] {n : ℕ}

@[expose] def embAlt {L : Subgroup G} (e : L ≃* alternatingGroup (Fin n)) :
    alternatingGroup (Fin n) →* G :=
  L.subtype.comp e.symm.toMonoidHom

theorem embAlt_injective {L : Subgroup G} (e : L ≃* alternatingGroup (Fin n)) :
    Function.Injective (embAlt e) :=
  Subtype.val_injective.comp e.symm.injective

theorem wreathPair_of_wlift {L : Subgroup G} (e : L ≃* alternatingGroup (Fin n)) {z : G}
    {Ψ : alternatingGroup (Fin n) →* G} (hdiag : ∀ x, Ψ x * (z * Ψ x * z⁻¹) = embAlt e x)
    (hcomm : ∀ x y, Ψ x * (z * Ψ y * z⁻¹) = (z * Ψ y * z⁻¹) * Ψ x)
    (hinj : Function.Injective Ψ) : WreathPair L z n Ψ.range := by
  refine ⟨⟨(MonoidHom.ofInjective hinj).symm⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact hcomm x y
  · ext g
    constructor
    · intro hg
      refine ⟨Ψ (e ⟨g, hg⟩), ⟨_, rfl⟩, ?_⟩
      rw [hdiag]
      simp [embAlt]
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      rw [hdiag]
      exact (e.symm x).2

end Pair

end CFSG.OddStandard.AltStdSec
