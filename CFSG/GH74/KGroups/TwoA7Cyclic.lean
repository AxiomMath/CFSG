module

public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG CFSG.GH74.GLS CFSG.Assembly.LowTwoRank Subgroup

section Cyclic

variable {X : Type*} [Group X]

theorem le_pPrimeCore_of_odd {M : Subgroup X} [M.Normal] (hM : ¬ 2 ∣ Nat.card M) :
    M ≤ pPrimeCore 2 X :=
  le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hM⟩

theorem quotient_comm_of_cyclic_sylow [Finite X] (h : ∀ P : Sylow 2 X, IsCyclic P)
    (a b : X ⧸ pPrimeCore 2 X) : a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hdvd : 2 ∣ Nat.card X
  · have hmin : (Nat.card X).minFac = 2 := by
      have h1 : (Nat.card X).minFac ≤ 2 := Nat.minFac_le_of_dvd (le_refl 2) hdvd
      have h2 := Nat.minFac_prime (n := Nat.card X) (by rintro h1; rw [h1] at hdvd; omega)
      have := h2.two_le
      omega
    obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
    have hP := h P
    have hcomp := IsCyclic.isComplement' hmin hP
    set M := (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hmin)).ker with hM
    have hMn : ¬ 2 ∣ Nat.card M := MonoidHom.not_dvd_card_ker_transferSylow P _
    have hMN : M ≤ pPrimeCore 2 X := le_pPrimeCore_of_odd hMn
    have hsup : M ⊔ (P : Subgroup X) = ⊤ := hcomp.sup_eq_top
    have hform : ∀ x : X, ∃ p ∈ (P : Subgroup X), (x : X ⧸ pPrimeCore 2 X) = p := by
      intro x
      have hx : x ∈ M ⊔ (P : Subgroup X) := by rw [hsup]; exact mem_top x
      obtain ⟨m, hm, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      refine ⟨p, hp, ?_⟩
      have : ((m : X) : X ⧸ pPrimeCore 2 X) = 1 := (QuotientGroup.eq_one_iff m).2 (hMN hm)
      rw [QuotientGroup.mk_mul, this, one_mul]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨p, hp, hxp⟩ := hform x
    obtain ⟨q, hq, hyq⟩ := hform y
    rw [hxp, hyq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have : IsCyclic (P : Subgroup X) := hP
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(P : Subgroup X))).comm
        (⟨p, hp⟩ : (P : Subgroup X)) ⟨q, hq⟩)
  ·
    have hMn : ¬ 2 ∣ Nat.card (⊤ : Subgroup X) := by
      rwa [Subgroup.card_top]
    have hle : (⊤ : Subgroup X) ≤ pPrimeCore 2 X := le_pPrimeCore_of_odd hMn
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : ((x : X) : X ⧸ pPrimeCore 2 X) = 1 := (QuotientGroup.eq_one_iff x).2 (hle (mem_top x))
    have hy : ((y : X) : X ⧸ pPrimeCore 2 X) = 1 := (QuotientGroup.eq_one_iff y).2 (hle (mem_top y))
    rw [hx, hy]

theorem not_exists_pComponent_of_comm
    (hc : ∀ a b : X ⧸ pPrimeCore 2 X, a * b = b * a) : ¬ ∃ L : Subgroup X, IsPComponent 2 L := by
  rintro ⟨L, K, ⟨⟨-, -, a, b, hab⟩, -⟩, -, -, -⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hc x y)

section SL2

variable (F : Type) [Field F]

def tU : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp)

def tL : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by simp)

theorem tU_mem : tU F ∈ StatedSL 2 F :=
  Subgroup.subset_closure (by simp [tU, Matrix.GeneralLinearGroup.mkOfDetNeZero])

theorem tL_mem : tL F ∈ StatedSL 2 F :=
  Subgroup.subset_closure (by simp [tL, Matrix.GeneralLinearGroup.mkOfDetNeZero])

theorem exists_noncomm : ∃ u v : StatedSL 2 F, u * v ≠ v * u := by
  refine ⟨⟨tU F, tU_mem F⟩, ⟨tL F, tL_mem F⟩, fun h => ?_⟩
  have h1 := congrArg (fun g : StatedSL 2 F => (g : GL (Fin 2) F)) h
  have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  simp [tU, tL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two] at h2

end SL2

theorem not_hasSolvableTwoComponentSL23_of_comm
    (hc : ∀ a b : X ⧸ pPrimeCore 2 X, a * b = b * a) : ¬ HasSolvableTwoComponentSL23 X := by
  rintro ⟨W, -, F, hF, -, -, ⟨e⟩⟩
  obtain ⟨u, v, huv⟩ := exists_noncomm F
  apply huv
  have h1 : e.symm u * e.symm v = e.symm v * e.symm u := Subtype.ext (hc _ _)
  have := congrArg e h1
  simpa using this

theorem not_components_of_cyclic_sylow [Finite X] (h : ∀ P : Sylow 2 X, IsCyclic P) :
    ¬ ((∃ L : Subgroup X, IsPComponent 2 L) ∨ HasSolvableTwoComponentSL23 X) :=
  fun hh => hh.elim (not_exists_pComponent_of_comm (quotient_comm_of_cyclic_sylow h))
    (not_hasSolvableTwoComponentSL23_of_comm (quotient_comm_of_cyclic_sylow h))

end Cyclic

end CFSG.GH74.KGroups.TwoA7
