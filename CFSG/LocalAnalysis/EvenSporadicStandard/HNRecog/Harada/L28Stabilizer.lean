module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Stab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

theorem L28_exists_stabilizer (h : L28Hyp A w ψ) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (e : ↥A ≃* Multiplicative V)
    (σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* (V ≃ₗ[ZMod 2] V))
    (hact : ∀ (n : ↥(normalizer (A : Set X)))
      (g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)),
        ψ n = A5WrTwo.baseEmb g → ∀ a : ↥A,
          ((e.symm (Multiplicative.ofAdd (σ g (Multiplicative.toAdd (e a)))) : ↥A) : X) =
            (n : X) * (a : X) * (n : X)⁻¹) :
    ∃ v : V, v ≠ 0 ∧ ∃ S : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)),
      (∀ g, g ∈ S ↔ σ g v = v) ∧ Nonempty (↥S ≃* alternatingGroup (Fin 5)) := by
  classical
  let wN : ↥(normalizer (A : Set X)) := ⟨w, Subgroup.le_normalizer h.w_mem⟩
  let C : Subgroup ↥(normalizer (A : Set X)) :=
    Subgroup.centralizer ({wN} : Set ↥(normalizer (A : Set X)))
  let St : Subgroup A5WrTwo := C.map ψ
  let S : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (St ⊓ commutator A5WrTwo).comap A5WrTwo.baseEmb
  let a0 : ↥A := ⟨w, h.w_mem⟩
  let v : V := Multiplicative.toAdd (e a0)
  have hv_ne : v ≠ 0 := by
    intro hv
    have hea : e a0 = 1 :=
      Multiplicative.toAdd.injective (by simpa [v] using hv)
    have ha0 : a0 = 1 := e.injective (by simpa using hea)
    exact h.w_ne_one (by simpa [a0] using congrArg (fun x : ↥A => (x : X)) ha0)
  refine ⟨v, hv_ne, S, ?_, ?_⟩
  ·
    have hAleC : A.subgroupOf (normalizer (A : Set X)) ≤ C := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have hc := (h.elemAb.1).is_comm.comm (⟨w, h.w_mem⟩ : ↥A)
        (⟨(x : X), Subgroup.mem_subgroupOf.mp hx⟩ : ↥A)
      simpa using congrArg (fun z : ↥A => (z : X)) hc
    intro g
    obtain ⟨n, hn⟩ := h.surj (A5WrTwo.baseEmb g)
    have hrange : A5WrTwo.baseEmb g ∈ commutator A5WrTwo := by
      rw [← A5WrTwo.range_baseEmb]
      exact ⟨g, rfl⟩
    have hmemS : g ∈ S ↔ A5WrTwo.baseEmb g ∈ St := by
      change g ∈ (St ⊓ commutator A5WrTwo).comap A5WrTwo.baseEmb ↔
        A5WrTwo.baseEmb g ∈ St
      rw [Subgroup.mem_comap]
      exact ⟨fun hg => hg.1, fun hg => ⟨hg, hrange⟩⟩
    have hmemC_iff : n ∈ C ↔ (n : X) * w * (n : X)⁻¹ = w := by
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro hc
        have hw : wN * n = n * wN := hc wN (by simp)
        have hval : (w : X) * (n : X) = (n : X) * (w : X) := by
          have := congrArg (fun x : ↥(normalizer (A : Set X)) => (x : X)) hw
          simpa using this
        rw [← hval]
        group
      · intro hnw
        intro x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hcomm : (n : X) * w = w * (n : X) :=
          (mul_inv_eq_iff_eq_mul).mp hnw
        exact hcomm.symm
    have hbaseSt : A5WrTwo.baseEmb g ∈ St ↔ n ∈ C := by
      change A5WrTwo.baseEmb g ∈ C.map ψ ↔ n ∈ C
      constructor
      · intro hb
        obtain ⟨m, hmC, hm⟩ := Subgroup.mem_map.mp hb
        have hker : n * m⁻¹ ∈ ψ.ker := by
          rw [MonoidHom.mem_ker]
          simp [map_mul, map_inv, hn, hm]
        have hmemA : (n * m⁻¹ : ↥(normalizer (A : Set X))) ∈
            A.subgroupOf (normalizer (A : Set X)) := h.ker ▸ hker
        have hprod : (n * m⁻¹) * m ∈ C := C.mul_mem (hAleC hmemA) hmC
        simpa [mul_assoc] using hprod
      · intro hnC
        exact Subgroup.mem_map.mpr ⟨n, hnC, hn⟩
    have hsigma : σ g v = v ↔ (n : X) * w * (n : X)⁻¹ = w := by
      have hact' : ((e.symm (Multiplicative.ofAdd (σ g v)) : ↥A) : X) =
          (n : X) * w * (n : X)⁻¹ := by
        simpa [v, a0] using hact n g hn a0
      have hev : e.symm (Multiplicative.ofAdd v) = a0 := by
        simp [v]
      constructor
      · intro hσ
        have hEq : (e.symm (Multiplicative.ofAdd (σ g v)) : ↥A) = a0 := by
          rw [hσ, hev]
        have hval := congrArg (fun x : ↥A => (x : X)) hEq
        rw [hact'] at hval
        simpa [a0] using hval
      · intro hnw
        have hinj : Function.Injective
            (fun x : V => e.symm (Multiplicative.ofAdd x)) :=
          e.symm.injective.comp Multiplicative.ofAdd.injective
        apply hinj
        apply Subtype.ext
        simp [hact', hnw, hev, a0]
    rw [hmemS, hbaseSt, hmemC_iff]
    exact hsigma.symm
  ·
    have hSmap : S.map A5WrTwo.baseEmb = St ⊓ commutator A5WrTwo := by
      change (Subgroup.comap A5WrTwo.baseEmb (St ⊓ commutator A5WrTwo)).map
        A5WrTwo.baseEmb = St ⊓ commutator A5WrTwo
      rw [Subgroup.map_comap_eq, A5WrTwo.range_baseEmb]
      exact le_antisymm inf_le_right (le_inf inf_le_right le_rfl)
    have hSt : Nonempty (↥St ≃* Equiv.Perm (Fin 5)) := h.stab
    obtain ⟨eSt⟩ := hSt
    obtain ⟨eInf⟩ := L28_nonempty_equiv_inf_base (S := St) eSt
    exact ⟨(Subgroup.equivMapOfInjective S A5WrTwo.baseEmb
      A5WrTwo.baseEmb_injective).trans ((MulEquiv.subgroupCongr hSmap).trans eInf)⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
