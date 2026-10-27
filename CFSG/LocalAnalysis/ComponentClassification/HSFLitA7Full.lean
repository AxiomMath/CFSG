module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Skeleton
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Section3

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem Config.exists_mulEquiv_of_action (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (ψ : normalizer (L : Set X) →* Perm (Fin 7))
    (hker : ∀ g, ψ g = 1 ↔ (g : X) ∈ coreActionKernel L)
    (hL : ∀ g : normalizer (L : Set X), (g : X) ∈ L → ψ g ∈ alternatingGroup (Fin 7)) :
    ∃ e' : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7),
      ∀ l : L, ψ ⟨l, Subgroup.le_normalizer l.2⟩ = (e' (QuotientGroup.mk l) : Perm (Fin 7)) := by
  classical
  set f : L →* alternatingGroup (Fin 7) :=
    { toFun := fun l => ⟨ψ ⟨l, Subgroup.le_normalizer l.2⟩, hL _ l.2⟩
      map_one' := Subtype.ext (by
        change ψ ⟨1, _⟩ = 1
        exact map_one ψ)
      map_mul' := fun a b => Subtype.ext (by
        change ψ ⟨a * b, _⟩ = ψ ⟨a, _⟩ * ψ ⟨b, _⟩
        rw [← map_mul]
        rfl) } with hf
  have hfapp : ∀ l : L, (f l : Perm (Fin 7)) = ψ ⟨l, Subgroup.le_normalizer l.2⟩ := fun _ => rfl
  have hfker : f.ker = pPrimeCore 2 L := by
    ext l
    rw [MonoidHom.mem_ker]
    constructor
    · intro hl
      have h1 : ψ ⟨l, Subgroup.le_normalizer l.2⟩ = 1 := by
        rw [← hfapp, hl]
        rfl
      have hC : (l : X) ∈ coreActionKernel L := (hker _).mp h1
      have := h.inf_kernel_le_oddCore ⟨l.2, hC⟩
      obtain ⟨l', hl', hll'⟩ := this
      have : l' = l := Subtype.ext hll'
      rw [← this]
      exact hl'
    · intro hl
      apply Subtype.ext
      have h1 : ψ ⟨l, Subgroup.le_normalizer l.2⟩ = 1 := by
        rw [hker]
        refine ⟨Subgroup.le_normalizer l.2, fun j hj => ?_⟩
        refine ⟨(⟨j, hj⟩ : L)⁻¹ * l⁻¹ * ⟨j, hj⟩ * l, ?_, by simp⟩
        have hn : (pPrimeCore 2 L).Normal := inferInstance
        have h2 : (⟨j, hj⟩ : L)⁻¹ * l⁻¹ * ⟨j, hj⟩ ∈ pPrimeCore 2 L := by
          have := hn.conj_mem _ (inv_mem hl) (⟨j, hj⟩ : L)⁻¹
          simpa [mul_assoc] using this
        exact mul_mem h2 hl
      rw [hfapp, h1]
      rfl
  have hcardL : Nat.card (L ⧸ pPrimeCore 2 L) = Nat.card (alternatingGroup (Fin 7)) :=
    Nat.card_congr e.toEquiv
  have hsurj : Function.Surjective f := by
    have hinj : Function.Injective (QuotientGroup.kerLift f) := QuotientGroup.kerLift_injective f
    have hcard : Nat.card (L ⧸ f.ker) = Nat.card (alternatingGroup (Fin 7)) := by
      rw [← hcardL, hfker]
    have hbij := hinj.bijective_of_nat_card_le hcard.ge
    intro a
    obtain ⟨q, hq⟩ := hbij.2 a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, by simpa using hq⟩
  set e₀ := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  set e' := (QuotientGroup.quotientMulEquivOfEq hfker).symm.trans e₀ with he'
  refine ⟨e', fun l => ?_⟩
  have h1 : e' (QuotientGroup.mk l) = f l := by
    rw [he', MulEquiv.trans_apply]
    rfl
  rw [h1, hfapp]

theorem Config.exists_a7Base (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) (hH : HaradaInput)
    (hnot : ¬ SectRank4 X) : ∃ S : A7Base X, S.t = t ∧ S.L = L := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(centralizer ({t} : Set X))) := inferInstance
  have hex := h.exists_good_action e T
  set A := h.a7Data e T with hA
  set Ψ := Classical.choose hex with hΨ
  have hspec := Classical.choose_spec hex
  obtain ⟨e', he'⟩ := h.exists_mulEquiv_of_action e Ψ hspec.1 hspec.2.1
  obtain ⟨hK, k, hk, hk2, hψk⟩ := A.exists_involution_c0 e hH hnot
  exact ⟨⟨t, L, A, hK, k, hk, hk2, hψk, Or.inr ⟨⟨e', Ψ, hspec.1, he', fun _ => rfl⟩⟩⟩, rfl, rfl⟩

end CFSG.ComponentClassification.HSFLit
