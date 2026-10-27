module

public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralComponentLifts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Comp

variable {X Y : Type*} [Group X] [Group Y]

theorem isQuasisimple_localCores_of_open {Q : Type*} [Group Q]
    (hQ : Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem isComponentOf_map_top_of_surj (f : X →* Y) (hf : Function.Surjective f)
    {L : Subgroup X} (hL : IsComponentOf L ⊤) (hLf : ¬ L ≤ f.ker) :
    IsComponentOf (L.map f) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have h := CFSG.RankThreeCoreUniqueness.Helpers.cfsg_isSubnormal_map f hL.2.1
    rwa [Subgroup.map_top_of_surjective f hf] at h
  · have h := CFSG.LocalCores.isQuasisimple_map (isQuasisimple_localCores_of_open hL.2.2) f
      hLf
    exact ⟨h.1.commutator_eq_top, h.2.1⟩

theorem ker_restrict_le_center_of_isQuasisimple (f : X →* Y) {L : Subgroup X}
    (hL : Open.IsQuasisimple L) (hLf : ¬ L ≤ f.ker) :
    (f.comp L.subtype).ker ≤ Subgroup.center L := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_localCores_of_open hL)
    (f.comp L.subtype).normal_ker with h | h
  · exfalso
    apply hLf
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ (f.comp L.subtype).ker := h ▸ Subgroup.mem_top _
    exact this
  · exact h

end Comp

section PCore

theorem pCore_two_ne_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {V : Subgroup B} (hVn : V.Normal) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) :
    CFSG.pCore 2 A ≠ ⊥ := by
  set V' := V.comap e.toMonoidHom with hV'
  have hV'n : V'.Normal := hVn.comap _
  have hV'p : IsPGroup 2 V' := hV.comap_of_injective e.toMonoidHom e.injective
  have hle : V' ≤ CFSG.pCore 2 A := le_sSup ⟨hV'n, hV'p⟩
  intro hbot
  apply hV1
  rw [eq_bot_iff]
  intro v hv
  have h1 : e.symm v ∈ V' := by simpa [hV'] using hv
  have h2 := hle h1
  rw [hbot, Subgroup.mem_bot] at h2
  simpa using congrArg e h2

theorem not_nonempty_quotient_pCore_equiv {J B : Type*} [Group J] [Group B] {V : Subgroup B}
    (hVn : V.Normal) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) :
    ¬ Nonempty (J ⧸ CFSG.pCore 2 J ≃* B) := by
  rintro ⟨e⟩
  exact pCore_two_ne_bot_of_mulEquiv e hVn hV hV1 (pCore_quotient_pCore_eq_bot' 2)

theorem exists_normal_two_perm_four :
    ∃ V : Subgroup (Equiv.Perm (Fin 4)), V.Normal ∧ IsPGroup 2 V ∧ V ≠ ⊥ := by
  have h4 : Nat.card (Fin 4) = 4 := Nat.card_fin 4
  set V := (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype with hV
  have hcard : Nat.card V = 4 := by
    rw [hV, Subgroup.card_map_of_injective (alternatingGroup (Fin 4)).subtype_injective,
      alternatingGroup.kleinFour_card_of_card_eq_four h4]
  refine ⟨V, ⟨fun v hv g => ?_⟩, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), ?_⟩
  · obtain ⟨k, hk, rfl⟩ := hv
    have hkA : ((k : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) ∈ alternatingGroup (Fin 4) :=
      k.2
    have hcA : g * (k : Equiv.Perm (Fin 4)) * g⁻¹ ∈ alternatingGroup (Fin 4) :=
      (alternatingGroup.normal (α := Fin 4)).conj_mem _ hkA g
    have hord : orderOf (g * (k : Equiv.Perm (Fin 4)) * g⁻¹) ∣ 2 ^ 2 := by
      have hc : orderOf (g * (k : Equiv.Perm (Fin 4)) * g⁻¹) =
          orderOf (k : Equiv.Perm (Fin 4)) := by
        have := MulEquiv.orderOf_eq (MulAut.conj g) (k : Equiv.Perm (Fin 4))
        simpa [MulAut.conj_apply] using this
      rw [hc]
      have h1 : orderOf k ∣ Nat.card (alternatingGroup.kleinFour (Fin 4)) := by
        have := orderOf_dvd_natCard (⟨k, hk⟩ : alternatingGroup.kleinFour (Fin 4))
        rwa [Subgroup.orderOf_mk] at this
      rw [alternatingGroup.kleinFour_card_of_card_eq_four h4] at h1
      have h2 : orderOf (k : Equiv.Perm (Fin 4)) = orderOf k := Subgroup.orderOf_coe k
      rw [h2]
      simpa using h1
    have hct := alternatingGroup.mem_kleinFour_of_order_two_pow h4 hcA hord
    have hmem : (⟨_, hcA⟩ : alternatingGroup (Fin 4)) ∈ alternatingGroup.kleinFour (Fin 4) := by
      rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four h4]
      rcases hct with h | h
      · left
        exact Subtype.ext (Equiv.Perm.cycleType_eq_zero.mp (by simpa using h))
      · right
        exact h
    exact ⟨⟨_, hcA⟩, hmem, rfl⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard

theorem exists_normal_two_perm_two :
    ∃ V : Subgroup (Equiv.Perm (Fin 2)), V.Normal ∧ IsPGroup 2 V ∧ V ≠ ⊥ := by
  refine ⟨⊤, inferInstance, IsPGroup.of_card (n := 1) ?_, ?_⟩
  · rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]; rfl
  · intro h
    have : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 2))) = 1 := by rw [h, Subgroup.card_bot]
    rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin] at this
    norm_num at this

end PCore

theorem eq_eight_of_factorial_eq {m : ℕ} (h : m.factorial = 40320) : m = 8 := by
  rcases Nat.lt_or_ge m 9 with hm | hm
  · interval_cases m <;> simp_all [Nat.factorial]
  · have := Nat.factorial_le hm
    rw [h] at this
    norm_num [Nat.factorial] at this

theorem eq_eight_of_card_alternatingGroup {m : ℕ}
    (h : Nat.card (alternatingGroup (Fin m)) = 20160) : m = 8 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rw [alternatingGroup.eq_bot_of_card_le_two (by rw [Nat.card_fin]; omega),
      Subgroup.card_bot] at h
    norm_num at h
  · have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    rw [nat_card_alternatingGroup, Nat.card_fin] at h
    have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
    apply eq_eight_of_factorial_eq
    omega

end CFSG.AGLEmbedding
