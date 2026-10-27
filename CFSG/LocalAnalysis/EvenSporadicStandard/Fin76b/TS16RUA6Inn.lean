module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6

public section

namespace CFSG.EvenSporadicStandard.Fin76b.A6X

theorem fixed_of_comm_conj {γ : MulAut (alternatingGroup (Fin 6))} {a : alternatingGroup (Fin 6)}
    (h : γ * MulAut.conj a = MulAut.conj a * γ) : γ a = a := by
  apply CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
  refine MulEquiv.ext fun x => ?_
  have hx := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ ((MulEquiv.symm γ) x)) h
  simpa [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] using hx

theorem inn_unique {H : Subgroup (MulAut (alternatingGroup (Fin 6)))}
    (e : ↥H ≃* alternatingGroup (Fin 6)) :
    H = (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    CFSG.EvenSporadicStandard.M24Std.DRes.alt6_simple
  haveI hHsimple : IsSimpleGroup ↥H := e.isSimpleGroup
  have hIcard : Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin 6))) = 360 :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_card
  have hIidx : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin 6))).index = 4 :=
    CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6
  have hHcard : Nat.card ↥H = 360 := by
    rw [Nat.card_congr e.toEquiv, CFSG.EvenSporadicStandard.M24Std.DRes.card_alt6]
  have hquot : Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸
      CFSG.ComponentClassification.OuterAutomorphisms.inner (alternatingGroup (Fin 6))) = 4 :=
    hIidx
  haveI : Finite (MulAut (alternatingGroup (Fin 6)) ⧸
      CFSG.ComponentClassification.OuterAutomorphisms.inner (alternatingGroup (Fin 6))) :=
    Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin 6))) :=
    Nat.finite_of_card_ne_zero (by omega)
  let φ : ↥H →* MulAut (alternatingGroup (Fin 6)) ⧸
      CFSG.ComponentClassification.OuterAutomorphisms.inner (alternatingGroup (Fin 6)) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin 6)))).comp H.subtype
  have hle : H ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin 6)) := by
    rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with hbot | htop
    · exfalso
      have hinj : Function.Injective (⇑φ) := (MonoidHom.ker_eq_bot_iff φ).mp hbot
      have hle' := Nat.card_le_card_of_injective (⇑φ) hinj
      omega
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥H) ∈ φ.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner
        (alternatingGroup (Fin 6))) x).mp (MonoidHom.mem_ker.mp hmem)
  have hcardle : Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin 6))) ≤ Nat.card ↥H := by omega
  exact Subgroup.eq_of_le_of_card_ge hle hcardle

theorem cent_inn {γ : MulAut (alternatingGroup (Fin 6))}
    (h : ∀ a : alternatingGroup (Fin 6), γ * MulAut.conj a = MulAut.conj a * γ) : γ = 1 := by
  refine MulEquiv.ext fun x => ?_
  exact fixed_of_comm_conj (h x)

theorem cent_A6' {H : Subgroup (MulAut (alternatingGroup (Fin 6)))}
    (e : ↥H ≃* alternatingGroup (Fin 6)) {γ : MulAut (alternatingGroup (Fin 6))}
    (h : ∀ x ∈ H, γ * x = x * γ) : γ = 1 := by
  refine cent_inn fun a => h _ ?_
  rw [inn_unique e]
  exact MonoidHom.mem_range.mpr ⟨a, rfl⟩

end CFSG.EvenSporadicStandard.Fin76b.A6X
