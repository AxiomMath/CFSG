module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusHas

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail LeviBlock

@[expose] def IdxTwistedDExcept (c : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedD _ q => q.p = 2 ∧ q.card ≠ c
  | _ => False

@[expose] def IdxTwistedDAt (c : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedD _ q => q.p = 2 ∧ q.card = c
  | _ => False

theorem idxTwistedD_of_except {c : ℕ} {d : TauCeti.LieTypeIndex} (hd : IdxTwistedDExcept c d) :
    IdxTwistedD d := by
  cases d with
  | twistedD r₀ q => exact hd.1
  | _ => exact hd.elim

theorem isLieOf_twistedD_cases (c : ℕ) {X : Type} [Group X] (hX : IsLieOf IdxTwistedD X) :
    IsLieOf (IdxTwistedDExcept c) X ∨ IsLieOf (IdxTwistedDAt c) X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := hX
  cases d with
  | twistedD r₀ q =>
    by_cases hq : q.card = c
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, hq⟩, he⟩
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, hq⟩, he⟩
  | _ => exact hd.elim

theorem LeviBlock.orthMinus_card_eq_two_pow {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem LeviBlock.exists_hasLeviBlocks_of_twistedD (hZ : OddCenterRest) {Y : Type} [Group Y]
    [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P) (dI : TauCeti.ValidLieTypeIndex)
    (hdI : IdxTwistedD dI.1) (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie dI).Group) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (f : ℕ),
      Function.Surjective ρ ∧ HasLeviBlocks ↥((P.subgroupOf L).comap ρ)
        (orthMinusBlockOrders (2 ^ f)) ∧ ∀ n q, dI.1 = .twistedD n q → q.card = 2 ^ f := by
  obtain ⟨K, _, _, _, b, c, r, s, d, ρ, hr, hirr, hcuts, hρ, hq⟩ :=
    exists_orthCover_of_twistedD hZ hCP dI hdI e
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  obtain ⟨f, hK⟩ := LeviBlock.orthMinus_card_eq_two_pow (K := K)
  refine ⟨_, inferInstance, inferInstance, ρ.toMonoidHom, f, ρ.surjective, ?_,
    fun n q h => (hq n q h).symm.trans hK⟩
  rw [hρ, ← hK]
  exact hasLeviBlocks_orthParab hcuts hr hirr

theorem kFactCompParabSU38On_twistedD (hZ : OddCenterRest) :
    KFactCompParabSU38On (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP ⟨dI, hdI, ⟨e⟩⟩
  obtain ⟨K, _, _, ρ, f, hρ, hQ, -⟩ := LeviBlock.exists_hasLeviBlocks_of_twistedD hZ hCP dI hdI e
  exact su38At_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ, _, hρ, hQ,
    u38_not_mem_orthMinusBlockOrders⟩

theorem kFactCompParabLeviU42On_twistedD (hZ : OddCenterRest) :
    KFactCompParabLeviU42On (IsLieOf (IdxTwistedDExcept 2)) := by
  intro Y _ _ L P hCP ⟨dI, hdI, ⟨e⟩⟩
  obtain ⟨K, _, _, ρ, f, hρ, hQ, hq⟩ :=
    LeviBlock.exists_hasLeviBlocks_of_twistedD hZ hCP dI (idxTwistedD_of_except hdI) e
  have hne : 2 ^ f ≠ 2 := by
    obtain ⟨dI, hv⟩ := dI
    cases dI with
    | twistedD r₀ q => exact (hq r₀ q rfl) ▸ hdI.2
    | _ => exact hdI.elim
  exact leviU42At_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ, _, hρ, hQ,
    u42_not_mem_orthMinusBlockOrders hne⟩

theorem kFactCompParabLeviU42On_twistedD_of_two (hZ : OddCenterRest)
    (h2 : KFactCompParabLeviU42On (IsLieOf (IdxTwistedDAt 2))) :
    KFactCompParabLeviU42On (IsLieOf IdxTwistedD) := fun Y _ _ L P hCP hD =>
  (isLieOf_twistedD_cases 2 hD).elim (kFactCompParabLeviU42On_twistedD hZ Y L P hCP)
    (h2 Y L P hCP)

end CFSG.AGLEmbedding
