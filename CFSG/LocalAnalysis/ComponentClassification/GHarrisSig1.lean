module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo
public import CFSG.GroupTheory.PCore.CommutingBalance

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem

variable {G : Type} [Group G]

@[expose] def oddCent (S : Subgroup G) : Subgroup G :=
  (pPrimeCore 2 (centralizer (S : Set G))).map (centralizer (S : Set G)).subtype

theorem oddCent_le (S : Subgroup G) : oddCent S ≤ centralizer (S : Set G) := map_subtype_le _

theorem card_oddCent [Finite G] (S : Subgroup G) : Nat.Coprime 2 (Nat.card (oddCent S)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCent, card_map_of_injective (centralizer (S : Set G)).subtype_injective]
  exact pPrimeCore_coprime_card

theorem centralizer_le_normalizer_oddCent (S : Subgroup G) :
    centralizer (S : Set G) ≤ normalizer (oddCent S : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro w
  have hn := (pPrimeCore_normal : (pPrimeCore 2 (centralizer (S : Set G))).Normal)
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨c, hc⟩ * u * ⟨c, hc⟩⁻¹, hn.conj_mem u hu ⟨c, hc⟩, rfl⟩
  · rintro ⟨u, hu, hu'⟩
    refine ⟨⟨c, hc⟩⁻¹ * u * ⟨c, hc⟩, by simpa using hn.conj_mem u hu ⟨c, hc⟩⁻¹, ?_⟩
    change c⁻¹ * (u : G) * c = w
    rw [show (u : G) = c * w * c⁻¹ from hu']
    group

theorem centralizer_map_equiv (φ : G ≃* G) (S : Subgroup G) :
    centralizer ((S.map φ.toMonoidHom : Subgroup G) : Set G) =
      (centralizer (S : Set G)).map φ.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro s hs
    have h := mem_centralizer_iff.mp hy (φ s) ⟨s, hs, rfl⟩
    apply φ.injective
    simpa using h
  · rintro ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    change φ s * φ c = φ c * φ s
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc s hs]

theorem oddCent_map (φ : G ≃* G) (S : Subgroup G) :
    oddCent (S.map φ.toMonoidHom) = (oddCent S).map φ.toMonoidHom := by
  have hC := centralizer_map_equiv φ S
  let e : centralizer (S : Set G) ≃* centralizer ((S.map φ.toMonoidHom : Subgroup G) : Set G) :=
    (φ.subgroupMap _).trans (MulEquiv.subgroupCongr hC.symm)
  have he := pPrimeCore_map_iso 2 e
  unfold oddCent
  rw [← he, map_map, map_map]
  rfl

abbrev CharTwoCent (S : Subgroup G) : Prop :=
  IsCharacteristicP 2 (centralizer (S : Set G) ⧸ pPrimeCore 2 (centralizer (S : Set G)))

abbrev CharTwoAt (A : Subgroup G) : Prop :=
  ∀ S ∈ signalizerFunctorEk 2 1 A, CharTwoCent S

@[expose] def sigW (A : Subgroup G) : Subgroup G :=
  ⨆ (S : Subgroup G) (_ : S ∈ signalizerFunctorEk 2 1 A), oddCent S

theorem oddCent_le_sigW {A S : Subgroup G} (hS : S ∈ signalizerFunctorEk 2 1 A) :
    oddCent S ≤ sigW A :=
  le_iSup₂ (f := fun S (_ : S ∈ signalizerFunctorEk 2 1 A) => oddCent S) S hS

theorem mcBrideB_of_odd [Finite G] {H : Subgroup G} (hH : Nat.Coprime 2 (Nat.card H)) :
    signalizerMcBrideHypothesisB 2 H := by
  refine ⟨Nat.prime_two, hH, fun K L hKH hLK _ hsimple hnc => ?_⟩
  exfalso
  have hK : Group.IsSolvable K := isSolvable_of_coprime_two K
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le hKH) hH)
  have : Group.IsSolvable (K ⧸ L.subgroupOf K) := inferInstance
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

variable [Finite G]

theorem sigW_spec {A : Subgroup G} (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A)
    (hch : CharTwoAt A) :
    (Nat.Coprime 2 (Nat.card (sigW A)) ∧ A ≤ normalizer (sigW A : Set G)) ∧
      ∀ S ∈ signalizerFunctorEk 2 1 A, sigW A ⊓ centralizer (S : Set G) = oddCent S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h2 : ∀ S ∈ signalizerFunctorEk 2 1 A, IsPGroup 2 S := fun S hS =>
    IsPGroup.of_card (n := 1) (by rw [hS.2])
  have hAS : ∀ S ∈ signalizerFunctorEk 2 1 A, A ≤ centralizer (S : Set G) :=
    fun S hS a ha => mem_centralizer_iff.mpr fun s hs => (hAc a ha s (hS.1 hs)).symm
  have hspec := signalizer_functor_theorem_two G 1 le_rfl A hA (by simpa using h8) oddCent
    (fun S _ => oddCent_le S) (fun S _ => card_oddCent S)
    (fun S hS => (hAS S hS).trans (centralizer_le_normalizer_oddCent S))
    (fun S hS S' hS' => by
      have hcomm : ⁅S, S'⁆ = ⊥ := by
        rw [commutator_eq_bot_iff_le_centralizer]
        intro s hs
        exact mem_centralizer_iff.mpr fun s' hs' => hAc s' (hS'.1 hs') s (hS.1 hs)
      have hb := (pPrimeCore_commuting_centralizers_balance G 2 S S' (h2 S hS) (h2 S' hS')
        hcomm (hch S hS) (hch S' hS')).1.trans
        (pPrimeCore_commuting_centralizers_balance G 2 S S' (h2 S hS) (h2 S' hS') hcomm
          (hch S hS) (hch S' hS')).2
      change oddCent S ⊓ centralizer (S' : Set G) ≤ oddCent S'
      rw [oddCent, hb]
      exact inf_le_left)
    (fun S _ => mcBrideB_of_odd (card_oddCent S))
  exact ⟨hspec.1, hspec.2.1⟩

end CFSG.ComponentClassification.GHarris
