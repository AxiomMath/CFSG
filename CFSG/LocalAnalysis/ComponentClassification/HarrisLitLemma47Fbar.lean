module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma44a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Lemma47

theorem isPGroup_quot_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hA : IsPGroup 2 (A ⧸ pPrimeCore 2 A)) :
    IsPGroup 2 (B ⧸ pPrimeCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨k, hk⟩ := hA (QuotientGroup.mk a)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk ⊢
  rw [← map_pow]
  exact map_pPrimeCore_le f hf ⟨_, hk, rfl⟩

theorem fbar_component {X : Type} [Group X] [Finite X] {z t : X}
    (htz : t ∈ centralizer ({z} : Set X)) (ht : orderOf t = 2)
    (hC : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {z}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {z})))
    {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer {z}))
    (hKt : K.map (MulAut.conj t).toMonoidHom = K) :
    IsComponent ((K.subgroupOf (centralizer {z})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))) ∧
      Nonempty (↥((K.subgroupOf (centralizer {z})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))) ≃*
        ↥K ⧸ pPrimeCore 2 ↥K) ∧
      (QuotientGroup.mk ⟨t, htz⟩ : MBar z) ∈ normalizer
        (((K.subgroupOf (centralizer {z})).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))) : Set (MBar z)) ∧
      IsPGroup 2 (↥(((K.subgroupOf (centralizer {z})).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))) ⊓
            centralizer {(QuotientGroup.mk ⟨t, htz⟩ : MBar z)}) ⧸
        pPrimeCore 2 ↥(((K.subgroupOf (centralizer {z})).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X))))) ⊓
            centralizer {(QuotientGroup.mk ⟨t, htz⟩ : MBar z)})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := centralizer ({z} : Set X) with hF
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥F) with hπ
  have hO : pPrimeCore 2 (MBar z) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  obtain ⟨hbij, -, hiso⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    π (QuotientGroup.mk'_surjective _) (GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥F))
  have hKp : IsPComponent 2 (K.subgroupOf F) := (isTwoComponentIn_iff hK.1).mp hK
  have hKbp : IsPComponent 2 ((K.subgroupOf F).map π) := hbij.mapsTo hKp
  have hKbc : IsComponent ((K.subgroupOf F).map π) :=
    (isTwoComponent_iff_isComponent hO _).mp ((isTwoComponent_iff_isPComponent _).mpr hKbp)
  refine ⟨hKbc, ?_, ?_, ?_⟩
  · obtain ⟨e, -⟩ := hiso _ hKp
    have hOb : pPrimeCore 2 ↥((K.subgroupOf F).map π) = ⊥ :=
      pPrimeCore_eq_bot_of_isSubnormal hO hKbc.2
    have e₁ : ↥((K.subgroupOf F).map π) ≃*
        ↥((K.subgroupOf F).map π) ⧸ pPrimeCore 2 ↥((K.subgroupOf F).map π) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOb.symm)
    have e₂ : ↥(K.subgroupOf F) ⧸ pPrimeCore 2 ↥(K.subgroupOf F) ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
      QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1)
        (pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hK.1))
    exact ⟨e₁.trans (e.symm.trans e₂)⟩
  · rw [mem_normalizer_iff]
    have hKt' : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk => by
      rw [← hKt]
      exact ⟨k, hk, rfl⟩
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by rw [← sq, ← ht, pow_orderOf_eq_one])
    have hKt'' : ∀ k ∈ K, t⁻¹ * k * t ∈ K := fun k hk => by
      have h1 := hKt' k hk
      rw [htinv]
      rw [htinv] at h1
      exact h1
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    constructor
    · rintro ⟨k, hk, hky⟩
      refine ⟨⟨t, htz⟩ * k * ⟨t, htz⟩⁻¹, ?_, ?_⟩
      · exact hKt' k hk
      · rw [map_mul, map_mul, map_inv, hky]
        rfl
    · rintro ⟨k, hk, hky⟩
      refine ⟨⟨t, htz⟩⁻¹ * k * ⟨t, htz⟩, ?_, ?_⟩
      · exact hKt'' k hk
      · rw [map_mul, map_mul, map_inv, hky]
        change (QuotientGroup.mk ⟨t, htz⟩ : MBar z)⁻¹ *
          ((QuotientGroup.mk ⟨t, htz⟩ : MBar z) * QuotientGroup.mk y *
            (QuotientGroup.mk ⟨t, htz⟩ : MBar z)⁻¹) * QuotientGroup.mk ⟨t, htz⟩ = QuotientGroup.mk y
        group
  ·
    set t' : ↥F := ⟨t, htz⟩
    have ht'2 : t' * t' = 1 := Subtype.ext (by
      change t * t = 1
      rw [← sq, ← ht, pow_orderOf_eq_one])
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥F)) := by
      have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥F)
      rw [QuotientGroup.ker_mk'] at h2
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    have hCmap : (centralizer ({t'} : Set ↥F)).map π = centralizer {π t'} :=
      map_centralizer_eq hodd ht'2
    have e : ↥(centralizer ({t'} : Set ↥F)) ≃* ↥(centralizer ({t} : Set X) ⊓ centralizer {z}) :=
      (equivMapOfInjective _ F.subtype F.subtype_injective).trans
        (MulEquiv.subgroupCongr (map_subtype_centralizer htz))
    have hC' := isPGroup_quot_of_mulEquiv e.symm hC
    let g : ↥(centralizer ({t'} : Set ↥F)) →* ↥(centralizer ({π t'} : Set (MBar z))) :=
      (π.comp (centralizer ({t'} : Set ↥F)).subtype).codRestrict _
        (fun x => hCmap ▸ mem_map_of_mem π x.2)
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      rw [← hCmap] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hCb := isPGroup_quot_of_surjective g hg hC'
    have hle : ((K.subgroupOf F).map π) ⊓ centralizer {π t'} ≤ centralizer {π t'} :=
      inf_le_right
    exact isPGroup_quot_of_le hle hCb

end Lemma47

end CFSG.ComponentClassification.HarrisLit
