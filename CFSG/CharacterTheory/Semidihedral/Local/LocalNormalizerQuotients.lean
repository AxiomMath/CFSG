module

public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotientsSupport
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_image_inf_normalizer_mul (S : Sylow 2 G) (T : Subgroup G) (hTS : T ≤ S)
    (hSC : (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) ≤ T) :
    Nat.card ((((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
        (Subgroup.normalizer (T : Set G))).map T.normalizerMonoidHom) *
      Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) =
      Nat.card ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) := by
  have hCN := Subgroup.centralizer_le_normalizer (T : Set G)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (T.normalizerMonoidHom.domRestrict (((S : Subgroup G) ⊓
      Subgroup.normalizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)))).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, Subgroup.normalizerMonoidHom_ker,
    card_subgroupOf_eq, card_subgroupOf_eq, inf_assoc, inf_idem] at h1
  have hinter : (Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)) ⊓
      ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
        (Subgroup.normalizer (T : Set G)) =
      (T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hxC, hxS, -⟩
      exact ⟨hSC ⟨hxS, hxC⟩, hxC⟩
    · rintro ⟨hxT, hxC⟩
      exact ⟨hxC, hTS hxT, x.2⟩
  rw [hinter, card_subgroupOf_eq, inf_eq_left.mpr (inf_le_right.trans hCN)] at h1
  exact h1.symm

theorem card_quotient_oddCore_eq (T : Subgroup G)
    (hcardC : Nat.card (Subgroup.centralizer (T : Set G)) =
      Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) *
        Nat.card ((CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
          (Subgroup.normalizer (T : Set G)).subtype)) :
    Nat.card (Subgroup.normalizer (T : Set G) ⧸ CFSG.oddCore (Subgroup.normalizer (T : Set G))) =
      Nat.card T.normalizerMonoidHom.range *
        Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := by
  have hCN := Subgroup.centralizer_le_normalizer (T : Set G)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.oddCore (Subgroup.normalizer (T : Set G)))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup T.normalizerMonoidHom.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    Subgroup.normalizerMonoidHom_ker, card_subgroupOf_eq, inf_eq_left.mpr hCN, hcardC] at h2
  rw [← Subgroup.card_map_of_injective (Subgroup.normalizer (T : Set G)).subtype_injective] at h1
  have hpos : 0 < Nat.card ((CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h1, h2, mul_assoc]

theorem four_and_quaternion_eight_local_normalizer_quotients (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) (T : Subgroup G) (hTS : T ≤ S)
    (hT : IsKleinFour T ∨ Nonempty (T ≃* QuaternionGroup 2)) :
    let N := Subgroup.normalizer (T : Set G)
    let C := Subgroup.centralizer (T : Set G)
    let R := (S : Subgroup G) ⊓ N
    let K := (CFSG.oddCore N).map N.subtype
    let Z := (Subgroup.center T).map T.subtype
    let AutG := T.normalizerMonoidHom.range
    let AutS := (R.subgroupOf N).map T.normalizerMonoidHom
    (∃ P : Sylow 2 N, (P : Subgroup N) = R.subgroupOf N) ∧
    Z ⊔ K = C ∧ Z ⊓ K = ⊥ ∧ (∀ a ∈ Z, ∀ k ∈ K, Commute a k) ∧ K ⊓ T = ⊥ ∧
    T.normalizerMonoidHom.ker = C.subgroupOf N ∧
    Nonempty (N ⧸ T.normalizerMonoidHom.ker ≃* AutG) ∧
    (IsKleinFour T →
      Nonempty (R ≃* DihedralGroup 4) ∧ Nat.card R = 8 ∧ Nat.card AutS = 2 ∧
      ((AutG = AutS ∧ Nat.card (N ⧸ CFSG.oddCore N) = 8) ∨
        (AutG = ⊤ ∧ Nat.card (N ⧸ CFSG.oddCore N) = 24))) ∧
    (Nonempty (T ≃* QuaternionGroup 2) →
      Nat.card R = 16 ∧ Nat.card AutS = 8 ∧
      ((AutG = AutS ∧ Nat.card (N ⧸ CFSG.oddCore N) = 16) ∨
        (AutG = ⊤ ∧ Nat.card (N ⧸ CFSG.oddCore N) = 48)) ∧
      (n = 4 → Nonempty (R ≃* SemidihedralGroup 4)) ∧
      (5 ≤ n → Nonempty (R ≃* QuaternionGroup 4))) := by
  intro N C R K Z AutG AutS
  have hT2 : IsPGroup 2 T := S.isPGroup'.to_le hTS
  have hZ : (Subgroup.center T).map T.subtype = T ⊓ Subgroup.centralizer (T : Set G) :=
    center_map_subtype_eq T
  obtain ⟨r₀, zc, hr₀, hSC, hzc, hz2, hnorm⟩ : ∃ r₀ zc : ℕ,
      Nat.card ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) = r₀ ∧
      (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) ≤ T ∧
      Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) = zc ∧ 2 ∣ zc ∧
      (∀ g : G, T.map (MulAut.conj g).toMonoidHom ≤ S →
        Nat.card ((S : Subgroup G) ⊓ Subgroup.normalizer
          ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) : Subgroup G) = r₀) := by
    rcases hT with hK | hQ
    · obtain ⟨-, h8, hSC⟩ := kleinFour_sylow_facts hn S f T hTS
      refine ⟨8, 4, h8, hSC, ?_, ⟨2, rfl⟩, fun g hg => ?_⟩
      · have hTC : T ≤ Subgroup.centralizer (T : Set G) := fun a ha =>
          Subgroup.mem_centralizer_iff.mpr fun b hb => kleinFour_mul_comm T hb ha
        rw [inf_eq_left.mpr hTC, IsKleinFour.card_four]
      · have : IsKleinFour (T.map (MulAut.conj g).toMonoidHom) :=
          isKleinFour_of_mulEquiv (T.equivMapOfInjective _ (MulAut.conj g).injective)
        exact (kleinFour_sylow_facts hn S f _ hg).2.1
    · obtain ⟨eQ⟩ := hQ
      obtain ⟨h16, hSC, -⟩ := quaternionEight_sylow_facts hn S f T hTS ⟨eQ⟩
      refine ⟨16, 2, h16, hSC, ?_, dvd_refl 2, fun g hg => ?_⟩
      · rw [← hZ, Subgroup.card_map_of_injective T.subtype_injective, card_center_of_equiv eQ]
      · exact (quaternionEight_sylow_facts hn S f _ hg
          ⟨(T.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans eQ⟩).1
  have hRsyl := sylow_inf_normalizer S T hT2 fun g hg => ((hnorm g hg).trans hr₀.symm).le
  have hodd := odd_index_inf_centralizer S T hTS hSC (hzc ▸ hz2) hRsyl
  obtain ⟨hsup, hinf, hcardC, hKT⟩ := center_oddCore_complement T hT2 hodd
  have hAutS : Nat.card AutS * zc = r₀ := by
    rw [← hzc, ← hr₀]
    exact card_image_inf_normalizer_mul S T hTS hSC
  have hNK : Nat.card (N ⧸ CFSG.oddCore N) = Nat.card AutG * zc := by
    rw [← hzc]
    exact card_quotient_oddCore_eq T hcardC
  have hAutSG : AutS ≤ AutG := by
    change (((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G))).map T.normalizerMonoidHom ≤ T.normalizerMonoidHom.range
    rw [MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  have hcommon : (∃ P : Sylow 2 N, (P : Subgroup N) = R.subgroupOf N) ∧
      Z ⊔ K = C ∧ Z ⊓ K = ⊥ ∧ (∀ a ∈ Z, ∀ k ∈ K, Commute a k) ∧ K ⊓ T = ⊥ ∧
      T.normalizerMonoidHom.ker = C.subgroupOf N ∧
      Nonempty (N ⧸ T.normalizerMonoidHom.ker ≃* AutG) := by
    refine ⟨hRsyl, ?_, ?_, ?_, hKT, Subgroup.normalizerMonoidHom_ker T,
      ⟨QuotientGroup.quotientKerEquivRange _⟩⟩
    · change (Subgroup.center T).map T.subtype ⊔ _ = _
      rw [hZ]
      exact hsup
    · change (Subgroup.center T).map T.subtype ⊓ _ = _
      rw [hZ]
      exact hinf
    · intro a ha k hk
      have haT : a ∈ T := by
        change a ∈ (Subgroup.center T).map T.subtype at ha
        rw [hZ] at ha
        exact ha.1
      have hkC : k ∈ Subgroup.centralizer (T : Set G) := hsup ▸ Subgroup.mem_sup_right hk
      exact Subgroup.mem_centralizer_iff.mp hkC a haT
  refine ⟨hcommon.1, hcommon.2.1, hcommon.2.2.1, hcommon.2.2.2.1, hcommon.2.2.2.2.1,
    hcommon.2.2.2.2.2.1, hcommon.2.2.2.2.2.2, fun hK => ?_, fun hQ => ?_⟩
  ·
    obtain ⟨hD8, h8, -⟩ := kleinFour_sylow_facts hn S f T hTS
    have h8' : r₀ = 8 := hr₀.symm.trans h8
    have h4 : zc = 4 := by
      rw [← hzc]
      have hTC : T ≤ Subgroup.centralizer (T : Set G) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb => kleinFour_mul_comm T hb ha
      rw [inf_eq_left.mpr hTC, IsKleinFour.card_four]
    rw [h8', h4] at hAutS
    rw [h4] at hNK
    have hS2 : Nat.card AutS = 2 := by omega
    obtain ⟨-, hAut6, -, halt⟩ := kleinFour_automorphism_action (V := T)
    refine ⟨hD8, h8, hS2, ?_⟩
    rcases halt AutG AutS hAutSG hS2 with h2 | htop
    · refine Or.inl ⟨(Subgroup.eq_of_le_of_card_ge hAutSG (by rw [h2, hS2])).symm, ?_⟩
      rw [hNK, h2]
    · refine Or.inr ⟨htop, ?_⟩
      rw [hNK, htop, Subgroup.card_top, hAut6]
  ·
    obtain ⟨h16, -, hSD, hQ16⟩ := quaternionEight_sylow_facts hn S f T hTS hQ
    have h16' : r₀ = 16 := hr₀.symm.trans h16
    obtain ⟨eQ⟩ := hQ
    have h2 : zc = 2 := by
      rw [← hzc, ← hZ, Subgroup.card_map_of_injective T.subtype_injective,
        card_center_of_equiv eQ]
    rw [h16', h2] at hAutS
    rw [h2] at hNK
    have hS8 : Nat.card AutS = 8 := by omega
    obtain ⟨-, hAut24, -, -, -, -, -, halt⟩ := quaternionEight_automorphism_action ⟨eQ⟩
    refine ⟨h16, hS8, ?_, hSD, hQ16⟩
    rcases halt AutG AutS hAutSG hS8 with h8 | htop
    · refine Or.inl ⟨(Subgroup.eq_of_le_of_card_ge hAutSG (by rw [h8, hS8])).symm, ?_⟩
      rw [hNK, h8]
    · refine Or.inr ⟨htop, ?_⟩
      rw [hNK, htop, Subgroup.card_top, hAut24]

end CFSG.Semidihedral.Local
