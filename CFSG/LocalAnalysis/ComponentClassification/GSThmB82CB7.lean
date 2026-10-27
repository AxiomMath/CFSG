module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB5

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem lieModel_two_mul_of_isSec8JType {Y : Type} [Group Y] {p f : ℕ} (hJ : IsSec8JType Y p f) :
    Blueprint.LieModel Y .PSL 2 p (2 * f) := by
  rcases hJ with hL | ⟨rfl, rfl, hA⟩
  · exact hL
  · exact Or.inl ⟨by decide,
      CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six Y hA⟩

namespace Setting3

variable (s : Setting3 X)

theorem card_B0_eq_two (hCyc : CF82L2Cyc)
    (hA : ¬ Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)))
    {u : X} (hu : u ∈ normalizer (s.h.S : Set X)) (hua : u⁻¹ * s.h.a * u ≠ s.h.a) :
    Nat.card (s.h.secB0 s.y) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := conjugate s.h.P u with hWdef
  have hWN : W ≤ normalizer (s.h.J : Set X) :=
    (s.h.sec8_conjugate_P_le_S hu).trans s.h.S_le_normalizer
  have hW := conjugate_P_inf_kernel' s.C_eq hu hua
  have hCW : conjugate s.Cp u ≤ W := map_mono s.Cp_le_P
  have hBW : conjugate (s.h.secB0 s.y) u ≤ W := map_mono s.B0_le_P
  have hcyc : IsCyclic ↥(rhoImg s.h.J (conjugate s.Cp u)) := by
    have := s.isCyclic_Cp hA
    have h1 : IsCyclic ↥(conjugate s.Cp u) :=
      isCyclic_of_surjective (conjugateEquiv s.Cp u).toMonoidHom (MulEquiv.surjective _)
    have h2 : IsCyclic ↥((conjugate s.Cp u).subgroupOf (normalizer (s.h.J : Set X))) :=
      isCyclic_of_surjective (subgroupOfEquivOfLe (hCW.trans hWN)).symm.toMonoidHom
        (MulEquiv.surjective _)
    exact isCyclic_of_surjective ((Eight.oddBarAction s.h.J).subgroupMap _)
      ((Eight.oddBarAction s.h.J).subgroupMap_surjective _)
  obtain ⟨T, -, hT⟩ := s.h.sec8_exists_sylow_Dbar
  have hcard : 2 * Nat.card ↥(rhoImg s.h.J (conjugate s.Cp u)) = Nat.card T := by
    rw [card_rhoImg hWN hW hCW, card_conjugate, hT, s.two_mul_card_Cp hA]
  have hE2 : IsPGroup 2 ↥(rhoImg s.h.J (conjugate (s.h.secB0 s.y) u)) := by
    have hB2 : IsPGroup 2 (conjugate (s.h.secB0 s.y) u) := (s.h.isPGroup_secB0 s.y).map _
    exact (hB2.of_equiv (subgroupOfEquivOfLe (hBW.trans hWN)).symm).map _
  have hcomm : rhoImg s.h.J (conjugate (s.h.secB0 s.y) u) ≤ centralizer
      (rhoImg s.h.J (conjugate s.Cp u) : Set (MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))) := by
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change d * e = e * d
    have he' := mem_subgroupOf.mp he
    have hd' := mem_subgroupOf.mp hd
    rw [mem_conjugate_iff] at he' hd'
    have hc : (u * d * u⁻¹) * (u * e * u⁻¹) = (u * e * u⁻¹) * (u * d * u⁻¹) :=
      s.Cp_comm_B0 hd' he'
    calc d * e = u⁻¹ * ((u * d * u⁻¹) * (u * e * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * e * u⁻¹) * (u * d * u⁻¹)) * u := by rw [hc]
      _ = e * d := by group
  have hdisj : rhoImg s.h.J (conjugate s.Cp u) ⊓
      rhoImg s.h.J (conjugate (s.h.secB0 s.y) u) = ⊥ := by
    rw [eq_bot_iff]
    rintro σ ⟨⟨⟨d, hdN⟩, hd, rfl⟩, ⟨⟨e, heN⟩, he, he'⟩⟩
    have hde : (⟨e, heN⟩ : ↥(normalizer (s.h.J : Set X))) = ⟨d, hdN⟩ :=
      rho_injOn hW (show _ ∈ W.subgroupOf _ from hBW (mem_subgroupOf.mp he))
        (show _ ∈ W.subgroupOf _ from hCW (mem_subgroupOf.mp hd)) he'
    have hed : e = d := congrArg Subtype.val hde
    have hd1 : d ∈ conjugate s.Cp u := mem_subgroupOf.mp hd
    have he1 : e ∈ conjugate (s.h.secB0 s.y) u := mem_subgroupOf.mp he
    rw [hed, mem_conjugate_iff] at he1
    rw [mem_conjugate_iff] at hd1
    have h0 : u * d * u⁻¹ = 1 := by
      have := s.Cp_inf_B0 ▸ mem_inf.mpr ⟨hd1, he1⟩
      exact mem_bot.mp this
    have hd0 : d = 1 := by
      calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
        _ = 1 := by rw [h0]; group
    rw [mem_bot]
    change Eight.oddBarAction s.h.J ⟨d, hdN⟩ = 1
    rw [show (⟨d, hdN⟩ : ↥(normalizer (s.h.J : Set X))) = 1 from Subtype.ext hd0, map_one]
  obtain ⟨-, p, f, hp, hp2, hf, -, hJt⟩ := Hyp52.Sec8Case.exists_params s.h s.case8
  have hE := hCyc _ p f hp hp2 hf (lieModel_two_mul_of_isSec8JType hJt) T _ _ hcyc hcard hE2
    hcomm hdisj
  rw [card_rhoImg hWN hW hBW, card_conjugate] at hE
  have hB0 := s.B0_ne_bot
  have h1 : Nat.card (s.h.secB0 s.y) ≠ 1 := fun h1 => hB0 (Subgroup.eq_bot_of_card_eq _ h1)
  have h0 : 0 < Nat.card (s.h.secB0 s.y) := Nat.card_pos
  omega

end Setting3

end Eight2

end CFSG.ComponentClassification.GSThmB
