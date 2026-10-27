module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB5
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X]

namespace Setting3

variable (s : Setting3 X)

theorem card_B0_eq_two_of_A10 (hJo : CFSec8JOrder) (hP : CF82A10P)
    (hNine : CF82L2NineAbelian)
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)))
    {u : X} (hu : u ∈ normalizer (s.h.S : Set X)) (hua : u⁻¹ * s.h.a * u ≠ s.h.a) :
    Nat.card (s.h.secB0 s.y) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := conjugate s.h.P u with hWdef
  have hWN : W ≤ normalizer (s.h.J : Set X) :=
    (s.h.sec8_conjugate_P_le_S hu).trans s.h.S_le_normalizer
  have hW := conjugate_P_inf_kernel' s.C_eq hu hua
  have hCW : conjugate s.Ct u ≤ W := map_mono s.Ct_le_P
  have hBW : conjugate (s.h.secB0 s.y) u ≤ W := map_mono s.B0_le_P
  set C := rhoImg s.h.J (conjugate s.Ct u) with hCdef
  set E := rhoImg s.h.J (conjugate (s.h.secB0 s.y) u) with hEdef
  have hcomm : E ≤ centralizer (C : Set (MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))) := by
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
      s.Ct_comm_B0 hd' he'
    calc d * e = u⁻¹ * ((u * d * u⁻¹) * (u * e * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * e * u⁻¹) * (u * d * u⁻¹)) * u := by rw [hc]
      _ = e * d := by group
  have hdisj : C ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro σ ⟨⟨⟨d, hdN⟩, hd, rfl⟩, ⟨⟨e, heN⟩, he, he'⟩⟩
    have hde : (⟨e, heN⟩ : ↥(normalizer (s.h.J : Set X))) = ⟨d, hdN⟩ :=
      rho_injOn hW (show _ ∈ W.subgroupOf _ from hBW (mem_subgroupOf.mp he))
        (show _ ∈ W.subgroupOf _ from hCW (mem_subgroupOf.mp hd)) he'
    have hed : e = d := congrArg Subtype.val hde
    have hd1 : d ∈ conjugate s.Ct u := mem_subgroupOf.mp hd
    have he1 : e ∈ conjugate (s.h.secB0 s.y) u := mem_subgroupOf.mp he
    rw [hed, mem_conjugate_iff] at he1
    rw [mem_conjugate_iff] at hd1
    have h0 : u * d * u⁻¹ = 1 := mem_bot.mp (s.Ct_inf_B0 ▸ mem_inf.mpr ⟨hd1, he1⟩)
    have hd0 : d = 1 := by
      calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
        _ = 1 := by rw [h0]; group
    rw [mem_bot]
    change Eight.oddBarAction s.h.J ⟨d, hdN⟩ = 1
    rw [show (⟨d, hdN⟩ : ↥(normalizer (s.h.J : Set X))) = 1 from Subtype.ext hd0, map_one]
  have hC2 : IsPGroup 2 C := by
    have h1 : IsPGroup 2 (conjugate s.Ct u) := s.isPGroup_Ct.map _
    exact (h1.of_equiv (subgroupOfEquivOfLe (hCW.trans hWN)).symm).map _
  have hE2 : IsPGroup 2 E := by
    have hB2 : IsPGroup 2 (conjugate (s.h.secB0 s.y) u) := (s.h.isPGroup_secB0 s.y).map _
    exact (hB2.of_equiv (subgroupOfEquivOfLe (hBW.trans hWN)).symm).map _
  obtain ⟨hJL, hJ8, -⟩ := hP _ s.p s.f s.hp s.hp2 s.hf s.centralizer_eq hA s.sec.a
    s.sec.orderOf_a s.sec.J s.sec.J_le s.sec.isPComponent_J s.J_type
  obtain ⟨eJ⟩ := s.sec_J_equiv
  have hJL' := LieType.CurtisTits.lieModel_of_mulEquiv eJ hJL
  have hD8 : Nat.card s.h.D = 8 := by
    have h1 := card_D_ge_eight hJo s.case8
    have h2 := hJ8 (s.sec.S ⊓ s.sec.J) (s.sec.toHyp52.isPGroup_S.to_le inf_le_left) inf_le_right
    rw [s.card_secD] at h2
    omega
  have hC4 : Nat.card C = 4 := by
    rw [hCdef, card_rhoImg hWN hW hCW, card_conjugate]
    have := s.two_mul_card_Ct hA
    omega
  have hEc : Nat.card E = Nat.card (s.h.secB0 s.y) := by
    rw [hEdef, card_rhoImg hWN hW hBW, card_conjugate]
  by_contra hne
  obtain ⟨m, hm⟩ := (s.h.isPGroup_secB0 s.y).exists_card_eq
  have hB1 : Nat.card (s.h.secB0 s.y) ≠ 1 := fun h1 =>
    s.B0_ne_bot (Subgroup.eq_bot_of_card_eq _ h1)
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · exact absurd (by rw [hm, pow_zero]) hB1
    · exact absurd (by rw [hm, pow_one]) hne
    · omega
  have h4 : 2 ^ 2 ∣ Nat.card E := by
    rw [hEc, hm]
    exact pow_dvd_pow 2 hm2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  set E' := K.map E.subtype with hE'def
  have hE'E : E' ≤ E := map_subtype_le _
  have hE'c : Nat.card E' = 4 := by
    rw [hE'def, card_map_of_injective E.subtype_injective, hK]
    norm_num
  have hab : ∀ (V : Subgroup (MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))), Nat.card V = 4 →
      ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun V hV x hx y hy =>
    congrArg Subtype.val ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥V)
      (by rw [hV]; norm_num)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCE' : C ≤ centralizer (E' : Set (MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))) :=
    le_centralizer_iff.mp (hE'E.trans hcomm)
  set A := C ⊔ E' with hAdef
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    rw [hAdef, sup_eq_closure] at hx hy
    refine comm_of_mem_closure ?_ hx hy
    rintro w₁ (hw₁ | hw₁) w₂ (hw₂ | hw₂)
    · exact hab C hC4 _ hw₁ _ hw₂
    · exact (mem_centralizer_iff.mp (hCE' hw₁) w₂ hw₂).symm
    · exact mem_centralizer_iff.mp (hCE' hw₂) w₁ hw₁
    · exact hab E' hE'c _ hw₁ _ hw₂
  have hA2 : IsPGroup 2 A := IsPGroup.to_sup_of_normal_right' hC2 (hE2.to_le hE'E)
    (hCE'.trans (centralizer_le_normalizer _))
  have hA16 : 16 ≤ Nat.card A := by
    let f : ↥C × ↥E' → ↥A := fun q =>
      ⟨(q.1 : MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J)) * q.2,
        mul_mem (mem_sup_left q.1.2) (mem_sup_right q.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨c₁, hc₁⟩, ⟨e₁, he₁⟩⟩ ⟨⟨c₂, hc₂⟩, ⟨e₂, he₂⟩⟩ h
      have h1 : c₁ * e₁ = c₂ * e₂ := congrArg Subtype.val h
      have h2 : c₂⁻¹ * c₁ = e₂ * e₁⁻¹ := by
        calc c₂⁻¹ * c₁ = c₂⁻¹ * (c₁ * e₁) * e₁⁻¹ := by group
          _ = c₂⁻¹ * (c₂ * e₂) * e₁⁻¹ := by rw [h1]
          _ = e₂ * e₁⁻¹ := by group
      have h3 : c₂⁻¹ * c₁ ∈ C ⊓ E :=
        mem_inf.mpr ⟨mul_mem (inv_mem hc₂) hc₁, h2 ▸ hE'E (mul_mem he₂ (inv_mem he₁))⟩
      rw [hdisj, mem_bot, inv_mul_eq_one] at h3
      subst h3
      obtain rfl : e₁ = e₂ := mul_left_cancel h1
      rfl
    have h1 := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, hC4, hE'c] at h1
  have h8 := hNine _ hJL' A hA2 hAab
  omega

end Setting3

theorem gs82OS8Input (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J) (hRank : CFL2Rank)
    (hJo : CFSec8JOrder) (hComm : CF82L2Comm) (hP : CF82A10P) (hNine : CF82L2NineAbelian) :
    ∀ (X : Type) [Group X] [Finite X] (s : Eight2.Setting3 X),
      ¬ normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
      Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) →
        Nat.card (s.h.secB0 s.y) = 2 := by
  intro X _ _ s hNS hA
  obtain ⟨Z⟩ := exists_zData hSy hC hJ hRank hJo s.case8 s.center_J
  have hD8 := card_D_ge_eight hJo s.case8
  have haS := a_mem_commutator s.secCond.mem_P s.lemma61
  have hzS' := z_mem_commutator Z hD8
  obtain ⟨u, hu, hua, -, -⟩ := exists_swap hComm Z s.S_sylow s.C_eq s.center_J
    s.eight_le_card_P haS hzS' hNS
  have hua' : u⁻¹ * s.h.a * u ≠ s.h.a := by
    rw [hua]
    exact fun h1 => Z.hzP (h1 ▸ s.h.a_mem_P)
  exact s.card_B0_eq_two_of_A10 hJo hP hNine hA hu hua'

end Eight2

end CFSG.ComponentClassification.GSThmB
