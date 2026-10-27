module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdAE5A
public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs
public import CFSG.ClassicalInvolution.Q3.TL3T23

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AE5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent)
open scoped commutatorElement

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem pSpan_eq_top (hgen : omegaGen Φ = ⊤) : pSpan Φ = ⊤ := hgen

theorem mem_pSpan (hgen : omegaGen Φ = ⊤) (y : X) : y ∈ pSpan Φ := by
  rw [pSpan_eq_top hgen]
  exact Subgroup.mem_top y

theorem mem_center_of_mem_ker (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {k : ↥(pSpan Φ)}
    (hk : k ∈ I.φ.ker) : (k : X) ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (I.ker_le hk) ⟨y, mem_pSpan hgen y⟩)

theorem map_eq_one_of_mem_center (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {c : X}
    (hc : c ∈ Subgroup.center X) : I.φ ⟨c, mem_pSpan hgen c⟩ = 1 := by
  refine eq_one_of_comm_aeBar fun g hg => ?_
  rw [← I.range_eq] at hg
  obtain ⟨y, rfl⟩ := hg
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (y : X)).symm

variable [Finite X]

theorem oddCoreOf_eq_bot (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (I : AEIdent Φ 5) {L : Subgroup X} (hL : L ∈ Φ) : oddCoreOf L = ⊥ := by
  have hodd : Odd (Nat.card ↥(oddCoreOf L)) := by
    rw [oddCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥L
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  have h2 : IsPGroup 2 ↥(memBar α h b) :=
    IsPGroup.of_card (n := 3) (by rw [natCard_memBar (by norm_num) α h b]; norm_num)
  have hcen : oddCoreOf L ≤ Subgroup.center X := by
    intro w hw
    have hwL : w ∈ L := by
      obtain ⟨m, -, rfl⟩ := hw
      exact m.2
    refine mem_center_of_mem_ker hgen I (k := ⟨w, le_pSpan hL hwL⟩) ?_
    have hmem : I.φ ⟨w, le_pSpan hL hwL⟩ ∈ memBar α h b := by
      rw [← hlab]
      exact I.mem_map hL hwL
    have hodd' : Odd (orderOf (I.φ ⟨w, le_pSpan hL hwL⟩)) := by
      refine hodd.of_dvd_nat ((orderOf_map_dvd I.φ _).trans ?_)
      rw [Subgroup.orderOf_mk]
      exact Subgroup.orderOf_dvd_natCard _ hw
    obtain ⟨j, hj⟩ := h2 ⟨_, hmem⟩
    have hj' : I.φ ⟨w, le_pSpan hL hwL⟩ ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow] at this
    have h1 : orderOf (I.φ ⟨w, le_pSpan hL hwL⟩) = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hodd').pow_left j)
        (orderOf_dvd_of_pow_eq_one hj') dvd_rfl
    exact orderOf_eq_one_iff.mp h1
  have hnorm : (oddCoreOf L).Normal := ⟨fun w hw g => by
    rw [(Subgroup.mem_center_iff.mp (hcen hw) g), mul_inv_cancel_right]
    exact hw⟩
  have hle : oddCoreOf L ≤ classicalInvolutionOddCore X := le_sSup ⟨hnorm, hodd⟩
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem isPGroup_mem (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {L : Subgroup X} (hL : L ∈ Φ) :
    IsPGroup 2 ↥L := by
  have hb : classicalInvolutionOddCore ↥L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
      (oddCoreOf_eq_bot hO hgen I hL)
  refine (h.twoGroup L hL).of_injective (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) ?_
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hb]

theorem natCard_mem (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {L : Subgroup X} (hL : L ∈ Φ) :
    Nat.card ↥L = 8 := by
  obtain ⟨e⟩ : Nonempty (↥L ≃* QuaternionGroup 2) := h.quat L hL L
    ⟨le_rfl, isPGroup_mem h hO hgen I hL, fun _ hVL _ hLV => le_antisymm hVL hLV⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem eq_of_map_eq (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {K J : Subgroup X} (hK : K ∈ Φ) (hJ : J ∈ Φ)
    (he : (K.subgroupOf (pSpan Φ)).map I.φ = (J.subgroupOf (pSpan Φ)).map I.φ) : K = J := by
  have hZc : I.φ.ker.map (pSpan Φ).subtype ≤ Subgroup.center X := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_center_of_mem_ker hgen I hk
  have hZK : ∀ L ∈ Φ, I.φ.ker.map (pSpan Φ).subtype ⊓ L = ⊥ := by
    intro L hL
    rw [eq_bot_iff]
    rintro w ⟨⟨k, hk, hkw⟩, hwL⟩
    obtain ⟨α, h', b, hlab⟩ := I.label L hL
    rw [Subgroup.mem_bot]
    refine I.injOn (by norm_num) hL (natCard_mem h hO hgen I hL) hlab hwL L.one_mem ?_
    have hk1 : I.φ k = 1 := hk
    have hk' : k = ⟨w, le_pSpan hL hwL⟩ := Subtype.ext hkw
    rw [← hk', hk1]
    exact (map_one I.φ).symm
  obtain ⟨α, h', b, hlab⟩ := I.label K hK
  obtain ⟨a, ha, ha2⟩ := SecIdE2.exists_mul_self_ne_one_memBar (by norm_num) α h' b
  rw [← hlab] at ha
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hK ha
  have hl2 : l * l ≠ 1 := fun h1 => ha2 (by
    rw [← map_mul, ← map_one I.φ]
    congr 1
    exact Subtype.ext h1)
  have hlJ := I.mem_map hK hl
  rw [he] at hlJ
  obtain ⟨j, hj, hje⟩ := I.exists_of_mem_map hJ hlJ
  have hc : j⁻¹ * l ∈ I.φ.ker.map (pSpan Φ).subtype := by
    refine ⟨⟨j, le_pSpan hJ hj⟩⁻¹ * ⟨l, le_pSpan hK hl⟩, ?_, rfl⟩
    show I.φ (⟨j, le_pSpan hJ hj⟩⁻¹ * ⟨l, le_pSpan hK hl⟩) = 1
    rw [map_mul, map_inv, hje, inv_mul_cancel]
  exact TC.Thin.eq_of_mem_sup_center h.hyp (fun L hL => isPGroup_mem h hO hgen I hL) hZc hZK hK hJ
    hl hl2 hj hc (by group)

theorem ne_mul_inv_inv (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hx : IsUniqueInvolution A x)
    (hx' : IsUniqueInvolution B x') (hxx' : x * x' ∈ Subgroup.center X) {e : X}
    (heA : ∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) (heB : ∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B)
    {P : Subgroup X} (hP : P ∈ Φ) (hPA : P ≠ A) (hPB : P ≠ B) {v : X}
    (hv : IsUniqueInvolution P v) {g k : X} (hg : g ∈ A) (hk : k ∈ B) :
    e ≠ v * g⁻¹ * k⁻¹ := by
  intro hev
  have hB' : B ∈ Φ := hB.1
  obtain ⟨α, hα, bA, hlA⟩ := I.label A hA
  obtain ⟨β, hβ, bB, hlB⟩ := I.label B hB'
  obtain ⟨γ, hγ, bP, hlP⟩ := I.label P hP
  have hzA := I.map_eq_zBar (by norm_num) hA (natCard_mem h hO hgen I hA) hlA hx
  have hzB := I.map_eq_zBar (by norm_num) hB' (natCard_mem h hO hgen I hB') hlB hx'
  have hzP := I.map_eq_zBar (by norm_num) hP (natCard_mem h hO hgen I hP) hlP hv
  have hαβ : α = β := by
    have h1 := map_eq_one_of_mem_center hgen I hxx'
    have h2 : I.φ ⟨x * x', mem_pSpan hgen _⟩ = zBar α hα * zBar β hβ := by
      rw [← hzA, ← hzB, ← map_mul]
      rfl
    rw [h2] at h1
    refine eq_of_zBar_eq (by norm_num) (h := hα) (h' := hβ) ?_
    calc zBar α hα = zBar α hα * (zBar β hβ * zBar β hβ) := by rw [zBar_mul_self, mul_one]
      _ = (zBar α hα * zBar β hβ) * zBar β hβ := by group
      _ = zBar β hβ := by rw [h1, one_mul]
  subst hαβ
  have hlB' : (B.subgroupOf (pSpan Φ)).map I.φ = memBar α hα bB := hlB
  have hbB : bB = !bA := by
    by_contra hb
    have hbb : bB = bA := by cases bA <;> cases bB <;> simp_all
    subst hbb
    exact hB.2.1 (eq_of_map_eq h hO hgen I hB' hA (hlB'.trans hlA.symm))
  subst hbB
  have hγα : γ ≠ α := by
    rintro rfl
    have hlP' : (P.subgroupOf (pSpan Φ)).map I.φ = memBar γ hα bP := hlP
    by_cases hb : bP = bA
    · subst hb
      exact hPA (eq_of_map_eq h hO hgen I hP hA (hlP'.trans hlA.symm))
    · have hb' : bP = !bA := by cases bA <;> cases bP <;> simp_all
      subst hb'
      exact hPB (eq_of_map_eq h hO hgen I hP hB' (hlP'.trans hlB'.symm))
  have hcomm : ∀ {L : Subgroup X} (hL : L ∈ Φ), (∀ k ∈ L, ⁅e, k⁆ ∈ oddCoreOf L) →
      ∀ a ∈ (L.subgroupOf (pSpan Φ)).map I.φ,
        I.φ ⟨e, mem_pSpan hgen e⟩ * a = a * I.φ ⟨e, mem_pSpan hgen e⟩ := by
    intro L hL heL a ha
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL ha
    have h1 := heL l hl
    rw [oddCoreOf_eq_bot hO hgen I hL, Subgroup.mem_bot] at h1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hcA := hcomm hA heA
  have hcB := hcomm hB' heB
  rw [hlA] at hcA
  rw [hlB'] at hcB
  have hcT : ∀ a ∈ memBar α hα true,
      I.φ ⟨e, mem_pSpan hgen e⟩ * a = a * I.φ ⟨e, mem_pSpan hgen e⟩ := by
    cases bA
    · exact hcB
    · exact hcA
  have hcF : ∀ a ∈ memBar α hα false,
      I.φ ⟨e, mem_pSpan hgen e⟩ * a = a * I.φ ⟨e, mem_pSpan hgen e⟩ := by
    cases bA
    · exact hcA
    · exact hcB
  have heM : ∀ b, I.φ ⟨e, mem_pSpan hgen e⟩ ∈ memBar α hα b := fun b => by
    rcases eq_one_or_eq_zBar_of_comm α hα hcT hcF with h1 | h1 <;> rw [h1]
    · exact (memBar α hα b).one_mem
    · exact zBar_mem_memBar α hα b
  have hkM : I.φ ⟨k, le_pSpan hB' hk⟩ ∈ memBar α hα (!bA) := by
    rw [← hlB']
    exact I.mem_map hB' hk
  have hgM : I.φ ⟨g, le_pSpan hA hg⟩ ∈ memBar α hα bA := by
    rw [← hlA]
    exact I.mem_map hA hg
  have hv' : I.φ ⟨e, mem_pSpan hgen e⟩ * I.φ ⟨k, le_pSpan hB' hk⟩ * I.φ ⟨g, le_pSpan hA hg⟩ =
      zBar γ hγ := by
    rw [← hzP, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show e * k * g = v
    rw [hev]
    group
  cases bA
  · exact mul_ne_zBar α hα hγ hγα ((memBar α hα true).mul_mem (heM true) hkM) hgM hv'
  · have hF := (memBar α hα false).mul_mem (heM false) hkM
    exact mul_ne_zBar α hα hγ hγα hgM hF
      ((SecIdE2.comm_memBar_twin α hα _ hgM _ hF).trans hv')

end CFSG.ClassicalInvolution.Q3.TL4.AE5
