module

public import CFSG.ClassicalInvolution.Asc77.AscR10M3
public import CFSG.ClassicalInvolution.Asc77.AscR10T9c
public import CFSG.ClassicalInvolution.Asc77.AscR10Aft1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.R10
  CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

variable {Y : Type} [Group Y]



@[expose] def SectionG2 (Λ : Set (Subgroup Y)) (K : Subgroup Y) : Prop :=
  ∃ E : Subgroup (Y ⧸ classicalInvolutionOddCore Y), E.Normal ∧ IsSimpleGroup ↥E ∧
    K.map (oddQuot Y) ≤ E ∧
    Nonempty (Ih8Model 3 1 (restrictFamily (oddQuotientFamily Λ) E) .G2 0 1)

variable [Finite Y]

theorem aft_fusion3 {K : Subgroup Y} {zK : Y} (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily K))
    (hzK : IsUniqueInvolution K zK) (hsec : SectionG2 (conjFamily K) K) (T : Set Y)
    (hT : ∀ t ∈ T, ∀ d : Y, d * t * d⁻¹ ∈ T)
    (hZ : ∀ t ∈ T, t * t = 1 → ∀ Q : Subgroup Y, Q ≤ K → IsPGroup 2 Q →
      (∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) →
      (∀ q ∈ Q, t⁻¹ * (q * t * q⁻¹) ∈ classicalInvolutionOddCore Y) →
      ∃ o ∈ classicalInvolutionOddCore Y, t = o * zK * o⁻¹)
    {s : Y} (hs : s ∈ T) (hs2 : s * s = 1) (hsK : conjSub s K = K) :
    ∃ c : Y, s = c * zK * c⁻¹ := by
  classical
  have hK : K ∈ conjFamily K := ⟨1, conjSub_one _⟩
  by_cases hdone : ∃ o ∈ classicalInvolutionOddCore Y, s = o * zK * o⁻¹
  · obtain ⟨o, -, h⟩ := hdone
    exact ⟨o, h⟩
  push Not at hdone
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have hΩg : HypOmegaGen (conjFamily K) := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ
  obtain ⟨E, hEn, hEs, hKE, ⟨Mdl⟩⟩ := hsec
  set Lh : Subgroup ↥E := (K.map (oddQuot Y)).subgroupOf E with hLh
  have hLhmap : Lh.map E.subtype = K.map (oddQuot Y) := Subgroup.map_subgroupOf_eq_of_le hKE
  have hLhΩ : Lh ∈ restrictFamily (oddQuotientFamily (conjFamily K)) E :=
    mem_restrictFamily_iff.mpr (by rw [hLhmap]; exact mem_oddQuotientFamily hK)
  set φ : MulAut ↥E := MulAut.conjNormal (oddQuot Y s) with hφ
  have hπs2 : oddQuot Y s * oddQuot Y s = 1 := by rw [← map_mul, hs2, map_one]
  have hφ2 : φ * φ = 1 := by
    rw [hφ, ← map_mul, hπs2, map_one]
  have hπsK : conjSub (oddQuot Y s) (K.map (oddQuot Y)) = K.map (oddQuot Y) := by
    rw [← AscQuot.map_conjSub, hsK]
  have hφL : Lh.map φ.toMonoidHom = Lh := by
    apply Subgroup.map_injective E.subtype_injective
    rw [hφ, map_map_conjNormal, hLhmap, hπsK]
  have hnonab : ∃ P : Subgroup ↥E, IsPGroup 2 P ∧ P ≤ Lh ∧ ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
    obtain ⟨R₀, hR₀, hR₀1, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot' (G := Y)) bot_le
    obtain ⟨x, hx, y, hy, hxy⟩ := (exists_ne_comm_of_mem_rSetGen hΩg hR₀).1
    have hx' : oddQuot Y x ∈ E := hKE ⟨x, hR₀1.1 hx, rfl⟩
    have hy' : oddQuot Y y ∈ E := hKE ⟨y, hR₀1.1 hy, rfl⟩
    refine ⟨(R₀.map (oddQuot Y)).subgroupOf E, (hR₀1.2.1.map _).comap_subtype, ?_,
      ⟨_, hx'⟩, Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩, ⟨_, hy'⟩,
      Subgroup.mem_subgroupOf.mpr ⟨y, hy, rfl⟩, fun h => hxy ?_⟩
    · intro u hu
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.map_mono hR₀1.1 (Subgroup.mem_subgroupOf.mp hu))
    · have h1 : oddQuot Y (x * y * x⁻¹ * y⁻¹) = 1 := by
        have h2 : oddQuot Y x * oddQuot Y y = oddQuot Y y * oddQuot Y x :=
          congrArg Subtype.val h
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
        group
      have h3 : x * y * x⁻¹ * y⁻¹ = 1 :=
        quot_injOn_of_isPGroup hR₀1.2.1 _ (R₀.mul_mem (R₀.mul_mem (R₀.mul_mem hx hy)
          (R₀.inv_mem hx)) (R₀.inv_mem hy)) h1
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [h3, one_mul]
  have hH : ∀ P : Subgroup ↥E, IsPGroup 2 P → P ≤ Lh → (∀ x ∈ P, φ x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro P hP2 hPL hfix
    by_contra hnc
    push Not at hnc
    obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hnc
    have hP'2 : IsPGroup 2 (P.map E.subtype) := hP2.map _
    have hP'K : P.map E.subtype ≤ K.map (oddQuot Y) := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hPL hx)
    obtain ⟨Q, hQK, hQ2, hQmap⟩ := r_exists_lift_pgroup hodd hP'2 hP'K
    have hQnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      apply hxy₀
      apply E.subtype_injective
      have h1 : (x₀ : Y ⧸ classicalInvolutionOddCore Y) ∈ Q.map (oddQuot Y) :=
        hQmap ▸ ⟨x₀, hx₀, rfl⟩
      have h2 : (y₀ : Y ⧸ classicalInvolutionOddCore Y) ∈ Q.map (oddQuot Y) :=
        hQmap ▸ ⟨y₀, hy₀, rfl⟩
      obtain ⟨q₁, hq₁, hq₁x⟩ := h1
      obtain ⟨q₂, hq₂, hq₂y⟩ := h2
      change (x₀ : Y ⧸ classicalInvolutionOddCore Y) * y₀ = y₀ * x₀
      rw [← hq₁x, ← hq₂y, ← map_mul, ← map_mul, hcon q₁ hq₁ q₂ hq₂]
    have hQfix : ∀ q ∈ Q, s⁻¹ * (q * s * q⁻¹) ∈ classicalInvolutionOddCore Y := by
      intro q hq
      have hqP' : oddQuot Y q ∈ P.map E.subtype := hQmap ▸ ⟨q, hq, rfl⟩
      obtain ⟨x, hx, hxq⟩ := hqP'
      have hφx : (φ x : Y ⧸ classicalInvolutionOddCore Y) = x := congrArg Subtype.val (hfix x hx)
      rw [hφ, MulAut.conjNormal_apply] at hφx
      have hcomm : oddQuot Y s * oddQuot Y q = oddQuot Y q * oddQuot Y s := by
        rw [← hxq]
        calc oddQuot Y s * (x : Y ⧸ classicalInvolutionOddCore Y)
            = oddQuot Y s * x * (oddQuot Y s)⁻¹ * oddQuot Y s := by group
          _ = x * oddQuot Y s := by rw [hφx]
      rw [← QuotientGroup.eq_one_iff]
      show oddQuot Y (s⁻¹ * (q * s * q⁻¹)) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    obtain ⟨o, ho, h⟩ := hZ s hs hs2 Q hQK hQ2 hQnc hQfix
    exact hdone o ho h
  obtain ⟨ē, hē⟩ := factM1_three ↥E (restrictFamily (oddQuotientFamily (conjFamily K)) E) 1 Mdl φ
    hφ2 hLhΩ hφL hH
  have hact : ∀ x : ↥E, oddQuot Y s * (x : Y ⧸ classicalInvolutionOddCore Y) * (oddQuot Y s)⁻¹ =
      (ē : Y ⧸ classicalInvolutionOddCore Y) * x * (ē : Y ⧸ classicalInvolutionOddCore Y)⁻¹ := by
    intro x
    have h1 := congrArg (fun ψ : MulAut ↥E => ((ψ x : ↥E) : Y ⧸ classicalInvolutionOddCore Y)) hē
    simpa [hφ, MulAut.conjNormal_apply, MulAut.conj_apply] using h1
  have hē1 : ē ≠ 1 := by
    intro h1
    obtain ⟨P, hP2, hPL, x, hx, y, hy, hxy⟩ := hnonab
    exact hxy (hH P hP2 hPL (fun u _ => by rw [hē, h1]; simp) x hx y hy)
  have hctr : Subgroup.center ↥E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥E) with h | h
    · exact h
    · exfalso
      obtain ⟨P, -, -, x, hx, y, hy, hxy⟩ := hnonab
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hē2 : ē * ē = 1 := by
    have hcen : ē * ē ∈ Subgroup.center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun ψ : MulAut ↥E => ψ g) hφ2
      simp only [MulAut.mul_apply, MulAut.one_apply] at h
      rw [hē] at h
      simp only [MulAut.conj_apply] at h
      have e : ē * ē * g = (ē * (ē * g * ē⁻¹) * ē⁻¹) * (ē * ē) := by group
      rw [h] at e
      exact e.symm
    rw [hctr, Subgroup.mem_bot] at hcen
    exact hcen
  obtain ⟨L', hL'Ω, hL'⟩ := factM2_three ↥E (restrictFamily (oddQuotientFamily (conjFamily K)) E)
    1 Mdl ⟨Lh, hLhΩ⟩ ē hē2 hē1
  obtain ⟨M₀, ⟨c, rfl⟩, hM₀⟩ := mem_restrictFamily_iff.mp hL'Ω
  have hu₁ : IsUniqueInvolution ((conjSub c K).map (oddQuot Y)) (oddQuot Y (c * zK * c⁻¹)) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_oddCore_inf _) (hzK.conj c)
  have hu₂ : IsUniqueInvolution ((conjSub c K).map (oddQuot Y))
      (E.subtype ē) := by
    rw [hM₀]
    exact isUniqueInvolution_map_of_injective E.subtype_injective hL'
  have hēz' : (ē : Y ⧸ classicalInvolutionOddCore Y) = oddQuot Y (c * zK * c⁻¹) := hu₂.eq hu₁
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : Y, z₁ = c * zK * c⁻¹ := ⟨_, rfl⟩
  have hz₁2 : z₁ * z₁ = 1 := by rw [hz₁]; exact (hzK.conj c).sq
  have hēz : (ē : Y ⧸ classicalInvolutionOddCore Y) = oddQuot Y z₁ := by rw [hz₁]; exact hēz'
  have hcomm_sē : oddQuot Y s * (ē : Y ⧸ classicalInvolutionOddCore Y) =
      (ē : Y ⧸ classicalInvolutionOddCore Y) * oddQuot Y s := by
    have h := hact ē
    calc oddQuot Y s * (ē : Y ⧸ classicalInvolutionOddCore Y)
        = (oddQuot Y s * (ē : Y ⧸ classicalInvolutionOddCore Y) * (oddQuot Y s)⁻¹) *
            oddQuot Y s := by group
      _ = ((ē : Y ⧸ classicalInvolutionOddCore Y) * (ē : Y ⧸ classicalInvolutionOddCore Y) *
            (ē : Y ⧸ classicalInvolutionOddCore Y)⁻¹) * oddQuot Y s := by rw [h]
      _ = (ē : Y ⧸ classicalInvolutionOddCore Y) * oddQuot Y s := by group
  have hQs : IsPGroup 2 (Subgroup.zpowers s) := by
    have hord : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hs2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2]; rfl)
  have hQt : ∀ q ∈ Subgroup.zpowers s, z₁⁻¹ * (q * z₁ * q⁻¹) ∈
      classicalInvolutionOddCore Y := by
    intro q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rw [← QuotientGroup.eq_one_iff]
    show oddQuot Y (z₁⁻¹ * (s ^ k * z₁ * (s ^ k)⁻¹)) = 1
    have hc : oddQuot Y s ^ k * (ē : Y ⧸ classicalInvolutionOddCore Y) =
        (ē : Y ⧸ classicalInvolutionOddCore Y) * oddQuot Y s ^ k :=
      (Commute.zpow_left (show Commute (oddQuot Y s) (ē : Y ⧸ classicalInvolutionOddCore Y) from
        hcomm_sē) k).eq
    simp only [map_mul, map_inv, map_zpow]
    rw [show oddQuot Y z₁ = (ē : Y ⧸ classicalInvolutionOddCore Y) from hēz.symm, hc]
    group
  obtain ⟨v, hvN, hv'⟩ := r_exists_conj_centralizes_of_odd hodd hQs hz₁2 hQt
  have hsz₂ : s * (v * z₁ * v⁻¹) = (v * z₁ * v⁻¹) * s := hv' s (Subgroup.mem_zpowers s)
  obtain ⟨d, hd⟩ : ∃ d : Y, d = v * c := ⟨_, rfl⟩
  have hz₂ : v * z₁ * v⁻¹ = d * zK * d⁻¹ := by rw [hd, hz₁]; group
  have hπv : oddQuot Y v = 1 := (QuotientGroup.eq_one_iff v).mpr hvN
  have hπz₂ : oddQuot Y (d * zK * d⁻¹) = (ē : Y ⧸ classicalInvolutionOddCore Y) := by
    rw [← hz₂, map_mul, map_mul, map_inv, hπv, one_mul, inv_one, mul_one]
    exact hēz.symm
  have hconjz : (oddQuot Y d)⁻¹ * (ē : Y ⧸ classicalInvolutionOddCore Y) * oddQuot Y d =
      oddQuot Y zK := by
    rw [← hπz₂, map_mul, map_mul, map_inv]
    group
  have ht₁T : d⁻¹ * s * d ∈ T := by
    have := hT s hs d⁻¹
    rwa [inv_inv] at this
  have ht₁2 : (d⁻¹ * s * d) * (d⁻¹ * s * d) = 1 := by
    calc (d⁻¹ * s * d) * (d⁻¹ * s * d) = d⁻¹ * (s * s) * d := by group
      _ = 1 := by rw [hs2]; group
  have hzcomm : ∀ x ∈ K, x * zK = zK * x := by
    intro x hx
    have hsq : x * zK * x⁻¹ * (x * zK * x⁻¹) = 1 := by
      calc x * zK * x⁻¹ * (x * zK * x⁻¹) = x * (zK * zK) * x⁻¹ := by group
        _ = 1 := by rw [hzK.sq]; group
    have hm : x * zK * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hx hzK.mem) (K.inv_mem hx)
    have h1 := (hzK.unique _ hm hsq).resolve_left (fun h => hzK.ne_one (by
      have := congrArg (fun y => x⁻¹ * y * x) h
      simpa [mul_assoc] using this))
    calc x * zK = x * zK * x⁻¹ * x := by group
      _ = zK * x := by rw [h1]
  have key : ∀ q ∈ K, oddQuot Y (d⁻¹ * s * d) * oddQuot Y q * (oddQuot Y (d⁻¹ * s * d))⁻¹ =
      oddQuot Y q := by
    intro q hq
    have hqE : oddQuot Y q ∈ E := hKE ⟨q, hq, rfl⟩
    have hy : oddQuot Y d * oddQuot Y q * (oddQuot Y d)⁻¹ ∈ E := hEn.conj_mem _ hqE _
    have h1 := hact ⟨_, hy⟩
    simp only [map_mul, map_inv]
    calc (oddQuot Y d)⁻¹ * oddQuot Y s * oddQuot Y d * oddQuot Y q *
          ((oddQuot Y d)⁻¹ * oddQuot Y s * oddQuot Y d)⁻¹
        = (oddQuot Y d)⁻¹ * (oddQuot Y s * (oddQuot Y d * oddQuot Y q * (oddQuot Y d)⁻¹) *
            (oddQuot Y s)⁻¹) * oddQuot Y d := by group
      _ = (oddQuot Y d)⁻¹ * ((ē : Y ⧸ classicalInvolutionOddCore Y) *
            (oddQuot Y d * oddQuot Y q * (oddQuot Y d)⁻¹) *
            (ē : Y ⧸ classicalInvolutionOddCore Y)⁻¹) * oddQuot Y d := by rw [h1]
      _ = ((oddQuot Y d)⁻¹ * (ē : Y ⧸ classicalInvolutionOddCore Y) * oddQuot Y d) *
            oddQuot Y q * ((oddQuot Y d)⁻¹ * (ē : Y ⧸ classicalInvolutionOddCore Y) *
            oddQuot Y d)⁻¹ := by group
      _ = oddQuot Y zK * oddQuot Y q * (oddQuot Y zK)⁻¹ := by rw [hconjz]
      _ = oddQuot Y q := by
        rw [← map_inv, ← map_mul, ← map_mul, ← hzcomm q hq]
        simp
  obtain ⟨R₀, hR₀, hR₀1, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot' (G := Y)) bot_le
  have hR₀nc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x := (exists_ne_comm_of_mem_rSetGen hΩg hR₀).1
  have hQfix₁ : ∀ q ∈ R₀, (d⁻¹ * s * d)⁻¹ * (q * (d⁻¹ * s * d) * q⁻¹) ∈
      classicalInvolutionOddCore Y := by
    intro q hq
    rw [← QuotientGroup.eq_one_iff]
    show oddQuot Y ((d⁻¹ * s * d)⁻¹ * (q * (d⁻¹ * s * d) * q⁻¹)) = 1
    have hk := key q (hR₀1.1 hq)
    have hc : oddQuot Y (d⁻¹ * s * d) * oddQuot Y q = oddQuot Y q * oddQuot Y (d⁻¹ * s * d) := by
      calc oddQuot Y (d⁻¹ * s * d) * oddQuot Y q
          = (oddQuot Y (d⁻¹ * s * d) * oddQuot Y q * (oddQuot Y (d⁻¹ * s * d))⁻¹) *
              oddQuot Y (d⁻¹ * s * d) := by group
        _ = oddQuot Y q * oddQuot Y (d⁻¹ * s * d) := by rw [hk]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  obtain ⟨o, -, hto⟩ := hZ _ ht₁T ht₁2 R₀ hR₀1.1 hR₀1.2.1 hR₀nc hQfix₁
  refine ⟨d * o, ?_⟩
  calc s = d * (d⁻¹ * s * d) * d⁻¹ := by group
    _ = d * (o * zK * o⁻¹) * d⁻¹ := by rw [hto]
    _ = d * o * zK * (d * o)⁻¹ := by group

end CFSG.ClassicalInvolution.Asc77.T3CII
