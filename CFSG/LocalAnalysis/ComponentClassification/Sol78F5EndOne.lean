module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndT3
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndL
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndW1

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.Goldschmidt CFSG.Goldschmidt75
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCent_eq_oddCoreOfCentralizer (a : G) : oddCent a = oddCoreOfCentralizer a := by
  unfold oddCent oddCoreOf oddCoreOfCentralizer
  rw [goldschmidtOddCore_eq_pPrimeCore]

omit [Finite G] in
theorem commute_of_commutator_eq_bot {N : Subgroup G} {a : G} (h : ⁅N, zpowers a⁆ = ⊥) :
    ∀ n ∈ N, n * a = a * n := fun n hn => by
  have h1 := commutator_eq_bot_iff_le_centralizer.mp h hn
  exact (mem_centralizer_iff.mp h1 a (mem_zpowers a)).symm

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem le_centralizer_oddCoreIn (htz : ∀ n ∈ oddCent z, n * t = t * n) :
    L ≤ centralizer (oddCoreIn L : Set G) := by
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  have hOz : oddCoreIn L ≤ oddCent z :=
    oddCoreIn_le_oddCent H.sec5.zL.2.1 H.sec5.centralizer_le_normalizer
  exact le_centralizer_of_commute H.le_oddResidualIn
    (fun l hl => mem_normalizer_oddCoreIn (le_normalizer hl)) H.sec5.tL H.t_not_mem_oddCoreIn
    (fun n hn => htz n (hOz hn))
    (fun o ho x hx => mem_centralizer_iff.mp (mem_inf.mp hx).2 o ho)

theorem le_centralizer_of_mem_Rs (hLO : L ≤ centralizer (oddCoreIn L : Set G)) {r : G}
    (hr : r ∈ conjugate (S ⊓ L) s) (hr2 : orderOf r = 2) :
    L ≤ centralizer ({r} : Set G) := by
  have hP : IsPGroup 2 (zpowers r) := isPGroup_zpowers_of_orderOf hr2
  have hPC : zpowers r ≤ coreActionKernel L :=
    zpowers_le_of_mem (H.sec5.Q_le (H.l511 hr))
  have h1 := le_inf_centralizer_sup_oddCoreIn hP hPC
  have h2 := le_of_le_sup_commute H.le_oddResidualIn h1 (odd_card_oddCoreIn L)
    fun n hn x hx => (mem_centralizer_iff.mp (hLO (mem_inf.mp hx).1) n hn)
  rw [← FooteLit.centralizer_zpowers_eq]
  exact h2.trans inf_le_right

theorem centralizer_le_normalizer_of_mem_Rs (hLO : L ≤ centralizer (oddCoreIn L : Set G))
    {r : G} (hr : r ∈ conjugate (S ⊓ L) s) (hr2 : orderOf r = 2)
    (htr : ∀ n ∈ oddCent r, n * t = t * n) :
    centralizer ({r} : Set G) ≤ normalizer (L : Set G) := by
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  have hLr := H.le_centralizer_of_mem_Rs hLO hr hr2
  have hrQ := H.l511 hr
  obtain ⟨hfix, hM, hMF, -, -, -⟩ := H.sec5.footeF_data hrQ hr2
  have hCM := le_normalizer_of_mem_footeFamilyOf H.sec5.sec4.huniq hM hMF
  have hLN : L ≤ centralizer (oddCoreOfCentralizer r : Set G) :=
    le_centralizer_of_commute H.le_oddResidualIn
      (fun l hl => mem_normalizer_oddCoreOfCentralizer (hLr hl)) H.sec5.tL H.t_not_mem_oddCoreIn
      (fun n hn => htr n (by rw [oddCent_eq_oddCoreOfCentralizer]; exact hn))
      (fun o ho x hx => mem_centralizer_iff.mp (hLO (mem_inf.mp hx).1) o ho)
  have hLF : L ≤ footeFixed L r := by
    refine H.le_oddResidualIn.trans (closure_mono ?_)
    rintro g ⟨hgL, k, hk⟩
    exact ⟨mem_sup_left (mem_inf.mpr ⟨hgL, hLr hgL⟩), k, hk⟩
  have hFL : footeFixed L r ≤ L ⊔ oddCoreOfCentralizer r := by
    rw [footeFixed, closure_le]
    rintro g ⟨hg, -⟩
    exact (sup_le_sup_right (inf_le_left : L ⊓ centralizer ({r} : Set G) ≤ L)
      (oddCoreOfCentralizer r)) hg
  intro x hx
  apply mem_normalizer_of_map_conj_le
  have h1 : L.map (MulAut.conj x).toMonoidHom ≤ footeFixed L r := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hfix]
    exact (mem_normalizer_iff.mp (hCM hx) y).mp (hfix ▸ hLF hy)
  refine le_of_le_sup_commute ?_ (h1.trans hFL) (odd_card_oddCoreOfCentralizer r)
    fun n hn y hy => (mem_centralizer_iff.mp (hLN hy) n hn)
  rw [← map_oddResidualIn _ (MulAut.conj x).injective]
  exact map_mono H.le_oddResidualIn

theorem conjugate_le_normalizer (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hLO : L ≤ centralizer (oddCoreIn L : Set G))
    (htr : ∀ r ∈ conjugate (S ⊓ L) s, orderOf r = 2 → ∀ n ∈ oddCent r, n * t = t * n) :
    conjugate L s ≤ normalizer (L : Set G) := by
  have h1 : L ≤ conjugate (normalizer (L : Set G)) s⁻¹ := by
    refine H.le_of_forall_inf_centralizer_le hK hcalc fun r hr hr2 x hx => ?_
    obtain ⟨-, hxr⟩ := mem_inf.mp hx
    rw [mem_conjugate_iff, inv_inv]
    have hr' : s⁻¹ * r * s ∈ conjugate (S ⊓ L) s := conj_inv_mem_conjugate hr
    have hr'2 : orderOf (s⁻¹ * r * s) = 2 := by
      rw [show s⁻¹ * r * s = s⁻¹ * r * s⁻¹⁻¹ by rw [inv_inv], orderOf_conj', hr2]
    refine H.centralizer_le_normalizer_of_mem_Rs hLO hr' hr'2 (htr _ hr' hr'2) ?_
    rw [mem_centralizer_singleton_iff] at hxr ⊢
    calc s⁻¹ * x * s * (s⁻¹ * r * s) = s⁻¹ * (x * r) * s := by group
      _ = s⁻¹ * (r * x) * s := by rw [hxr]
      _ = s⁻¹ * r * s * (s⁻¹ * x * s) := by group
  intro y hy
  rw [mem_conjugate_iff] at hy
  have h2 := h1 hy
  rw [mem_conjugate_iff, inv_inv] at h2
  rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h2

theorem normalizer_conjugate_le (hLs : conjugate L s ≤ normalizer (L : Set G)) :
    normalizer (conjugate L s : Set G) ≤ normalizer (L : Set G) := by
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  intro x hx
  have hzLs : z ∈ conjugate L s := by rw [mem_conjugate_iff, H.conj_s_z]; exact H.sec5.tL
  have h1 : x * z * x⁻¹ ∈ conjugate L s := (mem_normalizer_iff.mp hx z).mp hzLs
  have h2 : s * (x * z * x⁻¹) * s⁻¹ ∈ L := mem_conjugate_iff.mp h1
  have h3 : orderOf (s * (x * z * x⁻¹) * s⁻¹) = 2 := by
    rw [orderOf_conj', orderOf_conj', H.sec5.z2]
  obtain ⟨k, hkL, -, hk⟩ := exists_conj_of_involutions (W := ⊥) H.sec5.quotient_nonabelian
    H.sec5.hasDihedralSylowTwo_quotient IsPGroup.of_bot bot_le h2 H.sec5.tL h3 H.sec5.t2
    (mem_centralizer_bot _) (mem_centralizer_bot _)
  set l := s⁻¹ * k * s with hl
  have hlLs : l ∈ conjugate L s := by
    rw [mem_conjugate_iff, hl, show s * (s⁻¹ * k * s) * s⁻¹ = k by group]
    exact hkL
  have hlz : (x⁻¹ * l)⁻¹ * z * (x⁻¹ * l) = z := by
    calc (x⁻¹ * l)⁻¹ * z * (x⁻¹ * l) = s⁻¹ * (k⁻¹ * (s * (x * z * x⁻¹) * s⁻¹) * k) * s := by
          rw [hl]; group
      _ = z := by rw [hk, H.conj_s_inv_t]
  have hxl : x⁻¹ * l ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc x⁻¹ * l * z = x⁻¹ * l * ((x⁻¹ * l)⁻¹ * z * (x⁻¹ * l)) := by rw [hlz]
      _ = z * (x⁻¹ * l) := by group
  rw [show x = l * (x⁻¹ * l)⁻¹ by group]
  exact mul_mem (hLs hlLs) (inv_mem (H.sec5.centralizer_le_normalizer hxl))

theorem centralizer_t_le_normalizer_conjugate :
    centralizer ({t} : Set G) ≤ normalizer (conjugate L s : Set G) := by
  intro x hx
  have h1 : s * x * s⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    rw [← H.conj_s_t]
    calc s * x * s⁻¹ * (s * t * s⁻¹) = s * (x * t) * s⁻¹ := by group
      _ = s * (t * x) * s⁻¹ := by rw [hx]
      _ = s * t * s⁻¹ * (s * x * s⁻¹) := by group
  have h2 := H.sec5.centralizer_le_normalizer h1
  rw [mem_normalizer_iff]
  intro y
  rw [mem_conjugate_iff, mem_conjugate_iff,
    show s * (x * y * x⁻¹) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) * (s * x * s⁻¹)⁻¹ by group]
  exact mem_normalizer_iff.mp h2 _

theorem isDihedralTwoGroup_R : AschbacherTheorem3.IsDihedralTwoGroup (S ⊓ L) := by
  obtain ⟨m, hm1, ⟨eD⟩⟩ := H.sec5.exists_dihedral_R
  exact ⟨m + 1, by omega, ⟨eD⟩⟩

theorem four_lt_card_R : 4 < Nat.card ↥(S ⊓ L) := by
  obtain ⟨ρ, b', j, hD, -⟩ := H.exists_dihData_R
  rw [card_eq_two_mul hD, hD.ord]
  have : 0 < 2 ^ j := by positivity
  omega

theorem false_of_centralizer_t_le (h3 : Asc76.Asc76Theorem3Large)
    (hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) : False := by
  have : IsSimpleGroup G := H.sec5.sec4.simple
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  have hTE := tightlyEmbedded_of_centralizer_le H.sec5.quotient_nonabelian
    H.sec5.hasDihedralSylowTwo_quotient H.sec5.tL H.sec5.t2 hCt
  obtain ⟨a, -, b, -, hab⟩ := H.nonab
  have hcen : center G = ⊥ := center_eq_bot_of_isSimpleGroup ⟨a, b, hab⟩
  have hL1 : L ≠ ⊥ := fun h => H.t_ne_one (by
    have h1 := H.sec5.tL
    rw [h] at h1
    exact mem_bot.mp h1)
  have hLtop : L ≠ ⊤ := fun h => H.z_ne_one (by
    have hzc : z ∈ center G := mem_center_iff.mpr fun g =>
      mem_centralizer_singleton_iff.mp (H.sec5.zL.2.1 (h ▸ mem_top g))
    rwa [hcen, mem_bot] at hzc)
  exact false_of_tightlyEmbedded h3 hab hTE hL1 hLtop H.sec5.R_sylow H.isDihedralTwoGroup_R
    H.four_lt_card_R

theorem false_of_commutator_eq_bot (h3 : Asc76.Asc76Theorem3Large)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hW : ∀ r ∈ conjugate (S ⊓ L) s, orderOf r = 2 → ⁅oddCent r, zpowers t⁆ = ⊥) : False := by
  have htz := commute_of_commutator_eq_bot (hW z H.z_mem_Rs H.sec5.z2)
  have hLO := H.le_centralizer_oddCoreIn htz
  have hLs := H.conjugate_le_normalizer hK hcalc hLO fun r hr hr2 =>
    commute_of_commutator_eq_bot (hW r hr hr2)
  exact H.false_of_centralizer_t_le h3
    (H.centralizer_t_le_normalizer_conjugate.trans (H.normalizer_conjugate_le hLs))

end Hyp

end CFSG.ComponentClassification.Sol78.F514
