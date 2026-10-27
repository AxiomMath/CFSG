module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Coord
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5VLike

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

namespace Sec3

structure RCoords (L T R R₂ : Subgroup G) (a : ℕ) (v : G → BinaryGaloisField (2 * a + 1))
    (φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1))
    (c e : BinaryGaloisField (2 * a + 1)) (Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))) :
    Prop where
  v_mul : ∀ b ∈ gmsA L T, ∀ b' ∈ gmsA L T, v (b * b') = v b + v b'
  v_inj : ∀ b ∈ gmsA L T, v b = 0 → b = 1
  v_surj : ∀ w, ∃ b ∈ gmsA L T, v b = w
  mul : ∀ x ∈ R, ∀ x' ∈ R, φ (x * x') = φ x + φ x'
  ker : ∀ x ∈ R, φ x = 0 ↔ x ∈ gmsA L T
  mem : ∀ x ∈ R, (φ x).2.2 ∈ Λ
  surj : ∀ z, z.2.2 ∈ Λ → ∃ x ∈ R, φ x = z
  of_T₁ : ∀ t ∈ T ⊓ L, (φ t).2.1 = 0 ∧ (φ t).2.2 = 0
  of_R₂ : ∀ r ∈ R₂, (φ r).1 = 0 ∧ (φ r).2.2 = 0
  of_T₀ : ∀ s ∈ T ⊓ centralizer (L : Set G), (φ s).1 = 0 ∧ (φ s).2.1 = 0
  T₀_surj : ∀ w ∈ Λ, ∃ s ∈ T ⊓ centralizer (L : Set G), φ s = (0, 0, w)
  R₂_surj : ∀ w, ∃ r ∈ R₂, φ r = (0, w, 0)
  card : Nat.card Λ = Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G)
  sq : ∀ x ∈ R, v (x ^ 2) = VLike.sqMap a c e (φ x)
  comm : ∀ x ∈ R, ∀ x' ∈ R, v (x * x' * x⁻¹ * x'⁻¹) = VLike.commMap a c (φ x) (φ x')

namespace SzR

variable {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}

theorem exists_decomp
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d) {x : G}
    (hx : x ∈ R) :
    ∃ t ∈ T ⊓ L, ∃ r ∈ R₂, ∃ s ∈ T ⊓ centralizer (L : Set G), t * r * s = x := by
  obtain ⟨x₀, hx₀, s, hs, rfl⟩ := hS.exists_mul_of_mem_R h34 hR₂ hx
  obtain ⟨t, ht, r, hr, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer
    ((inf_le_left.trans hS.T_le).trans (hS.le_normalizer_R₂ h34 hR₂)) hx₀
  exact ⟨t, ht, r, hr, s, hs, rfl⟩

theorem eq_one_of_mul_eq (hS : SzR G L T R a y d) (hR₂ : IsR₂ L T R R₂ d) {t r s : G}
    (ht : t ∈ T ⊓ L) (hr : r ∈ R₂) (hs : s ∈ T ⊓ centralizer (L : Set G)) (h : t * r = s) :
    s = 1 := by
  have hrT : r ∈ T := by
    have e : r = t⁻¹ * s := by rw [← h]; group
    rw [e]
    exact mul_mem (inv_mem (mem_inf.mp ht).1) (mem_inf.mp hs).1
  have hrA : r ∈ gmsA L T := by rw [← hR₂.inf_eq]; exact mem_inf.mpr ⟨hrT, hr⟩
  have hs' : s ∈ (T ⊓ L) ⊓ (T ⊓ centralizer (L : Set G)) :=
    mem_inf.mpr ⟨h ▸ mul_mem ht (mem_inf.mp hrA).1, hs⟩
  rw [hS.sec3.inf_eq_bot_of_odd hS.oddCenter, mem_bot] at hs'
  exact hs'

theorem decomp_unique
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    {t r s t' r' s' : G} (ht : t ∈ T ⊓ L) (hr : r ∈ R₂) (hs : s ∈ T ⊓ centralizer (L : Set G))
    (ht' : t' ∈ T ⊓ L) (hr' : r' ∈ R₂) (hs' : s' ∈ T ⊓ centralizer (L : Set G))
    (h : t * r * s = t' * r' * s') : s = s' ∧ t⁻¹ * t' ∈ gmsA L T := by
  have hN : T ⊓ L ≤ normalizer (R₂ : Set G) :=
    (inf_le_left.trans hS.T_le).trans (hS.le_normalizer_R₂ h34 hR₂)
  have h1 : s' * s⁻¹ ∈ gmsR₀ L T R₂ := by
    have e : s' * s⁻¹ = (t' * r')⁻¹ * (t * r) := by
      have e' : s' = (t' * r')⁻¹ * (t * r * s) := by rw [h]; group
      rw [e']
      group
    rw [e]
    exact mul_mem (inv_mem (mul_mem (mem_sup_left ht') (mem_sup_right hr')))
      (mul_mem (mem_sup_left ht) (mem_sup_right hr))
  obtain ⟨t₂, ht₂, r₂, hr₂, he⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hN h1
  have hss := hS.eq_one_of_mul_eq hR₂ ht₂ hr₂ (mul_mem hs' (inv_mem hs)) he
  have hs_eq : s' = s := mul_inv_eq_one.mp hss
  subst hs_eq
  have h2 : t * r = t' * r' := mul_right_cancel h
  have h3 : t'⁻¹ * t = r' * r⁻¹ := by
    calc t'⁻¹ * t = t'⁻¹ * (t * r) * r⁻¹ := by group
      _ = t'⁻¹ * (t' * r') * r⁻¹ := by rw [h2]
      _ = r' * r⁻¹ := by group
  have h4 : t'⁻¹ * t ∈ gmsA L T := by
    rw [← hR₂.inf_eq]
    refine mem_inf.mpr ⟨mul_mem (inv_mem (mem_inf.mp ht').1) (mem_inf.mp ht).1, ?_⟩
    rw [h3]
    exact mul_mem hr' (inv_mem hr)
  refine ⟨rfl, ?_⟩
  simpa using inv_mem h4

theorem exists_rCoords
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d) :
    ∃ (v : G → BinaryGaloisField (2 * a + 1))
      (φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
        BinaryGaloisField (2 * a + 1))
      (c e : BinaryGaloisField (2 * a + 1)) (Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))),
      RCoords L T R R₂ a v φ c e Λ := by
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  obtain ⟨u, v, κ, hc, hμ⟩ := hS.exists_rootCoords
  obtain ⟨⟨s₀, hs₀⟩, hs₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS.sec3.T₀_ne_bot
  have hs₀1' : s₀ ≠ 1 := fun h => hs₀1 (Subtype.ext h)
  obtain ⟨lam, hlam⟩ := hS.exists_lam hR₂ hc hs₀ hs₀1' hμ
  obtain ⟨e, he⟩ := hS.exists_e h34 hR₂ hc hs₀ hs₀1' hμ
  obtain ⟨c, hcc⟩ := hS.exists_c h34 hR₂ hc hs₀ hs₀1' hμ
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  have hT₀el := hS.sec3.isElemAbelian_T₀ hS.foundation
  have hcomm : ∀ x ∈ R, ∀ z ∈ R, x * z * x⁻¹ * z⁻¹ ∈ gmsA L T := fun x hx z hz =>
    hS.commutator_mem_gmsA h34 hx hz
  obtain ⟨ρ, hρ⟩ : ∃ ρ : G → BinaryGaloisField (2 * a + 1),
      ∀ x, ρ x = v (x * s₀ * x⁻¹ * s₀⁻¹) := ⟨_, fun _ => rfl⟩
  simp only [← hρ] at hlam he hcc
  have hρmul : ∀ x ∈ R, ∀ x' ∈ R, ρ (x * x') = ρ x + ρ x' := fun x hx x' hx' => by
    simp only [hρ]; exact hS.rho_mul hc hs₀ hx hx'
  have hρT : ∀ x ∈ T, ρ x = 0 := fun x hx => by
    rw [hρ]; exact hS.rho_eq_zero_of_mem_T hc hs₀ hx
  have hρzero : ∀ r ∈ R₂, ρ r = 0 ↔ r ∈ gmsA L T := fun r hr => by
    rw [hρ]; exact hS.rho_eq_zero_iff hc hs₀ hR₂ hs₀1' hr
  have hρsurj : ∀ w, ∃ r ∈ R₂, ρ r = w := fun w => by
    simp only [hρ]; exact hS.exists_rho_eq hc hs₀ hR₂ hs₀1' w
  obtain ⟨r₁, hr₁, hr₁ρ⟩ := hρsurj 1
  have hr₁R := hR₂.le_R hr₁
  have hlam_mul : ∀ s ∈ T ⊓ centralizer (L : Set G), ∀ s' ∈ T ⊓ centralizer (L : Set G),
      lam (s * s') = lam s + lam s' := by
    intro s hs s' hs'
    have hsR := hS.T_le (mem_inf.mp hs).1
    have hs'R := hS.T_le (mem_inf.mp hs').1
    have h1 := hlam _ (mul_mem hs hs') r₁ hr₁
    rw [hS.commutator_mul_right h34 hr₁R hsR hs'R, hS.v_mul_gmsA hc (hcomm _ hr₁R _ hsR)
      (hcomm _ hr₁R _ hs'R), hlam s hs r₁ hr₁, hlam s' hs' r₁ hr₁, hr₁ρ] at h1
    linear_combination -h1
  have hlam_one : lam 1 = 0 := by
    have h := hlam_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hlam_zero : ∀ s ∈ T ⊓ centralizer (L : Set G), lam s = 0 → s = 1 := by
    intro s hs h0
    by_contra hs1
    obtain ⟨r, hr, hrA⟩ := hS.exists_mem_isR₂_not_mem_gmsA hR₂
    apply hrA
    rw [← hS.commutator_eq_one_iff hR₂ hs hs1 hr]
    exact hS.eq_one_of_v_eq_zero hc (conj_mul_inv_mem (hS.isR.le_gmsTrans (hR₂.le_R hr))
      (mem_sup_right hs)) (by rw [hlam s hs r hr, h0, zero_mul])
  have hlam_inj : ∀ s ∈ T ⊓ centralizer (L : Set G), ∀ s' ∈ T ⊓ centralizer (L : Set G),
      lam s = lam s' → s = s' := by
    intro s hs s' hs' h
    have h1 := hlam_mul s hs s' hs'
    rw [h] at h1
    have h4 := hlam_zero _ (mul_mem hs hs') (by rw [h1]; exact CharTwo.add_self_eq_zero _)
    have hs2 : s ^ 2 = 1 := hT₀el.2 s hs
    rw [eq_inv_of_mul_eq_one_right h4, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hs2)]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : AddSubgroup (BinaryGaloisField (2 * a + 1)),
      ∀ w, w ∈ Λ ↔ ∃ s ∈ T ⊓ centralizer (L : Set G), lam s = w :=
    ⟨{ carrier := {w | ∃ s ∈ T ⊓ centralizer (L : Set G), lam s = w}
       add_mem' := by
         rintro _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
         exact ⟨s * s', mul_mem hs hs', hlam_mul s hs s' hs'⟩
       zero_mem' := ⟨1, one_mem _, hlam_one⟩
       neg_mem' := by
         rintro _ ⟨s, hs, rfl⟩
         exact ⟨s, hs, (CharTwo.neg_eq _).symm⟩ }, fun w => Iff.rfl⟩
  choose! tc htc rc hrc sc hsc htrs using fun x (hx : x ∈ R) => hS.exists_decomp h34 hR₂ hx
  have hφu : ∀ x ∈ R, ∀ t ∈ T ⊓ L, ∀ r ∈ R₂, ∀ s ∈ T ⊓ centralizer (L : Set G),
      t * r * s = x → u (tc x) = u t ∧ sc x = s := by
    intro x hx t ht r hr s hs hx'
    obtain ⟨hs', hb⟩ := hS.decomp_unique h34 hR₂ (htc x hx) (hrc x hx) (hsc x hx) ht hr hs
      ((htrs x hx).trans hx'.symm)
    refine ⟨?_, hs'⟩
    have hu := hS.u_eq_zero_of_mem_gmsA hc hb
    rw [(hc.mul _ (inv_mem (htc x hx)) _ ht).1, (hc.inv (htc x hx)).1] at hu
    linear_combination hu - u t * h2
  have hρx : ∀ x ∈ R, ρ (rc x) = ρ x := by
    intro x hx
    have htR := hS.T_le (mem_inf.mp (htc x hx)).1
    have hsR := hS.T_le (mem_inf.mp (hsc x hx)).1
    conv_rhs => rw [← htrs x hx]
    rw [hρmul _ (mul_mem htR (hR₂.le_R (hrc x hx))) _ hsR, hρmul _ htR _ (hR₂.le_R (hrc x hx)),
      hρT _ (mem_inf.mp (htc x hx)).1, hρT _ (mem_inf.mp (hsc x hx)).1]
    ring
  have hv0 : ∀ x z, x * z = z * x → v (x * z * x⁻¹ * z⁻¹) = 0 := fun x z h => by
    have e : x * z * x⁻¹ * z⁻¹ = 1 := by rw [h]; group
    rw [e, hc.v_one]
  have hvs : ∀ x ∈ R, ∀ z ∈ R, v (z * x * z⁻¹ * x⁻¹) = v (x * z * x⁻¹ * z⁻¹) := by
    intro x hx z hz
    have e : z * x * z⁻¹ * x⁻¹ = (x * z * x⁻¹ * z⁻¹)⁻¹ := by group
    rw [e, hS.v_inv_gmsA hc (hcomm _ hx _ hz)]
  have hsq : ∀ t ∈ T ⊓ L, ∀ r ∈ R₂, ∀ s ∈ T ⊓ centralizer (L : Set G),
      v ((t * r * s) ^ 2) = VLike.sqMap a c e (u t, ρ r, lam s) := by
    intro t ht r hr s hs
    have htR := hS.T_le (mem_inf.mp ht).1
    have hrR := hR₂.le_R hr
    have hsR := hS.T_le (mem_inf.mp hs).1
    have hts : t * s = s * t := mem_centralizer_iff.mp (mem_inf.mp hs).2 t (mem_inf.mp ht).2
    rw [hS.sq_mul h34 (mul_mem htR hrR) hsR, hS.sq_mul h34 htR hrR, hT₀el.2 s hs, mul_one,
      hS.commutator_mul_left h34 htR hrR hsR]
    have e1 : t * s * t⁻¹ * s⁻¹ = 1 := by rw [hts]; group
    have ht2 := hS.facts.sq_mem t ht
    have hr2 := hS.sq_mem_gmsA_of_mem_R h34 hX hrR
    rw [e1, one_mul, hS.v_mul_gmsA hc (hcomm _ hrR _ hsR)
      (mul_mem (mul_mem (hcomm _ htR _ hrR) ht2) hr2),
      hS.v_mul_gmsA hc (mul_mem (hcomm _ htR _ hrR) ht2) hr2,
      hS.v_mul_gmsA hc (hcomm _ htR _ hrR) ht2, hlam s hs r hr, hcc t ht r hr, (hc.sq ht).2,
      he r hr]
    simp only [VLike.sqMap]
    ring
  have hcm : ∀ t ∈ T ⊓ L, ∀ r ∈ R₂, ∀ s ∈ T ⊓ centralizer (L : Set G),
      ∀ t' ∈ T ⊓ L, ∀ r' ∈ R₂, ∀ s' ∈ T ⊓ centralizer (L : Set G),
      v (t * r * s * (t' * r' * s') * (t * r * s)⁻¹ * (t' * r' * s')⁻¹) =
        VLike.commMap a c (u t, ρ r, lam s) (u t', ρ r', lam s') := by
    intro t ht r hr s hs t' ht' r' hr' s' hs'
    have htR := hS.T_le (mem_inf.mp ht).1
    have hrR := hR₂.le_R hr
    have hsR := hS.T_le (mem_inf.mp hs).1
    have ht'R := hS.T_le (mem_inf.mp ht').1
    have hr'R := hR₂.le_R hr'
    have hs'R := hS.T_le (mem_inf.mp hs').1
    have hz : t' * r' * s' ∈ R := mul_mem (mul_mem ht'R hr'R) hs'R
    have hL : v (t * r * s * (t' * r' * s') * (t * r * s)⁻¹ * (t' * r' * s')⁻¹) =
        v (t * (t' * r' * s') * t⁻¹ * (t' * r' * s')⁻¹) +
          v (r * (t' * r' * s') * r⁻¹ * (t' * r' * s')⁻¹) +
            v (s * (t' * r' * s') * s⁻¹ * (t' * r' * s')⁻¹) := by
      rw [hS.commutator_mul_left h34 (mul_mem htR hrR) hsR hz,
        hS.commutator_mul_left h34 htR hrR hz,
        hS.v_mul_gmsA hc (mul_mem (hcomm _ htR _ hz) (hcomm _ hrR _ hz)) (hcomm _ hsR _ hz),
        hS.v_mul_gmsA hc (hcomm _ htR _ hz) (hcomm _ hrR _ hz)]
    have hR' : ∀ α ∈ R, v (α * (t' * r' * s') * α⁻¹ * (t' * r' * s')⁻¹) =
        v (α * t' * α⁻¹ * t'⁻¹) + v (α * r' * α⁻¹ * r'⁻¹) + v (α * s' * α⁻¹ * s'⁻¹) := by
      intro α hα
      rw [hS.commutator_mul_right h34 hα (mul_mem ht'R hr'R) hs'R,
        hS.commutator_mul_right h34 hα ht'R hr'R,
        hS.v_mul_gmsA hc (mul_mem (hcomm _ hα _ ht'R) (hcomm _ hα _ hr'R)) (hcomm _ hα _ hs'R),
        hS.v_mul_gmsA hc (hcomm _ hα _ ht'R) (hcomm _ hα _ hr'R)]
    have hts' : t * s' = s' * t := mem_centralizer_iff.mp (mem_inf.mp hs').2 t (mem_inf.mp ht).2
    have hst' : s * t' = t' * s :=
      (mem_centralizer_iff.mp (mem_inf.mp hs).2 t' (mem_inf.mp ht').2).symm
    have hss' : s * s' = s' * s :=
      congrArg Subtype.val (hT₀el.1.is_comm.comm ⟨s, hs⟩ ⟨s', hs'⟩)
    rw [hL, hR' t htR, hR' r hrR, hR' s hsR, (hc.comm ht ht').2, hcc t ht r' hr', hv0 _ _ hts',
      hvs t' ht'R r hrR, hcc t' ht' r hr, hv0 _ _ (hS.commute_of_isR₂ h34 hR₂ hr hr'),
      hlam s' hs' r hr, hv0 _ _ hst', hvs r' hr'R s hsR, hlam s hs r' hr', hv0 _ _ hss']
    simp only [VLike.commMap]
    ring
  refine ⟨v, fun x => (u (tc x), ρ x, lam (sc x)), c, e, Λ,
    ⟨fun b hb b' hb' => hS.v_mul_gmsA hc hb hb', fun b hb h => hS.eq_one_of_v_eq_zero hc hb h,
      hS.exists_v_eq hc, ?_, ?_, fun x hx => (hΛ _).mpr ⟨sc x, hsc x hx, rfl⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro x hx x' hx'
    have ht := htc x hx
    have hs := hsc x hx
    have ht' := htc x' hx'
    have hs' := hsc x' hx'
    have hN := hS.le_normalizer_R₂ h34 hR₂
    have hρ₀ : (tc x')⁻¹ * rc x * tc x' * (sc x * rc x' * (sc x)⁻¹) ∈ R₂ := by
      refine mul_mem ?_ ((mem_normalizer_iff.mp (hN (hS.T_le (mem_inf.mp hs).1)) _).mp
        (hrc x' hx'))
      simpa using (mem_normalizer_iff.mp (hN (inv_mem (hS.T_le (mem_inf.mp ht').1))) _).mp
        (hrc x hx)
    have hts : tc x' * sc x = sc x * tc x' :=
      mem_centralizer_iff.mp (mem_inf.mp hs).2 _ (mem_inf.mp ht').2
    have e : x * x' = tc x * tc x' * ((tc x')⁻¹ * rc x * tc x' * (sc x * rc x' * (sc x)⁻¹)) *
        (sc x * sc x') := by
      calc x * x' = tc x * rc x * sc x * (tc x' * rc x' * sc x') := by
            rw [htrs x hx, htrs x' hx']
        _ = tc x * rc x * (sc x * tc x') * rc x' * sc x' := by group
        _ = tc x * rc x * (tc x' * sc x) * rc x' * sc x' := by rw [hts]
        _ = _ := by group
    obtain ⟨hu, hsc'⟩ := hφu (x * x') (mul_mem hx hx') _ (mul_mem ht ht') _ hρ₀ _
      (mul_mem hs hs') e.symm
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show u (tc (x * x')) = u (tc x) + u (tc x')
      rw [hu, (hc.mul _ ht _ ht').1]
    · exact hρmul x hx x' hx'
    · show lam (sc (x * x')) = lam (sc x) + lam (sc x')
      rw [hsc', hlam_mul _ hs _ hs']
  ·
    intro x hx
    constructor
    · intro h
      have h1 : u (tc x) = 0 := congrArg Prod.fst h
      have h3 : ρ x = 0 := congrArg (fun p => p.2.1) h
      have h4 : lam (sc x) = 0 := congrArg (fun p => p.2.2) h
      have htA : tc x ∈ gmsA L T := (hc.mem_center_iff hS.one_le (htc x hx)).mpr h1
      have hrA : rc x ∈ gmsA L T := (hρzero _ (hrc x hx)).mp (by rw [hρx x hx]; exact h3)
      rw [← htrs x hx, hlam_zero _ (hsc x hx) h4, mul_one]
      exact mul_mem htA hrA
    · intro h
      obtain ⟨hu, hs1⟩ := hφu x hx x (mem_inf.mp h).1 1 (one_mem _) 1 (one_mem _) (by group)
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show u (tc x) = 0
        rw [hu]
        exact hS.u_eq_zero_of_mem_gmsA hc h
      · exact hρT x (gmsA_le_T h)
      · show lam (sc x) = 0
        rw [hs1, hlam_one]
  ·
    intro z hz
    obtain ⟨s, hs, hsz⟩ := (hΛ _).mp hz
    obtain ⟨t, ht, htu, -⟩ := hc.surj z.1 0
    obtain ⟨r, hr, hrz⟩ := hρsurj z.2.1
    have htR := hS.T_le (mem_inf.mp ht).1
    have hsR := hS.T_le (mem_inf.mp hs).1
    have hx : t * r * s ∈ R := mul_mem (mul_mem htR (hR₂.le_R hr)) hsR
    obtain ⟨hu, hs'⟩ := hφu _ hx t ht r hr s hs rfl
    refine ⟨t * r * s, hx, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
    · show u (tc (t * r * s)) = z.1
      rw [hu, htu]
    · show ρ (t * r * s) = z.2.1
      rw [hρmul _ (mul_mem htR (hR₂.le_R hr)) _ hsR, hρmul _ htR _ (hR₂.le_R hr),
        hρT _ (mem_inf.mp ht).1, hρT _ (mem_inf.mp hs).1, hrz]
      ring
    · show lam (sc (t * r * s)) = z.2.2
      rw [hs', hsz]
  ·
    intro t ht
    obtain ⟨-, hs1⟩ := hφu t (hS.T_le (mem_inf.mp ht).1) t ht 1 (one_mem _) 1 (one_mem _)
      (by group)
    exact ⟨hρT t (mem_inf.mp ht).1, by rw [hs1]; exact hlam_one⟩
  ·
    intro r hr
    obtain ⟨hu, hs1⟩ := hφu r (hR₂.le_R hr) 1 (one_mem _) r hr 1 (one_mem _) (by group)
    exact ⟨by rw [hu]; exact hc.u_one, by rw [hs1]; exact hlam_one⟩
  ·
    intro s hs
    obtain ⟨hu, -⟩ := hφu s (hS.T_le (mem_inf.mp hs).1) 1 (one_mem _) 1 (one_mem _) s hs
      (by group)
    exact ⟨by rw [hu]; exact hc.u_one, hρT s (mem_inf.mp hs).1⟩
  ·
    intro w hw
    obtain ⟨s, hs, rfl⟩ := (hΛ w).mp hw
    obtain ⟨hu, hs1⟩ := hφu s (hS.T_le (mem_inf.mp hs).1) 1 (one_mem _) 1 (one_mem _) s hs
      (by group)
    refine ⟨s, hs, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
    · show u (tc s) = 0
      rw [hu]; exact hc.u_one
    · exact hρT s (mem_inf.mp hs).1
    · show lam (sc s) = lam s
      rw [hs1]
  ·
    intro w
    obtain ⟨r, hr, hrw⟩ := hρsurj w
    obtain ⟨hu, hs1⟩ := hφu r (hR₂.le_R hr) 1 (one_mem _) r hr 1 (one_mem _) (by group)
    refine ⟨r, hr, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
    · show u (tc r) = 0
      rw [hu]; exact hc.u_one
    · exact hrw
    · show lam (sc r) = 0
      rw [hs1, hlam_one]
  ·
    refine (Nat.card_congr (Equiv.ofBijective (fun s : (T ⊓ centralizer (L : Set G) :
      Subgroup G) => (⟨lam s, (hΛ _).mpr ⟨s, s.2, rfl⟩⟩ : Λ)) ⟨fun s s' h => ?_, ?_⟩)).symm
    · exact Subtype.ext (hlam_inj s s.2 s' s'.2 (congrArg Subtype.val h))
    · rintro ⟨w, hw⟩
      obtain ⟨s, hs, rfl⟩ := (hΛ w).mp hw
      exact ⟨⟨s, hs⟩, rfl⟩
  ·
    intro x hx
    have h := hsq _ (htc x hx) _ (hrc x hx) _ (hsc x hx)
    rw [htrs x hx, hρx x hx] at h
    exact h
  ·
    intro x hx x' hx'
    have h := hcm _ (htc x hx) _ (hrc x hx) _ (hsc x hx) _ (htc x' hx') _ (hrc x' hx') _
      (hsc x' hx')
    rw [htrs x hx, htrs x' hx', hρx x hx, hρx x' hx'] at h
    exact h

end SzR

end Sec3

end CFSG.ComponentClassification.GMS78
