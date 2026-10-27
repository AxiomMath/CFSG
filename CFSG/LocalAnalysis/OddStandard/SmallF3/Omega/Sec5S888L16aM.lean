module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L16aStmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L16aD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L16aH
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888C41

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem l16a_twoCoreIn_le_Qsub (h514 : Asc82Lemma514)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : twoCoreIn (K₁ ⊔ K₂) ≤ Qsub K₁ K₂ h := by
  have hq := sec5b517_quad h514 c
  have hpair_eq := Sec5B517Q8.twoCoreIn_sup_eq_pair hq (i := 0) (j := 1) (by decide)
  rw [show Kfam5 K₁ K₂ h 0 = K₁ by simp [Kfam5], show Kfam5 K₁ K₂ h 1 = K₂ by simp [Kfam5]]
    at hpair_eq
  rw [hpair_eq, l16a_Qsub_eq h514 c]
  exact inf_le_left

private theorem l16a_t_mem_L (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ∈ L :=
  (sec5_mem_centerIn_iff.mp (by rw [c.centre]; exact Subgroup.mem_zpowers t)).1

private theorem l16a_centralizer_le_normalizer (h52a : Asc82Lemma52a)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    centralizer ({t} : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) := by
  have hconj : ∀ y ∈ centralizer ({t} : Set G), ∀ d ∈ centralizer (L : Set G),
      y * d * y⁻¹ ∈ centralizer (L : Set G) := by
    intro y hy d hd
    have hconjL : CFSG.conjugate L y = L := sec5_conj_L h52a c hy
    rw [Subgroup.mem_centralizer_iff] at hd ⊢
    intro l hl
    have hyl : y⁻¹ * l * y ∈ L := sec5b_mem_of_conjugate_eq' hconjL hl
    have hcomm := hd (y⁻¹ * l * y) hyl
    calc l * (y * d * y⁻¹) = y * ((y⁻¹ * l * y) * d) * y⁻¹ := by group
      _ = y * (d * (y⁻¹ * l * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * d * y⁻¹) * l := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    exact hconj x hx d hd
  · intro hd
    have h1 := hconj x⁻¹ (inv_mem hx) _ hd
    simpa [mul_assoc] using h1

theorem asc82Lemma516a_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (h514 : Asc82Lemma514) (h73 : Asc82CHdLeN) (hF3 : Asc82FactOm6CentD)
    (hHeart : Asc82HeartDict) (h511 : Asc82Lemma511CSL) : Asc82Lemma516a := by
  classical
  intro G _ _ t L S z r B A K₁ K₂ h c
  have hq := sec5b517_quad h514 c
  have hQeq : Qsub K₁ K₂ h = Sec5B517Q8 hq := l16a_Qsub_eq h514 c
  have htQ : t ∈ Qsub K₁ K₂ h := l16a_t_mem_Qsub h514 c
  have hQR : Qsub K₁ K₂ h ≤
      centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) :=
    qsub_le_centralizerMod h514 c
  have hUQ : oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (Qsub K₁ K₂ h : Set G) :=
    l16a_oddCore_le_centralizer_Q h36 h37 h514 h73 c
  have hzQ : z ∈ Qsub K₁ K₂ h := by rw [hQeq]; exact z_mem_Q8 hq
  have hUR : oddCoreIn (centralizer ({t} : Set G)) ≤
      centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) := by
    intro u hu
    have huQ := hUQ hu
    refine ⟨Subgroup.centralizer_le_normalizer _ huQ, ?_, Subgroup.centralizer_le_normalizer _ huQ,
      ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp huQ z hzQ).symm
    · intro q hqQ
      have hqu : q * u = u * q := Subgroup.mem_centralizer_iff.mp huQ q hqQ
      have h1 : u * q * u⁻¹ * q⁻¹ = 1 := by
        calc u * q * u⁻¹ * q⁻¹ = (u * q) * u⁻¹ * q⁻¹ := rfl
          _ = (q * u) * u⁻¹ * q⁻¹ := by rw [hqu]
          _ = 1 := by group
      rw [h1]
      exact (zpowers z).one_mem
  refine le_antisymm (sup_le hQR hUR) ?_
  intro g hgR
  obtain ⟨w, hwQ8, hw⟩ := Sec5B517Q8.exists_inner hq (g := g)
    (fun q hqQ => hgR.2.2.2 q (by rw [hQeq]; exact hqQ))
  have hwQ : w ∈ Qsub K₁ K₂ h := by rw [hQeq]; exact hwQ8
  have hg'Q : w⁻¹ * g ∈ centralizer (Qsub K₁ K₂ h : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hqQ
    have hqQ8 : q ∈ Sec5B517Q8 hq := by rw [← hQeq]; exact hqQ
    calc q * (w⁻¹ * g) = w⁻¹ * (w * q * w⁻¹) * g := by group
      _ = w⁻¹ * (g * q * g⁻¹) * g := by rw [← hw q hqQ8]
      _ = (w⁻¹ * g) * q := by group
  have hg't : w⁻¹ * g ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hg'Q t htQ).symm
  have hg'P : w⁻¹ * g ∈ centralizer ((twoCoreIn (K₁ ⊔ K₂) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (fun _ hx => l16a_twoCoreIn_le_Qsub h514 c hx) hg'Q
  obtain ⟨c₀, -, hc₀Q, -, hyD⟩ := c41 h514 h52a h37 hF3 c hg't hg'P
  have hyR : w⁻¹ * g * c₀⁻¹ ∈
      centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) :=
    mul_mem (mul_mem (inv_mem (hQR hwQ)) hgR) (inv_mem (hQR hc₀Q))
  have htL : t ∈ L := l16a_t_mem_L c
  have hDX : centralizer (L : Set G) ≤ centralizer ({t} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hd t htL).symm
  have hXN := l16a_centralizer_le_normalizer h52a c
  obtain ⟨o, hoD, s, hsSD, hyos⟩ := l16a_exists_oddCore_mul c.sylow hDX hXN
    (h52a G t L c.toSec5Setting) _ hyD
  have hoU : o ∈ oddCoreIn (centralizer ({t} : Set G)) :=
    oddCoreIn_le_of_normal hDX ((Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr hXN) hoD
  have hsR : s ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) := by
    have h1 := mul_mem (inv_mem (hUR hoU)) hyR
    rwa [hyos, inv_mul_cancel_left] at h1
  have hsQ : s ∈ Qsub K₁ K₂ h := by
    rcases h511 G t L S z r B A c.toSec5RCtx s hsSD with hst | ⟨hsN, hsA⟩
    · exact (Subgroup.zpowers_le.mpr htQ) hst
    · exact (l16a_heart_false h37 h514 hHeart c hsSD.2 hsN hsR.2.2.2 hsA).elim
  have hgeq : g = w * (o * s) * c₀ := by
    calc g = w * (w⁻¹ * g * c₀⁻¹) * c₀ := by group
      _ = w * (o * s) * c₀ := by rw [hyos]
  rw [hgeq]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hwQ)
    (mul_mem (Subgroup.mem_sup_right hoU) (Subgroup.mem_sup_left hsQ)))
    (Subgroup.mem_sup_left hc₀Q)

end CFSG.OddStandard.SmallF3.Omega
