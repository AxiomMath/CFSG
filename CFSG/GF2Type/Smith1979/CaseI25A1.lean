module

public import CFSG.GF2Type.Smith1979.CaseI25A2
public import CFSG.GF2Type.Smith1979.CaseICount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_conj)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Basic

theorem delta_subset_Lbar {t : S.O} (ht : t ∈ S.Lbar g) {x : S.O} (hx : x ∈ Delta S g t) :
    x ∈ S.Lbar g := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact (mem_normalizer_iff.mp hn.2 t).mp ht

theorem conj_mem_Delta {t : S.O} {n x : S.O} (hn : n ∈ NLbar S g) (hx : x ∈ Delta S g t) :
    n * x * n⁻¹ ∈ Delta S g t := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨n * m, mul_mem hn hm, by group⟩

@[expose] noncomputable def resLext {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG) (ht : t ∈ S.Lbar g)
    (x : S.O) : Vt S g t ≃ₗ[ZMod 2] Vt S g t :=
  open scoped Classical in
  if hx : x ∈ S.Lbar g then resL haQ ht ⟨x, hx⟩ else 1

theorem resLext_of_mem {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG) (ht : t ∈ S.Lbar g) {x : S.O}
    (hx : x ∈ S.Lbar g) : resLext haQ ht x = resL haQ ht ⟨x, hx⟩ := by
  unfold resLext
  exact dif_pos hx

end Basic

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
  {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
  (hpol : Q.polarBilin = beta H C ht ht1 hVQ) (hX : RmodN S g t = omegaGroup Q hQ)
  (hE : LmodN S g t = pointRadical Q (aV ht))
  (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
include hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing

theorem resL_delta_mem {x : S.O} (hx : x ∈ Delta S g t) (hxt : x ≠ t) :
    ∃ hxL : x ∈ S.Lbar g, ∃ α ∈ singPerp Q (aV ht),
      resL H.conj_mem ht ⟨x, hxL⟩ = eichler Q (aV ht) α := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hn.1
  rcases CaseIClosure.claimA H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hCE countSixStmt hn.2
    with h | ⟨-, α, hα0, hαa, hQα, hpolα, hx', hres⟩
  · exact absurd h hxt
  · exact ⟨hx', α, ⟨hpolα, hQα, hα0, hαa⟩, hres⟩

theorem ncard_singular_of_delta (hΔ : (Delta S g t).ncard = 6) :
    {v : Vt S g t | v ≠ 0 ∧ Q v = 0}.ncard = 27 := by
  obtain ⟨x, hx, hxt⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (Delta S g t).ncard) t
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hn.1
  rcases CaseIClosure.claimA H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hCE countSixStmt hn.2
    with h | ⟨h27, -⟩
  · exact absurd h hxt
  · exact h27

theorem delta_eichler_bij (hΔ : (Delta S g t).ncard = 6) :
    Set.BijOn (resLext H.conj_mem ht) (Delta S g t \ {t}) (eichlerFive Q (aV ht)) := by
  classical
  have h27 := ncard_singular_of_delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  have ha0 : aV ht ≠ 0 := aV_ne_zero H ht
  have ha : Q (aV ht) = 0 := CaseIClosure.Q_aV_eq_zero H ht hsing
  set Δ' : Set S.O := Delta S g t \ {t} with hΔ'
  have hΔ'card : Δ'.ncard = 5 := by
    have h : Δ'.ncard + 1 = (Delta S g t).ncard :=
      Set.ncard_sdiff_singleton_add_one (mem_Delta_self S g t) (Set.toFinite _)
    omega
  obtain ⟨cb, hcbΩ, hcba, hcb5, hcb1, hfix⟩ := CaseIClosure.exists_order_five h6 hQ ha0 ha h27
  have hcbR : cb ∈ RmodN S g t := hX ▸ hcbΩ
  obtain ⟨r, hr, hrcb⟩ := hcbR
  have hrv : resV H.conj_mem t ⟨r, hr⟩ = cb :=
    LinearEquiv.ext fun v => Subtype.ext (hrcb v).symm
  have hra : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    have := hrcb (aV ht)
    rw [hcba] at this
    exact this.symm
  have hrN : r ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) H.conj_mem H.conj_ne
      (Rbar_le_Mbar hr) (by simpa using hra)
    simpa using this
  have hrNL : r ∈ NLbar S g := ⟨Rbar_le_Mbar hr, hrN⟩
  have hrt : r * t = t * r := commute_of_mem_Rbar H.conj_mem hr
  have hmap : ∀ x ∈ Δ', resLext H.conj_mem ht x ∈ eichlerFive Q (aV ht) := by
    rintro x ⟨hx, hxt⟩
    obtain ⟨hxL, α, hα, hres⟩ :=
      resL_delta_mem hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hx hxt
    exact ⟨α, hα, by rw [resLext_of_mem H.conj_mem ht hxL, hres]⟩
  have hconjΔ : ∀ x ∈ Δ', r * x * r⁻¹ ∈ Δ' := by
    rintro x ⟨hx, hxt⟩
    refine ⟨conj_mem_Delta hrNL hx, fun h => hxt ?_⟩
    rw [Set.mem_singleton_iff] at h ⊢
    calc x = r⁻¹ * (r * x * r⁻¹) * r := by group
      _ = r⁻¹ * t * r := by rw [h]
      _ = t := by rw [mul_assoc, ← hrt, inv_mul_cancel_left]
  have hconjφ : ∀ x ∈ Δ', resLext H.conj_mem ht (r * x * r⁻¹) =
      cb * resLext H.conj_mem ht x * cb⁻¹ := by
    rintro x ⟨hx, hxt⟩
    have hxL := delta_subset_Lbar ht hx
    have hrxL : r * x * r⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hrN x).mp hxL
    rw [resLext_of_mem H.conj_mem ht hxL, resLext_of_mem H.conj_mem ht hrxL,
      CaseIClosure.resL_eq_resV H ht hxL, CaseIClosure.resL_eq_resV H ht hrxL]
    have : (⟨r * x * r⁻¹, Lbar_le_Rbar ht hrxL⟩ : Rbar S g t) =
        ⟨r, hr⟩ * ⟨x, Lbar_le_Rbar ht hxL⟩ * ⟨r, hr⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hrv]
  set B := resLext H.conj_mem ht '' Δ' with hB
  have hBE : B ⊆ eichlerFive Q (aV ht) := Set.image_subset_iff.mpr hmap
  have hE5 : (eichlerFive Q (aV ht)).ncard = 5 :=
    ncard_eichlerFive countSixStmt h6 hQ ha0 ha h27
  have hBpos : 0 < B.ncard := by
    refine (Set.ncard_pos (Set.toFinite _)).mpr ?_
    obtain ⟨x, hx⟩ : Δ'.Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
    exact ⟨resLext H.conj_mem ht x, x, hx, rfl⟩
  have hBle : B.ncard ≤ 5 := hE5 ▸ Set.ncard_le_ncard hBE (Set.toFinite _)
  have hB5 : 5 ∣ B.ncard := by
    refine CaseIClosure.five_dvd_ncard (Set.toFinite _) (fun x _ => by rw [hcb5]; simp) ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨r * x * r⁻¹, hconjΔ x hx, hconjφ x hx⟩
    · rintro y hy hcy
      obtain ⟨α, hα, rfl⟩ := hBE hy
      exact eichler_ne_one_of_mem_singPerp hQ ha0 ha hα
        (hfix _ (eichler_mem_pointRadical ha hα.1) hcy)
  have hBcard : B.ncard = 5 := by omega
  have hBeq : B = eichlerFive Q (aV ht) :=
    Set.eq_of_subset_of_ncard_le hBE (by omega) (Set.toFinite _)
  refine ⟨hmap, (Set.ncard_image_iff (Set.toFinite _)).mp (by show B.ncard = Δ'.ncard; omega), ?_⟩
  rw [← hBeq]
  exact fun y hy => hy

theorem closure_Delta_of_form (hΔ : (Delta S g t).ncard = 6) :
    closure (Delta S g t) = S.Lbar g := by
  classical
  have h27 := ncard_singular_of_delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  have ha0 : aV ht ≠ 0 := aV_ne_zero H ht
  have ha : Q (aV ht) = 0 := CaseIClosure.Q_aV_eq_zero H ht hsing
  have hbij := delta_eichler_bij hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  refine le_antisymm ((closure_le _).mpr fun x hx => delta_subset_Lbar ht hx) ?_
  intro l hl
  set Cl : Subgroup (S.Lbar g) := (closure (Delta S g t)).comap (S.Lbar g).subtype with hCl
  have hE5 : eichlerFive Q (aV ht) ⊆ (Cl.map (resL H.conj_mem ht) : Set _) := by
    rw [← hbij.image_eq]
    rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    refine ⟨⟨x, delta_subset_Lbar ht hx⟩, subset_closure hx, ?_⟩
    exact (resLext_of_mem H.conj_mem ht (delta_subset_Lbar ht hx)).symm
  have hPR : pointRadical Q (aV ht) ≤ Cl.map (resL H.conj_mem ht) := by
    rw [← closure_eichlerFive countSixStmt h6 hQ ha0 ha h27]
    exact (closure_le _).mpr hE5
  have hmem : resL H.conj_mem ht ⟨l, hl⟩ ∈ pointRadical Q (aV ht) := by
    rw [← hE, ← range_resL H.conj_mem ht]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy, hyl⟩ := hPR hmem
  have hyl' : resL H.conj_mem ht ⟨(y : S.O)⁻¹ * l, mul_mem (inv_mem y.2) hl⟩ = 1 := by
    have : (⟨(y : S.O)⁻¹ * l, mul_mem (inv_mem y.2) hl⟩ : S.Lbar g) = y⁻¹ * ⟨l, hl⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_inv, hyl, inv_mul_cancel]
  have hz := CaseIClosure.mem_zpowers_of_resL_eq_one H ht hN (mul_mem (inv_mem y.2) hl) hyl'
  have hyC : (y : S.O) ∈ closure (Delta S g t) := hy
  have hzC : (y : S.O)⁻¹ * l ∈ closure (Delta S g t) :=
    (zpowers_le.mpr (subset_closure (mem_Delta_self S g t))) hz
  have := mul_mem hyC hzC
  simpa using this

end Context

section NoForm

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem closure_Delta (hΔ : (Delta S g t).ncard = 6) :
    closure (Delta S g t) = S.Lbar g := by
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := hΩ.exists_form
  exact closure_Delta_of_form hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ

end NoForm

end Case25

end CFSG.GF2Type.Smith1979
