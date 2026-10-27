module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfCover
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.RankThree.PerfectCover

set_option linter.unusedSectionVars false


abbrev WP : Type := ↥wPlus

noncomputable abbrev sigmaO : MulAut omegaT := autEquiv rhoA

@[expose] noncomputable def YP : Subgroup (WP × WP) :=
  MonoidHom.eqLocus ((sigmaO.toMonoidHom.comp pHat).comp (MonoidHom.fst WP WP))
    (pHat.comp (MonoidHom.snd WP WP))

abbrev HY : Type := ↥YP

theorem mem_YP {x y : WP} : (x, y) ∈ YP ↔ sigmaO (pHat x) = pHat y := Iff.rfl

@[expose] noncomputable def qY : HY →* omegaT := pHat.comp ((MonoidHom.fst WP WP).comp YP.subtype)

theorem qY_apply (u : HY) : qY u = pHat (u : WP × WP).1 := rfl

theorem qY_surjective : Function.Surjective qY := by
  intro ω
  obtain ⟨x, rfl⟩ := pHat_surjective ω
  obtain ⟨y, hy⟩ := pHat_surjective (sigmaO (pHat x))
  exact ⟨⟨(x, y), mem_YP.2 hy.symm⟩, rfl⟩

private theorem md_pHat_eq_one {x : WP} : pHat x = 1 ↔ x = 1 ∨ x = zPlus := by
  have h := pHat_eq_iff (x := 1) (y := x)
  rw [map_one, one_mul] at h
  exact eq_comm.trans h

private theorem md_pHat_zPlus : pHat zPlus = 1 := md_pHat_eq_one.2 (Or.inr rfl)

private theorem md_zPlus_mul_self : zPlus * zPlus = 1 := Subtype.ext zPerm_mul_self

private theorem md_sq {a : WP} (h : a = 1 ∨ a = zPlus) : a * a = 1 := by
  rcases h with rfl | rfl
  · exact mul_one 1
  · exact md_zPlus_mul_self

private theorem md_comm {a : WP} (h : a = 1 ∨ a = zPlus) (g : WP) : g * a = a * g := by
  rcases h with rfl | rfl
  · rw [mul_one, one_mul]
  · exact Subgroup.mem_center_iff.1 zPlus_mem_center g

private theorem md_mem_YP {a b : WP} (ha : a = 1 ∨ a = zPlus) (hb : b = 1 ∨ b = zPlus) :
    (a, b) ∈ YP := by
  rw [mem_YP, md_pHat_eq_one.2 ha, md_pHat_eq_one.2 hb, map_one]

theorem mem_ker_qY {u : HY} : u ∈ qY.ker ↔
    ((u : WP × WP).1 = 1 ∨ (u : WP × WP).1 = zPlus) ∧ ((u : WP × WP).2 = 1 ∨ (u : WP × WP).2 = zPlus) := by
  obtain ⟨⟨x, y⟩, hu⟩ := u
  have hxy : sigmaO (pHat x) = pHat y := mem_YP.1 hu
  rw [MonoidHom.mem_ker, qY_apply]
  change pHat x = 1 ↔ (x = 1 ∨ x = zPlus) ∧ (y = 1 ∨ y = zPlus)
  rw [md_pHat_eq_one]
  constructor
  · intro hx
    refine ⟨hx, md_pHat_eq_one.1 ?_⟩
    rw [← hxy, md_pHat_eq_one.2 hx, map_one]
  · exact fun h => h.1

theorem ker_qY_le_center : qY.ker ≤ Subgroup.center HY := by
  intro u hu
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨h1, h2⟩ := mem_ker_qY.1 hu
  exact Subtype.ext (Prod.ext (md_comm h1 (g : WP × WP).1) (md_comm h2 (g : WP × WP).2))

private noncomputable def md_fst : HY →* WP := (MonoidHom.fst WP WP).comp YP.subtype

private theorem md_fst_surjective : Function.Surjective md_fst := by
  intro x
  obtain ⟨y, hy⟩ := pHat_surjective (sigmaO (pHat x))
  exact ⟨⟨(x, y), mem_YP.2 hy.symm⟩, rfl⟩

private theorem md_card_ker_fst : Nat.card md_fst.ker = 2 := by
  rw [Nat.card_eq_two_iff' (1 : md_fst.ker)]
  refine ⟨⟨⟨(1, zPlus), md_mem_YP (Or.inl rfl) (Or.inr rfl)⟩, rfl⟩, ?_, ?_⟩
  · intro h
    exact zPlus_ne_one (congrArg (fun z : md_fst.ker => ((z : HY) : WP × WP).2) h)
  · rintro ⟨⟨⟨a, b⟩, hab⟩, hk⟩ hne
    have ha : a = 1 := hk
    subst ha
    have hb : b = 1 ∨ b = zPlus := md_pHat_eq_one.1 (by
      have := mem_YP.1 hab
      rw [map_one, map_one] at this
      exact this.symm)
    rcases hb with rfl | rfl
    · exact absurd rfl hne
    · rfl

theorem card_YP : Nat.card YP = 696729600 := by
  have h : Nat.card md_fst.ker * Nat.card WP = Nat.card YP :=
    Subgroup.card_ker_mul_card_of_surjective md_fst_surjective
  rw [md_card_ker_fst, card_wPlus] at h
  omega

instance : Finite HY := inferInstance

private theorem md_ker_sq {k : HY} (hk : k ∈ qY.ker) : k * k = 1 := by
  obtain ⟨h1, h2⟩ := mem_ker_qY.1 hk
  exact Subtype.ext (Prod.ext (md_sq h1) (md_sq h2))

theorem isPerfect_HY : Group.IsPerfect HY := by
  have hperf : Group.IsPerfect omegaT := Cover.isPerfect_omegaT
  have hmap : (commutator HY).map qY = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ qY_surjective, ← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hdec : ∀ u : HY, ∃ d ∈ commutator HY, ∃ k ∈ qY.ker, u = d * k := by
    intro u
    have : qY u ∈ (commutator HY).map qY := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨d, hd, hdu⟩ := Subgroup.mem_map.1 this
    refine ⟨d, hd, d⁻¹ * u, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdu, inv_mul_cancel]
  have hsq : ∀ u : HY, u * u ∈ commutator HY := by
    intro u
    obtain ⟨d, hd, k, hk, rfl⟩ := hdec u
    have hc : d * k = k * d := Subgroup.mem_center_iff.1 (ker_qY_le_center hk) d
    have : d * k * (d * k) = d * d := by
      calc d * k * (d * k) = d * (k * d) * k := by group
        _ = d * (d * k) * k := by rw [← hc]
        _ = d * d * (k * k) := by group
        _ = d * d := by rw [md_ker_sq hk, mul_one]
    rw [this]
    exact mul_mem hd hd
  let e1 : HY := ⟨(zPlus, 1), md_mem_YP (Or.inr rfl) (Or.inl rfl)⟩
  let e2 : HY := ⟨(1, zPlus), md_mem_YP (Or.inl rfl) (Or.inr rfl)⟩
  have he2 : e2 ∈ commutator HY := by
    have hm : (uPlus, yPlus) ∈ YP := mem_YP.2 autEquiv_rhoA_uPlus
    have := hsq ⟨(uPlus, yPlus), hm⟩
    have heq : (⟨(uPlus, yPlus), hm⟩ * ⟨(uPlus, yPlus), hm⟩ : HY) = e2 :=
      Subtype.ext (Prod.ext uPlus_mul_self yPlus_mul_self)
    rwa [heq] at this
  have he1 : e1 ∈ commutator HY := by
    obtain ⟨v, hv⟩ := pHat_surjective (sigmaO (pHat yPlus))
    have hn : (yPlus, v) ∈ YP := mem_YP.2 hv.symm
    have hvv : pHat (v * v) = 1 := by
      rw [map_mul, hv, ← map_mul, ← map_mul, yPlus_mul_self, md_pHat_zPlus, map_one]
    have := hsq ⟨(yPlus, v), hn⟩
    rcases md_pHat_eq_one.1 hvv with h | h
    · have heq : (⟨(yPlus, v), hn⟩ * ⟨(yPlus, v), hn⟩ : HY) = e1 :=
        Subtype.ext (Prod.ext yPlus_mul_self h)
      rwa [heq] at this
    · have heq : (⟨(yPlus, v), hn⟩ * ⟨(yPlus, v), hn⟩ : HY) * e2 = e1 :=
        Subtype.ext (Prod.ext (by
          change yPlus * yPlus * 1 = zPlus
          rw [mul_one, yPlus_mul_self]) (by
          change v * v * zPlus = 1
          rw [h, md_zPlus_mul_self]))
      rw [← heq]
      exact mul_mem this he2
  have hker : ∀ k ∈ qY.ker, k ∈ commutator HY := by
    intro k hk
    obtain ⟨h1, h2⟩ := mem_ker_qY.1 hk
    obtain ⟨⟨a, b⟩, hab⟩ := k
    change a = 1 ∨ a = zPlus at h1
    change b = 1 ∨ b = zPlus at h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact one_mem _
    · exact he2
    · exact he1
    · have heq : (⟨(zPlus, zPlus), hab⟩ : HY) = e1 * e2 :=
        Subtype.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
      rw [heq]
      exact mul_mem he1 he2
  refine Group.isPerfect_def.2 (eq_top_iff.2 fun u _ => ?_)
  obtain ⟨d, hd, k, hk, rfl⟩ := hdec u
  exact mul_mem hd (hker k hk)

private noncomputable def md_L : HopfCover omegaT →* HY :=
  hopfLift qY qY_surjective ker_qY_le_center

private theorem md_L_surjective : Function.Surjective md_L :=
  haveI := isPerfect_HY
  hopfLift_surjective qY qY_surjective ker_qY_le_center

private theorem md_L_bijective : Function.Bijective md_L := by
  obtain ⟨hfin, hle⟩ := Cover.card_hopfCover_le
  haveI := hfin
  rw [Nat.bijective_iff_surjective_and_card]
  refine ⟨md_L_surjective, ?_⟩
  have h1 : Nat.card HY ≤ Nat.card (HopfCover omegaT) :=
    Nat.card_le_card_of_surjective _ md_L_surjective
  rw [card_omegaT] at hle
  have h2 : Nat.card HY = 696729600 := card_YP
  omega

noncomputable def hopfEquivY : Twin1711.ModOm2 ≃* HY :=
  MulEquiv.ofBijective md_L md_L_bijective

theorem qY_hopfEquivY (u : Twin1711.ModOm2) : qY (hopfEquivY u) = hopfCoverMap omegaT u :=
  DFunLike.congr_fun (comp_hopfLift qY qY_surjective ker_qY_le_center) u

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
