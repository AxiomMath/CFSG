module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81P5

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem rhoS_sigma_mem_centralizer (F : d.Facts) :
    rhoS d.sigma_mem_S ∈ centralizer ((Seven.rhoImg h.J h.D : Subgroup _) :
      Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨⟨e, heN⟩, he, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (d.D_comm_R0 F e (mem_subgroupOf.mp he) d.sigma sigma_mem_R0)

theorem rhoS_sigma_not_mem (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    rhoS d.sigma_mem_S ∉ Seven.rhoImg h.J h.D := by
  rintro ⟨⟨e, heN⟩, he, heq⟩
  have hσS := d.sigma_mem_S
  have heS : e ∈ h.S := h.toHyp52.D_le_S (mem_subgroupOf.mp he)
  have h1 : rhoS (mul_mem (inv_mem heS) hσS) = 1 := by
    show Eight.oddBarAction h.J ((⟨e, heN⟩ : ↥(normalizer (h.J : Set H)))⁻¹ *
      ⟨d.sigma, h.toHyp52.S_le_normalizer hσS⟩) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  have h2 := (rho_eq_one_iff (h := h) (mul_mem (inv_mem heS) hσS)).mp h1
  apply d.sigma_not_mem_DP hCF1 hCF2 F
  have h3 := mul_mem_sup (mem_subgroupOf.mp he) h2
  rwa [mul_inv_cancel_left] at h3

theorem rhoS_mem_commutator {u : H} (hu : u ∈ ⁅h.D, h.D⁆) (huS : u ∈ h.S) :
    rhoS huS ∈ ⁅Seven.rhoImg h.J h.D, Seven.rhoImg h.J h.D⁆ := by
  set K₀ : Subgroup H := (⁅Seven.rhoImg h.J h.D, Seven.rhoImg h.J h.D⁆.comap
    (Eight.oddBarAction h.J)).map (normalizer (h.J : Set H)).subtype with hK₀
  have hle : ⁅h.D, h.D⁆ ≤ K₀ := by
    rw [commutator_le]
    intro x hx y hy
    have hxS := h.toHyp52.D_le_S hx
    have hyS := h.toHyp52.D_le_S hy
    refine ⟨⁅(⟨x, h.toHyp52.S_le_normalizer hxS⟩ : ↥(normalizer (h.J : Set H))),
      ⟨y, h.toHyp52.S_le_normalizer hyS⟩⁆, ?_, rfl⟩
    show Eight.oddBarAction h.J _ ∈ ⁅Seven.rhoImg h.J h.D, Seven.rhoImg h.J h.D⁆
    rw [map_commutatorElement]
    exact commutator_mem_commutator (rhoS_mem hxS hx) (rhoS_mem hyS hy)
  obtain ⟨w, hw, hwu⟩ := mem_map.mp (hle hu)
  have : w = ⟨u, h.toHyp52.S_le_normalizer huS⟩ := Subtype.ext hwu
  rw [mem_comap, this] at hw
  exact hw

section Seven

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
include hv I F

theorem exists_U_conj_of_orbit {t t' : H} (hne : t' ≠ t)
    (hex : ∃ n ∈ normalizer (h.F32 : Set H), n⁻¹ * t * n = t')
    (hall : ∀ m ∈ normalizer (h.F32 : Set H), m⁻¹ * t * m = t ∨ m⁻¹ * t * m = t') :
    ∃ y ∈ h.U81 v, y⁻¹ * t * y = t' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  obtain ⟨n, hnN, hnt⟩ := hex
  set N := normalizer (h.F32 : Set H) with hN
  set C := N ⊓ centralizer ({t} : Set H) with hC
  have hmemC : ∀ m ∈ N, m⁻¹ * t * m = t → m ∈ C := fun m hm hmt =>
    mem_inf.mpr ⟨hm, mem_centralizer_singleton_iff.mpr (by
      calc m * t = m * (m⁻¹ * t * m) := by rw [hmt]
        _ = t * m := by group)⟩
  have hCmem : ∀ m ∈ C, m⁻¹ * t * m = t := fun m hm => by
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hm).2
    rw [mul_assoc, ← h1, inv_mul_cancel_left]
  have hUN := U_le_normalizer_F hv
  have hUC : h.U81 v ≤ C := fun y hy => by
    refine hmemC y (hUN hy) ?_
    rcases hall y (hUN hy) with h1 | h1
    · exact h1
    · exact absurd ⟨y, hy, h1⟩ hno
  have hn2 : n⁻¹ * t' * n = t := by
    have e1 : (n * n)⁻¹ * t * (n * n) = n⁻¹ * t' * n := by rw [← hnt]; group
    rcases hall (n * n) (mul_mem hnN hnN) with h1 | h1
    · rw [← e1, h1]
    · exfalso
      apply hne
      have h2 : n⁻¹ * t' * n = n⁻¹ * t * n := by rw [← e1, h1, hnt]
      exact mul_left_cancel (mul_right_cancel h2)
  have hidx : C.relIndex N = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨n, hnN⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    show Xor ((b : H) * n ∈ C) ((b : H) ∈ C)
    have hconj : ((b : H) * n)⁻¹ * t * ((b : H) * n) = n⁻¹ * ((b : H)⁻¹ * t * b) * n := by
      group
    rcases hall b b.2 with h1 | h1
    · have hbC : (b : H) ∈ C := hmemC b b.2 h1
      have hbn : ¬ ((b : H) * n ∈ C) := by
        intro hbn
        have h2 := hCmem _ hbn
        rw [hconj, h1, hnt] at h2
        exact hne h2
      simp [hbC, hbn]
    · have hbC : ¬ ((b : H) ∈ C) := fun hbC => hne (h1.symm.trans (hCmem _ hbC))
      have hbn : (b : H) * n ∈ C := by
        refine hmemC _ (mul_mem b.2 hnN) ?_
        rw [hconj, h1, hn2]
      simp [hbC, hbn]
  obtain ⟨T, hT⟩ := isSylow_U hv I.rk I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F
  have hodd : ¬ 2 ∣ (h.U81 v).index := by
    have := T.not_dvd_index
    rwa [hT] at this
  have h1 := Subgroup.relIndex_mul_index hUN
  have h2 := Subgroup.relIndex_mul_relIndex (h.U81 v) C N hUC inf_le_left
  apply hodd
  rw [← h1, ← h2, hidx]
  exact Dvd.dvd.mul_right (dvd_mul_left 2 _) _

omit I F in
theorem mem_S_of_mem_U {y : H} (hyU : y ∈ h.U81 v) (hya : y⁻¹ * h.a * y = h.a) : y ∈ h.S := by
  have hCa : centralizer ({h.a} : Set H) ⊓ h.U81 v = h.S := by
    have hSle : h.S ≤ centralizer ({h.a} : Set H) ⊓ h.U81 v :=
      le_inf H₁.isSylowIn_S.1 le_sup_left
    exact eq_of_sylow_of_le H₁.isSylowIn_S.2 hSle inf_le_left
      ((isPGroup_U hv).to_le inf_le_right)
  rw [← hCa]
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hyU⟩
  calc y * h.a = y * (y⁻¹ * h.a * y) := by rw [hya]
    _ = h.a * y := by group

theorem conj_z_of_conj_a {n : H} (hn : n ∈ normalizer (h.F32 : Set H)) :
    (n⁻¹ * h.a * n = h.a → n⁻¹ * d.z * n = d.z) ∧
      (n⁻¹ * h.a * n = d.z → n⁻¹ * d.z * n = h.a) := by
  have hne : n⁻¹ * h.a * n ≠ n⁻¹ * d.z * n := fun he =>
    d.z_ne_a (mul_left_cancel (mul_right_cancel he)).symm
  constructor
  · intro h1
    rcases conj_z_cases hv I F hn with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact h2
  · intro h1
    rcases conj_z_cases hv I F hn with h2 | h2
    · exact h2
    · exact absurd (h1.trans h2.symm) hne

theorem exists_y (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
    (h6 : ∃ c : H, c⁻¹ * (h.a * d.sigma) * c = d.z * d.sigma) :
    ∃ y ∈ h.S, y⁻¹ * h.a * y = h.a ∧ y⁻¹ * d.z * y = d.z ∧
      y⁻¹ * d.sigma * y = h.a * d.z * d.sigma := by
  have haa : h.a * h.a = 1 := Six.a_mul_a_self h.toHyp52
  have hUN := U_le_normalizer_F hv
  obtain ⟨c₂, hc₂⟩ := h6
  have hzσZ : d.z * d.sigma ∈ h.ZF32 := mul_mem (z_mem_ZF I F) (sigma_mem_ZF I F)
  have haσZ : h.a * d.sigma ∈ h.ZF32 := mul_mem (a_mem_ZF I F) (sigma_mem_ZF I F)
  obtain ⟨n₂, hn₂N, hn₂⟩ := exists_normalizer_conj hv I F haσZ (hc₂ ▸ hzσZ)
  rw [hc₂] at hn₂
  have hne2 : d.z * d.sigma ≠ h.a * d.sigma := fun h1 => d.z_ne_a (mul_right_cancel h1)
  obtain ⟨y₂, hy₂U, hy₂⟩ := exists_U_conj_of_orbit hv I F hne2 ⟨n₂, hn₂N, hn₂⟩
    (fun m hm => conj_asigma_cases hv I F h3 hm)
  obtain ⟨c₁, hc₁⟩ := d.exists_conj_sigma F
  have hazσZ : h.a * d.z * d.sigma ∈ h.ZF32 :=
    mul_mem (mul_mem (a_mem_ZF I F) (z_mem_ZF I F)) (sigma_mem_ZF I F)
  obtain ⟨n₁, hn₁N, hn₁⟩ := exists_normalizer_conj hv I F (sigma_mem_ZF I F) (hc₁ ▸ hazσZ)
  rw [hc₁] at hn₁
  have hne1 : h.a * d.z * d.sigma ≠ d.sigma := by
    intro h1
    apply d.z_ne_a
    have h2 : h.a * d.z = 1 := by
      have := mul_right_cancel (h1.trans (one_mul d.sigma).symm)
      exact this
    calc d.z = h.a * (h.a * d.z) := by rw [← mul_assoc, haa, one_mul]
      _ = h.a := by rw [h2, mul_one]
  obtain ⟨y₁, hy₁U, hy₁⟩ := exists_U_conj_of_orbit hv I F hne1 ⟨n₁, hn₁N, hn₁⟩
    (fun m hm => conj_sigma_cases hv I F h3 hm)
  rw [Eight.conj_mul_distrib] at hy₂
  rcases conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F (hUN hy₂U) with
    ha2 | ha2
  ·
    refine ⟨y₂, mem_S_of_mem_U hv hy₂U ha2, ha2,
      (conj_z_of_conj_a hv I F (hUN hy₂U)).1 ha2, ?_⟩
    rw [ha2] at hy₂
    calc y₂⁻¹ * d.sigma * y₂ = h.a * (h.a * (y₂⁻¹ * d.sigma * y₂)) := by
          rw [← mul_assoc h.a h.a, haa, one_mul]
      _ = h.a * (d.z * d.sigma) := by rw [hy₂]
      _ = h.a * d.z * d.sigma := (mul_assoc _ _ _).symm
  ·
    have hz2 := (conj_z_of_conj_a hv I F (hUN hy₂U)).2 ha2
    rw [ha2] at hy₂
    have hσ2 : y₂⁻¹ * d.sigma * y₂ = d.sigma := mul_left_cancel hy₂
    rcases conj_a_cases I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F (hUN hy₁U) with
      ha1 | ha1
    · exact ⟨y₁, mem_S_of_mem_U hv hy₁U ha1, ha1,
        (conj_z_of_conj_a hv I F (hUN hy₁U)).1 ha1, hy₁⟩
    · have hz1 := (conj_z_of_conj_a hv I F (hUN hy₁U)).2 ha1
      have hya : (y₁ * y₂)⁻¹ * h.a * (y₁ * y₂) = h.a := by
        rw [Eight.conj_mul_right, ha1, hz2]
      refine ⟨y₁ * y₂, mem_S_of_mem_U hv (mul_mem hy₁U hy₂U) hya, hya, ?_, ?_⟩
      · rw [Eight.conj_mul_right, hz1, ha2]
      · rw [Eight.conj_mul_right, hy₁, Eight.conj_mul_distrib, Eight.conj_mul_distrib, ha2, hz2,
          hσ2, ← d.z_comm_a]

omit hv in
theorem y_nontrivial_D (hDg : CF81Diag) {y : H} (hyS : y ∈ h.S)
    (hyσ : y⁻¹ * d.sigma * y = h.a * d.z * d.sigma) :
    ∃ e ∈ h.D, y * e * y⁻¹ * e⁻¹ ∉ ⁅h.D, h.D⁆ := by
  obtain ⟨T, hinn, hTD⟩ := exists_sylow_innOf (h := h)
  obtain ⟨p₀, f₀, hp₀, hp₀2, hf₀, hJL⟩ := H₁.exists_lieModel_Jbar
  have hσS := d.sigma_mem_S
  have hzS : d.z ∈ h.S := h.toHyp52.D_le_S d.z_D
  have haS : h.a ∈ h.S := h.toHyp52.a_mem_S
  have hσC := rhoS_sigma_mem_centralizer F
  have hσnot := rhoS_sigma_not_mem I.cf1 I.cf2 F
  have hζ : rhoS hzS ∈ Seven.rhoImg h.J h.D := rhoS_mem hzS d.z_D
  have hζC : rhoS hzS ∈ centralizer ((Seven.rhoImg h.J h.D : Subgroup _) :
      Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (d.comm_z_of_mem_S (h.toHyp52.D_le_S (mem_subgroupOf.mp he)))
  have hζ1 : rhoS hzS ≠ 1 := by
    intro h1
    have hzP := (rho_eq_one_iff (h := h) hzS).mp h1
    have := (h.toHyp52.D_inf_P_eq_bot H₁.center_J) ▸ mem_inf.mpr ⟨d.z_D, hzP⟩
    exact d.z_ne_one (mem_bot.mp this)
  have hyD : ∀ e ∈ h.D, y⁻¹ * e * y ∈ h.D := fun e he => by
    have hyS' := inv_mem hyS
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hyS' (mem_inf.mp he).1) hyS
    · have := (mem_normalizer_iff.mp (h.toHyp52.S_le_normalizer hyS') e).mp (mem_inf.mp he).2
      rwa [inv_inv] at this
  have hwN : rhoS hyS ∈ normalizer ((Seven.rhoImg h.J h.D : Subgroup _) :
      Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
    refine Eight.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨⟨e, heN⟩, he, rfl⟩ := hx
    have heD := mem_subgroupOf.mp he
    have h1 : (rhoS hyS)⁻¹ * Eight.oddBarAction h.J ⟨e, heN⟩ * rhoS hyS =
        rhoS (h.toHyp52.D_le_S (hyD e heD)) := by
      show (Eight.oddBarAction h.J ⟨y, _⟩)⁻¹ * Eight.oddBarAction h.J ⟨e, heN⟩ *
        Eight.oddBarAction h.J ⟨y, _⟩ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    exact rhoS_mem _ (hyD e heD)
  have hwφ : (rhoS hyS)⁻¹ * rhoS hσS * rhoS hyS = rhoS hzS * rhoS hσS := by
    have h1 : (rhoS hyS)⁻¹ * rhoS hσS * rhoS hyS = rhoS (mul_mem (mul_mem haS hzS) hσS) := by
      show (Eight.oddBarAction h.J ⟨y, _⟩)⁻¹ * Eight.oddBarAction h.J ⟨d.sigma, _⟩ *
        Eight.oddBarAction h.J ⟨y, _⟩ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hyσ
    have h2 : rhoS (mul_mem (mul_mem haS hzS) hσS) = rhoS haS * rhoS hzS * rhoS hσS := by
      show Eight.oddBarAction h.J ⟨h.a * d.z * d.sigma, _⟩ = _
      rw [show (⟨h.a * d.z * d.sigma, _⟩ : ↥(normalizer (h.J : Set H))) =
        ⟨h.a, h.toHyp52.S_le_normalizer haS⟩ * ⟨d.z, h.toHyp52.S_le_normalizer hzS⟩ *
          ⟨d.sigma, h.toHyp52.S_le_normalizer hσS⟩ from rfl, map_mul, map_mul]
    have h3 : rhoS haS = 1 := (rho_eq_one_iff (h := h) haS).mpr h.toHyp52.a_mem_P
    rw [h1, h2, h3, one_mul]
  obtain ⟨t, ht, hnot⟩ := hDg _ p₀ f₀ hp₀ hp₀2 hf₀ hJL T (hTD ▸ F.eight_le) _
    (rhoS_mul_self hσS d.sigma_mul_self) (hinn ▸ hσC) (hinn ▸ hσnot) _ (hinn ▸ hζ)
    (hinn ▸ hζC) hζ1 _ (hinn ▸ hwN) hwφ
  rw [hinn] at ht hnot
  obtain ⟨⟨e, heN⟩, he, rfl⟩ := ht
  have heD := mem_subgroupOf.mp he
  have heS := h.toHyp52.D_le_S heD
  refine ⟨e, heD, fun hmem => hnot ?_⟩
  have hu : y * e * y⁻¹ * e⁻¹ ∈ h.S :=
    mul_mem (mul_mem (mul_mem hyS heS) (inv_mem hyS)) (inv_mem heS)
  have h4 := rhoS_mem_commutator hmem hu
  have h5 : rhoS hu = rhoS hyS * Eight.oddBarAction h.J ⟨e, heN⟩ * (rhoS hyS)⁻¹ *
      (Eight.oddBarAction h.J ⟨e, heN⟩)⁻¹ := by
    show Eight.oddBarAction h.J ⟨y * e * y⁻¹ * e⁻¹, _⟩ = _
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rwa [h5] at h4

end Seven

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
