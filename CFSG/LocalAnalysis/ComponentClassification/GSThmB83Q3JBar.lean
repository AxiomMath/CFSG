module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Q
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Fix

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem eq_of_card_eq_two {G : Type*} [Group G] {C : Subgroup G} (hC : Nat.card C = 2) {u v : G}
    (hu : u ∈ C) (hv : v ∈ C) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  by_contra huv
  have : Finite C := Nat.finite_of_card_ne_zero (by omega)
  let f : Fin 3 → C := ![1, ⟨u, hu⟩, ⟨v, hv⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢ <;>
      first | exact absurd hij.symm hu1 | exact absurd hij.symm hv1 | exact absurd hij hu1 |
        exact absurd hij hv1 | exact absurd hij huv | exact absurd hij.symm huv
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem mem_four_of_card_eq_four {G : Type*} [Group G] {C : Subgroup G} (hC : Nat.card C = 4)
    {u₁ u₂ u₃ u₄ w : G} (h₁ : u₁ ∈ C) (h₂ : u₂ ∈ C) (h₃ : u₃ ∈ C) (h₄ : u₄ ∈ C) (hw : w ∈ C)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h14 : u₁ ≠ u₄) (h23 : u₂ ≠ u₃) (h24 : u₂ ≠ u₄)
    (h34 : u₃ ≠ u₄) : w = u₁ ∨ w = u₂ ∨ w = u₃ ∨ w = u₄ := by
  by_contra hne
  push Not at hne
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hne
  have : Finite C := Nat.finite_of_card_ne_zero (by omega)
  let f : Fin 5 → C := ![⟨u₁, h₁⟩, ⟨u₂, h₂⟩, ⟨u₃, h₃⟩, ⟨u₄, h₄⟩, ⟨w, hw⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢ <;>
      first | exact absurd hij h12 | exact absurd hij h13 | exact absurd hij h14 |
        exact absurd hij h23 | exact absurd hij h24 | exact absurd hij h34 |
        exact absurd hij.symm h12 | exact absurd hij.symm h13 | exact absurd hij.symm h14 |
        exact absurd hij.symm h23 | exact absurd hij.symm h24 | exact absurd hij.symm h34 |
        exact absurd hij hw1 | exact absurd hij hw2 | exact absurd hij hw3 | exact absurd hij hw4 |
        exact absurd hij.symm hw1 | exact absurd hij.symm hw2 | exact absurd hij.symm hw3 |
        exact absurd hij.symm hw4
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (φ : MulAut G) (y : G) :
    φ * MulAut.conj y * φ⁻¹ = MulAut.conj (φ y) := by
  ext w
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem conj_eq_conj_of_center_eq_bot {G : Type*} [Group G] (hZ : center G = ⊥) {u v : G}
    (h : MulAut.conj u = MulAut.conj v) : u = v := by
  have hc : v⁻¹ * u ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut G => φ y) h
    simp only [MulAut.conj_apply] at this
    calc y * (v⁻¹ * u) = v⁻¹ * (v * y * v⁻¹) * u := by group
      _ = v⁻¹ * (u * y * u⁻¹) * u := by rw [this]
      _ = v⁻¹ * u * y := by group
  rw [hZ, mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X)

theorem sec8_S_le_normalizer_J : h.S ≤ normalizer (h.J : Set X) := h.S_le.trans inf_le_right

theorem sec8_centralizer_a_le_normalizer_J
    (hJn : (h.J.subgroupOf (centralizer ({h.a} : Set X))).Normal) :
    centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X) :=
  Six.centralizer_le_normalizer_of_normal h.J_le hJn

theorem mem_P_of_oddBarAction_eq_one {s : X} (hs : s ∈ h.S)
    (h1 : Eight.oddBarAction h.J ⟨s, h.sec8_S_le_normalizer_J hs⟩ = 1) : s ∈ h.P :=
  ⟨hs, Eight.mem_ker_oddBarAction.mp h1⟩

theorem oddCoreIn_J_ne : oddCoreIn h.J ≠ h.J := by
  intro heq
  obtain ⟨-, -, u, v, huv⟩ := h.sec8_quasisimple_Jbar
  have htop : pPrimeCore 2 h.J = ⊤ := by
    apply map_injective h.J.subtype_injective
    rw [← MonoidHom.range_eq_map, range_subtype]
    exact heq
  have hall : ∀ w : h.J ⧸ pPrimeCore 2 h.J, w = 1 := by
    intro w
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
    exact (QuotientGroup.eq_one_iff j).mpr (htop ▸ mem_top j)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  apply huv
  rw [hall u, hall v]

noncomputable abbrev sigmaJ (s : X) (hs : s ∈ normalizer (h.J : Set X)) : MulAut ↥h.J :=
  h.J.normalizerMonoidHom ⟨s, hs⟩

theorem mem_fix_sigmaJ {s : X} (hs : s ∈ normalizer (h.J : Set X)) (j : h.J) :
    j ∈ Eight.fixSubgroup (h.sigmaJ s hs) ↔ s * (j : X) = j * s := by
  rw [Eight.mem_fixSubgroup]
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    change s * (j : X) * s⁻¹ = j at this
    calc s * (j : X) = (s * (j : X) * s⁻¹) * s := by group
      _ = j * s := by rw [this]
  · intro h1
    apply Subtype.ext
    change s * (j : X) * s⁻¹ = j
    rw [h1, mul_inv_cancel_right]

theorem sec8_D_le_J : h.D ≤ h.J := inf_le_right

abbrev Dbar : Subgroup (h.J ⧸ pPrimeCore 2 h.J) :=
  (h.D.subgroupOf h.J).map (QuotientGroup.mk' (pPrimeCore 2 h.J))

theorem conj_mk_eq (e : h.J) :
    MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 h.J) e) =
      Eight.oddBarAction h.J ⟨(e : X), le_normalizer e.2⟩ :=
  (Eight.oddBarAction_of_mem e).symm

theorem sec8_x_mem_normalizer_J : h.x ∈ normalizer (h.J : Set X) := h.sec8_S_le_normalizer_J h.x_mem

noncomputable abbrev xbar : MulAut (h.J ⧸ pPrimeCore 2 h.J) :=
  Eight.oddBarAction h.J ⟨h.x, h.sec8_x_mem_normalizer_J⟩

namespace L83Hyp

variable {h} (H : L83Hyp h)
include H

theorem xbar_mul_self : h.xbar * h.xbar = 1 := by
  rw [← map_mul]
  rw [show (⟨h.x, h.sec8_x_mem_normalizer_J⟩ : normalizer (h.J : Set X)) *
    ⟨h.x, h.sec8_x_mem_normalizer_J⟩
    = 1 from Subtype.ext H.x_mul_x, map_one]

theorem card_fix_x (hq : h.IsQ3) (hDiag : CFA6Diag) :
    Nat.card (Eight.fixSubgroup h.xbar) = 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCaN := h.sec8_centralizer_a_le_normalizer_J H.J_normal
  set Cx : Subgroup X := centralizer ({h.x} : Set X) with hCx
  set Dx : Subgroup X := (pPrimeCore 2 Cx).map Cx.subtype ⊓ centralizer ({h.a} : Set X) with hDx
  have hDxN : Dx ≤ normalizer (h.J : Set X) := inf_le_right.trans hCaN
  obtain ⟨-, -, -, -, -, -, hJD⟩ := gsUnbalancingTriple_iff.mp H.maximal.1
  set O' : Subgroup (MulAut (h.J ⧸ pPrimeCore 2 h.J)) :=
    (Dx.subgroupOf (normalizer (h.J : Set X))).map (Eight.oddBarAction h.J) with hO'
  refine hDiag _ hq.2 h.xbar H.xbar_mul_self ⟨O', ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hdx : (d : X) ∈ Cx := by
      obtain ⟨c, -, hc⟩ := mem_map.mp (mem_inf.mp hd).1
      have hcd : (d : X) = c := hc.symm
      rw [hcd]
      exact c.2
    exact (mem_centralizer_singleton_iff.mp hdx)
  ·
    intro hbot
    apply h.oddCoreIn_J_ne
    refine le_antisymm (map_subtype_le _) ?_
    calc h.J = ⁅h.J, Dx⁆ := hJD.symm
      _ ≤ oddCoreIn h.J := ?_
    rw [commutator_le]
    intro j hj dd hdd
    have hker : (⟨dd⁻¹, inv_mem (hDxN hdd)⟩ : normalizer (h.J : Set X)) ∈
        (Eight.oddBarAction h.J).ker := by
      rw [MonoidHom.mem_ker]
      have h1 : Eight.oddBarAction h.J ⟨dd, hDxN hdd⟩ ∈ O' := ⟨⟨dd, hDxN hdd⟩, hdd, rfl⟩
      rw [hbot, mem_bot] at h1
      rw [show (⟨dd⁻¹, inv_mem (hDxN hdd)⟩ : normalizer (h.J : Set X)) =
        (⟨dd, hDxN hdd⟩)⁻¹ from rfl, map_inv, h1, inv_one]
    obtain ⟨-, hc⟩ := mem_coreActionKernel.mp (Eight.mem_ker_oddBarAction.mp hker)
    have := hc j⁻¹ (inv_mem hj)
    rw [inv_inv, inv_inv] at this
    rw [commutatorElement_def]
    exact this
  ·
    have h1 : Nat.card O' ∣ Nat.card Dx := by
      refine (card_map_dvd (Dx.subgroupOf (normalizer (h.J : Set X))) _).trans ?_
      rw [← card_map_of_injective (normalizer (h.J : Set X)).subtype_injective,
        subgroupOf_map_subtype, inf_eq_left.mpr hDxN]
    have h2 : Nat.card Dx ∣ Nat.card ((pPrimeCore 2 Cx).map Cx.subtype) :=
      card_dvd_of_le inf_le_left
    have h3 : Odd (Nat.card ((pPrimeCore 2 Cx).map Cx.subtype)) := by
      rw [card_map_of_injective Cx.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat h3 (h1.trans h2)
  ·
    have hσ : IsPGroup 2 (zpowers (h.sigmaJ h.x h.sec8_x_mem_normalizer_J)) := by
      refine isPGroup_zpowers_of_mul_self ?_
      rw [← map_mul]
      rw [show (⟨h.x, h.sec8_x_mem_normalizer_J⟩ : normalizer (h.J : Set X)) *
        ⟨h.x, h.sec8_x_mem_normalizer_J⟩ = 1 from Subtype.ext H.x_mul_x, map_one]
    have hfix : Eight.fixSubgroup h.xbar =
        (Eight.fixSubgroup (h.sigmaJ h.x h.sec8_x_mem_normalizer_J)).map
          (QuotientGroup.mk' (pPrimeCore 2 h.J)) :=
      Eight.fixSubgroup_oddBarAut _ hσ
    rw [hfix, map_map]
    refine le_normalizer_of_conj fun y hy w hw => ?_
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
    obtain ⟨dd, hdd, rfl⟩ := mem_map.mp hw
    have hjx : h.x * (j : X) = j * h.x := (h.mem_fix_sigmaJ _ j).mp hj
    have hjN : (j : X) ∈ normalizer (h.J : Set X) := le_normalizer j.2
    have hconj : MulAut.conj ((QuotientGroup.mk' (pPrimeCore 2 h.J)) j) =
        Eight.oddBarAction h.J ⟨(j : X), hjN⟩ := (Eight.oddBarAction_of_mem j).symm
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [hconj, ← map_inv, ← map_mul, ← map_mul]
    refine mem_map_of_mem _ ?_
    show (j : X) * dd * (j : X)⁻¹ ∈ Dx
    have hjCx : (j : X) ∈ Cx := mem_centralizer_singleton_iff.mpr hjx.symm
    have hja : (j : X) ∈ centralizer ({h.a} : Set X) := h.J_le j.2
    have hd := (show (dd : X) ∈ Dx from hdd)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp
        (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Cx (pPrimeCore 2 Cx)
          (le_normalizer hjCx)) dd).mp hd.1
    · exact mul_mem (mul_mem hja hd.2) (inv_mem hja)

namespace Q3Data

variable {H} (d : Q3Data H)
include d

theorem tau_mem_S : d.tau ∈ h.S := d.tau_mem.1.1

noncomputable abbrev taubar : MulAut (h.J ⧸ pPrimeCore 2 h.J) :=
  Eight.oddBarAction h.J ⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩

theorem taubar_mul_self : d.taubar * d.taubar = 1 := by
  rw [← map_mul]
  rw [show (⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩ : normalizer (h.J : Set X)) *
    ⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩ = 1 from Subtype.ext d.tau_sq, map_one]

theorem card_Dbar (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) : Nat.card h.Dbar = 8 := by
  have hD2 : IsPGroup 2 (h.D.subgroupOf h.J) :=
    ((Six.isPGroup_S h).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype
  rw [OddQuot.card_map_of_isPGroup hD2, ← d.card_D hq hCF1 hCF2 hL0,
    ← card_map_of_injective h.J.subtype_injective, map_subgroupOf_eq_of_le h.sec8_D_le_J]

abbrev zbar : h.J ⧸ pPrimeCore 2 h.J :=
  ((⟨d.z, h.sec8_D_le_J d.z_D⟩ : h.J) : h.J ⧸ pPrimeCore 2 h.J)

theorem zbar_mem_centralizer : d.zbar ∈ centralizer (h.Dbar : Set (h.J ⧸ pPrimeCore 2 h.J)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨e, he, rfl⟩
  simp only [QuotientGroup.coe_mk']
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (d.z_comm (e : X) he).symm

theorem zbar_ne_one : d.zbar ≠ 1 := by
  intro h1
  have hD2 : IsPGroup 2 (h.D.subgroupOf h.J) :=
    ((Six.isPGroup_S h).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype
  have := OddQuot.injOn_of_isPGroup hD2
    (show (⟨d.z, h.sec8_D_le_J d.z_D⟩ : h.J) ∈ h.D.subgroupOf h.J from d.z_D) (one_mem _)
    (h1.trans (QuotientGroup.mk_one _).symm)
  exact d.z_ne (congrArg Subtype.val this)

theorem center_Jbar (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) (hSC : CFA6SylowCent) (hII : CFA6InnerInv) :
    center (h.J ⧸ pPrimeCore 2 h.J) = ⊥ := by
  have hC2 := (hSC _ hq.2 h.Dbar (d.card_Dbar hq hCF1 hCF2 hL0)).2
  have hZle : center (h.J ⧸ pPrimeCore 2 h.J) ≤
      centralizer (h.Dbar : Set (h.J ⧸ pPrimeCore 2 h.J)) :=
    fun w hw => mem_centralizer_iff.mpr fun y _ => (Subgroup.mem_center_iff.mp hw y)
  refine eq_bot_iff.mpr fun w hw => ?_
  rw [mem_bot]
  by_contra hw1
  have hwz : w = d.zbar := eq_of_card_eq_two hC2 (hZle hw) d.zbar_mem_centralizer hw1 d.zbar_ne_one
  rw [hwz] at hw
  have hz2 : d.zbar * d.zbar = 1 := by
    rw [← QuotientGroup.mk_mul]
    rw [show (⟨d.z, h.sec8_D_le_J d.z_D⟩ : h.J) * ⟨d.z, h.sec8_D_le_J d.z_D⟩ = 1 from
      Subtype.ext d.z_sq, QuotientGroup.mk_one]
  have h8 := (hII _ hq.2 d.zbar hz2 d.zbar_ne_one).1
  have htop : centralizer ({d.zbar} : Set (h.J ⧸ pPrimeCore 2 h.J)) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    rw [mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hw y)
  rw [htop, Subgroup.card_top, card_of_isSec8JType_three hq.2] at h8
  norm_num at h8

theorem tau_comm_D (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {e : X}
    (he : e ∈ h.D) : d.tau * e = e * d.tau :=
  d.tau_comm_Q1 hCF1 hCF2 ⟨h.sec8_D_le_Q he, H.D_le_M3 he⟩

theorem taubar_mem_centralizer (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    d.taubar ∈ centralizer ((h.Dbar.map (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →*
      MulAut (h.J ⧸ pPrimeCore 2 h.J)) : Subgroup _) : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
  rw [h.conj_mk_eq e, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (d.tau_comm_D hCF1 hCF2 he).symm

theorem eq_one_of_mem_P (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {w : X}
    (hwP : w ∈ h.P) (hwK : w ∈ h.K) : w = 1 := by
  rcases d.P_mem w hwP with h1 | h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hwK) (H.a_not_mem_K hCF1 hCF2)
  · exact absurd (h1 ▸ (show w ∈ h.M3 from mem_sup_left hwK)) (d.b_not_mem_M3 hCF1 hCF2)
  · exfalso
    apply d.b_not_mem_M3 hCF1 hCF2
    have hab : h.a * d.b ∈ h.M3 := h1 ▸ (show w ∈ h.M3 from mem_sup_left hwK)
    have := mul_mem (inv_mem h.a_mem_M3) hab
    rwa [inv_mul_cancel_left] at this

theorem taubar_not_inner (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) (hSC : CFA6SylowCent) (hII : CFA6InnerInv) :
    d.taubar ∉
      (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →* MulAut (h.J ⧸ pPrimeCore 2 h.J)).range := by
  rintro ⟨y, hy⟩
  have hZ := d.center_Jbar hq hCF1 hCF2 hL0 hSC hII
  have hC2 := (hSC _ hq.2 h.Dbar (d.card_Dbar hq hCF1 hCF2 hL0)).2
  have hyC : y ∈ centralizer (h.Dbar : Set (h.J ⧸ pPrimeCore 2 h.J)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h1 := mem_centralizer_iff.mp (d.taubar_mem_centralizer hCF1 hCF2)
      (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 h.J) e)) ⟨_, ⟨e, he, rfl⟩, rfl⟩
    rw [← hy, ← map_mul, ← map_mul] at h1
    exact conj_eq_conj_of_center_eq_bot hZ h1
  have hτK : d.tau ∈ h.K := d.tau_K
  have hzK : d.z ∈ h.K := H.fixedLayer_le_K (h.D_le_JB d.z_D)
  by_cases hy1 : y = 1
  ·
    rw [hy1, map_one] at hy
    exact d.tau_ne_one (d.eq_one_of_mem_P hCF1 hCF2
      (h.mem_P_of_oddBarAction_eq_one d.tau_mem_S hy.symm) hτK)
  ·
    have hyz : y = d.zbar := eq_of_card_eq_two hC2 hyC d.zbar_mem_centralizer hy1 d.zbar_ne_one
    rw [hyz, show d.zbar = QuotientGroup.mk' (pPrimeCore 2 h.J) ⟨d.z, h.sec8_D_le_J d.z_D⟩ from rfl,
      h.conj_mk_eq] at hy
    have hzS : d.z ∈ h.S := d.z_D.1
    have h1 : Eight.oddBarAction h.J ⟨d.tau * d.z⁻¹,
        h.sec8_S_le_normalizer_J (mul_mem d.tau_mem_S (inv_mem hzS))⟩ = 1 := by
      rw [show (⟨d.tau * d.z⁻¹, _⟩ : normalizer (h.J : Set X)) =
        ⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩ *
          (⟨d.z, le_normalizer (h.sec8_D_le_J d.z_D)⟩)⁻¹ from rfl, map_mul, map_inv]
      rw [show Eight.oddBarAction h.J ⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩ = d.taubar
        from rfl, ← hy]
      exact mul_inv_cancel _
    have h2 := d.eq_one_of_mem_P hCF1 hCF2
      (h.mem_P_of_oddBarAction_eq_one (mul_mem d.tau_mem_S (inv_mem hzS)) h1)
      (mul_mem hτK (inv_mem hzK))
    exact d.tau_ne_z hq hCF1 hCF2 hL0 (mul_inv_eq_one.mp h2)

theorem P_comm_Q {w q : X} (hw : w ∈ h.P) (hq : q ∈ h.Q) : w * q = q * w := by
  have hb : d.b * q = q * d.b :=
    (mem_centralizer_iff.mp (d.B_le_centralizer_Q (d.B_eq ▸ mem_zpowers d.b)) q hq).symm
  have ha : h.a * q = q * h.a := (H.comm_a_of_mem_Q hq).symm
  rcases d.P_mem w hw with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact ha
  · exact hb
  · rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

omit d H in
theorem x_conj_mem_D {e : X} (he : e ∈ h.D) : h.x⁻¹ * e * h.x ∈ h.D := by
  have hxS := h.x_mem
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hxS) he.1) hxS, ?_⟩
  have := (mem_normalizer_iff.mp (inv_mem h.sec8_x_mem_normalizer_J) e).mp he.2
  rwa [inv_inv] at this

theorem tau_x (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) (hDiag : CFA6Diag) (hSC : CFA6SylowCent) (hNC : CFA6NoComm)
    (hII : CFA6InnerInv) : ∃ p ∈ h.P, h.x⁻¹ * d.tau * h.x = d.tau * d.z * p := by
  set DC : Subgroup (MulAut (h.J ⧸ pPrimeCore 2 h.J)) :=
    h.Dbar.map (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →* MulAut (h.J ⧸ pPrimeCore 2 h.J))
    with hDC
  set C := centralizer (DC : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) with hCdef
  have hZ := d.center_Jbar hq hCF1 hCF2 hL0 hSC hII
  have hC4 : Nat.card C = 4 := (hSC _ hq.2 h.Dbar (d.card_Dbar hq hCF1 hCF2 hL0)).1
  set cz : MulAut (h.J ⧸ pPrimeCore 2 h.J) := MulAut.conj d.zbar with hcz
  have hczC : cz ∈ C := by
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [hcz, ← map_mul, ← map_mul]
    exact congrArg _ (mem_centralizer_iff.mp d.zbar_mem_centralizer y hy)
  have hτC : d.taubar ∈ C := d.taubar_mem_centralizer hCF1 hCF2
  have hnot := d.taubar_not_inner hq hCF1 hCF2 hL0 hSC hII
  have hcz1 : cz ≠ 1 := by
    intro h1
    apply d.zbar_ne_one
    exact conj_eq_conj_of_center_eq_bot hZ (h1.trans (map_one _).symm)
  have hczInn : cz ∈ (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →*
      MulAut (h.J ⧸ pPrimeCore 2 h.J)).range := ⟨_, rfl⟩
  have hτcz : d.taubar * cz ∉ (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →*
      MulAut (h.J ⧸ pPrimeCore 2 h.J)).range := by
    intro h1
    apply hnot
    have := mul_mem h1 (inv_mem hczInn)
    rwa [mul_inv_cancel_right] at this
  have hxDC : ∀ y ∈ DC, h.xbar * y * h.xbar⁻¹ ∈ DC := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    have hxe : h.x * (e : X) * h.x⁻¹ ∈ h.D := by
      have he' : (e : X) ∈ h.D := he
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem h.x_mem he'.1) (inv_mem h.x_mem), ?_⟩
      exact (mem_normalizer_iff.mp h.sec8_x_mem_normalizer_J e).mp he'.2
    refine ⟨_, ⟨⟨h.x * (e : X) * h.x⁻¹, hxe.2⟩, hxe, rfl⟩, ?_⟩
    rw [h.conj_mk_eq, h.conj_mk_eq, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hx2 : h.xbar⁻¹ = h.xbar := inv_eq_of_mul_eq_one_right H.xbar_mul_self
  have hτx : h.xbar⁻¹ * d.taubar * h.xbar ∈ C := by
    rw [mem_centralizer_iff]
    intro y hy
    have hy' := hxDC y hy
    have hc := mem_centralizer_iff.mp hτC _ hy'
    calc y * (h.xbar⁻¹ * d.taubar * h.xbar) =
        h.xbar⁻¹ * ((h.xbar * y * h.xbar⁻¹) * d.taubar) * h.xbar := by group
      _ = h.xbar⁻¹ * (d.taubar * (h.xbar * y * h.xbar⁻¹)) * h.xbar := by rw [hc]
      _ = h.xbar⁻¹ * d.taubar * h.xbar * y := by group
  have hτxInn : h.xbar⁻¹ * d.taubar * h.xbar ∉ (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →*
      MulAut (h.J ⧸ pPrimeCore 2 h.J)).range := by
    rintro ⟨y, hy⟩
    apply hnot
    refine ⟨h.xbar y, ?_⟩
    rw [← mulAut_mul_conj_mul_inv, hy]
    group
  have h1R : (1 : MulAut (h.J ⧸ pPrimeCore 2 h.J)) ∈ (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →*
      MulAut (h.J ⧸ pPrimeCore 2 h.J)).range := one_mem _
  have hne : ∀ u v : MulAut (h.J ⧸ pPrimeCore 2 h.J),
      u ∈ (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →* MulAut (h.J ⧸ pPrimeCore 2 h.J)).range →
      v ∉ (MulAut.conj : (h.J ⧸ pPrimeCore 2 h.J) →* MulAut (h.J ⧸ pPrimeCore 2 h.J)).range →
      u ≠ v := fun u v hu hv huv => hv (huv ▸ hu)
  have hmem := mem_four_of_card_eq_four hC4 (one_mem C) hczC hτC (mul_mem hτC hczC) hτx
    (Ne.symm hcz1) (hne _ _ h1R hnot) (hne _ _ h1R hτcz) (hne _ _ hczInn hnot)
    (hne _ _ hczInn hτcz) (fun h2 => hcz1 (mul_left_cancel (h2.trans (mul_one _).symm).symm))
  rcases hmem with h2 | h2 | h2 | h2
  · exact absurd (h2 ▸ h1R) hτxInn
  · exact absurd (h2 ▸ hczInn) hτxInn
  · exfalso
    refine hNC _ hq.2 h.xbar d.taubar H.xbar_mul_self d.taubar_mul_self (H.card_fix_x hq hDiag) hnot
      h.Dbar (d.card_Dbar hq hCF1 hCF2 hL0) hτC ?_
    calc h.xbar * d.taubar = h.xbar * (h.xbar⁻¹ * d.taubar * h.xbar) := by rw [h2]
      _ = d.taubar * h.xbar := by group
  ·
    have hzS : d.z ∈ h.S := d.z_D.1
    set w : X := (h.x⁻¹ * d.tau * h.x) * (d.tau * d.z)⁻¹ with hw
    have hwS : w ∈ h.S := mul_mem (mul_mem (mul_mem (inv_mem h.x_mem) d.tau_mem_S) h.x_mem)
      (inv_mem (mul_mem d.tau_mem_S hzS))
    have hw1 : Eight.oddBarAction h.J ⟨w, h.sec8_S_le_normalizer_J hwS⟩ = 1 := by
      rw [show (⟨w, h.sec8_S_le_normalizer_J hwS⟩ : normalizer (h.J : Set X)) =
        (⟨h.x, h.sec8_x_mem_normalizer_J⟩)⁻¹ *
          ⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩ * ⟨h.x, h.sec8_x_mem_normalizer_J⟩ *
          (⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩ *
            ⟨d.z, le_normalizer (h.sec8_D_le_J d.z_D)⟩)⁻¹ from rfl]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul]
      have hczz : cz = Eight.oddBarAction h.J ⟨d.z, le_normalizer (h.sec8_D_le_J d.z_D)⟩ :=
        h.conj_mk_eq ⟨d.z, h.sec8_D_le_J d.z_D⟩
      rw [show Eight.oddBarAction h.J ⟨h.x, h.sec8_x_mem_normalizer_J⟩ = h.xbar from rfl,
        show Eight.oddBarAction h.J ⟨d.tau, h.sec8_S_le_normalizer_J d.tau_mem_S⟩ = d.taubar
          from rfl, h2, ← hczz]
      group
    have hwP := h.mem_P_of_oddBarAction_eq_one hwS hw1
    refine ⟨w, hwP, ?_⟩
    have hτzQ : d.tau * d.z ∈ h.Q := mul_mem d.tau_mem.1 (h.sec8_D_le_Q d.z_D)
    have hc := d.P_comm_Q hwP hτzQ
    calc h.x⁻¹ * d.tau * h.x = w * (d.tau * d.z) := by rw [hw]; group
      _ = d.tau * d.z * w := hc

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
