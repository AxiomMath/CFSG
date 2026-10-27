module

public import CFSG.ClassicalInvolution.AschTight.S1911Case2b
public import CFSG.ClassicalInvolution.AschTight.S1911Case2c
public import CFSG.ClassicalInvolution.AschTight.S19BWC
public import CFSG.ClassicalInvolution.AschTight.S1916CSR

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem inv_of_conj_eq_mul (hd : Sec19DataT p f K z S W L t V) {c : G}
    (hcS : c ∈ (S : Subgroup G)) (hcR : ∀ r ∈ (S : Subgroup G) ⊓ K, c * r = r * c)
    (hct : c * t * c⁻¹ = t * z) : ∀ w ∈ W ⊓ sec19Y K z, c * w * c⁻¹ = w⁻¹ := by
  have hd0 := hd.toSec19Data
  obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hd
  have hrinv := S1911.conj_eq_inv_of_conj_eq_mul hd hrR hrt
  have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz hrR.1)
  have hz2 : z * z = 1 := (isUniqueInvolution_of_tight hd0.tight.toTightBranch).sq
  have hxS : r * c ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hrR.1 hcS
  have hxt : r * c ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : r * c * t * (r * c)⁻¹ = t := by
      calc r * c * t * (r * c)⁻¹ = r * (c * t * c⁻¹) * r⁻¹ := by group
        _ = r * (t * z) * r⁻¹ := by rw [hct]
        _ = (r * t * r⁻¹) * (r * z * r⁻¹) := by group
        _ = t * z * z := by rw [hrt, hrz, mul_inv_cancel_right]
        _ = t := by rw [mul_assoc, hz2, mul_one]
    calc r * c * t = r * c * t * (r * c)⁻¹ * (r * c) := by group
      _ = t * (r * c) := by rw [e]
  have hxU : ∀ u ∈ K ⊓ W, r * c * u * (r * c)⁻¹ = u⁻¹ := by
    intro u hu
    have hcu : c * u = u * c := hcR u ⟨hd.hWS hu.2, hu.1⟩
    calc r * c * u * (r * c)⁻¹ = r * (c * u) * c⁻¹ * r⁻¹ := by group
      _ = r * u * r⁻¹ := by rw [hcu]; group
      _ = u⁻¹ := hrinv u hu
  have hW := S1911.inv_W_of_inv_U hd hxS hxt hxU
  intro w hw
  have hw' : w ∈ W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    rw [← S1911.inf_sec19Y_eq hd0]
    exact hw
  have hrw : r * w = w * r := Subgroup.mem_centralizer_iff.mp hw'.2 r hrR
  have hrw' : r * w⁻¹ = w⁻¹ * r := by
    calc r * w⁻¹ = w⁻¹ * (w * r) * w⁻¹ := by group
      _ = w⁻¹ * (r * w) * w⁻¹ := by rw [hrw]
      _ = w⁻¹ * r := by group
  calc c * w * c⁻¹ = r⁻¹ * (r * c * w * (r * c)⁻¹) * r := by group
    _ = r⁻¹ * (w⁻¹ * r) := by rw [hW w hw.1, mul_assoc]
    _ = r⁻¹ * (r * w⁻¹) := by rw [hrw']
    _ = w⁻¹ := by group

theorem exists_involution_of_conj_eq_mul (h11b : C19_11bTmp p f)
    (hd : Sec19DataT p f K z S W L t V) {c : G} (hcS : c ∈ (S : Subgroup G))
    (hcR : ∀ r ∈ (S : Subgroup G) ⊓ K, c * r = r * c) (hct : c * t * c⁻¹ = t * z) :
    ∃ u ∈ (S : Subgroup G), u * u = 1 ∧ (∀ w ∈ W ⊓ sec19Y K z, u * w * u⁻¹ = w⁻¹) ∧
      ∀ x ∈ K ⊓ W, u * x = x * u := by
  have hd0 := hd.toSec19Data
  have hI := isUniqueInvolution_of_tight hd0.tight.toTightBranch
  have hinv := inv_of_conj_eq_mul hd hcS hcR hct
  have hcomm := S1911.comm_of_mem hd0
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz hcS)
  have hcU : ∀ x ∈ K ⊓ W, c * x = x * c := fun x hx => hcR x ⟨hd.hWS hx.2, hx.1⟩
  have hc2R : ∀ r ∈ (S : Subgroup G) ⊓ K, c * c * r = r * (c * c) := fun r hr => by
    rw [mul_assoc, hcR r hr, ← mul_assoc, hcR r hr, mul_assoc]
  have hc2t : c * c * t = t * (c * c) := by
    have e : c * c * t * (c * c)⁻¹ = t := by
      calc c * c * t * (c * c)⁻¹ = c * (c * t * c⁻¹) * c⁻¹ := by group
        _ = c * (t * z) * c⁻¹ := by rw [hct]
        _ = (c * t * c⁻¹) * (c * z * c⁻¹) := by group
        _ = t * z * z := by rw [hct, hcz, mul_inv_cancel_right]
        _ = t := by rw [mul_assoc, hI.sq, mul_one]
    calc c * c * t = c * c * t * (c * c)⁻¹ * (c * c) := by group
      _ = t * (c * c) := by rw [e]
  have hc2 := S1916.mem_W_inf_of_mem_centralizer_t h11b hd ((S : Subgroup G).mul_mem hcS hcS)
    hc2R hc2t
  have hc4 : c * c * (c * c) = 1 := by
    have h := hinv (c * c) hc2
    have e : c * (c * c) * c⁻¹ = c * c := by group
    rw [e] at h
    calc c * c * (c * c) = c * c * (c * c)⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  rcases (S1916.isUniqueInvolution_W_inf hd).unique _ hc2 hc4 with h | h
  · exact ⟨c, hcS, h, hinv, hcU⟩
  ·
    obtain ⟨η, S', hη, hinvη, hWη, hηS⟩ := S1911.exists_eta hd0
    have hU : K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
      (hη.1 (S1911.inf_mem_eta hd0 hη hinvη hWη hηS)).1
    obtain ⟨-, -, -, hUcyc, -⟩ := hU
    have hU4 : 4 ≤ Nat.card ↥(K ⊓ W) := by
      rw [S1911.card_inf_eq_card hd]
      exact S1911.four_le_card hd
    obtain ⟨w, hw, hw2⟩ := exists_mul_self_eq_of_isCyclic hI inf_le_left hUcyc
      (S.isPGroup'.to_le (inf_le_right.trans hd.hWS)) hU4
    have hcw : c * w = w * c := hcU w hw
    refine ⟨c * w, (S : Subgroup G).mul_mem hcS (hd.hWS hw.2), ?_, fun x hx => ?_,
      fun x hx => ?_⟩
    · calc c * w * (c * w) = c * (w * c) * w := by group
        _ = c * (c * w) * w := by rw [← hcw]
        _ = c * c * (w * w) := by group
        _ = 1 := by rw [h, hw2, hI.sq]
    · have hwx : w * x = x * w := hcomm w hw.2 x hx.1
      calc c * w * x * (c * w)⁻¹ = c * (w * x) * w⁻¹ * c⁻¹ := by group
        _ = c * x * c⁻¹ := by rw [hwx]; group
        _ = x⁻¹ := hinv x hx
    · have hwx : w * x = x * w := hcomm w hw.2 x hx.2
      rw [mul_assoc, hwx, ← mul_assoc, hcU x hx, mul_assoc]

theorem comm_U_of_comm_V (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (hat : a ∈ Subgroup.centralizer ({t} : Set G))
    (haV : ∀ v ∈ V, a * v = v * a) : ∀ x ∈ K ⊓ W, a * x = x * a := by
  have hd0 := hd.toSec19Data
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := S1911.exists_sylow_member_of_mem_A hd haS hat
  obtain ⟨b, hbR, hbV⟩ := S1911.exists_mem_not_mem hcardRL
  have hcomm := S1911.comm_of_mem hd0
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    hcomm x (hd.leW hx) y (hd.leW hy)
  have haN : a ∈ Subgroup.normalizer (RL : Set G) := mem_normalizer_iff_conjSub_eq.mpr haRL
  have haVN : a ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun v hv => (haV v hv).symm)
  have haK : a ∈ Subgroup.normalizer (K : Set G) := (S1916.sd_normalizer_eq hd0).ge (hd0.hSz haS)
  have haW : a ∈ Subgroup.normalizer (W : Set G) := S19B.le_normalizer_W hd haS
  intro x hx
  have hx' : a * x * a⁻¹ ∈ K ⊓ W := ⟨(Subgroup.mem_normalizer_iff.mp haK x).mp hx.1,
    (Subgroup.mem_normalizer_iff.mp haW x).mp hx.2⟩
  have hxN : x ∈ Subgroup.normalizer (RL : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.2)
  have hx'N : a * x * a⁻¹ ∈ Subgroup.normalizer (RL : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hWRL _ hx'.2)
  have hxV : ∀ y ∈ V, x * y = y * x := fun y hy => hcomm x hx.2 y (hd.leW hy)
  have hx'V : ∀ y ∈ V, a * x * a⁻¹ * y = y * (a * x * a⁻¹) := fun y hy =>
    hcomm _ hx'.2 y (hd.leW hy)
  have hδ : b⁻¹ * (x * b * x⁻¹) ∈ V := S1911.inv_mul_conj_mem hVRL hcardRL hbR hxN hxV
  have hδ' : b⁻¹ * (a * x * a⁻¹ * b * (a * x * a⁻¹)⁻¹) ∈ V :=
    S1911.inv_mul_conj_mem hVRL hcardRL hbR hx'N hx'V
  obtain ⟨c, hc, hcdef⟩ : ∃ c ∈ V, b⁻¹ * (a * b * a⁻¹) = c :=
    ⟨_, S1911.inv_mul_conj_mem_of_normalizer hVRL hcardRL hbR hbV haN haVN, rfl⟩
  have hab : a * b * a⁻¹ = b * c := by rw [← hcdef]; group
  have hxc : a * x * a⁻¹ * c * (a * x * a⁻¹)⁻¹ = c := by rw [hx'V c hc]; group
  have e1 : a * (b⁻¹ * (x * b * x⁻¹)) * a⁻¹ =
      c⁻¹ * (b⁻¹ * (a * x * a⁻¹ * b * (a * x * a⁻¹)⁻¹)) *
        (a * x * a⁻¹ * c * (a * x * a⁻¹)⁻¹) := by
    have e2 : a * (b⁻¹ * (x * b * x⁻¹)) * a⁻¹ =
        (a * b * a⁻¹)⁻¹ * (a * x * a⁻¹) * (a * b * a⁻¹) * (a * x * a⁻¹)⁻¹ := by group
    rw [e2, hab]
    group
  rw [hxc, mul_assoc c⁻¹, hVc _ hδ' c hc, inv_mul_cancel_left] at e1
  have hfix : a * (b⁻¹ * (x * b * x⁻¹)) * a⁻¹ = b⁻¹ * (x * b * x⁻¹) := by
    rw [haV _ hδ]
    group
  rw [hfix] at e1
  have hC := S1911.mem_centralizer_of_defect_eq hVRL hcardRL hbR hbV hxN hx'V hxV e1.symm
  have hmem : a * x * a⁻¹ * x⁻¹ ∈ K ⊓ W ⊓ Subgroup.centralizer (RL : Set G) :=
    ⟨(K ⊓ W).mul_mem hx' ((K ⊓ W).inv_mem hx), hC⟩
  rw [S1911.inf_inf_centralizer_eq_bot hd hRL, Subgroup.mem_bot] at hmem
  calc a * x = a * x * a⁻¹ * x⁻¹ * x * a := by group
    _ = x * a := by rw [hmem, one_mul]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
