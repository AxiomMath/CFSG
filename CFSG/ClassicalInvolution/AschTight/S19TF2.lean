module

public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.AschTight.S1911C8c

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem conj_eq_mul_of_conj_eq_mul {x t' z : G} (h : x * t' * x⁻¹ = t' * z)
    (ht2 : t' * t' = 1) (hxz : x * z = z * x) : t' * x * t'⁻¹ = x * z := by
  have ht' : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
  have h1 : x * t' = t' * z * x := by
    calc x * t' = x * t' * x⁻¹ * x := by group
      _ = t' * z * x := by rw [h]
  calc t' * x * t'⁻¹ = t' * (x * t') := by rw [ht', mul_assoc]
    _ = t' * (t' * z * x) := by rw [h1]
    _ = (t' * t') * z * x := by group
    _ = z * x := by rw [ht2, one_mul]
    _ = x * z := hxz.symm

variable [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem le_centralizer_W_of_mem_A (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓
        Subgroup.centralizer (((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤
      Subgroup.centralizer (W : Set G) := by
  obtain ⟨hA, -, -⟩ := S1911.c19_8_of p f G K z S W L t V hd
  rw [hA]
  refine sup_le (fun a ha => ?_) (fun b hb => ?_)
  · have haA := ha.1
    have haS : a ∈ (S : Subgroup G) := haA.1
    have haR : a ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) haA.2
    exact S19B.mem_centralizer_W hd haS (S19B.mem_centralizerModOdd_K hd haS haR)
      ⟨Subgroup.mem_top a, ha.2.1, ha.2.2.1, ha.2.2.2⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact S1911.comm_of_mem hd.toSec19Data w hw b hb.1

theorem conj_mem_sec19BPrime (hd : Sec19DataT p f K z S W L t V) {x d : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) (hdz : d * z = z * d)
    (hdS : d * x * d⁻¹ ∈ (S : Subgroup G)) : d * x * d⁻¹ ∈ S19B.sec19BPrime K S W L := by
  have hd0 := hd.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hcomm := S1911.comm_of_mem hd0
  have htW : t ∈ W := S1911.mem_W hd
  have hzW : z ∈ W := Hall196.mem_W_of_sec19DataT hd
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz hs))
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight hd.tight.toTightBranch]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hdz
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hxK : x ∈ centralizerModOdd ⊤ K := ((S19B.mem_sec19BPrime_iff hd).mp hx).2.1
  have hyK : d * x * d⁻¹ ∈ centralizerModOdd ⊤ K := by
    have h := S19B.conj_mem_centralizerModOdd_top hxK d
    rwa [mem_normalizer_iff_conjSub_eq.mp hdN] at h
  have hyR := S19B.mem_centralizer_inf_of_mem S hdS hyK
  have hyW : d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (S19B.le_normalizer_W hd hdS) t).mp htW
  have ht2 : t * t = 1 := hd.invL.sq
  have hyt2 : d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) = 1 := by
    calc d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) =
        d * x * d⁻¹ * (t * t) * (d * x * d⁻¹)⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have hyt1 : d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ ≠ 1 := by
    intro h
    apply hd.invL.ne_one
    calc t = (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by group
      _ = 1 := by rw [h]; group
  rcases S1911.invol_mem_W hd hyW hyt2 hyt1 with h | h | h
  · exfalso
    apply hd.ne
    have hyz : d * x * d⁻¹ * z * (d * x * d⁻¹)⁻¹ = z := by
      rw [hzS _ hdS, mul_assoc, mul_inv_cancel, mul_one]
    calc t = (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by group
      _ = (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹ * z * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by
          rw [h, hyz]
      _ = z := by group
  · have hyC : d * x * d⁻¹ ∈ Subgroup.centralizer
        (((S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hle : (S : Subgroup G) ⊓ K ⊔ Subgroup.zpowers t ≤
          Subgroup.centralizer ({d * x * d⁻¹} : Set G) := by
        refine sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hyR r hr)) ?_
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        calc t * (d * x * d⁻¹) = d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ * (d * x * d⁻¹) := by
              rw [h]
          _ = d * x * d⁻¹ * t := by group
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    exact S19B.mem_sec19BPrime_of_conj_mem hd hx hdS
      (le_centralizer_W_of_mem_A hd (Subgroup.mem_inf.mpr ⟨hdS, hyC⟩))
  · exfalso
    have hxt : x * (d⁻¹ * t * d) * x⁻¹ = d⁻¹ * t * d * z := by
      have hdz' : d⁻¹ * z * d = z := by
        rw [mul_assoc, ← hdz, ← mul_assoc, inv_mul_cancel, one_mul]
      calc x * (d⁻¹ * t * d) * x⁻¹ =
          d⁻¹ * (d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹) * d := by group
        _ = d⁻¹ * t * d * (d⁻¹ * z * d) := by rw [h]; group
        _ = d⁻¹ * t * d * z := by rw [hdz']
    have ht'2 : d⁻¹ * t * d * (d⁻¹ * t * d) = 1 := by
      calc d⁻¹ * t * d * (d⁻¹ * t * d) = d⁻¹ * (t * t) * d := by group
        _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
    have hconj := conj_eq_mul_of_conj_eq_mul hxt ht'2 (hzS x hxS)
    have hzS' : z ∈ (S : Subgroup G) := hd0.hWS hzW
    have hxzS : (d⁻¹ * t * d) * x * (d⁻¹ * t * d)⁻¹ ∈ (S : Subgroup G) := by
      rw [hconj]
      exact (S : Subgroup G).mul_mem hxS hzS'
    have hxzW : (d⁻¹ * t * d) * x * (d⁻¹ * t * d)⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
      rw [hconj]
      refine (Subgroup.centralizer (W : Set G)).mul_mem hx.1.2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hcomm w hw z hzW
    have hxzB := S19B.mem_sec19BPrime_of_conj_mem hd hx hxzS hxzW
    rw [hconj] at hxzB
    have hzB : z ∈ S19B.sec19BPrime K S W L := by
      have := (S19B.sec19BPrime K S W L).mul_mem
        ((S19B.sec19BPrime K S W L).inv_mem hx) hxzB
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have hbot := S19B.inf_sec19BPrime_eq_bot hd
    have hz1 : z ∈ W ⊓ S19B.sec19BPrime K S W L := ⟨hzW, hzB⟩
    rw [hbot, Subgroup.mem_bot] at hz1
    exact hI.ne_one hz1

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
