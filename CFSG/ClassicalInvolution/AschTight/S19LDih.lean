module

public import CFSG.ClassicalInvolution.AschTight.S19LTr
public import CFSG.ClassicalInvolution.AschTight.S19QTSign

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem mem_or_of_dihedral (hd : Sec19DataT p f K z S W L t V) {q : G}
    (hqinv : ∀ c ∈ W ⊓ sec19Y K z, q * c * q⁻¹ = c⁻¹) (hq2 : q * q = 1)
    (hcoset : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, x ∉ W ⊓ sec19Y K z → q⁻¹ * x ∈ W ⊓ sec19Y K z)
    {ζ : G} (hζ : ζ ∈ W ⊓ sec19Y K z) (hζ2 : ζ * ζ = z) :
    ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) ∧
      (ζ⁻¹ * (s * ζ * s⁻¹) ∈ oddCoreOf (sec19Y K z) ∨
        ζ * (s * ζ * s⁻¹) ∈ oddCoreOf (sec19Y K z)) := by
  have hd0 := hd.toSec19Data
  have hNY := S1916.sd_centralizer_le_normalizer_Y hd0
  intro s hs
  refine ⟨AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (hNY (hd0.hSz hs)), ?_⟩
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have hcomm := S1911.comm_of_mem hd0
  have hwP : s * ζ * s⁻¹ ∈ (S : Subgroup G) ⊓ sec19Y K z :=
    ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs (hd0.hWS hζ.1))
      ((S : Subgroup G).inv_mem hs),
      (Subgroup.mem_normalizer_iff.mp (hNY (hd0.hSz hs)) ζ).mp hζ.2⟩
  have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz hs)
  have hww : s * ζ * s⁻¹ * (s * ζ * s⁻¹) = z := by
    calc s * ζ * s⁻¹ * (s * ζ * s⁻¹) = s * (ζ * ζ) * s⁻¹ := by group
      _ = z := by rw [hζ2, hsz, mul_inv_cancel_right]
  have hwC : s * ζ * s⁻¹ ∈ W ⊓ sec19Y K z := by
    by_contra hwC
    have hc := hcoset _ hwP hwC
    have e : s * ζ * s⁻¹ = q * (q⁻¹ * (s * ζ * s⁻¹)) := by group
    have h1 : q * (q⁻¹ * (s * ζ * s⁻¹)) * q⁻¹ = (q⁻¹ * (s * ζ * s⁻¹))⁻¹ := hqinv _ hc
    have h2 : s * ζ * s⁻¹ * (s * ζ * s⁻¹) = 1 := by
      rw [e]
      calc q * (q⁻¹ * (s * ζ * s⁻¹)) * (q * (q⁻¹ * (s * ζ * s⁻¹))) =
          (q * (q⁻¹ * (s * ζ * s⁻¹)) * q⁻¹) * (q * q) * (q⁻¹ * (s * ζ * s⁻¹)) := by
            group
        _ = 1 := by rw [h1, hq2]; group
    rw [hww] at h2
    exact hzZ.ne_one h2
  rcases S1916.eq_or_eq_inv_of_mul_self_eq hzZ (fun x hx y hy => hcomm x hx.1 y hy.1) hwC hζ hww
    hζ2 with h | h
  · left
    rw [h, inv_mul_cancel]
    exact Subgroup.one_mem _
  · right
    rw [h, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem false_of_dihedral (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V) {q : G}
    (hqP : q ∈ (S : Subgroup G) ⊓ sec19Y K z) (hqC : q ∉ W ⊓ sec19Y K z)
    (hqinv : ∀ c ∈ W ⊓ sec19Y K z, q * c * q⁻¹ = c⁻¹) (hq2 : q * q = 1)
    (hcoset : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, x ∉ W ⊓ sec19Y K z →
      q⁻¹ * x ∈ W ⊓ sec19Y K z) : False := by
  have hd0 := hd.toSec19Data
  have hNY := S1916.sd_centralizer_le_normalizer_Y hd0
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  obtain ⟨ζ, hζ, hζ2⟩ := S19Q.exists_mul_self_eq_z hd
  have hP := mem_or_of_dihedral hd hqinv hq2 hcoset hζ hζ2
  have hζO : ζ * ζ ∉ oddCoreOf (sec19Y K z) := by
    rw [hζ2]
    intro hz
    have hmem : z ∈ W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) := ⟨hzZ.mem, hz⟩
    rw [S1916.inf_oddCoreOf_eq_bot (S.isPGroup'.to_le (inf_le_left.trans hd.hWS)) _,
      Subgroup.mem_bot] at hmem
    exact hzZ.ne_one hmem
  have hconj : ∀ d ∈ Subgroup.centralizer ({z} : Set G), d⁻¹ * q * d ∈ sec19Y K z ∧
      d⁻¹ * q * d * (d⁻¹ * q * d) = 1 ∧ d⁻¹ * q * d ∉ W ⊓ sec19Y K z := by
    intro d hdz
    have hdY : d⁻¹ * q * d ∈ sec19Y K z := by
      have h := (Subgroup.mem_normalizer_iff.mp (hNY (Subgroup.inv_mem _ hdz)) q).mp hqP.2
      rwa [inv_inv] at h
    have h2 : d⁻¹ * q * d * (d⁻¹ * q * d) = 1 := by
      calc d⁻¹ * q * d * (d⁻¹ * q * d) = d⁻¹ * (q * q) * d := by group
        _ = 1 := by rw [hq2]; group
    refine ⟨hdY, h2, fun hC => hqC ?_⟩
    rcases hzZ.unique _ hC h2 with h | h
    · have : q = 1 := by
        calc q = d * (d⁻¹ * q * d) * d⁻¹ := by group
          _ = 1 := by rw [h]; group
      rw [this]
      exact Subgroup.one_mem _
    · have hdz' : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp hdz
      have : q = z := by
        calc q = d * (d⁻¹ * q * d) * d⁻¹ := by group
          _ = d * z * d⁻¹ := by rw [h]
          _ = z := by rw [hdz', mul_inv_cancel_right]
      rw [this]
      exact hzZ.mem
  refine false_of_transfer h11b hd (H := S19Q.signSub (oddCoreOf (sec19Y K z)) ζ)
    (fun s hs x hx => S19Q.conj_mem_signSub hP hs hx.1 hx.2)
    (fun a ha b hb haH hbH => S19Q.inv_mul_mem_signSub hP ha hb haH hbH) hqP.1
    (S19Q.not_mem_signSub_of_inv hζO (hqinv ζ hζ)) hq2 ?_ ?_ ?_
  · intro x hx
    exact (S1916.sd_commute_R_Q hd0 x ⟨hd.hWS hx.2, hx.1⟩ q hqP).symm
  · intro d hdz hdS hdH
    obtain ⟨hdY, -, hdC⟩ := hconj d hdz
    have hc := hcoset _ ⟨hdS, hdY⟩ hdC
    refine S19Q.not_mem_signSub_of_inv hζO ?_ hdH
    have e : d⁻¹ * q * d = q * (q⁻¹ * (d⁻¹ * q * d)) := by group
    rw [e]
    have hcc := (S1911.comm_of_mem hd0) _ hc.1 ζ hζ.1
    calc q * (q⁻¹ * (d⁻¹ * q * d)) * ζ * (q * (q⁻¹ * (d⁻¹ * q * d)))⁻¹ =
        q * ((q⁻¹ * (d⁻¹ * q * d)) * ζ) * (q⁻¹ * (d⁻¹ * q * d))⁻¹ * q⁻¹ := by group
      _ = q * (ζ * (q⁻¹ * (d⁻¹ * q * d))) * (q⁻¹ * (d⁻¹ * q * d))⁻¹ * q⁻¹ := by rw [hcc]
      _ = q * ζ * q⁻¹ := by group
      _ = ζ⁻¹ := hqinv ζ hζ
  · intro d hdz hdW
    obtain ⟨hdY, -, hdC⟩ := hconj d hdz
    exact hdC ⟨hdW, hdY⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
