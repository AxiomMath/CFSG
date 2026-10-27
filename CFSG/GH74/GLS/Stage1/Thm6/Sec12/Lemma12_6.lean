module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_5
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_3

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

omit [Finite G] in
theorem T_le_cent_of_mem_Z {w : G} (hw : w ∈ omegaZ T) :
    T ≤ Subgroup.centralizer ({w} : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hw.2.2 t ht

omit [Finite G] in
theorem normalIn_hconj {N T : Subgroup G} {m : G} (hN : NormalIn N T)
    (hm : ∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) : NormalIn (Hconj m N) T := by
  refine ⟨fun a ha => (hm a).2 (hN.1 ha), fun t ht a ha => ?_⟩
  show m * (t * a * t⁻¹) * m⁻¹ ∈ N
  have e : m * (t * a * t⁻¹) * m⁻¹ = (m * t * m⁻¹) * (m * a * m⁻¹) * (m * t * m⁻¹)⁻¹ := by group
  rw [e]
  exact hN.2 _ ((hm t).1 ht) _ ha

theorem HBase.exists_normalizing_x (h : HBase G x S T P Q Rd F) (hz : HZ T P z) {g : G}
    (hg : g⁻¹ * x * g = x * z) :
    ∃ n : G, (∀ a, a ∈ T ↔ n * a * n⁻¹ ∈ T) ∧ n⁻¹ * x * n = x * z := by
  have hxzZ : x * z ∈ omegaZ T := (omegaZ T).mul_mem h.x_mem_Z (hz.mem_Z h.P_le_T)
  have hSw : IsSylow2In T (Subgroup.centralizer ({x * z} : Set G)) :=
    h.sylow_cent_of_conj hg (T_le_cent_of_mem_Z hxzZ)
  have hS1 : IsSylow2In (Hconj g T) (Subgroup.centralizer ({x * z} : Set G)) := by
    have := sylow2_conj h.T_sylow g
    rwa [Hconj_centralizer, hg] at this
  obtain ⟨c, hc, hcT⟩ := sylow2_exists_conj hS1 hSw
  rw [Hconj_mul] at hcT
  refine ⟨g * c, fun a => (SetLike.ext_iff.1 hcT a).trans mem_Hconj, ?_⟩
  have hcw : (x * z) * c = c * (x * z) :=
    Subgroup.mem_centralizer_iff.1 hc (x * z) (Set.mem_singleton _)
  calc (g * c)⁻¹ * x * (g * c) = c⁻¹ * (g⁻¹ * x * g) * c := by group
    _ = c⁻¹ * (x * z) * c := by rw [hg]
    _ = c⁻¹ * ((x * z) * c) := by rw [mul_assoc]
    _ = c⁻¹ * (c * (x * z)) := by rw [hcw]
    _ = x * z := by group

theorem lemma_12_6 {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}
    (hZ : IG_15_3) (hBur : IG_16_2) (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (hout : IP_outer x T Rd) (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P)
    (hRf : IP_Rd_factor T P Q Rd) (hconj : IP_P_conj x z P) (htrans : IP_P_trans P Q Rd)
    (hCRd : IP_cent_Rd P Q Rd) (hexp : IP_cent_P_exp T P Q) : Q = Subgroup.zpowers x := by
  by_contra hQ
  rcases h.card_Z hz with h4 | h8
  · by_cases hweak : ∀ g : G, g⁻¹ * x * g ∈ omegaZ T → g⁻¹ * x * g = x
    ·
      have hTS : T = S := by
        by_contra hTS
        have hlt' : T < S := lt_of_le_of_ne h.T_le_S hTS
        obtain ⟨a, haS, haT, hanorm⟩ := exists_mem_normalizer_of_lt h.S_pgroup hlt'
        have hxa : a * x * a⁻¹ ∈ omegaZ T := omegaZ_conj_mem hanorm h.x_mem_Z
        have hne : a * x * a⁻¹ ≠ x := by
          intro e
          apply haT
          apply h.extremal a haS
          calc a * x = (a * x * a⁻¹) * a := by group
            _ = x * a := by rw [e]
        have h1 := hweak a⁻¹ (by simpa using hxa)
        apply hne
        simpa using h1
      have hTsyl : IsSylow2In T ⊤ := hTS ▸ h.S_sylow
      obtain ⟨g, hgT, hgx⟩ := hZ G h.simple h.nonabelian T hTsyl x h.x_mem_T h.x_sq h.x_ne_one
        h.x_central
      exact hQ (lemma_12_5 h hz hout hcf hP4 hRf hconj htrans h4 hweak g hgT hgx).2
    ·
      obtain ⟨g, hgZ, hgx⟩ : ∃ g : G, g⁻¹ * x * g ∈ omegaZ T ∧ g⁻¹ * x * g ≠ x := by
        by_contra hcon
        apply hweak
        intro g hg
        by_contra hne
        exact hcon ⟨g, hg, hne⟩
      have h123 := lemma_12_3a h hz hP4 h4
      have hw : g⁻¹ * x * g = x * z := by
        rcases h.Z_cases hz h4 _ hgZ with e | e | e | e
        · exfalso
          apply h.x_ne_one
          have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          rw [this, e]; group
        · exact absurd e hgx
        · exact absurd e (h123 g).1
        · exact e
      obtain ⟨n, hn, hnx⟩ := h.exists_normalizing_x hz hw
      obtain ⟨q₂, hq₂Q, hq₂sq⟩ := h.exists_sq_eq_x hP4 hQ
      have hQn : NormalIn (Hconj n Q) T := normalIn_hconj h.Q_normal hn
      have hw'Q : n⁻¹ * q₂ * n ∈ Hconj n Q := by
        show n * (n⁻¹ * q₂ * n) * n⁻¹ ∈ Q
        have : n * (n⁻¹ * q₂ * n) * n⁻¹ = q₂ := by group
        rw [this]; exact hq₂Q
      have hd : Hconj n Q ⊓ P = ⊥ := by
        by_contra hne
        have hpg : IsPGroup 2 ↥(Hconj n Q ⊓ P) := h.T_pgroup.to_le (inf_le_left.trans hQn.1)
        obtain ⟨y, ⟨hyQn, hyP⟩, hy1, hy2⟩ := exists_involution_of_ne_bot hpg hne
        have hnyQ : n * y * n⁻¹ ∈ Q := hyQn
        have hny2 : (n * y * n⁻¹) * (n * y * n⁻¹) = 1 := by
          have : (n * y * n⁻¹) * (n * y * n⁻¹) = n * (y * y) * n⁻¹ := by group
          rw [this, hy2]; group
        rcases h.Q_invol hP4 hnyQ hny2 with e | e
        · apply hy1
          have : y = n⁻¹ * (n * y * n⁻¹) * n := by group
          rw [this, e]; group
        · have hyxz : y = x * z := by
            have : y = n⁻¹ * (n * y * n⁻¹) * n := by group
            rw [this, e, hnx]
          apply h.x_not_mem_P
          have : x = y * z := by rw [hyxz, mul_assoc, hz.z_sq, mul_one]
          rw [this]
          exact P.mul_mem hyP hz.z_mem_P
      have hcomm := comm_of_normal_inf_bot hQn h.P_normal hd
      have hw'T : n⁻¹ * q₂ * n ∈ T := hQn.1 hw'Q
      have hsq : (n⁻¹ * q₂ * n) * (n⁻¹ * q₂ * n) = x * z := by
        have : (n⁻¹ * q₂ * n) * (n⁻¹ * q₂ * n) = n⁻¹ * (q₂ * q₂) * n := by group
        rw [this, hq₂sq, hnx]
      have hmem := hexp _ hw'T (fun p hp => hcomm _ hw'Q p hp)
      rw [hsq] at hmem
      have hzQ : z ∈ Q := by
        have : z = x * (x * z) := by rw [← mul_assoc, h.x_sq, one_mul]
        rw [this]
        exact Q.mul_mem h.x_mem_Q hmem
      exact hz.z_ne_one (h.eq_one_of_mem_P_Q hz.z_mem_P hzQ)
  ·
    have hTZ := lemma_12_3b hZ hBur h hout hcf hP4 hCRd h8
    have hlt : Subgroup.zpowers x < Q :=
      lt_of_le_of_ne ((Subgroup.zpowers_le).2 h.x_mem_Q) (Ne.symm hQ)
    obtain ⟨q, hqQ, hqx⟩ := IsConcreteLE.exists_of_lt hlt
    have hqZ : q ∈ omegaZ T := by
      have := h.Q_le_T hqQ
      rwa [hTZ] at this
    rcases h.Q_invol hP4 hqQ hqZ.2.1 with e | e
    · exact hqx (by rw [e]; exact Subgroup.one_mem _)
    · exact hqx (by rw [e]; exact Subgroup.mem_zpowers x)

end CFSG.GH74.GLS.Stage1.Thm6.Sec12

