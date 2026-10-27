module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G}

theorem HBase.exists_normalizing (h : HBase G x S T P Q Rd F) (hz : HZ T P z)
    (h4 : Nat.card (omegaZ T) = 4) {w g : G} (hw : w = x ∨ w = x * z) (hg : g⁻¹ * w * g = z) :
    ∃ m : G, (∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) ∧ m * z * m⁻¹ = w := by
  have hwZ : w ∈ omegaZ T := by
    rcases hw with rfl | rfl
    · exact h.x_mem_Z
    · exact (omegaZ T).mul_mem h.x_mem_Z (hz.mem_Z h.P_le_T)
  have hTw : T ≤ Subgroup.centralizer ({w} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hwZ.2.2 t ht
  have hSz : IsSylow2In T (Subgroup.centralizer ({z} : Set G)) := by
    rcases hw with rfl | rfl
    · exact h.sylow_cent_of_conj hg hz.T_le_cent
    · by_contra hns
      obtain ⟨T₁, hT₁, hTT₁⟩ := exists_sylow2_ge h.T_pgroup hz.T_le_cent
      have hlt : T < T₁ := lt_of_le_of_ne hTT₁ (fun e => hns (e ▸ hT₁))
      obtain ⟨a, haT₁, haT, hanorm⟩ := exists_mem_normalizer_of_lt hT₁.2.1 hlt
      have hxZ : a * x * a⁻¹ ∈ omegaZ T := omegaZ_conj_mem hanorm h.x_mem_Z
      rcases h.Z_cases hz h4 _ hxZ with e | e | e | e
      · apply h.x_ne_one
        have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
        rw [this, e]; group
      · apply haT
        have haC : a ∈ Subgroup.centralizer ({x} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          calc x * a = (a * x * a⁻¹) * a := by rw [e]
            _ = a * x := by group
        have hpg : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers a) :=
          hT₁.2.1.to_le (sup_le hTT₁ ((Subgroup.zpowers_le).2 haT₁))
        have hle : T ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({x} : Set G) :=
          sup_le h.T_le_C ((Subgroup.zpowers_le).2 haC)
        have heq := sylow2_eq_of_le h.T_sylow hpg le_sup_left hle
        have haz : a ∈ T ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
        rw [heq] at haz
        exact haz
      · apply hns
        have : (a⁻¹)⁻¹ * x * a⁻¹ = z := by rw [inv_inv]; exact e
        exact h.sylow_cent_of_conj this hz.T_le_cent
      · apply hns
        have : (a⁻¹ * g)⁻¹ * x * (a⁻¹ * g) = z := by
          calc (a⁻¹ * g)⁻¹ * x * (a⁻¹ * g) = g⁻¹ * (a * x * a⁻¹) * g := by group
            _ = g⁻¹ * (x * z) * g := by rw [e]
            _ = z := hg
        exact h.sylow_cent_of_conj this hz.T_le_cent
  have hgw : g * z * g⁻¹ = w := by rw [← hg]; group
  have hC : Hconj g⁻¹ (Subgroup.centralizer ({z} : Set G)) =
      Subgroup.centralizer ({w} : Set G) := by
    rw [Hconj_centralizer, inv_inv, hgw]
  have hSw' : IsSylow2In (Hconj g⁻¹ T) (Subgroup.centralizer ({w} : Set G)) := by
    have := sylow2_conj hSz g⁻¹
    rwa [hC] at this
  have hSw : IsSylow2In T (Subgroup.centralizer ({w} : Set G)) :=
    sylow2_of_card hTw h.T_pgroup hSw' (by rw [Hconj_card])
  obtain ⟨c, hc, hcT⟩ := sylow2_exists_conj hSw' hSw
  rw [Hconj_mul] at hcT
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · intro a
    have key : ∀ b, b ∈ T ↔ (g⁻¹ * c) * b * (g⁻¹ * c)⁻¹ ∈ T :=
      fun b => (SetLike.ext_iff.1 hcT b).trans mem_Hconj
    have h1 := key ((c⁻¹ * g) * a * (c⁻¹ * g)⁻¹)
    have e : (g⁻¹ * c) * ((c⁻¹ * g) * a * (c⁻¹ * g)⁻¹) * (g⁻¹ * c)⁻¹ = a := by group
    rw [e] at h1
    exact h1.symm
  · have hcw : w * c = c * w := Subgroup.mem_centralizer_iff.1 hc w (Set.mem_singleton w)
    calc c⁻¹ * g * z * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * z * g⁻¹) * c := by group
      _ = c⁻¹ * w * c := by rw [hgw]
      _ = c⁻¹ * (w * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * w) := by rw [hcw]
      _ = w := by group

theorem HBase.false_of_conj (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hP4 : IP_P_four P)
    (h4 : Nat.card (omegaZ T) = 4) {w m : G} (hwz : w ≠ z)
    (hm : ∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) (hmz : m * z * m⁻¹ = w) : False := by
  obtain ⟨V, hVP, hV⟩ := hP4
  have hmem : ∀ a, a ∈ Hconj m⁻¹ P ↔ m⁻¹ * a * m ∈ P := by
    intro a; simp
  have hinv : ∀ a, a ∈ T ↔ m⁻¹ * a * m ∈ T := by
    intro a
    have := normalizes_inv hm a
    simpa using this
  have hPmT : NormalIn (Hconj m⁻¹ P) T := by
    refine ⟨fun a ha => ?_, fun t ht a ha => ?_⟩
    · exact (hinv a).2 (h.P_le_T ((hmem a).1 ha))
    · rw [hmem]
      have e : m⁻¹ * (t * a * t⁻¹) * m = (m⁻¹ * t * m) * (m⁻¹ * a * m) * (m⁻¹ * t * m)⁻¹ := by
        group
      rw [e]
      exact h.P_normal.2 _ ((hinv t).1 ht) _ ((hmem a).1 ha)
  have hd : P ⊓ Hconj m⁻¹ P = ⊥ := by
    by_contra hne
    obtain ⟨u, ⟨huP, huPm⟩, hu1, hu2, huc⟩ :=
      exists_central_involution_of_normal h.T_pgroup (inf_le_left.trans h.P_le_T)
        (fun t ht n hn => ⟨h.P_normal.2 t ht n hn.1, hPmT.2 t ht n hn.2⟩) hne
    have huZ : u ∈ omegaZ T := ⟨h.P_le_T huP, hu2, huc⟩
    have h1 := h.P_inf_Z hz h4 huP huZ
    have huZ' : m⁻¹ * u * m ∈ omegaZ T := omegaZ_conj_inv_mem hm huZ
    have h2 := h.P_inf_Z hz h4 ((hmem u).1 huPm) huZ'
    rcases h1 with h1 | h1
    · exact hu1 h1
    · rcases h2 with h2 | h2
      · apply hu1
        have : u = m * (m⁻¹ * u * m) * m⁻¹ := by group
        rw [this, h2]; group
      · apply hwz
        rw [h1] at h2
        have : m * z * m⁻¹ = z := by
          calc m * z * m⁻¹ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [h2]
            _ = z := by group
        rw [← hmz]
        exact this
  have hVm : IsFour (Hconj m⁻¹ V) := ⟨hV.1.hconj m⁻¹, by rw [Hconj_card, hV.2]⟩
  have hVmPm : Hconj m⁻¹ V ≤ Hconj m⁻¹ P := Hconj_le_Hconj hVP
  refine no_two_fours h.rank_le hV hVm (fun a ha => h.T_le_C (h.P_le_T (hVP ha)))
    (fun a ha => h.T_le_C (hPmT.1 (hVmPm ha)))
    (fun a ha b hb => comm_of_normal_inf_bot h.P_normal hPmT hd a (hVP ha) b (hVmPm hb)) ?_
  rw [eq_bot_iff, ← hd]
  exact inf_le_inf hVP hVmPm

theorem lemma_12_3a (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (hP4 : IP_P_four P)
    (h4 : Nat.card (omegaZ T) = 4) : ∀ g : G, g⁻¹ * x * g ≠ z ∧ g⁻¹ * (x * z) * g ≠ z := by
  intro g
  constructor
  · intro hg
    obtain ⟨m, hm, hmz⟩ := h.exists_normalizing hz h4 (Or.inl rfl) hg
    exact h.false_of_conj hz hP4 h4 (h.x_ne_z hz) hm hmz
  · intro hg
    obtain ⟨m, hm, hmz⟩ := h.exists_normalizing hz h4 (Or.inr rfl) hg
    refine h.false_of_conj hz hP4 h4 ?_ hm hmz
    intro e
    apply h.x_ne_one
    have : x = (x * z) * z := by rw [mul_assoc, hz.z_sq, mul_one]
    rw [this, e, hz.z_sq]

theorem invol_mem_Z (h : HBase G x S T P Q Rd F) (h8 : Nat.card (omegaZ T) = 8) {u : G}
    (huT : u ∈ T) (hu2 : u * u = 1) : u ∈ omegaZ T := by
  by_contra hu
  have hu1 : u ≠ 1 := fun e => hu (by rw [e]; exact Subgroup.one_mem _)
  have hcomm : ∀ a ∈ omegaZ T, ∀ b ∈ Subgroup.zpowers u, a * b = b * a := by
    intro a ha b hb
    exact ha.2.2 b ((Subgroup.zpowers_le.2 huT) hb)
  have hd : omegaZ T ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcZ, hcu⟩
    rcases zpowers_sq_cases hu2 hcu with e | e
    · rw [e]; exact Subgroup.one_mem _
    · exact absurd (e ▸ hcZ) hu
  have hE : IsElemAb2 (omegaZ T ⊔ Subgroup.zpowers u) :=
    (omegaZ_isElemAb2 T).sup (isElemAb2_zpowers hu2) hcomm
  have hcard : Nat.card ↥(omegaZ T ⊔ Subgroup.zpowers u) = 16 := by
    rw [card_sup_of_commute hcomm hd, h8, card_zpowers_of_sq hu2 hu1]
  have hle : omegaZ T ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le h.omegaZ_le_C (fun a ha => h.T_le_C ((Subgroup.zpowers_le.2 huT) ha))
  have := h.rank_le _ hle hE
  rw [hcard] at this
  norm_num at this

theorem HBase.Z_le_R (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hCRd : IP_cent_Rd P Q Rd) : omegaZ T ≤ P ⊔ Q := by
  intro a ha
  have haRd : a ∈ Rd := involution_mem_Rd h hout ha.1 ha.2.1
  exact hCRd a haRd (fun p hp => ha.2.2 p (h.P_le_T hp))

theorem HBase.exists_four_in_Z (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hCRd : IP_cent_Rd P Q Rd) (hP4 : IP_P_four P) (h8 : Nat.card (omegaZ T) = 8) :
    ∃ V : Subgroup G, V ≤ P ∧ IsFour V ∧ V ⊔ Subgroup.zpowers x = omegaZ T := by
  set V : Subgroup G := omegaZ T ⊓ P with hV
  have hVZ : V ≤ omegaZ T := inf_le_left
  have hVP : V ≤ P := inf_le_right
  have hZsub : omegaZ T ≤ V ⊔ Subgroup.zpowers x := by
    intro a ha
    obtain ⟨p, hp, q, hq, e⟩ := h.mem_R.1 (h.Z_le_R hout hCRd ha)
    have haa : a * a = 1 := ha.2.1
    have hpq : p * q = q * p := h.PQ_comm p hp q hq
    have h1 : p * q * (p * q) = p * p * (q * q) :=
      (show Commute q p from hpq.symm).mul_mul_mul_comm p q
    have hsq : p * p * (q * q) = 1 := by rw [← h1, ← e]; exact haa
    have hpp : p * p = (q * q)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have hpp1 : p * p = 1 := by
      apply h.eq_one_of_mem_P_Q (P.mul_mem hp hp)
      rw [hpp]
      exact Q.inv_mem (Q.mul_mem hq hq)
    have hqq : q * q = 1 := by rw [hpp1, one_mul] at hsq; exact hsq
    have hqx : q = 1 ∨ q = x := h.Q_invol hP4 hq hqq
    have hqZ : q ∈ omegaZ T := by
      rcases hqx with e1 | e1
      · rw [e1]; exact Subgroup.one_mem _
      · rw [e1]; exact h.x_mem_Z
    have hqzp : q ∈ Subgroup.zpowers x := by
      rcases hqx with e1 | e1
      · rw [e1]; exact Subgroup.one_mem _
      · rw [e1]; exact Subgroup.mem_zpowers x
    have hpZ : p ∈ omegaZ T := by
      have : p = a * q⁻¹ := by rw [e]; group
      rw [this]
      exact (omegaZ T).mul_mem ha ((omegaZ T).inv_mem hqZ)
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hpZ, hp⟩ hqzp
  have hVx : V ⊔ Subgroup.zpowers x ≤ omegaZ T :=
    sup_le hVZ ((Subgroup.zpowers_le).2 h.x_mem_Z)
  have hEq : V ⊔ Subgroup.zpowers x = omegaZ T := le_antisymm hVx hZsub
  have hcomm : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    exact (hVZ ha).2.2 b ((Subgroup.zpowers_le.2 h.x_mem_T) hb)
  have hd : V ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcV, hcx⟩
    rcases zpowers_sq_cases h.x_sq hcx with e | e
    · rw [e]; exact Subgroup.one_mem _
    · exact absurd (e ▸ hVP hcV) h.x_not_mem_P
  have hcard : Nat.card ↥(V ⊔ Subgroup.zpowers x) = Nat.card V * 2 := by
    rw [card_sup_of_commute hcomm hd, card_zpowers_of_sq h.x_sq h.x_ne_one]
  rw [hEq, h8] at hcard
  have hV4 : Nat.card V = 4 := by omega
  exact ⟨V, hVP, ⟨(omegaZ_isElemAb2 T).mono hVZ, hV4⟩, hEq⟩

omit [Finite G] in
theorem centIn_omegaZ (T : Subgroup G) : centIn T (omegaZ T) = T := by
  ext t
  constructor
  · intro ht; exact (Subgroup.mem_inf.1 ht).1
  · intro ht
    refine Subgroup.mem_inf.2 ⟨ht, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ha.2.2 t ht

omit [Finite G] in
theorem phi2_conj_mem {T : Subgroup G} {m : G} (hm : ∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) {a : G}
    (ha : a ∈ phi2 T) : m * a * m⁻¹ ∈ phi2 T := by
  have : phi2 T ≤ Hconj m (phi2 T) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro s ⟨d, hd, rfl⟩
    show m * (d * d) * m⁻¹ ∈ phi2 T
    have e : m * (d * d) * m⁻¹ = (m * d * m⁻¹) * (m * d * m⁻¹) := by group
    rw [e]
    exact Subgroup.subset_closure ⟨m * d * m⁻¹, (hm d).1 hd, rfl⟩
  exact this ha

omit [Finite G] in
theorem phi2_le (T : Subgroup G) : phi2 T ≤ T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro s ⟨d, hd, rfl⟩
  exact T.mul_mem hd hd

theorem HBase.fix_x_of_ne (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) (hCRd : IP_cent_Rd P Q Rd) (hP4 : IP_P_four P)
    (h8 : Nat.card (omegaZ T) = 8) (hne : T ≠ omegaZ T) {m : G}
    (hm : ∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) : m * x * m⁻¹ = x := by
  obtain ⟨V, hVP, hV, hVx⟩ := h.exists_four_in_Z hout hCRd hP4 h8
  have h12 := omega1_phi_cent_le h hout hcf hVP hV
  rw [hVx, centIn_omegaZ] at h12
  have hex : ∃ t ∈ T, t ∉ omegaZ T := by
    by_contra hcon
    apply hne
    apply le_antisymm
    · intro t ht
      by_contra h'
      exact hcon ⟨t, ht, h'⟩
    · exact omegaZ_le T
  obtain ⟨t, htT, htZ⟩ := hex
  have htt : t * t ≠ 1 := fun e => htZ (invol_mem_Z h h8 htT e)
  have hpg : IsPGroup 2 ↥(phi2 T) := h.T_pgroup.to_le (phi2_le T)
  have hne2 : phi2 T ≠ ⊥ := by
    intro hbot
    have : t * t ∈ phi2 T := Subgroup.subset_closure ⟨t, htT, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact htt this
  obtain ⟨y, hy, hy1, hy2⟩ := exists_involution_of_ne_bot hpg hne2
  have hyx : y ∈ Subgroup.zpowers x := h12 (Subgroup.subset_closure ⟨hy, hy2⟩)
  have hyx' : y = x := by
    rcases zpowers_sq_cases h.x_sq hyx with e | e
    · exact absurd e hy1
    · exact e
  have hx : x ∈ phi2 T := hyx' ▸ hy
  have hmx : m * x * m⁻¹ ∈ phi2 T := phi2_conj_mem hm hx
  have hmx2 : m * x * m⁻¹ * (m * x * m⁻¹) = 1 := by
    have : m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
    rw [this, h.x_sq]; group
  have hmxz : m * x * m⁻¹ ∈ Subgroup.zpowers x := h12 (Subgroup.subset_closure ⟨hmx, hmx2⟩)
  rcases zpowers_sq_cases h.x_sq hmxz with e | e
  · exfalso
    apply h.x_ne_one
    have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    rw [this, e]; group
  · exact e

theorem lemma_12_3b {G : Type} [Group G] [Finite G] {x : G} {S T P Q Rd F : Subgroup G}
    (hZ : IG_15_3) (hBur : IG_16_2) (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) (hP4 : IP_P_four P) (hCRd : IP_cent_Rd P Q Rd)
    (h8 : Nat.card (omegaZ T) = 8) : T = omegaZ T := by
  by_contra hne
  have hfix : ∀ m : G, (∀ a, a ∈ T ↔ m * a * m⁻¹ ∈ T) → m * x * m⁻¹ = x :=
    fun m hm => h.fix_x_of_ne hout hcf hCRd hP4 h8 hne hm
  have hTS : T = S := by
    by_contra hTS
    have hlt : T < S := lt_of_le_of_ne h.T_le_S hTS
    obtain ⟨a, haS, haT, hanorm⟩ := exists_mem_normalizer_of_lt h.S_pgroup hlt
    have hax := hfix a hanorm
    apply haT
    apply h.extremal a haS
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [hax]
  have hTsyl : IsSylow2In T ⊤ := hTS ▸ h.S_sylow
  obtain ⟨g, hgT, hgx⟩ := hZ G h.simple h.nonabelian T hTsyl x h.x_mem_T h.x_sq h.x_ne_one
    h.x_central
  have hy2 : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
    have : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [this, h.x_sq]; group
  have hyZ : g⁻¹ * x * g ∈ omegaZ T := invol_mem_Z h h8 hgT hy2
  obtain ⟨n, hn, hnxy⟩ := hBur G T hTsyl x (g⁻¹ * x * g) h.x_mem_T hgT h.x_central hyZ.2.2 ⟨g, rfl⟩
  have hn' : ∀ a, a ∈ T ↔ n * a * n⁻¹ ∈ T := fun a => Subgroup.mem_normalizer_iff.1 hn a
  have hfx := hfix n⁻¹ (normalizes_inv hn')
  rw [inv_inv] at hfx
  exact hgx (hnxy.symm.trans hfx)

end CFSG.GH74.GLS.Stage1.Thm6.Sec12

