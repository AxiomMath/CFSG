module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Sigma
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsSub

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G]

theorem conj_mul_eq_mul_pow {a b z e : G} (he : e ∈ Subgroup.center G) {α β : ℕ}
    (ha : a * z * a⁻¹ = z * e ^ α) (hb : b * z * b⁻¹ = z * e ^ β) :
    a * b * z * (a * b)⁻¹ = z * e ^ (α + β) := by
  have hc : a⁻¹ * e ^ β = e ^ β * a⁻¹ :=
    Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ he β) a⁻¹
  calc a * b * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group
    _ = a * z * a⁻¹ * e ^ β := by
        rw [hb, show a * (z * e ^ β) * a⁻¹ = a * z * (e ^ β * a⁻¹) by group, ← hc,
          ← mul_assoc]
    _ = z * e ^ (α + β) := by rw [ha, mul_assoc, ← pow_add]

theorem conj_pow_eq_mul_pow {a z e : G} (he : e ∈ Subgroup.center G) {α : ℕ}
    (ha : a * z * a⁻¹ = z * e ^ α) (i : ℕ) : a ^ i * z * (a ^ i)⁻¹ = z * e ^ (α * i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', conj_mul_eq_mul_pow he ha ih, show α * (i + 1) = α + α * i by ring]

variable {T Q P₁ S : Subgroup G} {e u y x m : G}

@[expose] def e1Lift (u m y x : G) (v : Fin 64) : G :=
  u ^ (v.val / 32 % 2) * m ^ (v.val / 16 % 2) *
    ((x * u * x⁻¹) ^ (v.val / 8 % 2) * (x * m * x⁻¹) ^ (v.val / 4 % 2)) *
    y ^ (v.val / 2 % 2) * x ^ (v.val % 2)

theorem mk_e1Lift {Z : Subgroup G} [Z.Normal] (v : Fin 64) :
    ((e1Lift u m y x v : G) : G ⧸ Z) = caseC3Word Z u m y x v := by
  rw [CaseC3BCD.caseC3Word_eq, e1Lift]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow]

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z)
include hb

theorem commute_u_conj : x * u * x⁻¹ * u = u * (x * u * x⁻¹) :=
  hb.partC.commute _ (hb.swap_right u hb.partC.self_mem) u hb.partC.self_mem

theorem lift_forty_mul_self : u * (x * u * x⁻¹) * (u * (x * u * x⁻¹)) = 1 := by
  have hc := hb.partC
  rw [show u * (x * u * x⁻¹) * (u * (x * u * x⁻¹)) = u * ((x * u * x⁻¹) * u) * (x * u * x⁻¹) by
    group, hb.commute_u_conj, show u * (u * (x * u * x⁻¹)) * (x * u * x⁻¹) =
      u * u * (x * (u * u) * x⁻¹) by group, hc.sq, hc.conj_centralElt, hc.centralElt_mul_self]

theorem m_not_mem : m ≠ 1 ∧ m ≠ e ∧ m ≠ u ∧ m ≠ u * e := by
  have hc := hb.partC
  have hfix : ∀ g : G, (g = 1 ∨ g = e ∨ g = u ∨ g = u * e) →
      y * g * y⁻¹ = g ∨ y * g * y⁻¹ = g * e := by
    rintro g (rfl | rfl | rfl | rfl)
    · left
      group
    · exact Or.inl (hc.conj_centralElt y)
    · exact hb.conj_self
    · exact conj_mul_mod_central hc.center hc.centralElt_mul_self hb.conj_self
        (Or.inl (hc.conj_centralElt y))
  have hmU : ¬ (m = 1 ∨ m = e ∨ m = u ∨ m = u * e) := fun h' => by
    rcases hfix m h' with h1 | h1
    exacts [hb.m_moved h1, hb.m_moved' h1]
  push Not at hmU
  exact hmU

theorem conj_m_u : m * u * m⁻¹ = u * e := by
  have hc := hb.partC
  obtain ⟨φ⟩ := hb.quaternion_right
  obtain ⟨hm1, hme, hmu, hmue⟩ := hb.m_not_mem
  have hmm : m * m = e := quaternion_mul_self_of_ne φ hc.mem_right hc.order hb.m_mem hm1 hme
  have h := quaternion_anticomm φ hc.mem_right hc.order hb.m_mem hc.self_mem hmm hc.sq
    (fun h => hmu h.symm) (fun h => hmue (by rw [h, hc.mul_centralElt_mul_centralElt]))
  rw [h, mul_assoc u m e, hc.commute_centralElt m]
  group

theorem conj_u_z : u * (u * (x * u * x⁻¹)) * u⁻¹ = u * (x * u * x⁻¹) := by
  calc u * (u * (x * u * x⁻¹)) * u⁻¹ = u * (x * u * x⁻¹ * u) * u⁻¹ := by
        rw [hb.commute_u_conj]
    _ = u * (x * u * x⁻¹) := by group

theorem conj_q_z :
    x * u * x⁻¹ * (u * (x * u * x⁻¹)) * (x * u * x⁻¹)⁻¹ = u * (x * u * x⁻¹) := by
  calc x * u * x⁻¹ * (u * (x * u * x⁻¹)) * (x * u * x⁻¹)⁻¹ = x * u * x⁻¹ * u := by group
    _ = u * (x * u * x⁻¹) := hb.commute_u_conj

theorem conj_m_z : m * (u * (x * u * x⁻¹)) * m⁻¹ = u * (x * u * x⁻¹) * e := by
  have hc := hb.partC
  have hqm := hc.commute _ (hb.swap_right u hc.self_mem) m hb.m_mem
  calc m * (u * (x * u * x⁻¹)) * m⁻¹ = m * u * m⁻¹ * (m * (x * u * x⁻¹) * m⁻¹) := by group
    _ = u * e * (x * u * x⁻¹) := by
        rw [hb.conj_m_u, show m * (x * u * x⁻¹) * m⁻¹ = x * u * x⁻¹ by rw [← hqm]; group]
    _ = u * (x * u * x⁻¹) * e := by
        rw [mul_assoc, ← hc.commute_centralElt (x * u * x⁻¹), ← mul_assoc]

theorem conj_d_z : x * m * x⁻¹ * (u * (x * u * x⁻¹)) * (x * m * x⁻¹)⁻¹ =
    u * (x * u * x⁻¹) * e := by
  have hc := hb.partC
  have hud := hc.commute _ (hb.swap_right m hb.m_mem) u hc.self_mem
  calc x * m * x⁻¹ * (u * (x * u * x⁻¹)) * (x * m * x⁻¹)⁻¹ =
        x * m * x⁻¹ * u * (x * m * x⁻¹)⁻¹ * (x * (m * u * m⁻¹) * x⁻¹) := by group
    _ = u * (x * (u * e) * x⁻¹) := by
        rw [hb.conj_m_u, show x * m * x⁻¹ * u * (x * m * x⁻¹)⁻¹ = u by rw [hud]; group]
    _ = u * (x * u * x⁻¹) * e := by
        rw [show x * (u * e) * x⁻¹ = x * u * (e * x⁻¹) by group, ← hc.commute_centralElt x⁻¹]
        group

theorem conj_inv_x_y : x⁻¹ * y * x = y ∨ x⁻¹ * y * x = y * e := by
  have hxy : ((y : G) : G ⧸ Z) = ((x⁻¹ * y * x : G) : G ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_assoc,
      ← hb.mk_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  rcases (hb.mem_iff _).mp (QuotientGroup.eq.mp hxy) with h | h
  · exact Or.inl (inv_mul_eq_one.mp h).symm
  · exact Or.inr (by rw [← h]; group)

theorem conj_y_z : y * (u * (x * u * x⁻¹)) * y⁻¹ = u * (x * u * x⁻¹) := by
  have hc := hb.partC
  have hyq : y * (x * u * x⁻¹) * y⁻¹ = x * (y * u * y⁻¹) * x⁻¹ := by
    rw [show y * (x * u * x⁻¹) * y⁻¹ = x * ((x⁻¹ * y * x) * u * (x⁻¹ * y * x)⁻¹) * x⁻¹ by group]
    rcases hb.conj_inv_x_y with h | h <;> rw [h]
    rw [mul_conj_centralElt hc.center]
  calc y * (u * (x * u * x⁻¹)) * y⁻¹ = y * u * y⁻¹ * (y * (x * u * x⁻¹) * y⁻¹) := by group
    _ = y * u * y⁻¹ * (x * (y * u * y⁻¹) * x⁻¹) := by rw [hyq]
    _ = u * (x * u * x⁻¹) := by
        rcases hb.conj_self with h | h <;> rw [h]
        rw [show u * e * (x * (u * e) * x⁻¹) = u * (e * (x * u * x⁻¹ * e)) by
            rw [show x * (u * e) * x⁻¹ = x * u * (e * x⁻¹) by group,
              ← hc.commute_centralElt x⁻¹]
            group, ← hc.commute_centralElt (x * u * x⁻¹ * e)]
        rw [show u * (x * u * x⁻¹ * e * e) = u * (x * u * x⁻¹) * (e * e) by group,
          hc.centralElt_mul_self, mul_one]

theorem conj_x_z : x * (u * (x * u * x⁻¹)) * x⁻¹ = u * (x * u * x⁻¹) := by
  have hc := hb.partC
  have hxx : x * x ∈ Z := (QuotientGroup.eq_one_iff _).mp hb.mk_mul_self
  calc x * (u * (x * u * x⁻¹)) * x⁻¹ = x * u * x⁻¹ * (x * x * u * (x * x)⁻¹) := by group
    _ = x * u * x⁻¹ * u := by
        rcases (hb.mem_iff _).mp hxx with h | h <;> rw [h]
        · group
        · rw [← hc.commute_centralElt u, mul_inv_cancel_right]
    _ = u * (x * u * x⁻¹) := hb.commute_u_conj

theorem conj_lift_eq (v : Fin 64) :
    e1Lift u m y x v * (u * (x * u * x⁻¹)) * (e1Lift u m y x v)⁻¹ =
      u * (x * u * x⁻¹) * e ^ (v.val / 16 % 2 + v.val / 4 % 2) := by
  have he := hb.partC.center
  have h0 : ∀ {a : G}, a * (u * (x * u * x⁻¹)) * a⁻¹ = u * (x * u * x⁻¹) →
      a * (u * (x * u * x⁻¹)) * a⁻¹ = u * (x * u * x⁻¹) * e ^ 0 := fun h => by
    rw [h, pow_zero, mul_one]
  have h1 : ∀ {a : G}, a * (u * (x * u * x⁻¹)) * a⁻¹ = u * (x * u * x⁻¹) * e →
      a * (u * (x * u * x⁻¹)) * a⁻¹ = u * (x * u * x⁻¹) * e ^ 1 := fun h => by
    rw [h, pow_one]
  rw [e1Lift, conj_mul_eq_mul_pow he (conj_mul_eq_mul_pow he (conj_mul_eq_mul_pow he
    (conj_mul_eq_mul_pow he (conj_pow_eq_mul_pow he (h0 hb.conj_u_z) _)
      (conj_pow_eq_mul_pow he (h1 hb.conj_m_z) _))
    (conj_mul_eq_mul_pow he (conj_pow_eq_mul_pow he (h0 hb.conj_q_z) _)
      (conj_pow_eq_mul_pow he (h1 hb.conj_d_z) _)))
    (conj_pow_eq_mul_pow he (h0 hb.conj_y_z) _)) (conj_pow_eq_mul_pow he (h0 hb.conj_x_z) _)]
  congr 2
  omega

theorem caseC3Word_mem_e1M0_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ e1M0 Z (u * (x * u * x⁻¹)) ↔ e1R v := by
  rw [← mk_e1Lift, mk_mem_e1M0_iff hb.partC.center hb.mem_iff, hb.conj_lift_eq v, mul_eq_left,
    ← orderOf_dvd_iff_pow_eq_one, hb.partC.order]
  unfold e1R
  omega

variable [Finite G]

theorem map_top_le_centralizer :
    S.map (QuotientGroup.mk' Z) ≤ Subgroup.centralizer {((u * (x * u * x⁻¹) : G) : G ⧸ Z)} := by
  intro s hs
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  rw [← caseC3Word_forty (m := m) (y := y), Subgroup.mem_centralizer_singleton_iff,
    hb.caseC3Word_mul, hb.caseC3Word_mul, c3Mul_forty_comm]

theorem caseC3Word_mem_centralizer (v : Fin 64) :
    caseC3Word Z u m y x v ∈ Subgroup.centralizer {((u * (x * u * x⁻¹) : G) : G ⧸ Z)} :=
  hb.map_top_le_centralizer (hb.caseC3Word_mem v)

theorem e1Sigma_caseC3Word (v : Fin 64) :
    e1Sigma Z (u * (x * u * x⁻¹)) hb.partC.center hb.mem_iff
        ⟨caseC3Word Z u m y x v, hb.caseC3Word_mem_centralizer v⟩ =
      (-1) ^ (v.val / 16 % 2 + v.val / 4 % 2) := by
  have key := hb.caseC3Word_mem_e1M0_iff (v := v)
  unfold e1R at key
  rw [e1Sigma_apply, Subgroup.coe_mk]
  rcases Nat.mod_two_eq_zero_or_one (v.val / 16) with hj | hj <;>
    rcases Nat.mod_two_eq_zero_or_one (v.val / 4) with hl | hl <;> simp [key, hj, hl]

theorem e1M0_inf_map_top :
    e1M0 Z (u * (x * u * x⁻¹)) ⊓ S.map (QuotientGroup.mk' Z) = e1RBar Z u m y x := by
  ext s
  refine ⟨fun ⟨hM, hS⟩ => ?_, fun hR => ⟨?_, hb.e1RBar_le hR⟩⟩
  · obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hS
    exact hb.caseC3Word_mem_e1RBar_iff.mpr (hb.caseC3Word_mem_e1M0_iff.mp hM)
  · obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hR
    exact hb.caseC3Word_mem_e1M0_iff.mpr hv

theorem e1RBar_le_e1M0 : e1RBar Z u m y x ≤ e1M0 Z (u * (x * u * x⁻¹)) :=
  hb.e1M0_inf_map_top ▸ inf_le_left

omit [Finite G] in
theorem sixteen_not_mem_e1M0 : caseC3Word Z u m y x 16 ∉ e1M0 Z (u * (x * u * x⁻¹)) := by
  rw [hb.caseC3Word_mem_e1M0_iff]
  decide

theorem relIndex_e1M0 : (e1M0 Z (u * (x * u * x⁻¹))).relIndex
    (Subgroup.centralizer {((u * (x * u * x⁻¹) : G) : G ⧸ Z)}) = 2 :=
  relIndex_e1M0_of_le hb.partC.center hb.mem_iff le_rfl (hb.caseC3Word_mem_centralizer 16)
    hb.sixteen_not_mem_e1M0

theorem isPGroup_e1RBar : IsPGroup 2 (e1RBar Z u m y x) :=
  IsPGroup.of_card (n := 5) (by rw [hb.card_e1RBar]; norm_num)

theorem not_two_dvd_relIndex (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) :
    ¬ 2 ∣ (e1RBar Z u m y x).relIndex (e1M0 Z (u * (x * u * x⁻¹))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := (S'.mapSurjective (QuotientGroup.mk'_surjective Z)).not_dvd_index
  rw [Sylow.coe_mapSurjective, hS'] at hidx
  have hRS := hb.e1RBar_le
  have hSC := hb.map_top_le_centralizer
  have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hb.e1RBar_le_e1M0 e1M0_le_centralizer
  have h2 := Subgroup.relIndex_mul_relIndex _ _ _ hRS hSC
  have h4 : (e1RBar Z u m y x).relIndex (S.map (QuotientGroup.mk' Z)) = 2 := by
    have h := Subgroup.relIndex_mul_card (e1RBar Z u m y x) (S.map (QuotientGroup.mk' Z))
    rw [inf_eq_left.mpr hRS, hb.card_e1RBar, hb.card_map_top] at h
    omega
  rw [hb.relIndex_e1M0] at h1
  rw [h4] at h2
  have h6 : (e1RBar Z u m y x).relIndex (e1M0 Z (u * (x * u * x⁻¹))) =
      (S.map (QuotientGroup.mk' Z)).relIndex
        (Subgroup.centralizer {((u * (x * u * x⁻¹) : G) : G ⧸ Z)}) := by
    omega
  rw [h6]
  intro hdvd
  exact hidx (Subgroup.relIndex_mul_index hSC ▸ dvd_mul_of_dvd_left hdvd _)

@[expose] noncomputable def e1RSylow (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) :
    Sylow 2 (e1M0 Z (u * (x * u * x⁻¹))) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.toSylow (P := (e1RBar Z u m y x).subgroupOf (e1M0 Z (u * (x * u * x⁻¹))))
    hb.isPGroup_e1RBar.comap_subtype (hb.not_two_dvd_relIndex S' hS')

theorem coe_e1RSylow (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) :
    (hb.e1RSylow S' hS' : Subgroup (e1M0 Z (u * (x * u * x⁻¹)))) =
      (e1RBar Z u m y x).subgroupOf (e1M0 Z (u * (x * u * x⁻¹))) :=
  rfl

theorem mem_e1RBar_of_pow_eq_one (S' : Sylow 2 G) (hS' : (S' : Subgroup G) = S) {g : G ⧸ Z}
    (hgM : g ∈ e1M0 Z (u * (x * u * x⁻¹)))
    (hgR : g ∈ Subgroup.normalizer (e1RBar Z u m y x : Set (G ⧸ Z))) {k : ℕ}
    (hgk : g ^ 2 ^ k = 1) : g ∈ e1RBar Z u m y x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgp : IsPGroup 2 (Subgroup.zpowers g) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hgk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hP := IsPGroup.to_sup_of_normal_left' hb.isPGroup_e1RBar hgp
    (Subgroup.zpowers_le.mpr hgR)
  have hPM : e1RBar Z u m y x ⊔ Subgroup.zpowers g ≤ e1M0 Z (u * (x * u * x⁻¹)) :=
    sup_le hb.e1RBar_le_e1M0 (Subgroup.zpowers_le.mpr hgM)
  have hdvd := Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hPM)
  obtain ⟨n, hn⟩ := hP.index ((e1RBar Z u m y x).subgroupOf
    (e1RBar Z u m y x ⊔ Subgroup.zpowers g))
  have hn0 : n = 0 := by
    by_contra h0
    refine hb.not_two_dvd_relIndex S' hS' (dvd_trans ?_ hdvd)
    rw [Subgroup.relIndex, hn]
    exact dvd_pow_self 2 h0
  rw [hn0, pow_zero] at hn
  exact (Subgroup.relIndex_eq_one (H := e1RBar Z u m y x)
    (K := e1RBar Z u m y x ⊔ Subgroup.zpowers g)).mp hn
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
