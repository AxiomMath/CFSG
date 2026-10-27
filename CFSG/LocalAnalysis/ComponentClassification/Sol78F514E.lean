module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Pgl

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_zpowers_two {z : G} (hz : orderOf z = 2) :
    CFSG.Open.IsElemAbelian 2 (zpowers z) ∧ Nat.card (zpowers z) = 2 ^ 1 := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, by rw [Nat.card_zpowers, hz, pow_one]⟩
  · obtain ⟨a, i, rfl⟩ := a
    obtain ⟨b, j, rfl⟩ := b
    exact Subtype.ext (Commute.zpow_zpow_self z i j).eq
  · obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz, pow_orderOf_eq_one,
      one_zpow]

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers_two {z w : G} (hz : z * z = 1) (hw : w ∈ zpowers z) :
    w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, hz, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hz, one_zpow, one_mul, zpow_one]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem open_pRank_Q : CFSG.Open.pRank 2 Q = 2 := by
  have h1 := H.sec5.pRank_Q
  rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1

theorem false_of_three_Q {v w : G} (hvQ : v ∈ Q) (hv2 : v * v = 1)
    (hvRs : v ∉ conjugate (S ⊓ L) s) (hwRs : w ∈ conjugate (S ⊓ L) s) (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hwz : w ≠ z) (hvw : v * w = w * v) : False := by
  set H₂ := conjugate (S ⊓ L) s ⊓ centralizer ({v} : Set G) with hH₂
  have hvz : v * z = z * v := H.sec5.zS v (H.sec5.QS hvQ)
  have hwz' : w * z = z * w := H.sec5.zS w (H.Rs_le_S hwRs)
  obtain ⟨hzE, hzcard⟩ := isElemAbelian_zpowers_two H.sec5.z2
  have h2 : 1 + 1 ≤ CFSG.Open.pRank 2 H₂ := by
    refine succ_le_open_pRank_of_commute Nat.prime_two hzE hzcard (b := w) ?_
      (by rw [sq]; exact hw2) ?_ ?_ ?_
    · intro e he
      rcases eq_one_or_eq_of_mem_zpowers_two H.mul_self_z he with rfl | rfl
      · exact Commute.one_left w
      · exact hwz'.symm
    · intro hw
      rcases eq_one_or_eq_of_mem_zpowers_two H.mul_self_z hw with h | h
      · exact hw1 h
      · exact hwz h
    · intro e he
      rcases eq_one_or_eq_of_mem_zpowers_two H.mul_self_z he with rfl | rfl
      · exact one_mem _
      · exact mem_inf.mpr ⟨H.z_mem_Rs, mem_centralizer_singleton_iff.mpr hvz.symm⟩
    · exact mem_inf.mpr ⟨hwRs, mem_centralizer_singleton_iff.mpr hvw.symm⟩
  obtain ⟨E₂, hE₂, hE₂e, hE₂card⟩ := SectionRank.exists_pRank one_lt_two H₂
  have h3 := succ_le_open_pRank_of_commute Nat.prime_two hE₂e hE₂card (b := v)
    (fun e he => mem_centralizer_singleton_iff.mp (mem_inf.mp (hE₂ he)).2)
    (by rw [sq]; exact hv2) (fun hv => hvRs (mem_inf.mp (hE₂ hv)).1)
    (hE₂.trans (inf_le_left.trans H.l511)) hvQ
  rw [H.open_pRank_Q] at h3
  omega

theorem false_of_commutator_le_t {y' : G}
    (hfix : ∀ r ∈ S ⊓ L, r * y' = y' * r → r = 1 ∨ r = t)
    (hcomm : ∀ r ∈ S ⊓ L, y' * r * y'⁻¹ * r⁻¹ = 1 ∨ y' * r * y'⁻¹ * r⁻¹ = t) : False := by
  obtain ⟨ρ, b, j, hD, hc⟩ := H.exists_dihData_R
  have hρR : ρ ∈ S ⊓ L := hD.ρ_mem
  have hbR : b ∈ S ⊓ L := hD.s_mem
  have hcomm_of : ∀ r : G, y' * r * y'⁻¹ * r⁻¹ = 1 → r * y' = y' * r := fun r hr => by
    have h1 : y' * r * y'⁻¹ = r := by
      calc y' * r * y'⁻¹ = y' * r * y'⁻¹ * r⁻¹ * r := by group
        _ = r := by rw [hr, one_mul]
    exact commute_of_conj_eq h1
  have hρne : ρ ≠ 1 ∧ ρ ≠ t := by
    refine ⟨fun e => hD.ρ_sq_ne_one (by rw [e, one_mul]), fun e => hD.ρ_sq_ne_one ?_⟩
    rw [e]; exact H.mul_self_t
  have hbne : b ≠ 1 ∧ b ≠ t := ⟨hD.s_ne_one, by rw [← hc]; exact hD.s_ne_z0⟩
  rcases hcomm ρ hρR with h1 | h1
  · rcases hfix ρ hρR (hcomm_of ρ h1) with e | e
    · exact hρne.1 e
    · exact hρne.2 e
  rcases hcomm b hbR with h2 | h2
  · rcases hfix b hbR (hcomm_of b h2) with e | e
    · exact hbne.1 e
    · exact hbne.2 e
  have htc : ∀ r ∈ S ⊓ L, t * r = r * t := fun r hr => (H.sec5.tZ r (mem_inf.mp hr).1).symm
  have h1' : y' * ρ * y'⁻¹ = t * ρ := by
    calc y' * ρ * y'⁻¹ = y' * ρ * y'⁻¹ * ρ⁻¹ * ρ := by group
      _ = t * ρ := by rw [h1]
  have h2' : y' * b * y'⁻¹ = t * b := by
    calc y' * b * y'⁻¹ = y' * b * y'⁻¹ * b⁻¹ * b := by group
      _ = t * b := by rw [h2]
  have h3 : y' * (b * ρ) * y'⁻¹ = b * ρ := by
    calc y' * (b * ρ) * y'⁻¹ = (y' * b * y'⁻¹) * (y' * ρ * y'⁻¹) := by group
      _ = t * b * (t * ρ) := by rw [h1', h2']
      _ = b * ρ := by
          rw [htc b hbR, show b * t * (t * ρ) = b * (t * t) * ρ by group, H.mul_self_t,
            mul_one]
  rcases hfix _ (mul_mem hbR hρR) (commute_of_conj_eq h3) with e | e
  · exact refl_ne_zpow hD 1 0 (by rw [zpow_one, zpow_zero]; exact e)
  · exact refl_ne_zpow hD 1 (DihData.zc j) (by rw [zpow_one, hc]; exact e)

theorem exists_refl_commute {y' r₀ : G} (hr₀ : r₀ ∈ S ⊓ L) (hr₀2 : r₀ * r₀ = 1)
    (hact : ∀ r ∈ S ⊓ L, y' * r * y'⁻¹ = r₀ * r * r₀⁻¹) :
    ∃ w ∈ S ⊓ L, w * w = 1 ∧ w ≠ 1 ∧ w ≠ t ∧ w * y' = y' * w := by
  obtain ⟨ρ, b, j, hD, hc⟩ := H.exists_dihData_R
  by_cases hr₀c : r₀ = 1 ∨ r₀ = t
  ·
    have hbc : b * y' = y' * b := by
      apply commute_of_conj_eq
      rw [hact b hD.s_mem]
      rcases hr₀c with rfl | rfl
      · group
      · rw [(H.sec5.tZ b (mem_inf.mp hD.s_mem).1).symm]; group
    exact ⟨b, hD.s_mem, hD.s_sq, hD.s_ne_one, by rw [← hc]; exact hD.s_ne_z0, hbc⟩
  · push Not at hr₀c
    refine ⟨r₀, hr₀, hr₀2, hr₀c.1, hr₀c.2, commute_of_conj_eq ?_⟩
    rw [hact r₀ hr₀]; group

variable {y : G} (hyS : y ∈ S) (hy2 : y * y = 1)
  (hfix : ∀ r ∈ S ⊓ L, r * y = y * r → r = 1 ∨ r = t)
  (hfixs : ∀ r ∈ conjugate (S ⊓ L) s, r * y = y * r → r = 1 ∨ r = z)
  {E : Subgroup G} (hES : E ≤ S) (hTE : T ≤ normalizer (E : Set G)) (hE2 : ∀ e ∈ E, e * e = 1)

include hyS hy2 hfixs hTE hE2 in
theorem mem_E_inf_Rs {v : G} (hvE : v ∈ E) (hvRs : v ∈ conjugate (S ⊓ L) s) : v = 1 ∨ v = z := by
  by_contra hne
  push Not at hne
  refine H.false_of_elemAbelian_Rs hyS hy2 hfixs hvRs (hE2 v hvE) hne.1 hne.2 fun g hg => ?_
  have hgv : g * v * g⁻¹ ∈ E := (mem_normalizer_iff.mp (hTE (H.sec5.ST hg)) v).mp hvE
  exact hE2 _ (mul_mem hvE hgv)

include hyS hy2 hfixs hTE hE2 in
theorem mem_E_inf_Q {v : G} (hvE : v ∈ E) (hvQ : v ∈ Q) : v = 1 ∨ v = z := by
  by_cases hvRs : v ∈ conjugate (S ⊓ L) s
  · exact H.mem_E_inf_Rs hyS hy2 hfixs hTE hE2 hvE hvRs
  exfalso
  have hv2 := hE2 v hvE
  have hcomm : ∀ r ∈ conjugate (S ⊓ L) s, v * r * v⁻¹ * r⁻¹ = 1 ∨ v * r * v⁻¹ * r⁻¹ = z := by
    intro r hr
    have hrS : r ∈ S := H.Rs_le_S hr
    have h1 : v * r * v⁻¹ * r⁻¹ ∈ E := by
      have : r * v⁻¹ * r⁻¹ ∈ E :=
        (mem_normalizer_iff.mp (hTE (H.sec5.ST hrS)) _).mp (inv_mem hvE)
      rw [show v * r * v⁻¹ * r⁻¹ = v * (r * v⁻¹ * r⁻¹) by group]
      exact mul_mem hvE this
    have h2 : v * r * v⁻¹ * r⁻¹ ∈ conjugate (S ⊓ L) s :=
      mul_mem ((H.mem_Rs_iff_conj (H.sec5.QS hvQ) r).mp hr) (inv_mem hr)
    exact H.mem_E_inf_Rs hyS hy2 hfixs hTE hE2 h1 h2
  set v' := s * v * s⁻¹ with hv'
  have hv'S : v' ∈ S := by
    have := conj_mem_of_mem_normalizer (inv_mem H.s_mem_normalizer) (H.sec5.QS hvQ)
    rwa [inv_inv] at this
  have hv'2 : v' * v' = 1 := by
    rw [hv', show s * v * s⁻¹ * (s * v * s⁻¹) = s * (v * v) * s⁻¹ by group, hv2]; group
  have hcomm' : ∀ r ∈ S ⊓ L, v' * r * v'⁻¹ * r⁻¹ = 1 ∨ v' * r * v'⁻¹ * r⁻¹ = t := by
    intro r hr
    have he : v' * r * v'⁻¹ * r⁻¹ =
        s * (v * (s⁻¹ * r * s) * v⁻¹ * (s⁻¹ * r * s)⁻¹) * s⁻¹ := by rw [hv']; group
    rcases hcomm (s⁻¹ * r * s) (conj_inv_mem_conjugate hr) with h1 | h1
    · left; rw [he, h1]; group
    · right; rw [he, h1, H.conj_s_z]
  have hnpgl : ¬ (actG L ε v' ∈ Lin ∧ actG L ε v' ∉ innAut5 𝕊) := by
    rintro ⟨hlin, hinn⟩
    exact H.false_of_commutator_le_t
      (fun r hr hrc => H.sec5.eq_one_or_eq_t_of_pgl ε H.autData hv'S hv'2 hlin hinn hr hrc) hcomm'
  obtain ⟨r₀, hr₀, hr₀2, hact⟩ := H.sec5.exists_inner_action ε H.autData hv'S hv'2 hnpgl
  obtain ⟨w, hwR, hw2, hw1, hwt, hwc⟩ := H.exists_refl_commute hr₀ hr₀2 hact
  refine H.false_of_three_Q hvQ hv2 hvRs (conj_inv_mem_conjugate hwR) ?_ ?_ ?_ ?_
  · rw [show s⁻¹ * w * s * (s⁻¹ * w * s) = s⁻¹ * (w * w) * s by group, hw2]; group
  · intro e
    apply hw1
    calc w = s * (s⁻¹ * w * s) * s⁻¹ := by group
      _ = 1 := by rw [e]; group
  · intro e
    apply hwt
    calc w = s * (s⁻¹ * w * s) * s⁻¹ := by group
      _ = t := by rw [e, H.conj_s_z]
  · have hv : v = s⁻¹ * v' * s := by rw [hv']; group
    rw [hv]
    calc s⁻¹ * v' * s * (s⁻¹ * w * s) = s⁻¹ * (v' * w) * s := by group
      _ = s⁻¹ * (w * v') * s := by rw [hwc]
      _ = s⁻¹ * w * s * (s⁻¹ * v' * s) := by group

omit hyS hy2 hfix hfixs hES hTE hE2 in
theorem sq_of_mul_sq {q r : G} (hq : q ∈ Q) (hr : r ∈ S ⊓ L) (h1 : q * r * (q * r) = 1) :
    q * q = 1 ∧ r * r = 1 := by
  have hqr : q * r = r * q := H.sec5.commute_Q_R hq hr
  have h2 : q * q = (r * r)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc q * q * (r * r) = q * (q * r) * r := by group
      _ = q * (r * q) * r := by rw [hqr]
      _ = q * r * (q * r) := by group
      _ = 1 := h1
  have h3 : q * q ∈ Q ⊓ L := mem_inf.mpr ⟨mul_mem hq hq, h2 ▸ inv_mem (mul_mem
    (mem_inf.mp hr).2 (mem_inf.mp hr).2)⟩
  rw [H.sec5.Q_inf_L, mem_bot] at h3
  refine ⟨h3, ?_⟩
  rw [h3] at h2
  exact inv_eq_one.mp h2.symm

include hyS hy2 hfix hfixs hTE hE2 in
theorem mem_Z_of_mem_E (htE : t ∈ E) {e q r : G} (heE : e ∈ E) (hq : q ∈ Q) (hr : r ∈ S ⊓ L)
    (he : e = q * r) : e = 1 ∨ e = z ∨ e = t ∨ e = z * t := by
  have hsq := H.sq_of_mul_sq hq hr (he ▸ hE2 e heE)
  by_cases hr1 : r = 1
  · subst hr1
    rw [mul_one] at he
    subst he
    rcases H.mem_E_inf_Q hyS hy2 hfixs hTE hE2 heE hq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  by_cases hrt : r = t
  · subst hrt
    have hqE : q ∈ E := by
      have := mul_mem heE htE
      rwa [he, mul_assoc, H.mul_self_t, mul_one] at this
    rcases H.mem_E_inf_Q hyS hy2 hfixs hTE hE2 hqE hq with h | h
    · right; right; left; rw [he, h, one_mul]
    · right; right; right; rw [he, h]
  exfalso
  refine H.false_of_elemAbelian_R hyS hy2 hfix hr hsq.2 hr1 hrt fun g hg => ?_
  have hgE : g * e * g⁻¹ ∈ E := (mem_normalizer_iff.mp (hTE (H.sec5.ST hg)) e).mp heE
  have hgq : g * q * g⁻¹ ∈ Q := H.sec5.conj_mem_Q hg hq
  have hgr : g * r * g⁻¹ ∈ S ⊓ L := H.sec5.conj_mem_R hg hr
  have hprod : e * (g * e * g⁻¹) = (q * (g * q * g⁻¹)) * (r * (g * r * g⁻¹)) := by
    have hc : r * (g * q * g⁻¹) = (g * q * g⁻¹) * r := (H.sec5.commute_Q_R hgq hr).symm
    rw [he, show g * (q * r) * g⁻¹ = (g * q * g⁻¹) * (g * r * g⁻¹) by group]
    calc q * r * ((g * q * g⁻¹) * (g * r * g⁻¹)) = q * (r * (g * q * g⁻¹)) * (g * r * g⁻¹) := by
          group
      _ = q * ((g * q * g⁻¹) * r) * (g * r * g⁻¹) := by rw [hc]
      _ = (q * (g * q * g⁻¹)) * (r * (g * r * g⁻¹)) := by group
  have h1 := hE2 _ (mul_mem heE hgE)
  rw [hprod] at h1
  exact (H.sq_of_mul_sq (mul_mem hq hgq) (mul_mem hr hgr) h1).2

include hyS hy2 hfix hfixs hES hTE hE2 in
theorem field_of_mem_E (htE : t ∈ E) {f : G} (hfE : f ∈ E)
    (hfZ : ¬ (f = 1 ∨ f = z ∨ f = t ∨ f = z * t)) :
    actG L ε f ∉ Lin ∧ ∃ r₀ ∈ S ⊓ L, r₀ * r₀ = 1 ∧ ∀ r ∈ S ⊓ L, f * r * f⁻¹ = r₀ * r * r₀⁻¹ := by
  have hfS : f ∈ S := hES hfE
  have hf2 := hE2 f hfE
  have hinn : actG L ε f ∉ innAut5 𝕊 := by
    intro hinn
    obtain ⟨q, hq, r, hr, rfl⟩ := H.sec5.exists_mul_of_inner ε hfS hinn
    exact hfZ (H.mem_Z_of_mem_E hyS hy2 hfix hfixs hTE hE2 htE hfE hq hr rfl)
  have hzR : z ∉ S ⊓ L := fun hz => by
    have : z ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr ⟨hz, H.z_mem_Rs⟩
    rw [H.R_inf_Rs, mem_bot] at this
    exact H.z_ne_one this
  have hcomm : ∀ r ∈ S ⊓ L, f * r * f⁻¹ * r⁻¹ = 1 ∨ f * r * f⁻¹ * r⁻¹ = t := by
    intro r hr
    have hrS := (mem_inf.mp hr).1
    have h1 : f * r * f⁻¹ * r⁻¹ ∈ E := by
      have : r * f⁻¹ * r⁻¹ ∈ E :=
        (mem_normalizer_iff.mp (hTE (H.sec5.ST hrS)) _).mp (inv_mem hfE)
      rw [show f * r * f⁻¹ * r⁻¹ = f * (r * f⁻¹ * r⁻¹) by group]
      exact mul_mem hfE this
    have h2 : f * r * f⁻¹ * r⁻¹ ∈ S ⊓ L := mul_mem (H.sec5.conj_mem_R hfS hr) (inv_mem hr)
    rcases H.mem_Z_of_mem_E hyS hy2 hfix hfixs hTE hE2 htE h1 (one_mem Q) h2
      (one_mul _).symm with h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ h2) hzR
    · exact Or.inr h
    · exfalso
      apply hzR
      have := mul_mem (h ▸ h2) H.sec5.tR
      rwa [mul_assoc, H.mul_self_t, mul_one] at this
  have hnpgl : ¬ (actG L ε f ∈ Lin ∧ actG L ε f ∉ innAut5 𝕊) := by
    rintro ⟨hlin, hinn'⟩
    exact H.false_of_commutator_le_t
      (fun r hr hrc => H.sec5.eq_one_or_eq_t_of_pgl ε H.autData hfS hf2 hlin hinn' hr hrc) hcomm
  exact ⟨fun hlin => hnpgl ⟨hlin, hinn⟩, H.sec5.exists_inner_action ε H.autData hfS hf2 hnpgl⟩

include hyS hy2 hfix hfixs hES hTE hE2 in
theorem exists_field_centralizing (htE : t ∈ E) (hE8 : Nat.card E = 8) :
    ∃ f ∈ S, f * f = 1 ∧ actG L ε f ∉ Lin ∧ (∀ r ∈ S ⊓ L, f * r = r * f) ∧
      ∀ r ∈ conjugate (S ⊓ L) s, f * r = r * f := by
  obtain ⟨f, hfE, hfZ⟩ : ∃ f ∈ E, ¬ (f = 1 ∨ f = z ∨ f = t ∨ f = z * t) := by
    by_contra hall
    push Not at hall
    have hsub : (E : Set G) ⊆ {1, z, t, z * t} := fun f hf => by
      rcases hall f hf with h | h | h | h <;> simp [h]
    have h1 : (E : Set G).ncard ≤ ({1, z, t, z * t} : Set G).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z, t, z * t} : Set G).ncard ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      rw [Set.ncard_singleton]
    have h3 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
    omega
  obtain ⟨hflin, r₀, hr₀, hr₀2, hact₀⟩ :=
    H.field_of_mem_E hyS hy2 hfix hfixs hES hTE hE2 htE hfE hfZ
  set f₁ := s * f * s⁻¹ with hf₁
  have hf₁E : f₁ ∈ E := (mem_normalizer_iff.mp (hTE H.sT) f).mp hfE
  have hf : f = s⁻¹ * f₁ * s := by rw [hf₁]; group
  have hf₁Z : ¬ (f₁ = 1 ∨ f₁ = z ∨ f₁ = t ∨ f₁ = z * t) := by
    intro h
    apply hfZ
    rcases h with h | h | h | h
    · left; rw [hf, h]; group
    · right; right; left; rw [hf, h, H.conj_s_inv_z]
    · right; left; rw [hf, h, H.conj_s_inv_t]
    · right; right; right; rw [hf, h, H.conj_s_inv_d]
  obtain ⟨-, r₁, hr₁, hr₁2, hact₁⟩ :=
    H.field_of_mem_E hyS hy2 hfix hfixs hES hTE hE2 htE hf₁E hf₁Z
  set r₀' := s⁻¹ * r₁ * s with hr₀'
  have hr₀'Rs : r₀' ∈ conjugate (S ⊓ L) s := conj_inv_mem_conjugate hr₁
  have hr₀'2 : r₀' * r₀' = 1 := by
    rw [hr₀', show s⁻¹ * r₁ * s * (s⁻¹ * r₁ * s) = s⁻¹ * (r₁ * r₁) * s by group, hr₁2]; group
  have hact₀' : ∀ w ∈ conjugate (S ⊓ L) s, f * w * f⁻¹ = r₀' * w * r₀'⁻¹ := by
    intro w hw
    have h1 := hact₁ (s * w * s⁻¹) (mem_conjugate_iff.mp hw)
    calc f * w * f⁻¹ = s⁻¹ * (f₁ * (s * w * s⁻¹) * f₁⁻¹) * s := by rw [hf₁]; group
      _ = s⁻¹ * (r₁ * (s * w * s⁻¹) * r₁⁻¹) * s := by rw [h1]
      _ = r₀' * w * r₀'⁻¹ := by rw [hr₀']; group
  have hfS : f ∈ S := hES hfE
  have hr₀S : r₀ ∈ S := (mem_inf.mp hr₀).1
  have hr₀'S : r₀' ∈ S := H.Rs_le_S hr₀'Rs
  have hr₀f : r₀ * f = f * r₀ := commute_of_conj_eq (by rw [hact₀ r₀ hr₀]; group)
  have hr₀'f : r₀' * f = f * r₀' := commute_of_conj_eq (by rw [hact₀' r₀' hr₀'Rs]; group)
  have hr₀r₀' : r₀ * r₀' = r₀' * r₀ := H.commute_R_Rs hr₀ hr₀'Rs
  refine ⟨f * r₀ * r₀', mul_mem (mul_mem hfS hr₀S) hr₀'S, ?_, ?_, ?_, ?_⟩
  · calc f * r₀ * r₀' * (f * r₀ * r₀') = f * (r₀ * (r₀' * f)) * r₀ * r₀' := by group
      _ = f * (r₀ * (f * r₀')) * r₀ * r₀' := by rw [hr₀'f]
      _ = f * ((r₀ * f) * r₀') * r₀ * r₀' := by group
      _ = f * ((f * r₀) * r₀') * r₀ * r₀' := by rw [hr₀f]
      _ = (f * f) * r₀ * (r₀' * r₀) * r₀' := by group
      _ = (f * f) * r₀ * (r₀ * r₀') * r₀' := by rw [hr₀r₀']
      _ = (f * f) * (r₀ * r₀) * (r₀' * r₀') := by group
      _ = 1 := by rw [hE2 f hfE, hr₀2, hr₀'2]; group
  · intro hlin
    apply hflin
    have hN := fun x (hx : x ∈ S) => H.sec5.S_le hx
    have h1 : actG L ε (f * r₀ * r₀') = actG L ε f * actG L ε r₀ * actG L ε r₀' := by
      rw [actG_mul ε (mul_mem (hN f hfS) (hN r₀ hr₀S)) (hN r₀' hr₀'S),
        actG_mul ε (hN f hfS) (hN r₀ hr₀S)]
    have h2 : actG L ε r₀' = 1 := (H.sec5.actG_eq_one_iff_mem_Q ε hr₀'S).mpr (H.l511 hr₀'Rs)
    have h3 : actG L ε r₀ ∈ Lin := by
      rw [actG_of_mem_self ε (mem_inf.mp hr₀).2]
      exact H.autData.inn_le ⟨_, rfl⟩
    rw [h1, h2, mul_one] at hlin
    have := Subgroup.mul_mem _ hlin (Subgroup.inv_mem _ h3)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this
  · intro r hr
    have hrr₀ : r₀ * r * r₀⁻¹ ∈ S ⊓ L := H.sec5.conj_mem_R hr₀S hr
    have hr₀'r : r₀' * r = r * r₀' := (H.commute_R_Rs hr hr₀'Rs).symm
    refine (commute_of_conj_eq ?_).symm
    calc f * r₀ * r₀' * r * (f * r₀ * r₀')⁻¹ = f * (r₀ * (r₀' * r * r₀'⁻¹) * r₀⁻¹) * f⁻¹ := by
          group
      _ = f * (r₀ * r * r₀⁻¹) * f⁻¹ := by rw [hr₀'r]; group
      _ = r₀ * (r₀ * r * r₀⁻¹) * r₀⁻¹ := hact₀ _ hrr₀
      _ = (r₀ * r₀) * r * (r₀ * r₀)⁻¹ := by group
      _ = r := by rw [hr₀2]; group
  · intro w hw
    have hww : r₀' * w * r₀'⁻¹ ∈ conjugate (S ⊓ L) s :=
      (H.mem_Rs_iff_conj hr₀'S w).mp hw
    have hr₀w : r₀ * (r₀' * w * r₀'⁻¹) = (r₀' * w * r₀'⁻¹) * r₀ := H.commute_R_Rs hr₀ hww
    refine (commute_of_conj_eq ?_).symm
    calc f * r₀ * r₀' * w * (f * r₀ * r₀')⁻¹ =
        f * (r₀ * (r₀' * w * r₀'⁻¹) * r₀⁻¹) * f⁻¹ := by group
      _ = f * (r₀' * w * r₀'⁻¹) * f⁻¹ := by rw [hr₀w]; group
      _ = r₀' * (r₀' * w * r₀'⁻¹) * r₀'⁻¹ := hact₀' _ hww
      _ = (r₀' * r₀') * w * (r₀' * r₀')⁻¹ := by group
      _ = w := by rw [hr₀'2]; group

end Hyp

end CFSG.ComponentClassification.Sol78.F514
