module

public import CFSG.LargeExtraspecial.S6EightD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G]

@[expose] def NoA2All (S : Setting G) : Prop :=
  ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → ¬ S.HasTypeAInL g'

structure Hyp (S : Setting G) (g : G) : Prop where
  hyp4 : Hyp4 S g
  cons : Cons311 S g
  noA2 : NoA2All S
  lin : ∀ {t : S.O} (ht : t ∈ S.Lbar g), t ≠ 1 → Rbar S g t = S.Lbar g ∨ LinCase S g ht

variable {S : Setting G} {g : G}

theorem Hyp.noA2' (hy : Hyp S g) : NoA2 S g :=
  fun α h1 h2 h3 => hy.noA2 g hy.hyp4.conj_mem hy.hyp4.conj_ne ⟨α, h1, h2, h3⟩

theorem Hyp.fusion (hy : Hyp S g) : FusionCtl S g :=
  fusionCtl_of_lemma_3_13 hy.hyp4 hy.noA2

omit [Finite G] in
theorem mul_conj_eq_of_conj_eq {g' : G} (hc : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) (h : G) :
    h * g * S.z * (h * g)⁻¹ = h * g' * S.z * (h * g')⁻¹ := by
  rw [mul_conj_z S, mul_conj_z S, hc]

theorem hyp4_of_conj_eq {g' : G} (H : Hyp4 S g) (hc : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) :
    Hyp4 S g' where
  conj_mem := hc ▸ H.conj_mem
  conj_ne := hc ▸ H.conj_ne
  fixSub_eq := by rw [← S.Lbar_eq_of_conj_eq hc, ← hc]; exact H.fixSub_eq
  two_lt_width := H.two_lt_width

theorem cons311_of_conj_eq {g' : G} (C : Cons311 S g) (hc : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) :
    Cons311 S g' where
  weaklyClosed := fun h hh hle => by
    have e := S.Lbar_eq_of_conj_eq (mul_conj_eq_of_conj_eq hc h)
    rw [← e, ← S.Lbar_eq_of_conj_eq hc] at hle ⊢
    exact C.weaklyClosed h hh hle
  card_Lbar := by rw [← S.Lbar_eq_of_conj_eq hc]; exact C.card_Lbar
  card_QG_inf_Qa := by rw [← S.Qa_eq_of_conj_eq hc]; exact C.card_QG_inf_Qa
  comm_le := by
    rw [← S.Lbar_eq_of_conj_eq hc, ← S.Qa_eq_of_conj_eq hc, ← hc]
    exact C.comm_le
  faithful := by
    rw [← S.Lbar_eq_of_conj_eq hc, ← S.Qa_eq_of_conj_eq hc]
    exact C.faithful

theorem Hyp.hyp4_of (hy : Hyp S g) {g' : G} (hQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hz : g' * S.z * g'⁻¹ ≠ S.z) : Hyp4 S g' := by
  obtain ⟨m, hm, hmg⟩ := hy.fusion g' hQ hz
  exact hyp4_of_conj_eq (hy.hyp4.mul ⟨m, hm⟩) (by rw [mul_conj_z S]; exact hmg)

theorem Hyp.cons_of (hy : Hyp S g) {g' : G} (hQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hz : g' * S.z * g'⁻¹ ≠ S.z) : Cons311 S g' := by
  obtain ⟨m, hm, hmg⟩ := hy.fusion g' hQ hz
  exact cons311_of_conj_eq (hy.cons.mul ⟨m, hm⟩) (by rw [mul_conj_z S]; exact hmg)

theorem Vt_le_span_of_Rbar_eq (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (hR : Rbar S g t = S.Lbar g) : Vt S g t ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, hth, rfl⟩
  have hle : S.Lbar ((h : G) * g) ≤ S.Lbar g := hR ▸ Lbar_mul_le_Rbar hth
  have heq := C.weaklyClosed h h.2 (hle.trans (le_normalizer))
  have h1 := cl_mem_fixSub H h
  rw [heq, H.fixSub_eq] at h1
  exact h1

theorem V_le_Qa_of_Rbar_eq (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (hR : Rbar S g t = S.Lbar g) : V S g t ≤ S.Qa g := by
  rw [V_le_Qa_iff H.conj_mem H.conj_ne]
  refine (Vt_le_span_of_Rbar_eq H C hR).trans ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact S.cl_mem_clSub ⟨H.conj_mem, S.conj_z_mem_Qa g⟩ H.conj_mem

theorem Hyp.V_le_Qa (hy : Hyp S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    V S g t ≤ S.Qa g := by
  rcases hy.lin ht ht1 with hR | hL
  · exact V_le_Qa_of_Rbar_eq hy.hyp4 hy.cons hR
  · exact hL.le_Qa

theorem Hyp.mem_Qa_of_mem_La₀ (hy : Hyp S g) {y j : G} (hyL : y ∈ S.L0 g) (hyQ : y ∉ S.QG)
    (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjz : j * S.z * j⁻¹ ≠ S.z) (hyj : y ∈ S.La j) :
    j * S.z * j⁻¹ ∈ S.Qa g := by
  have ht : S.ρ ⟨y, S.L0_le_M g hyL⟩ ∈ S.Lbar g := S.ρ_mem_Lbar hyL
  have ht1 : S.ρ ⟨y, S.L0_le_M g hyL⟩ ≠ 1 := fun h => hyQ ((S.ρ_eq_one_iff _).mp h)
  have hV := hy.V_le_Qa ht ht1
  obtain ⟨m, hm, hmd⟩ := hy.fusion j hjQ hjz
  have hc : ((⟨m, hm⟩ : S.M) : G) * g * S.z * (((⟨m, hm⟩ : S.M) : G) * g)⁻¹ =
      j * S.z * j⁻¹ := by
    rw [mul_conj_z S]
    exact hmd
  have htm : S.ρ ⟨y, S.L0_le_M g hyL⟩ ∈ S.Lbar (((⟨m, hm⟩ : S.M) : G) * g) := by
    rw [S.Lbar_eq_of_conj_eq hc, ← S.map_La_eq_Lbar j]
    exact ⟨⟨y, S.L0_le_M g hyL⟩, mem_subgroupOf.mpr hyj, rfl⟩
  have hdV : ((⟨m, hm⟩ : S.M) : G) * g * S.z * (((⟨m, hm⟩ : S.M) : G) * g)⁻¹ ∈ V S g _ :=
    S.mem_clPre.mpr ⟨by rw [hc]; exact hjQ, cl_mem_Vt htm⟩
  have := hV hdV
  rwa [hc] at this

theorem Hyp.mem_Qa_of_mem_La (hy : Hyp S g) {y k j : G} (hkQ : k * S.z * k⁻¹ ∈ S.QG)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (hyL : y ∈ S.L0 k) (hyQ : y ∉ S.QG)
    (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjz : j * S.z * j⁻¹ ≠ S.z) (hyj : y ∈ S.La j) :
    j * S.z * j⁻¹ ∈ S.Qa k := by
  obtain ⟨m, hm, hmk⟩ := hy.fusion k hkQ hkz
  have hc : m * g * S.z * (m * g)⁻¹ = k * S.z * k⁻¹ := by
    rw [mul_conj_z S]
    exact hmk
  have hyL' : m⁻¹ * y * m ∈ S.L0 g := by
    rw [← mem_L0_mul_iff S hm, show S.L0 (m * g) = S.L0 k by
      unfold Setting.L0; rw [S.Qa_eq_of_conj_eq hc]]
    exact hyL
  have hyQ' : m⁻¹ * y * m ∉ S.QG := fun h => hyQ (by
    simpa [mul_assoc] using S.conj_mem_QG hm h)
  have hj' : (m⁻¹ * j) * S.z * (m⁻¹ * j)⁻¹ = m⁻¹ * (j * S.z * j⁻¹) * m⁻¹⁻¹ := by group
  have hjQ' : (m⁻¹ * j) * S.z * (m⁻¹ * j)⁻¹ ∈ S.QG := by
    rw [hj']
    exact S.conj_mem_QG (S.M.inv_mem hm) hjQ
  have hjz' : (m⁻¹ * j) * S.z * (m⁻¹ * j)⁻¹ ≠ S.z := by
    rw [hj']
    intro h
    apply hjz
    calc j * S.z * j⁻¹ = m * (m⁻¹ * (j * S.z * j⁻¹) * m⁻¹⁻¹) * m⁻¹ := by group
      _ = m * S.z * m⁻¹ := by rw [h]
      _ = S.z := by rw [S.z_comm hm]; group
  have hyj' : m⁻¹ * y * m ∈ S.La (m⁻¹ * j) := by
    have h1 := La_mul (S := S) (g := m⁻¹ * j) ⟨m, hm⟩
    rw [show (m : G) * (m⁻¹ * j) = j by group] at h1
    rw [h1] at hyj
    obtain ⟨w, hw, hwy⟩ := hyj
    rw [← hwy]
    simpa [mul_assoc] using hw
  have h1 := hy.mem_Qa_of_mem_La₀ hyL' hyQ' hjQ' hjz' hyj'
  have h2 := conj_mem_Qa_mul S (h := m) h1
  rw [S.Qa_eq_of_conj_eq hc, hj'] at h2
  simpa [mul_assoc] using h2

theorem Hyp.V_le_Qa_of (hy : Hyp S g) {g' : G} (hQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hz : g' * S.z * g'⁻¹ ≠ S.z) {t : S.O} (ht : t ∈ S.Lbar g') (ht1 : t ≠ 1) :
    V S g' t ≤ S.Qa g' := by
  rw [V_le_Qa_iff hQ hz]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, hth, rfl⟩
  obtain ⟨y, hy1, rfl⟩ := (mem_Lbar S).mp ht
  have hyQ : (y : G) ∉ S.QG := fun h' => ht1 ((S.ρ_eq_one_iff y).mpr h')
  have hbQ := conj_mem_QG' S h.2 hQ
  have hbz := conj_ne_z' S h.2 hz
  have hyh : (y : G) ∈ S.La ((h : G) * g') := by
    rw [← S.map_La_eq_Lbar] at hth
    obtain ⟨y', hy', hyy⟩ := hth
    have hq : ((y'⁻¹ * y : S.M) : G) ∈ S.QG := by
      rw [← S.ρ_eq_one_iff (y'⁻¹ * y), map_mul, map_inv, hyy, inv_mul_cancel]
    have := mul_mem (mem_subgroupOf.mp hy') ((QG_le_La S _) hq)
    simpa using this
  exact S.cl_mem_clSub ⟨hbQ, hy.mem_Qa_of_mem_La hQ hz hy1 hyQ hbQ hbz hyh⟩ hbQ

theorem Hyp.lin_of (hy : Hyp S g) {g' : G} (hQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hz : g' * S.z * g'⁻¹ ≠ S.z) {t : S.O} (ht : t ∈ S.Lbar g') (ht1 : t ≠ 1) :
    Rbar S g' t = S.Lbar g' ∨ LinCase S g' ht := by
  by_cases hR : Rbar S g' t = S.Lbar g'
  · exact Or.inl hR
  have H' := hy.hyp4_of hQ hz
  have hVQ := hy.V_le_Qa_of hQ hz ht ht1
  exact Or.inr ⟨hVQ, RmodN_eq_top H' ht hVQ, two_le_finrank_Vt H' ht hR,
    LmodN_eq_centreGroup H' ht hVQ, fun v hv0 =>
      mem_orbit_of_V_le H' ht hVQ v.2 fun h => hv0 (Subtype.ext h)⟩

theorem Hyp.of_conj (hy : Hyp S g) {g' : G} (hQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hz : g' * S.z * g'⁻¹ ≠ S.z) : Hyp S g' :=
  ⟨hy.hyp4_of hQ hz, hy.cons_of hQ hz, hy.noA2, fun ht ht1 => hy.lin_of hQ hz ht ht1⟩

variable (S g) in
structure Conf (t : S.O) (τ : S.M) (u : G) : Prop where
  mem_Lbar : t ∈ S.Lbar g
  ne_one : t ≠ 1
  lin : LinCase S g mem_Lbar
  rho_eq : S.ρ τ = t
  conj_eq : (τ : G) = u * S.z * u⁻¹
  mem_Qa : g * S.z * g⁻¹ ∈ S.Qa u

variable {t : S.O} {τ : S.M} {u : G}

theorem Conf.not_mem_QG (K : Conf S g t τ u) : (τ : G) ∉ S.QG :=
  tau_not_mem_QG K.ne_one K.rho_eq

theorem Conf.z_not_mem (K : Conf S g t τ u) : S.z ∉ S.Qa u :=
  z_not_mem_Qa_of_tau K.ne_one K.rho_eq K.conj_eq

theorem Conf.Vt_le (hy : Hyp S g) (K : Conf S g t τ u) :
    Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa u) :=
  timmesfeld_6_8 hy.hyp4 hy.noA2' hy.cons hy.fusion K.ne_one K.lin K.rho_eq K.conj_eq K.mem_Qa

theorem Hyp.conf (hy : Hyp S g) {τ : S.M} {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    (hτQ : (τ : G) ∉ S.QG) (hτa : (τ : G) ∈ S.Qa g) (hR : Rbar S g (S.ρ τ) ≠ S.Lbar g) :
    Conf S g (S.ρ τ) τ u := by
  have ht : S.ρ τ ∈ S.Lbar g := S.ρ_mem_Lbar ⟨hτa, τ.2⟩
  have ht1 : S.ρ τ ≠ 1 := fun h => hτQ ((S.ρ_eq_one_iff τ).mp h)
  have hne : u * S.z * u⁻¹ ≠ g * S.z * g⁻¹ := by
    rw [← hτu]
    intro h
    exact hτQ (h ▸ hy.hyp4.conj_mem)
  refine ⟨ht, ht1, (hy.lin ht ht1).resolve_left hR, rfl, hτu, ?_⟩
  exact S.mem_Qa_symm hne (hτu ▸ hτa)

@[expose] def Timmesfeld11_1Stmt (S : Setting G) : Prop :=
  ∃ (k u : G) (hτ : u * S.z * u⁻¹ ∈ S.M), k * S.z * k⁻¹ ∈ S.QG ∧ k * S.z * k⁻¹ ≠ S.z ∧
    u * S.z * u⁻¹ ∉ S.QG ∧ u * S.z * u⁻¹ ∈ S.Qa k ∧
      Rbar S k (S.ρ ⟨u * S.z * u⁻¹, hτ⟩) ≠ S.Lbar k

end CFSG.LargeExtraspecial.S11
