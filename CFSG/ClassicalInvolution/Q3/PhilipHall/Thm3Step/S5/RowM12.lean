module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowsBasic
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift
public import Certificates.Certificate516002

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.Blueprint Certificates.S5Rows Certificates.S5RowsM12

theorem m12RowsF2a_holds : m12RowsF2a () = true :=
  Certificates.certificate516002.1

theorem m12RowsF2b_holds : m12RowsF2b () = true :=
  Certificates.certificate516002.2

abbrev sylowM12 : Subgroup NativeSporadic.M12 :=
  ComponentClassification.M12Cover.S.subgroupOf NativeSporadic.M12

theorem mem_sylowL {s : NativeSporadic.M12} (hs : s ∈ sylowM12) : s ∈ sylowL () := by
  obtain ⟨x, hx, rfl⟩ := M12Model.exists_eltM (Subgroup.mem_subgroupOf.mp hs)
  exact List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩

theorem m12_conj_mem_sylow (H : Subgroup NativeSporadic.M12)
    (hH : IsPGroup 2 H) : ∃ g : NativeSporadic.M12, ∀ x ∈ H, g⁻¹ * x * g ∈ sylowM12 := by
  obtain ⟨g, hg⟩ := M12Model.exists_conj_mem_S_of_isPGroup hH
  exact ⟨g, fun x hx => Subgroup.mem_subgroupOf.mpr (hg x hx)⟩

theorem m12_threeCyc {i j : NativeSporadic.M12}
    (hi : i ∈ sylowM12) (hj : j ∈ sylowM12) (hij : Q8Rel i j) :
    ∃ y : NativeSporadic.M12, y⁻¹ * i * y = j ∧ (y⁻¹ * j * y = i * j ∨ y⁻¹ * j * y = j * i) := by
  obtain ⟨y, -, hy⟩ := threeCycCheck_sound (L := sylowL ()) (Y := czL ()) (p := fun _ => true)
    m12RowsF2a_holds (mem_sylowL hi) (mem_sylowL hj) rfl rfl hij
  exact ⟨y, hy⟩

theorem m12_invPair {i j : NativeSporadic.M12}
    (hi : i ∈ sylowM12) (hj : j ∈ sylowM12) (hij : Q8Rel i j) :
    ∃ u : NativeSporadic.M12, ∃ x ∈ q8Span i j, u * u = 1 ∧ u ≠ 1 ∧ u⁻¹ * i * u ∈ q8Span i j ∧
      u⁻¹ * j * u ∈ q8Span i j ∧ u * x * (u * x) = 1 ∧ u * x ≠ 1 ∧
      ComponentClassification.M12Cover.fixedCount u ≠
        ComponentClassification.M12Cover.fixedCount (u * x) := by
  obtain ⟨u, -, x, hx, h1⟩ := invPairCheck_sound (L := sylowL ()) (f := M12Model.fp)
    m12RowsF2b_holds (mem_sylowL hi) (mem_sylowL hj) hij
  exact ⟨u, x, hx, h1⟩

section Row

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {K Q : Subgroup G}
  {X : Type} [Group X] {ρ : G →* X}

theorem S5Hyp.commutator_eq_top_of_m12
    (h : S5Hyp Φ K Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Q) (θ : X ≃* NativeSporadic.M12) : commutator G = ⊤ :=
  h.commutator_eq_top fun _ hT => h.le_commutator_of_model hρ hker θ sylowM12
    m12_conj_mem_sylow ⊤ (fun _ hi _ hj _ _ hij => m12_threeCyc hi hj hij) hT
    fun _ _ => Subgroup.mem_top _

theorem false_of_m12_lift
    (hQc : Q ≤ Subgroup.center G) (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) (hperf : commutator G = ⊤)
    (π : G →* NativeSporadic.M12) (hπ : Function.Surjective π) (hker : π.ker = Q)
    {T : Subgroup G} (hTQ : T ⊓ Q = ⊥) {u x : G} (hu : u ∈ Subgroup.normalizer (T : Set G))
    (hx : x ∈ T) (hu2 : π u * π u = 1) (hu1 : π u ≠ 1) (hux2 : π (u * x) * π (u * x) = 1)
    (hux1 : π (u * x) ≠ 1)
    (hfix : ComponentClassification.M12Cover.fixedCount (π u) ≠
      ComponentClassification.M12Cover.fixedCount (π (u * x))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  obtain ⟨H, hH⟩ := exists_index_two_of_isPGroup hQ2
  set Q₀ : Subgroup G := H.map Q.subtype with hQ₀
  have hQ₀Q : Q₀ ≤ Q := Subgroup.map_subtype_le H
  have hmemQ₀ : ∀ q (hq : q ∈ Q), q ∈ Q₀ ↔ (⟨q, hq⟩ : Q) ∈ H := by
    intro q hq
    constructor
    · rintro ⟨q', hq', hqq'⟩
      have : q' = ⟨q, hq⟩ := Subtype.ext hqq'
      rwa [← this]
    · intro hqH
      exact ⟨⟨q, hq⟩, hqH, rfl⟩
  haveI : Q₀.Normal := Subgroup.normal_of_le_center (hQ₀Q.trans hQc)
  have hHtop : H ≠ ⊤ := by
    intro hHt
    rw [hHt, Subgroup.index_top] at hH
    exact absurd hH (by norm_num)
  obtain ⟨⟨q₁, hq₁Q⟩, hq₁H⟩ : ∃ q : Q, q ∉ H := by
    by_contra hall
    push Not at hall
    exact hHtop (eq_top_iff.mpr fun q _ => hall q)
  have hq₁ : q₁ ∉ Q₀ := fun h1 => hq₁H ((hmemQ₀ q₁ hq₁Q).mp h1)
  have hsplit : ∀ q ∈ Q, q ∈ Q₀ ∨ q * q₁⁻¹ ∈ Q₀ := by
    intro q hq
    by_cases hqH : (⟨q, hq⟩ : Q) ∈ H
    · exact Or.inl ((hmemQ₀ q hq).mpr hqH)
    · right
      have h1 := Subgroup.mul_mem_iff_of_index_two hH (a := ⟨q, hq⟩) (b := (⟨q₁, hq₁Q⟩ : Q)⁻¹)
      have h2 : (⟨q₁, hq₁Q⟩ : Q)⁻¹ ∉ H := fun h3 => hq₁H (by simpa using H.inv_mem h3)
      have h3 : (⟨q, hq⟩ : Q) * (⟨q₁, hq₁Q⟩ : Q)⁻¹ ∈ H := h1.mpr (iff_of_false hqH h2)
      exact ⟨_, h3, rfl⟩
  have hq₁sq : q₁ * q₁ ∈ Q₀ := ⟨_, Subgroup.mul_self_mem_of_index_two hH ⟨q₁, hq₁Q⟩, rfl⟩
  set mk : G →* G ⧸ Q₀ := QuotientGroup.mk' Q₀ with hmk
  have hle : Q₀ ≤ π.ker := hker ▸ hQ₀Q
  set πL : G ⧸ Q₀ →* NativeSporadic.M12 := QuotientGroup.lift Q₀ π hle with hπL
  have hπLmk : ∀ g, πL (mk g) = π g := fun g => rfl
  have hπLs : Function.Surjective πL := fun m => by
    obtain ⟨g, rfl⟩ := hπ m
    exact ⟨mk g, rfl⟩
  set t : G ⧸ Q₀ := mk q₁ with ht
  have ht1 : t ≠ 1 := by
    rw [ht, hmk, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hq₁
  have htt : t * t = 1 := by
    rw [ht, ← map_mul, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hq₁sq
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hmkQ : ∀ q ∈ Q, mk q = 1 ∨ mk q = t := by
    intro q hq
    rcases hsplit q hq with h1 | h1
    · left
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h1
    · right
      have h2 : mk (q * q₁⁻¹) = 1 := by
        rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact h1
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
  have hkerL : πL.ker = Subgroup.zpowers t := by
    rw [hπL, QuotientGroup.ker_lift, hker]
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨q₁, hq₁Q, rfl⟩)
    rintro _ ⟨q, hq, rfl⟩
    rcases hmkQ q hq with h1 | h1
    · rw [h1]
      exact (Subgroup.zpowers t).one_mem
    · rw [h1]
      exact Subgroup.mem_zpowers t
  have htZ : t ∈ Subgroup.center (G ⧸ Q₀) := by
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q₀ l
    rw [ht, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hQc hq₁Q) g)]
  have hZ : Subgroup.center (G ⧸ Q₀) = Subgroup.zpowers t := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr htZ)
    intro z hz
    rw [← hkerL, MonoidHom.mem_ker]
    have h1 : πL z ∈ Subgroup.center NativeSporadic.M12 := by
      rw [Subgroup.mem_center_iff]
      intro m
      obtain ⟨l, rfl⟩ := hπLs m
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [CFSG.Sporadic.Schreier.m12_center_eq_bot', Subgroup.mem_bot] at h1
    exact h1
  have hLq : CFSG.Assembly.IsQuasisimple (G ⧸ Q₀) := by
    refine ⟨commutator_eq_top_of_surjective mk (QuotientGroup.mk'_surjective Q₀) hperf, ?_⟩
    haveI : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact (QuotientGroup.liftEquiv (Subgroup.center (G ⧸ Q₀)) hπLs
      (hZ.trans hkerL.symm)).isSimpleGroup
  obtain ⟨h40, h4, h0⟩ := ComponentClassification.M12Cover.m12_double_cover_involution_lift_orders
    hLq hto hZ πL hπLs hkerL
  have hord : ∀ v : G, π v * π v = 1 → π v ≠ 1 → orderOf (πL (mk v)) = 2 := fun v h2 h1 =>
    orderOf_eq_prime (by rw [hπLmk, sq]; exact h2) (by rw [hπLmk]; exact h1)
  have hsq1 : ∀ v : G, orderOf (mk v) = 2 → mk v * mk v = 1 := fun v hv => by
    rw [← sq, ← hv, pow_orderOf_eq_one]
  have htT : t ∉ T.map mk := by
    rintro ⟨τ, hτ, hτt⟩
    apply ht1
    have h1 : τ⁻¹ * q₁ ∈ Q₀ := by
      rw [← QuotientGroup.eq]
      exact hτt.trans rfl
    have h2 : τ ∈ Q := by
      have h3 : τ⁻¹ ∈ Q := by
        have := Q.mul_mem (hQ₀Q h1) (Q.inv_mem hq₁Q)
        rwa [mul_inv_cancel_right] at this
      simpa using Q.inv_mem h3
    have h4 : τ ∈ T ⊓ Q := Subgroup.mem_inf.mpr ⟨hτ, h2⟩
    rw [hTQ, Subgroup.mem_bot] at h4
    rw [← hτt, h4, map_one]
  have hun : mk u ∈ Subgroup.normalizer ((T.map mk : Subgroup (G ⧸ Q₀)) : Set (G ⧸ Q₀)) :=
    mk_mem_normalizer_map hu
  have hxT : mk x ∈ T.map mk := Subgroup.mem_map_of_mem mk hx
  have hmul : mk u * mk x = mk (u * x) := (map_mul mk u x).symm
  have hf1 := h40 _ (hord u hu2 hu1)
  have hf2 := h40 _ (hord (u * x) hux2 hux1)
  rw [hπLmk] at hf1 hf2
  refine false_of_lift_squares htZ htT hun hxT ?_
  rw [hmul]
  rcases hf1 with hf1 | hf1 <;> rcases hf2 with hf2 | hf2
  · exact absurd (hf1.trans hf2.symm) hfix
  · left
    refine ⟨hsq1 u (h4 _ (hord u hu2 hu1) (by rw [hπLmk]; exact hf1)), ?_⟩
    rw [← sq]
    exact (h0 _ (hord (u * x) hux2 hux1) (by rw [hπLmk]; exact hf2)).1
  · right
    refine ⟨?_, hsq1 (u * x) (h4 _ (hord (u * x) hux2 hux1) (by rw [hπLmk]; exact hf2))⟩
    rw [← sq]
    exact (h0 _ (hord u hu2 hu1) (by rw [hπLmk]; exact hf1)).1
  · exact absurd (hf1.trans hf2.symm) hfix

theorem S5Hyp.false_of_rowM12
    (h : S5Hyp Φ K Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Q) (hrow : NativeSporadic.IsSporadic X .M12) : False := by
  obtain ⟨θ₀⟩ := hrow
  let θ : X ≃* NativeSporadic.M12 := θ₀
  have hperf := h.commutator_eq_top_of_m12 hρ hker θ
  obtain ⟨T, hT⟩ := h.exists_mem_RSet
  obtain ⟨e⟩ := h.nonempty_q8 hT
  obtain ⟨i, hi, j, hj, hij, hspan⟩ := exists_q8Pair e
  obtain ⟨g, hgP, hq⟩ :=
    h.exists_model_pair hker θ.toMonoidHom θ.injective sylowM12 m12_conj_mem_sylow hT hi hij
  simp only [MulEquiv.coe_toMonoidHom] at hgP hq
  obtain ⟨u, x, hx, hu2, hu1, hui, huj, hux2, hux1, hfix⟩ :=
    m12_invPair (hgP i hi) (hgP j hj) hq
  set φ : G →* NativeSporadic.M12 := (MulAut.conj g⁻¹).toMonoidHom.comp (θ.toMonoidHom.comp ρ)
    with hφ
  have hφx : ∀ a : G, φ a = g⁻¹ * θ (ρ a) * g := fun a => by
    simp [hφ, MulAut.conj_apply]
  have hθφ : ∀ a : G, θ (ρ a) = g * φ a * g⁻¹ := fun a => by
    rw [hφx]
    group
  rw [← hφx, ← hφx] at hx hui huj
  obtain ⟨x₀, hx₀, rfl⟩ := exists_of_mem_q8Span_map φ hx
  obtain ⟨wi, hwi, hwi'⟩ := exists_of_mem_q8Span_map φ hui
  obtain ⟨wj, hwj, hwj'⟩ := exists_of_mem_q8Span_map φ huj
  set ub : X := θ.symm (g * u * g⁻¹) with hub
  have hθub : θ ub = g * u * g⁻¹ := by rw [hub, MulEquiv.apply_symm_apply]
  have hconj : ∀ a w : G, φ w = u⁻¹ * φ a * u → ub⁻¹ * ρ a * ub = ρ w := by
    intro a w haw
    apply θ.injective
    rw [map_mul, map_mul, map_inv, hθub, hθφ a, hθφ w, haw]
    group
  have hTi : ub⁻¹ * ρ i * ub ∈ T.map ρ := by
    rw [hconj i wi hwi']
    exact Subgroup.mem_map_of_mem ρ (mem_of_mem_q8Span hi hj hwi)
  have hTj : ub⁻¹ * ρ j * ub ∈ T.map ρ := by
    rw [hconj j wj hwj']
    exact Subgroup.mem_map_of_mem ρ (mem_of_mem_q8Span hi hj hwj)
  obtain ⟨u₀, hu₀, -, hu₀N⟩ := h.exists_lift_normalizer hρ hker hT hi hj hspan hTi hTj
  set π : G →* NativeSporadic.M12 := θ.toMonoidHom.comp ρ with hπdef
  have hπ : Function.Surjective π := θ.surjective.comp hρ
  have hπker : π.ker = Q := by
    rw [hπdef, MonoidHom.ker_comp_of_injective _ _ θ.injective, hker]
  have hπu : π u₀ = g * u * g⁻¹ := by
    rw [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hu₀, hθub]
  have hπux : π (u₀ * x₀) = g * (u * φ x₀) * g⁻¹ := by
    rw [map_mul, hπu, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hθφ]
    group
  have hc1 : ∀ v : NativeSporadic.M12, v * v = 1 → g * v * g⁻¹ * (g * v * g⁻¹) = 1 :=
    fun v hv => by
      calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [hv]; group
  have hc2 : ∀ v : NativeSporadic.M12, v ≠ 1 → g * v * g⁻¹ ≠ 1 := fun v hv h1 => hv (by
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  refine false_of_m12_lift h.le_center h.pgrp h.ne_bot hperf π hπ hπker (h.inf_eq_bot_RSet hT)
    hu₀N (mem_of_mem_q8Span hi hj hx₀) ?_ ?_ ?_ ?_ ?_
  · rw [hπu]
    exact hc1 u hu2
  · rw [hπu]
    exact hc2 u hu1
  · rw [hπux]
    exact hc1 _ hux2
  · rw [hπux]
    exact hc2 _ hux1
  · rw [hπu, hπux, ComponentClassification.M12Cover.fixedCount_conj,
      ComponentClassification.M12Cover.fixedCount_conj]
    exact hfix

end Row

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
