module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfGen

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups Subgroup
open CFSG.ComponentClassification.GSThmB

namespace Q3ConfData

variable {K₀ : Type} [Group K₀] {G : Type} [Group G] (D : Q3ConfData K₀ G)

theorem L_le : D.L ≤ D.M.P := by
  rw [← D.commL]
  exact (commutator_le_self _).trans inf_le_left

theorem L_le_A : D.L ≤ D.M.A := D.L_le.trans D.PA

theorem Q₀_le_A : D.Q₀ ≤ D.M.A := fun _ hq => (D.Q₀le hq).1

theorem Q₀_comm_s₀ {q : G} (hq : q ∈ D.Q₀) : q * D.s₀ = D.s₀ * q :=
  mem_centralizer_singleton_iff.1 (D.Q₀le hq).2

end Q3ConfData

variable {K₀ : Type} [Group K₀] [Finite K₀] {G : Type} [Group G]

theorem props_of_model (D : Q3ConfData K₀ G) (M : AutModel K₀ G) (hP : M.P = D.M.P)
    (hA : M.A = D.M.A) (c : Cat8.Q3Conf K₀) (ha : M.ι c.a = D.s₀)
    (hQ : c.Q.map M.ι = D.Q₀) : c.Props := by
  classical
  have : Finite (MulAut K₀) :=
    Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀)) DFunLike.coe_injective
  have : Finite D.M.A := Finite.of_equiv _ D.M.Φ.toEquiv
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact D.PA
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by rw [hP, hA]; exact D.cent
  have hιA : ∀ θ, M.ι θ ∈ D.M.A := fun θ => by rw [← hA]; exact M.ι_mem θ
  have hInn : (Cat8.Inn K₀).map M.ι = D.M.P := by rw [map_Inn M hPA hcent, hP]
  have hinn : ∀ θ, θ ∈ Cat8.Inn K₀ ↔ M.ι θ ∈ D.M.P := fun θ => by rw [← hInn, mem_map_ι]
  have hpre : ∀ y ∈ D.M.A, ∃ θ, M.ι θ = y := fun y hy =>
    exists_ι_eq M (by rw [hA]; exact hy)
  have hcomap : ∀ X : Subgroup G, X ≤ D.M.A → (X.comap M.ι).map M.ι = X := fun X hX =>
    map_comap_ι M (by rw [hA]; exact hX)
  have hmapC : ∀ θ, (centralizer ({θ} : Set (MulAut K₀))).map M.ι =
      D.M.A ⊓ centralizer ({M.ι θ} : Set G) := fun θ => by
    rw [← hA]; exact map_centralizer_singleton M θ
  have hL0 : (Cat8.L0 K₀ c.a).map M.ι = D.L := by
    rw [map_L0 M hPA hcent, ha, hP, D.commL]
  have hDmap : c.D.map M.ι = D.Q₀ ⊓ D.L := by
    rw [Cat8.Q3Conf.D, map_inf_eq _ _ _ M.ι_injective, hQ, hL0]
  obtain ⟨q, hq, hgq⟩ : ∃ q ∈ D.Q₀, M.ι c.g = D.g₀ * q := by
    have hnorm : ∀ q ∈ D.Q₀, M.ι c.g * q * (M.ι c.g)⁻¹ ∈ D.Q₀ := by
      intro q hq
      rw [← hQ] at hq ⊢
      obtain ⟨η, hη, rfl⟩ := hq
      have := (mem_normalizer_iff.1 c.g_norm η).1 hη
      rw [← map_inv, ← map_mul, ← map_mul]
      exact mem_map_of_mem _ this
    have hnot : M.ι c.g ∉ D.Q₀ := by rw [← hQ, mem_map_ι]; exact c.g_not_mem
    exact ⟨_, D.g_coset _ (hιA c.g) hnorm hnot, by group⟩
  have hgQ₀ : D.g₀ = M.ι c.g * q⁻¹ := by rw [hgq]; group
  have hτ : M.ι c.tau = D.τ₀ := by
    have hqs : q * D.s₀ = D.s₀ * q := D.Q₀_comm_s₀ hq
    have hqs' : D.s₀ * q⁻¹ = q⁻¹ * D.s₀ := by
      calc D.s₀ * q⁻¹ = q⁻¹ * (q * D.s₀) * q⁻¹ := by group
        _ = q⁻¹ * (D.s₀ * q) * q⁻¹ := by rw [hqs]
        _ = q⁻¹ * D.s₀ := by group
    show M.ι (c.a * (c.g⁻¹ * c.a * c.g)) = D.τ₀
    rw [map_mul, map_mul, map_mul, map_inv, ha, hgq]
    calc D.s₀ * ((D.g₀ * q)⁻¹ * D.s₀ * (D.g₀ * q))
        = (D.s₀ * q⁻¹) * (D.g₀⁻¹ * D.s₀ * D.g₀) * q := by group
      _ = q⁻¹ * (D.s₀ * (D.g₀⁻¹ * D.s₀ * D.g₀)) * q := by rw [hqs']; group
      _ = q⁻¹ * (D.τ₀ * q) := by rw [← D.τ_eq]; group
      _ = q⁻¹ * (q * D.τ₀) := by rw [D.τ_Q q hq]
      _ = D.τ₀ := by group
  have hz : M.ι c.z = D.z₀ := by
    have hzD : M.ι c.z ∈ D.Q₀ ⊓ D.L := by rw [← hDmap]; exact mem_map_of_mem _ c.z_mem
    refine D.z_unique _ hzD ?_ ?_ ?_
    · intro v hv
      rw [← hDmap] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      rw [← map_mul, ← map_mul, c.z_comm w hw]
    · rw [← map_mul, c.z_sq, map_one]
    · intro h1
      exact c.z_ne (M.ι_injective (h1.trans (map_one _).symm))
  obtain ⟨mA, hmA, hcardA⟩ := D.card_A
  have hcardAut : Nat.card (MulAut K₀) = 2 ^ 7 * mA := by rw [M.card_mulAut, hA, hcardA]
  have hcardR : Nat.card c.R = 128 := by
    obtain ⟨T, hT⟩ := c.R_sylow
    rw [← hT, card_sylow_of_card T hmA hcardAut]
    norm_num
  have hR : c.R.map M.ι = D.R₀ := by
    refine D.R_unique _ (fun y hy => ?_) ?_ ?_ ?_
    · obtain ⟨θ, -, rfl⟩ := hy
      exact hιA θ
    · rw [card_map_ι, hcardR]
    · rw [← hQ]
      exact map_mono c.Q_le_R
    · rw [hgQ₀]
      refine mul_mem (mem_map_of_mem _ c.g_mem_R) (inv_mem ?_)
      rw [← hQ] at hq
      exact map_mono c.Q_le_R hq
  have hR0 : c.R0.map M.ι = D.R₀ ⊓ centralizer ({D.z₀} : Set G) := by
    rw [Cat8.Q3Conf.R0, map_inf_eq _ _ _ M.ι_injective, hR, hmapC, hz, ← inf_assoc,
      inf_eq_left.2 D.R_le]
  have hR0A : D.R₀ ⊓ centralizer ({D.z₀} : Set G) ≤ D.M.A := inf_le_left.trans D.R_le
  have hzτ : D.z₀ * D.τ₀ = M.ι (c.z * c.tau) := by rw [map_mul M.ι c.z c.tau, hz, hτ]
  exact
  { card_D := by
      refine ⟨?_, ?_, hcardR⟩
      · rw [← card_map_ι M, hDmap, D.card_D.1]
      · rw [← card_map_ι M, hQ, D.cardQ₀]
        norm_num
    Q_eq := by
      apply map_ι_injective M
      rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hDmap,
        hτ, ha, hQ]
      exact D.Q_eq
    tau_comm := by
      intro w hw
      apply M.ι_injective
      rw [map_mul M.ι c.tau w, map_mul M.ι w c.tau, hτ]
      exact D.τ_Q _ (by rw [← hQ]; exact mem_map_of_mem _ hw)
    card_fix_tau := by
      rw [← card_map_ι M, map_inf_eq _ _ _ M.ι_injective, hL0, hmapC, hτ, ← inf_assoc,
        inf_eq_left.2 D.L_le_A]
      exact D.fix_τ
    g_z := by
      apply M.ι_injective
      rw [map_mul, map_mul, map_inv, hz, hgq]
      calc (D.g₀ * q)⁻¹ * D.z₀ * (D.g₀ * q) = q⁻¹ * (D.g₀⁻¹ * D.z₀ * D.g₀) * q := by group
        _ = q⁻¹ * (D.z₀ * q) := by rw [D.g_z]; group
        _ = q⁻¹ * (q * D.z₀) := by rw [D.z_Q q hq]
        _ = D.z₀ := by group
    tz_central := by
      have hT₀A : D.T₀ ≤ D.M.A := fun x hx => (D.T_le hx).1
      have hcT : Nat.card (D.T₀.comap M.ι) = 2 ^ 7 := by
        rw [← card_map_ι M, hcomap _ hT₀A, D.card_T]
        norm_num
      obtain ⟨T, hT⟩ := sylow_of_card (D.T₀.comap M.ι) hmA hcardAut hcT
      refine ⟨T, ?_⟩
      rw [hT]
      intro x hx
      rw [mem_centralizer_singleton_iff]
      apply M.ι_injective
      have h1 := mem_centralizer_singleton_iff.1 (D.T_le (mem_comap.1 hx)).2
      rw [map_mul M.ι x (c.tau * c.z), map_mul M.ι (c.tau * c.z) x, map_mul M.ι c.tau c.z, hτ,
        hz]
      exact h1
    tz_comm := by
      intro T hT
      obtain ⟨m₁, hm₁, hC⟩ := D.card_Ctz
      have : Finite ↥(D.M.A ⊓ centralizer ({D.τ₀ * D.z₀} : Set G)) :=
        Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
      have hTmap : (T : Subgroup (MulAut K₀)).map M.ι ≤
          D.M.A ⊓ centralizer ({D.τ₀ * D.z₀} : Set G) := by
        have := map_mono (f := M.ι) hT
        rwa [hmapC, map_mul M.ι c.tau c.z, hτ, hz] at this
      have hcardT : Nat.card ((T : Subgroup (MulAut K₀)).map M.ι) = 2 ^ 7 := by
        rw [card_map_ι, card_sylow_of_card T hmA hcardAut]
      have h := mem_commutator_of_sylow hm₁ hC D.T_le hTmap (by rw [D.card_T]; norm_num) hcardT
        (x := D.τ₀ * D.z₀) (fun x hx => by
          have h2 := mem_centralizer_singleton_iff.1 hx.2
          calc x * (D.τ₀ * D.z₀) * x⁻¹ = (D.τ₀ * D.z₀) * x * x⁻¹ := by rw [h2]
            _ = D.τ₀ * D.z₀ := by group) D.tz_comm
      rw [← map_commutator] at h
      have h3 : M.ι (c.tau * c.z) = D.τ₀ * D.z₀ := by rw [map_mul M.ι c.tau c.z, hτ, hz]
      rw [← h3, mem_map_ι] at h
      exact h
    z_tau := by
      obtain ⟨k₀, hk₀P, hk₀⟩ := D.z_τ
      obtain ⟨θ, hθ⟩ := hpre k₀ (D.PA hk₀P)
      refine ⟨θ, (hinn θ).2 (hθ ▸ hk₀P), M.ι_injective ?_⟩
      rw [map_mul M.ι (θ⁻¹ * c.z) θ, map_mul M.ι θ⁻¹ c.z, map_inv, hθ, hz, hτ]
      exact hk₀
    R0_sylow := by
      have hc64 : Nat.card c.R0 = 64 := by rw [← card_map_ι M, hR0, D.card_R0]
      refine ⟨hc64, ?_⟩
      obtain ⟨m₂, hm₂, hCz⟩ := D.card_Cz
      have hcardC : Nat.card ↥(centralizer ({c.z} : Set (MulAut K₀))) = 2 ^ 6 * m₂ := by
        rw [← card_map_ι M, hmapC, hz, hCz]
      have hle : c.R0 ≤ centralizer ({c.z} : Set (MulAut K₀)) := inf_le_right
      exact sylow_of_card _ hm₂ hcardC
        (by rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hc64]; norm_num)
    R0_decomp := by
      obtain ⟨D₁, D₂, hsup, hinf, hcomm, ⟨e₁⟩, ⟨e₂⟩, hc₁, hc₂⟩ := D.R0_decomp
      have hD₁A : D₁ ≤ D.M.A := (le_sup_left.trans hsup.le).trans hR0A
      have hD₂A : D₂ ≤ D.M.A := (le_sup_right.trans hsup.le).trans hR0A
      have hD₁A' : D₁ ≤ M.A := by rw [hA]; exact hD₁A
      have hD₂A' : D₂ ≤ M.A := by rw [hA]; exact hD₂A
      refine ⟨D₁.comap M.ι, D₂.comap M.ι, ?_, ?_, ?_, ⟨(comapEquiv M hD₁A').trans e₁⟩,
        ⟨(comapEquiv M hD₂A').trans e₂⟩, ?_, ?_⟩
      · apply map_ι_injective M
        rw [Subgroup.map_sup, hcomap _ hD₁A, hcomap _ hD₂A, hsup, hR0]
      · apply map_ι_injective M
        rw [map_inf_eq _ _ _ M.ι_injective, hcomap _ hD₁A, hcomap _ hD₂A, hinf, Subgroup.map_bot]
      · intro x hx
        rw [mem_centralizer_iff]
        intro h hh
        apply M.ι_injective
        rw [map_mul, map_mul]
        exact (mem_centralizer_iff.1 (hcomm (mem_comap.1 hx))) (M.ι h) (mem_comap.1 hh)
      · exact center_comap M hD₁A' (by rw [hz]; exact hc₁)
      · exact center_comap M hD₂A' (by rw [hτ]; exact hc₂)
    R0_center := by
      constructor
      · apply map_ι_injective M
        rw [map_center, hR0, D.R0_center.1, Subgroup.map_sup, MonoidHom.map_zpowers,
          MonoidHom.map_zpowers, hz, hτ]
      · apply map_ι_injective M
        rw [MonoidHom.map_closure, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
          hz, hτ, ← D.R0_center.2]
        congr 1
        ext y
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨M.ι x, by rw [← hR0]; exact mem_map_of_mem _ hx, map_mul _ _ _⟩
        · rintro ⟨x, hx, rfl⟩
          rw [← hR0] at hx
          obtain ⟨w, hw, rfl⟩ := hx
          exact ⟨w * w, ⟨w, hw, rfl⟩, map_mul _ _ _⟩
    R0_gen := by
      apply map_ι_injective M
      rw [MonoidHom.map_closure, hR0, ← D.R0_gen]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨E, hER, hE2, hE16, hxE⟩, rfl⟩
        refine ⟨E.map M.ι, ?_, ?_, by rw [card_map_ι, hE16], mem_map_of_mem _ hxE⟩
        · rw [← hR0]
          exact map_mono hER
        · rintro _ ⟨w, hw, rfl⟩
          rw [← map_mul, hE2 w hw, map_one]
      · rintro ⟨E, hER, hE2, hE16, hyE⟩
        have hEA : E ≤ D.M.A := hER.trans hR0A
        obtain ⟨θ, rfl⟩ := hpre y (hEA hyE)
        refine ⟨θ, ⟨E.comap M.ι, ?_, ?_, ?_, hyE⟩, rfl⟩
        · intro x hx
          have : M.ι x ∈ c.R0.map M.ι := by rw [hR0]; exact hER (mem_comap.1 hx)
          exact (mem_map_ι M).1 this
        · intro x hx
          apply M.ι_injective
          rw [map_mul, map_one]
          exact hE2 (M.ι x) (mem_comap.1 hx)
        · rw [← card_map_ι M, hcomap _ hEA, hE16]
    E0 := by
      obtain ⟨E₀, hEle, hE2, hE16, hEu, hzE, hτE, hEc, horb, hdisj, hnorm, hcomma, e, he, heN,
        he2, heC⟩ := D.E0
      have hEA : E₀ ≤ D.M.A := hEle.trans (inf_le_left.trans D.R_le)
      have hEKmap : (E₀.comap M.ι).map M.ι = E₀ := hcomap _ hEA
      have hN : (normalizer ((E₀.comap M.ι : Subgroup (MulAut K₀)) : Set (MulAut K₀))).map M.ι =
          D.M.A ⊓ normalizer (E₀ : Set G) := by
        rw [map_normalizer, hEKmap, hA]
      have horbz : M.ι '' Cat8.conjOrbit (normalizer ((E₀.comap M.ι : Subgroup (MulAut K₀)) :
          Set (MulAut K₀))) c.z = Cat8.conjOrbit (D.M.A ⊓ normalizer (E₀ : Set G)) D.z₀ := by
        rw [image_conjOrbit, hN, hz]
      have horbzτ : M.ι '' Cat8.conjOrbit (normalizer ((E₀.comap M.ι : Subgroup (MulAut K₀)) :
          Set (MulAut K₀))) (c.z * c.tau) =
          Cat8.conjOrbit (D.M.A ⊓ normalizer (E₀ : Set G)) (D.z₀ * D.τ₀) := by
        rw [image_conjOrbit, hN, hzτ]
      obtain ⟨θe, hθe⟩ := hpre e ((inf_le_left.trans D.R_le) he)
      refine ⟨E₀.comap M.ι, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        have h1 := hEle (mem_comap.1 hx)
        refine ⟨(mem_map_ι M).1 (by rw [hR]; exact h1.1), (hinn x).2 h1.2⟩
      · intro x hx
        apply M.ι_injective
        rw [map_mul, map_one]
        exact hE2 (M.ι x) (mem_comap.1 hx)
      · rw [← card_map_ι M, hEKmap, hE16]
      · intro E' hE'le hE'2 hE'16
        apply map_ι_injective M
        rw [hEKmap]
        refine hEu _ ?_ ?_ (by rw [card_map_ι, hE'16])
        · rintro _ ⟨x, hx, rfl⟩
          have h1 := hE'le hx
          exact ⟨by rw [← hR]; exact mem_map_of_mem _ h1.1, (hinn x).1 h1.2⟩
        · rintro _ ⟨x, hx, rfl⟩
          rw [← map_mul, hE'2 x hx, map_one]
      · show M.ι c.z ∈ E₀
        rw [hz]
        exact hzE
      · show M.ι c.tau ∈ E₀
        rw [hτ]
        exact hτE
      · apply map_ι_injective M
        rw [map_centralizer_set', hEKmap, hA, hEc]
      · intro w hw
        rcases horb (M.ι w) (mem_comap.1 hw) with h | h | h
        · exact Or.inl (M.ι_injective (h.trans (map_one _).symm))
        · rw [← horbz] at h
          obtain ⟨w', hw', hww⟩ := h
          rw [M.ι_injective hww] at hw'
          exact Or.inr (Or.inl hw')
        · rw [← horbzτ] at h
          obtain ⟨w', hw', hww⟩ := h
          rw [M.ι_injective hww] at hw'
          exact Or.inr (Or.inr hw')
      · rcases hdisj with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
        · refine Or.inl ⟨by rw [← card_map_ι M, hN, h1], ?_, ?_, ?_⟩
          · rw [← Nat.card_image_of_injective M.ι_injective, horbz, h2]
          · rw [← Nat.card_image_of_injective M.ι_injective, horbzτ, h3]
          · apply map_ι_injective M
            rw [MonoidHom.map_closure, horbzτ, h4, hEKmap]
        · refine Or.inr ⟨by rw [← card_map_ι M, hN, h1], ?_, ?_, ?_⟩
          · rw [← Nat.card_image_of_injective M.ι_injective, horbz, h2]
          · rw [← Nat.card_image_of_injective M.ι_injective, horbzτ, h3]
          · apply map_ι_injective M
            rw [MonoidHom.map_closure, hEKmap]
            convert h4 using 2
            ext y
            constructor
            · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
              refine ⟨M.ι u, ?_, M.ι v, ?_, map_mul _ _ _⟩
              · rw [← horbz]; exact Set.mem_image_of_mem _ hu
              · rw [← horbz]; exact Set.mem_image_of_mem _ hv
            · rintro ⟨u, hu, v, hv, rfl⟩
              rw [← horbz] at hu hv
              obtain ⟨u', hu', rfl⟩ := hu
              obtain ⟨v', hv', rfl⟩ := hv
              exact ⟨u' * v', ⟨u', hu', v', hv', rfl⟩, map_mul _ _ _⟩
      · intro A' hA'R hA'2 hA'16 hA'n
        have hA'map : A'.map M.ι ≤ D.R₀ := by rw [← hR]; exact map_mono hA'R
        rcases hnorm (A'.map M.ι) hA'map
            (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, hA'2 x hx, map_one])
            (by rw [card_map_ι, hA'16]) (by
              intro r hr x hx
              rw [← hR] at hr
              obtain ⟨ρ, hρ, rfl⟩ := hr
              obtain ⟨ξ, hξ, rfl⟩ := hx
              have h1 := hA'n.conj_mem ⟨ξ, hA'R hξ⟩ (mem_subgroupOf.2 hξ) ⟨ρ, hρ⟩
              rw [mem_subgroupOf] at h1
              rw [← map_inv, ← map_mul, ← map_mul]
              exact mem_map_of_mem _ h1) with h | ⟨w', hw', y', hy', hyw⟩
        · exact Or.inl (map_ι_injective M (h.trans hEKmap.symm))
        · obtain ⟨w, hw, rfl⟩ := hw'
          obtain ⟨y, rfl⟩ := hpre y' hy'
          refine Or.inr ⟨w, hw, y, M.ι_injective ?_⟩
          rw [map_mul, map_mul, map_inv, ha]
          exact hyw
      · rw [← card_map_ι M, map_commutator, hEKmap, MonoidHom.map_zpowers, ha, hcomma]
      · refine ⟨θe, ⟨(mem_map_ι M).1 (by rw [hR, hθe]; exact he.1),
          (hinn θe).2 (by rw [hθe]; exact he.2)⟩, ?_, ?_, ?_⟩
        · refine (mem_map_ι M).1 ?_
          rw [map_commutator, hN, hθe]
          exact heN
        · apply M.ι_injective
          rw [map_mul, hθe, he2, map_one]
        · intro hc
          apply heC
          have h1 := mem_map_of_mem M.ι hc
          rw [map_centralizer_set', hEKmap, hθe] at h1
          exact h1.2
    Z_R := by
      apply map_ι_injective M
      rw [map_center, hR, D.Z_R, MonoidHom.map_zpowers, map_mul M.ι c.tau c.z, hτ, hz]
    no_E32 := by
      intro A' hA'R hA'2 h32
      exact D.no_E32 (A'.map M.ι) (by rw [← hR]; exact map_mono hA'R)
        (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, hA'2 x hx, map_one]) (by rw [card_map_ι, h32])
    outer_classes := by
      intro y hy2 hyI
      rcases D.outer (M.ι y) (hιA y) (by rw [← map_mul, hy2, map_one])
          (fun h => hyI ((hinn y).2 h)) with ⟨k, hk, hky⟩ | ⟨k, hk, hky⟩
      · obtain ⟨κ, rfl⟩ := hpre k hk
        refine Or.inl ⟨κ, M.ι_injective ?_⟩
        simp only [map_mul, map_inv, ha]
        exact hky
      · obtain ⟨κ, rfl⟩ := hpre k hk
        refine Or.inr ⟨κ, M.ι_injective ?_⟩
        rw [map_mul M.ι (κ⁻¹ * (c.a * c.z * c.tau)) κ, map_mul M.ι κ⁻¹ (c.a * c.z * c.tau),
          map_inv, map_mul M.ι (c.a * c.z) c.tau, map_mul M.ι c.a c.z, ha, hz, hτ]
        exact hky
    inner_classes := by
      intro y hyI hy2 hy1
      rcases D.inner (M.ι y) ((hinn y).1 hyI) (by rw [← map_mul, hy2, map_one])
          (fun h => hy1 (M.ι_injective (h.trans (map_one _).symm))) with
        ⟨k, hk, hky⟩ | ⟨k, hk, hky⟩
      · obtain ⟨κ, rfl⟩ := hpre k (D.PA hk)
        refine Or.inl ⟨κ, (hinn κ).2 hk, M.ι_injective ?_⟩
        simp only [map_mul, map_inv, hz]
        exact hky
      · obtain ⟨κ, rfl⟩ := hpre k (D.PA hk)
        refine Or.inr ⟨κ, (hinn κ).2 hk, M.ι_injective ?_⟩
        rw [map_mul M.ι (κ⁻¹ * (c.z * c.tau)) κ, map_mul M.ι κ⁻¹ (c.z * c.tau), map_inv,
          map_mul M.ι c.z c.tau, hz, hτ]
        exact hky }

theorem props_of_confData (D : Q3ConfData K₀ G) (c : Cat8.Q3Conf K₀) : c.Props := by
  obtain ⟨M₁, hP₁, hA₁, hΦ₁⟩ := exists_model_s₀ D.toQ3ModelData c.a c.adm
  have hQ₀ : D.Q₀ ≤ M₁.A ⊓ centralizer ({(M₁.Φ c.a : G)} : Set G) := by
    rw [hΦ₁, hA₁]
    exact D.Q₀le
  have hcard : Nat.card ↥(M₁.A ⊓ centralizer ({(M₁.Φ c.a : G)} : Set G)) = 2 ^ 5 * 45 := by
    rw [hΦ₁, hA₁]
    exact D.cardCA
  obtain ⟨k, hk, hkQ⟩ := exists_conj_mem_iff M₁ c.a D.Q₀ hQ₀ hcard D.cardQ₀ c.Q c.Q_le c.Q_sylow
  have hks : k * D.s₀ = D.s₀ * k := by
    have h1 := mem_centralizer_singleton_iff.1 hk.2
    rwa [hΦ₁] at h1
  obtain ⟨M, hMP, hMA, hι⟩ : ∃ M : AutModel K₀ G, M.P = D.M.P ∧ M.A = D.M.A ∧
      ∀ θ, M.ι θ = k⁻¹ * M₁.ι θ * k :=
    ⟨conjModel M₁ k⁻¹ (M₁.A.inv_mem hk.1), by rw [conjModel_P, hP₁], by rw [conjModel_A, hA₁],
      fun θ => by
        show ((conjModel M₁ k⁻¹ (M₁.A.inv_mem hk.1)).Φ θ : G) = _
        rw [conjModel_Φ, inv_inv]
        rfl⟩
  refine props_of_model D M hMP hMA c ?_ ?_
  · rw [hι, ι_apply, hΦ₁]
    calc k⁻¹ * D.s₀ * k = k⁻¹ * (D.s₀ * k) := by group
      _ = k⁻¹ * (k * D.s₀) := by rw [hks]
      _ = D.s₀ := by group
  · ext y
    constructor
    · rintro ⟨η, hη, rfl⟩
      rw [hι]
      exact (hkQ η).1 hη
    · intro hy
      obtain ⟨θ, rfl⟩ := exists_ι_eq M (by rw [hMA]; exact D.Q₀_le_A hy)
      refine ⟨θ, (hkQ θ).2 ?_, rfl⟩
      rw [← hι]
      exact hy

end CFSG.ComponentClassification.CatFactsSmall
