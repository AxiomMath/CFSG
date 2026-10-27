module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin5
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fin3

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem InH.of_conc {x : G} {T V H : Subgroup G} {f : G} (hc : Lemma13_1Conc x V H f)
    (hp : Para13 x T V H) : InH x V H f :=
  ⟨hp.E_le, hc.sylow.1, hc.sylow.2.1, hc.f3, hc.f_mem, hc.a_norm, hc.f_not, hc.a_cent⟩

theorem normalizer_Hzero {H : Subgroup G} {f : G} (hf : f ∈ normalizer (H : Set G)) :
    f ∈ normalizer ((Hzero H f : Subgroup G) : Set G) := by
  have := mem_normalizer_commutator hf
  unfold Hzero
  rw [commutator_comm]
  exact this

theorem comm_mod_normal {S H₀ : Subgroup G} (hnorm : ∀ s ∈ S, ∀ q ∈ H₀, s * q * s⁻¹ ∈ H₀)
    (hsq : ∀ s ∈ S, s * s ∈ H₀) {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    s * t * s⁻¹ * t⁻¹ ∈ H₀ := by
  have h1 : (s * t) * (s * t) ∈ H₀ := hsq _ (S.mul_mem hs ht)
  have h2 : t⁻¹ * (s * s)⁻¹ * t ∈ H₀ := by
    have := hnorm t⁻¹ (S.inv_mem ht) (s * s)⁻¹ (H₀.inv_mem (hsq s hs))
    have e0 : t⁻¹ * (s * s)⁻¹ * t⁻¹⁻¹ = t⁻¹ * (s * s)⁻¹ * t := by rw [inv_inv]
    rw [e0] at this
    exact this
  have h3 : (t * t)⁻¹ ∈ H₀ := H₀.inv_mem (hsq t ht)
  have e : s * t * s⁻¹ * t⁻¹ = ((s * t) * (s * t)) * (t⁻¹ * (s * s)⁻¹ * t) * (t * t)⁻¹ := by group
  rw [e]
  exact H₀.mul_mem (H₀.mul_mem h1 h2) h3

theorem exists_moved_of {V : Subgroup G} {f : G} (hfC : f ∉ centralizer (V : Set G)) :
    ∃ v ∈ V, f * v * f⁻¹ ≠ v := by
  by_contra hcon
  push Not at hcon
  apply hfC
  rw [mem_centralizer_iff]
  intro v hv
  have := hcon v hv
  calc v * f = (f * v * f⁻¹) * f := by rw [this]
    _ = f * v := by group

theorem prop12_1_nonE8_of (h131 : Lemma13_1Full) (h132 : Lemma13_2) (h133 : Lemma13_3) :
    Prop12_1_nonE8 := by
  intro G _ _ x T V hout
  obtain ⟨H, f, hc, hp⟩ := h131 G x T V hout
  have hI : InH x V H f := InH.of_conc hc hp
  have hne := h132 G x T V H f hout hc hp
  obtain ⟨hSyl, hnorm, hH0S, hidx, hsq, -, -, g, hgS, hZ, hnot⟩ :=
    h133 G x T V H f hout hc hp hne
  obtain ⟨hy₀H, hy₀sq, hcard, a, b, haH₀, hbH₀, ha4, hb4, hab, hgen, hya, hyb⟩ := hZ
  generalize hy₀ : g * x * g⁻¹ = y₀ at hgS hy₀H hy₀sq hya hyb hnot
  have z4 : Z4Data (Hzero H f) a b := ⟨ha4, hb4, hab, hgen, hcard⟩
  have hS2 : IsPGroup 2 ↥(H ⊔ T) := hSyl.2.1
  have hS64 : Nat.card ↥(H ⊔ T) = 64 := by
    have h := relIndex_mul_card (Hzero H f) (H ⊔ T)
    rw [inf_of_le_left hH0S, hidx, hcard] at h
    omega
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hI.x_mem
  have hTS : T ≤ H ⊔ T := le_sup_right
  have hH0H : Hzero H f ≤ H := le_trans le_sup_left hc.b_eq.symm.le
  have hVH : V ≤ Hzero H f := InH.V_le_Hzero hout hI
  have hV4 : Nat.card V = 4 := hout.V_four.2
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => (hout.V_four.1 v hv).1
  obtain ⟨ha2V, hb2V, hzV⟩ := z4.V_mem hVH hV4 hVsq
  have hVsub : ∀ v ∈ V, v = 1 ∨ v = a ^ 2 ∨ v = b ^ 2 ∨ v = a ^ 2 * b ^ 2 :=
    fun v hv => z4.sq_one (hVH hv) (hVsq v hv)
  have hxN : ∀ q ∈ Hzero H f, x * q * x⁻¹ ∈ Hzero H f := fun q hq => hnorm x hxS q hq
  have hx0 : x ∉ Hzero H f := hc.b_not
  have hCx : ∀ h ∈ Hzero H f, x * h = h * x → h ∈ V := by
    intro h hh hxh
    have hhC : h ∈ H ⊓ centralizer ({x} : Set G) := by
      refine ⟨hH0H hh, ?_⟩
      show h ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hxh
    rw [InH.C_H_x hout hI] at hhC
    obtain ⟨v, hv, h1 | h1⟩ := (hout.mem_EV).1 hhC
    · rw [h1]; exact hv
    · exfalso
      apply hx0
      have : x = v⁻¹ * h := by rw [h1]; group
      rw [this]
      exact (Hzero H f).mul_mem ((Hzero H f).inv_mem (hVH hv)) hh
  have hfN : ∀ q ∈ Hzero H f, f * q * f⁻¹ ∈ Hzero H f := fun q hq =>
    (mem_normalizer_iff.1 (normalizer_Hzero hc.a_norm) q).1 hq
  have hfV : ∀ v ∈ V, f * v * f⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.1 hc.f_mem v).1 hv
  have hfmoved := exists_moved_of hc.f_not
  have hffix : ∀ v ∈ V, f * v * f⁻¹ = v → v = 1 := by
    obtain ⟨k, hk⟩ := hc.f3
    exact fix_free_four V f k hk hfV hV4 hfmoved
  have hxy := comm_mod_normal hnorm hsq hxS hgS
  have hctx : XCtx (Hzero H f) V a b x y₀ f :=
    { z4 := z4, xN := hxN, xx := hout.x_sq, xV := fun v hv => hout.x_comm hv, Cx := hCx,
      VH := hVH, Vsq := hVsq, yN := fun q hq => hnorm y₀ hgS q hq, ya := hya, yb := hyb,
      xy := hxy, fN := hfN, fx := hI.f_comm_x, fV := hfV, ffix := hffix, a2V := ha2V,
      b2V := hb2V, zV := hzV, Vsub := hVsub }
  have hinv := hctx.x_inverts
  have hTeq : (H ⊔ T) ⊓ centralizer ({x} : Set G) = T := T_eq_inf hout hS2 hTS
  have hy₀notH : y₀ ∉ H := by
    intro hyH
    rw [hc.b_eq] at hyH
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_invol hout.x_sq hxN).1 hyH
    · exact hy₀H (h1 ▸ hq)
    · apply hnot
      have : x = q⁻¹ * y₀ := by rw [h1]; group
      rw [this]
      exact (Hzero H f ⊔ zpowers y₀).mul_mem (Subgroup.mem_sup_left ((Hzero H f).inv_mem hq))
        (Subgroup.mem_sup_right (mem_zpowers y₀))
  have hnleT : ¬ T ≤ H := fun hTH => hy₀notH ((sup_le le_rfl hTH : H ⊔ T ≤ H) hgS)
  have hT16 : Nat.card T = 16 := card_T_eq_16 hout hp.T_inter hnleT
  have hCS : Nat.card ↥((H ⊔ T) ⊓ centralizer ({x} : Set G)) = 16 := by
    rw [hTeq]; exact hT16
  obtain ⟨k, hk, hkc⟩ := exists_y1 z4 hS64 hH0S hxS hinv hV4 hVsub hCS hgS hy₀sq hya hyb
  have hkS : k ∈ H ⊔ T := hH0S hk
  have hyy : (k * y₀ * k⁻¹) * (k * y₀ * k⁻¹) = 1 := by
    calc k * y₀ * k⁻¹ * (k * y₀ * k⁻¹) = k * (y₀ * y₀) * k⁻¹ := by group
      _ = 1 := by rw [hy₀sq]; group
  have hka : k⁻¹ * a * k = a := by
    calc k⁻¹ * a * k = (a * k⁻¹) * k := by rw [z4.comm ((Hzero H f).inv_mem hk) haH₀]
      _ = a := by group
  have hkb : k⁻¹ * b * k = b := by
    calc k⁻¹ * b * k = (b * k⁻¹) * k := by rw [z4.comm ((Hzero H f).inv_mem hk) hbH₀]
      _ = b := by group
  have hya1 : (k * y₀ * k⁻¹) * a * (k * y₀ * k⁻¹)⁻¹ = b := by
    calc (k * y₀ * k⁻¹) * a * (k * y₀ * k⁻¹)⁻¹ = k * y₀ * (k⁻¹ * a * k) * y₀⁻¹ * k⁻¹ := by group
      _ = k * (y₀ * a * y₀⁻¹) * k⁻¹ := by rw [hka]; group
      _ = k * b * k⁻¹ := by rw [hya]
      _ = b := by rw [z4.comm hk hbH₀]; group
  have hyb1 : (k * y₀ * k⁻¹) * b * (k * y₀ * k⁻¹)⁻¹ = a := by
    calc (k * y₀ * k⁻¹) * b * (k * y₀ * k⁻¹)⁻¹ = k * y₀ * (k⁻¹ * b * k) * y₀⁻¹ * k⁻¹ := by group
      _ = k * (y₀ * b * y₀⁻¹) * k⁻¹ := by rw [hkb]; group
      _ = k * a * k⁻¹ := by rw [hyb]
      _ = a := by rw [z4.comm hk haH₀]; group
  have hy₁S : k * y₀ * k⁻¹ ∈ H ⊔ T :=
    (H ⊔ T).mul_mem ((H ⊔ T).mul_mem hkS hgS) ((H ⊔ T).inv_mem hkS)
  have hy₁H : k * y₀ * k⁻¹ ∉ Hzero H f := by
    intro h
    apply hy₀H
    have : y₀ = k⁻¹ * (k * y₀ * k⁻¹) * k := by group
    rw [this]
    exact (Hzero H f).mul_mem ((Hzero H f).mul_mem ((Hzero H f).inv_mem hk) h) hk
  have hxy1 : x ∉ Hzero H f ⊔ zpowers (k * y₀ * k⁻¹) := by
    have hmem : k * y₀ * k⁻¹ ∈ Hzero H f ⊔ zpowers y₀ := by
      have : k * y₀ * k⁻¹ = (k * (y₀ * k⁻¹ * y₀⁻¹)) * y₀ := by group
      rw [this]
      exact (Hzero H f ⊔ zpowers y₀).mul_mem
        ((Hzero H f ⊔ zpowers y₀).mul_mem (Subgroup.mem_sup_left hk)
          (Subgroup.mem_sup_left (hnorm y₀ hgS k⁻¹ ((Hzero H f).inv_mem hk))))
        (Subgroup.mem_sup_right (mem_zpowers y₀))
    have hle : Hzero H f ⊔ zpowers (k * y₀ * k⁻¹) ≤ Hzero H f ⊔ zpowers y₀ :=
      sup_le le_sup_left ((zpowers_le).2 hmem)
    exact fun hx => hnot (hle hx)
  have hdata : M12Data (H ⊔ T) a b (k * y₀ * k⁻¹) x :=
    m12data_of_y1 z4 hS64 hH0S hxS hy₁S hout.x_sq hyy hkc hya1 hyb1 hinv hx0 hy₁H hxy1
  refine ⟨H ⊔ T, a, b, k * y₀ * k⁻¹, hout, hSyl, hTeq.symm, ?_, hdata, ?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne hTS ?_
    intro h
    apply hout.T_not_sylow
    rw [h]
    exact hSyl
  · refine ⟨k * g, ?_⟩
    rw [← hy₀]
    group
  · intro g'
    rw [hgen]
    exact not_fused hout hT16 z4 g'
  · apply le_antisymm
    · intro v hv
      rcases hVsub v hv with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.subset_closure (by simp [pow_two])
      · exact Subgroup.subset_closure (by simp [pow_two])
      · have e : a ^ 2 * b ^ 2 = (a * a) * (b * b) := by simp only [pow_two]
        rw [e]
        exact (Subgroup.closure ({a * a, b * b} : Set G)).mul_mem
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · have := ha2V
        rwa [pow_two] at this
      · have := hb2V
        rwa [pow_two] at this
  · refine ⟨f, hc.f3, ?_, hI.f_comm_x, hfmoved⟩
    rw [hgen]
    exact normalizer_Hzero hc.a_norm

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
