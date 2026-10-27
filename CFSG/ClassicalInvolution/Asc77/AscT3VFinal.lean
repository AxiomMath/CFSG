module

public import CFSG.ClassicalInvolution.Asc77.AscT3VHexX
public import CFSG.ClassicalInvolution.Asc77.AscT3VInn
public import CFSG.ClassicalInvolution.Asc77.AscT3R10bMain
public import CFSG.ClassicalInvolution.Asc77.AscT3SOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.v_inZ_mem_X (d : Std20 p f K K' J S R R' W V z t) {ζ : G} (hζ : InZ z t ζ) :
    ζ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  have hKX : K ≤ sec20X (CoreAssembly.conjClass K) z K K' := le_sup_right.trans le_sup_left
  have hK'X : K' ≤ sec20X (CoreAssembly.conjClass K) z K K' := le_sup_right
  have hzX : z ∈ sec20X (CoreAssembly.conjClass K) z K K' := hKX d.viol.hzK.mem
  have htX : t ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
    have : K ⊔ K' ≤ sec20X (CoreAssembly.conjClass K) z K K' := sup_le hKX hK'X
    exact this d.htKK
  rcases hζ with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hzX
  · exact htX
  · exact Subgroup.mul_mem _ hzX htX

theorem Std20.v_contra (d : Std20 p f K K' J S R R' W V z t) (h8 : Nat.card R = 8)
    {s₁ ρ h : G} (hh : h * z * h⁻¹ = s₁) (hs₁z : s₁ * z = z * s₁) (hs₁t : s₁ * t = t * s₁)
    (hρs : ρ * s₁ = s₁ * ρ) (hρodd : Odd (orderOf ρ)) (hρz : ρ * z * ρ⁻¹ = z * t)
    (hρt : ρ * t * ρ⁻¹ = z) : s₁ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  obtain ⟨hM₀Ω, hM₀'Ω, hM₀ne, hM₀i, hM₀'i⟩ := d.late_member_data h
  rw [hh] at hM₀i hM₀'i
  set M₀ : Subgroup G := conjSub h K with hM₀
  set M₀' : Subgroup G := conjSub h K' with hM₀'
  have hdich : ∀ c : G, c * s₁ = s₁ * c → conjSub c M₀ = M₀ ∨ conjSub c M₀ = M₀' := by
    intro c hc
    have hcs : c * s₁ * c⁻¹ = s₁ := by
      calc c * s₁ * c⁻¹ = (s₁ * c) * c⁻¹ := by rw [hc]
        _ = s₁ := by group
    have hi : IsUniqueInvolution (conjSub c M₀) s₁ := by
      have := hM₀i.conj c
      rwa [hcs] at this
    exact d.late_members_of_inv hh (d.hyp.conjInvariant c M₀ hM₀Ω) hi
  have hdich' : ∀ c : G, c * s₁ = s₁ * c → conjSub c M₀' = M₀ ∨ conjSub c M₀' = M₀' := by
    intro c hc
    have hcs : c * s₁ * c⁻¹ = s₁ := by
      calc c * s₁ * c⁻¹ = (s₁ * c) * c⁻¹ := by rw [hc]
        _ = s₁ := by group
    have hi : IsUniqueInvolution (conjSub c M₀') s₁ := by
      have := hM₀'i.conj c
      rwa [hcs] at this
    exact d.late_members_of_inv hh (d.hyp.conjInvariant c M₀' hM₀'Ω) hi
  have hoddfix : ∀ c : G, c * s₁ = s₁ * c → Odd (orderOf c) →
      conjSub c M₀ = M₀ ∧ conjSub c M₀' = M₀' := by
    intro c hc hcodd
    have hcM : conjSub c M₀ = M₀ := by
      rcases hdich c hc with h1 | h1
      · exact h1
      · exfalso
        have h2 : conjSub c M₀' = M₀ := by
          rcases hdich' c hc with h3 | h3
          · exact h3
          · exact absurd (conjSub_injective c (h3.trans h1.symm)) hM₀ne.symm
        have hcc : c * c ∈ Subgroup.normalizer (M₀ : Set G) := by
          rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, h1, h2]
        obtain ⟨m, hm⟩ := hcodd
        have hcpow : c = (c * c) ^ (m + 1) := by
          have h4 : c ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
          calc c = c ^ (2 * m + 1) * c := by rw [h4, one_mul]
            _ = (c * c) ^ (m + 1) := by
              rw [← pow_two, ← pow_mul, ← pow_succ]
              congr 1
        have hcN : c ∈ Subgroup.normalizer (M₀ : Set G) := by
          rw [hcpow]
          exact Subgroup.pow_mem _ hcc _
        have := mem_normalizer_iff_conjSub_eq.mp hcN
        rw [this] at h1
        exact hM₀ne h1
    refine ⟨hcM, ?_⟩
    rcases hdich' c hc with h1 | h1
    · exact absurd (conjSub_injective c (h1.trans hcM.symm)) hM₀ne.symm
    · exact h1
  obtain ⟨hρM, hρM'⟩ := hoddfix ρ hρs hρodd
  have hρinv : conjSub ρ⁻¹ M₀ = M₀ := by
    have := congrArg (conjSub ρ⁻¹) hρM
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hzc : z * s₁ = s₁ * z := hs₁z.symm
  have htc : t * s₁ = s₁ * t := hs₁t.symm
  have hztc : (z * t) * s₁ = s₁ * (z * t) := by
    calc (z * t) * s₁ = z * (t * s₁) := by rw [mul_assoc]
      _ = z * (s₁ * t) := by rw [htc]
      _ = (z * s₁) * t := by rw [mul_assoc]
      _ = (s₁ * z) * t := by rw [hzc]
      _ = s₁ * (z * t) := by rw [mul_assoc]
  have e3 : (z * t) * z = t := by rw [mul_assoc, ← hzt, ← mul_assoc, hz2, one_mul]
  have hzN : conjSub z M₀ = M₀ := by
    by_contra hne
    have hz' : conjSub z M₀ = M₀' := (hdich z hzc).resolve_left hne
    have h1 : conjSub (z * t) M₀ = M₀' := by
      have e : z * t = ρ * z * ρ⁻¹ := hρz.symm
      rw [e, conjSub_mul, conjSub_mul, hρinv, hz', hρM']
    have e2 : t = ρ * (z * t) * ρ⁻¹ := by
      calc t = (z * t) * z := e3.symm
        _ = (ρ * z * ρ⁻¹) * (ρ * t * ρ⁻¹) := by rw [hρz, hρt]
        _ = ρ * (z * t) * ρ⁻¹ := by group
    have h2 : conjSub t M₀ = M₀' := by
      rw [e2, conjSub_mul, conjSub_mul, hρinv, h1, hρM']
    have h3 : conjSub (z * t) M₀ = M₀ := by
      rw [conjSub_mul, h2, ← hz', ← conjSub_mul]
      have : z * z = 1 := hz2
      rw [this, conjSub_one]
    exact hM₀ne (h3.symm.trans h1)
  have hztN : conjSub (z * t) M₀ = M₀ := by
    have e : z * t = ρ * z * ρ⁻¹ := hρz.symm
    rw [e, conjSub_mul, conjSub_mul, hρinv, hzN, hρM]
  have hconjN : ∀ c : G, conjSub c M₀ = M₀ → h⁻¹ * c * h ∈ Subgroup.normalizer (K : Set G) := by
    intro c hc
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul]
    change conjSub h⁻¹ (conjSub c M₀) = K
    rw [hc]
    exact conjSub_inv_conjSub h K
  have hρ'N := hconjN ρ hρM
  have hζ'N := hconjN (z * t) hztN
  have hz'N := hconjN z hzN
  have hzt2 : (z * t) * (z * t) = 1 := by
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, one_mul]
  have e4 : ρ * (z * t) * ρ⁻¹ * (z * t)⁻¹ = z := by
    have e5 : ρ * (z * t) * ρ⁻¹ = t := by
      calc ρ * (z * t) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * t * ρ⁻¹) := by group
        _ = (z * t) * z := by rw [hρz, hρt]
        _ = t := e3
    rw [e5, inv_eq_of_mul_eq_one_right hzt2]
    calc t * (z * t) = (t * z) * t := by rw [mul_assoc]
      _ = (z * t) * t := by rw [← hzt]
      _ = z := by rw [mul_assoc, ht2, mul_one]
  have hcomm : ⁅h⁻¹ * ρ * h, h⁻¹ * (z * t) * h⁆ = h⁻¹ * z * h := by
    calc ⁅h⁻¹ * ρ * h, h⁻¹ * (z * t) * h⁆ = h⁻¹ * (ρ * (z * t) * ρ⁻¹ * (z * t)⁻¹) * h := by
          simp only [commutatorElement_def]
          group
      _ = h⁻¹ * z * h := by rw [e4]
  have hz'2 : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨eK⟩ := d.hyp.nonempty_equiv_sl2 d.late_mem_K
  have hout := T3S.outCommMod_of_chart hp hq eK
  obtain ⟨k, hkK, hk⟩ := hout _ hρ'N _ hζ'N
  rw [hcomm] at hk
  obtain ⟨φ, hφs, hφk⟩ := d.hyp.exists_chart d.late_mem_K
  obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
  obtain ⟨u, huK, hu4, hu⟩ := T3V.exists_order_four_fixed (odd_natCard_galoisField hp hq)
    d.viol.hzK hφs hφk heKW.1 he2 hz'N hz'2 hkK hk
  set u₀ : G := h * u * h⁻¹ with hu₀
  have hu₀M : u₀ ∈ M₀ := conj_mem_conjSub huK
  have hu₀4 : orderOf u₀ = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj h) u
    simpa [MulAut.conj_apply, hu₀, hu4] using this
  have hcardu : Nat.card ↥(Subgroup.zpowers u₀) = 4 := by rw [Nat.card_zpowers, hu₀4]
  have hPG : IsPGroup 2 ↥(Subgroup.zpowers u₀) :=
    IsPGroup.of_card (n := 2) (by rw [hcardu]; norm_num)
  have hle : Subgroup.zpowers u₀ ≤ M₀ := Subgroup.zpowers_le.mpr hu₀M
  obtain ⟨R₂, hR₂, hUR₂⟩ := IsSylow2In.exists_ge hPG hle
  have hR₂card : Nat.card R₂ = 8 := by
    have := Sec6Gen.natCard_isSylow2In_eq d.late_hΩ d.late_mem_K hM₀Ω d.hR hR₂
    rw [← this]
    exact h8
  have hUset : Subgroup.zpowers u₀ ∈ USet (CoreAssembly.conjClass K) :=
    mem_USet_of_natCard hM₀Ω hR₂ hUR₂ inferInstance (by rw [hR₂card, hcardu])
  have hz'c : (h⁻¹ * z * h) * u = u * (h⁻¹ * z * h) := by
    have := hu
    calc (h⁻¹ * z * h) * u = (h⁻¹ * z * h) * u * (h⁻¹ * z * h)⁻¹ * (h⁻¹ * z * h) := by group
      _ = u * (h⁻¹ * z * h) := by rw [this]
  have hu₀z : z * u₀ = u₀ * z := by
    have e1 : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
    calc z * u₀ = h * ((h⁻¹ * z * h) * u) * h⁻¹ := by rw [hu₀]; group
      _ = h * (u * (h⁻¹ * z * h)) * h⁻¹ := by rw [hz'c]
      _ = u₀ * z := by rw [hu₀]; group
  have hUC : Subgroup.zpowers u₀ ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hu₀z.symm)
  have hUX : Subgroup.zpowers u₀ ≤ sec20X (CoreAssembly.conjClass K) z K K' :=
    (le_iSup₂ (f := fun (U : Subgroup G) (_ : U ∈ {U : Subgroup G | U ∈ USet
      (CoreAssembly.conjClass K) ∧ U ≤ Subgroup.centralizer ({z} : Set G)}) => U)
      (Subgroup.zpowers u₀) ⟨hUset, hUC⟩).trans (le_sup_left.trans le_sup_left)
  have huu : u * u = z := by
    have hsq : (u * u) * (u * u) = 1 := by
      have : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
      calc (u * u) * (u * u) = u ^ 4 := by rw [← pow_two, ← pow_two, ← pow_mul]
        _ = 1 := this
    rcases d.viol.hzK.unique (u * u) (K.mul_mem huK huK) hsq with h1 | h1
    · exfalso
      have : u ^ 2 = 1 := by rw [pow_two]; exact h1
      have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one this
      rw [hu4] at h2
      omega
    · exact h1
  have hs₁u : s₁ = u₀ * u₀ := by
    rw [← hh]
    calc h * z * h⁻¹ = h * (u * u) * h⁻¹ := by rw [huu]
      _ = u₀ * u₀ := by rw [hu₀]; group
  rw [hs₁u]
  exact hUX (Subgroup.mul_mem _ (Subgroup.mem_zpowers u₀) (Subgroup.mem_zpowers u₀))

theorem Std20.v_inZ_mem_W (d : Std20 p f K K' J S R R' W V z t) {ζ : G} (hζ : InZ z t ζ) :
    ζ ∈ W := by
  rcases hζ with rfl | rfl | rfl | rfl
  · exact W.one_mem
  · exact d.late_z_mem_W
  · exact d.late_t_mem_W
  · exact W.mul_mem d.late_z_mem_W d.late_t_mem_W

end Std

variable (p f : ℕ) [Fact p.Prime]


theorem res10bP1_proved : Res10bP1 p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 h8 a haS g hg
  by_contra haX
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ha2 : a * a = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hTX := d.r10b_TX c8 h8
  have hsK : conjSub a K = K' := by
    rcases d.late_conj_K (d.hSz haS) with h | h
    · exact absurd (hTX a haS h) haX
    · exact h
  obtain ⟨s₁, ρ, ⟨w, hw, hws⟩, hs₁S, hs₁2, ⟨ζ, hζ, hs₁ζ⟩, hρs, hρodd, hρz, hρt⟩ :=
    d.v_swap_rho h8 haS hsK ha2
  have hs₁X : s₁ ∉ sec20X (CoreAssembly.conjClass K) z K K' := by
    intro h1
    apply haX
    have : a = s₁ * ζ⁻¹ := by rw [hs₁ζ]; group
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (d.v_inZ_mem_X hζ))
  have hh : (w * g) * z * (w * g)⁻¹ = s₁ := by
    rw [← hws, ← hg]
    group
  obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
  obtain ⟨-, hst⟩ := d.late_swap_sq_data haS hsK (by rw [ha2]; exact W.one_mem) heKW he2
  have haz : a * z = z * a := by
    have := d.late_S_act_z haS
    calc a * z = (a * z * a⁻¹) * a := by group
      _ = z * a := by rw [this]
  have hat : a * t = t * a := by
    calc a * t = (a * t * a⁻¹) * a := by group
      _ = t * a := by rw [hst]
  have hζW : ζ ∈ W := d.v_inZ_mem_W hζ
  have hs₁z : s₁ * z = z * s₁ := by
    rw [hs₁ζ]
    calc a * ζ * z = a * (ζ * z) := mul_assoc _ _ _
      _ = a * (z * ζ) := by rw [d.late_hWc ζ hζW z d.late_z_mem_W]
      _ = (a * z) * ζ := (mul_assoc _ _ _).symm
      _ = (z * a) * ζ := by rw [haz]
      _ = z * (a * ζ) := mul_assoc _ _ _
  have hs₁t : s₁ * t = t * s₁ := by
    rw [hs₁ζ]
    calc a * ζ * t = a * (ζ * t) := mul_assoc _ _ _
      _ = a * (t * ζ) := by rw [d.late_hWc ζ hζW t d.late_t_mem_W]
      _ = (a * t) * ζ := (mul_assoc _ _ _).symm
      _ = (t * a) * ζ := by rw [hat]
      _ = t * (a * ζ) := mul_assoc _ _ _
  exact hs₁X (d.v_contra h8 hh hs₁z hs₁t hρs hρodd hρz hρt)

end CFSG.ClassicalInvolution.Asc77.T3CII
