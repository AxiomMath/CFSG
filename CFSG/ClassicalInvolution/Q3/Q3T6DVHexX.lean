module

public import CFSG.ClassicalInvolution.Q3.Q3T6DVHexY
public import CFSG.ClassicalInvolution.Q3.Q3T6DVSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement Pointwise

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.v_hexg (d : Std20Three K K' J S R R' W V z t) :
    ∃ g : G, g ∈ pairNormalizers K J z t ∧ g ∈ Subgroup.normalizer (W : Set G) ∧
      g * z * g⁻¹ = z * t ∧ g * t * g⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  refine ⟨t₀ * r, Subgroup.mul_mem _ hh.t₀_mem_pair hh.r_mem_pair,
    Subgroup.mul_mem _ hh.t₀_normW hh.r_normW, ?_, ?_⟩
  · calc t₀ * r * z * (t₀ * r)⁻¹ = t₀ * (r * z * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * z * t₀⁻¹ := by rw [hh.hrz]
      _ = z * t := hh.htz
  · calc t₀ * r * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
      _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
      _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
      _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

theorem Std20Three.v_decomp (d : Std20Three K K' J S R R' W V z t) {c : G}
    (hc : c ∈ pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G)) :
    ∃ q ∈ oddCoreOf (pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G)),
      ∃ w ∈ W, c = q * w := by
  obtain ⟨X, -, hXY, hYX, hXeq, hf, -, φ, hφs, hφk⟩ := d.v_hexY
  set C₀ : Subgroup G := pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) with hC₀
  have hWX : W ≤ X := hXeq ▸ le_sup_right
  have hXN : X ≤ Subgroup.normalizer (oddCoreOf X : Set G) := fun a ha =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer ha)
  have hset2 := Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreOf X) W (hWX.trans hXN)
  obtain ⟨q', hq', w, hw, hqw⟩ : c ∈ (oddCoreOf X : Set G) * (W : Set G) := by
    rw [← hset2, ← hXeq]
    exact hf hc
  have hwC : w ∈ C₀ := ⟨hXY (hWX hw), Subgroup.mem_centralizer_iff.mpr fun a ha =>
    d.late_hWc a ha w hw⟩
  have hq'C : q' ∈ C₀ := by
    have : q' = c * w⁻¹ := by rw [← hqw]; group
    rw [this]
    exact C₀.mul_mem hc (C₀.inv_mem hwC)
  have hAC : oddCoreOf X ⊓ C₀ ≤ oddCoreOf C₀ := by
    refine Sec6Gen.le_oddCoreOf_of_normal inf_le_right ?_ ?_
    · intro a ha
      exact late_mem_normalizer_inf
        (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hf ha)))
        (Subgroup.le_normalizer ha)
    · exact (oddCoreOf_odd_natCard X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact ⟨q', hAC ⟨hq', hq'C⟩, w, hw, hqw.symm⟩

theorem Std20Three.v_exists_x (d : Std20Three K K' J S R R' W V z t) {s : G} (hs2 : s * s = 1)
    (hsY : s ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G)) (hsz : s * z * s⁻¹ = z)
    (hst : s * t * s⁻¹ = t) :
    ∃ (x : G) (e : ℕ), x ∈ Subgroup.normalizer (W : Set G) ∧ x * z * x⁻¹ = z * t ∧
      x * t * x⁻¹ = z ∧ (∃ ε ∈ W, x * s * x⁻¹ = s * ε) ∧ x ^ 3 ^ e = 1 := by
  obtain ⟨g, hgY, hgW, hgz, hgt⟩ := d.v_hexg
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hzt : z * t = t * z := d.late_zt_comm
  obtain ⟨k, e, hk, hge⟩ := T3V.exists_pow_three_part g (isOfFinOrder_of_finite g)
  set x₀ := g ^ k with hx₀
  have hx₀Y : x₀ ∈ pairNormalizers K J z t := Subgroup.pow_mem _ hgY k
  have hx₀W : x₀ ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ hgW k
  obtain ⟨hx₀z, hx₀t⟩ := T3V.pow_act_of_mod hz2 hzt hgz hgt hk
  have hx₀odd : Odd (orderOf x₀) := by
    have : orderOf x₀ ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hge
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat this
  have hy := d.v_Y_odd hsY hsW hsz hst hx₀Y hx₀W hx₀odd
  obtain ⟨q, hq, w, hw, hyqw⟩ := d.v_decomp hy
  set C₀ : Subgroup G := pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) with hC₀
  set Q : Subgroup G := oddCoreOf C₀ with hQ
  set N : Subgroup G := Subgroup.normalizer (W : Set G) with hN
  have hQC : Q ≤ C₀ := oddCoreOf_le_self C₀
  have hQN : Q ≤ N := hQC.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hWN : W ≤ N := Subgroup.le_normalizer
  have hNC : ∀ {a : G}, a ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G) →
      a ∈ N → a ∈ Subgroup.normalizer (C₀ : Set G) := fun ha haN =>
    late_mem_normalizer_inf ha (T3V.mem_normalizer_centralizer haN)
  have hx₀C : x₀ ∈ Subgroup.normalizer (Q : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (hNC (Subgroup.le_normalizer hx₀Y) hx₀W)
  have hsC : s ∈ Subgroup.normalizer (Q : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (hNC hsY hsW)
  have hWnorm : (W.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mpr le_rfl
  have hodd : Odd (Nat.card ↥(Q.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]
    exact oddCoreOf_odd_natCard C₀
  have hQW : ∀ a ∈ Q.subgroupOf N, a ∈ W.subgroupOf N → a = 1 := by
    intro a haQ haW
    have haQ' : (a : G) ∈ Q := haQ
    have haW' : (a : G) ∈ W := haW
    have hodd' : Odd (orderOf (a : G)) := odd_orderOf_of_mem_oddCoreOf C₀ haQ'
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨(a : G), d.hWS haW'⟩
    have hk' : (a : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf (a : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf (a : G)) (2 ^ k) := hodd'.coprime_two_right.pow_right k
    have h1 : orderOf (a : G) = 1 := hcop.eq_one_of_dvd hdvd
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  set x' : ↥N := ⟨x₀, hx₀W⟩ with hx'
  set s' : ↥N := ⟨s, hsW⟩ with hs'
  have hqx : ∀ a ∈ Q.subgroupOf N, x' * a * x'⁻¹ ∈ Q.subgroupOf N := by
    intro a ha
    exact (Subgroup.mem_normalizer_iff.mp hx₀C (a : G)).mp ha
  have hqs : ∀ a ∈ Q.subgroupOf N, s' * a * s'⁻¹ ∈ Q.subgroupOf N := by
    intro a ha
    exact (Subgroup.mem_normalizer_iff.mp hsC (a : G)).mp ha
  have hss : s' * s' = 1 := Subtype.ext hs2
  have hsx : ∃ q₂ ∈ Q.subgroupOf N, ∃ w₂ ∈ W.subgroupOf N, s' * x' * s'⁻¹ = x' * q₂ * w₂ := by
    refine ⟨⟨q, hQN hq⟩, hq, ⟨w, hWN hw⟩, hw, Subtype.ext ?_⟩
    show s * x₀ * s⁻¹ = x₀ * q * w
    have : x₀⁻¹ * (s * x₀ * s⁻¹) = q * w := hyqw
    calc s * x₀ * s⁻¹ = x₀ * (x₀⁻¹ * (s * x₀ * s⁻¹)) := by group
      _ = x₀ * (q * w) := by rw [this]
      _ = x₀ * q * w := by group
  obtain ⟨q₃, hq₃, w₃, hw₃, hfix⟩ := T3V.exists_mod_fixed (W.subgroupOf N) (Q.subgroupOf N)
    hodd hQW hqx hqs hss hsx
  have hfix' : s * ((q₃ : G) * x₀) * s⁻¹ = ((q₃ : G) * x₀) * (w₃ : G) :=
    congrArg Subtype.val hfix
  have hq₃Q : (q₃ : G) ∈ Q := hq₃
  have hq₃c : ∀ c ∈ W, c * (q₃ : G) = (q₃ : G) * c := fun c hc =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hQC hq₃Q)).2 c hc
  have hw₃W : (w₃ : G) ∈ W := hw₃
  have hztW : z * t ∈ W := W.mul_mem d.late_z_mem_W d.late_t_mem_W
  set x₁ : G := (q₃ : G) * x₀ with hx₁
  have hx₁W : x₁ ∈ N := N.mul_mem q₃.2 hx₀W
  have hx₁z : x₁ * z * x₁⁻¹ = z * t := by
    calc x₁ * z * x₁⁻¹ = (q₃ : G) * (x₀ * z * x₀⁻¹) * (q₃ : G)⁻¹ := by rw [hx₁]; group
      _ = (q₃ : G) * (z * t) * (q₃ : G)⁻¹ := by rw [hx₀z]
      _ = z * t := by rw [← hq₃c _ hztW]; group
  have hx₁t : x₁ * t * x₁⁻¹ = z := by
    calc x₁ * t * x₁⁻¹ = (q₃ : G) * (x₀ * t * x₀⁻¹) * (q₃ : G)⁻¹ := by rw [hx₁]; group
      _ = (q₃ : G) * z * (q₃ : G)⁻¹ := by rw [hx₀t]
      _ = z := by rw [← hq₃c _ d.late_z_mem_W]; group
  obtain ⟨k₂, e₂, hk₂, hge₂⟩ := T3V.exists_pow_three_part x₁ (isOfFinOrder_of_finite x₁)
  obtain ⟨hx₂z, hx₂t⟩ := T3V.pow_act_of_mod hz2 hzt hx₁z hx₁t hk₂
  obtain ⟨w', hw', hpow⟩ := T3V.pow_mul_mem hx₁W hw₃W k₂
  have hsx₂ : s * x₁ ^ k₂ * s⁻¹ = x₁ ^ k₂ * w' := by
    rw [← hpow, ← conj_pow, hfix']
  have hinv : s * (x₁ ^ k₂)⁻¹ * s⁻¹ = w'⁻¹ * (x₁ ^ k₂)⁻¹ := by
    have := congrArg (fun a => a⁻¹) hsx₂
    simpa [mul_assoc] using this
  have hx₂N : x₁ ^ k₂ ∈ N := Subgroup.pow_mem _ hx₁W k₂
  have hsi : s⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hsW
  refine ⟨x₁ ^ k₂, e₂, hx₂N, hx₂z, hx₂t, ⟨s⁻¹ * (x₁ ^ k₂ * w'⁻¹ * (x₁ ^ k₂)⁻¹) * s, ?_, ?_⟩,
    hge₂⟩
  · have h1 : x₁ ^ k₂ * w'⁻¹ * (x₁ ^ k₂)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hx₂N w'⁻¹).mp (W.inv_mem hw')
    have := (Subgroup.mem_normalizer_iff.mp hsi _).mp h1
    simpa [mul_assoc] using this
  · calc x₁ ^ k₂ * s * (x₁ ^ k₂)⁻¹ = x₁ ^ k₂ * (s * (x₁ ^ k₂)⁻¹ * s⁻¹) * s := by group
      _ = x₁ ^ k₂ * (w'⁻¹ * (x₁ ^ k₂)⁻¹) * s := by rw [hinv]
      _ = s * (s⁻¹ * (x₁ ^ k₂ * w'⁻¹ * (x₁ ^ k₂)⁻¹) * s) := by group

theorem Std20Three.v_swap_Y (d : Std20Three K K' J S R R' W V z t) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K') (hst : s * t * s⁻¹ = t) :
    s ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G) := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  set Z : Subgroup G := Subgroup.closure {z, t} with hZ
  set Y : Subgroup G := pairNormalizers K J z t with hY
  set NZ : Subgroup G := Subgroup.normalizer (Z : Set G) with hNZ
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hsz : s * z * s⁻¹ = z := d.late_S_act_z hs
  have hsZ : s ∈ NZ := by
    refine T3V.mem_normalizer_of_conj_eq (T3V.conj_eq_of_mem_closure ?_)
    intro a ha
    rcases ha with rfl | ha
    · exact hsz
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hst
  have hYN : Y ≤ NZ := pairNormalizers_le_normalizer K J z t
  have hKY : K ⊓ NZ ≤ Y := le_sup_left
  have hJY : J ⊓ NZ ≤ Y := le_sup_right
  have hconj_inf : ∀ {h : G} (A : Subgroup G), h ∈ NZ →
      conjSub h (A ⊓ NZ) = conjSub h A ⊓ NZ := by
    intro h A hh'
    rw [late_conjSub_inf, conjSub_eq_self_of_mem hh']
  have hconj_Y : ∀ {h : G} {A : Subgroup G}, h ∈ Y → A ≤ Y → conjSub h A ≤ Y := by
    intro h A hhY hA
    calc conjSub h A ≤ conjSub h Y := conjSub_mono hA
      _ = Y := conjSub_eq_self_of_mem hhY
  have hgY : t₀ * r ∈ Y := Y.mul_mem hh.t₀_mem_pair hh.r_mem_pair
  have hK'Y : K' ⊓ NZ ≤ Y := by
    have : K' ⊓ NZ = conjSub (t₀ * r) (J ⊓ NZ) := by
      rw [hconj_inf J (hYN hgY), hh.conj_J]
    rw [this]
    exact hconj_Y hgY hJY
  have hmY : r * t₀ ∈ Y := Y.mul_mem hh.r_mem_pair hh.t₀_mem_pair
  have hmt : (r * t₀) * z * (r * t₀)⁻¹ = t := by
    calc (r * t₀) * z * (r * t₀)⁻¹ = r * (t₀ * z * t₀⁻¹) * r⁻¹ := by group
      _ = r * (z * t) * r⁻¹ := by rw [hh.htz]
      _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
      _ = z * (t * z) := by rw [hh.hrz, hh.hrt]
      _ = t := by
        rw [← mul_assoc, hzt, mul_assoc, hz2, mul_one]
  have hJsi : IsUniqueInvolution (conjSub s J) t := by
    have := d.viol.hzJ.conj s
    rwa [hst] at this
  have hJsY : conjSub s J ⊓ NZ ≤ Y := by
    rcases d.late_members_of_inv hmt (d.hyp.conjInvariant s J d.late_mem_J) hJsi with h | h
    · rw [h, ← hconj_inf K (hYN hmY)]
      exact hconj_Y hmY hKY
    · rw [h, ← hconj_inf K' (hYN hmY)]
      exact hconj_Y hmY hK'Y
  refine mem_normalizer_of_conjSub_le ?_
  calc conjSub s Y = conjSub s (K ⊓ NZ) ⊔ conjSub s (J ⊓ NZ) := by
        rw [hY, pairNormalizers, late_conjSub_sup]
    _ = (K' ⊓ NZ) ⊔ (conjSub s J ⊓ NZ) := by
        rw [hconj_inf K hsZ, hconj_inf J hsZ, hsK]
    _ ≤ Y := sup_le hK'Y hJsY

theorem Std20Three.v_swap_rho (d : Std20Three K K' J S R R' W V z t) (h8 : Nat.card R = 8) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K') (hs2 : s * s = 1) :
    ∃ s₁ ρ : G, (∃ w ∈ W, w * s * w⁻¹ = s₁) ∧ s₁ ∈ (S : Subgroup G) ∧ s₁ * s₁ = 1 ∧
      (∃ ζ : G, InZ z t ζ ∧ s₁ = s * ζ) ∧ ρ * s₁ = s₁ * ρ ∧ Odd (orderOf ρ) ∧
      ρ * z * ρ⁻¹ = z * t ∧ ρ * t * ρ⁻¹ = z := by
  obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
  obtain ⟨-, hst⟩ := d.late_swap_sq_data hs hsK (by rw [hs2]; exact W.one_mem) heKW he2
  have hsz : s * z * s⁻¹ = z := d.late_S_act_z hs
  obtain ⟨x, e, hxW, hxz, hxt, hxs, hx3⟩ := d.v_exists_x hs2 (d.v_swap_Y hs hsK hst) (d.hWN hs)
    hsz hst
  obtain ⟨ζ, hζ, hW', hfix⟩ := d.v_swap_fixed h8 hs hsK hs2 hxW hxz hxt hxs hx3
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hζW : ζ ∈ W := by
    rcases hζ with rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact d.late_z_mem_W
    · exact d.late_t_mem_W
    · exact W.mul_mem d.late_z_mem_W d.late_t_mem_W
  have hsζ : s * ζ * s⁻¹ = ζ := by
    rcases hζ with rfl | rfl | rfl | rfl
    · group
    · exact hsz
    · exact hst
    · calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
        _ = z * t := by rw [hsz, hst]
  have hζ2 : ζ * ζ = 1 := by
    rcases hζ with rfl | rfl | rfl | rfl
    · group
    · exact hz2
    · exact ht2
    · calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [hzt]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hz2, ht2, one_mul]
  refine ⟨s * ζ, x, hW', Subgroup.mul_mem _ hs (d.hWS hζW), ?_, ⟨ζ, hζ, rfl⟩, ?_, ?_, hxz, hxt⟩
  · have hc : ζ * s = s * ζ := by
      calc ζ * s = (s * ζ * s⁻¹) * s := by rw [hsζ]
        _ = s * ζ := by group
    calc s * ζ * (s * ζ) = s * (ζ * s) * ζ := by group
      _ = s * (s * ζ) * ζ := by rw [hc]
      _ = (s * s) * (ζ * ζ) := by group
      _ = 1 := by rw [hs2, hζ2, one_mul]
  · calc x * (s * ζ) = (x * (s * ζ) * x⁻¹) * x := by group
      _ = (s * ζ) * x := by rw [hfix]
  · have : orderOf x ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hx3
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat this

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
