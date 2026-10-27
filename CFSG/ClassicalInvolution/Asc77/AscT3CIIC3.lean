module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC4
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC7
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexMain

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Data

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G}
  {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem KW_inf_JW : (W ⊓ K) ⊓ (W ⊓ J) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨hxW, hxK⟩, -, hxJ⟩ := hx
  rw [Subgroup.mem_bot]
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hxS : x ∈ (S : Subgroup G) := d.hWS hxW
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  have hKJ : K ≠ J := fun h => d.viol.ne h.symm
  have hcard := d.hyp.card_le_two_of_le_inf hKΩ d.viol.mem hKJ hx2 (Subgroup.zpowers_le.mpr hxK)
    (Subgroup.zpowers_le.mpr hxJ)
  have hsq : x * x = 1 := mul_self_eq_one_of_card_zpowers_le_two hcard
  by_contra hne
  rcases d.viol.hzK.unique x hxK hsq with h1 | h1
  · exact hne h1
  · rcases d.viol.hzJ.unique x hxJ hsq with h2 | h2
    · exact hne h2
    · exact d.t_ne_z (h2.symm.trans h1)

theorem eq_t_of_invol_mem_V {x : G} (hx : x ∈ V) (hsq : x * x = 1) (hx1 : x ≠ 1) : x = t := by
  have hp := d.branch.odd
  have hq := d.branch.five
  obtain ⟨L₀, hL₀, hVL₀⟩ := d.hyp.exists_member_of_mem_USet hp d.hV
  obtain ⟨a₀, ha₀⟩ := d.hyp.exists_uniqueInvolution hp hq hL₀
  rcases ha₀.unique x (hVL₀ hx) hsq with h | h
  · exact absurd h hx1
  · rcases ha₀.unique t (hVL₀ d.htV) d.viol.hzJ.sq with h' | h'
    · exact absurd h' d.viol.hzJ.ne_one
    · exact h.trans h'.symm

theorem W_le_V_sup_K (hex : Hex20 (CoreAssembly.conjClass K) K J W) : W ≤ V ⊔ (W ⊓ K) := by
  have hp := d.branch.odd
  have hΩ := d.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hWc := d.late_hWc
  have hJWK : W ⊓ J ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => hWc x hx.1 y hy.1
  have hcV := Sec7.natCard_eq_two_mul_of_mem_USet hp hΩ d.hV hKΩ d.hR
  have hcJ := Sec7.natCard_eq_two_mul_of_mem_USet hp hΩ hex.JW hKΩ d.hR
  have hcard : Nat.card ↥(J ⊓ W) = Nat.card ↥V := by omega
  obtain ⟨-, -, -, -, -, -, hVcyc, -, hV4⟩ := hΩ.exists_data_of_mem_USet hp d.hV
  have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet hp d.hV
  obtain ⟨g, hg⟩ := hVcyc.exists_generator
  have hgord : orderOf g = Nat.card V := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := hV2.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set v₀ : G := (g : G) with hv₀
  have hv₀V : v₀ ∈ V := g.2
  have hv₀ord : orderOf v₀ = 2 ^ m := by rw [hv₀, Subgroup.orderOf_coe, hgord, hm]
  have hv₀W : v₀ ∈ W := d.hVW hv₀V
  have hv₀' : v₀ ∈ (W ⊓ K) ⊔ (W ⊓ J) := hex.hW ▸ hv₀W
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) (W ⊓ J) hJWK]
    at hv₀'
  obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := hv₀'
  have hcomm : a₁ * b₁ = b₁ * a₁ := hWc a₁ ha₁.1 b₁ hb₁.1
  have hpow : ∀ n : ℕ, v₀ ^ n = a₁ ^ n * b₁ ^ n := by
    intro n
    rw [← hab]
    exact (Commute.mul_pow (a := a₁) (b := b₁) hcomm) n
  have hpow_mem : ∀ n : ℕ, a₁ ^ n = 1 → b₁ ^ n = 1 → v₀ ^ n = 1 := by
    intro n h1 h2
    rw [hpow, h1, h2, one_mul]
  have hbot := d.KW_inf_JW
  have hb1e : b₁ ^ (2 ^ m) = 1 := by
    have h1 : v₀ ^ (2 ^ m) = 1 := by
      rw [← hv₀ord]
      exact pow_orderOf_eq_one v₀
    rw [hpow] at h1
    have h2 : a₁ ^ (2 ^ m) = (b₁ ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a₁ ^ (2 ^ m) ∈ (W ⊓ K) ⊓ (W ⊓ J) :=
      ⟨(W ⊓ K).pow_mem ha₁ _, by rw [h2]; exact (W ⊓ J).inv_mem ((W ⊓ J).pow_mem hb₁ _)⟩
    rw [hbot, Subgroup.mem_bot] at h3
    rw [h3] at h2
    exact inv_eq_one.mp h2.symm
  have hb1h : ¬ b₁ ^ (2 ^ (m - 1)) = 1 := by
    intro hb
    have hm1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hx : v₀ ^ (2 ^ (m - 1)) = a₁ ^ (2 ^ (m - 1)) := by
      rw [hpow, hb, mul_one]
    have hxV : v₀ ^ (2 ^ (m - 1)) ∈ V := V.pow_mem hv₀V _
    have hsq : v₀ ^ (2 ^ (m - 1)) * v₀ ^ (2 ^ (m - 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← hm1, ← hv₀ord]
      exact pow_orderOf_eq_one v₀
    have hx1 : v₀ ^ (2 ^ (m - 1)) ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hv₀ord] at this
      have h2 := Nat.le_of_dvd (by positivity) this
      have h3 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hxt := d.eq_t_of_invol_mem_V hxV hsq hx1
    have htK : t ∈ K := by
      rw [← hxt, hx]
      exact K.pow_mem ha₁.2 _
    have htsq : t * t = 1 := d.viol.hzJ.sq
    rcases d.viol.hzK.unique t htK htsq with h | h
    · exact d.viol.hzJ.ne_one h
    · exact d.t_ne_z h
  have hb1ord : orderOf b₁ = 2 ^ m := by
    have h := orderOf_eq_prime_pow (p := 2) (n := m - 1) hb1h (by
      rw [show m - 1 + 1 = m by omega]; exact hb1e)
    rwa [show m - 1 + 1 = m by omega] at h
  have hb₁J : Subgroup.zpowers b₁ ≤ J ⊓ W := by
    rw [Subgroup.zpowers_le]
    exact ⟨hb₁.2, hb₁.1⟩
  have hzeq : Subgroup.zpowers b₁ = J ⊓ W := by
    refine Subgroup.eq_of_le_of_card_ge hb₁J ?_
    rw [Nat.card_zpowers, hb1ord, hcard, ← hm]
  intro w hw
  have hw' : w ∈ (W ⊓ K) ⊔ (W ⊓ J) := hex.hW ▸ hw
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) (W ⊓ J) hJWK]
    at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  have hbz : b ∈ Subgroup.zpowers b₁ := by
    rw [hzeq]
    exact ⟨hb.2, hb.1⟩
  have hb₁V : b₁ ∈ V ⊔ (W ⊓ K) := by
    have : b₁ = a₁⁻¹ * v₀ := by
      rw [← hab]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right ha₁))
      (Subgroup.mem_sup_left hv₀V)
  have hbV : b ∈ V ⊔ (W ⊓ K) := by
    have := (Subgroup.zpowers_le (H := V ⊔ (W ⊓ K))).mpr hb₁V
    exact this hbz
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) hbV

theorem exists_conj_le_S {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUC : U ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c U ≤ (S : Subgroup G) := by
  obtain ⟨V₂, hV₂, hUV₂⟩ := IsSylow2In.exists_ge hU2 hUC
  obtain ⟨x, hx, hxS⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In d.late_isSylow2In_S hV₂
  refine ⟨x⁻¹, (Subgroup.centralizer _).inv_mem hx, ?_⟩
  have := conjSub_mono (n := x⁻¹) hUV₂
  rwa [← hxS, conjSub_inv_conjSub] at this

theorem U_cases {U : Subgroup G} (hU : U ∈ USet (CoreAssembly.conjClass K))
    (hUS : U ≤ (S : Subgroup G)) : U ≤ W ∨ U ≤ K ∨ U ≤ K' := by
  have hp := d.branch.odd
  have hq := d.branch.five
  obtain ⟨η, hη, hWη⟩ := d.hW
  have hηW : ∀ V' ∈ η, V' ≤ W := fun V' hV' => by
    rw [hWη]
    exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) V' hV'
  have hηS' : ∀ V' ∈ η, V' ≤ (S : Subgroup G) := fun V' hV' => (hηW V' hV').trans d.hWS
  obtain ⟨V', ⟨hV'η, hcase⟩, -⟩ := l6_8 p f hp hq G (CoreAssembly.conjClass K) d.hyp S U hU hUS
    η hη hηS'
  rcases hcase with h | h
  · exact Or.inl (h ▸ hηW V' hV'η)
  · have hle : U ⊔ V' ≤ (S : Subgroup G) := sup_le hUS (hηS' V' hV'η)
    rcases d.hRG _ h hle with h2 | h2
    · exact Or.inr (Or.inl ((le_sup_left.trans h2.le).trans d.hR.1))
    · exact Or.inr (Or.inr ((le_sup_left.trans h2.le).trans d.hR'.1))

end Std20

variable (p f)

@[expose] def Res20_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      ∀ c ∈ Subgroup.centralizer ({z} : Set G),
        conjSub c V ≤ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K'))

variable {p f}

theorem c20_3_of_res (hres : Res20_3 p f) : C20_3 p f := by
  intro G _ _ _ K K' J S R R' W V z t d
  have hx : Hex20 (CoreAssembly.conjClass K) K J W := hexAll p f G K K' J S R R' W V z t d
  have hp := d.branch.odd
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  show sec20X (CoreAssembly.conjClass K) z K K' =
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K'))
  have hNX : oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) ≤
      sec20X (CoreAssembly.conjClass K) z K K' :=
    sup_le (oddCoreOf_le_self _) (sup_le (tw.hVX) le_sec20X_pair)
  refine le_antisymm ?_ hNX
  set N := oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) with hN
  have hMN : K ⊔ K' ≤ N := le_trans le_sup_right le_sup_right
  have hKconj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inl rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  have hK'conj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K' ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inr rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  unfold sec20X
  refine sup_le (sup_le ?_ (le_trans le_sup_left hMN)) (le_trans le_sup_right hMN)
  refine iSup₂_le fun U hU => ?_
  obtain ⟨hUU, hUC⟩ := hU
  have hU2 : IsPGroup 2 U := d.hyp.isPGroup_of_mem_USet hp hUU
  obtain ⟨c, hc, hcU⟩ := d.exists_conj_le_S hU2 hUC
  have hU1 : conjSub c U ∈ USet (CoreAssembly.conjClass K) := USet.conj d.hyp.conjInvariant hUU c
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := (Subgroup.centralizer _).inv_mem hc
  have hback : U = conjSub c⁻¹ (conjSub c U) := (conjSub_inv_conjSub c U).symm
  rcases d.U_cases hU1 hcU with h | h | h
  · have h1 : conjSub c U ≤ V ⊔ K :=
      h.trans ((d.W_le_V_sup_K hx).trans (sup_le_sup_left inf_le_right V))
    have h2 := conjSub_mono (n := c⁻¹) h1
    rw [conjSub_inv_conjSub, conjSub_sup'] at h2
    exact h2.trans (sup_le (hres G K K' J S R R' W V z t d c⁻¹ hc') ((hKconj c⁻¹ hc').trans hMN))
  · have h2 := conjSub_mono (n := c⁻¹) h
    rw [conjSub_inv_conjSub] at h2
    exact h2.trans ((hKconj c⁻¹ hc').trans hMN)
  · have h2 := conjSub_mono (n := c⁻¹) h
    rw [conjSub_inv_conjSub] at h2
    exact h2.trans ((hK'conj c⁻¹ hc').trans hMN)

theorem res20_3_of_c20_3 (h3 : C20_3 p f) : Res20_3 p f := by
  intro G _ _ _ K K' J S R R' W V z t d c hc
  have hp := d.branch.odd
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have hX : sec20X (CoreAssembly.conjClass K) z K K' =
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) :=
    h3 G K K' J S R R' W V z t d
  have h1 : conjSub c V ≤ conjSub c (sec20X (CoreAssembly.conjClass K) z K K') :=
    conjSub_mono tw.hVX
  have h2 : conjSub c (sec20X (CoreAssembly.conjClass K) z K K') ≤
      sec20X (CoreAssembly.conjClass K) z K K' :=
    conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins hc
  exact (h1.trans h2).trans (Eq.le hX)

end Data

end CFSG.ClassicalInvolution.Asc77.T3CII
