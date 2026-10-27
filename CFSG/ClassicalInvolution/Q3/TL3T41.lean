module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLC
public import CFSG.ClassicalInvolution.Q3.TL3T32

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4 Matrix

theorem mat_pow_five : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A * A * A * A = 1 → A = 1 := by
  decide +kernel

theorem sl_pow_five {A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} (h : A ^ 5 = 1) : A = 1 := by
  apply Subtype.ext
  apply mat_pow_five
  have := congrArg Subtype.val h
  simpa [pow_succ, mul_assoc] using this

theorem l32_pow_five {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ l32) (h5 : σ ^ 5 = 1) : σ = 1 := by
  obtain ⟨A, rfl⟩ := exists_lpermHom_eq hσ
  have hA : A ^ 5 = 1 := lpermHom_injective (by rw [map_pow, h5, map_one])
  rw [sl_pow_five hA, map_one]

theorem agl32_pow_five {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ agl32) (h5 : σ ^ 5 = 1) : σ = 1 := by
  set s : ↥agl32 := ⟨σ, hσ⟩ with hs
  have hs5 : s ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h5)
  have hlin : linHom s = 1 := sl_pow_five (by rw [← map_pow, hs5, map_one])
  have h1 : σ = aperm 1 (transPart s) := by
    have := aperm_linPart s
    rw [← linHom_apply, hlin] at this
    exact this.symm
  have h2 : σ * σ = 1 := by rw [h1]; exact aperm_one_mul_self _
  calc σ = σ ^ 5 * ((σ * σ) * (σ * σ))⁻¹ := by group
    _ = 1 := by rw [h5, h2, mul_one, inv_one, mul_one]

theorem aeBarOver_pow_five {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))}
    (hA : ∀ σ ∈ A, σ ^ 5 = 1 → σ = 1) {x : AEQ n} (hx : x ∈ aeBarOver A) (h5 : x ^ 5 = 1) :
    x = 1 := by
  have hp : permQ n x = 1 := hA _ (permQ_mem_of_mem_aeBarOver hx) (by rw [← map_pow, h5, map_one])
  have h2 : x * x = 1 := mul_self_of_mem_ker_permQ hp
  calc x = x ^ 5 * ((x * x) * (x * x))⁻¹ := by group
    _ = 1 := by rw [h5, h2, mul_one, inv_one, mul_one]

variable {G : Type} [Group G]

theorem eq_one_of_pow_five_of_two {x : G} (h5 : x ^ 5 = 1) (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x = 1 := by
  obtain ⟨k, hk⟩ := h2
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 5)) (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one h5))

theorem AEIdentOn.pow_five {P : Set (Subgroup G)} {m : ℕ} {𝒜 : Set (Finset (Fin m))}
    {H : Subgroup (AEQ m)} (I : AEIdentOn P m 𝒜 H) (hk : IsPGroup 2 I.φ.ker)
    (hH : ∀ h ∈ H, h ^ 5 = 1 → h = 1) {x : ↥(pSpan P)} (h5 : x ^ 5 = 1) : x = 1 := by
  have hr : I.φ.range = H := I.range_eq
  have hx : I.φ x ∈ I.φ.range := ⟨x, rfl⟩
  rw [hr] at hx
  have h1 : I.φ x = 1 := hH _ hx (by rw [← map_pow, h5, map_one])
  obtain ⟨k, hk'⟩ := hk ⟨x, h1⟩
  exact eq_one_of_pow_five_of_two h5 ⟨k, by
    have := congrArg Subtype.val hk'
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this⟩

theorem E8Struct.pow_five {E : Subgroup G} (hE : E8Struct ⊤ E) {x : G} (h5 : x ^ 5 = 1) :
    x = 1 := by
  have hG := card_e8 hE
  have h1 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have h2 : orderOf x ∣ 1344 := hG ▸ orderOf_dvd_natCard x
  have h3 : orderOf x ∣ Nat.gcd 5 1344 := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 5 1344 = 1 by norm_num, Nat.dvd_one] at h3
  exact orderOf_eq_one_iff.mp h3

section W

variable [Finite G] {Ω : Set (Subgroup G)}

theorem sup_eq_of_relIndex_two {L U U' : Subgroup G} (h8 : Nat.card L = 8) (hU : U ≤ L)
    (hU' : U' ≤ L) (hi : U.relIndex L = 2) (hi' : U'.relIndex L = 2) (hne : U ≠ U') :
    U ⊔ U' = L := by
  have hc : Nat.card U = 4 := by
    have := Subgroup.relIndex_mul_card U L
    rw [inf_eq_left.mpr hU, hi, h8] at this
    omega
  have hc' : Nat.card U' = 4 := by
    have := Subgroup.relIndex_mul_card U' L
    rw [inf_eq_left.mpr hU', hi', h8] at this
    omega
  have hle : U ⊔ U' ≤ L := sup_le hU hU'
  have hlt : U < U ⊔ U' := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    have h1 : U' ≤ U := h ▸ le_sup_right
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hc, hc'])).symm
  have hdvd : Nat.card ↥(U ⊔ U') ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hle
  have hdvd' : 4 ∣ Nat.card ↥(U ⊔ U') := hc ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne' : Nat.card ↥(U ⊔ U') ≠ 4 := by
    intro h
    exact (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hc]))
  have h8' : Nat.card ↥(U ⊔ U') = 8 := by
    obtain ⟨k, hk⟩ := hdvd'
    have hpos : 0 < Nat.card ↥(U ⊔ U') := Nat.card_pos
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(U ⊔ U') <;> omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8, h8'])

theorem wSet_ne_singleton (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) (hne : Ω.Nonempty)
    (hmove : ∀ L ∈ Ω, ∀ U : Subgroup G, U ≤ L → U.relIndex L = 2 → IsCyclic U →
      ∃ x : G, conjSub x L = L ∧ conjSub x U ≠ U)
    (W : Subgroup G) : WSet Ω ≠ {W} := by
  classical
  intro hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L₀, hL₀⟩ := hne
  obtain ⟨S, hL₀S⟩ := (h2 L₀ hL₀).exists_le_sylow
  have hq₀ : IsQuatSub L₀ :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup hL₀ (h2 L₀ hL₀))
  obtain ⟨a, haL₀, ha4⟩ := hq₀.exists_orderOf_four
  set U₀ := Subgroup.zpowers a with hU₀
  have hU₀L : U₀ ≤ L₀ := Subgroup.zpowers_le.mpr haL₀
  have hU₀c : Nat.card U₀ = 4 := by rw [hU₀, Nat.card_zpowers, ha4]
  have hU₀i : U₀.relIndex L₀ = 2 := by
    have := Subgroup.relIndex_mul_card U₀ L₀
    rw [inf_eq_left.mpr hU₀L, hU₀c, h8 L₀ hL₀] at this
    omega
  have hU₀U : U₀ ∈ USet Ω :=
    ⟨L₀, mem_RSet_of_isPGroup hL₀ (h2 L₀ hL₀), hU₀L, inferInstance, hU₀i⟩
  obtain ⟨η, hηS, hinv⟩ := (Q3T8.Asc77.l6_9_proved G Ω hΩ S).1
  have hηG : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηne : η.Nonempty := by
    by_contra hη
    rw [Set.not_nonempty_iff_eq_empty] at hη
    have h1 := hηS.2.2 {U₀} (fun U hU => by
      rw [Set.mem_singleton_iff.mp hU]
      exact ⟨hU₀U, hU₀L.trans hL₀S⟩) (fun U hU U' hU' hne' => by
        rw [Set.mem_singleton_iff.mp hU, Set.mem_singleton_iff.mp hU'] at hne'
        exact absurd rfl hne')
    rw [hη, Set.ncard_singleton, Set.ncard_empty] at h1
    omega
  obtain ⟨U, hU⟩ := hηne
  have hUU : U ∈ USet Ω := (hηS.1 hU).1
  obtain ⟨R, hR, hUR, hUcyc, hUi⟩ := hUU
  obtain ⟨L, hL, hRL, -, hmax⟩ := mem_RSet_iff.mp hR
  have hRe : L = R := hmax L le_rfl (h2 L hL) hRL
  subst hRe
  have hWeq : W = etaSpan η := by
    have : etaSpan η ∈ WSet Ω := ⟨η, hηG, rfl⟩
    rw [hW] at this
    exact this.symm
  have hWn : ∀ g : G, conjSub g W = W := by
    intro g
    have h1 : etaSpan (conjSub g '' η) ∈ WSet Ω :=
      ⟨_, Sec7.etaG_conj hΩ.conjInvariant hηG g, rfl⟩
    rw [hW] at h1
    have h2' : etaSpan (conjSub g '' η) = conjSub g (etaSpan η) := by
      unfold etaSpan conjSub
      rw [iSup_image, Subgroup.map_iSup]
      congr 1
      funext U
      rw [Subgroup.map_iSup]
    rw [Set.mem_singleton_iff.mp h1] at h2'
    rw [hWeq] at h2' ⊢
    exact h2'.symm
  have hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    rw [hWeq]
    exact etaSpan_comm hΩ hηG
  obtain ⟨x, hxL, hxU⟩ := hmove L hL U hUR hUi hUcyc
  have hUW : U ≤ W := hWeq ▸ le_etaSpan hU
  have hUxW : conjSub x U ≤ W := by
    rw [← hWn x]
    exact conjSub_mono hUW
  have hUxL : conjSub x U ≤ L := by
    rw [← hxL]
    exact conjSub_mono hUR
  have hUxi : (conjSub x U).relIndex L = 2 := by
    have h1 := Subgroup.relIndex_mul_card (conjSub x U) L
    rw [inf_eq_left.mpr hUxL, h8 L hL] at h1
    have h3 := Subgroup.relIndex_mul_card U L
    rw [inf_eq_left.mpr hUR, hUi, h8 L hL] at h3
    have hcard : Nat.card ↥(conjSub x U) = Nat.card U :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have hU4 : Nat.card U = 4 := by omega
    rw [hcard, hU4] at h1
    omega
  have hLW : L ≤ W := by
    rw [← sup_eq_of_relIndex_two (h8 L hL) hUR hUxL hUi hUxi (Ne.symm hxU)]
    exact sup_le hUW hUxW
  obtain ⟨-, P, hP, hPnc⟩ := hΩ.omega1 L hL
  apply hPnc
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  exact hWc _ (hLW (hP.1 a.2)) _ (hLW (hP.1 b.2))

theorem comm_of_pow_three_of_conjSub_eq {L U : Subgroup G} (h8 : Nat.card L = 8) (hUL : U ≤ L)
    (hi : U.relIndex L = 2) (hUc : IsCyclic U) {y : G} (hy3 : y ^ 3 = 1)
    (hyL : conjSub y L = L) (hyU : conjSub y U = U) : ∀ l ∈ L, y * l = l * y := by
  classical
  have hU4 : Nat.card U = 4 := by
    have := Subgroup.relIndex_mul_card U L
    rw [inf_eq_left.mpr hUL, hi, h8] at this
    omega
  have hmemU : ∀ {x : G}, x ∈ U → y * x * y⁻¹ ∈ U := fun hx => by
    rw [← hyU]
    exact conj_mem_conjSub hx
  have hmemU' : ∀ {x : G}, y * x * y⁻¹ ∈ U → x ∈ U := fun {x} hx => by
    rw [← hyU, mem_conjSub_iff] at hx
    have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rwa [e] at hx
  have hmemL : ∀ {x : G}, x ∈ L → y * x * y⁻¹ ∈ L := fun hx => by
    rw [← hyL]
    exact conj_mem_conjSub hx
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥U)
  set u : G := (g : G) with hu
  have huU : u ∈ U := g.2
  have hgen : ∀ x ∈ U, ∃ k : ℤ, u ^ k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨k, by have := congrArg Subtype.val hk; simpa using this⟩
  have hUz : Subgroup.zpowers u = U := by
    apply le_antisymm (Subgroup.zpowers_le.mpr huU)
    intro x hx
    obtain ⟨k, hk⟩ := hgen x hx
    exact ⟨k, hk⟩
  have hou : orderOf u = 4 := by rw [← Nat.card_zpowers, hUz, hU4]
  have hu4 : u ^ 4 = 1 := by rw [← hou]; exact pow_orderOf_eq_one u
  have hu2 : u ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hou] at this
    norm_num at this
  have hc : y * u * y⁻¹ = u ∨ y * u * y⁻¹ = u⁻¹ := by
    have hko : orderOf (y * u * y⁻¹) = 4 := by
      rw [← hou, ← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective u
    have hcz : y * u * y⁻¹ ∈ Subgroup.zpowers u := hUz ▸ hmemU huU
    rw [mem_zpowers_iff_mem_range_orderOf, hou] at hcz
    obtain ⟨j, hj, hju⟩ := Finset.mem_image.mp hcz
    rw [Finset.mem_range] at hj
    interval_cases j
    · rw [pow_zero] at hju
      rw [← hju, orderOf_one] at hko
      norm_num at hko
    · left
      rw [← hju, pow_one]
    · exfalso
      have : (y * u * y⁻¹) ^ 2 = 1 := by rw [← hju, ← pow_mul]; exact hu4
      have := orderOf_dvd_of_pow_eq_one this
      rw [hko] at this
      norm_num at this
    · right
      rw [← hju, eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hu4
  have hyu : y * u * y⁻¹ = u := by
    rcases hc with h | h
    · exact h
    · exfalso
      have h3 : y ^ 3 * u * (y ^ 3)⁻¹ = u⁻¹ := by
        have e1 : y ^ 3 * u * (y ^ 3)⁻¹ = y * (y * (y * u * y⁻¹) * y⁻¹) * y⁻¹ := by
          rw [pow_three]
          group
        rw [e1, h]
        have e2 : y * u⁻¹ * y⁻¹ = (y * u * y⁻¹)⁻¹ := by group
        rw [e2, h, inv_inv, h]
      rw [hy3, one_mul, inv_one, mul_one] at h3
      apply hu2
      calc u ^ 2 = u * u := pow_two u
        _ = u * u⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel u
  have hcU : ∀ x ∈ U, y * x * y⁻¹ = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := hgen x hx
    rw [← conj_zpow, hyu]
  have hidx : (U.subgroupOf L).index = 2 := hi
  intro l hl
  by_cases hlU : l ∈ U
  · have := hcU l hlU
    calc y * l = y * l * y⁻¹ * y := by group
      _ = l * y := by rw [this]
  set b := y * l * y⁻¹ with hb
  have hbL : b ∈ L := hmemL hl
  have hbU : b ∉ U := fun h => hlU (hmemU' h)
  set v := l⁻¹ * b with hv
  have hvU : v ∈ U := by
    have hl' : (⟨l⁻¹, L.inv_mem hl⟩ : ↥L) ∉ U.subgroupOf L := fun h =>
      hlU (by have := U.inv_mem (Subgroup.mem_subgroupOf.mp h); simpa using this)
    have hb' : (⟨b, hbL⟩ : ↥L) ∉ U.subgroupOf L := fun h => hbU (Subgroup.mem_subgroupOf.mp h)
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hl' hb')
    exact Subgroup.mem_subgroupOf.mp h1
  have hyv : y * v * y⁻¹ = v := hcU v hvU
  have hbv : b = l * v := by rw [hv]; group
  have hconj : ∀ w : G, y * (w * v) * y⁻¹ = (y * w * y⁻¹) * v := fun w => by
    calc y * (w * v) * y⁻¹ = (y * w * y⁻¹) * (y * v * y⁻¹) := by group
      _ = (y * w * y⁻¹) * v := by rw [hyv]
  have h3 : y ^ 3 * l * (y ^ 3)⁻¹ = l * v ^ 3 := by
    have e1 : y ^ 3 * l * (y ^ 3)⁻¹ = y * (y * (y * l * y⁻¹) * y⁻¹) * y⁻¹ := by
      rw [pow_three]
      group
    have s1 : y * l * y⁻¹ = l * v := hbv
    have s2 : y * (l * v) * y⁻¹ = l * v * v := by rw [hconj, s1]
    have s3 : y * (l * v * v) * y⁻¹ = l * v * v * v := by rw [hconj, s2]
    rw [e1, s1, s2, s3, pow_three]
    group
  rw [hy3, one_mul, inv_one, mul_one] at h3
  have hv3 : v ^ 3 = 1 := by
    have := congrArg (fun w => l⁻¹ * w) h3
    simpa using this.symm
  have hv1 : v = 1 := by
    have h1 : orderOf v ∣ 3 := orderOf_dvd_of_pow_eq_one hv3
    have h2 : orderOf v ∣ 4 := by
      have := orderOf_dvd_natCard (⟨v, hvU⟩ : ↥U)
      rwa [Subgroup.orderOf_mk, hU4] at this
    have : orderOf v ∣ Nat.gcd 3 4 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 3 4 = 1 by norm_num, Nat.dvd_one] at this
    exact orderOf_eq_one_iff.mp this
  have hbl : b = l := by rw [hbv, hv1, mul_one]
  calc y * l = y * l * y⁻¹ * y := by group
    _ = l * y := by rw [← hb, hbl]

end W

end CFSG.ClassicalInvolution.Q3.TC.Thin
