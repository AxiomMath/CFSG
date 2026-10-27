module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Central
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YInterface

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit

variable {G : Type} [Group G] [Finite G] {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}

section Aux

variable (hS : Setting L z) (hD : LocalData L U T0) (hY : YStruct L U z Y)
include hS hD hY

omit [Finite G] hY in
theorem z_mem_W : z ∈ Csub U z := V_le_Csub hS hD z_mem_V

omit [Finite G] in
theorem cent_Y_aux {y : G} (hy : y ∈ Y) (hc : y * z = z * y) : y ∈ U := by
  have hyW := hY.le_W hy
  have hV := Csub_comm_mem_V hS hD hyW hc.symm
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨u, hu, hyu⟩ := (mem_Vsub_iff hS hUL).1 hV
  rcases hyu with hyu | hyu
  · rw [hyu]; exact hu
  · exfalso
    apply hY.z_not_mem
    have : z = y * u⁻¹ := by rw [hyu]; group
    rw [this]
    exact mul_mem hy (inv_mem (hY.U_le hu))

theorem card_W_eq_two_mul (hW : Nat.card (Csub U z) = 2 ^ 23) : Nat.card Y = 2 ^ 22 := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  have hdisj : Disjoint (Y : Set G) ((fun y => z * y) '' (Y : Set G)) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨y', hy', rfl⟩
    apply hY.z_not_mem
    have : z = (z * y') * y'⁻¹ := by group
    rw [this]
    exact mul_mem hy (inv_mem hy')
  have hunion : (Csub U z : Set G) = (Y : Set G) ∪ (fun y => z * y) '' (Y : Set G) := by
    ext w
    constructor
    · intro hw
      rcases hY.cover w hw with h | h
      · exact Or.inl h
      · exact Or.inr ⟨z * w, h, by show z * (z * w) = w; rw [← mul_assoc, hS.z_mul_self, one_mul]⟩
    · rintro (h | ⟨y, hy, rfl⟩)
      · exact hY.le_W h
      · exact mul_mem (z_mem_W hS hD) (hY.le_W hy)
  have h1 : Nat.card (Csub U z) = (Csub U z : Set G).ncard := Nat.card_coe_set_eq _
  have h2 : Nat.card Y = (Y : Set G).ncard := Nat.card_coe_set_eq _
  have h3 : ((fun y => z * y) '' (Y : Set G)).ncard = (Y : Set G).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective z)
  rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), h3] at h1
  omega

end Aux

section Weak

variable (hS : Setting L z) (hD : LocalData L U T0) (hY : YStruct L U z Y)
include hS hD hY

omit hY in
theorem phi_surj (hW : Nat.card (Csub U z) = 2 ^ 23) :
    ∀ u ∈ U, ∃ c ∈ Csub U z, phiVal z c = u := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  let φ := phiHom hS hD
  have hrangeU : φ.range ≤ U := by
    rintro _ ⟨c, rfl⟩
    exact phiVal_mem hS hD (mem_Csub.1 c.2).1
  have hk : φ.ker = (Vsub U z).subgroupOf (Csub U z) := by
    ext ⟨c, hc⟩
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : phiVal z c = 1 := h
      exact Csub_comm_mem_V hS hD hc ((phiVal_eq_one_iff hS).1 h1)
    · intro hv
      have hv' : c ∈ Vsub U z := hv
      have hcz : z * c = c * z := V_comm hS hD z_mem_V hv'
      exact (phiVal_eq_one_iff hS).2 hcz
  have hker : Nat.card φ.ker = 2 ^ 12 := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (V_le_Csub hS hD)).toEquiv,
      card_Vsub hS hUL, hD.card_U]
    norm_num
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hker, hW] at hmul
  have hrange : Nat.card φ.range = 2 ^ 11 := by
    have : 2 ^ 12 * Nat.card φ.range = 2 ^ 12 * 2 ^ 11 := by rw [hmul]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hRU : φ.range = U :=
    Subgroup.eq_of_le_of_card_ge hrangeU (by rw [hrange, hD.card_U])
  intro u hu
  have : u ∈ φ.range := by rw [hRU]; exact hu
  obtain ⟨c, hc⟩ := this
  exact ⟨c, c.2, hc⟩

omit hY in
theorem z_conj_W_aux (hW : Nat.card (Csub U z) = 2 ^ 23) :
    ∀ u ∈ U, ∃ w ∈ Csub U z, w * z * w⁻¹ = z * u := by
  intro u hu
  obtain ⟨c, hc, hcu⟩ := phi_surj hS hD hW u hu
  refine ⟨c⁻¹, inv_mem hc, ?_⟩
  rw [inv_inv, conj_z_eq hS c, hcu]

omit [Finite G] in
theorem involution_mem_zU {w : G} (hwW : w ∈ Csub U z) (hwY : w ∉ Y) (hw2 : w * w = 1)
    (hYsq : ∀ y ∈ Y, y * y = 1) : ∃ u ∈ U, w = z * u := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  have hyY : z * w ∈ Y := (hY.cover w hwW).resolve_left hwY
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hcomm : z * w = w * z := by
    have h1 := hYsq _ hyY
    have h2 : z * w * z = w := by
      have : z * w * z * w = 1 := by simpa [mul_assoc] using h1
      calc z * w * z = z * w * z * (w * w) := by rw [hw2, mul_one]
        _ = (z * w * z * w) * w := by group
        _ = w := by rw [this, one_mul]
    calc z * w = z * w * z * z := by rw [mul_assoc, mul_assoc, hS.z_mul_self, mul_one]
      _ = w * z := by rw [h2]
  have hyz : (z * w) * z = z * (z * w) := by
    calc z * w * z = z * (w * z) := by group
      _ = z * (z * w) := by rw [hcomm]
  have hu := cent_Y_aux hS hD hY hyY hyz
  refine ⟨z * w, hu, ?_⟩
  calc w = (z * z) * w := by rw [hS.z_mul_self, one_mul]
    _ = z * (z * w) := by group

omit [Finite G] in
theorem conj_W_aux (hYsq : ∀ y ∈ Y, y * y = 1) (hnoconj : ∀ g : G, ∀ y ∈ Y, g * z * g⁻¹ ≠ y) :
    ∀ g : G, g * z * g⁻¹ ∈ Csub U z → ∃ u ∈ U, g * z * g⁻¹ = z * u := by
  intro g hg
  have hw2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hS.z_mul_self]; group
  have hwY : g * z * g⁻¹ ∉ Y := fun h => hnoconj g _ h rfl
  exact involution_mem_zU hS hD hY hg hwY hw2 hYsq

theorem noconj_Y_aux (hR : RankData L U z) (hYsq : ∀ y ∈ Y, y * y = 1)
    (hYab : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) (hW : Nat.card (Csub U z) = 2 ^ 23) :
    ∀ g : G, ∀ y ∈ Y, g * z * g⁻¹ ≠ y := by
  intro g y hy hgy
  have hcard := card_W_eq_two_mul hS hD hY hW
  have hB : Nat.card (conjSub g⁻¹ Y) ≤ 2 ^ 12 := by
    refine hR.rank_cent _ ?_ ?_ ?_
    · intro b hb
      rw [mem_conjSub, inv_inv] at hb
      have := hYab _ hb y hy
      rw [← hgy] at this
      calc b * z = g⁻¹ * (g * b * g⁻¹ * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * (g * b * g⁻¹)) * g := by rw [this]
        _ = z * b := by group
    · intro b hb
      rw [mem_conjSub, inv_inv] at hb
      have := hYsq _ hb
      calc b * b = g⁻¹ * (g * b * g⁻¹ * (g * b * g⁻¹)) * g := by group
        _ = 1 := by rw [this]; group
    · intro b hb b' hb'
      rw [mem_conjSub, inv_inv] at hb hb'
      have := hYab _ hb _ hb'
      calc b * b' = g⁻¹ * (g * b * g⁻¹ * (g * b' * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * b' * g⁻¹ * (g * b * g⁻¹)) * g := by rw [this]
        _ = b' * b := by group
  rw [card_conjSub, hcard] at hB
  norm_num at hB

theorem unique_Y_aux (hYsq : ∀ y ∈ Y, y * y = 1) (hW : Nat.card (Csub U z) = 2 ^ 23) :
    ∀ A : Subgroup G, A ≤ Csub U z → (∀ a ∈ A, a * a = 1) →
      (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) → Nat.card A = 2 ^ 22 → A = Y := by
  intro A hAW hA2 hAc hAcard
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  have hYcard := card_W_eq_two_mul hS hD hY hW
  have hAY : A ≤ Y := by
    by_contra hnle
    obtain ⟨a, haA, haY⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    have haz : ∃ u ∈ U, a = z * u :=
      involution_mem_zU hS hD hY (hAW haA) haY (hA2 a haA) hYsq
    obtain ⟨u, hu, hau⟩ := haz
    have hinfU : A ⊓ Y ≤ U := by
      intro y hy
      have hyA := hy.1
      have hyY := hy.2
      apply cent_Y_aux hS hD hY hyY
      have hc := hAc a haA y hyA
      have huy : y * u = u * y := (mem_Csub.1 (hY.le_W hyY)).2 u hu
      have : (y * z) * u = (z * y) * u := by
        calc y * z * u = y * (z * u) := by group
          _ = y * a := by rw [hau]
          _ = a * y := hc.symm
          _ = z * u * y := by rw [hau]
          _ = z * (u * y) := by group
          _ = z * (y * u) := by rw [huy]
          _ = z * y * u := by group
      exact mul_right_cancel this
    have hsplit : ∀ x ∈ A, x ∈ A ⊓ Y ∨ a⁻¹ * x ∈ A ⊓ Y := by
      intro x hx
      by_cases hxY : x ∈ Y
      · exact Or.inl ⟨hx, hxY⟩
      · right
        refine mem_inf.2 ⟨mul_mem (inv_mem haA) hx, ?_⟩
        have h1 : z * a ∈ Y := (hY.cover a (hAW haA)).resolve_left haY
        have h2 : z * x ∈ Y := (hY.cover x (hAW hx)).resolve_left hxY
        have h3 := mul_mem (inv_mem h1) h2
        have e : (z * a)⁻¹ * (z * x) = a⁻¹ * x := by group
        rwa [e] at h3
    have h1 := card_le_two_mul_of_split hsplit
    have h2 : Nat.card (A ⊓ Y : Subgroup G) ≤ Nat.card U := Subgroup.card_le_of_le hinfU
    rw [hD.card_U] at h2
    rw [hAcard] at h1
    omega
  exact Subgroup.eq_of_le_of_card_ge hAY (by rw [hYcard, hAcard])

theorem sylow_W_aux (hYsq : ∀ y ∈ Y, y * y = 1)
    (hnoconj : ∀ g : G, ∀ y ∈ Y, g * z * g⁻¹ ≠ y) (hW : Nat.card (Csub U z) = 2 ^ 23) :
    ∀ P : Subgroup G, P ≤ centralizer (U : Set G) → IsPGroup 2 P →
      ∃ c ∈ centralizer (U : Set G), P ≤ conjSub c (Csub U z) := by
  have := Fact.mk Nat.prime_two
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hconjW := conj_W_aux hS hD hY hYsq hnoconj
  have hWC : Csub U z ≤ centralizer (U : Set G) := fun c hc =>
    mem_centralizer_iff.2 fun u hu => ((mem_Csub.1 hc).2 u hu).symm
  have hW2 : IsPGroup 2 (Csub U z) := IsPGroup.of_card (n := 23) hW
  have hzW : z ∈ Csub U z := z_mem_W hS hD
  have hmax : ∀ Q : Subgroup G, Q ≤ centralizer (U : Set G) → IsPGroup 2 Q → Csub U z ≤ Q →
      Q = Csub U z := by
    intro Q hQC hQ hWQ
    by_contra hne
    have hlt : Csub U z < Q := lt_of_le_of_ne hWQ (Ne.symm hne)
    obtain ⟨x, hxQ, hxW, hxN⟩ := exists_mem_normalizer_of_lt hQ hlt
    have key : ∀ x' ∈ Q, x' ∈ normalizer (Csub U z : Set G) → ∀ v ∈ Vsub U z,
        x' * v * x'⁻¹ ∈ Vsub U z := by
      intro x' hx'Q hx'N v hv
      obtain ⟨u, hu, hvu⟩ := (mem_Vsub_iff hS hUL).1 hv
      have hx'C : ∀ u ∈ U, x' * u = u * x' := fun u hu =>
        (mem_centralizer_iff.1 (hQC hx'Q) u hu).symm
      have hxu : x' * u * x'⁻¹ = u := by rw [hx'C u hu]; group
      have hconj : x' * z * x'⁻¹ ∈ Csub U z := (mem_normalizer_iff.1 hx'N z).1 hzW
      obtain ⟨u', hu', hzu'⟩ := hconjW x' hconj
      rcases hvu with hvu | hvu
      · rw [hvu, hxu]; exact U_le_V hu
      · rw [hvu]
        have : x' * (z * u) * x'⁻¹ = (x' * z * x'⁻¹) * (x' * u * x'⁻¹) := by group
        rw [this, hzu', hxu]
        exact mul_mem (mul_mem z_mem_V (U_le_V hu')) (U_le_V hu)
    have hxN' : x ∈ Nsub U z := by
      rw [Nsub, mem_normalizer_iff]
      intro v
      refine ⟨key x hxQ hxN v, fun hv => ?_⟩
      have hxinvN : x⁻¹ ∈ normalizer (Csub U z : Set G) := inv_mem hxN
      have := key x⁻¹ (inv_mem hxQ) hxinvN _ hv
      have e : x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v := by group
      rwa [e] at this
    exact hxW (mem_Csub.2 ⟨hxN', fun u hu => (mem_centralizer_iff.1 (hQC hxQ) u hu).symm⟩)
  have hsyl : IsSylowOf 2 (Csub U z) (centralizer (U : Set G)) := by
    obtain ⟨S, hS', hWS⟩ := exists_isSylowOf_ge_of_le hWC hW2
    have := hmax S hS'.le hS'.isPGroup hWS
    rw [← this]; exact hS'
  intro P hPC hP
  obtain ⟨k, hk, hkP⟩ := exists_conj_le_of_isSylowOf hsyl hPC hP
  refine ⟨k, hk, fun a ha => ?_⟩
  rw [mem_conjSub]
  exact hkP a ha

theorem weakData_of (hR : RankData L U z) (hYsq : ∀ y ∈ Y, y * y = 1)
    (hYab : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y) (hW : Nat.card (Csub U z) = 2 ^ 23) :
    WeakData U z Y := by
  have hnoconj := noconj_Y_aux hS hD hY hR hYsq hYab hW
  exact
    { card_W := hW
      card_Y := card_W_eq_two_mul hS hD hY hW
      Y_sq := hYsq
      Y_comm := hYab
      cent_Y := fun y hy hc => cent_Y_aux hS hD hY hy hc
      noconj_Y := hnoconj
      conj_W := conj_W_aux hS hD hY hYsq hnoconj
      z_conj_W := z_conj_W_aux hS hD hW
      unique_Y := unique_Y_aux hS hD hY hYsq hW
      sylow_W := sylow_W_aux hS hD hY hYsq hnoconj hW }

end Weak

end CFSG.EvenSporadicStandard.J4Std
