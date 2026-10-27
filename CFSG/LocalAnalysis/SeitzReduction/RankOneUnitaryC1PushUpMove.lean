module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NcycEnd

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem pushUp_false_of_card_le_neg (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U W : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y) (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hUA : szA₁ (szT₁ L T) ≤ U)
    (hUT : T ≤ normalizer (U : Set G)) (hTUeq : T ⊓ U = szA₁ (szT₁ L T))
    (hT₁Ueq : szT₁ L T ⊓ U = szA₁ (szT₁ L T)) (hPN : T ⊔ U ≤ normalizer (U : Set G))
    (hWT : W ≤ szT₁ L T) (hAW : szA₁ (szT₁ L T) ≤ W) (hWcard : Nat.card W = (2 ^ f) ^ 2)
    {w : G} (hwT : w ∈ T)
    (hWiff : ∀ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W))
    (hneg : ∀ u ∈ U, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) {y u₁ g : G} (hu₁ : u₁ ∈ U)
    (hy : y ∈ szT₁ L T) (hx_eq : g⁻¹ * t * g = y * u₁ * w) (hxP : g⁻¹ * t * g ∈ T ⊔ U)
    (hTle : Nat.card T ≤
      Nat.card ((T ⊔ U) ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G)) : False := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, hA₁comm, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hT₁N : szT₁ L T ≤ normalizer (U : Set G) := hT₁T.trans hUT
  set x := g⁻¹ * t * g with hxdef
  have hconjU : ∀ u' ∈ U, x * u' * x⁻¹ = w * u' * w⁻¹ := by
    intro u' hu'
    have hc : w * u' * w⁻¹ ∈ U := (mem_normalizer_iff.mp (hUT hwT) u').mp hu'
    have h2 : y * (w * u' * w⁻¹) = (w * u' * w⁻¹) * y := hUc y hy _ hc
    have h1 : u₁ * (w * u' * w⁻¹) = (w * u' * w⁻¹) * u₁ := hUab _ hu₁ _ hc
    rw [hx_eq]
    calc y * u₁ * w * u' * (y * u₁ * w)⁻¹ = y * (u₁ * (w * u' * w⁻¹)) * u₁⁻¹ * y⁻¹ := by group
      _ = y * ((w * u' * w⁻¹) * u₁) * u₁⁻¹ * y⁻¹ := by rw [h1]
      _ = (y * (w * u' * w⁻¹)) * y⁻¹ := by group
      _ = ((w * u' * w⁻¹) * y) * y⁻¹ := by rw [h2]
      _ = w * u' * w⁻¹ := by group
  have hconjT : ∀ y' ∈ szT₁ L T, x * y' * x⁻¹ = y * (w * y' * w⁻¹) * y⁻¹ := by
    intro y' hy'
    have hc : w * y' * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y').mp hy'
    have h1 : u₁ * (w * y' * w⁻¹) = (w * y' * w⁻¹) * u₁ := (hUc _ hc u₁ hu₁).symm
    rw [hx_eq]
    calc y * u₁ * w * y' * (y * u₁ * w)⁻¹ = y * (u₁ * (w * y' * w⁻¹)) * u₁⁻¹ * y⁻¹ := by group
      _ = y * ((w * y' * w⁻¹) * u₁) * u₁⁻¹ * y⁻¹ := by rw [h1]
      _ = y * (w * y' * w⁻¹) * y⁻¹ := by group
  have hxT₁ : ∀ y' ∈ szT₁ L T, x * y' * x⁻¹ ∈ szT₁ L T := by
    intro y' hy'
    rw [hconjT y' hy']
    exact mul_mem (mul_mem hy ((mem_normalizer_iff.mp (hTN₁ hwT) y').mp hy')) (inv_mem hy)
  have hxU : ∀ u' ∈ U, x * u' * x⁻¹ ∈ U := fun u' hu' =>
    (mem_normalizer_iff.mp (hPN hxP) u').mp hu'
  have hWx : ∀ y' ∈ szT₁ L T, y'⁻¹ * (x * y' * x⁻¹) ∈ szA₁ (szT₁ L T) → y' ∈ W := by
    intro y' hy' hm
    have hc : w * y' * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y').mp hy'
    have hcomm' : y * (w * y' * w⁻¹)⁻¹ * y⁻¹ * (w * y' * w⁻¹) ∈ szA₁ (szT₁ L T) := by
      rw [hA₁comm]
      have := commutator_mem_commutator hy (inv_mem hc)
      rwa [commutatorElement_def, inv_inv] at this
    refine (hWiff y' hy').mp ?_
    have e : y'⁻¹ * (w * y' * w⁻¹) = (y'⁻¹ * (x * y' * x⁻¹)) *
        (y * (w * y' * w⁻¹)⁻¹ * y⁻¹ * (w * y' * w⁻¹)) := by
      rw [hconjT y' hy']; group
    rw [e]
    exact mul_mem hm hcomm'
  have hC := ncyc_card_inf_centralizer_mul_le hUc (le_of_eq hT₁Ueq) hAW hWT hUA hxT₁ hxU hWx
  have hCU : Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 ^ f := by
    rw [← hA₁card]
    apply card_le_of_le
    intro u' hu'
    obtain ⟨hu'U, hu'C⟩ := mem_inf.mp hu'
    apply hneg u' hu'U
    rw [← hconjU u' hu'U]
    have := mem_centralizer_singleton_iff.mp hu'C
    rw [← this, mul_inv_cancel_right]
  have hBN : (T ⊔ U) ⊓ centralizer ({x} : Set G) ≤
      normalizer ((szT₁ L T ⊔ U : Subgroup G) : Set G) :=
    inf_le_left.trans (h.sup_le_normalizer_sup_szT₁ hS2 hUc hUT)
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hBN
  have hBP : szT₁ L T ⊔ U ≤ T ⊔ U := sup_le (hT₁T.trans le_sup_left) le_sup_right
  have hCB : (T ⊔ U) ⊓ centralizer ({x} : Set G) ⊓ (szT₁ L T ⊔ U) =
      (szT₁ L T ⊔ U) ⊓ centralizer ({x} : Set G) := by
    ext z
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨-, hzc⟩, hzB⟩
      exact ⟨hzB, hzc⟩
    · rintro ⟨hzB, hzc⟩
      exact ⟨⟨hBP hzB, hzc⟩, hzB⟩
  rw [hCB] at hprod
  have hsupP : Nat.card (((T ⊔ U) ⊓ centralizer ({x} : Set G)) ⊔ (szT₁ L T ⊔ U) : Subgroup G) ≤
      Nat.card (T ⊔ U : Subgroup G) := card_le_of_le (sup_le inf_le_left hBP)
  have hP := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hUT
  have hB := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hT₁N
  rw [hTUeq, hA₁card] at hP
  rw [hT₁Ueq, hA₁card, hT₁card] at hB
  rw [hA₁card, hWcard] at hC
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  set q := 2 ^ f with hqdef
  set c := Nat.card ((T ⊔ U) ⊓ centralizer ({x} : Set G) : Subgroup G)
  set bb := Nat.card (szT₁ L T ⊔ U : Subgroup G)
  set bc := Nat.card ((szT₁ L T ⊔ U) ⊓ centralizer ({x} : Set G) : Subgroup G)
  set pp := Nat.card (T ⊔ U : Subgroup G)
  set nu := Nat.card U
  set nt := Nat.card T
  set cu := Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G)
  have hnu : 0 < nu := Nat.card_pos
  have hcpos : 0 < c := Nat.card_pos
  have hqpos : 0 < q := by omega
  have h1 : c * bb ≤ pp * bc := by
    rw [← hprod]
    exact Nat.mul_le_mul_right _ hsupP
  have h3 : bc ≤ q ^ 2 := by
    have : bc * q ≤ q ^ 2 * q := hC.trans (Nat.mul_le_mul_left _ hCU)
    exact Nat.le_of_mul_le_mul_right this hqpos
  have h2 : c * (q ^ 3 * nu) ≤ nt * nu * q ^ 2 := by
    calc c * (q ^ 3 * nu) = c * (bb * q) := by rw [hB]
      _ = (c * bb) * q := by ring
      _ ≤ (pp * bc) * q := Nat.mul_le_mul_right _ h1
      _ = (pp * q) * bc := by ring
      _ = nt * nu * bc := by rw [hP]
      _ ≤ nt * nu * q ^ 2 := Nat.mul_le_mul_left _ h3
  have h4 : c * nu * q ^ 3 ≤ c * nu * q ^ 2 := by
    calc c * nu * q ^ 3 = c * (q ^ 3 * nu) := by ring
      _ ≤ nt * nu * q ^ 2 := h2
      _ ≤ c * nu * q ^ 2 := by
        have := Nat.mul_le_mul_right (nu * q ^ 2) hTle
        calc nt * nu * q ^ 2 = nt * (nu * q ^ 2) := by ring
          _ ≤ c * (nu * q ^ 2) := this
          _ = c * nu * q ^ 2 := by ring
  have h5 : q ^ 3 ≤ q ^ 2 := Nat.le_of_mul_le_mul_left h4 (Nat.mul_pos hcpos hnu)
  have h6 : q ^ 3 = q * q ^ 2 := by ring
  have h7 : 0 < q ^ 2 := by positivity
  rw [h6] at h5
  have : q ≤ 1 := by
    by_contra hq
    push Not at hq
    have : 2 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
    omega
  omega

theorem pushUp_exists_mul_t_of_card_le (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y)
    (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hUA : szA₁ (szT₁ L T) ≤ U) (hUT : T ≤ normalizer (U : Set G))
    (hU8 : ∃ a ∈ U, ∃ b ∈ U, ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1)
    (hsign : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
      (∀ u ∈ U, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∨
        ∀ u ∈ U, u⁻¹ * (w * u * w⁻¹) ∈ szA₁ (szT₁ L T))
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t)
    (hTU : ∀ x ∈ T, x ∈ U → x ∈ szA₁ (szT₁ L T)) (hTUeq : T ⊓ U = szA₁ (szT₁ L T))
    (hT₁Ueq : szT₁ L T ⊓ U = szA₁ (szT₁ L T)) (hP2 : IsPGroup 2 (T ⊔ U : Subgroup G))
    (hPN : T ⊔ U ≤ normalizer (U : Set G)) {g : G} (hgP : g⁻¹ * t * g ∈ T ⊔ U)
    (hTle : Nat.card T ≤
      Nat.card ((T ⊔ U) ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G)) :
    ∃ y ∈ szT₁ L T, ∃ u ∈ U, g⁻¹ * t * g = y * u * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, hA₁comm, hsq, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hT₁N : szT₁ L T ≤ normalizer (U : Set G) := hT₁T.trans hUT
  obtain ⟨a, ha, a', ha', hab⟩ := hU8
  set x := g⁻¹ * t * g with hxdef
  have hxP : x ∈ T ⊔ U := hgP
  have hCp : IsPGroup 2 ((T ⊔ U) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    hP2.to_le inf_le_left
  have hx2 : x ^ 2 = 1 := by
    rw [hxdef, sq, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ← sq,
      h.sq_eq_one]
    group
  obtain ⟨s, hs, u, hu, hsu⟩ := ncyc_exists_mul_of_mem_sup hUT hxP
  have hs2 : s ^ 2 ∈ szT₁ L T := by
    have e : s ^ 2 = (s * u) ^ 2 * (u⁻¹ * (s⁻¹ * u⁻¹ * s)) := by rw [sq, sq]; group
    have hU' : u⁻¹ * (s⁻¹ * u⁻¹ * s) ∈ U :=
      mul_mem (inv_mem hu) ((mem_normalizer_iff''.mp (hUT hs) _).mp (inv_mem hu))
    have hsU : s ^ 2 ∈ U := by rw [e, hsu, hx2, one_mul]; exact hU'
    exact szA₁_le _ (hTU _ (pow_mem hs 2) hsU)
  have hZ8 : ∀ b₁ ∈ T ⊔ U, ∀ b₂ ∈ T ⊔ U, x * b₁ = b₁ * x → x * b₂ = b₂ * x →
      (∀ k : ℤ, (b₁ ^ k * b₂) ^ 4 ≠ 1 ∧ (b₂ ^ k * b₁) ^ 4 ≠ 1) → False := by
    intro b₁ hb₁ b₂ hb₂ hc₁ hc₂ hk
    exact h.false_of_conj_of_pow_four hS2 hCp inf_le_right
      (mem_inf.mpr ⟨hb₁, mem_centralizer_singleton_iff.mpr hc₁.symm⟩)
      (mem_inf.mpr ⟨hb₂, mem_centralizer_singleton_iff.mpr hc₂.symm⟩) hk
  by_cases hsS : s ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsS
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    ·
      rw [hz1, mul_one] at hyz
      have hcx : ∀ u' ∈ U, x * u' = u' * x := by
        intro u' hu'
        rw [← hsu, ← hyz]
        calc y * u * u' = y * (u * u') := by group
          _ = y * (u' * u) := by rw [hUab u hu u' hu']
          _ = (y * u') * u := by group
          _ = (u' * y) * u := by rw [hUc y hy u' hu']
          _ = u' * (y * u) := by group
      exact (hZ8 a (mem_sup_right ha) a' (mem_sup_right ha') (hcx a ha) (hcx a' ha') hab).elim
    ·
      rw [hz1] at hyz
      have htu : t * u * t⁻¹ ∈ U := (mem_normalizer_iff.mp (hUT htT) u).mp hu
      exact ⟨y, hy, t * u * t⁻¹, htu, hsu.symm.trans (by rw [← hyz]; group)⟩
  ·
    obtain ⟨v, hvT, hv2, hvS⟩ := hv
    have hsv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hs hvT (mem_sup_left hs2)
      (by rw [hv2]; exact one_mem _) hsS hvS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsv
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    have hzv : z * v = v * z := (commute_of_mem_zpowers hz
      (mem_centralizer_singleton_iff.mp (h.le hvT))).symm
    set w := z * v with hwdef
    have hwT : w ∈ T := mul_mem hzT hvT
    have hw2 : w ^ 2 = 1 := by
      have hz2 : z ^ 2 = 1 := by
        rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
        · exact one_pow 2
        · exact h.sq_eq_one
      rw [hwdef, (show Commute z v from hzv).mul_pow, hz2, hv2, one_mul]
    have hwS : w ∉ szT₁ L T ⊔ zpowers t := by
      intro hwS'
      apply hvS
      rw [show v = z⁻¹ * w by rw [hwdef]; group]
      exact mul_mem (mem_sup_right (inv_mem hz)) hwS'
    have hs_eq : s = y * w := by rw [hwdef, ← mul_assoc, hyz]; group
    set u₁ := w * u * w⁻¹ with hu₁def
    have hu₁ : u₁ ∈ U := (mem_normalizer_iff.mp (hUT hwT) u).mp hu
    have hx_eq : x = y * u₁ * w := by rw [← hsu, hs_eq, hu₁def]; group
    obtain ⟨W, hWT, hAW, hWcard, hWc, hWinv, hWsq, hWiff⟩ :=
      h.exists_W_of_card_sylow hS2 hwT hw2 hwS
    rcases hsign w hwT hw2 hwS with hneg | hpos
    · exact (h.pushUp_false_of_card_le_neg hS2 hUc hUab hUA hUT hTUeq hT₁Ueq hPN hWT hAW hWcard
        hwT hWiff hneg hu₁ hy hx_eq hxP hTle).elim
    ·
      exfalso
      have hyW : y ∈ W := by
        have hc : w * y * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
        have hu₁' : w * u₁ * w⁻¹ ∈ U := (mem_normalizer_iff.mp (hUT hwT) u₁).mp hu₁
        have hww : w * w = 1 := by rw [← sq, hw2]
        have h1 : u₁ * (w * y * w⁻¹) = (w * y * w⁻¹) * u₁ := (hUc _ hc u₁ hu₁).symm
        have hxx : x * x = (y * (w * y * w⁻¹)) * (u₁ * (w * u₁ * w⁻¹)) := by
          rw [hx_eq]
          calc y * u₁ * w * (y * u₁ * w) =
              y * (u₁ * (w * y * w⁻¹)) * (w * u₁ * w⁻¹) * (w * w) := by group
            _ = y * ((w * y * w⁻¹) * u₁) * (w * u₁ * w⁻¹) * (w * w) := by rw [h1]
            _ = (y * (w * y * w⁻¹)) * (u₁ * (w * u₁ * w⁻¹)) := by rw [hww]; group
        have hx1 : x * x = 1 := by rw [← sq]; exact hx2
        have hyc : y * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) := by
          have e : y * (w * y * w⁻¹) = (u₁ * (w * u₁ * w⁻¹))⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← hxx, hx1]
          apply hTU _ (hT₁T (mul_mem hy hc))
          rw [e]
          exact inv_mem (mul_mem hu₁ hu₁')
        refine (hWiff y hy).mp ?_
        rw [show y⁻¹ * (w * y * w⁻¹) = (y ^ 2)⁻¹ * (y * (w * y * w⁻¹)) by group]
        exact mul_mem (inv_mem (hsq y hy)) hyc
      have hcent : ∀ u ∈ U, ∃ yh ∈ W, x * (yh * u) = (yh * u) * x := by
        intro u' hu'
        obtain ⟨yh, hyh, hyh2⟩ := hWsq _ (hpos u' hu')
        refine ⟨yh, hyh, ?_⟩
        rw [hx_eq]
        exact ncyc_conj_of_sign_pos hUc hUab hWT hWc hyW hu₁ hu' hyh (hWinv yh hyh) hyh2
      obtain ⟨y₁, hy₁, hc₁⟩ := hcent a ha
      obtain ⟨y₂, hy₂, hc₂⟩ := hcent a' ha'
      refine hZ8 (y₁ * a) (mul_mem (mem_sup_left (hT₁T (hWT hy₁))) (mem_sup_right ha))
        (y₂ * a') (mul_mem (mem_sup_left (hT₁T (hWT hy₂))) (mem_sup_right ha')) hc₁ hc₂
        fun k => ?_
      rw [h.pow_four_of_mem_mul hS2 hUc (hWT hy₁) (hWT hy₂) ha ha' k,
        h.pow_four_of_mem_mul hS2 hUc (hWT hy₂) (hWT hy₁) ha' ha k]
      exact hab k


theorem pushUp_exists_mul_t_of_conj_normalizer
    (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y)
    (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hUA : szA₁ (szT₁ L T) ≤ U) (hUt : ∀ u ∈ U, t * u * t⁻¹ = u → u ∈ szA₁ (szT₁ L T))
    (hUT : T ≤ normalizer (U : Set G))
    (hU8 : ∃ a ∈ U, ∃ b ∈ U, ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1)
    (hsign : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
      (∀ u ∈ U, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∨
        ∀ u ∈ U, u⁻¹ * (w * u * w⁻¹) ∈ szA₁ (szT₁ L T))
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) (hP2 : IsPGroup 2 (T ⊔ U : Subgroup G))
    {g : G} (hg : g ∈ normalizer ((T ⊔ U : Subgroup G) : Set G)) :
    (∃ y ∈ szT₁ L T, ∃ u ∈ U, g⁻¹ * t * g = y * u * t) ∧
      ((∀ u ∈ U, t * u * t⁻¹ = u⁻¹) → ∃ u ∈ U, g⁻¹ * t * g = u * t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hinvA, -, -⟩ := h.facts_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hA₁T : szA₁ (szT₁ L T) ≤ T := (szA₁_le _).trans hT₁T
  have hTU : ∀ x ∈ T, x ∈ U → x ∈ szA₁ (szT₁ L T) := by
    intro x hxT hxU
    refine hUt x hxU ?_
    rw [← mem_centralizer_singleton_iff.mp (h.le hxT), mul_inv_cancel_right]
  have hTUeq : T ⊓ U = szA₁ (szT₁ L T) :=
    le_antisymm (fun z hz => hTU z (mem_inf.mp hz).1 (mem_inf.mp hz).2) (le_inf hA₁T hUA)
  have hT₁Ueq : szT₁ L T ⊓ U = szA₁ (szT₁ L T) :=
    le_antisymm (fun z hz => hTU z (hT₁T (mem_inf.mp hz).1) (mem_inf.mp hz).2)
      (le_inf (szA₁_le _) hUA)
  have hPN : T ⊔ U ≤ normalizer (U : Set G) := sup_le hUT Subgroup.le_normalizer
  have hgP : g⁻¹ * t * g ∈ T ⊔ U := (mem_normalizer_iff''.mp hg t).mp (mem_sup_left htT)
  have hTle : Nat.card T ≤
      Nat.card ((T ⊔ U) ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G) := by
    have hle : T.map (MulAut.conj g⁻¹).toMonoidHom ≤
        (T ⊔ U) ⊓ centralizer ({g⁻¹ * t * g} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine mem_inf.mpr ⟨(mem_normalizer_iff''.mp hg y).mp (mem_sup_left hy), ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hyt := mem_centralizer_singleton_iff.mp (h.le hy)
      calc g⁻¹ * y * g * (g⁻¹ * t * g) = g⁻¹ * (y * t) * g := by group
        _ = g⁻¹ * (t * y) * g := by rw [hyt]
        _ = g⁻¹ * t * g * (g⁻¹ * y * g) := by group
    calc Nat.card T = Nat.card (T.map (MulAut.conj g⁻¹).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj _).injective).symm
      _ ≤ _ := card_le_of_le hle
  obtain ⟨y, hy, u, hu, hx⟩ := h.pushUp_exists_mul_t_of_card_le hS2 hUc hUab hUA hUT hU8 hsign hv
    hTU hTUeq hT₁Ueq hP2 hPN hgP hTle
  refine ⟨⟨y, hy, u, hu, hx⟩, fun hinv => ⟨y * u, mul_mem (hUA ?_) hu, by rw [hx]⟩⟩
  refine hinvA y hy ?_
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (h.le (hT₁T hy))
  have htu : t * u = u⁻¹ * t := by
    rw [← hinv u hu]; group
  have hyu : y * u = u * y := hUc y hy u hu
  have hx2 : (g⁻¹ * t * g) ^ 2 = 1 := by
    rw [sq, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ← sq, h.sq_eq_one]
    group
  rw [hx] at hx2
  have htt : t * t = 1 := by rw [← sq]; exact h.sq_eq_one
  have key : (y * u * t) ^ 2 = y ^ 2 := by
    calc (y * u * t) ^ 2 = y * u * (t * y) * u * t := by rw [sq]; group
      _ = y * u * (y * t) * u * t := by rw [hyt]
      _ = y * (u * y) * (t * u) * t := by group
      _ = y * (y * u) * (u⁻¹ * t) * t := by rw [← hyu, htu]
      _ = y * y * (t * t) := by group
      _ = y ^ 2 := by rw [htt, mul_one, sq]
  rw [key] at hx2
  exact hx2

theorem pushUp_pow_four_ne_one_of_outer (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {y : G} (hy : y ∈ szT₁ L T)
    (hyw : (y * w) ^ 2 ≠ 1) : (y * w) ^ 4 ≠ 1 := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, hsq, hinvA, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W, -, -, -, -, hWinv, -, hWiff⟩ := h.exists_W_of_card_sylow hS2 hwT hw2 hwS
  set a := w * y * w⁻¹ with ha
  have haT : a ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
  have hww : w * w = 1 := by rw [← sq, hw2]
  set c := y⁻¹ * a with hc
  have hcT : c ∈ szT₁ L T := mul_mem (inv_mem hy) haT
  have h2 : (y * w) ^ 2 = y * a := by
    calc (y * w) ^ 2 = y * (w * y * w⁻¹) * (w * w) := by rw [sq]; group
      _ = y * a := by rw [hww, mul_one]
  have hyW : y ∉ W := fun hyW => hyw (by rw [h2, ha, hWinv y hyW, mul_inv_cancel])
  have hcA : c ∉ szA₁ (szT₁ L T) := fun hcA => hyW ((hWiff y hy).mp hcA)
  have hwc : w * c * w⁻¹ = a⁻¹ * y := by
    rw [hc, ha]
    calc w * (y⁻¹ * (w * y * w⁻¹)) * w⁻¹ =
        (w * y * w⁻¹)⁻¹ * ((w * w) * y * (w * w)⁻¹) := by group
      _ = (w * y * w⁻¹)⁻¹ * y := by rw [hww]; group
  have hcW : c ∈ W := by
    refine (hWiff c hcT).mp ?_
    rw [hwc, show c⁻¹ * (a⁻¹ * y) = (a⁻¹ * y) ^ 2 by rw [hc, sq]; group]
    exact hsq _ (mul_mem (inv_mem haT) hy)
  have hy2 : y ^ 2 ∈ szA₁ (szT₁ L T) := hsq y hy
  have hcomm : Commute (y ^ 2) c := (mem_centralizer_iff.mp (mem_szA₁.mp hy2).2 c hcT).symm
  have hya : y * a = y ^ 2 * c := by rw [hc, sq]; group
  have h4 : (y * w) ^ 4 = c ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, hya, hcomm.mul_pow, hA₁sq _ hy2, one_mul]
  rw [h4]
  intro hc2
  exact hcA (hinvA c hcT hc2)

theorem pushUp_mem_normalizer_szT₁_of_mem_normalizer
    (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {g : G}
    (hg : g ∈ normalizer ((szT₁ L T ⊔ zpowers w : Subgroup G) : Set G)) :
    g ∈ normalizer (szT₁ L T : Set G) := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, -, hsq, hinvA, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  have hzN : zpowers w ≤ normalizer (szT₁ L T : Set G) := zpowers_le.mpr (hTN₁ hwT)
  have hy4 : ∀ y ∈ szT₁ L T, y ^ 4 = 1 := fun y hy => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; exact hA₁sq _ (hsq y hy)
  have key : ∀ g' ∈ normalizer ((szT₁ L T ⊔ zpowers w : Subgroup G) : Set G),
      ∀ y ∈ szT₁ L T, y ^ 2 ≠ 1 → g' * y * g'⁻¹ ∈ szT₁ L T := by
    intro g' hg' y hy hy2
    have hx : g' * y * g'⁻¹ ∈ zpowers w ⊔ szT₁ L T := by
      rw [sup_comm]; exact (mem_normalizer_iff.mp hg' y).mp (mem_sup_left hy)
    obtain ⟨a, ha, b, hb, hab⟩ := ncyc_exists_mul_of_mem_sup hzN hx
    have hx4 : (g' * y * g'⁻¹) ^ 4 = 1 := by rw [conj_pow, hy4 y hy]; group
    have hx2 : (g' * y * g'⁻¹) ^ 2 ≠ 1 := by
      rw [conj_pow]
      intro h1
      apply hy2
      have := congrArg (fun z => g'⁻¹ * z * g') h1
      simpa [mul_assoc] using this
    rcases mem_zpowers_involution_eq_one_or_eq hw2 ha with ha1 | ha1
    · rw [← hab, ha1, one_mul]; exact hb
    · exfalso
      have hb' : w * b * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) b).mp hb
      have e : g' * y * g'⁻¹ = (w * b * w⁻¹) * w := by rw [← hab, ha1]; group
      rw [e] at hx4 hx2
      exact h.pushUp_pow_four_ne_one_of_outer hS2 hwT hw2 hwS hb' hx2 hx4
  obtain ⟨z, hzT, hzA⟩ : ∃ z ∈ szT₁ L T, z ∉ szA₁ (szT₁ L T) := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card (szT₁ L T) ≤ Nat.card (szA₁ (szT₁ L T)) := card_le_of_le hcon
    rw [hT₁card, hA₁card] at hle
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
    have h5 := Nat.pow_lt_pow_right (show 1 < 2 ^ f by omega) (show 1 < 3 by norm_num)
    rw [pow_one] at h5
    omega
  have hz2 : z ^ 2 ≠ 1 := fun h1 => hzA (hinvA z hzT h1)
  have key' : ∀ g' ∈ normalizer ((szT₁ L T ⊔ zpowers w : Subgroup G) : Set G),
      ∀ y ∈ szT₁ L T, g' * y * g'⁻¹ ∈ szT₁ L T := by
    intro g' hg' y hy
    by_cases hy2 : y ^ 2 = 1
    · have hyz : (y * z) ^ 2 ≠ 1 := by
        intro h1
        apply hzA
        have hyA := hinvA y hy hy2
        have := hinvA (y * z) (mul_mem hy hzT) h1
        rw [show z = y⁻¹ * (y * z) by group]
        exact mul_mem (inv_mem hyA) this
      have e : g' * y * g'⁻¹ = (g' * (y * z) * g'⁻¹) * (g' * z * g'⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem (key g' hg' _ (mul_mem hy hzT) hyz) (inv_mem (key g' hg' z hzT hz2))
    · exact key g' hg' y hy hy2
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => ?_
  have := key' g⁻¹ (inv_mem hg) y hy
  rwa [inv_inv] at this

end U3Start

end CFSG.SeitzReduction.RankOne
