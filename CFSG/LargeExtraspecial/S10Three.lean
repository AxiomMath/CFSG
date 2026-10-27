module

public import CFSG.LargeExtraspecial.S10ThreeB
public import CFSG.LargeExtraspecial.S10ThreeA
public import CFSG.LargeExtraspecial.S10TwoE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Hyp10.card_Lbar_eq (X : Hyp10 S g t) :
    Nat.card (S.Lbar g) = 4 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  rw [card_Lbar_eq_mul X.haQ X.ht, X.card_LmodN]

theorem card_hyperplane (X : Hyp10 S g t) {L₀ : Subgroup S.O} (hL₀ : L₀ ≤ S.Lbar g)
    (hidx : L₀.relIndex (S.Lbar g) = 2) :
    Nat.card L₀ = 2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  have h1 := Subgroup.relIndex_mul_card L₀ (S.Lbar g)
  rw [hidx, inf_of_le_left hL₀, X.card_Lbar_eq] at h1
  omega

theorem Abar_le_of_comm (X : Hyp10 S g t) (F : Frame X) {h : Rbar S g t} (hs : (F.π h).2 = 1)
    (hs3 : F.π h ^ 3 = 1) (hs1 : F.π h ≠ 1) {L₀ : Subgroup S.O} (hL₀ : L₀ ≤ S.Lbar g)
    (hidx : L₀.relIndex (S.Lbar g) = 2) (hc : ∀ l ∈ L₀, l * h = h * l) :
    S.Lbar g ⊓ Nbar S g t ≤ L₀ := by
  have hL₀R : L₀ ≤ Rbar S g t := hL₀.trans (Lbar_le_Rbar X.ht)
  set ψ : L₀ →* Gm := F.π.comp (Subgroup.inclusion hL₀R) with hψ
  have hrange : ψ.range ≤ zpowers τ₂ := by
    rintro _ ⟨l, rfl⟩
    have hst := F.π_mem_stabA (hL₀ l.2)
    have hcomm : F.π ⟨l, hL₀R l.2⟩ * F.π h = F.π h * F.π ⟨l, hL₀R l.2⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc l l.2)
    rcases stab_comm_Γ₁ _ hs hs3 hs1 _ hst hcomm with h1 | h2
    · change F.π ⟨l, hL₀R l.2⟩ ∈ zpowers τ₂
      rw [h1]; exact one_mem _
    · change F.π ⟨l, hL₀R l.2⟩ ∈ zpowers τ₂
      rw [h2]; exact mem_zpowers τ₂
  have hker : Nat.card ψ.ker = Nat.card (L₀ ⊓ Nbar S g t : Subgroup S.O) := by
    refine Nat.card_congr ?_
    refine (Equiv.subtypeEquivRight (q := fun l : L₀ => (l : S.O) ∈ Nbar S g t)
      fun l => ?_).trans ?_
    · rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, F.ker]
      rfl
    · exact
        { toFun := fun l => ⟨l, l.1.2, l.2⟩
          invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
          left_inv := fun l => rfl
          right_inv := fun y => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker,
    card_hyperplane X hL₀ hidx] at h1
  have h2 := Subgroup.card_le_of_le hrange
  rw [Nat.card_zpowers, orderOf_τ₂] at h2
  have hle : L₀ ⊓ Nbar S g t ≤ S.Lbar g ⊓ Nbar S g t := inf_le_inf_right _ hL₀
  have h3 : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) ≤
      Nat.card (L₀ ⊓ Nbar S g t : Subgroup S.O) := by
    have hpos : 0 < Nat.card (L₀ ⊓ Nbar S g t : Subgroup S.O) := Nat.card_pos
    nlinarith
  have heq := Subgroup.eq_of_le_of_card_ge hle h3
  rw [← heq]
  exact inf_le_left

theorem exists_mem_hyperplane_not_mem_Nbar (X : Hyp10 S g t) {L₀ : Subgroup S.O}
    (hL₀ : L₀ ≤ S.Lbar g) (hidx : L₀.relIndex (S.Lbar g) = 2) :
    ∃ l ∈ L₀, l ∉ Nbar S g t := by
  by_contra hcon
  push Not at hcon
  have hle : L₀ ≤ S.Lbar g ⊓ Nbar S g t := fun l hl => ⟨hL₀ hl, hcon l hl⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [card_hyperplane X hL₀ hidx] at h1
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := Nat.card_pos
  omega

theorem eq_one_of_mem_Nbar_of_cube (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {n : S.O}
    (hn : n ∈ Nbar S g t) (h3 : n ^ 3 = 1) : n = 1 := by
  obtain ⟨k, hk⟩ := (X.isPGroup_Nbar hCE) ⟨n, hn⟩
  have hnk : n ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf n ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hnk) (orderOf_dvd_of_pow_eq_one h3)
  rw [(Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact h1

theorem le_commutator_of_Γ₂ (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb) (F : Frame X) (hFY : (D.piY F).range = Γ₂)
    {H : Subgroup S.O} (hHR : H ≤ Rbar S g t) (hodd : Odd (Nat.card H))
    (hπ : ∀ h (hh : h ∈ H), (F.π ⟨h, hHR hh⟩).1 = 1) : H ≤ ⁅Yb, Yb⁆ := by
  have hNX := D.Nbar_le hCE X
  intro h hh
  obtain ⟨y, hy⟩ : F.π ⟨h, hHR hh⟩ ∈ (D.piY F).range := hFY ▸ mem_Γ₂.mpr (hπ h hh)
  rw [DirDec.piY_apply] at hy
  have hyR := D.le_Rbar_right y.2
  have hc3 := cube_π_of_odd F hodd hh (hHR hh)
  have hy3 : (y : S.O) ^ 3 = 1 := by
    have h3 : F.π ⟨(y : S.O) ^ 3, pow_mem hyR 3⟩ = 1 := by
      have e : (⟨(y : S.O) ^ 3, pow_mem hyR 3⟩ : Rbar S g t) = ⟨y, hyR⟩ ^ 3 :=
        Subtype.ext (by simp)
      rw [e, map_pow, hy, hc3]
    exact D.eq_one_of_mem_Nbar hCE X (pow_mem y.2 3) ((F.ker _).mp h3)
  have hnN : (y : S.O)⁻¹ * h ∈ Nbar S g t := by
    have e : (⟨(y : S.O)⁻¹ * h, mul_mem (inv_mem hyR) (hHR hh)⟩ : Rbar S g t) =
        (⟨y, hyR⟩ : Rbar S g t)⁻¹ * ⟨h, hHR hh⟩ := Subtype.ext (by simp)
    refine (F.ker ⟨(y : S.O)⁻¹ * h, mul_mem (inv_mem hyR) (hHR hh)⟩).mp ?_
    rw [e, map_mul, map_inv, hy, inv_mul_cancel]
  have hny : Commute ((y : S.O)⁻¹ * h) (y : S.O) := D.comm _ (hNX hnN) _ y.2
  have hh3 : h ^ 3 = ((y : S.O)⁻¹ * h) ^ 3 := by
    have e : h = (y : S.O) * ((y : S.O)⁻¹ * h) := by group
    conv_lhs => rw [e]
    rw [(hny.symm).mul_pow, hy3, one_mul]
  have hn3 : ((y : S.O)⁻¹ * h) ^ 3 = 1 := by
    rw [← hh3]
    exact eq_one_of_mem_Nbar_of_odd hCE X hodd (pow_mem hh 3) (hh3 ▸ pow_mem hnN 3)
  have hn1 := eq_one_of_mem_Nbar_of_cube hCE X hnN hn3
  have hhy : h = (y : S.O) := by
    have e : h = (y : S.O) * ((y : S.O)⁻¹ * h) := by group
    rw [e, hn1, mul_one]
  rw [hhy, D.mem_commutator_iff]
  exact ⟨y.2, hy3⟩

theorem false_of_Γ₁ (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb) (F : Frame X) (hFY : (D.piY F).range = Γ₂)
    {h₁ : Rbar S g t} (hs : (F.π h₁).2 = 1) (hs3 : F.π h₁ ^ 3 = 1) (hs1 : F.π h₁ ≠ 1)
    {L₀ : Subgroup S.O} (hL₀ : L₀ ≤ S.Lbar g) (hidx : L₀.relIndex (S.Lbar g) = 2)
    (hc : ∀ l ∈ L₀, l * h₁ = h₁ * l) : False := by
  have hNX := D.Nbar_le hCE X
  have hAL₀ := Abar_le_of_comm X F hs hs3 hs1 hL₀ hidx hc
  obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.commutator_ne_bot
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hdY := ((D.mem_commutator_iff).mp hdY').1
  have hd3 := ((D.mem_commutator_iff).mp hdY').2
  have hdR := D.le_Rbar_right hdY
  have hπd1 : (F.π ⟨d, hdR⟩).1 = 1 := by
    have : F.π ⟨d, hdR⟩ ∈ Γ₂ := hFY ▸ ⟨⟨d, hdY⟩, rfl⟩
    exact mem_Γ₂.mp this
  have hπd3 : F.π ⟨d, hdR⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdR⟩ : Rbar S g t) ^ 3 = 1 := Subtype.ext hd3
    rw [this, map_one]
  have hπdne : F.π ⟨d, hdR⟩ ≠ 1 := fun h => hd1 (by
    have := D.piY_injective hCE F (a₁ := ⟨d, hdY⟩) (a₂ := 1)
      (by rw [DirDec.piY_apply, map_one]; exact h)
    exact congrArg Subtype.val this)
  obtain ⟨a, -, b, -, hab⟩ := exists_pf_Γ₁Γ₂ _ _ hs hs3 hs1 hπd1 hπd3 hπdne
  refine false_of_Abar_comm hCE X F (k := h₁ ^ a * ⟨d, hdR⟩ ^ b) ?_ fun z hz => ?_
  · rw [map_mul, map_pow, map_pow]
    exact hab
  · have hz1 : z * (h₁ : S.O) = h₁ * z := hc z (hAL₀ hz)
    have hz2 : z * d = d * z := D.comm z (hNX hz.2) d hdY
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    exact ((Commute.pow_right hz1 a).mul_right (Commute.pow_right hz2 b))

theorem timmesfeld_10_3_beta (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb) {H : Subgroup S.O} (hHR : H ≤ Rbar S g t)
    (hodd : Odd (Nat.card H)) (hH1 : H ≠ ⊥) {L₀ : Subgroup S.O} (hL₀ : L₀ ≤ S.Lbar g)
    (hidx : L₀.relIndex (S.Lbar g) = 2) (hc : ∀ h ∈ H, ∀ l ∈ L₀, h * l = l * h) :
    H = ⁅Yb, Yb⁆ := by
  obtain ⟨F, hFY, -⟩ := D.exists_frame hCE X
  obtain ⟨l, hlL₀, hlN⟩ := exists_mem_hyperplane_not_mem_Nbar X hL₀ hidx
  have hlR := Lbar_le_Rbar X.ht (hL₀ hlL₀)
  have hst := F.π_mem_stabA (hL₀ hlL₀)
  rw [mem_stabA, act_E00_iff] at hst
  have hcomm : ∀ h (hh : h ∈ H),
      F.π ⟨h, hHR hh⟩ * F.π ⟨l, hlR⟩ = F.π ⟨l, hlR⟩ * F.π ⟨h, hHR hh⟩ := fun h hh => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc h hh l hlL₀)
  have hcube : ∀ h (hh : h ∈ H), F.π ⟨h, hHR hh⟩ ^ 3 = 1 := fun h hh =>
    cube_π_of_odd F hodd hh (hHR hh)
  obtain ⟨⟨h₁, hh₁H⟩, hh₁'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hH1
  have hπh₁ : F.π ⟨(h₁ : S.O), hHR hh₁H⟩ ≠ 1 := fun h =>
    hh₁' (Subtype.ext (eq_one_of_mem_Nbar_of_odd hCE X hodd hh₁H ((F.ker _).mp h)))
  rcases hst with h1 | h1 | h2 | hd
  · exact absurd ((F.ker _).mp h1) hlN
  ·
    have hle := le_commutator_of_Γ₂ hCE X D F hFY hHR hodd fun h hh =>
      comm_τ₁ _ (hcube h hh) (by rw [← h1]; exact hcomm h hh)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [D.card_commutator] at hdvd
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [D.card_commutator]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq H h) hH1
    · exact h.ge
  ·
    exfalso
    refine false_of_Γ₁ hCE X D F hFY (h₁ := ⟨h₁, hHR hh₁H⟩)
      (comm_τ₂ _ (hcube _ hh₁H) (by rw [← h2]; exact hcomm _ hh₁H)) (hcube _ hh₁H) hπh₁ hL₀ hidx
      fun l' hl' => ?_
    exact (hc h₁ hh₁H l' hl').symm
  ·
    exfalso
    exact hπh₁ (comm_τ₁τ₂ _ (hcube _ hh₁H) (by rw [← hd]; exact hcomm _ hh₁H))

theorem timmesfeld_10_3_hyperplane (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb) :
    (S.Lbar g ⊓ Xb).relIndex (S.Lbar g) = 2 ∧
      ∀ w ∈ ⁅Yb, Yb⁆, ∀ l ∈ S.Lbar g ⊓ Xb, w * l = l * w := by
  obtain ⟨F, hFY, hFX⟩ := D.exists_frame hCE X
  refine ⟨?_, fun w hw l hl => (D.comm l hl.2 w ((D.mem_commutator_iff).mp hw).1).symm⟩
  have hNX := D.Nbar_le hCE X
  obtain ⟨l₁, hl₁, hπl₁⟩ := F.exists_Lbar_of_stab
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inl rfl))
  obtain ⟨l₂, hl₂, hπl₂⟩ := F.exists_Lbar_of_stab
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inr (Or.inl rfl)))
  have hl₁X : l₁ ∈ Xb := by
    rw [hFX]
    exact (F.mem_pre).mpr ⟨_, by rw [hπl₁]; exact τ₁_mem_Γ₁⟩
  have hl₂X : l₂ ∉ Xb := by
    rw [hFX]
    intro h
    obtain ⟨hR, hπ⟩ := (F.mem_pre).mp h
    have : F.π ⟨l₂, hR⟩ = τ₂ := hπl₂
    rw [this, mem_Γ₁] at hπ
    exact τ₂_ne_one (Prod.ext (by decide +kernel) hπ)
  have hlt : S.Lbar g ⊓ Xb < S.Lbar g :=
    lt_of_le_of_ne inf_le_left fun h => hl₂X (h ▸ hl₂ |>.2)
  have h1 := Subgroup.relIndex_mul_card (S.Lbar g ⊓ Xb) (S.Lbar g)
  rw [inf_of_le_left (inf_le_left : S.Lbar g ⊓ Xb ≤ S.Lbar g), X.card_Lbar_eq] at h1
  have hord : orderOf l₁ = 2 := by
    refine orderOf_eq_prime (by rw [_root_.sq]; exact S4.mul_self_of_mem_Lbar S X.haQ hl₁) ?_
    rintro rfl
    have : F.π ⟨1, Lbar_le_Rbar X.ht hl₁⟩ = 1 := map_one F.π
    rw [hπl₁] at this
    exact τ₁_ne_one this
  have hnorm : zpowers l₁ ≤ normalizer (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro x
    have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → l₁ * x = x * l₁ := fun {x} hx =>
      S4.Lbar_comm S X.haQ hl₁ hx
    constructor
    · intro hx
      rwa [hcomm hx.1, mul_inv_cancel_right]
    · intro hx
      have e : x = l₁⁻¹ * (l₁ * x * l₁⁻¹) * l₁ := by group
      have e2 : l₁⁻¹ * (l₁ * x * l₁⁻¹) * l₁ = l₁ * x * l₁⁻¹ := by
        rw [mul_assoc, ← hcomm hx.1, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e, e2]
      exact hx
  have h2 := card_sup_mul_card_inf hnorm
  have hbot : zpowers l₁ ⊓ (S.Lbar g ⊓ Nbar S g t) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases mem_zpowers_of_orderOf_two hord hx.1 with h0 | h0
    · rw [h0]; exact one_mem _
    · exfalso
      have hxN := hx.2.2
      rw [h0] at hxN
      have := (F.ker ⟨l₁, Lbar_le_Rbar X.ht hl₁⟩).mpr hxN
      rw [hπl₁] at this
      exact τ₁_ne_one this
  rw [hbot, card_bot, mul_one, Nat.card_zpowers, hord] at h2
  have hle : zpowers l₁ ⊔ (S.Lbar g ⊓ Nbar S g t) ≤ S.Lbar g ⊓ Xb :=
    sup_le ((zpowers_le).mpr ⟨hl₁, hl₁X⟩) (fun x hx => ⟨hx.1, hNX hx.2⟩)
  have h3 := Subgroup.card_le_of_le hle
  have hne : (S.Lbar g ⊓ Xb).relIndex (S.Lbar g) ≠ 1 := by
    intro h
    exact hlt.ne (le_antisymm inf_le_left (Subgroup.relIndex_eq_one.mp h))
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := Nat.card_pos
  have h4 : (S.Lbar g ⊓ Xb).relIndex (S.Lbar g) ≤ 2 := by nlinarith
  have h0 : (S.Lbar g ⊓ Xb).relIndex (S.Lbar g) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    omega
  omega

end CFSG.LargeExtraspecial.S10
