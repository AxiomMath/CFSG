module

public import CFSG.LargeExtraspecial.S10TwoD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem conj_τ₂_of_Γ₁ {s : Gm} (hs : s.2 = 1) : s * τ₂ * s⁻¹ = τ₂ := by
  refine Prod.ext ?_ ?_ <;> simp [τ₂, hs]

theorem orderOf_τ₂ : orderOf τ₂ = 2 :=
  orderOf_eq_prime (by rw [_root_.sq]; exact τ₂_sq) τ₂_ne_one

theorem mem_zpowers_of_orderOf_two {X : Type*} [Group X] {w : X} (hw : orderOf w = 2) {γ : X}
    (h : γ ∈ zpowers w) : γ = 1 ∨ γ = w := by
  have h2 : Nat.card (zpowers w) = 2 := by rw [Nat.card_zpowers, hw]
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : zpowers w)).mp h2
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  by_cases h1 : γ = 1
  · exact Or.inl h1
  · right
    have a1 := huniq ⟨γ, h⟩ fun h' => h1 (congrArg Subtype.val h')
    have a2 := huniq ⟨w, mem_zpowers w⟩ fun h' => hw1 (congrArg Subtype.val h')
    exact congrArg Subtype.val (a1.trans a2.symm)

theorem mem_zpowers_τ₂ {γ : Gm} (h : γ ∈ zpowers τ₂) : γ = 1 ∨ γ = τ₂ :=
  mem_zpowers_of_orderOf_two orderOf_τ₂ h

theorem exists_Lbar_inf_π_eq_τ₂ (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {k : S.M} (hk : S.ρ k ∈ Rbar S g t) (hs : (F.π ⟨S.ρ k, hk⟩).2 = 1)
    (hinf : (S.Lbar g ⊓ Nbar S g t) ⊓ S.Lbar ((k : G) * g) = zpowers t) :
    ∃ y, ∃ hy : y ∈ S.Lbar g ⊓ S.Lbar ((k : G) * g),
      F.π ⟨y, Lbar_le_Rbar X.ht hy.1⟩ = τ₂ := by
  obtain ⟨Y₂, hY₂⟩ : ∃ Y : Subgroup S.O, Y = F.pre (zpowers τ₂) := ⟨_, rfl⟩
  have hY₂card : Nat.card Y₂ = 2 * Nat.card (Nbar S g t) := by
    rw [hY₂, F.card_pre, Nat.card_zpowers, orderOf_τ₂]
  have h2N := two_mul_card_Nbar hCE X
  have ha4 : 4 ≤ Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    rw [X.card_Abar]
    have := X.five_le_width
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨l₀, hl₀, hπl₀⟩ := F.exists_Lbar_of_stab
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inr (Or.inl rfl)))
  have hl₀N : l₀ ∉ Nbar S g t := fun h => τ₂_ne_one (hπl₀.symm.trans ((F.ker _).mpr h))
  have hl₀Y : l₀ ∈ Y₂ := by
    rw [hY₂]
    exact (F.mem_pre).mpr ⟨_, by rw [hπl₀]; exact mem_zpowers τ₂⟩
  have hNY : Nbar S g t ≤ Y₂ := by rw [hY₂]; exact F.Nbar_le_pre _
  obtain ⟨Lt, hLtd⟩ : ∃ L : Subgroup S.O, L = S.Lbar g ⊓ Y₂ := ⟨_, rfl⟩
  obtain ⟨Lt', hLtd'⟩ : ∃ L : Subgroup S.O, L = S.Lbar ((k : G) * g) ⊓ Y₂ := ⟨_, rfl⟩
  have hLt : 2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) ≤ Nat.card Lt := by
    have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → l₀ * x = x * l₀ := fun {x} hx =>
      S4.Lbar_comm S X.haQ hl₀ hx
    have hnorm : zpowers l₀ ≤ normalizer (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
      rw [zpowers_le, mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rwa [hcomm hx.1, mul_inv_cancel_right]
      · intro hx
        have e : x = l₀⁻¹ * (l₀ * x * l₀⁻¹) * l₀ := by group
        have e2 : l₀⁻¹ * (l₀ * x * l₀⁻¹) * l₀ = l₀ * x * l₀⁻¹ := by
          rw [mul_assoc, ← hcomm hx.1, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [e, e2]
        exact hx
    have h1 := card_sup_mul_card_inf hnorm
    have hord : orderOf l₀ = 2 := by
      refine orderOf_eq_prime (by rw [_root_.sq]; exact S4.mul_self_of_mem_Lbar S X.haQ hl₀) ?_
      rintro rfl
      exact hl₀N (one_mem _)
    have hbot : zpowers l₀ ⊓ (S.Lbar g ⊓ Nbar S g t) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases mem_zpowers_of_orderOf_two hord hx.1 with h0 | h0
      · rw [h0]; exact one_mem _
      · exact absurd (h0 ▸ hx.2.2) hl₀N
    rw [hbot, card_bot, mul_one, Nat.card_zpowers, hord] at h1
    have hle : zpowers l₀ ⊔ (S.Lbar g ⊓ Nbar S g t) ≤ Lt := by
      rw [hLtd]
      exact sup_le ((zpowers_le).mpr ⟨hl₀, hl₀Y⟩) (fun x hx => ⟨hx.1, hNY hx.2⟩)
    have := Subgroup.card_le_of_le hle
    omega
  have hLt' : Nat.card Lt ≤ Nat.card Lt' := by
    have hle : Lt.map (MulAut.conj (S.ρ k)).toMonoidHom ≤ Lt' := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hLtd] at hx
      rw [hLtd']
      refine ⟨conj_mem_Lbar_mul S k hx.1, ?_⟩
      rw [hY₂] at hx ⊢
      obtain ⟨hxR, hxπ⟩ := (F.mem_pre).mp hx.2
      obtain ⟨r, hrd⟩ : ∃ r : Rbar S g t, r = ⟨S.ρ k, hk⟩ * ⟨x, hxR⟩ * ⟨S.ρ k, hk⟩⁻¹ :=
        ⟨_, rfl⟩
      have hr : (MulAut.conj (S.ρ k)).toMonoidHom x = (r : S.O) := by
        rw [hrd]
        simp
      rw [hr]
      refine (F.mem_pre).mpr ⟨r.2, ?_⟩
      rw [Subtype.coe_eta, hrd, map_mul, map_mul, map_inv]
      rcases mem_zpowers_τ₂ hxπ with h1 | h1
      · have e : F.π ⟨S.ρ k, hk⟩ * F.π ⟨x, hxR⟩ * (F.π ⟨S.ρ k, hk⟩)⁻¹ = 1 :=
          (congrArg (fun z => F.π ⟨S.ρ k, hk⟩ * z * (F.π ⟨S.ρ k, hk⟩)⁻¹) h1).trans
            (by rw [mul_one, mul_inv_cancel])
        rw [e]
        exact one_mem _
      · have e : F.π ⟨S.ρ k, hk⟩ * F.π ⟨x, hxR⟩ * (F.π ⟨S.ρ k, hk⟩)⁻¹ = τ₂ :=
          (congrArg (fun z => F.π ⟨S.ρ k, hk⟩ * z * (F.π ⟨S.ρ k, hk⟩)⁻¹) h1).trans
            (conj_τ₂_of_Γ₁ hs)
        rw [e]
        exact mem_zpowers τ₂
    calc Nat.card Lt = Nat.card (Lt.map (MulAut.conj (S.ρ k)).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj (S.ρ k)).injective).symm
      _ ≤ Nat.card Lt' := Subgroup.card_le_of_le hle
  have hex : ∃ y ∈ Lt ⊓ Lt', y ∉ Nbar S g t := by
    by_contra hcon
    push Not at hcon
    have hsub : Lt ⊓ Lt' ≤ zpowers t := by
      rw [← hinf]
      intro y hy
      have hyN := hcon y hy
      rw [hLtd, hLtd'] at hy
      exact ⟨⟨hy.1.1, hyN⟩, hy.2.1⟩
    have hint2 : Nat.card (Lt' ⊓ Lt : Subgroup S.O) ≤ 2 := by
      rw [inf_comm]
      have := Subgroup.card_le_of_le hsub
      rwa [Nat.card_zpowers, X.orderOf_t] at this
    have hLtY : Lt ≤ Y₂ := by rw [hLtd]; exact inf_le_right
    have hLt'Y : Lt' ≤ Y₂ := by rw [hLtd']; exact inf_le_right
    have r1 := Subgroup.relIndex_mul_card Lt' Lt
    have r2 := Subgroup.relIndex_mul_card Lt' Y₂
    rw [inf_of_le_left hLt'Y, hY₂card] at r2
    have hne : Lt'.relIndex Y₂ ≠ 0 := by
      intro h0
      have hpos : 0 < Nat.card (Nbar S g t) := Nat.card_pos
      have : Lt'.relIndex Y₂ * Nat.card Lt' = 0 := by rw [h0, zero_mul]
      omega
    have r3 := Subgroup.relIndex_le_of_le_right hLtY hne
    have h5 : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * (2 * Lt'.relIndex Y₂) ≤
        Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
          Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
      calc Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * (2 * Lt'.relIndex Y₂) =
            2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * Lt'.relIndex Y₂ := by ring
        _ ≤ Nat.card Lt' * Lt'.relIndex Y₂ := Nat.mul_le_mul_right _ (hLt.trans hLt')
        _ = Lt'.relIndex Y₂ * Nat.card Lt' := mul_comm _ _
        _ = 2 * Nat.card (Nbar S g t) := r2
        _ = _ := h2N
    have h7 := Nat.le_of_mul_le_mul_left h5 (by omega)
    have h6 : 2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) ≤ 2 * Lt'.relIndex Y₂ := by
      calc 2 * Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) ≤ Nat.card Lt := hLt
        _ = Lt'.relIndex Lt * Nat.card (Lt' ⊓ Lt : Subgroup S.O) := r1.symm
        _ ≤ Lt'.relIndex Y₂ * 2 := Nat.mul_le_mul r3 hint2
        _ = 2 * Lt'.relIndex Y₂ := by ring
    omega
  obtain ⟨y, hy, hyN⟩ := hex
  rw [hLtd, hLtd', hY₂] at hy
  have hyL : y ∈ S.Lbar g := hy.1.1
  have hyLc : y ∈ S.Lbar ((k : G) * g) := hy.2.1
  obtain ⟨hyR, hyπ⟩ := (F.mem_pre).mp hy.1.2
  have hπ : F.π ⟨y, hyR⟩ = τ₂ :=
    (mem_zpowers_τ₂ hyπ).resolve_left fun h1 => hyN ((F.ker _).mp h1)
  exact ⟨y, ⟨hyL, hyLc⟩, hπ⟩

theorem comm_h_of_mem_inf (X : Hyp10 S g t) (F : Frame X) {x : S.O} (hxL : x ∈ S.Lbar g)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hk3 : (S.ρ k) ^ 3 = 1) (hs : (F.π ⟨S.ρ k, hk⟩).2 = 1)
    (hs3 : (F.π ⟨S.ρ k, hk⟩) ^ 3 = 1) {y : S.O} (hy : y ∈ S.Lbar g ⊓ S.Lbar ((k : G) * g))
    (hyN : ∀ n ∈ Nbar S g t, n * y = y * n) :
    S.ρ k * y = y * S.ρ k := by
  set h := S.ρ k with hh
  have hxR := Lbar_le_Rbar X.ht hxL
  have hn₀ : h * (x * h * x⁻¹) ∈ Nbar S g t := by
    obtain ⟨r, hrd⟩ : ∃ r : Rbar S g t, r = ⟨h, hk⟩ * (⟨x, hxR⟩ * ⟨h, hk⟩ * ⟨x, hxR⟩⁻¹) :=
      ⟨_, rfl⟩
    have hr : h * (x * h * x⁻¹) = (r : S.O) := by
      rw [hrd]
      simp
    rw [hr]
    refine (F.ker r).mp ?_
    rw [hrd, map_mul, map_mul, map_mul, map_inv, hπx, τ₁_inv _ hs hs3, mul_inv_cancel]
  set n₀ := h * (x * h * x⁻¹) with hn₀d
  have e1 : x * h * x⁻¹ = h⁻¹ * n₀ := by rw [hn₀d]; group
  have hxy : x * y = y * x := S4.Lbar_comm S X.haQ hxL hy.1
  have e2 : x * y * x⁻¹ = y := by rw [hxy, mul_inv_cancel_right]
  have hny := hyN n₀ hn₀
  have e3 : x * (h * y * h⁻¹) * x⁻¹ = h⁻¹ * y * h := by
    calc x * (h * y * h⁻¹) * x⁻¹ = (x * h * x⁻¹) * (x * y * x⁻¹) * (x * h * x⁻¹)⁻¹ := by group
      _ = (h⁻¹ * n₀) * y * (h⁻¹ * n₀)⁻¹ := by rw [e1, e2]
      _ = h⁻¹ * (n₀ * y) * n₀⁻¹ * h := by group
      _ = h⁻¹ * y * h := by rw [hny]; group
  have hv : h⁻¹ * y * h ∈ S.Lbar g := by
    have := (mem_Lbar_mul_iff S k g).mp hy.2
    rwa [← hh] at this
  have hxv : x * (h⁻¹ * y * h) = (h⁻¹ * y * h) * x := S4.Lbar_comm S X.haQ hxL hv
  have e4 : h * y * h⁻¹ = h⁻¹ * y * h := by
    calc h * y * h⁻¹ = x⁻¹ * (x * (h * y * h⁻¹) * x⁻¹) * x := by group
      _ = x⁻¹ * (h⁻¹ * y * h) * x := by rw [e3]
      _ = x⁻¹ * (x * (h⁻¹ * y * h)) := by rw [mul_assoc x⁻¹ _ x, ← hxv]
      _ = h⁻¹ * y * h := by group
  have e5 : (h * h) * y * (h * h)⁻¹ = y := by
    calc (h * h) * y * (h * h)⁻¹ = h * (h * y * h⁻¹) * h⁻¹ := by group
      _ = h * (h⁻¹ * y * h) * h⁻¹ := by rw [e4]
      _ = y := by group
  have hhh : h * h = h⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three']
    exact hk3
  rw [hhh, inv_inv] at e5
  calc h * y = h * (h⁻¹ * y * h) := by rw [e5]
    _ = y * h := by group

end CFSG.LargeExtraspecial.S10
