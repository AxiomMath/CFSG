module

public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic
public import CFSG.CGT.PushingUpLit.BHS.Prelim

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin.A1b CFSG.Open CFSG.LieType.BorelTits

variable {Γ : Type} [Group Γ]

@[expose] def lOne (A D : Subgroup Γ) (z : Γ) : Subgroup Γ := A ⊔ Subgroup.zpowers z ⊔ D

theorem le_lOne_left (A D : Subgroup Γ) (z : Γ) : A ≤ lOne A D z :=
  le_sup_of_le_left le_sup_left

theorem le_lOne_right (A D : Subgroup Γ) (z : Γ) : D ≤ lOne A D z := le_sup_right

theorem mem_lOne (A D : Subgroup Γ) (z : Γ) : z ∈ lOne A D z :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))

theorem lOne_le {A D Z : Subgroup Γ} {z : Γ} (hA : A ≤ Z) (hz : z ∈ Z) (hD : D ≤ Z) :
    lOne A D z ≤ Z :=
  sup_le (sup_le hA (Subgroup.zpowers_le.mpr hz)) hD

theorem lOne_unique_max [Finite Γ] {A D M₁ N : Subgroup Γ} (hAN : A ≤ N) (hDN : D ≤ N) {z : Γ}
    (hzmin : ∀ w ∈ N, w ∉ M₁ → Nat.card (lOne A D z) ≤ Nat.card (lOne A D w))
    (hzN : z ∈ N) {Z : Subgroup Γ} (hZK : Z ≤ lOne A D z) (hADZ : A ⊔ D ≤ Z)
    (hne : Z ≠ lOne A D z) : Z ≤ M₁ := by
  by_contra hZM
  obtain ⟨w, hwZ, hwM⟩ := IsConcreteLE.not_le_iff_exists.mp hZM
  have hKN : lOne A D z ≤ N := lOne_le hAN hzN hDN
  have hwN : w ∈ N := hKN (hZK hwZ)
  have h1 := hzmin w hwN hwM
  have h2 : lOne A D w ≤ Z :=
    lOne_le (le_sup_left.trans hADZ) hwZ (le_sup_right.trans hADZ)
  have h3 := Subgroup.card_le_of_le h2
  have h4 := Nine.card_lt_of_lt (lt_of_le_of_ne hZK hne)
  omega

theorem mem_of_conjSub_sup_le {X A D M₁ : Subgroup Γ} {F : Set (Subgroup Γ)} {x : Γ}
    (hFconj : ∀ Y ∈ F, ∀ y ∈ X, conjSub y Y ∈ F) (hM₁ : M₁ ∈ F)
    (hN₁ : ∀ y ∈ X, conjSub y M₁ = M₁ → y ∈ M₁) (huniq : ∀ Y ∈ F, A ⊔ D ≤ Y → Y = M₁)
    (hx : x ∈ X) (hxD : x ∈ Subgroup.normalizer (D : Set Γ)) (h : conjSub x A ⊔ D ≤ M₁) :
    x ∈ M₁ := by
  have h1 : A ⊔ D ≤ conjSub x⁻¹ M₁ := by
    have := conjSub_mono x⁻¹ h
    rwa [conjSub_sup, ← conjSub_mul, inv_mul_cancel, conjSub_one,
      conjSub_eq_of_mem_normalizer ((Subgroup.normalizer (D : Set Γ)).inv_mem hxD)] at this
  have h2 : conjSub x⁻¹ M₁ = M₁ := huniq _ (hFconj _ hM₁ x⁻¹ (X.inv_mem hx)) h1
  apply hN₁ x hx
  have := congrArg (conjSub x) h2
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
  exact this.symm

theorem lOne_eq_sup_conjSub [Finite Γ] {X A D M₁ N : Subgroup Γ} {F : Set (Subgroup Γ)} {z : Γ}
    (hFconj : ∀ Y ∈ F, ∀ y ∈ X, conjSub y Y ∈ F) (hM₁ : M₁ ∈ F)
    (hN₁ : ∀ y ∈ X, conjSub y M₁ = M₁ → y ∈ M₁) (huniq : ∀ Y ∈ F, A ⊔ D ≤ Y → Y = M₁)
    (hAN : A ≤ N) (hDN : D ≤ N) (hNX : N ≤ X) (hND : N ≤ Subgroup.normalizer (D : Set Γ))
    (hzmin : ∀ w ∈ N, w ∉ M₁ → Nat.card (lOne A D z) ≤ Nat.card (lOne A D w)) (hzN : z ∈ N)
    {x : Γ} (hx : x ∈ lOne A D z) (hxM : x ∉ M₁) : lOne A D z = A ⊔ conjSub x A ⊔ D := by
  have hxN : x ∈ N := lOne_le hAN hzN hDN hx
  by_contra hne
  have hZK : A ⊔ conjSub x A ⊔ D ≤ lOne A D z := by
    refine sup_le (sup_le (le_lOne_left A D z) ?_) (le_lOne_right A D z)
    rintro _ ⟨a, ha, rfl⟩
    exact (lOne A D z).mul_mem ((lOne A D z).mul_mem hx (le_lOne_left A D z ha))
      ((lOne A D z).inv_mem hx)
  have hADZ : A ⊔ D ≤ A ⊔ conjSub x A ⊔ D := sup_le_sup_right le_sup_left D
  have hle := lOne_unique_max hAN hDN hzmin hzN hZK hADZ (Ne.symm hne)
  have hcj : conjSub x A ⊔ D ≤ M₁ :=
    sup_le (le_sup_right.trans (le_sup_left.trans hle)) (le_sup_right.trans hle)
  exact hxM (mem_of_conjSub_sup_le hFconj hM₁ hN₁ huniq (hNX hxN) (hND hxN) hcj)

theorem l_core [Finite Γ] {X A D M₁ : Subgroup Γ} {F : Set (Subgroup Γ)}
    (hA2 : IsPGroup 2 A) (hAX : A ≤ X) (hD2 : IsPGroup 2 D) (hDX : D ≤ X)
    (hAD : A ≤ Subgroup.normalizer (D : Set Γ))
    (hFconj : ∀ Y ∈ F, ∀ y ∈ X, conjSub y Y ∈ F)
    (hFR : ∀ Y ∈ F, pCoreOf 2 X ≤ Y)
    (hF2 : ∀ P : Subgroup Γ, IsPGroup 2 P → P ≤ X → ∃ Y ∈ F, P ≤ Y)
    (hM₁ : M₁ ∈ F) (hN₁ : ∀ y ∈ X, conjSub y M₁ = M₁ → y ∈ M₁)
    (huniq : ∀ Y ∈ F, A ⊔ D ≤ Y → Y = M₁)
    (hNM : ¬ X ⊓ Subgroup.normalizer (D : Set Γ) ≤ M₁) :
    ∃ L : Subgroup Γ, pCoreOf 2 X ≤ L ∧ L ≤ X ∧ A ≤ L ∧
      (∃ L₀ : Subgroup Γ, L₀ < L ∧ A ⊔ pCoreOf 2 L ≤ L₀ ∧
        (∀ Z : Subgroup Γ, Z < L → A ⊔ pCoreOf 2 L ≤ Z → Z ≤ L₀) ∧ L₀ = L ⊓ M₁ ∧
        (∀ x ∈ L, x ∉ L₀ → L = A ⊔ conjSub x A ⊔ pCoreOf 2 L)) ∧
      (∀ Y ∈ F, ¬ L ≤ Y) := by
  classical
  set R := pCoreOf 2 X with hRdef
  set N : Subgroup Γ := X ⊓ Subgroup.normalizer (D : Set Γ) with hNdef
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 X
  have hRX : R ≤ X := pCoreOf_le 2 X
  have hXR : X ≤ Subgroup.normalizer (R : Set Γ) := le_normalizer_pCoreOf 2 X
  have hNX : N ≤ X := inf_le_left
  have hND : N ≤ Subgroup.normalizer (D : Set Γ) := inf_le_right
  have hAN : A ≤ N := le_inf hAX hAD
  have hDN : D ≤ N := le_inf hDX Subgroup.le_normalizer
  have hRM₁ : R ≤ M₁ := hFR M₁ hM₁
  obtain ⟨z, ⟨hzN, hzM⟩, hzmin'⟩ := Set.exists_min_image {w : Γ | w ∈ N ∧ w ∉ M₁}
    (fun w => Nat.card (lOne A D w)) (Set.toFinite _) (by
      obtain ⟨w, hw, hwM⟩ := IsConcreteLE.not_le_iff_exists.mp hNM
      exact ⟨w, hw, hwM⟩)
  have hzmin : ∀ w ∈ N, w ∉ M₁ → Nat.card (lOne A D z) ≤ Nat.card (lOne A D w) :=
    fun w hw hwM => hzmin' w ⟨hw, hwM⟩
  set K := lOne A D z with hK
  have hKN : K ≤ N := lOne_le hAN hzN hDN
  have hKX : K ≤ X := hKN.trans hNX
  have hADK : A ⊔ D ≤ K := sup_le (le_lOne_left A D z) (le_lOne_right A D z)
  have hAD2 : IsPGroup 2 (A ⊔ D : Subgroup Γ) := hA2.to_sup_of_normal_right' hD2 hAD
  have hKF : ∀ Y ∈ F, ¬ K ≤ Y := by
    intro Y hY hKY
    have := huniq Y hY (hADK.trans hKY)
    rw [this] at hKY
    exact hzM (hKY (mem_lOne A D z))
  have hKR : K ≤ Subgroup.normalizer (R : Set Γ) := hKX.trans hXR
  set L : Subgroup Γ := K ⊔ R with hL
  have hKL : K ≤ L := le_sup_left
  have hRL : R ≤ L := le_sup_right
  have hLX : L ≤ X := sup_le hKX hRX
  have hLR : L ≤ Subgroup.normalizer (R : Set Γ) := hLX.trans hXR
  have hALL : A ≤ L := (le_lOne_left A D z).trans hKL
  have hRO : R ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hRL hLR hR2
  have hDR2 : IsPGroup 2 (D ⊔ R : Subgroup Γ) :=
    hD2.to_sup_of_normal_right' hR2 (hDX.trans hXR)
  have hKDR : K ≤ Subgroup.normalizer ((D ⊔ R : Subgroup Γ) : Set Γ) := by
    intro k hk
    apply mem_normalizer_of_conjSub_eq
    rw [conjSub_sup, conjSub_eq_of_mem_normalizer (hND (hKN hk)),
      conjSub_eq_of_mem_normalizer (hKR hk)]
  have hLDR : L ≤ Subgroup.normalizer ((D ⊔ R : Subgroup Γ) : Set Γ) :=
    sup_le hKDR (le_sup_right.trans Subgroup.le_normalizer)
  have hDO : D ≤ pCoreOf 2 L :=
    le_sup_left.trans (le_pCoreOf_of_le_normalizer 2
      (sup_le ((le_lOne_right A D z).trans hKL) hRL) hLDR hDR2)
  have hOL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set Γ) := le_normalizer_pCoreOf 2 L
  have hiii : ∀ Y ∈ F, ¬ L ≤ Y := fun Y hY hLY => hKF Y hY (hKL.trans hLY)
  have hΛ : A ⊔ pCoreOf 2 L < L := by
    refine lt_of_le_of_ne (sup_le hALL hOL) ?_
    intro heq
    have h2 : IsPGroup 2 (A ⊔ pCoreOf 2 L : Subgroup Γ) :=
      hA2.to_sup_of_normal_right' (pCoreOf_isPGroup 2 L) (hALL.trans hLO)
    rw [heq] at h2
    obtain ⟨Y, hY, hle⟩ := hF2 L h2 hLX
    exact hiii Y hY hle
  have hclaim : ∀ Z : Subgroup Γ, Z < L → A ⊔ pCoreOf 2 L ≤ Z → Z ≤ M₁ := by
    intro Z hZL hΛZ z' hz'
    have hz'L : z' ∈ L := hZL.le hz'
    obtain ⟨k, hk, r, hr, rfl⟩ := (mem_sup_iff_of_le_normalizer hKR).1 hz'L
    have hrZ : r ∈ Z := hΛZ (Subgroup.mem_sup_right (hRO hr))
    have hkZ : k ∈ Z := by
      have := Z.mul_mem hz' (Z.inv_mem hrZ)
      simpa using this
    have hADZ : A ⊔ D ≤ Z ⊓ K :=
      le_inf (sup_le (le_sup_left.trans hΛZ) (hDO.trans (le_sup_right.trans hΛZ))) hADK
    have hne : Z ⊓ K ≠ K := by
      intro heq
      have hKZ : K ≤ Z := heq ▸ inf_le_left
      exact hZL.not_ge (sup_le hKZ (hRO.trans (le_sup_right.trans hΛZ)))
    have := lOne_unique_max hAN hDN hzmin hzN inf_le_right hADZ hne
    exact M₁.mul_mem (this ⟨hkZ, hk⟩) (hRM₁ hr)
  refine ⟨L, hRL, hLX, hALL, ⟨L ⊓ M₁, ?_, ?_, ?_, rfl, ?_⟩, hiii⟩
  · exact lt_of_le_of_ne inf_le_left fun h => hiii M₁ hM₁ ((le_of_eq h.symm).trans inf_le_right)
  · exact le_inf (sup_le hALL hOL) (hclaim _ hΛ le_rfl)
  · intro Z hZL hΛZ
    exact le_inf hZL.le (hclaim Z hZL hΛZ)
  · intro x hxL hxL₀
    have hxM : x ∉ M₁ := fun h => hxL₀ ⟨hxL, h⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := (mem_sup_iff_of_le_normalizer hKR).1 hxL
    have hkM : k ∉ M₁ := fun h => hxM (M₁.mul_mem h (hRM₁ hr))
    have hK' := lOne_eq_sup_conjSub hFconj hM₁ hN₁ huniq hAN hDN hNX hND hzmin hzN hk hkM
    apply le_antisymm
    · refine sup_le ?_ (hRO.trans le_sup_right)
      have hcj : conjSub k A ≤ A ⊔ conjSub (k * r) A ⊔ pCoreOf 2 L := by
        rintro _ ⟨a, ha, rfl⟩
        have h1 : r * a * r⁻¹ * a⁻¹ ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp (hXR (hAX ha)) r⁻¹).mp (R.inv_mem hr)
          have h2 := R.mul_mem hr this
          simpa [mul_assoc] using h2
        have hρ : k * (r * a * r⁻¹ * a⁻¹) * k⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hXR (hKX hk)) _).mp h1
        have e : k * a * k⁻¹ =
            (k * (r * a * r⁻¹ * a⁻¹) * k⁻¹)⁻¹ * ((k * r) * a * (k * r)⁻¹) := by group
        show k * a * k⁻¹ ∈ _
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hRO (R.inv_mem hρ)))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_conjSub_of_mem ha)))
      rw [show K = A ⊔ conjSub k A ⊔ D from hK']
      exact sup_le (sup_le (le_sup_left.trans le_sup_left) hcj) (hDO.trans le_sup_right)
    · refine sup_le (sup_le hALL ?_) hOL
      rintro _ ⟨a, ha, rfl⟩
      exact L.mul_mem (L.mul_mem hxL (hALL ha)) (L.inv_mem hxL)

end CFSG.CGT.PushingUpLit.BHS
