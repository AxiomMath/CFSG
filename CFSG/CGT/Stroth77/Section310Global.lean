module

public import CFSG.CGT.Stroth77.Section310Char
public import CFSG.CGT.Stroth77.Stroth35Plus

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem StrothFrame.stroth_3_10_global {G : Type} [Group G] [Finite G]
    (h223 : ∃ (F : StrothFrame G) (D : Subgroup G) (τ : StrothTypeIndex)
      (dD : StrothWeakTypeData D τ), F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (h223Xp : ∀ (F : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex)
      (dD' : StrothWeakTypeData D' τ') (X : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      IsMulCommutative X → F.A ≤ X →
      X ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ X, x⁻¹ * F.dA.uv * x * F.dA.uv⁻¹ ∈ D' ∧ x⁻¹ * F.dA.t * x * F.dA.t⁻¹ ∈ D') →
      F.dA.L ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) →
      (∀ Y : Subgroup G, Y ≤ X ⊔ D' → IsMulCommutative Y → Nat.card Y = Nat.card X → Y = X) →
      ∃ (F₁ : StrothFrame G) (D₁ : Subgroup G) (τ₁ : StrothTypeIndex)
        (dD₁ : StrothWeakTypeData D₁ τ₁), F₁.IsD D₁ dD₁ ∧
          IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
            ((F₁.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧
          Nat.card X ≤ Nat.card D₁)
    (hcharB : ∀ (F : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex)
      (dD' : StrothWeakTypeData D' τ'), F.IsD D' dD' → τ'.m ≠ τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (h226p : ∀ (F : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex)
      (dD' : StrothWeakTypeData D' τ') (B : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n) :
    ∃ (F : StrothFrame G) (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
      F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) ∧
      (∀ (F' : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex)
        (dD' : StrothWeakTypeData D' τ'), F'.IsD D' dD' →
        IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F'.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) ∧
      (τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D) ∧
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
  classical
  set P : ℕ → Prop := fun n => ∃ (F : StrothFrame G) (D : Subgroup G) (τ : StrothTypeIndex)
    (dD : StrothWeakTypeData D τ), F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) ∧ Nat.card D = n with hP
  obtain ⟨F₀, D₀, τ₀, dD₀, h₀, hns₀⟩ := h223
  have hP₀ : P (Nat.card D₀) := ⟨F₀, D₀, τ₀, dD₀, h₀, hns₀, rfl⟩
  obtain ⟨F, D, τ, dD, h, hns, hcard⟩ :=
    Nat.findGreatest_spec (Subgroup.card_le_card_group D₀) hP₀
  have hmax : ∀ (F' : StrothFrame G) (D' : Subgroup G) (τ' : StrothTypeIndex)
      (dD' : StrothWeakTypeData D' τ'), F'.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F'.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D :=
    fun F' D' τ' dD' h' hns' => by
      rw [hcard]
      exact Nat.le_findGreatest (Subgroup.card_le_card_group D') ⟨F', D', τ', dD', h', hns', rfl⟩
  refine ⟨F, D, τ, dD, h, hns, hmax, ?_⟩
  have hR : τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D := by
    intro hτ
    rcases F.stroth_3_5_to_3_9_plus D τ dD h hτ hns with hRD | ⟨X, hX, hAX, hXR, hXV, hL, hu, hlt⟩
    · exact hRD
    · obtain ⟨F₁, D₁, τ₁, dD₁, h₁, hns₁, hle⟩ := h223Xp F D τ dD X h hns hX hAX hXR hXV hL hu
      exact absurd (hmax F₁ D₁ τ₁ dD₁ h₁ hns₁) (by omega)
  refine ⟨hR, ?_⟩
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  have hDN : D ≤ N := le_inf h.le_S (Subgroup.le_normalizer)
  have hkey : ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer (N : Set G) →
      g ∈ Subgroup.normalizer (D : Set G) := by
    intro g hgS hgN
    by_cases hτ : τ.m = τ.n
    · exact h.mem_normalizer_of_mem_normalizer_normalizerIn hτ (hR hτ) hgS hgN
    by_contra hgD
    have hΩ := hcharB F D τ dD h hτ hns g hgS hgN
    have hcomm : ∀ x y : D, x * y = y * x := fun x y => dD.isMulCommutative.is_comm.comm x y
    have hmemB : ∀ b ∈ D.map (MulAut.conj g).toMonoidHom, ∃ d ∈ D, b = g * d * g⁻¹ := by
      rintro b ⟨d, hd, rfl⟩
      exact ⟨d, hd, rfl⟩
    refine hτ (h226p F D τ dD (D.map (MulAut.conj g).toMonoidHom) h hns ?_ ?_ ?_ ⟨g, rfl⟩)
    · intro b hb
      obtain ⟨d, hd, rfl⟩ := hmemB b hb
      have hdN : g * d * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hgN d).mp (hDN hd)
      refine Subgroup.mem_inf.mpr ⟨hdN, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : g⁻¹ * w * g ∈ omegaIn 1 D :=
        (Subgroup.mem_normalizer_iff''.mp hΩ w).mp hw
      have hc : d * (g⁻¹ * w * g) = (g⁻¹ * w * g) * d :=
        congrArg Subtype.val (hcomm ⟨d, hd⟩ ⟨_, omegaIn_le 1 D hw'⟩)
      calc w * (g * d * g⁻¹) = g * ((g⁻¹ * w * g) * d) * g⁻¹ := by group
        _ = g * (d * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc]
        _ = g * d * g⁻¹ * w := by group
    · intro x hx b hb
      obtain ⟨d, hd, rfl⟩ := hmemB b hb
      have hxN : g⁻¹ * x * g ∈ N :=
        (Subgroup.mem_normalizer_iff''.mp hgN x).mp (Subgroup.mem_inf.mp hx).1
      have hd' : (g⁻¹ * x * g) * d * (g⁻¹ * x * g)⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hxN).2 d).mp hd
      refine ⟨_, hd', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · intro hBD
      apply hgD
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · rw [← hBD]
        exact ⟨x, hx, rfl⟩
      · rw [← hBD] at hx
        obtain ⟨d, hd, hdx⟩ := hmemB _ hx
        have : x = d := by simpa using hdx
        exact this ▸ hd
  by_contra hSN
  have hNS : N < (F.S : Subgroup G) :=
    lt_of_le_of_ne inf_le_left fun hEq => hSN (hEq ▸ inf_le_right)
  set IP : Subgroup (F.S : Subgroup G) := N.subgroupOf (F.S : Subgroup G) with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hNS.ne (le_antisymm hNS.le fun x hx => ?_)
    have : (⟨x, hx⟩ : (F.S : Subgroup G)) ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent (F.S : Subgroup G) := F.S.isPGroup'.isNilpotent
  obtain ⟨x, hxN, hxnot⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent IP hIPlt)
  have hxsub : x ∈ (Subgroup.normalizer (N : Set G)).subgroupOf (F.S : Subgroup G) := by
    rw [Subgroup.subgroupOf_normalizer_eq hNS.le]
    exact hxN
  have hxD := hkey x x.2 (Subgroup.mem_subgroupOf.mp hxsub)
  exact hxnot (Subgroup.mem_subgroupOf.mpr ⟨x.2, hxD⟩)

end CFSG.CGT.Stroth77
