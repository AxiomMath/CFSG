module

public import CFSG.CGT.Stroth77.StrothAmbient
public import CFSG.CGT.Stroth77.StrothFrameD

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.IsD.stroth_3_10 {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hmax : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D)
    (h223X : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ')
      (X : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      IsMulCommutative X → F.A ≤ X → X ≤ (F.S : Subgroup G) →
      F.dA.L ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) →
      ∃ (D₁ : Subgroup G) (τ₁ : StrothTypeIndex) (dD₁ : StrothWeakTypeData D₁ τ₁),
        F.IsD D₁ dD₁ ∧ IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧ Nat.card X ≤ Nat.card D₁)
    (h35 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m = τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) = D' ∨
        ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
          F.dA.L ≤ Subgroup.normalizer
            ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) ∧
          Nat.card D' < Nat.card X)
    (hchar3 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m = τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) = D' →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer (D' : Set G))
    (hcharB : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m ≠ τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (h226 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ')
      (B : Subgroup G), F.IsD D' dD' →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n) :
    (τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D) ∧
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
  have hR : τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D := by
    intro hτ
    rcases h35 D τ dD h hτ hns with hRD | ⟨X, hX, hAX, hXS, hL, hlt⟩
    · exact hRD
    · obtain ⟨D₁, τ₁, dD₁, h₁, hns₁, hle⟩ := h223X D τ dD X h hns hX hAX hXS hL
      exact absurd (hmax D₁ τ₁ dD₁ h₁ hns₁) (by omega)
  refine ⟨hR, ?_⟩
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  have hDN : D ≤ N := le_inf h.le_S (Subgroup.le_normalizer)
  have hkey : ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer (N : Set G) →
      g ∈ Subgroup.normalizer (D : Set G) := by
    intro g hgS hgN
    by_cases hτ : τ.m = τ.n
    · exact hchar3 D τ dD h hτ hns (hR hτ) g hgS hgN
    by_contra hgD
    have hΩ := hcharB D τ dD h hτ hns g hgS hgN
    have hcomm : ∀ x y : D, x * y = y * x := fun x y => dD.isMulCommutative.is_comm.comm x y
    have hmemB : ∀ b ∈ D.map (MulAut.conj g).toMonoidHom, ∃ d ∈ D, b = g * d * g⁻¹ := by
      rintro b ⟨d, hd, rfl⟩
      exact ⟨d, hd, rfl⟩
    refine hτ (h226 D τ dD (D.map (MulAut.conj g).toMonoidHom) h ?_ ?_ ?_ ⟨g, rfl⟩)
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

theorem StrothFrame.stroth_3_10 (F : StrothFrame G)
    (h223 : ∃ (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
      F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (h223X : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ')
      (X : Subgroup G), F.IsD D' dD' →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      IsMulCommutative X → F.A ≤ X → X ≤ (F.S : Subgroup G) →
      F.dA.L ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) →
      ∃ (D₁ : Subgroup G) (τ₁ : StrothTypeIndex) (dD₁ : StrothWeakTypeData D₁ τ₁),
        F.IsD D₁ dD₁ ∧ IsSylowIn 2 (Subgroup.normalizer (D₁ : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D₁ : Set G)) ∧ Nat.card X ≤ Nat.card D₁)
    (h35 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m = τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) = D' ∨
        ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
          F.dA.L ≤ Subgroup.normalizer
            ((X ⊔ Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G) ∧
          Nat.card D' < Nat.card X)
    (hchar3 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m = τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) = D' →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer (D' : Set G))
    (hcharB : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → τ'.m ≠ τ'.n →
      IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) →
      ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer
          (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (h226 : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ')
      (B : Subgroup G), F.IsD D' dD' →
      B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D' → (∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) → τ'.m = τ'.n) :
    ∃ (D : Subgroup G) (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
      F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) ∧
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) ∧
      (τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D) ∧
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  set P : Set (Subgroup G) := {D | ∃ (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ),
    F.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))} with hP
  obtain ⟨D₀, τ₀, dD₀, h₀, hns₀⟩ := h223
  obtain ⟨D, ⟨τ, dD, h, hns⟩, hmax⟩ :=
    Set.exists_max_image P (fun D => Nat.card D) (Set.toFinite P) ⟨D₀, τ₀, dD₀, h₀, hns₀⟩
  have hmax' : ∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
      F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D :=
    fun D' τ' dD' h' hns' => hmax D' ⟨τ', dD', h', hns'⟩
  exact ⟨D, τ, dD, h, hns, hmax',
    h.stroth_3_10 hns hmax' h223X h35 hchar3 hcharB h226⟩

end CFSG.CGT.Stroth77
