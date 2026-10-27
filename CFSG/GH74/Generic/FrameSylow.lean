module

public import CFSG.GH74.Generic.Frame

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd Subgroup

variable {G : Type} [Group G] [Finite G]

theorem frame_center_sylow (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hfr : Q8Frame ↥K) (S : Sylow 2 (CentralizerBar x)) :
    ∀ s ∈ (S : Subgroup (CentralizerBar x)),
      ((∀ s' ∈ (S : Subgroup (CentralizerBar x)), s' * s = s * s') ↔
        s ∈ Subgroup.zpowers (xbar x)) := by
  intro s hs
  constructor
  · intro hsc
    obtain ⟨φ, hφ, w, hww, hsw⟩ := hfr
    let Φ : Q8 × Q8 →* CentralizerBar x := K.subtype.comp φ
    have hΦ : Function.Injective Φ := K.subtype_injective.comp hφ
    have hC := gen4_centralizerBar hG x
    have hxeq := frame_xbar_eq hG hx φ hφ w hsw
    let w' : CentralizerBar x := (w : CentralizerBar x)
    have hw' : w' * w' = 1 := congrArg Subtype.val hww
    have hnorm : ∀ a ∈ Φ.range, w' * a * w'⁻¹ ∈ Φ.range := by
      rintro _ ⟨⟨g, h⟩, rfl⟩
      refine ⟨(h, g), ?_⟩
      change ((φ (h, g) : ↥K) : CentralizerBar x) = _
      rw [← hsw g h]
      rfl
    have hP := isPGroup_two_sup_zpowers Φ.range (isPGroup_range_q8q8 Φ) w' hw' hnorm
    obtain ⟨S₁, hS₁⟩ := hP.exists_le_sylow
    have hAS : Φ.range ≤ S₁ := le_trans le_sup_left hS₁
    have hwS : w' ∈ (S₁ : Subgroup (CentralizerBar x)) :=
      hS₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w'))
    obtain ⟨g, hg⟩ := exists_conj_sylow S₁ S
    have hs₁ : g⁻¹ * s * g ∈ (S₁ : Subgroup (CentralizerBar x)) := (hg s).1 hs
    have hs₁c : ∀ u ∈ (S₁ : Subgroup (CentralizerBar x)),
        u * (g⁻¹ * s * g) = (g⁻¹ * s * g) * u := by
      intro u hu
      have hm : g * u * g⁻¹ ∈ (S : Subgroup (CentralizerBar x)) := by
        rw [hg]
        simpa [mul_assoc] using hu
      have := hsc _ hm
      calc u * (g⁻¹ * s * g) = g⁻¹ * ((g * u * g⁻¹) * s) * g := by group
        _ = g⁻¹ * (s * (g * u * g⁻¹)) * g := by rw [this]
        _ = (g⁻¹ * s * g) * u := by group
    have hTle : Subgroup.zpowers (g⁻¹ * s * g) ≤ (S₁ : Subgroup (CentralizerBar x)) :=
      (Subgroup.zpowers_le).2 hs₁
    have hT2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * s * g)) :=
      S₁.isPGroup'.to_le hTle
    have hcomm : ∀ (a : Q8 × Q8) (t : CentralizerBar x), t ∈ Subgroup.zpowers (g⁻¹ * s * g) →
        Φ a * t = t * Φ a := by
      intro a t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have h1 : Commute (Φ a) (g⁻¹ * s * g) := hs₁c (Φ a) (hAS ⟨a, rfl⟩)
      exact (h1.zpow_right k).eq
    obtain ⟨a, ha, hac⟩ := q8q8_commuting_two_subgroup_le_center hC Φ hΦ _ hT2 hcomm
      (g⁻¹ * s * g) (Subgroup.mem_zpowers _)
    have hswap : w' * (g⁻¹ * s * g) * w'⁻¹ = g⁻¹ * s * g := by
      have := hs₁c w' hwS
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hfix : a = (a.2, a.1) := by
      apply hΦ
      have h1 : w' * ((φ a : ↥K) : CentralizerBar x) * w'⁻¹ =
          ((φ (a.2, a.1) : ↥K) : CentralizerBar x) := by
        have := congrArg (fun u : ↥K => (u : CentralizerBar x)) (hsw a.1 a.2)
        simpa using this
      change ((φ a : ↥K) : CentralizerBar x) = ((φ (a.2, a.1) : ↥K) : CentralizerBar x)
      rw [← h1]
      have ha' : ((φ a : ↥K) : CentralizerBar x) = g⁻¹ * s * g := ha
      rw [ha']
      exact hswap.symm
    have hs₁x : g⁻¹ * s * g ∈ Subgroup.zpowers (xbar x) := by
      rcases central_swap_fixed hac hfix with h | h
      · rw [← ha, h, map_one]
        exact Subgroup.one_mem _
      · rw [← ha, h]
        change ((φ (QuaternionGroup.a 2, QuaternionGroup.a 2) : ↥K) : CentralizerBar x) ∈ _
        rw [hxeq]
        exact Subgroup.mem_zpowers _
    have hcomm' := commute_of_mem_zpowers_xbar x g hs₁x
    have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
    rw [this]
    have h2 : g * (g⁻¹ * s * g) = (g⁻¹ * s * g) * g := hcomm'
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
    exact hs₁x
  · intro hsx s' _
    exact commute_of_mem_zpowers_xbar x s' hsx

theorem frame_central_sylow_le_zpowers (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hfr : Q8Frame ↥K)
    (S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) (s : ↥(Subgroup.centralizer ({x} : Set G)))
    (hs : s ∈ (S : Subgroup _)) (hsc : ∀ s' ∈ (S : Subgroup _), s' * s = s * s') :
    s ∈ Subgroup.zpowers (xH x) := by
  let π : ↥(Subgroup.centralizer ({x} : Set G)) →* CentralizerBar x :=
    QuotientGroup.mk' (pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G)))
  let Sbar : Sylow 2 (CentralizerBar x) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hSbar : (Sbar : Subgroup (CentralizerBar x)) = (S : Subgroup _).map π := rfl
  have hmem : π s ∈ (Sbar : Subgroup (CentralizerBar x)) := ⟨s, hs, rfl⟩
  have hcent : ∀ u ∈ (Sbar : Subgroup (CentralizerBar x)), u * π s = π s * u := by
    intro u hu
    rw [hSbar] at hu
    obtain ⟨s', hs', rfl⟩ := hu
    rw [← map_mul, ← map_mul, hsc s' hs']
  have h1 := (frame_center_sylow hG hx hfr Sbar (π s) hmem).1 hcent
  have hπx : xbar x = π (xH x) := rfl
  rw [hπx, ← MonoidHom.map_zpowers] at h1
  obtain ⟨y, hy, hys⟩ := h1
  have hyS : y ∈ (S : Subgroup _) :=
    (Subgroup.zpowers_le).2 (xH_mem_sylow hx S) hy
  have hn : y⁻¹ * s ∈ pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G)) :=
    (QuotientGroup.eq).1 hys
  have hnS : y⁻¹ * s ∈ (S : Subgroup _) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hs
  have h0 := eq_one_of_mem_sylow_of_mem_pPrimeCore S hnS hn
  have : s = y := by
    rw [inv_mul_eq_one] at h0
    exact h0.symm
  rw [this]
  exact hy

theorem frame_sylow_centralizer_isSylow (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hfr : Q8Frame ↥K)
    (S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) :
    ∃ T : Sylow 2 G,
      (T : Subgroup G) = (S : Subgroup ↥(Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype ∧
      x ∈ (T : Subgroup G) ∧ (∀ t ∈ (T : Subgroup G), t * x = x * t) ∧
      ∀ c ∈ (T : Subgroup G), (∀ t ∈ (T : Subgroup G), t * c = c * t) →
        c ∈ Subgroup.zpowers x := by
  let H : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let St : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hSt : IsPGroup 2 ↥St := S.isPGroup'.map H.subtype
  obtain ⟨T₁, hT₁⟩ := hSt.exists_le_sylow
  have hxSt : x ∈ St := ⟨xH x, xH_mem_sylow hx S, rfl⟩
  have hxT₁ : x ∈ (T₁ : Subgroup G) := hT₁ hxSt
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have key : ∀ c ∈ (T₁ : Subgroup G), (∀ t ∈ (T₁ : Subgroup G), t * c = c * t) →
      c ∈ Subgroup.zpowers x := by
    intro c hcT hcc
    have hcH : c ∈ H := Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcc h hxT₁)
    let c₀ : ↥H := ⟨c, hcH⟩
    have hle : St ⊔ Subgroup.zpowers c ≤ (T₁ : Subgroup G) :=
      sup_le hT₁ ((Subgroup.zpowers_le).2 hcT)
    have hQ2 : IsPGroup 2 ↥((St ⊔ Subgroup.zpowers c).subgroupOf H) :=
      isPGroup_subgroupOf (T₁.isPGroup'.to_le hle) H
    have hSQ : (S : Subgroup ↥H) ≤ (St ⊔ Subgroup.zpowers c).subgroupOf H := fun s hs =>
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (⟨s, hs, rfl⟩ : (s : G) ∈ St))
    have hQS := S.is_maximal' hQ2 hSQ
    have hc₀S : c₀ ∈ (S : Subgroup ↥H) := by
      rw [← hQS]
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    have hc₀c : ∀ s' ∈ (S : Subgroup ↥H), s' * c₀ = c₀ * s' := fun s' hs' =>
      Subtype.ext (hcc _ (hT₁ ⟨s', hs', rfl⟩))
    have h1 := frame_central_sylow_le_zpowers hG hx hfr S c₀ hc₀S hc₀c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have h2 : ((xH x ^ k : ↥H) : G) = ((c₀ : ↥H) : G) := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h2
    exact Subgroup.mem_zpowers_iff.2 ⟨k, h2⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have : Nontrivial ↥(T₁ : Subgroup G) := ⟨⟨⟨x, hxT₁⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have := T₁.isPGroup'.center_nontrivial
  obtain ⟨⟨c, hc⟩, hcne⟩ := exists_ne (1 : ↥(Subgroup.center ↥(T₁ : Subgroup G)))
  have hcc : ∀ t ∈ (T₁ : Subgroup G), t * (c : G) = (c : G) * t := fun t ht =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨t, ht⟩)
  have hcx := key (c : G) c.2 hcc
  have hcx' : (c : G) = x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcx
    rcases zpow_eq_one_or_self hxx k with h | h
    · exfalso
      apply hcne
      apply Subtype.ext
      apply Subtype.ext
      rw [← hk, h]
      rfl
    · rw [← hk, h]
  have hxc : ∀ t ∈ (T₁ : Subgroup G), t * x = x * t := fun t ht => hcx' ▸ hcc t ht
  have hT₁H : (T₁ : Subgroup G) ≤ H := fun t ht =>
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hxc t ht).symm)
  have hQ2 : IsPGroup 2 ↥((T₁ : Subgroup G).subgroupOf H) :=
    isPGroup_subgroupOf T₁.isPGroup' H
  have hSQ : (S : Subgroup ↥H) ≤ (T₁ : Subgroup G).subgroupOf H := fun s hs =>
    Subgroup.mem_subgroupOf.2 (hT₁ (⟨s, hs, rfl⟩ : (s : G) ∈ St))
  have hQS := S.is_maximal' hQ2 hSQ
  refine ⟨T₁, ?_, hxT₁, hxc, key⟩
  apply le_antisymm
  · intro g hg
    have : (⟨g, hT₁H hg⟩ : ↥H) ∈ (T₁ : Subgroup G).subgroupOf H := hg
    rw [hQS] at this
    exact ⟨⟨g, hT₁H hg⟩, this, rfl⟩
  · exact hT₁

theorem frame_isCentralInvolution (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hfr : Q8Frame ↥K) : IsCentralInvolution x := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) := inferInstance
  obtain ⟨T, -, hxT, hcomm, -⟩ := frame_sylow_centralizer_isSylow hG hx hfr S
  exact ⟨hx, T, hxT, hcomm⟩

end CFSG.GH74.Generic
