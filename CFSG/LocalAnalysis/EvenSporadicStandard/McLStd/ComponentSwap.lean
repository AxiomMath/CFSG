module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Sign

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG

variable {Y : Type*} [Group Y]

@[expose] def conjSub (s : Y) (K : Subgroup Y) : Subgroup Y :=
  K.map (MulAut.conj s).toMonoidHom

theorem mem_conjSub {s : Y} {K : Subgroup Y} {x : Y} : x ∈ conjSub s K ↔ s⁻¹ * x * s ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : s⁻¹ * ((MulAut.conj s).toMonoidHom k) * s = k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this]; exact hk
  · intro h
    refine ⟨s⁻¹ * x * s, h, ?_⟩
    simp [MulAut.conj_apply]; group

theorem conjSub_conjSub {s : Y} (hs : s * s = 1) (K : Subgroup Y) :
    conjSub s (conjSub s K) = K := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  ext x
  rw [mem_conjSub, mem_conjSub, hsi]
  have : s * (s * x * s) * s = x := by
    calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
      _ = x := by rw [hs]; group
  rw [this]

theorem conjSub_mul (g h : Y) (K : Subgroup Y) :
    conjSub (g * h) K = conjSub g (conjSub h K) := by
  ext x
  rw [mem_conjSub, mem_conjSub, mem_conjSub]
  have : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [this]

theorem conjSub_one (K : Subgroup Y) : conjSub 1 K = K := by
  ext x
  rw [mem_conjSub]
  simp

theorem exists_noncentral_commutator {N : Subgroup Y} (hN : IsQuasisimple N) :
    ∃ n₁ ∈ N, ∃ n₂ ∈ N, ¬ ∀ x ∈ N, x * ((n₂ * n₁)⁻¹ * (n₁ * n₂)) =
      ((n₂ * n₁)⁻¹ * (n₁ * n₂)) * x := by
  obtain ⟨a, b, hab⟩ := hN.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', a'.2, b', b'.2, fun hall => hab ?_⟩
  have hc : (b' * a')⁻¹ * (a' * b') ∈ center N := by
    rw [mem_center_iff]
    intro g
    have := hall g g.2
    exact Subtype.ext (by simpa using this)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact ((QuotientGroup.eq (s := center N)).2 hc).symm

variable [Finite Y]

theorem eq_of_swapped_component {s : Y} (hs : s * s = 1) {K B : Subgroup Y}
    (hK : IsComponent K) (hBK : B ≤ K ⊔ conjSub s K)
    (hBs : B ≤ centralizer ({s} : Set Y))
    (hC : centralizer ({s} : Set Y) ≤ zpowers s ⊔ B)
    {N : Subgroup Y} (hN : IsComponent N) (hNs : conjSub s N ≠ N) :
    N = K ∨ N = conjSub s K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hNK, hNKs⟩ := hcon
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hKc : IsComponent (conjSub s K) := LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hK
  have hNc : IsComponent (conjSub s N) := LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hN
  have hcomm : ∀ {A C : Subgroup Y}, IsComponent A → IsComponent C → A ≠ C →
      ∀ a ∈ A, ∀ c ∈ C, a * c = c * a := by
    intro A C hA hC hne a ha c hc
    have h0 := (LocalCores.distinct_components_commute hA hC).resolve_left hne
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0 ha
    exact ((mem_centralizer_iff.1 h1) c hc).symm
  have hN_Ns : N ≠ conjSub s N := fun h => hNs h.symm
  have hNs_K : conjSub s N ≠ K := by
    intro h
    apply hNKs
    rw [← conjSub_conjSub hs N, h]
  have hNs_Ks : conjSub s N ≠ conjSub s K := by
    intro h
    apply hNK
    rw [← conjSub_conjSub hs N, h, conjSub_conjSub hs K]
  have hm : ∀ n ∈ N, s * n * s ∈ conjSub s N := by
    intro n hn
    rw [mem_conjSub, hsi]
    have : s * (s * n * s) * s = n := by
      calc s * (s * n * s) * s = (s * s) * n * (s * s) := by group
        _ = n := by rw [hs]; group
    rw [this]; exact hn
  have hNNs : ∀ a ∈ N, ∀ c ∈ conjSub s N, a * c = c * a := hcomm hN hNc hN_Ns
  have hNK' : ∀ a ∈ N, ∀ c ∈ K, a * c = c * a := hcomm hN hK hNK
  have hNKs' : ∀ a ∈ N, ∀ c ∈ conjSub s K, a * c = c * a := hcomm hN hKc hNKs
  have hNsK : ∀ a ∈ conjSub s N, ∀ c ∈ K, a * c = c * a := hcomm hNc hK hNs_K
  have hNsKs : ∀ a ∈ conjSub s N, ∀ c ∈ conjSub s K, a * c = c * a := hcomm hNc hKc hNs_Ks
  have hcB : ∀ x : Y, (∀ k ∈ K, x * k = k * x) → (∀ k ∈ conjSub s K, x * k = k * x) →
      ∀ b ∈ B, b * x = x * b := by
    intro x h1 h2 b hb
    have hle : K ⊔ conjSub s K ≤ centralizer ({x} : Set Y) :=
      sup_le (fun k hk => mem_centralizer_singleton_iff.2 (h1 k hk).symm)
        (fun k hk => mem_centralizer_singleton_iff.2 (h2 k hk).symm)
    exact mem_centralizer_singleton_iff.1 (hle (hBK hb))
  have hBz : B ≤ centralizer (zpowers s : Set Y) := by
    intro b hb
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    have hc : Commute s b := (mem_centralizer_singleton_iff.1 (hBs hb)).symm
    exact (hc.zpow_left k).eq
  have hdata : ∀ n ∈ N, ∃ a ∈ zpowers s, ∃ b ∈ B, n * (s * n * s) = a * b ∧
      ∀ b' ∈ B, b' * b = b * b' := by
    intro n hn
    have hmn := hm n hn
    have hcomm1 : (s * n * s) * n = n * (s * n * s) := (hNNs n hn _ hmn).symm
    have hds : (n * (s * n * s)) * s = s * (n * (s * n * s)) := by
      have h1 : (n * (s * n * s)) * s = ((s * n * s) * n) * s := by rw [hcomm1]
      rw [h1]; group
    have hdc : n * (s * n * s) ∈ centralizer ({s} : Set Y) :=
      mem_centralizer_singleton_iff.2 hds
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hBz (hC hdc)
    refine ⟨a, ha, b, hb, hab, fun b' hb' => ?_⟩
    have h1 : b' * (n * (s * n * s)) = (n * (s * n * s)) * b' := by
      have h2 := hcB n (fun k hk => hNK' n hn k hk) (fun k hk => hNKs' n hn k hk) b' hb'
      have h3 := hcB (s * n * s) (fun k hk => hNsK _ hmn k hk)
        (fun k hk => hNsKs _ hmn k hk) b' hb'
      calc b' * (n * (s * n * s)) = (b' * n) * (s * n * s) := (mul_assoc _ _ _).symm
        _ = n * (b' * (s * n * s)) := by rw [h2]; exact mul_assoc _ _ _
        _ = n * ((s * n * s) * b') := by rw [h3]
        _ = (n * (s * n * s)) * b' := (mul_assoc _ _ _).symm
    have h3 : b' * a = a * b' := ((mem_centralizer_iff.1 (hBz hb')) a ha).symm
    have h4 : b' * (a * b) = (a * b) * b' := by rw [← hab]; exact h1
    have e1 : a * (b' * b) = a * (b * b') := by
      calc a * (b' * b) = (a * b') * b := (mul_assoc _ _ _).symm
        _ = (b' * a) * b := by rw [h3]
        _ = b' * (a * b) := mul_assoc _ _ _
        _ = (a * b) * b' := h4
        _ = a * (b * b') := mul_assoc _ _ _
    exact mul_left_cancel e1
  obtain ⟨n₁, hn₁, n₂, hn₂, hnc⟩ := exists_noncentral_commutator hN.1
  obtain ⟨a₁, ha₁, b₁, hb₁, hab₁, hbc₁⟩ := hdata n₁ hn₁
  obtain ⟨a₂, ha₂, b₂, hb₂, hab₂, hbc₂⟩ := hdata n₂ hn₂
  have hm₁ := hm n₁ hn₁
  have hm₂ := hm n₂ hn₂
  have hdd : (n₁ * (s * n₁ * s)) * (n₂ * (s * n₂ * s)) =
      (n₂ * (s * n₂ * s)) * (n₁ * (s * n₁ * s)) := by
    rw [hab₁, hab₂]
    have haa : a₁ * a₂ = a₂ * a₁ := by
      obtain ⟨k₁, rfl⟩ := mem_zpowers_iff.1 ha₁
      obtain ⟨k₂, rfl⟩ := mem_zpowers_iff.1 ha₂
      exact ((Commute.refl s).zpow_zpow k₁ k₂).eq
    have hb2a : b₁ * a₂ = a₂ * b₁ := ((mem_centralizer_iff.1 (hBz hb₁)) a₂ ha₂).symm
    have hb1a : b₂ * a₁ = a₁ * b₂ := ((mem_centralizer_iff.1 (hBz hb₂)) a₁ ha₁).symm
    have hbb : b₁ * b₂ = b₂ * b₁ := (hbc₁ b₂ hb₂).symm
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [hb2a]
      _ = (a₁ * a₂) * (b₁ * b₂) := by group
      _ = (a₂ * a₁) * (b₂ * b₁) := by rw [haa, hbb]
      _ = a₂ * (a₁ * b₂) * b₁ := by group
      _ = a₂ * (b₂ * a₁) * b₁ := by rw [hb1a]
      _ = a₂ * b₂ * (a₁ * b₁) := by group
  have key : n₁ * n₂ * ((s * n₁ * s) * (s * n₂ * s)) =
      n₂ * n₁ * ((s * n₂ * s) * (s * n₁ * s)) := by
    have c1 : n₂ * (s * n₁ * s) = (s * n₁ * s) * n₂ := hNNs n₂ hn₂ _ hm₁
    have c2 : n₁ * (s * n₂ * s) = (s * n₂ * s) * n₁ := hNNs n₁ hn₁ _ hm₂
    calc n₁ * n₂ * ((s * n₁ * s) * (s * n₂ * s))
        = n₁ * (n₂ * (s * n₁ * s)) * (s * n₂ * s) := by group
      _ = n₁ * ((s * n₁ * s) * n₂) * (s * n₂ * s) := by rw [c1]
      _ = (n₁ * (s * n₁ * s)) * (n₂ * (s * n₂ * s)) := by group
      _ = (n₂ * (s * n₂ * s)) * (n₁ * (s * n₁ * s)) := hdd
      _ = n₂ * ((s * n₂ * s) * n₁) * (s * n₁ * s) := by group
      _ = n₂ * (n₁ * (s * n₂ * s)) * (s * n₁ * s) := by rw [← c2]
      _ = n₂ * n₁ * ((s * n₂ * s) * (s * n₁ * s)) := by group
  have hc_eq : (n₂ * n₁)⁻¹ * (n₁ * n₂) =
      ((s * n₂ * s) * (s * n₁ * s)) * ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by
    calc (n₂ * n₁)⁻¹ * (n₁ * n₂)
        = (n₂ * n₁)⁻¹ * (n₁ * n₂ * ((s * n₁ * s) * (s * n₂ * s))) *
            ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by group
      _ = (n₂ * n₁)⁻¹ * (n₂ * n₁ * ((s * n₂ * s) * (s * n₁ * s))) *
            ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by rw [key]
      _ = ((s * n₂ * s) * (s * n₁ * s)) * ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by group
  have hcmem : (n₂ * n₁)⁻¹ * (n₁ * n₂) ∈ conjSub s N := by
    rw [hc_eq]
    exact (conjSub s N).mul_mem ((conjSub s N).mul_mem hm₂ hm₁)
      ((conjSub s N).inv_mem ((conjSub s N).mul_mem hm₁ hm₂))
  exact hnc fun x hx => hNNs x hx _ hcmem

@[expose] def compPerm (g : Y) : Equiv.Perm {N : Subgroup Y // IsComponent N} where
  toFun N := ⟨conjSub g N.1, LocalCores.isComponent_map_mulEquiv (MulAut.conj g) N.2⟩
  invFun N := ⟨conjSub g⁻¹ N.1, LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) N.2⟩
  left_inv N := Subtype.ext (by
    show conjSub g⁻¹ (conjSub g N.1) = N.1
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one])
  right_inv N := Subtype.ext (by
    show conjSub g (conjSub g⁻¹ N.1) = N.1
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one])

@[expose] def compAct : Y →* Equiv.Perm {N : Subgroup Y // IsComponent N} where
  toFun := compPerm
  map_one' := Equiv.ext fun N => Subtype.ext (conjSub_one N.1)
  map_mul' g h := Equiv.ext fun N => Subtype.ext (conjSub_mul g h N.1)

@[expose] def unitsToZMod2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      decide

theorem unitsToZMod2_ne_one {u : ℤˣ} (hu : u ≠ 1) : unitsToZMod2 u ≠ 1 := by
  simp only [unitsToZMod2, MonoidHom.coe_mk, OneHom.coe_mk, hu, ↓reduceIte]
  decide

theorem exists_hom_of_swapped_component {s : Y} (hs : s * s = 1) {K B : Subgroup Y}
    (hK : IsComponent K) (hKs : conjSub s K ≠ K) (hBK : B ≤ K ⊔ conjSub s K)
    (hBs : B ≤ centralizer ({s} : Set Y))
    (hC : centralizer ({s} : Set Y) ≤ zpowers s ⊔ B) :
    ∃ φ : Y →* Multiplicative (ZMod 2), φ s ≠ 1 := by
  classical
  have : Fintype {N : Subgroup Y // IsComponent N} := Fintype.ofFinite _
  refine ⟨unitsToZMod2.comp (Equiv.Perm.sign.comp compAct), ?_⟩
  apply unitsToZMod2_ne_one
  intro hsign
  have hsq : compAct s * compAct s = 1 := by rw [← map_mul, hs, map_one]
  have h4 := M11Std.four_dvd_card_support_of_sign_eq_one hsq hsign
  have hKc : IsComponent (conjSub s K) := LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hK
  have hne : (⟨K, hK⟩ : {N : Subgroup Y // IsComponent N}) ≠ ⟨conjSub s K, hKc⟩ :=
    fun h => hKs (congrArg Subtype.val h).symm
  have hsupp : (compAct s).support = {⟨K, hK⟩, ⟨conjSub s K, hKc⟩} := by
    ext N
    rw [Equiv.Perm.mem_support, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hmoved
      have hmoved' : conjSub s N.1 ≠ N.1 := fun h => hmoved (Subtype.ext h)
      rcases eq_of_swapped_component hs hK hBK hBs hC N.2 hmoved' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact fun h => hKs (congrArg Subtype.val h)
      · intro h
        have h' : conjSub s (conjSub s K) = conjSub s K := congrArg Subtype.val h
        rw [conjSub_conjSub hs] at h'
        exact hKs h'.symm
  rw [hsupp, Finset.card_pair hne] at h4
  omega

end CFSG.EvenSporadicStandard.McLStd
