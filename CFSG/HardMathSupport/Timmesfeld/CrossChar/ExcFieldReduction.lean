module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isSubnormal_subgroupOf_of_chain₂ {M : Type*} [Group M] {A B C : Subgroup M}
    (hAB : A ≤ B) (hBC : B ≤ C) (h1 : ∀ y ∈ B, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (h2 : ∀ y ∈ C, ∀ b ∈ B, y * b * y⁻¹ ∈ B) : (A.subgroupOf C).IsSubnormal := by
  have hB : (B.subgroupOf C).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa [Subgroup.mem_subgroupOf] using h2 g.1 g.2 n.1 hn
  refine Subgroup.IsSubnormal.step _ _ (fun z hz => hAB hz) hB ?_
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (n : ↥C).1 ∈ A := hn
  simpa [Subgroup.mem_subgroupOf] using h1 g.1.1 g.2 (n : ↥C).1 hn'

@[expose] def FieldCoreAt (p : ℕ) {K : Type*} [Group K] (x : MulAut K) : Prop :=
  ∃ T : Subgroup K, T ≤ fixSub x ∧ (∀ f ∈ fixSub x, ∀ t ∈ T, f * t * f⁻¹ ∈ T) ∧
    CFSG.IsQuasisimple T ∧ ¬ Nat.Coprime p (Nat.card T) ∧
    ∀ g : MulAut K, Nat.Coprime p (orderOf g) → g * x = x * g → (∀ t ∈ T, g t = t) → g = 1

section Component

variable {K : Type*} [Group K]

theorem conj_commute_of_mem_fixSub {x : MulAut K} {t : K} (ht : t ∈ fixSub x) :
    x * MulAut.conj t = MulAut.conj t * x := by
  have h := mul_conj_mul_inv x t
  rw [mem_fixSub.1 ht] at h
  calc x * MulAut.conj t = (x * MulAut.conj t * x⁻¹) * x := by group
    _ = MulAut.conj t * x := by rw [h]

theorem isSubnormal_conj_of_normal_in_fixSub {x : MulAut K} {H : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) {T : Subgroup K} (hTF : T ≤ fixSub x)
    (hTn : ∀ f ∈ fixSub x, ∀ t ∈ T, f * t * f⁻¹ ∈ T)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) :
    ((T.map (MulAut.conj : K →* MulAut K)).subgroupOf
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))).IsSubnormal := by
  refine isSubnormal_subgroupOf_of_chain₂
    (B := (fixSub x).map (MulAut.conj : K →* MulAut K)) ?_ ?_ ?_ ?_
  · exact Subgroup.map_mono hTF
  · rintro _ ⟨f, hf, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hH ⟨f, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (conj_commute_of_mem_fixSub hf).symm
  · rintro _ ⟨f, hf, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨f * t * f⁻¹, hTn f hf t ht, by simp [map_mul, map_inv]⟩
  · rintro y hy _ ⟨f, hf, rfl⟩
    have hyx : y * x = x * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
    refine ⟨y f, ?_, (mul_conj_mul_inv y f).symm⟩
    change x (y f) = y f
    calc x (y f) = (x * y) f := rfl
      _ = (y * x) f := by rw [hyx]
      _ = y (x f) := rfl
      _ = y f := by rw [mem_fixSub.1 hf]

theorem isComponent_conj_of_fieldCore {x : MulAut K} {H : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) {T : Subgroup K} (hTF : T ≤ fixSub x)
    (hTn : ∀ f ∈ fixSub x, ∀ t ∈ T, f * t * f⁻¹ ∈ T) (hTq : CFSG.IsQuasisimple T)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) :
    CFSG.IsComponent ((T.map (MulAut.conj : K →* MulAut K)).subgroupOf
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))) := by
  refine ⟨?_, isSubnormal_conj_of_normal_in_fixSub hH hTF hTn hinj⟩
  have hTC : T.map (MulAut.conj : K →* MulAut K) ≤
      H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)) := by
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (conj_commute_of_mem_fixSub (hTF ht)).symm
  have e1 := T.equivMapOfInjective (MulAut.conj : K →* MulAut K) hinj
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (e1.trans (Subgroup.subgroupOfEquivOfLe hTC).symm) hTq

end Component

section Balance

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem localDeltaIn_eq_bot_of_fieldCore (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H D : Subgroup (MulAut K)} (hH : innerAut K ≤ H) {x : MulAut K} (hx : x ∈ D) (hx1 : x ≠ 1)
    (hfc : FieldCoreAt p x) : localDeltaIn p H D = ⊥ := by
  obtain ⟨T, hTF, hTn, hTq, hTp, hfaith⟩ := hfc
  have hTC : T.map (MulAut.conj : K →* MulAut K) ≤
      H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)) := by
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (conj_commute_of_mem_fixSub (hTF ht)).symm
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  exact hfaith g (coprime_orderOf_of_mem_localDeltaIn hp hg hx hx1)
    (commute_of_mem_localDeltaIn hg hx)
    fun t ht => mem_fixSub.1 (le_fixSub_of_component hp hinj hg hx hx1 hTC
      (isComponent_conj_of_fieldCore hH hTF hTn hTq hinj) hTp ht)

theorem isLocallyBalancedAbs_of_fieldCore (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hin : ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 3 →
      D ≤ innerAut K → False)
    (hfc : ∀ x : MulAut K, x ^ p = 1 → x ∉ innerAut K → FieldCoreAt p x) :
    IsLocallyBalancedAbs p 3 K := by
  intro D hD hcard H hH _
  by_cases hDin : D ≤ innerAut K
  · exact (hin D hD hcard hDin).elim
  · obtain ⟨x, hxD, hxin⟩ := SetLike.not_le_iff_exists.1 hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hxD hx1 (hfc x (hD.2 x hxD) hxin)

end Balance


end CFSG.HardMathSupport.Timmesfeld.CrossChar
