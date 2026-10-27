module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Balance

@[expose] def CoreFreeAt (p : ℕ) {K : Type*} [Group K] (x : MulAut K) : Prop :=
  (∀ N : Subgroup K, N ≤ fixSub x → (∀ f ∈ fixSub x, ∀ n ∈ N, f * n * f⁻¹ ∈ N) →
      Nat.Coprime p (Nat.card N) → N = ⊥) ∧
    ∀ g : MulAut K, Nat.Coprime p (orderOf g) → g * x = x * g → (∀ t ∈ fixSub x, g t = t) →
      g = 1

section Invariance

variable {K : Type*} [Group K] {p : ℕ}

theorem fixSub_inv_eq (x : MulAut K) : fixSub x⁻¹ = fixSub x := by
  ext t
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro h
    calc x t = x (x⁻¹ t) := by rw [h]
      _ = t := MulAut.apply_inv_self K x t
  · intro h
    calc x⁻¹ t = x⁻¹ (x t) := by rw [h]
      _ = t := MulAut.inv_apply_self K x t

theorem mem_fixSub_conj_iff (β x : MulAut K) (t : K) :
    t ∈ fixSub (β * x * β⁻¹) ↔ β⁻¹ t ∈ fixSub x := by
  rw [mem_fixSub, mem_fixSub, MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro h
    calc x (β⁻¹ t) = β⁻¹ (β (x (β⁻¹ t))) := (MulAut.inv_apply_self K β _).symm
      _ = β⁻¹ t := by rw [h]
  · intro h
    rw [h, MulAut.apply_inv_self]

theorem CoreFreeAt.inv {x : MulAut K} (h : CoreFreeAt p x) : CoreFreeAt p x⁻¹ := by
  rw [CoreFreeAt, fixSub_inv_eq]
  refine ⟨h.1, fun g hg hgx hfix => h.2 g hg ?_ hfix⟩
  calc g * x = x * (x⁻¹ * g) * x := by group
    _ = x * (g * x⁻¹) * x := by rw [← hgx]
    _ = x * g := by group

theorem CoreFreeAt.conj {x : MulAut K} (h : CoreFreeAt p x) (β : MulAut K) :
    CoreFreeAt p (β * x * β⁻¹) := by
  refine ⟨fun N hN hNn hcop => ?_, fun g hg hgx hfix => ?_⟩
  · have hN' := h.1 (N.map (β⁻¹ : MulAut K).toMonoidHom) ?_ ?_ ?_
    · have hinj : Function.Injective (β⁻¹ : MulAut K).toMonoidHom := (β⁻¹ : MulAut K).injective
      exact (Subgroup.map_eq_bot_iff_of_injective N hinj).1 hN'
    · rintro _ ⟨n, hn, rfl⟩
      exact (mem_fixSub_conj_iff β x n).1 (hN hn)
    · rintro f hf _ ⟨n, hn, rfl⟩
      refine ⟨β f * n * (β f)⁻¹, hNn _ ((mem_fixSub_conj_iff β x _).2 ?_) n hn, ?_⟩
      · rwa [MulAut.inv_apply_self]
      · change β⁻¹ (β f * n * (β f)⁻¹) = f * β⁻¹ n * f⁻¹
        rw [map_mul, map_mul, map_inv, MulAut.inv_apply_self]
    · rwa [Subgroup.card_map_of_injective (β⁻¹ : MulAut K).injective]
  · have hord : orderOf (β⁻¹ * g * β) = orderOf g := by
      refine SemiconjBy.orderOf_eq β ?_
      change β * (β⁻¹ * g * β) = g * β
      group
    have h1 := h.2 (β⁻¹ * g * β) (hord ▸ hg) ?_ ?_
    · calc g = β * (β⁻¹ * g * β) * β⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · calc β⁻¹ * g * β * x = β⁻¹ * (g * (β * x * β⁻¹)) * β := by group
        _ = β⁻¹ * ((β * x * β⁻¹) * g) * β := by rw [hgx]
        _ = x * (β⁻¹ * g * β) := by group
    · intro t ht
      have hβt : β t ∈ fixSub (β * x * β⁻¹) := by
        rw [mem_fixSub_conj_iff, MulAut.inv_apply_self]
        exact ht
      change β⁻¹ (g (β t)) = t
      rw [hfix _ hβt, MulAut.inv_apply_self]

theorem coreFreeAt_conj_iff (x β : MulAut K) :
    CoreFreeAt p (β * x * β⁻¹) ↔ CoreFreeAt p x := by
  refine ⟨fun h => ?_, fun h => h.conj β⟩
  have h1 := h.conj β⁻¹
  rwa [show β⁻¹ * (β * x * β⁻¹) * β⁻¹⁻¹ = x by group] at h1

end Invariance

section Balance

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem gLAPPrimeCoreOf_eq_bot_of_coreFree (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {H : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) {x : MulAut K} (h : CoreFreeAt p x) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K))) = ⊥ := by
  set C := H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)) with hCdef
  set M := GLAPPrimeCoreOf p C with hMdef
  have hMC : M ≤ C := gLAPPrimeCoreOf_le_self' C
  have hMn : ∀ g ∈ C, ∀ m ∈ M, g * m * g⁻¹ ∈ M := gLAPPrimeCoreOf_conj_mem'
  have hMp : Nat.Coprime p (Nat.card M) := coprime_card_gLAPPrimeCoreOf' hp C
  have hcomm : ∀ m ∈ M, m * x = x * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hMC hm)).2
  have hconjC : ∀ f ∈ fixSub x, MulAut.conj f ∈ C := fun f hf =>
    Subgroup.mem_inf.2 ⟨hH ⟨f, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2
      (conj_commute_of_mem_fixSub hf).symm⟩
  set N : Subgroup K := M.comap (MulAut.conj : K →* MulAut K) with hNdef
  have hNfix : N ≤ fixSub x := fun k hk => mem_fixSub_of_commute hinj (hcomm _ hk).symm
  have hNn : ∀ f ∈ fixSub x, ∀ n ∈ N, f * n * f⁻¹ ∈ N := by
    intro f hf n hn
    change MulAut.conj (f * n * f⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hMn _ (hconjC f hf) _ hn
  have hNp : Nat.Coprime p (Nat.card N) := by
    have hle : N.map (MulAut.conj : K →* MulAut K) ≤ M := Subgroup.map_comap_le _ _
    have hdvd : Nat.card N ∣ Nat.card M := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact Subgroup.card_dvd_of_le hle
    exact hMp.coprime_dvd_right hdvd
  have hN : N = ⊥ := h.1 N hNfix hNn hNp
  refine eq_bot_iff.2 fun m hm => ?_
  rw [Subgroup.mem_bot]
  refine h.2 m (hMp.coprime_dvd_right (Subgroup.orderOf_dvd_natCard M hm)) (hcomm m hm) ?_
  intro f hf
  have hmf : m f * f⁻¹ ∈ N := by
    change MulAut.conj (m f * f⁻¹) ∈ M
    rw [map_mul, map_inv, ← mul_conj_mul_inv]
    have h1 : MulAut.conj f * m⁻¹ * (MulAut.conj f)⁻¹ ∈ M :=
      hMn _ (hconjC f hf) _ (inv_mem hm)
    have h2 := mul_mem hm h1
    rwa [show m * (MulAut.conj f * m⁻¹ * (MulAut.conj f)⁻¹) =
      m * MulAut.conj f * m⁻¹ * (MulAut.conj f)⁻¹ by group] at h2
  rw [hN, Subgroup.mem_bot] at hmf
  exact mul_inv_eq_one.1 hmf

theorem localDeltaIn_eq_bot_of_coreFree (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {H D : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) {x : MulAut K} (hx : x ∈ D) (hx1 : x ≠ 1) (h : CoreFreeAt p x) :
    localDeltaIn p H D = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  have h1 := le_core_of_mem_localDeltaIn hg hx hx1
  rwa [gLAPPrimeCoreOf_eq_bot_of_coreFree hp hinj hH h] at h1

theorem isLocallyBalancedAbs_of_coreFree (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hin : ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 3 →
      D ≤ innerAut K → False)
    (hcf : ∀ x : MulAut K, x ^ p = 1 → x ∉ innerAut K → CoreFreeAt p x) :
    IsLocallyBalancedAbs p 3 K := by
  intro D hD hcard H hH _
  by_cases hDin : D ≤ innerAut K
  · exact (hin D hD hcard hDin).elim
  · obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    exact localDeltaIn_eq_bot_of_coreFree hp hinj hH hxD hx1 (hcf x (hD.2 x hxD) hxin)

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
