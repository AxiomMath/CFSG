module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Congr

variable {G G' : Type*} [Group G] [Group G']

theorem congr_apply' (e : G ≃* G') (x : MulAut G) (y : G') :
    MulAut.congr e x y = e (x (e.symm y)) := rfl

theorem mem_fixSub_congr (e : G ≃* G') (x : MulAut G) (y : G') :
    y ∈ fixSub (MulAut.congr e x) ↔ e.symm y ∈ fixSub x := by
  rw [mem_fixSub, mem_fixSub, congr_apply']
  constructor
  · intro h
    have h1 := congrArg e.symm h
    simpa using h1
  · intro h
    rw [h]
    simp

theorem congr_symm_congr (e : G ≃* G') (x : MulAut G) :
    MulAut.congr e.symm (MulAut.congr e x) = x := by
  ext y
  simp [MulAut.congr_apply]

theorem congr_congr_symm (e : G ≃* G') (g : MulAut G') :
    MulAut.congr e (MulAut.congr e.symm g) = g := by
  ext y
  simp [MulAut.congr_apply]

theorem coreFreeAt_congr {p : ℕ} (e : G ≃* G') {x : MulAut G} (h : CoreFreeAt p x) :
    CoreFreeAt p (MulAut.congr e x) := by
  refine ⟨fun N hN hNn hcop => ?_, fun g hg hgx hfix => ?_⟩
  ·
    set M : Subgroup G := N.comap e.toMonoidHom with hM
    have hMfix : M ≤ fixSub x := by
      intro m hm
      have h1 : e m ∈ fixSub (MulAut.congr e x) := hN hm
      have h2 := (mem_fixSub_congr e x (e m)).1 h1
      simpa using h2
    have hMn : ∀ f ∈ fixSub x, ∀ n ∈ M, f * n * f⁻¹ ∈ M := by
      intro f hf n hn
      have hf' : e f ∈ fixSub (MulAut.congr e x) := by
        rw [mem_fixSub_congr]
        simpa using hf
      have := hNn (e f) hf' (e n) hn
      simpa [hM, Subgroup.mem_comap] using this
    have hMcop : Nat.Coprime p (Nat.card M) := by
      have : Nat.card M = Nat.card N := by
        have h1 : M = N.map e.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm e N
        rw [h1, Subgroup.card_map_of_injective e.symm.injective]
      rwa [this]
    have hM1 : M = ⊥ := h.1 M hMfix hMn hMcop
    refine eq_bot_iff.2 fun y hy => ?_
    have hy' : e.symm y ∈ M := by
      simpa [hM, Subgroup.mem_comap] using hy
    rw [hM1, Subgroup.mem_bot] at hy'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hy'
  ·
    set g₀ : MulAut G := MulAut.congr e.symm g with hg₀
    have hg₀ord : orderOf g₀ = orderOf g := MulEquiv.orderOf_eq (MulAut.congr e.symm) g
    have hgx' : g₀ * x = x * g₀ := by
      have := congrArg (MulAut.congr e.symm) hgx
      rwa [map_mul, map_mul, congr_symm_congr] at this
    have hfix₀ : ∀ t ∈ fixSub x, g₀ t = t := by
      intro t ht
      have ht' : e t ∈ fixSub (MulAut.congr e x) := by
        rw [mem_fixSub_congr]
        simpa using ht
      have h1 := hfix (e t) ht'
      rw [hg₀, congr_apply']
      simp [h1]
    have h1 : g₀ = 1 := h.2 g₀ (hg₀ord ▸ hg) hgx' hfix₀
    have h2 : g = MulAut.congr e g₀ := (congr_congr_symm e g).symm
    rw [h2, h1, map_one]

end Congr

section NoNormal

variable {K K' : Type*} [Group K] [Group K']

@[expose] def NoNormalCop (p : ℕ) (F : Subgroup K) : Prop :=
  ∀ N : Subgroup K, N ≤ F → (∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N) → Nat.Coprime p (Nat.card N) →
    N = ⊥

theorem noNormalCop_of_mulEquiv {p : ℕ} {F : Subgroup K} {F' : Subgroup K'} (e : ↥F ≃* ↥F')
    (h : NoNormalCop p F') : NoNormalCop p F := by
  intro N hN hNn hcop
  set N₁ : Subgroup ↥F := N.subgroupOf F with hN₁
  set N₂ : Subgroup ↥F' := N₁.map e.toMonoidHom with hN₂
  set N₃ : Subgroup K' := N₂.map F'.subtype with hN₃
  have hcard₁ : Nat.card N₁ = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hcard₂ : Nat.card N₂ = Nat.card N₁ := Subgroup.card_map_of_injective e.injective
  have hcard₃ : Nat.card N₃ = Nat.card N₂ := Subgroup.card_map_of_injective F'.subtype_injective
  have h3 : N₃ = ⊥ := by
    refine h N₃ (Subgroup.map_subtype_le _) ?_ (by rw [hcard₃, hcard₂, hcard₁]; exact hcop)
    rintro f hf _ ⟨_, ⟨n₁, hn₁, rfl⟩, rfl⟩
    obtain ⟨f', hf'⟩ : ∃ f' : ↥F', (f' : K') = f := ⟨⟨f, hf⟩, rfl⟩
    have hmem : ((e.symm f' : ↥F) : K) * (n₁ : K) * ((e.symm f' : ↥F) : K)⁻¹ ∈ N :=
      hNn _ (e.symm f').2 _ hn₁
    refine ⟨e ((e.symm f') * n₁ * (e.symm f')⁻¹), ⟨_, ?_, rfl⟩, ?_⟩
    · exact hmem
    · rw [← hf']
      simp
  refine eq_bot_iff.2 fun y hy => ?_
  have hy1 : (⟨y, hN hy⟩ : ↥F) ∈ N₁ := hy
  have hy3 : ((e ⟨y, hN hy⟩ : ↥F') : K') ∈ N₃ := ⟨_, ⟨_, hy1, rfl⟩, rfl⟩
  rw [h3, Subgroup.mem_bot] at hy3
  have : e ⟨y, hN hy⟩ = 1 := Subtype.ext hy3
  have h4 : (⟨y, hN hy⟩ : ↥F) = 1 := by simpa using e.injective (this.trans (map_one e).symm)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h4

theorem noNormalCop_of_simple {p : ℕ} (hp : 1 < p) {F : Subgroup K} (hF : IsSimpleGroup ↥F)
    (hdvd : p ∣ Nat.card F) : NoNormalCop p F := by
  intro N hN hNn hcop
  set N₁ : Subgroup ↥F := N.subgroupOf F with hN₁
  haveI : N₁.Normal := ⟨fun n hn x => by
    rw [hN₁, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn x.1 x.2 n.1 hn⟩
  rcases hF.eq_bot_or_eq_top_of_normal N₁ with h | h
  · refine eq_bot_iff.2 fun y hy => ?_
    have hy1 : (⟨y, hN hy⟩ : ↥F) ∈ N₁ := hy
    rw [h, Subgroup.mem_bot] at hy1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hy1
  · exfalso
    have hcard : Nat.card N = Nat.card F := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv, ← Subgroup.card_top (G := ↥F)]
      rw [← h]
    rw [hcard] at hcop
    exact (Nat.not_coprime_of_dvd_of_dvd hp dvd_rfl hdvd) hcop

@[expose] def FaithfulAt (p : ℕ) (x : MulAut K) : Prop :=
  ∀ g : MulAut K, Nat.Coprime p (orderOf g) → g * x = x * g → (∀ t ∈ fixSub x, g t = t) → g = 1

theorem coreFreeAt_of_parts {p : ℕ} {x : MulAut K} (hA : NoNormalCop p (fixSub x))
    (hB : FaithfulAt p x) : CoreFreeAt p x := ⟨hA, hB⟩

end NoNormal

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
