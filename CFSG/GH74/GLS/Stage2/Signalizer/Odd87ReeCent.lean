module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeMaximal
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Blueprint CFSG.LieType.Ree CFSG.Walter.Ree.Model
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ree_model_data_pos
    {T : Type} [Group T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.G2.prime),
      1 ≤ a ∧ Nat.card K = 3 ^ (2 * a + 1) ∧ Nonempty (T ≃* ↥(ReeTag.G2.reeGamma K a)) := by
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T 3 f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  exact ⟨a', K, inferInstance, inferInstance, this, ha, by rw [hK, hfa], ⟨E⟩⟩

theorem ree_involution_centralizer
    {T : Type} [Group T] [Finite T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f) {k : T}
    (hk : orderOf k = 2) :
    IsCoatom (centralizer ({k} : Set T)) ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Y : Subgroup T, Y ≤ centralizer ({k} : Set T) →
      (∀ c ∈ centralizer ({k} : Set T), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) → IsPGroup p ↥Y → Y = ⊥ := by
  classical
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ := ree_model_data_pos h
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have hfinΓ : Finite ↥(ReeTag.G2.reeGamma K a) := Finite.of_equiv T e.toEquiv
  set J := smallReeJTHyp ha hK with hJ
  have hek : orderOf (((e k : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hk
  obtain ⟨g, hgΓ, hg⟩ := (small_Ree_prime_field_involution_fusion a K hK w₀ hw₀).2.2.2.2.2
    _ (e k).2 hek
  let g' : ↥(ReeTag.G2.reeGamma K a) := ⟨g, hgΓ⟩
  let ψ : T ≃* ↥(ReeTag.G2.reeGamma K a) := e.trans (MulAut.conj g')
  have hψk : ψ k = J.t := by
    apply Subtype.ext
    show g * ((e k : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) * g⁻¹ = _
    rw [hg]; rfl
  have hco : IsCoatom (centralizer ({J.t} : Set ↥(ReeTag.G2.reeGamma K a))) :=
    CFSG.ComponentClassification.LiteratureLocal.SmallRee.centralizer_torusInv_isCoatom ha hK
  refine ⟨isCoatom_centralizer_of_equiv ψ k (hψk ▸ hco), ?_⟩
  intro p hp hp2 Y hY1 hY2 hY3
  have hmapC : (centralizer ({k} : Set T)).map ψ.toMonoidHom =
      centralizer ({J.t} : Set ↥(ReeTag.G2.reeGamma K a)) := by
    rw [CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' ψ k, hψk]
  set Y' := Y.map ψ.toMonoidHom with hY'
  have hY'le : Y' ≤ zpowers J.t ⊔ J.F := by
    rw [← J.centralizer_eq, ← hmapC]; exact Subgroup.map_mono hY1
  have hY'norm : ∀ c ∈ centralizer ({J.t} : Set ↥(ReeTag.G2.reeGamma K a)), ∀ y ∈ Y',
      c * y * c⁻¹ ∈ Y' := by
    intro c hc y hy
    rw [← hmapC] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    exact ⟨c₀ * y₀ * c₀⁻¹, hY2 c₀ hc₀ y₀ hy₀, by simp⟩
  have hcomm : ∀ x ∈ J.F, x * J.t = J.t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (J.le_centralizer hx)
  have hYF : Y' ≤ J.F := by
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨m, hm⟩ := hY3 ⟨y₀, hy₀⟩
    have hym : (ψ y₀) ^ (p ^ m) = 1 := by
      have h1 : y₀ ^ (p ^ m) = 1 := congrArg Subtype.val hm
      rw [← map_pow, h1, map_one]
    exact mem_of_pPow_of_sup J.orderOf_t hcomm J.t_not_mem hp hp2 (hY'le ⟨y₀, hy₀, rfl⟩) hym
  have hF := CFSG.Walter.JT.psl2Facts J.F J.iso (by show (3 : ℕ) ≠ 2; decide) J.five_lt
  have hsimple : IsSimpleGroup ↥J.F := hF.simple
  have hnormF : (Y'.subgroupOf J.F).Normal := by
    refine ⟨fun y hy x => ?_⟩
    have hyY' : (y : ↥(ReeTag.G2.reeGamma K a)) ∈ Y' := hy
    have hxC : (x : ↥(ReeTag.G2.reeGamma K a)) ∈ centralizer ({J.t} : Set _) := by
      rw [J.centralizer_eq]; exact Subgroup.mem_sup_right x.2
    show (x : ↥(ReeTag.G2.reeGamma K a)) * (y : ↥(ReeTag.G2.reeGamma K a)) *
      (x : ↥(ReeTag.G2.reeGamma K a))⁻¹ ∈ Y'
    exact hY'norm _ hxC _ hyY'
  rcases hsimple.eq_bot_or_eq_top_of_normal (Y'.subgroupOf J.F) with h1 | h1
  · have hY'bot : Y' = ⊥ := by
      rw [eq_bot_iff_forall]
      intro y hy
      have hyF := hYF hy
      have : (⟨y, hyF⟩ : ↥J.F) ∈ Y'.subgroupOf J.F := hy
      rw [h1] at this
      have := (Subgroup.mem_bot).mp this
      exact congrArg Subtype.val this
    exact (Subgroup.map_eq_bot_iff_of_injective Y ψ.injective).mp hY'bot
  · exfalso
    have hFle : J.F ≤ Y' := by
      intro x hx
      have : (⟨x, hx⟩ : ↥J.F) ∈ Y'.subgroupOf J.F := by rw [h1]; exact Subgroup.mem_top _
      exact this
    have hpY' : IsPGroup p ↥Y' := hY3.map ψ.toMonoidHom
    have hpF : IsPGroup p ↥J.F := IsPGroup.to_le hpY' hFle
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hpF)
    have h2 : 2 ∣ Nat.card ↥J.F := by
      rw [hF.card]
      exact two_dvd_psl_card _ hF.odd_p.pow
    rw [hn] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    exact hp2 this.symm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
