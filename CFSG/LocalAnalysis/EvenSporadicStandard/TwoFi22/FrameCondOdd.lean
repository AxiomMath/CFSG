module

public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24Connected

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open CFSG.EvenSmallLie.ThreeTransposition CFSG.Fischer Subgroup

variable {G : Type} [Group G]

@[expose, instance_reducible] def conjSetAction (K : Subgroup G) (Ω : Set G)
    (h : ∀ k ∈ K, ∀ x ∈ Ω, k * x * k⁻¹ ∈ Ω) : MulAction K Ω where
  smul k s := ⟨k * s * (k : G)⁻¹, h k k.2 s s.2⟩
  one_smul s := Subtype.ext (by
    show ((1 : K) : G) * (s : G) * ((1 : K) : G)⁻¹ = s
    simp)
  mul_smul k k' s := Subtype.ext (by
    show ((k * k' : K) : G) * (s : G) * ((k * k' : K) : G)⁻¹ =
      (k : G) * ((k' : G) * s * (k' : G)⁻¹) * (k : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem exists_fixed_of_odd_ncard {K : Subgroup G} (hK : IsPGroup 2 K) {Ω : Set G}
    (h : ∀ k ∈ K, ∀ x ∈ Ω, k * x * k⁻¹ ∈ Ω) (hodd : Odd Ω.ncard) :
    ∃ x ∈ Ω, ∀ k ∈ K, k * x * k⁻¹ = x := by
  let _ := conjSetAction K Ω h
  have hnd : ¬ 2 ∣ Nat.card Ω := by
    rw [Nat.card_coe_set_eq]
    exact fun h2 => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  obtain ⟨⟨x, hx⟩, hfix⟩ := hK.nonempty_fixed_point_of_prime_not_dvd_card Ω hnd
  refine ⟨x, hx, fun k hk => ?_⟩
  have h1 : (⟨k, hk⟩ : K) • (⟨x, hx⟩ : Ω) = ⟨x, hx⟩ := hfix ⟨k, hk⟩
  exact congrArg Subtype.val h1

theorem exists_conj_mem_of_le [Finite G] {Y : Subgroup G} (T : Sylow 2 G)
    (hTY : (T : Subgroup G) ≤ Y) {x : G} (hxY : x ∈ Y) (hx2 : x * x = 1) :
    ∃ y ∈ Y, y * x * y⁻¹ ∈ T := by
  obtain ⟨Q, hQ⟩ := exists_sylow_of_pairwise (G := Y) (S := {⟨x, hxY⟩})
    (by rintro _ rfl _ rfl; rfl) (by rintro _ rfl; exact Subtype.ext hx2)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y Q (T.subtype hTY)
  have hmem : y * ⟨x, hxY⟩ * y⁻¹ ∈ ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) := by
    rw [← hy]
    show y * ⟨x, hxY⟩ * y⁻¹ ∈ (y • Q : Sylow 2 Y)
    rw [mem_smul_sylow_iff, show y⁻¹ * (y * ⟨x, hxY⟩ * y⁻¹) * y = ⟨x, hxY⟩ by group]
    exact hQ rfl
  rw [Sylow.coe_subtype, mem_subgroupOf] at hmem
  exact ⟨y, y.2, hmem⟩

theorem fixed_of_component_of_odd [Finite G] {D : Set G}
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (T : Sylow 2 G)
    (hcomm : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, a * b = b * a)
    (hodd : Odd ((T : Set G) ∩ D).ncard) :
    ∀ Δ : (commGraph D).ConnectedComponent,
      ∀ x ∈ Subgroup.normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f := by
  have hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g _ hx =>
    Timmesfeld.conj_mem_of_isClass hclass g hx
  obtain ⟨ω, hωT, hωD⟩ : ((T : Set G) ∩ D).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (fun h => by rw [h] at hodd; exact absurd hodd (by decide))
  have hΩΔ : (T : Set G) ∩ D ⊆ compSet D ω := fun s hs =>
    mem_compSet_of_commute hωD hs.2 (hcomm ω ⟨hωT, hωD⟩ s hs)
  have hTN : (T : Subgroup G) ≤ normalizer (compSet D ω) := by
    intro y hy
    rw [mem_normalizer_compSet_iff hDinv hωD]
    exact hΩΔ ⟨T.mul_mem (T.mul_mem hy hωT) (T.inv_mem hy), hDinv y ω hωD⟩
  have key : ∀ x ∈ normalizer (compSet D ω), x * x = 1 → ∃ f ∈ compSet D ω, x * f * x⁻¹ = f := by
    intro x hx hx2
    obtain ⟨y, hy, hyT⟩ := exists_conj_mem_of_le T hTN hx hx2
    obtain ⟨e, he, hfix⟩ := exists_fixed_of_odd_ncard (K := (T : Subgroup G)) T.isPGroup'
      (Ω := (T : Set G) ∩ D)
      (fun k hk s hs => ⟨T.mul_mem (T.mul_mem hk hs.1) (T.inv_mem hk), hDinv k s hs.2⟩) hodd
    refine ⟨y⁻¹ * e * y⁻¹⁻¹, (mem_set_normalizer_iff.1 (inv_mem hy) e).1 (hΩΔ he), ?_⟩
    have h1 := hfix _ hyT
    calc x * (y⁻¹ * e * y⁻¹⁻¹) * x⁻¹
        = y⁻¹ * ((y * x * y⁻¹) * e * (y * x * y⁻¹)⁻¹) * y⁻¹⁻¹ := by group
      _ = y⁻¹ * e * y⁻¹⁻¹ := by rw [h1]
  intro Δ
  induction Δ using SimpleGraph.ConnectedComponent.ind with
  | h v =>
  obtain ⟨v, hv⟩ := v
  intro x hx hx2
  rw [image_supp_connectedComponentMk hv] at hx ⊢
  obtain ⟨c, rfl⟩ := isConj_iff.1 (Timmesfeld.isConj_of_isClass hclass hωD hv)
  have hx2' : x * x = 1 := mul_self_of_orderOf hx2
  have hct : c⁻¹ * (c * ω * c⁻¹) * c⁻¹⁻¹ = ω := by group
  have hx' : c⁻¹ * x * c ∈ normalizer (compSet D ω) := by
    rw [mem_normalizer_compSet_iff hDinv hωD]
    have h1 := (mem_normalizer_compSet_iff hDinv hv x).1 hx
    have h2 := conj_mem_compSet hDinv c⁻¹ h1
    rw [hct] at h2
    rwa [show c⁻¹ * (x * (c * ω * c⁻¹) * x⁻¹) * c⁻¹⁻¹ = c⁻¹ * x * c * ω * (c⁻¹ * x * c)⁻¹ by
      group] at h2
  have hx'2 : c⁻¹ * x * c * (c⁻¹ * x * c) = 1 := by
    rw [show c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c by group, hx2', mul_one,
      inv_mul_cancel]
  obtain ⟨f, hf, hfix⟩ := key _ hx' hx'2
  refine ⟨c * f * c⁻¹, conj_mem_compSet hDinv c hf, ?_⟩
  calc x * (c * f * c⁻¹) * x⁻¹ = c * ((c⁻¹ * x * c) * f * (c⁻¹ * x * c)⁻¹) * c⁻¹ := by group
    _ = c * f * c⁻¹ := by rw [hfix]

end CFSG.EvenSporadicStandard.TwoFi22
