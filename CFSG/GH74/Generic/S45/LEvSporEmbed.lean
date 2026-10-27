module

public import CFSG.GH74.Generic.S45.LEvSporCorr
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

open Subgroup CFSG CFSG.Sporadic.SmallOddCore

namespace CFSG.GH74.Generic.S45

theorem exists_corr_equiv {M : Type*} [Group M] [Finite M] {P R : Subgroup M} (hA : AutModel P R)
    {G : Type*} [Group G] [Finite G] {N H : Subgroup G} (hHN : H ≤ N)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H)
    (hcent : ∀ n ∈ N, (∀ h ∈ H, n * h = h * n) → n = 1)
    (hcard : Nat.card ↥N = Nat.card ↥R) (e : ↥H ≃* ↥P) :
    ∃ ψ : ↥N ≃* ↥R, Corr ψ H P := by
  let S : Subgroup ↥N := H.subgroupOf N
  have hSn : S.Normal := ⟨fun s hs g => by
    have : ((g * s * g⁻¹ : ↥N) : G) = (g : G) * (s : G) * (g : G)⁻¹ := rfl
    rw [Subgroup.mem_subgroupOf, this]
    exact hnorm g g.2 s hs⟩
  have := hSn
  let θ : ↥S ≃* ↥P := (Subgroup.subgroupOfEquivOfLe hHN).trans e
  have hC : centralizer (S : Set ↥N) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    rw [mem_centralizer_iff] at hn
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hcent n n.2 fun h hh => ?_)
    have := hn ⟨h, hHN hh⟩ hh
    exact congrArg Subtype.val this.symm
  have hι := hA.embed_injective S θ hC
  set ι := hA.embed S θ with hιdef
  have hrange : ι.range = R := by
    refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨n, hn⟩ => hn ▸ hA.embed_mem S θ n) ?_
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).le
  let ψ : ↥N ≃* ↥R := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  have hψ : ∀ n : ↥N, ((ψ n : ↥R) : M) = ι n := fun n => rfl
  refine ⟨ψ, hHN, hA.le, fun n => ?_⟩
  rw [hψ]
  constructor
  · intro hn
    have hs : n ∈ S := hn
    have := hA.embed_coe S θ ⟨n, hs⟩
    rw [hιdef]
    exact this ▸ (θ ⟨n, hs⟩).2
  · intro hn
    set s : ↥S := θ.symm ⟨ι n, hn⟩ with hs
    have h1 : ι (s : ↥N) = ι n := by
      have := hA.embed_coe S θ s
      rw [hs, MulEquiv.apply_symm_apply] at this
      exact this
    have h2 : (s : ↥N) = n := hι h1
    have h3 : ((s : ↥N) : G) ∈ H := s.2
    rw [h2] at h3
    exact h3

end CFSG.GH74.Generic.S45
