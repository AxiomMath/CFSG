module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenULin
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem le_of_rep_isometry [Finite V] {k : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * k)
    (bil : V → V → ZMod 2) (hadd : ∀ x y w, bil (x + y) w = bil x w + bil y w)
    (hnd : ∀ w, (∀ v, bil v w = 0) → w = 0) {G : Type*} [Group G] {D Q F X : Subgroup G}
    (ψ : ↥D →* (V ≃ₗ[ZMod 2] V)) (hQ : IsPGroup 2 Q) (hker : ∀ d : ↥D, ψ d = 1 → (d : G) ∈ Q)
    (hbil : ∀ d v w, bil (ψ d v) (ψ d w) = bil v w) (hFD : F ≤ D) (hXD : X ≤ D)
    (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 3 ^ k) (hX : IsPGroup 2 X)
    (hFX : F ≤ Subgroup.normalizer (X : Set G)) : X ≤ Q := by
  have hinjF : Function.Injective (ψ.comp (F.subgroupOf D).subtype) := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hfQ : ((f : ↥D) : G) ∈ Q := hker _ hf
    have hf3 : ((f : ↥D) : G) ^ 3 = 1 := hF.2 _ f.2
    obtain ⟨n, hn⟩ := hQ ⟨_, hfQ⟩
    have hn' : ((f : ↥D) : G) ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h1 : orderOf ((f : ↥D) : G) ∣ Nat.gcd 3 (2 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf3) (orderOf_dvd_of_pow_eq_one hn')
    rw [(Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at h1
    exact Subtype.ext (Subtype.ext (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)))
  have hrange : (ψ.comp (F.subgroupOf D).subtype).range = (F.subgroupOf D).map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEc : Nat.card ((F.subgroupOf D).map ψ) = 3 ^ k := by
    rw [← hrange, ← hFc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjF).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFD).toEquiv)
  have hX' : IsPGroup 2 (X.subgroupOf D) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXD).symm
  have hFX' : F.subgroupOf D ≤ Subgroup.normalizer ((X.subgroupOf D : Subgroup ↥D) : Set ↥D) :=
    fun f hf => Subgroup.mem_normalizer_iff.2 fun h =>
      Subgroup.mem_normalizer_iff.1 (hFX hf) (h : G)
  have hET : (F.subgroupOf D).map ψ ≤
      Subgroup.normalizer (((X.subgroupOf D).map ψ : Subgroup _) : Set _) :=
    (Subgroup.map_mono hFX').trans (Subgroup.le_normalizer_map ψ)
  have hbil' : ∀ K : Subgroup ↥D, ∀ g ∈ K.map ψ, ∀ v w, bil (g v) (g w) = bil v w := by
    intro K g hg v w
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact hbil d v w
  have hbot : (X.subgroupOf D).map ψ = ⊥ :=
    eq_bot_of_normalizes_isometry hdim bil hadd hnd ((hF.subgroupOf D).map ψ) hEc (hX'.map ψ) hET
      (hbil' _) (hbil' _)
  intro x hx
  have h1 : ψ ⟨x, hXD hx⟩ ∈ (X.subgroupOf D).map ψ :=
    Subgroup.mem_map_of_mem ψ (show (⟨x, hXD hx⟩ : ↥D) ∈ X.subgroupOf D from hx)
  rw [hbot, Subgroup.mem_bot] at h1
  exact hker _ h1

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
