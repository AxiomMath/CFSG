module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial (SignalizerTrivialOn)

theorem exists_sylow_inf_normal {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (K : Subgroup X) [K.Normal] (R : Sylow p X) :
    ∃ P : Sylow p K, (P : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K := by
  have hRX : IsSylowOf p (R : Subgroup X) (⊤ : Subgroup X) := by
    rw [isSylowOf_iff]
    refine ⟨le_top, R.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact R.not_dvd_index
  have hRK := hRX.inf_of_le_normalizer (N := K) le_top (by
    intro x _
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top x)
  exact hRK

theorem signalizerTrivialX_of_on {T : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} (hp : p.Prime)
    (hon : ∀ (K : Type) [Group K] [Finite K], T p K → SignalizerTrivialOn p K) :
    SignalizerTrivialX T p := by
  intro X _ _ K hK R W hW hRK
  obtain ⟨hKn, hKc, hT⟩ := hK
  haveI : K.Normal := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := exists_sylow_inf_normal K R
  let φ : X →* MulAut K := MulAut.conjNormal
  have hφ : ∀ x : X, ∀ k : K, ((φ x k : K) : X) = x * k * x⁻¹ := fun x k => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : x ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro k hk
      have := congrArg (fun a : MulAut K => ((a ⟨k, hk⟩ : K) : X)) hx
      simp only [hφ, MulAut.one_apply] at this
      calc k * x = (x * k * x⁻¹) * x := by rw [this]
        _ = x * k := by group
    rw [hKc] at this
    exact Subgroup.mem_bot.mp this
  have hcard : Nat.card (W.map φ) = Nat.card W := Subgroup.card_map_of_injective (K := W) hφinj
  have hcop : Nat.Coprime p (Nat.card (W.map φ)) := by rw [hcard]; exact hW
  have hnorm : ∀ g ∈ (P : Subgroup K), ∀ w ∈ W.map φ,
      MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ W.map φ := by
    intro g hg w hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hgR : (g : X) ∈ (R : Subgroup X) ⊓ K := by
      rw [← hP]
      exact ⟨g, hg, rfl⟩
    have hgN : (g : X) ∈ normalizer (W : Set X) := hRK hgR
    refine ⟨(g : X) * y * (g : X)⁻¹, (Subgroup.mem_normalizer_iff.mp hgN y).mp hy, ?_⟩
    ext k
    simp only [hφ, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group
  have hbot := hon K hT P (W.map φ) hcop hnorm
  rw [eq_bot_iff]
  intro x hx
  have : φ x ∈ W.map φ := ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (hφinj (by rw [this, map_one]))

theorem eq_one_of_mem_two_pgroup_inf {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {V S : Subgroup X} (hV : IsPGroup 2 V) (hS : IsPGroup p S) {c : X}
    (hcV : c ∈ V) (hcS : c ∈ S) : c = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hV ⟨c, hcV⟩
  obtain ⟨b, hb⟩ := hS ⟨c, hcS⟩
  have h1 : c ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have h2 : c ^ p ^ b = 1 := congrArg Subtype.val hb
  have h3 : orderOf c ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf c ∣ p ^ b := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have : orderOf c ∣ 1 := hcop ▸ Nat.dvd_gcd h3 h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem lemma45Facts_of_inner {T : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}
    (hcore : ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), IsAutOverType T p K →
      ∀ (R : Sylow p X) (U₀ : Subgroup X), U₀ ≤ (R : Subgroup X) → IsElemAbelian p U₀ →
        Nat.card U₀ = p → Shape K (R : Subgroup X) U₀ →
        U₀ ≤ K ∧ ∃ V : Subgroup X, V ≤ K ∧ IsPGroup 2 V ∧ U₀ ≤ normalizer (V : Set X) ∧
          ∃ v ∈ V, ∃ u ∈ U₀, u * v ≠ v * u) :
    Lemma45Facts T p Shape := by
  intro X _ _ K hK R U₀ hUR hUe hUc hshape
  obtain ⟨hUK, V, hVK, hV2, hVN, v, hv, u, hu, hne⟩ := hcore X K hK R U₀ hUR hUe hUc hshape
  refine ⟨V, hVK, hV2, hVN, ?_⟩
  intro hVS
  apply hne
  have hS : IsPGroup p ((R : Subgroup X) ⊓ K : Subgroup X) := R.isPGroup'.to_inf_left
  have huS : u ∈ (R : Subgroup X) ⊓ K := ⟨hUR hu, hUK hu⟩
  have hvN : v ∈ normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) := hVS hv
  have h1 : v * u * v⁻¹ ∈ (R : Subgroup X) ⊓ K := (Subgroup.mem_normalizer_iff.mp hvN u).mp huS
  have h2 : (v * u * v⁻¹) * u⁻¹ ∈ (R : Subgroup X) ⊓ K := mul_mem h1 (inv_mem huS)
  have hvV : v ∈ V := hv
  have huN : u ∈ normalizer (V : Set X) := hVN hu
  have h3 : u * v⁻¹ * u⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp huN v⁻¹).mp (inv_mem hvV)
  have h4 : (v * u * v⁻¹) * u⁻¹ ∈ V := by
    have : (v * u * v⁻¹) * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
    rw [this]
    exact mul_mem hvV h3
  have h5 := eq_one_of_mem_two_pgroup_inf hp hp2 hV2 hS h4 h2
  have h6 : v * u * v⁻¹ = u := by
    have := mul_inv_eq_one.mp h5
    exact this
  calc u * v = v * u * v⁻¹ * v := by rw [h6]
    _ = v * u := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
