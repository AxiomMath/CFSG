module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Alt6Count
public import CFSG.RankThree.Native.ONTripleK0
public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.RankThree.Native.ONThreeCentralizer
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TripleCoverON

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple CFSG.Blueprint Subgroup
open CFSG.RankThree.PartTwo.Sec21

section Embedding


theorem exists_alt6_embedding {X : Type*} [Group X] (φ : GM →* X) (hker : φ.ker = zpowers zG) :
    ∃ ι : alternatingGroup (Fin 6) →* X, Function.Injective ι ∧
      ∀ g, ι g ∈ centralizer ({φ (xG 0)} : Set X) := by
  let ψ : K0G →* alternatingGroup (Fin 6) :=
    actK.codRestrict (alternatingGroup (Fin 6)) (fun k => by
      rw [← range_actK]; exact ⟨k, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro g
    have : (g : Equiv.Perm (Fin 6)) ∈ actK.range := by rw [range_actK]; exact g.2
    obtain ⟨k, hk⟩ := this
    exact ⟨k, Subtype.ext hk⟩
  have hψker : ∀ k, ψ k = 1 ↔ actK k = 1 := fun k => by
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  let φK : K0G →* X := φ.comp K0G.subtype
  have hz : ∀ n : ℤ, actK ((⟨zG, zG_mem_K0⟩ : K0G) ^ n) = 1 := by
    intro n
    rw [map_zpow, actK_z, one_zpow]
  have hle : ψ.ker ≤ φK.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hψker] at hk
    have hk' : k ∈ actK.ker := hk
    rw [ker_actK] at hk'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk'
    rw [MonoidHom.mem_ker]
    have h : zG ^ n ∈ φ.ker := by
      rw [hker]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zG) n
    rw [MonoidHom.mem_ker] at h
    simpa [φK] using h
  have hle' : φK.ker ≤ ψ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hk' : (k : GM) ∈ φ.ker := hk
    rw [hker] at hk'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk'
    have : k = (⟨zG, zG_mem_K0⟩ : K0G) ^ n := Subtype.ext (by simpa using hn.symm)
    rw [MonoidHom.mem_ker, hψker, this]
    exact hz n
  let ι := (MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ)
    (Function.rightInverse_surjInv hψ)) ⟨φK, hle⟩
  have hι : ∀ k, ι (ψ k) = φ (k : GM) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨φK, hle⟩ k
  refine ⟨ι, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨k, rfl⟩ := hψ a
    rw [hι] at ha
    have : k ∈ φK.ker := ha
    exact hle' this
  · intro a
    obtain ⟨k, rfl⟩ := hψ a
    rw [hι, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    have hc := K0G_le_centralizer k.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc]

end Embedding

theorem threeFiveData228_ON :
    ThreeFiveData228 (NativeSporadic.Carrier .ONan) := by
  have : Finite (NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.ON ≠ 0
      rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  obtain ⟨φ, -, hker⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.exists_hom_ON
  obtain ⟨ι, hι, hιC⟩ := exists_alt6_embedding φ hker
  set x₁ : (NativeSporadic.Carrier .ONan) := φ (xG 0) with hx₁
  have hx₁3 : orderOf x₁ = 3 := by
    have h3 : x₁ ^ 3 = 1 := by
      rw [hx₁, ← map_pow]
      have : xG 0 ^ 3 = 1 := by
        have h := pow_orderOf_eq_one (xG 0)
        rwa [orderOf_xG0] at h
      rw [this, map_one]
    have h1 : x₁ ≠ 1 := by
      intro h
      have hmem : xG 0 ∈ φ.ker := h
      rw [hker] at hmem
      have hK : xG 0 ∈ K0G := zpowers_le.mpr zG_mem_K0 hmem
      have : xG 0 ∈ zpowers (xG 0) ⊓ K0G := ⟨Subgroup.mem_zpowers _, hK⟩
      rw [zpowers_inf_K0, Subgroup.mem_bot] at this
      have h3 := orderOf_xG0
      rw [this, orderOf_one] at h3
      omega
    exact orderOf_eq_prime h3 h1
  have hconj : ∀ x : (NativeSporadic.Carrier .ONan), orderOf x = 3 → ∃ g : (NativeSporadic.Carrier .ONan),
      x = g * x₁ * g⁻¹ := fun x hx => by
    obtain ⟨k, hk⟩ := onThree_fusion hx₁3 hx
    exact ⟨k, hk.symm⟩
  have hcard : Nat.card (centralizer ({x₁} : Set (NativeSporadic.Carrier .ONan))) = 3240 := by
    obtain ⟨k, hk⟩ := onThree_fusion hx₁3 orderOf_onThreeElt
    have := (card_conj_data k x₁ x₁).2
    rw [hk] at this
    exact this.symm.trans card_centralizer_onThreeElt
  exact threeFiveData228_of_alt6 x₁ hconj hcard (by decide +kernel) ι hι hιC

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
