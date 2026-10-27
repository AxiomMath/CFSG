module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open scoped Pointwise

namespace Prop121

@[expose] def Input2027L34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J B T : Subgroup G),
    IsLThreeFour (↥J ⧸ CFSG.pCore 2 ↥J) → B ≤ J → IsElemAbelian 3 B → Nat.card ↥B = 9 →
      T ≤ J → IsPGroup 2 ↥T → B ≤ Subgroup.normalizer (T : Set G) → T ≤ pCoreOf 2 J

@[expose] def Input28_8Cons : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y J T B : Subgroup G),
    CFSG.Open.IsKProper G → Y ≠ ⊤ → J ≤ Y → Y ≤ Subgroup.normalizer (J : Set G) →
    IsLThreeFour (↥J ⧸ CFSG.pCore 2 ↥J) → B ≤ J → IsElemAbelian 3 B → Nat.card ↥B = 9 →
    T ≤ Y → IsPGroup 2 ↥T → B ≤ Subgroup.normalizer (T : Set G) →
    (∀ T' : Subgroup G, T' ≤ Y → IsPGroup 2 ↥T' → B ≤ Subgroup.normalizer (T' : Set G) →
        T ≤ T' → T' = T) →
    Y ≤ J ⊔ T → pCoreOf 2 Y ≤ T →
    Subgroup.centralizer (pCoreOf 2 Y : Set G) ⊓ Y ≤ pCoreOf 2 Y →
    Y ≤ ⨆ (T₀ : Subgroup G) (_ : T₀ ≠ ⊥ ∧ IsCharIn T₀ T), Subgroup.normalizer (T₀ : Set G) ⊓ Y

@[expose] def PrintedOJNorm : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) {K : Subgroup G} (hK : GLAPComponent 3 (Cg a) K)
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) {Js : Subgroup G},
    IsTwoPrimeComp ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G))) ⊔
        ⨆ (x : G) (_ : x ∈ centBar 3 A K) (_ : x ≠ 1), M ⊓ Cg x) Js →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G)) ≤ Js →
        pCoreOf 2 M ≤ Subgroup.normalizer (Js : Set G)

@[expose] def PrintedKLeKx : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) {K : Subgroup G} (hK : GLAPComponent 3 (Cg a) K)
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K),
    K ≤ Kx 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G))) a

@[expose] def PrintedY2c : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) {K : Subgroup G} (hK : GLAPComponent 3 (Cg a) K)
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) {Js : Subgroup G},
    IsTwoPrimeComp ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G))) ⊔
        ⨆ (x : G) (_ : x ∈ centBar 3 A K) (_ : x ≠ 1), M ⊓ Cg x) Js →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G)) ≤ Js →
        Subgroup.centralizer (pCoreOf 2 (pCoreOf 2 M ⊔ Js) : Set G) ⊓ (pCoreOf 2 M ⊔ Js) ≤
          pCoreOf 2 (pCoreOf 2 M ⊔ Js)

variable {G : Type} [Group G]

theorem normalizer_inf_mem {H1 H2 : Subgroup G} {g : G}
    (h1 : g ∈ Subgroup.normalizer (H1 : Set G)) (h2 : g ∈ Subgroup.normalizer (H2 : Set G)) :
    g ∈ Subgroup.normalizer ((H1 ⊓ H2 : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at *
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 x, h2 x]

theorem map_conj_eq_of_normalizes {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hg y).1 hy
    simpa [MulAut.conj_apply] using this
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2 (by
      simpa [mul_assoc] using hx)

theorem normalizer_sup_mem {H1 H2 : Subgroup G} {g : G}
    (h1 : g ∈ Subgroup.normalizer (H1 : Set G)) (h2 : g ∈ Subgroup.normalizer (H2 : Set G)) :
    g ∈ Subgroup.normalizer ((H1 ⊔ H2 : Subgroup G) : Set G) := by
  have hmap : (H1 ⊔ H2).map (MulAut.conj g).toMonoidHom = H1 ⊔ H2 := by
    rw [Subgroup.map_sup, map_conj_eq_of_normalizes h1, map_conj_eq_of_normalizes h2]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h2' : ∀ z, (MulAut.conj g).symm z ∈ H1 ⊔ H2 ↔ z ∈ H1 ⊔ H2 := by
    intro z
    rw [← Subgroup.mem_map_equiv, hmap]
  have h3 := h2' (g * x * g⁻¹)
  have e : (MulAut.conj g).symm (g * x * g⁻¹) = x := by
    rw [MulEquiv.symm_apply_eq, MulAut.conj_apply]
  rw [e] at h3
  exact h3

theorem mem_sup_decomp {P J : Subgroup G} (hPJ : P ≤ Subgroup.normalizer (J : Set G)) {y : G}
    (hy : y ∈ P ⊔ J) : ∃ p ∈ P, ∃ j ∈ J, y = p * j := by
  let S : Subgroup G :=
    { carrier := {y | ∃ p ∈ P, ∃ j ∈ J, y = p * j}
      mul_mem' := by
        rintro _ _ ⟨p1, hp1, j1, hj1, rfl⟩ ⟨p2, hp2, j2, hj2, rfl⟩
        have hc : p2⁻¹ * j1 * p2⁻¹⁻¹ ∈ J :=
          (Subgroup.mem_normalizer_iff.1 (hPJ (P.inv_mem hp2)) j1).1 hj1
        refine ⟨p1 * p2, P.mul_mem hp1 hp2, p2⁻¹ * j1 * p2⁻¹⁻¹ * j2, J.mul_mem hc hj2, ?_⟩
        group
      one_mem' := ⟨1, P.one_mem, 1, J.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨p, hp, j, hj, rfl⟩
        refine ⟨p⁻¹, P.inv_mem hp, p * j⁻¹ * p⁻¹, ?_, by group⟩
        exact (Subgroup.mem_normalizer_iff.1 (hPJ hp) j⁻¹).1 (J.inv_mem hj) }
  have hle : P ⊔ J ≤ S :=
    sup_le (fun p hp => ⟨p, hp, 1, J.one_mem, by simp⟩) (fun j hj => ⟨1, P.one_mem, j, hj, by simp⟩)
  obtain ⟨p, hp, j, hj, he⟩ := hle hy
  exact ⟨p, hp, j, hj, he⟩

end Prop121

open Prop121

theorem prop121_of_cex_of_inputs (h123 : Lemma123Statement) (h124 : Lemma124Statement)
    (h125 : Lemma125Statement) (h111 : Prop111Statement)
    (hI20 : Prop121.Input2027L34) (hI28 : Prop121.Input28_8Cons)
    (hNorm : Prop121.PrintedOJNorm) (hKa : Prop121.PrintedKLeKx)
    (hY2 : Prop121.PrintedY2c) : Prop121_of_cexStatement := by
  intro G _ _ m p B M E A a h
  obtain ⟨hp3, K, hK, ⟨hK3, hKM⟩, hu₀, hA0, -⟩ := h123 h
  subst hp3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3' : (3 : ℕ).Prime := by norm_num
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hmaxM : IsMaxTwoLocalSubgroup M := h.pre.1
  have haA : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hKC : K ≤ Cg a := Sec12b.comp_le hK
  have hcomm : ∀ k ∈ K, a * k = k * a := by
    intro k hk
    have hk' := hKC hk
    rw [Subgroup.mem_centralizer_iff] at hk'
    exact hk' a (Set.mem_singleton a)
  have haN : a ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have e : a * k * a⁻¹ = k := by rw [hcomm k hk]; group
      rw [e]; exact hk
    · intro hk
      have hx := hcomm _ hk
      have e : a⁻¹ * (a * k * a⁻¹) * a = a * k * a⁻¹ := by
        calc a⁻¹ * (a * k * a⁻¹) * a = a⁻¹ * ((a * k * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * k * a⁻¹)) := by rw [hx]
          _ = a * k * a⁻¹ := by group
      have e2 : k = a⁻¹ * (a * k * a⁻¹) * a := by group
      have hkx : k = a * k * a⁻¹ := e2.trans e
      rw [hkx]; exact hk
  have haF : a ∈ centBar 3 A K :=
    Lemma1112b.mem_centBar_of_mem_top (Lemma1112b.mem_centBar_top_of_central haN hcomm) haA
  obtain ⟨⟨-, -, -, -, hcard, -, -⟩, hxF, -, -⟩ := h124 h hK hK3 hKM hu₀ hA0
  obtain ⟨hCN, hcovKx⟩ := hxF a haF ha1
  set F := centBar 3 A K with hFdef
  set J := GLAPLayer 3 (K ⊓ Subgroup.centralizer (F : Set G)) with hJdef
  have hJK : J ≤ K := (Sec12b.layer_le 3 _).trans inf_le_left
  have hJC : J ≤ Cg a := hJK.trans hKC
  have hKxC : Kx 3 J a ≤ Cg a := Sec12b.kx_le_cent hJC
  have hJKx : J ≤ Kx 3 J a := Sec12b.le_kx (p := 3) a J
  have hKKx : K ≤ Kx 3 J a := hKa h hK hK3 hKM hu₀ hA0
  have hO3 : GLAPPrimeCoreOf 3 (Cg a) ≤ M := h111 h.toSec11 haA ha1
  have hnKx : ((Kx 3 J a).subgroupOf (Cg a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKxC).2 hCN
  have hOKx : GLAPPrimeCoreOf 3 (Kx 3 J a) ≤ GLAPPrimeCoreOf 3 (Cg a) :=
    glaPPrimeCoreOf_le_of_normal hp3' hKxC hnKx
  obtain ⟨hXne, hO2X, Js, hJs, hJJs, hJsL3⟩ := h125 h hK hK3 hKM hu₀ hA0
  set W := ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1), M ⊓ Cg x with hWdef
  have hPW : pCoreOf 2 M ≤ W := Sec12b.core_le_W_of_inputs h123 h124 h hK hK3 hKM hu₀ hA0
  have hPN : pCoreOf 2 M ≤ Subgroup.normalizer (Js : Set G) := hNorm h hK hK3 hKM hu₀ hA0 hJs hJJs
  have hJsX : Js ≤ J ⊔ W := hJs.1
  have hJsSub : IsSubnormal Js (J ⊔ W) := hJs.2.1
  set Y := pCoreOf 2 M ⊔ Js with hYdef
  have hYX : Y ≤ J ⊔ W := sup_le (hPW.trans le_sup_right) hJsX
  have hYne : Y ≠ ⊤ := by
    intro hY
    apply hXne
    rw [← top_le_iff, ← hY]
    exact hYX
  have hJY : Js ≤ Y := le_sup_right
  have hPY : pCoreOf 2 M ≤ Y := le_sup_left
  have hYN : Y ≤ Subgroup.normalizer (Js : Set G) := sup_le hPN Subgroup.le_normalizer
  have hcard' : Nat.card ↥(A ⊓ J) = 9 := hcard
  have hBJ : A ⊓ J ≤ Js := inf_le_right.trans hJJs
  have hBel : IsElemAbelian 3 (A ⊓ J) := Sec12b.isElemAbelian_mono inf_le_left hAel
  have hBAM : A ⊓ J ≤ M := inf_le_left.trans hAM
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hBP : A ⊓ J ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    hBAM.trans (le_normalizer_pCoreOf 2 M)
  have hmaxP : ∀ T' : Subgroup G, T' ≤ Y → IsPGroup 2 ↥T' →
      A ⊓ J ≤ Subgroup.normalizer (T' : Set G) → pCoreOf 2 M ≤ T' → T' = pCoreOf 2 M := by
    intro T' hT'Y hT'2 hBT' hPT'
    have hS2 : IsPGroup 2 ↥(T' ⊓ Js) := hT'2.to_le inf_le_left
    have hBS : A ⊓ J ≤ Subgroup.normalizer ((T' ⊓ Js : Subgroup G) : Set G) := fun b hb =>
      normalizer_inf_mem (hBT' hb) (Subgroup.le_normalizer (hBJ hb))
    have hSP : T' ⊓ Js ≤ pCoreOf 2 M := by
      have h1 := hI20 G Js (A ⊓ J) (T' ⊓ Js) hJsL3 hBJ hBel hcard' inf_le_right hS2 hBS
      have hsub : IsSubnormal (pCoreOf 2 Js) (J ⊔ W) :=
        (Sec12a2.isSubnormal_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 Js)
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
              (CFSG.LieType.BorelTits.pCoreOf_le 2 Js)).2
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Js))).trans hJsSub
      exact h1.trans ((Sec12a2.le_pCoreOf_of_isSubnormal hsub
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Js)).trans hO2X)
    apply le_antisymm
    · intro t ht
      obtain ⟨p', hp', j, hj, rfl⟩ := mem_sup_decomp hPN (hT'Y ht)
      have hjT : j ∈ T' := by
        have := T'.mul_mem (T'.inv_mem (hPT' hp')) ht
        simpa using this
      exact (pCoreOf 2 M).mul_mem hp' (hSP ⟨hjT, hj⟩)
    · exact hPT'
  have hR : pCoreOf 2 Y ≤ pCoreOf 2 M := by
    have hRY : pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
    have hYNR : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
    have hR2 : IsPGroup 2 ↥(pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    have hsup2 : IsPGroup 2 ↥(pCoreOf 2 Y ⊔ pCoreOf 2 M) :=
      IsPGroup.to_sup_of_normal_left' hR2 hP2 (hPY.trans hYNR)
    have hsupY : pCoreOf 2 Y ⊔ pCoreOf 2 M ≤ Y := sup_le hRY hPY
    have hBsup : A ⊓ J ≤ Subgroup.normalizer ((pCoreOf 2 Y ⊔ pCoreOf 2 M : Subgroup G) : Set G) :=
      fun b hb => normalizer_sup_mem (hYNR (hJY (hBJ hb))) (hBP hb)
    have heq := hmaxP (pCoreOf 2 Y ⊔ pCoreOf 2 M) hsupY hsup2 hBsup le_sup_right
    calc pCoreOf 2 Y ≤ pCoreOf 2 Y ⊔ pCoreOf 2 M := le_sup_left
      _ = pCoreOf 2 M := heq
  have hY2c := hY2 h hK hK3 hKM hu₀ hA0 hJs hJJs
  have hYJ : Y ≤ Js ⊔ pCoreOf 2 M := le_of_eq (sup_comm _ _)
  have hYsup := hI28 G Y Js (pCoreOf 2 M) (A ⊓ J) h.standing.kProper hYne hJY hYN hJsL3 hBJ hBel
    hcard' hPY hP2 hBP hmaxP hYJ hR hY2c
  have hYM : Y ≤ M := by
    refine hYsup.trans (iSup_le fun T₀ => iSup_le fun hT₀ => ?_)
    refine inf_le_left.trans ?_
    have hMN : M ≤ Subgroup.normalizer (T₀ : Set G) :=
      (le_normalizer_pCoreOf 2 M).trans hT₀.2.normalizer_le
    have hT₀2 : IsPGroup 2 ↥T₀ := hP2.to_le hT₀.2.1
    have hTL : IsTwoLocal (Subgroup.normalizer (T₀ : Set G)) := ⟨T₀, hT₀.1, hT₀2, rfl⟩
    exact le_of_eq (hmaxM.2 _ hTL hMN)
  have hJM : J ≤ M := hJJs.trans (hJY.trans hYM)
  have hKM' : K ≤ M := by
    intro k hk
    obtain ⟨j, hj, o, ho, rfl⟩ := Sec12b.mem_mul_glaPPrimeCoreOf_of_barX hJKx hcovKx (hKKx hk)
    exact M.mul_mem (hJM hj) (hO3 (hOKx ho))
  apply hKM
  have hsub : K ≤ M ⊓ Cg a := le_inf hKM' hKC
  exact Subgroup.map_mono (fun y hy => Subgroup.mem_subgroupOf.2 (hsub (Subgroup.mem_subgroupOf.1 hy)))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
