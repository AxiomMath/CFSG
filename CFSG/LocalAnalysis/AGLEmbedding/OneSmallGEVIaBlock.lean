module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaOrder
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaPhase
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.blockFacts_u33 (h : D1PhaseThree p P M H R) (hp : p.Prime) (hp2 : p ≠ 2)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hK9 : CitedBlockThreeAutNine)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
    {z : G} (hzM : z ∈ M) (hz : IsPGroup p (Subgroup.zpowers z)) (hz3 : z ^ 3 = 1)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
    ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup 3 U →
      (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 9 := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hzb3 : mk ⟨z, hzM⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have hperf' : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) := fun Y hY hYp => hperf Y (hKeq ▸ hY) hYp
  have hzN := mem_normalizer_barM hzM
    (h.mem_normalizer_block_of_cube hp hp2 h84 h86 hD2 hzM hz hz3 hCz hL)
  have hzC := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  have hfix := fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hz hCz (L := L) l hl hl'
  have h9 := h.nineThree h93 hL
  have hn1 := (h.nineThree_not_one h85 hD2 hL).1
  have hsyl := h.not_isSylowTwoOf_inf h85 hD2 hL
  exact ⟨(hK G M _ L h.isKGroup.1 h.asc81bHyp hL h9 hn1 hsyl hperf' _ hzN hzb3 hzC hfix).1,
    hK9 G M _ L h.isKGroup.1 h.asc81bHyp hL h9 hn1 hsyl hperf' _ hzN hzb3 hzC hfix⟩

theorem D1PhaseThree.card_le_of_zbar_mem (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hK9 : CitedBlockThreeAutNine)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
    {z : G} (hzR : z ∈ R) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hPz : ∀ y ∈ (P : Subgroup G), y * z = z * y → y ∈ R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hzL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, h.le_M hzR⟩ ∈ barM M L) :
    Nat.card (P : Subgroup G) ≤
      9 * Nat.card (rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hzM := h.le_M hzR
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hPM : (P : Subgroup G) ≤ M := h.sylow_le
  have hPp : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hzP : z ∈ (P : Subgroup G) := h.le_P hzR
  have hPN : barM M (P : Subgroup G) ≤
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, -, rfl⟩
    exact h.mem_normalizer_of_zbar_mem hp hp2 hperf hzM hz hz3 hCz hL hzL hgM
  have hUp : IsPGroup 3 (barM M (P : Subgroup G)) := (hPp.comap_subtype (K := M)).map _
  refine card_le_mul_card_rPart hPM hPp h.le_M h.isPGroup hzP hPz ?_
    ((h.blockFacts_u33 hp hp2 h84 h85 h86 h93 hD2 hK hK9 hperf hzM hz hz3 hCz hL).2 _ hPN hUp)
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx _ hzL).symm

omit [Finite G] in
theorem conj_mem_centralizer_map_of_mem {X : Type*} [Group X] {L : Subgroup X} {g c : X}
    (hc : c ∈ Subgroup.centralizer (L : Set X)) :
    g * c * g⁻¹ ∈
      Subgroup.centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hcy := Subgroup.mem_centralizer_iff.mp hc y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * (g * c * g⁻¹) = g * (y * c) * g⁻¹ := by group
    _ = g * (c * y) * g⁻¹ := by rw [hcy]
    _ = g * c * g⁻¹ * (g * y * g⁻¹) := by group

omit [Finite G] in
theorem map_conj_pow_two_eq {X : Type*} [Group X] (A : Subgroup X) (g : X) :
    A.map (MulAut.conj (g ^ 2)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [pow_two, mul_assoc]

omit [Finite G] in
theorem mem_of_sq_mem_of_pow_three {X : Type*} [Group X] {N : Subgroup X} {x : X} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) (hx2 : x ^ 2 ∈ N) : x ∈ N := by
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k + 1 = 2 * m := by
    have : Odd (3 ^ k) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := this
    exact ⟨m + 1, by omega⟩
  have h1 : x = (x ^ 2) ^ m := by
    rw [← pow_mul, ← hm, pow_succ, hx, one_mul]
  rw [h1]
  exact N.pow_mem hx2 m

theorem D1PhaseThree.card_le_of_two_blocks (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hK9 : CitedBlockThreeAutNine)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
    {z : G} (hzR : z ∈ R) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hPz : ∀ y ∈ (P : Subgroup G), y * z = z * y → y ∈ R) {L₁ L₂ : Subgroup G}
    (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₂ ≠ barM M L₁) {a b : ↥M ⧸ CFSG.pCore 2 ↥M} (haL : a ∈ barM M L₁)
    (hbL : b ∈ barM M L₂) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hzab : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, h.le_M hzR⟩ = a * b) :
    Nat.card (P : Subgroup G) ≤ 81 * Nat.card (rPart M R
      (Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hzM := h.le_M hzR
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hPM : (P : Subgroup G) ≤ M := h.sylow_le
  have hPp : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hzP : z ∈ (P : Subgroup G) := h.le_P hzR
  have honly : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M L = barM M L₁ ∨ barM M L = barM M L₂ := by
    intro L hL
    by_contra hc
    push Not at hc
    apply h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
    rw [hzab]
    exact Subgroup.mul_mem _
      (le_centralizer_of_component_ne hL₁.component hL.component (Ne.symm hc.1) haL)
      (le_centralizer_of_component_ne hL₂.component hL.component (Ne.symm hc.2) hbL)
  have hfix : ∀ g : G, ∀ hg : g ∈ M, g ∈ (P : Subgroup G) →
      mk ⟨g, hg⟩ ∈ Subgroup.normalizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      mk ⟨g, hg⟩ ∈ Subgroup.normalizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g hg hgP
    set gb := mk ⟨g, hg⟩ with hgb
    set σ := fun A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) => A.map (MulAut.conj gb).toMonoidHom
      with hσ
    have hσinj : ∀ A B, σ A = σ B → A = B := fun A B hAB =>
      Subgroup.map_injective (MulAut.conj gb).injective hAB
    have h1 := honly _ (h.isWeakSBlock_conj hperf hL₁ haL ha1 ha3 hg)
    have h2 := honly _ (h.isWeakSBlock_conj hperf hL₂ hbL hb1 hb3 hg)
    rw [barM_map_conj hg] at h1 h2
    have hσ12 : σ (barM M L₁) ≠ σ (barM M L₂) := fun he => hne (hσinj _ _ he).symm
    obtain ⟨k, hk⟩ := hPp ⟨g, hgP⟩
    have hgk : gb ^ 3 ^ k = 1 := by
      rw [hgb, ← map_pow]
      have : (⟨g, hg⟩ : M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    rcases h1 with h1 | h1
    · have h2' : σ (barM M L₂) = barM M L₂ := h2.resolve_left fun he => hσ12 (h1.trans he.symm)
      exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1,
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2'⟩
    · have h2' : σ (barM M L₂) = barM M L₁ := h2.resolve_right fun he => hσ12 (h1.trans he.symm)
      have hsq1 : gb ^ 2 ∈ Subgroup.normalizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
        exact (map_conj_pow_two_eq (barM M L₁) gb).trans
          ((congrArg (fun A => A.map (MulAut.conj gb).toMonoidHom) h1).trans h2')
      have hsq2 : gb ^ 2 ∈ Subgroup.normalizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
        exact (map_conj_pow_two_eq (barM M L₂) gb).trans
          ((congrArg (fun A => A.map (MulAut.conj gb).toMonoidHom) h2').trans h1)
      exact ⟨mem_of_sq_mem_of_pow_three hgk hsq1, mem_of_sq_mem_of_pow_three hgk hsq2⟩
  have hPN₁ : barM M (P : Subgroup G) ≤
      Subgroup.normalizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hgP, rfl⟩
    exact (hfix g hgM (Subgroup.mem_subgroupOf.mp hgP)).1
  have hPN₂ : barM M (P : Subgroup G) ≤
      Subgroup.normalizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hgP, rfl⟩
    exact (hfix g hgM (Subgroup.mem_subgroupOf.mp hgP)).2
  have hUp : IsPGroup 3 (barM M (P : Subgroup G)) := (hPp.comap_subtype (K := M)).map _
  have hb₁ := (h.blockFacts_u33 hp hp2 h84 h85 h86 h93 hD2 hK hK9 hperf hzM hz hz3 hCz hL₁).2 _
    hPN₁ hUp
  have hb₂ := (h.blockFacts_u33 hp hp2 h84 h85 h86 h93 hD2 hK hK9 hperf hzM hz hz3 hCz hL₂).2 _
    hPN₂ hUp
  set C₁ := Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₁
  set C₂ := Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC₂
  set U := barM M (P : Subgroup G) with hU
  have hidx : (U ⊓ (C₁ ⊓ C₂)).relIndex U ≤ 81 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [inf_comm, Subgroup.inf_relIndex_right] at hb₁ hb₂
    calc (C₁ ⊓ C₂).relIndex U ≤ C₁.relIndex U * C₂.relIndex U := Subgroup.relIndex_inf_le
      _ ≤ 9 * 9 := Nat.mul_le_mul hb₁ hb₂
      _ = 81 := by norm_num
  refine card_le_mul_card_rPart hPM hPp h.le_M h.isPGroup hzP hPz ?_ hidx
  intro x hx
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [hzab]
  have h1 : a * x = x * a := Subgroup.mem_centralizer_iff.mp hx.1 a haL
  have h2 : b * x = x * b := Subgroup.mem_centralizer_iff.mp hx.2 b hbL
  calc x * (a * b) = (x * a) * b := by group
    _ = a * (x * b) := by rw [← h1, mul_assoc]
    _ = a * (b * x) := by rw [h2]
    _ = a * b * x := by group

end CFSG.AGLEmbedding
