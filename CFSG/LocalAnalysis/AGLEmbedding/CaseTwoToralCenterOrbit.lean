module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexRank
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterClass
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1PhaseThree.bf_center (h : D1PhaseThree 3 P M H R) (hBF : CitedBlockToralThreeCenter)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hinL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hno6 : ¬ (Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))))
    {ζ : ↥M ⧸ CFSG.pCore 2 ↥M} (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    let zb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩
    (∀ x ∈ barM M L, x ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        x ^ 3 = 1 → x ∈ Subgroup.zpowers ζ) ∧
      (∃ v ∈ barM M L, v ^ 3 = 1 ∧
        v ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ v * zb = zb * v) ∧
      ∀ X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsPGroup 3 X →
        X ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        X ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        X ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → Nat.card X ≤ 3 ^ 4 →
        (∀ Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsPGroup 3 Y →
          Y ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          Y ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          Y ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          Nat.card Y ≤ Nat.card X) →
        ⁅X, X⁆ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
          ∀ e ∈ ⁅X, X⁆, e ∈ barM M L → e ^ 3 = 1 → e = 1 := by
  intro zb
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hKeq := h.toD1Escape.inf_eq_inf_normalizer_twoCore
  have hcycL : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M (pCoreOf 2 H) L →
      ⁅V, V⁆ = V → ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q →
        IsCyclic Q := by
    intro V hV hVp
    refine hcyc V (hV.trans (barM_mono ?_)) hVp
    rw [hKeq]
    exact le_inf (inf_le_right.trans hL.le) inf_le_left
  exact hBF G M (pCoreOf 2 H) L h.isKGroup.1 h.asc81bHyp hL (h.nineThree h93 hL)
    (h.nineThree_not_one h85 hD2 hL).1 (h.not_isSylowTwoOf_inf h85 hD2 hL) hcycL hno6 ζ hζA hζC
    hζ3 hζ1 zb hinL hzb3 (h.not_mem_centralizer_block hp hp2 hzM hz hCz hL)
    (fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hz hCz l hl hl')

theorem D1PhaseThree.mem_normalizer_of_center (h : D1PhaseThree 3 P M H R)
    (hBF : CitedBlockToralThreeCenter) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hno6 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    {g : G} (hgM : g ∈ M) (hg3 : IsPGroup 3 (Subgroup.zpowers g)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  have hnC : ∀ L : Subgroup G, IsWeakSBlock M S L →
      zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL =>
    h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  have hv : ∀ L' : Subgroup G, IsWeakSBlock M S L' → ∀ ζ' ∈ barM M L',
      ζ' ∈ Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → ζ' ^ 3 = 1 →
      ζ' ≠ 1 → ∃ v ∈ barM M L', v ^ 3 = 1 ∧
        v ∉ Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        v * zb = zb * v := by
    intro L' hL' ζ' hζ'A hζ'C hζ'3 hζ'1
    exact (D1PhaseThree.bf_center h hBF h85 h93 hD2 hcyc hzM hz3 hCz hL' (hin L' hL')
      (fun hh => hno6 L' hL' hh.1 hh.2) hζ'A hζ'C hζ'3 hζ'1).2.1
  set A₀ := barM M L with hA₀
  obtain ⟨v₀, hv₀A, hv₀3, hv₀n, hv₀z⟩ := hv L hL ζ hζA hζC hζ3 hζ1
  obtain ⟨hE₀c, hE₀e⟩ := card_sup_zpowers_rep hv₀A hv₀n hv₀3 hζC hζ1 hζ3
  have hE₀A : Subgroup.zpowers v₀ ⊔ Subgroup.zpowers ζ ≤ A₀ :=
    sup_le ((Subgroup.zpowers_le).mpr hv₀A) ((Subgroup.zpowers_le).mpr hζA)
  have hE₀3 : IsPGroup 3 (Subgroup.zpowers v₀ ⊔ Subgroup.zpowers ζ : Subgroup _) :=
    fun x => ⟨1, Subtype.ext (by simpa using hE₀e.2 x x.2)⟩
  have hE₀nc := not_isCyclic_of_isElemAbelian Nat.prime_three hE₀e le_rfl hE₀c
  by_contra hgL
  have hinj := injective_conj_pow_of_not_mem_normalizer hg3 hgL
  set gb := mk ⟨g, hgM⟩ with hgb
  set L₁ := L.map (MulAut.conj g).toMonoidHom with hL₁
  set L₂ := L.map (MulAut.conj (g ^ 2)).toMonoidHom with hL₂
  have hL₁w : IsWeakSBlock M S L₁ :=
    D1PhaseThree.isWeakSBlock_map_conj_of_cyc h hcyc hL hE₀A hE₀3 hE₀nc hgM
  have hL₂w : IsWeakSBlock M S L₂ :=
    D1PhaseThree.isWeakSBlock_map_conj_of_cyc h hcyc hL hE₀A hE₀3 hE₀nc (M.pow_mem hgM 2)
  have hL0 : L.map (MulAut.conj (g ^ ((0 : Fin 3) : ℕ))).toMonoidHom = L := by
    simp only [Fin.val_zero, pow_zero, map_one]
    ext x
    simp
  have hL1eq : L.map (MulAut.conj (g ^ ((1 : Fin 3) : ℕ))).toMonoidHom = L₁ := by
    rw [show ((1 : Fin 3) : ℕ) = 1 from rfl, pow_one]
  have hL2eq : L.map (MulAut.conj (g ^ ((2 : Fin 3) : ℕ))).toMonoidHom = L₂ := rfl
  have hne01 : L ≠ L₁ := by
    intro he
    have := @hinj 0 1 (by dsimp only; rw [hL0, hL1eq]; exact he)
    exact absurd this (by decide)
  have hne02 : L ≠ L₂ := by
    intro he
    have := @hinj 0 2 (by dsimp only; rw [hL0, hL2eq]; exact he)
    exact absurd this (by decide)
  have hne12 : L₁ ≠ L₂ := by
    intro he
    have := @hinj 1 2 (by dsimp only; rw [hL1eq, hL2eq]; exact he)
    exact absurd this (by decide)
  set A₁ := barM M L₁ with hA₁
  set A₂ := barM M L₂ with hA₂
  have hbne : ∀ {X Y : Subgroup G}, IsWeakSBlock M S X → IsWeakSBlock M S Y → X ≠ Y →
      barM M X ≠ barM M Y := fun hX hY hXY he =>
    hXY (hX.toIsTwoPrimeComponent.eq_of_barM_eq hY.toIsTwoPrimeComponent he)
  have h01 : A₁ ≤ Subgroup.centralizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    le_centralizer_of_component_ne hL₁w.component hL.component (hbne hL₁w hL hne01.symm)
  have h02 : A₂ ≤ Subgroup.centralizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    le_centralizer_of_component_ne hL₂w.component hL.component (hbne hL₂w hL hne02.symm)
  have h12 : A₂ ≤ Subgroup.centralizer (A₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    le_centralizer_of_component_ne hL₂w.component hL₁w.component (hbne hL₂w hL₁w hne12.symm)
  have hA₁eq : A₁ = A₀.map (MulAut.conj gb).toMonoidHom := barM_map_conj hgM L
  have hA₂eq : A₂ = A₀.map (MulAut.conj (mk ⟨g ^ 2, M.pow_mem hgM 2⟩)).toMonoidHom :=
    barM_map_conj (M.pow_mem hgM 2) L
  obtain ⟨hζ₁A, hζ₁C, hζ₁3, hζ₁1⟩ := conj_center_data gb hζA hζC hζ3 hζ1
  obtain ⟨hζ₂A, hζ₂C, hζ₂3, hζ₂1⟩ :=
    conj_center_data (mk ⟨g ^ 2, M.pow_mem hgM 2⟩) hζA hζC hζ3 hζ1
  rw [← hA₁eq] at hζ₁A hζ₁C
  rw [← hA₂eq] at hζ₂A hζ₂C
  obtain ⟨v₁, hv₁A, hv₁3, hv₁n, hv₁z⟩ := hv L₁ hL₁w _ hζ₁A hζ₁C hζ₁3 hζ₁1
  obtain ⟨v₂, hv₂A, hv₂3, hv₂n, hv₂z⟩ := hv L₂ hL₂w _ hζ₂A hζ₂C hζ₂3 hζ₂1
  obtain ⟨hEc, hEe⟩ := card_three_reps_center h01 h02 h12 hv₀A hv₀n hv₀3 hv₁A hv₁n hv₁3 hv₂A
    hv₂n hv₂3 hζA hζC hζ1 hζ3
  obtain ⟨r₀, hr₀A, -, hr₀c, -⟩ := exists_rep_of_mem_sup (hin L hL) hzb3 (hnC L hL)
  have hEz : (Subgroup.zpowers v₀ ⊔ Subgroup.zpowers ζ) ⊔ Subgroup.zpowers v₁ ⊔
      Subgroup.zpowers v₂ ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hv₀z
    · exact d1_mem_centralizer_of_rep_center hr₀A hr₀c hζA hζC
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hv₁z
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hv₂z
  have hle := card_le_of_le_centralizer_barM hzM hz3 hrk hEz hEe
  rw [hEc] at hle
  norm_num at hle

end CFSG.AGLEmbedding
