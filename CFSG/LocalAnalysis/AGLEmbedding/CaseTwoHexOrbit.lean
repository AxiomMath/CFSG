module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexRank
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1PhaseThree.mem_normalizer_of_threeASix (h : D1PhaseThree 3 P M H R)
    (hThree : KFactBlockThreeASix)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
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
  set A₀ := barM M L with hA₀
  obtain ⟨-, hb, -⟩ := hThree G M L hL.toIsTwoPrimeComponent hZ hA6
  obtain ⟨ζ, hζA, hζC, hζ1, hζ3⟩ := exists_center_of_card hZ
  obtain ⟨r₀, hr₀A, hr₀p, hr₀c, hr₀n⟩ := exists_rep_of_mem_sup (hin L hL) hzb3 (hnC L hL)
  have hr₀3 : r₀ ^ 3 = 1 := hb r₀ hr₀A hr₀p
  obtain ⟨hE₀c, hE₀e⟩ := card_sup_zpowers_rep hr₀A hr₀n hr₀3 hζC hζ1 hζ3
  have hE₀A : Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ ≤ A₀ :=
    sup_le ((Subgroup.zpowers_le).mpr hr₀A) ((Subgroup.zpowers_le).mpr hζA)
  have hE₀3 : IsPGroup 3 (Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ : Subgroup _) :=
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
  obtain ⟨r₁, hr₁A, hr₁p, hr₁c, hr₁n⟩ := exists_rep_of_mem_sup (hin L₁ hL₁w) hzb3 (hnC L₁ hL₁w)
  obtain ⟨r₂, hr₂A, hr₂p, hr₂c, hr₂n⟩ := exists_rep_of_mem_sup (hin L₂ hL₂w) hzb3 (hnC L₂ hL₂w)
  have hr₁A' : r₁ ∈ A₀.map (MulAut.conj gb).toMonoidHom := by rw [← hA₁eq]; exact hr₁A
  have hr₂A' : r₂ ∈ A₀.map (MulAut.conj (mk ⟨g ^ 2, M.pow_mem hgM 2⟩)).toMonoidHom := by
    rw [← hA₂eq]; exact hr₂A
  have hr₁3 : r₁ ^ 3 = 1 := d1_pow_three_of_mem_map_conj hb hr₁A' hr₁p
  have hr₂3 : r₂ ^ 3 = 1 := d1_pow_three_of_mem_map_conj hb hr₂A' hr₂p
  obtain ⟨hEc, hEe⟩ := card_three_reps_center h01 h02 h12 hr₀A hr₀n hr₀3 hr₁A hr₁n hr₁3 hr₂A
    hr₂n hr₂3 hζA hζC hζ1 hζ3
  have hEz : (Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ) ⊔ Subgroup.zpowers r₁ ⊔
      Subgroup.zpowers r₂ ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact d1_mem_centralizer_of_rep hr₀A hr₀c
    · exact d1_mem_centralizer_of_rep_center hr₀A hr₀c hζA hζC
    · exact d1_mem_centralizer_of_rep hr₁A hr₁c
    · exact d1_mem_centralizer_of_rep hr₂A hr₂c
  have hle := card_le_of_le_centralizer_barM hzM hz3 hrk hEz hEe
  rw [hEc] at hle
  norm_num at hle

end CFSG.AGLEmbedding
