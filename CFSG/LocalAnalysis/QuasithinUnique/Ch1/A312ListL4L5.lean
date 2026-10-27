module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem exists_big_or_small {n : ℕ} {I : Set ℕ} :
    (∀ a m : ℕ, a + m ≤ n → (a = 0 ∨ a ∈ I) → (a + m = n ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2) ∨
    ∃ a m : ℕ, a + m ≤ n ∧ 3 ≤ m ∧ (a = 0 ∨ a ∈ I) ∧ (a + m = n ∨ a + m ∈ I) ∧
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) := by
  by_cases h : ∀ a m : ℕ, a + m ≤ n → (a = 0 ∨ a ∈ I) → (a + m = n ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2
  · exact Or.inl h
  · right
    by_contra hcon
    apply h
    intro a m ham ha hb hno
    by_contra hm
    exact hcon ⟨a, m, ham, by omega, ha, hb, hno⟩

section Main

variable {K : Type} [Field K] [Finite K]

theorem bigBlock_conclusion (hK : Nat.card K = 2) {n : ℕ} (hn : 1 ≤ n) (hn5 : n ≤ 5) {I : Set ℕ}
    {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m) (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) {B : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hB : B ∈ lFamily (unitriangular n K))
    (hMQ : B ⊔ unitriangular n K = flagStabilizer n K I) :
    B = perfectCore (B ⊔ unitriangular n K) ∧ IsPSL m 2 1 (ModO2 B) := by
  classical
  have hcardK : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hcardK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj := bigBlockHom_surjective (K := K) hK h hm3 ha hb hno
  have hkerU : ∀ x, bigBlockHom (K := K) I a m h ha hb x = 1 →
      (x : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K := fun x hx =>
    unitriangular_of_bigBlockHom hK hn5 h hm3 ha hb hno x hx
  have hS := sl_isSimple_of_card_two hK hm3
  have hnab := sl_nonabelian_of_card_two hK hm3
  have hperfEq : perfectCore (B ⊔ unitriangular n K) = perfectCore (flagStabilizer n K I) :=
    congrArg perfectCore hMQ
  let eM := MulEquiv.subgroupCongr hperfEq
  let g' : ↥(perfectCore (B ⊔ unitriangular n K)) →* SpecialLinearGroup (Fin m) K :=
    (bigBlockHom (K := K) I a m h ha hb).comp eM.toMonoidHom
  have hg'surj : Function.Surjective g' := hsurj.comp eM.surjective
  have hker' : IsPGroup 2 g'.ker := by
    refine isPGroup_ker_of_unitriangular hn g' fun x hx => ?_
    have hx' : bigBlockHom (K := K) I a m h ha hb (eM x) = 1 := by
      rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.comp_apply]
      exact hx
    have h1 := hkerU (eM x) hx'
    rw [MulEquiv.subgroupCongr_apply] at h1
    exact h1
  have hsolv : Group.IsSolvable g'.ker := by
    have := hker'.isNilpotent
    infer_instance
  have hBeq : B = perfectCore (B ⊔ unitriangular n K) :=
    lFamily_eq_perfectCore hB hnab g' hg'surj hsolv
  refine ⟨hBeq, ?_⟩
  let gB : ↥B →* SpecialLinearGroup (Fin m) K :=
    g'.comp (MulEquiv.subgroupCongr hBeq).toMonoidHom
  have hgBsurj : Function.Surjective gB := hg'surj.comp (MulEquiv.subgroupCongr hBeq).surjective
  have hkerB : IsPGroup 2 gB.ker := by
    refine isPGroup_ker_of_unitriangular hn gB fun x hx => ?_
    have hx' : g' (MulEquiv.subgroupCongr hBeq x) = 1 := by
      rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.comp_apply]
      exact hx
    have hx'' : bigBlockHom (K := K) I a m h ha hb (eM (MulEquiv.subgroupCongr hBeq x)) = 1 := by
      rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.comp_apply]
      exact hx'
    have h1 := hkerU _ hx''
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.subgroupCongr_apply] at h1
    exact h1
  let eB : ModO2 B ≃* SpecialLinearGroup (Fin m) K := modO2EquivOfHom hnab gB hgBsurj hkerB
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, K, inferInstance, inferInstance, hcardK,
    ⟨eB.trans (slEquivStatedProj hK m)⟩⟩
  · intro h2
    have := congrArg Prod.fst h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.fst h2
    simp only at this
    omega

theorem a312For_sl_two (hK : Nat.card K = 2) {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin n) K))
    (hSL : IsPSL n 2 1 (SpecialLinearGroup (Fin n) K)) :
    A312For (SpecialLinearGroup (Fin n) K) := by
  classical
  have hcardK : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hcardK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) (by omega)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular n K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine A312For.of_sylow (unitriangular n K) hT₀ fun B hB hBtop => ?_
  have hB' : B ∈ cComp (B ⊔ unitriangular n K) := hB
  have hMne : B ⊔ unitriangular n K ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ unitriangular n K) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ unitriangular n K))
        (Subgroup.inclusion_injective _))
  have hUB : upperTriangular n K ≤ B ⊔ unitriangular n K :=
    (upperTriangular_le_unitriangular hK).trans le_sup_right
  obtain ⟨hMQ, -⟩ := borel_overgroups (B ⊔ unitriangular n K) hUB
  have hIcuts : ∀ c ∈ borelOvergroupCuts (B ⊔ unitriangular n K), 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  rcases exists_big_or_small (n := n) (I := borelOvergroupCuts (B ⊔ unitriangular n K)) with
    hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · exfalso
    apply hMns
    rw [isSolvable_iff_perfectCore_eq_bot, hMQ]
    exact perfectCore_eq_bot_of_small hK (by omega) hsmall
  · have hmn : m < n := by
      by_contra hmn
      have hmn' : m = n ∧ a = 0 := by omega
      have hIempty : borelOvergroupCuts (B ⊔ unitriangular n K) = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hc
        obtain ⟨h1, h2⟩ := hIcuts c hc
        exact hno c hc ⟨by omega, by omega⟩
      apply hMne
      rw [hMQ, hIempty, flagStabilizer_empty]
    obtain ⟨hBeq, hPSLB⟩ := bigBlock_conclusion hK (by omega) hn5 h hm3 ha hb hno hB hMQ
    have hpar : ∃ P, IsParabolic2 (⊤ : Subgroup (SpecialLinearGroup (Fin n) K)) P ∧
        B = perfectCore P :=
      ⟨B ⊔ unitriangular n K, ⟨le_top, unitriangular n K, hT₀, fun g hg =>
        hUB (normalizer_unitriangular.le hg.2)⟩, hBeq⟩
    have hLtop : IsPSL n 2 1 ↥(⊤ : Subgroup (SpecialLinearGroup (Fin n) K)) :=
      IsPSL.of_mulEquiv Subgroup.topEquiv.symm hSL
    have hm : m = 3 ∨ m = 4 := by omega
    rcases hm with rfl | rfl
    · iterate 2 right
      left
      rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
      · exact ⟨hPSLB, Or.inl hLtop, hpar⟩
      · exact ⟨hPSLB, Or.inr hLtop, hpar⟩
    · have hn : n = 5 := by omega
      subst hn
      iterate 3 right
      left
      exact ⟨hPSLB, hLtop, hpar⟩

end Main

theorem l4 : FamL4 := by
  intro X _ _ hq hX
  have hX' := hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hK : Nat.card K = 2 := by simpa using hcard
  let e' : X ≃* SpecialLinearGroup (Fin 4) K := e.trans (slEquivStatedProj hK 4).symm
  exact A312For.of_mulEquiv e' (a312For_sl_two hK le_rfl (by norm_num)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq) (IsPSL.of_mulEquiv e' hX'))

theorem l5 : FamL5 := by
  intro X _ _ hq hX
  have hX' := hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hK : Nat.card K = 2 := by simpa using hcard
  let e' : X ≃* SpecialLinearGroup (Fin 5) K := e.trans (slEquivStatedProj hK 5).symm
  exact A312For.of_mulEquiv e' (a312For_sl_two hK (by norm_num) le_rfl
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq) (IsPSL.of_mulEquiv e' hX'))

end CFSG.QuasithinUnique.Vol2Native.A312L
