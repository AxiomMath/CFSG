module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Tools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Core

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem lemma99_core (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i20 : Input20_1)
    (i11 : Input11_6) (l23 : Lemma23) (hSt : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) {d : G} (hd : d ∈ B)
    (hd1 : d ≠ 1) {K X : Subgroup G} (hKM : K ≤ M)
    (hKC : K ≤ Subgroup.centralizer ({d} : Set G))
    (hKsn : IsSubnormal K (M ⊓ Subgroup.centralizer ({d} : Set G))) (hKperf : ⁅K, K⁆ = K)
    (hKπ : IsPiGroup p (↥K ⧸ GLAPPrimeCore p ↥K))
    (hXC : X ≤ Subgroup.centralizer ({d} : Set G)) (hX2 : IsPGroup 2 X)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hKX : ⁅X, K⁆ = K) :
    K ≤ piOf p d ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) := by
  have hp := hSt.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hd
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hSt hd1
  have hQcore : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hQ : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
    isKGroup_quotient' (isKGroup_of_isKProper hSt.kProper hCtop) _
  have hOut : ∀ E : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf E ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥E) :=
    fun E hE => outer_solvable_of_component hSch hQ hE
  obtain ⟨hXF, hXN⟩ := barX_two_subgroup_props i20 i11 l23 hSt hB hCtop hBC hXC hX2 hBX
  have hKC' : K ≤ C := hKC
  have hKbar : barX p C K = ⁅barX p C X, barX p C K⁆ := by
    conv_lhs => rw [← hKX]
    exact barX_commutator p hXC hKC'
  have hKperfbar : ⁅barX p C K, barX p C K⁆ = barX p C K := barX_perfect p hKC' hKperf
  have hKY : barX p C K ≤ ⨆ y ∈ barX p C K, GLBConj y (barX p C X) := by
    conv_lhs => rw [hKbar]
    exact commutator_le_iSup_conj _ _
  have hKN : ∀ E : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf E ⊤ →
      barX p C K ≤ Subgroup.normalizer (E : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := fun E hE =>
    le_of_le_iSup_conj
      (F := fun K' => Subgroup.normalizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_normalizer g K') hKY
      (fun y _ => hXN _ (isComponentOf_gLBConj hE y⁻¹))
  have : (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C)).Normal :=
    CFSG.LieType.BorelTits.pCore_normal p
  have hKF : barX p C K ≤ Subgroup.centralizer
      (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    le_of_le_iSup_conj
      (F := fun K' => Subgroup.centralizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_centralizer g K') hKY
      (fun y _ => by rw [gLBConj_eq_of_normal]; exact hXF)
  have hKE : barX p C K ≤ CFSG.ComponentClassification.Layer.subgroup
      (↥C ⧸ GLAPPrimeCore p ↥C) :=
    le_layer_of_perfect hp hQcore hOut hKperfbar hKF hKN
  set 𝒦 : Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) := {E | ∃ L₀ : Subgroup G,
    GLAPComponent p C L₀ ∧ IsStronglyLocallyOneBalanced p B d L₀ ∧ barX p C L₀ = E} with h𝒦
  have h𝒦c : ∀ E ∈ 𝒦, IsComponentOf E ⊤ := by
    rintro _ ⟨L₀, hL₀, -, rfl⟩
    exact hL₀.2.2.1
  have hXE : ∀ E ∈ 𝒦, barX p C X ≤ Subgroup.centralizer (E : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rintro _ ⟨L₀, hL₀, hbal, rfl⟩
    exact barX_le_centralizer_of_balanced i11 l23 hSt hB hd hd1 hXC hX2 hBX hL₀ hbal
  set A₁ : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
    ⨆ E ∈ {E : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) | IsComponentOf E ⊤ ∧ E ∉ 𝒦}, E with hA₁
  set B₁ : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) := ⨆ E ∈ 𝒦, E with hB₁
  have hAB : A₁ ≤ Subgroup.centralizer (B₁ : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    refine iSup₂_le fun E hE => Subgroup.le_centralizer_iff.2 (iSup₂_le fun E' hE' => ?_)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne E' E (h𝒦c E' hE') hE.1
        (fun h => hE.2 (h ▸ hE')))
  have hXA : barX p C X ≤ Subgroup.normalizer (A₁ : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    fun x hx => mem_normalizer_biSup fun E hE => hXN E hE.1 hx
  have hXB : barX p C X ≤ Subgroup.centralizer (B₁ : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    Subgroup.le_centralizer_iff.2 (iSup₂_le fun E hE =>
      Subgroup.le_centralizer_iff.1 (hXE E hE))
  have hEAB : CFSG.ComponentClassification.Layer.subgroup (↥C ⧸ GLAPPrimeCore p ↥C) ≤ A₁ ⊔ B₁ := by
    refine sSup_le fun E hE => ?_
    by_cases hE𝒦 : E ∈ 𝒦
    · exact le_trans (le_iSup₂_of_le E hE𝒦 (le_refl E) : E ≤ B₁) le_sup_right
    · exact le_trans (le_iSup₂_of_le E ⟨hE, hE𝒦⟩ (le_refl E) : E ≤ A₁) le_sup_left
  have hKA : barX p C K ≤ A₁ := by
    have := commutator_le_of_le_sup_centralizes hXA hAB hXB (hKE.trans hEAB)
    rw [← hKbar] at this
    exact this
  have hlam : lambdaOf p B d ≤ M := lambdaOf_le_of_isPreUniquenessTwoLocal hM hd hd1
  have hA₁M : A₁ ≤ barX p C (M ⊓ C) := by
    refine iSup₂_le fun E hE => ?_
    obtain ⟨L₀, hL₀, rfl⟩ := exists_glaPComponent_barX_eq C hE.1
    have hbal : ¬ IsStronglyLocallyOneBalanced p B d L₀ := fun h => hE.2 ⟨L₀, hL₀, h, rfl⟩
    have hLM : L₀ ≤ M := (le_sSup ⟨hL₀, hbal⟩ : L₀ ≤ lambdaOf p B d).trans hlam
    exact barX_mono p (le_inf hLM hL₀.1)
  have hKQ : IsSubnormal (barX p C K) ⊤ :=
    isSubnormal_trans'
      (isSubnormal_of_le_of_le (isSubnormal_barX p hKsn) hKA hA₁M)
      (isSubnormal_iSup_components _ (fun E hE => hE.1))
  have hPC : IsSubnormal (preimBarX p C K) C := isSubnormal_preimBarX p hKQ
  have hPle : preimBarX p C K ≤ M ⊓ C := by
    intro y hy
    obtain ⟨k, hk, hkn⟩ := exists_mul_of_mem_preimBarX p hy
    have hnM : k⁻¹ * y ∈ M := lemma91_i hSt hB hM hd hkn
    have hyM : y ∈ M := by
      have := M.mul_mem (hKM hk) hnM
      simpa using this
    exact ⟨hyM, preimBarX_le p C K hy⟩
  have hKP : IsSubnormal K (preimBarX p C K) :=
    isSubnormal_of_le_of_le hKsn (le_preimBarX p hKC') hPle
  have hKsnC : IsSubnormal K C := isSubnormal_trans' hKP hPC
  have hKpi : IsPiGroup p ↥(barX p C K) := IsPiGroup.of_mulEquiv (quotEquivBarX hp hKC' hKsnC) hKπ
  have hKcomp : IsComponentOf (barX p C K) ⊤ := ⟨le_top, hKQ, hKpi.1⟩
  obtain ⟨L', hL', hL'bar⟩ := exists_glaPComponent_barX_eq C hKcomp
  have hL'pi' : IsPiGroup p (↥L' ⧸ GLAPPrimeCore p ↥L') := by
    refine IsPiGroup.of_mulEquiv (quotEquivBarX hp hL'.1 hL'.2.1).symm ?_
    rw [hL'bar]
    exact hKpi
  have hL'pi : L' ≤ piOf p d :=
    le_iSup₂_of_le L' ⟨hL', hL'pi'⟩ le_rfl
  intro k hk
  obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := C) (J := L') (K := K)
    (by rw [hL'bar]) hk (hKC' hk)
  have : k = j * (j⁻¹ * k) := by simp
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hL'pi hj)) (Subgroup.mem_sup_right hjk)

end Core

end CFSG.LocalAnalysis.GLTheoremB
