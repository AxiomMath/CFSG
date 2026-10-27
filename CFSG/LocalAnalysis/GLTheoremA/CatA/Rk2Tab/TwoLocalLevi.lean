module

public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.RootOps.Comm
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType
open scoped Pointwise

section Main

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem torusGroup_pow_card_sub_one_eq_one
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    h ^ (Nat.card K - 1) = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [rootDiagUnit_pow, ← rootDiagUnit_one]
  congr 1
  funext j
  rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
  exact pow_card_eq_one'

theorem twoLocal_card_le_of_levi'
    {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (hL : ∀ (J : Set (Fin τ.rank)), J ≠ Set.univ → ∀ E : Subgroup (ModGL τ K),
      E ≤ subsystemGroup τ K J → IsElemAbelian p E → Nat.card E ≤ p ^ k)
    {R E : Subgroup (adjointGroup τ K)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set (adjointGroup τ K))) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ k := by
  have := Fact.mk Nat.prime_two
  have := Fact.mk hp
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨S, P, hPtop, hNP, -, -, hSP⟩ := holds_adjointGroup_tag τ K 2 R hR hR2
  have hBC : borelGroup τ K ≤ (adjointGroup τ K) := borelGroup_le_adjointGroup'
  have hUC : posUnipotent τ K ≤ (adjointGroup τ K) := le_sup_right.trans hBC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index (τ := τ) 2 hUC card_posUnipotent
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup τ K) (hUp.toSylow hUi) S
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1) Subgroup.le_normalizer
  have hB₀N : (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤
      Subgroup.normalizer (((posUnipotent τ K).subgroupOf (adjointGroup τ K) :
        Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h := Subgroup.mem_normalizer_iff.1 (hBN (Subgroup.mem_subgroupOf.1 hb)) (u : ModGL τ K)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hSeq : (S : Subgroup (adjointGroup τ K)) =
      ((posUnipotent τ K).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'def
  have hB₀P' : (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤ P' := by
    intro b hb
    have h1 : (MulAut.conj g).toMonoidHom b ∈ P := by
      apply hSP
      rw [hSeq]
      exact Subgroup.le_normalizer_map _ ⟨b, hB₀N hb, rfl⟩
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set A := P'.map (adjointGroup τ K).subtype with hAdef
  have hBA : borelGroup τ K ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hB₀P' (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hAC : A ≤ (adjointGroup τ K) := Subgroup.map_le_iff_le_comap.2 fun x _ => x.2
  have hAJ := (borel_overgroup_classification τ K).1 A hBA hAC
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ A} with hJdef
  have hcells := standard_parabolic_cells τ K
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra hall
    push Not at hall
    apply hPtop
    have hJu : J = Set.univ := Set.eq_univ_of_forall hall
    have hAtop : A = (adjointGroup τ K) := by rw [hAJ, hJu, hcells.2.2.2.2.2.1]
    have hP'top : P' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : ModGL τ K) ∈ A := by rw [hAtop]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Subtype.ext hyx] at hy
      exact hy
    rw [eq_top_iff]
    intro x _
    have hx : (MulAut.conj g⁻¹).toMonoidHom x ∈ P' := by rw [hP'top]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g⁻¹).injective hyx
    rw [← this]
    exact hy
  set J₀ : Set (Fin τ.rank) := {j | j ≠ i} with hJ₀def
  have hJJ₀ : J ⊆ J₀ := fun j hj hji => hi (hji ▸ hj)
  have hAJ₀ : A ≤ parabolicSubgroup τ K J₀ := by
    rw [hAJ]
    exact (hcells.2.2.2.1 J J₀).2 hJJ₀
  set F := (E.map (MulAut.conj g⁻¹).toMonoidHom).map (adjointGroup τ K).subtype with hFdef
  have hFA : F ≤ A := Subgroup.map_mono (Subgroup.map_mono (hER.trans hNP))
  have hFcard : Nat.card F = Nat.card E := by
    rw [Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hFel : IsElemAbelian p F :=
    hE.map _ |>.map _
  obtain ⟨hQP, -, -, hMP, -, -, huniq, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors (τ := τ) (K := K) J₀
  obtain ⟨-, hQ2, -⟩ := hfin 2
  have hcard := F4Rest.card_eq_mul_of_existsUnique hQP hMP huniq
  have hQp : ¬ p ∣ Nat.card (parabolicRadical τ K J₀) := by
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨x, -, hxM⟩ := F4Rest.exists_conj_le_of_card_eq_mul hMP hcard hQp (hFA.trans hAJ₀)
    hFel.isPGroup
  set F' := F.map (MulAut.conj x).toMonoidHom with hF'def
  have hF'el : IsElemAbelian p F' := hFel.map _
  have hF'L : F' ≤ subsystemGroup τ K J₀ := by
    intro y hy
    have hyM : y ∈ subsystemGroup τ K J₀ ⊔ torusGroup τ K := by
      rw [sup_comm]
      exact hxM hy
    exact F4Rest.mem_of_mem_sup_of_pow_eq_one
      (RootCentExc.torusGroup_le_normalizer_leviGens J₀) hp hpq
      (fun h hh => torusGroup_pow_card_sub_one_eq_one hh) hyM (hF'el.2 y hy)
  have hJ₀ne : J₀ ≠ Set.univ := by
    intro h
    have hmem : i ∈ J₀ := h ▸ Set.mem_univ i
    rw [hJ₀def] at hmem
    exact hmem rfl
  calc Nat.card E = Nat.card F' := by
        rw [hF'def, Subgroup.card_map_of_injective (MulAut.conj x).injective, hFcard]
    _ ≤ p ^ k := hL J₀ hJ₀ne F' hF'L hF'el

end Main

end CFSG.LocalAnalysis.GLTheoremA
