module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOn
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.AltTypeOdd
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBYTwoCoreResidual

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.Open
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem blockU_eq_commutator_of_isElemAbelian_odd {W L : Subgroup G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hWL : W ≤ Subgroup.normalizer (L : Set G))
    (hLodd : L = Subgroup.closure {x : G | x ∈ L ∧ Odd (orderOf x)})
    (hQW : ⁅CFSG.Open.pCoreOf 2 L, L⁆ ≤ W) : blockU L = ⁅W, L⁆ := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hWp : IsPGroup 2 W := fun x => ⟨1, Subtype.ext (by simpa using hW.2 x x.2)⟩
  have hLQ : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hQp : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hUL : ⁅W, L⁆ ≤ L :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := W) (K := L)).mp hWL
  have hUW : ⁅W, L⁆ ≤ W := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right (H := L) (K := W)).mp hLW
  have h1 : ⁅W, L⁆ ≤ ⁅⁅W, L⁆, L⁆ :=
    CFSG.AGLEmbeddingD2.GN.commutator_le_commutator_commutator_of_odd hWp hLW hLodd.le
  have h2 : ⁅⁅W, L⁆, L⁆ ≤ ⁅CFSG.Open.pCoreOf 2 L, L⁆ := by
    refine Subgroup.commutator_mono ?_ le_rfl
    exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hUL
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr
        (Subgroup.normalizer_commutator_ge_right W L))
      (hWp.to_le hUW)
  have h3 : ⁅CFSG.Open.pCoreOf 2 L, L⁆ ≤ ⁅⁅CFSG.Open.pCoreOf 2 L, L⁆, L⁆ :=
    CFSG.AGLEmbeddingD2.GN.commutator_le_commutator_commutator_of_odd hQp hLQ hLodd.le
  have h4 : ⁅⁅CFSG.Open.pCoreOf 2 L, L⁆, L⁆ ≤ ⁅W, L⁆ :=
    Subgroup.commutator_mono hQW le_rfl
  exact le_antisymm (h3.trans h4) (h1.trans h2)

theorem exists_altHom_ker_pCore {W L M : Subgroup G} {n : ℕ}
    (hn5 : 5 ≤ n) (hLM : L ≤ M)
    (hLodd : L = Subgroup.closure {x : G | x ∈ L ∧ Odd (orderOf x)})
    (hLC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (W : Set G)))
    (θ : ↥M →* Equiv.Perm (Fin n))
    (hθsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ l ∈ L, ∃ hl : l ∈ M, θ ⟨l, hl⟩ = σ)
    (hθker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (W : Set G)) :
    ∃ (θL : ↥L →* Equiv.Perm (Fin n)) (α : ↥L →* alternatingGroup (Fin n)),
      (∀ l : ↥L, (α l : Equiv.Perm (Fin n)) = θL l) ∧
      (∀ l : ↥L, θL l = θ ⟨(l : G), hLM l.2⟩) ∧
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  let θL : ↥L →* Equiv.Perm (Fin n) := θ.comp (Subgroup.inclusion hLM)
  let ψ : ↥L →* ℤˣ := Equiv.Perm.sign.comp θL
  have hnoTwo := CFSG.QuasithinUnique.SteinbergBY.hasNoTwoQuotient_of_le_oddOrderSubgroup
    (Z := L) (by rw [CFSG.QuasithinUnique.Setup.oddOrderSubgroup]; exact hLodd.le)
  have hψeq : ψ = 1 := by
    have hP : IsPGroup 2 (↥L ⧸ ψ.ker) := by
      have hcardle : Nat.card (↥L ⧸ ψ.ker) ≤ 2 := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
        calc Nat.card ↥(ψ.range) ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
          _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
      have hdvd : Nat.card (↥L ⧸ ψ.ker) ∣ 2 := by
        have hpos : 0 < Nat.card (↥L ⧸ ψ.ker) := Nat.card_pos
        rcases (by omega : Nat.card (↥L ⧸ ψ.ker) = 1 ∨
            Nat.card (↥L ⧸ ψ.ker) = 2) with h | h
        · rw [h]; exact one_dvd 2
        · rw [h]
      exact IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by simpa using hdvd)
    have hNtop : ψ.ker = ⊤ := hnoTwo ψ.ker hP
    exact MonoidHom.ker_eq_top_iff.mp hNtop
  have hsign : ∀ l : ↥L, Equiv.Perm.sign (θL l) = 1 := by
    intro l
    have := congrArg (fun f : ↥L →* ℤˣ => f l) hψeq
    simpa [ψ] using this
  let α : ↥L →* alternatingGroup (Fin n) :=
    θL.codRestrict _ fun l => (Equiv.Perm.mem_alternatingGroup).mpr (hsign l)
  have hαval : ∀ l : ↥L, (α l : Equiv.Perm (Fin n)) = θL l := fun l => rfl
  have hαsurj : Function.Surjective α := by
    intro σ
    obtain ⟨l, hlL, hlM, hl⟩ := hθsurj σ.1 σ.2
    refine ⟨⟨l, hlL⟩, Subtype.ext ?_⟩
    rw [hαval]
    show θ ⟨l, hLM hlL⟩ = σ.1
    rw [← hl]
  have hker_le : α.ker ≤ (L ⊓ Subgroup.centralizer (W : Set G)).subgroupOf L := by
    intro l hl
    rw [Subgroup.mem_subgroupOf]
    refine ⟨l.2, ?_⟩
    have h1 : θL l = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    exact hθker ⟨(l : G), hLM l.2⟩ h1
  have hkerP : IsPGroup 2 α.ker :=
    (hLC.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm).to_le hker_le
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    refine le_antisymm ?_ ?_
    · exact CFSG.LieType.BorelTits.le_pCore (r := 2) (inferInstance : α.ker.Normal) hkerP
    · have hmapP : IsPGroup 2 ((CFSG.pCore 2 ↥L).map α) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map α
      haveI : ((CFSG.pCore 2 ↥L).map α).Normal :=
        (inferInstance : (CFSG.pCore 2 ↥L).Normal).map α hαsurj
      have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
        alternatingGroup.isSimpleGroup (by simpa using hn5)
      rcases hsimple.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥L).map α) with hbot | htop
      · rwa [Subgroup.map_eq_bot_iff] at hbot
      · exfalso
        have hAnP : IsPGroup 2 (alternatingGroup (Fin n)) := by
          have := hmapP
          rw [htop] at this
          exact this.of_equiv Subgroup.topEquiv
        have hnontriv : Nontrivial (alternatingGroup (Fin n)) :=
          alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
        have hnc : ¬ IsMulCommutative (alternatingGroup (Fin n)) := by
          rw [alternatingGroup.isMulCommutative_iff_card_le_three]
          simp
          omega
        have hnc' : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
          rw [isMulCommutative_iff] at hnc
          push Not at hnc
          exact hnc
        obtain ⟨-, hZbot⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc'
        have hZnt : Nontrivial (Subgroup.center (alternatingGroup (Fin n))) :=
          hAnP.center_nontrivial
        rw [hZbot] at hZnt
        exact not_nontrivial_iff_subsingleton.mpr inferInstance hZnt
  exact ⟨θL, α, hαval, fun _ => rfl, hαsurj, hαker⟩

theorem blockU_le_inf_centralizer_of_commutator {W L : Subgroup G}
    (hW : CFSG.Open.IsElemAbelian 2 W) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hQC : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hU : blockU L = ⁅W, L⁆) :
    blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) ∧
      ∀ x ∈ blockU L, x ^ 2 = 1 := by
  have hQL : ⁅CFSG.Open.pCoreOf 2 L, L⁆ ≤ CFSG.Open.pCoreOf 2 L :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L)
      (K := CFSG.Open.pCoreOf 2 L)).mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hUW : ⁅W, L⁆ ≤ W := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right (H := L) (K := W)).mp hLW
  have hUQ : ⁅W, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
    rw [← hU]
    exact hQL
  refine ⟨?_, ?_⟩
  · rw [hU]
    refine le_inf hUQ ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hQC hq) u (hUW hu)).symm
  · intro x hx
    exact hW.2 x (hUW (hU ▸ hx))

theorem theta_eq_one_of_centralizes_commutator {W L M : Subgroup G} {n : ℕ}
    (hn5 : 5 ≤ n) (hLM : L ≤ M)
    {π : ↥⁅W, L⁆ →* Multiplicative (altHeart n)} (hπ : Function.Surjective π)
    {θ : ↥M →* Equiv.Perm (Fin n)} (hsec : SectionEquiv ⁅W, L⁆ M π θ)
    {l : G} (hlL : l ∈ L) (hlU : l ∈ Subgroup.centralizer ((⁅W, L⁆ : Subgroup G) : Set G)) :
    θ ⟨l, hLM hlL⟩ = 1 := by
  refine perm_eq_one_of_altHeart_fixed hn5 _ fun x => ?_
  obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (QuotientAddGroup.mk x : altHeart n))
  have hcomm : (u : G) = (⟨l, hLM hlL⟩ : ↥M) * u * (⟨l, hLM hlL⟩ : ↥M)⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.mp hlU (u : G) u.2
    simp only [Subgroup.coe_inv, Subgroup.coe_mk]
    rw [← h1]
    group
  have h1 := hsec ⟨l, hLM hlL⟩ u u hcomm x (by rw [hu]; rfl)
  rw [hu] at h1
  exact h1.symm

theorem charTwo_of_naturalSectionOn {W L M : Subgroup G} {n : ℕ}
    (hn5 : 5 ≤ n) (hLM : L ≤ M)
    (hQC : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hU : blockU L = ⁅W, L⁆)
    {θL : ↥L →* Equiv.Perm (Fin n)} {α : ↥L →* alternatingGroup (Fin n)}
    (hαval : ∀ l : ↥L, (α l : Equiv.Perm (Fin n)) = θL l)
    (hαker : α.ker = CFSG.pCore 2 ↥L)
    {π : ↥⁅W, L⁆ →* Multiplicative (altHeart n)} (hπ : Function.Surjective π)
    {θ : ↥M →* Equiv.Perm (Fin n)} (hsec : SectionEquiv ⁅W, L⁆ M π θ)
    (hθL : ∀ l : ↥L, θL l = θ ⟨(l : G), hLM l.2⟩) :
    CharTwo L := by
  intro x hx
  obtain ⟨hxL, hxC⟩ := hx
  have hUQ : ⁅W, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
    rw [← hU]
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := L)
      (K := CFSG.Open.pCoreOf 2 L)).mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hxU : x ∈ Subgroup.centralizer ((⁅W, L⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp hxC u (hUQ hu)
  have hθ1 : θL ⟨x, hxL⟩ = 1 := by
    rw [hθL]
    exact theta_eq_one_of_centralizes_commutator hn5 hLM hπ hsec hxL hxU
  have hα1 : α ⟨x, hxL⟩ = 1 := by
    ext
    rw [hαval, hθ1]
    rfl
  have hmem : (⟨x, hxL⟩ : ↥L) ∈ α.ker := hα1
  rw [hαker] at hmem
  exact (CFSG.mem_openPCoreOf_iff ⟨x, hxL⟩).mpr hmem

theorem isQuasisimple_quotient_pCore_of_altHom {L : Subgroup G} {n : ℕ} (hn5 : 5 ≤ n)
    {α : ↥L →* alternatingGroup (Fin n)} (hαsurj : Function.Surjective α)
    (hαker : α.ker = CFSG.pCore 2 ↥L) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn5)
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin n)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
    omega
  have hnc' : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    exact hnc
  have hAnQ : CFSG.IsQuasisimple (alternatingGroup (Fin n)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc').1
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hαker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαsurj)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hAnQ

theorem blockZ_clause_of_naturalSectionOn {W L M : Subgroup G} {n : ℕ} (hn5 : 5 ≤ n)
    (hU : blockU L = ⁅W, L⁆)
    {π : ↥⁅W, L⁆ →* Multiplicative (altHeart n)} (hπ : Function.Surjective π)
    (hπker : π.ker = (⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅W, L⁆)
    {θ : ↥M →* Equiv.Perm (Fin n)} (hsec : SectionEquiv ⁅W, L⁆ M π θ)
    (hθsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ l ∈ L, ∃ hl : l ∈ M, θ ⟨l, hl⟩ = σ) :
    blockZ L < blockU L ∧
      ∀ W' : Subgroup G, blockZ L ≤ W' → W' ≤ blockU L →
        L ≤ Subgroup.normalizer (W' : Set G) →
          W' = blockZ L ∨ W' = blockU L := by
  have hZ : blockZ L = ⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← hU]; rfl
  constructor
  · rw [hZ, hU]
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    have hker_top : π.ker = ⊤ := by
      rw [hπker, hEq]
      simp
    have hπ1 : π = 1 := MonoidHom.ker_eq_top_iff.mp hker_top
    haveI : Nontrivial (altHeart n) := altHeart_nontrivial (by omega)
    haveI : Nontrivial (Multiplicative (altHeart n)) := inferInstance
    obtain ⟨v, hv⟩ := exists_ne (1 : Multiplicative (altHeart n))
    obtain ⟨u, hu⟩ := hπ v
    rw [hπ1, MonoidHom.one_apply] at hu
    exact hv hu.symm
  · intro W' hZW' hW'U hNW'
    have hW'U' : W' ≤ ⁅W, L⁆ := by rwa [hU] at hW'U
    let U' : AddSubgroup (altHeart n) :=
      { carrier := {v | ∃ w : ↥⁅W, L⁆, (w : G) ∈ W' ∧ π w = Multiplicative.ofAdd v}
        zero_mem' := ⟨1, W'.one_mem, by simp⟩
        add_mem' := by
          rintro v₁ v₂ ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
          refine ⟨w₁ * w₂, W'.mul_mem hw₁ hw₂, ?_⟩
          rw [map_mul, h₁, h₂, ← ofAdd_add]
        neg_mem' := by
          rintro v ⟨w, hw, h⟩
          refine ⟨w⁻¹, W'.inv_mem hw, ?_⟩
          rw [map_inv, h]
          simp }
    have hmemU' : ∀ v : altHeart n, v ∈ U' ↔
        ∃ w : ↥⁅W, L⁆, (w : G) ∈ W' ∧ π w = Multiplicative.ofAdd v := fun v => Iff.rfl
    have hinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ x : evenWeight n,
        (QuotientAddGroup.mk x : altHeart n) ∈ U' →
          (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) ∈ U' := by
      intro σ hσ x hx
      obtain ⟨w, hwW, hwx⟩ := (hmemU' _).mp hx
      obtain ⟨l, hlL, hlM, hlθ⟩ := hθsurj σ hσ
      have hnorm : (l : G) * (w : G) * (l : G)⁻¹ ∈ W' :=
        (Subgroup.mem_normalizer_iff.mp (hNW' hlL) (w : G)).mp hwW
      have hUnorm : (l : G) * (w : G) * (l : G)⁻¹ ∈ ⁅W, L⁆ :=
        (Subgroup.mem_normalizer_iff.mp
          (Subgroup.normalizer_commutator_ge_right W L hlL) (w : G)).mp w.2
      let w' : ↥⁅W, L⁆ := ⟨(l : G) * (w : G) * (l : G)⁻¹, hUnorm⟩
      refine (hmemU' _).mpr ⟨w', hnorm, ?_⟩
      have hcomm : (w' : G) = (⟨l, hlM⟩ : ↥M) * w * (⟨l, hlM⟩ : ↥M)⁻¹ := rfl
      have h1 := hsec ⟨l, hlM⟩ w w' hcomm x hwx
      rw [hlθ] at h1
      exact h1
    rcases altHeart_irreducible (by omega : 4 ≤ n) U' hinv with hbot | htop
    · left
      rw [hZ]
      have hZW'' : ⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ W' := by rwa [hZ] at hZW'
      refine le_antisymm ?_ hZW''
      intro x hxW'
      have hxU : x ∈ ⁅W, L⁆ := hW'U' hxW'
      have hπ0 : π ⟨x, hxU⟩ = 1 := by
        have hmem : Multiplicative.toAdd (π ⟨x, hxU⟩) ∈ U' :=
          (hmemU' _).mpr ⟨⟨x, hxU⟩, hxW', by simp⟩
        rw [hbot, AddSubgroup.mem_bot] at hmem
        exact Multiplicative.toAdd.injective hmem
      have hkernel : (⟨x, hxU⟩ : ↥⁅W, L⁆) ∈ π.ker := hπ0
      rw [hπker, Subgroup.mem_subgroupOf] at hkernel
      exact ⟨hxU, hkernel.2⟩
    · right
      refine le_antisymm hW'U ?_
      intro x hxU
      rw [hU] at hxU
      have hxmem : Multiplicative.toAdd (π ⟨x, hxU⟩) ∈ U' := by rw [htop]; trivial
      obtain ⟨a, haW, hax⟩ := (hmemU' _).mp hxmem
      have hπeq : π a = π ⟨x, hxU⟩ := by
        rw [← ofAdd_toAdd (π ⟨x, hxU⟩)]
        exact hax
      have hmemker : (⟨(a : G)⁻¹ * x, (⁅W, L⁆).mul_mem ((⁅W, L⁆).inv_mem a.2) hxU⟩ :
          ↥⁅W, L⁆) ∈ π.ker := by
        change π ⟨(a : G)⁻¹ * x, _⟩ = 1
        rw [show (⟨(a : G)⁻¹ * x, _⟩ : ↥⁅W, L⁆) = a⁻¹ * ⟨x, hxU⟩ from rfl,
          map_mul, map_inv, hπeq, inv_mul_cancel]
      rw [hπker, Subgroup.mem_subgroupOf] at hmemker
      have hprod : (a : G)⁻¹ * x ∈ blockZ L := by
        rw [hZ]; exact ⟨hmemker.1, hmemker.2⟩
      have hxW : x ∈ W' := by
        have h1 := W'.mul_mem haW (hZW' hprod)
        rwa [mul_inv_cancel_left] at h1
      exact hxW

theorem inClassXBlock_of_naturalSectionOn {W L M : Subgroup G} {n : ℕ} (hn : Odd n)
    (hn5 : 5 ≤ n) (hW : CFSG.Open.IsElemAbelian 2 W) (hLM : L ≤ M)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hWL : W ≤ Subgroup.normalizer (L : Set G))
    (hLodd : L = Subgroup.closure {x : G | x ∈ L ∧ Odd (orderOf x)})
    (hQW : ⁅CFSG.Open.pCoreOf 2 L, L⁆ ≤ W)
    (hQC : CFSG.Open.pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hLC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (W : Set G)))
    (hnat : NaturalSectionOn W L M n) :
    CFSG.AGLEmbedding.InClassXBlock L := by
  obtain ⟨π, θ, hπsurj, hπker, hθsurj, hsec, hθker⟩ := hnat
  have hU : blockU L = ⁅W, L⁆ :=
    blockU_eq_commutator_of_isElemAbelian_odd hW hLW hWL hLodd hQW
  obtain ⟨θL, α, hαval, hθL, hαsurj, hαker⟩ :=
    exists_altHom_ker_pCore hn5 hLM hLodd hLC θ hθsurj hθker
  have hnoTwo := CFSG.QuasithinUnique.SteinbergBY.hasNoTwoQuotient_of_le_oddOrderSubgroup
    (Z := L) (by rw [CFSG.QuasithinUnique.Setup.oddOrderSubgroup]; exact hLodd.le)
  have hshort : IsShort2 L := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro N hN hq
      exact hnoTwo N hq
    · exact charTwo_of_naturalSectionOn hn5 hLM hQC hU hαval hαker hπsurj hsec hθL
    · exact blockU_le_inf_centralizer_of_commutator hW hLW hQC hU
    · exact Or.inl (isQuasisimple_quotient_pCore_of_altHom hn5 hαsurj hαker)
    · exact blockZ_clause_of_naturalSectionOn hn5 hU hπsurj hπker hsec hθsurj
  have hnatType : IsAltNaturalType L n := by
    let β : ↥(blockU L) →* Multiplicative (altHeart n) :=
      π.comp (Subgroup.inclusion hU.le)
    have hβval : ∀ u : ↥(blockU L), β u = π ⟨u, hU.le u.2⟩ := fun u => rfl
    have hβsurj : Function.Surjective β := by
      intro y
      obtain ⟨u, hu⟩ := hπsurj y
      refine ⟨⟨u, hU.symm ▸ u.2⟩, ?_⟩
      simpa [hβval] using hu
    have hβker : β.ker = (blockZ L).subgroupOf (blockU L) := by
      ext u
      rw [MonoidHom.mem_ker, hβval]
      have hZ : blockZ L = ⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
        rw [← hU]; rfl
      rw [hZ, Subgroup.mem_subgroupOf]
      rw [show (π ⟨u, hU.le u.2⟩ = 1) ↔
        ((⟨u, hU.le u.2⟩ : ↥⁅W, L⁆) ∈ π.ker) from Iff.rfl,
        hπker, Subgroup.mem_subgroupOf]
    have hβeq : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
        ∀ x : evenWeight n, Multiplicative.toAdd (β u) = (x : altHeart n) →
          Multiplicative.toAdd (β v) =
            (evenWeightPerm (α ℓ : Equiv.Perm (Fin n)) x : altHeart n) := by
      intro ℓ u v huv x hx
      have hx' : Multiplicative.toAdd (π ⟨u, hU.le u.2⟩) = (x : altHeart n) := hx
      have huv' : ((⟨v, hU.le v.2⟩ : ↥⁅W, L⁆) : G) =
          (ℓ : G) * (⟨u, hU.le u.2⟩ : ↥⁅W, L⁆) * (ℓ : G)⁻¹ := huv
      have h1 := hsec ⟨(ℓ : G), hLM ℓ.2⟩ ⟨u, hU.le u.2⟩ ⟨v, hU.le v.2⟩ huv' x hx'
      rw [← hθL ℓ, ← hαval ℓ] at h1
      exact h1
    exact ⟨α, hαsurj, hαker, β, hβsurj, hβker, hβeq⟩
  obtain ⟨k, rfl⟩ := hn
  refine ⟨hshort, Or.inr ⟨k, ?_, ?_⟩⟩
  · omega
  · exact CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.isAltType_of_isAltNaturalType_odd
      ⟨k, rfl⟩ hnatType

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
