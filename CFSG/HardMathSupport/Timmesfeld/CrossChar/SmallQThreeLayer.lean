module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.ChevalleyBinomial
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.LieType.Chevalley.C2E6BruhatBuilding
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

section Criterion

variable {K : Type*} [Group K]

@[expose] def NoNormalPPrime (p : ℕ) (L : Subgroup K) : Prop :=
  ∀ N : Subgroup K, N ≤ L → (∀ y ∈ L, ∀ x ∈ N, y * x * y⁻¹ ∈ N) →
    Nat.Coprime p (Nat.card N) → N = ⊥

theorem le_fixSub_of_noNormalPPrime [Finite K] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {H : Subgroup (MulAut K)}
    {e : MulAut K} {g : MulAut K}
    (hg : g ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({e} : Set (MulAut K))))
    {L : Subgroup K} (hLH : ∀ x ∈ L, MulAut.conj x ∈ H)
    (hLe : ∀ x ∈ L, MulAut.conj x * e = e * MulAut.conj x)
    (hLn : ∀ h ∈ H, h * e = e * h → ∀ x ∈ L, h x ∈ L) (hL : NoNormalPPrime p L) :
    L ≤ fixSub g := by
  set C := H ⊓ Subgroup.centralizer ({e} : Set (MulAut K)) with hC
  set O := GLAPPrimeCoreOf p C with hO
  have hOC : O ≤ C := gLAPPrimeCoreOf_le_self' C
  have hgC := hOC hg
  have hgH : g ∈ H := (Subgroup.mem_inf.1 hgC).1
  have hge : g * e = e * g :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hgC).2
  have hLC : ∀ x ∈ L, MulAut.conj x ∈ C := fun x hx =>
    Subgroup.mem_inf.2 ⟨hLH x hx, Subgroup.mem_centralizer_singleton_iff.2 (hLe x hx)⟩
  set N : Subgroup K := L ⊓ O.comap (MulAut.conj : K →* MulAut K) with hN
  have hNbot : N = ⊥ := by
    refine hL N inf_le_left ?_ ?_
    · intro y hy x hx
      obtain ⟨hxL, hxO⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨L.mul_mem (L.mul_mem hy hxL) (L.inv_mem hy), ?_⟩
      change MulAut.conj (y * x * y⁻¹) ∈ O
      rw [map_mul, map_mul, map_inv]
      exact gLAPPrimeCoreOf_conj_mem' _ (hLC y hy) _ hxO
    · have hcop := coprime_card_gLAPPrimeCoreOf' hp C
      have hle : N.map (MulAut.conj : K →* MulAut K) ≤ O := by
        rintro _ ⟨x, hx, rfl⟩
        exact (Subgroup.mem_inf.1 hx).2
      have hdvd : Nat.card (N.map (MulAut.conj : K →* MulAut K)) ∣ Nat.card O :=
        Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective hinj] at hdvd
      exact hcop.coprime_dvd_right hdvd
  intro x hx
  rw [mem_fixSub]
  have hgx : g x ∈ L := hLn g hgH hge x hx
  have hz : g x * x⁻¹ ∈ N := by
    refine Subgroup.mem_inf.2 ⟨L.mul_mem hgx (L.inv_mem hx), ?_⟩
    change MulAut.conj (g x * x⁻¹) ∈ O
    have h1 : MulAut.conj (g x * x⁻¹) =
        g * (MulAut.conj x * g⁻¹ * (MulAut.conj x)⁻¹) := by
      rw [map_mul, map_inv, ← mul_conj_mul_inv]
      group
    rw [h1]
    exact O.mul_mem hg (gLAPPrimeCoreOf_conj_mem' _ (hLC x hx) _ (O.inv_mem hg))
  rw [hNbot, Subgroup.mem_bot] at hz
  exact mul_inv_eq_one.1 hz

@[expose] def centralizerOf (e : MulAut K) : Subgroup K :=
  (Subgroup.centralizer ({e} : Set (MulAut K))).comap (MulAut.conj : K →* MulAut K)

theorem mem_centralizerOf {e : MulAut K} {x : K} :
    x ∈ centralizerOf e ↔ MulAut.conj x * e = e * MulAut.conj x := by
  rw [centralizerOf, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]

end Criterion

end CFSG.HardMathSupport.Timmesfeld.CrossChar
