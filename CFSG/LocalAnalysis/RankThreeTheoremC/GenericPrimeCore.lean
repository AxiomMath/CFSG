module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFixedPoints
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFrobenius
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerCoprime
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

@[expose] def FPFSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T N : Subgroup G) (x : G),
    IsPGroup 2 T → T ≤ N → Group.IsSolvable N → N ≤ normalizer (T : Set G) →
    N ⊓ centralizer (T : Set G) ≤ T →
    (∀ W : Subgroup G, W ≤ N → IsPGroup 2 W → N ≤ normalizer (W : Set G) → W ≤ T) →
    ¬ p ∣ Nat.card N → x ^ p = 1 → x ≠ 1 → x ∈ normalizer (N : Set G) →
    x ∈ normalizer (T : Set G) → (∀ t ∈ T, x * t = t * x → t = 1) →
    ∀ n ∈ N, n⁻¹ * x⁻¹ * n * x ∈ T

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_inf_centralizer_of_fpf {T N : Subgroup G} {x : G} (hTN : T ≤ N)
    (hxT : x ∈ normalizer (T : Set G)) (hfpf : ∀ t ∈ T, x * t = t * x → t = 1)
    (hcomm : ∀ n ∈ N, n⁻¹ * x⁻¹ * n * x ∈ T) {n : G} (hn : n ∈ N) :
    ∃ s ∈ T, s * n ∈ N ⊓ centralizer ({x} : Set G) := by
  classical
  have ht₁ : x⁻¹ * n * x * n⁻¹ ∈ T := by
    have := T.inv_mem (hcomm n⁻¹ (N.inv_mem hn))
    simpa [mul_assoc] using this
  have hconj : ∀ s ∈ T, x⁻¹ * s * x ∈ T := fun s hs => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxT) s).mp hs
    simpa using this
  let ψ : T → T := fun s => ⟨(x⁻¹ * s * x)⁻¹ * s, T.mul_mem (T.inv_mem (hconj s s.2)) s.2⟩
  have hψ : Function.Injective ψ := by
    intro s s' h
    have h1 : (x⁻¹ * (s : G) * x)⁻¹ * s = (x⁻¹ * (s' : G) * x)⁻¹ * s' := congrArg Subtype.val h
    have h1' : (s : G)⁻¹ * x * s = (s' : G)⁻¹ * x * s' := by
      have := congrArg (fun y => x * y) h1
      calc (s : G)⁻¹ * x * s = x * ((x⁻¹ * (s : G) * x)⁻¹ * s) := by group
        _ = x * ((x⁻¹ * (s' : G) * x)⁻¹ * s') := this
        _ = (s' : G)⁻¹ * x * s' := by group
    have h2 : (s' : G) * (s : G)⁻¹ ∈ T := T.mul_mem s'.2 (T.inv_mem s.2)
    have h3 : x * ((s' : G) * (s : G)⁻¹) = ((s' : G) * (s : G)⁻¹) * x := by
      calc x * ((s' : G) * (s : G)⁻¹) = (s' : G) * ((s' : G)⁻¹ * x * s') * (s : G)⁻¹ := by group
        _ = (s' : G) * ((s : G)⁻¹ * x * s) * (s : G)⁻¹ := by rw [h1']
        _ = ((s' : G) * (s : G)⁻¹) * x := by group
    have h6 := hfpf _ h2 h3
    rw [mul_inv_eq_one] at h6
    exact Subtype.ext h6.symm
  have hsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψ
  obtain ⟨s, hs⟩ := hsurj ⟨x⁻¹ * n * x * n⁻¹, ht₁⟩
  have hs' : (x⁻¹ * (s : G) * x)⁻¹ * s = x⁻¹ * n * x * n⁻¹ := congrArg Subtype.val hs
  have hs'' : (s : G)⁻¹ * x * s = n * x * n⁻¹ := by
    have := congrArg (fun y => x * y) hs'
    calc (s : G)⁻¹ * x * s = x * ((x⁻¹ * (s : G) * x)⁻¹ * s) := by group
      _ = x * (x⁻¹ * n * x * n⁻¹) := this
      _ = n * x * n⁻¹ := by group
  refine ⟨s, s.2, N.mul_mem (hTN s.2) hn, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc ((s : G) * n) * x = (s : G) * (n * x * n⁻¹) * n := by group
    _ = (s : G) * ((s : G)⁻¹ * x * s) * n := by rw [hs'']
    _ = x * ((s : G) * n) := by group

theorem rankThreePrimeCore_le_of_isSolvable (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) (hF : FPFSolvable) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hx : IsGenericPoint p P M x) (h5 : 5 ≤ p) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m))
    (hsolv : Group.IsSolvable (rankThreePrimeCore p M)) :
    rankThreePrimeCore p M ≤ pCoreOf 2 M ⊔
      centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨hNM, hMN, hNcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have hT2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTN : pCoreOf 2 M ≤ rankThreePrimeCore p M :=
    pCoreOf_two_le_rankThreePrimeCore Fact.out (sigmaA_odd p hp) M
  have hMT : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hNT : rankThreePrimeCore p M ≤ normalizer (pCoreOf 2 M : Set G) := hNM.trans hMT
  have hC : rankThreePrimeCore p M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    fun n hn => hS.charTwo M hM.1.1 ⟨hNM hn.1, hn.2⟩
  have hO2 : ∀ W : Subgroup G, W ≤ rankThreePrimeCore p M → IsPGroup 2 W →
      rankThreePrimeCore p M ≤ normalizer (W : Set G) → W ≤ pCoreOf 2 M := by
    intro W hWN hW2 hNW
    have h1 : W ≤ pCoreOf 2 (rankThreePrimeCore p M) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWN hNW hW2
    have h2 : pCoreOf 2 (rankThreePrimeCore p M) ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hNM)
        (hMN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact h1.trans h2
  obtain ⟨-, ⟨hxM, hx1, hxp, -, -⟩, -, -⟩ := id hx
  have hfpf : ∀ t ∈ pCoreOf 2 M, x * t = t * x → t = 1 := by
    intro t ht htx
    have : t ∈ pCoreOf 2 M ⊓ centralizer ({x} : Set G) :=
      ⟨ht, Subgroup.mem_centralizer_singleton_iff.mpr htx.symm⟩
    rw [pCoreOf_two_inf_centralizer_eq_bot hS hD1 hU0 hp hM hx h5 hm e] at this
    exact Subgroup.mem_bot.mp this
  have hcomm := hF G p (pCoreOf 2 M) (rankThreePrimeCore p M) x hT2 hTN hsolv hNT hC hO2
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hNcop) hxp hx1 (hMN hxM) (hMT hxM) hfpf
  intro n hn
  obtain ⟨s, hsT, hsn⟩ := exists_mul_mem_inf_centralizer_of_fpf hTN (hMT hxM) hfpf hcomm hn
  have hZ := primeCore_inf_centralizer_le_centralizer_layer hS hp hM hx hm e hsn
  have hn' : n = s⁻¹ * (s * n) := by group
  rw [hn']
  exact Subgroup.mul_mem_sup ((pCoreOf 2 M).inv_mem hsT) hZ

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC
