module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Quasi

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankFourTheoremC CFSG.RankThreeCoreUniqueness.Helpers CFSG.Open
  CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem cyc_eq_one_of_pow_mem_coprime {Γ : Type} [Group Γ] {p k : ℕ} {g : Γ} (A : Subgroup Γ)
    (hpow : g ^ p ^ k = 1) (hgA : g ∈ A) (hA : p.Coprime (Nat.card A)) : g = 1 := by
  have h1 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf g ∣ Nat.card A := by
    have h := orderOf_dvd_natCard (⟨g, hgA⟩ : A)
    rwa [orderOf_mk] at h
  have h3 : Nat.Coprime (orderOf g) p := (Nat.Coprime.coprime_dvd_right h2 hA).symm
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h3) h1)

theorem pt_cyclic [Fact p.Prime] (hs : PtSchurBound) (hG : FrobGlobal G) (hl : PtPoint p P M x)
    {n : ℕ} {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} (hD : PtData p n P M x R K) :
    ∀ S : Subgroup G, S ≤ centralizer ((zpowers x : Subgroup G) : Set G) ⊓
      centralizer ((layerOf x : Subgroup G) : Set G) → IsPGroup p S → IsCyclic S := by
  intro S hS hSp
  have hSC : S ≤ centralizer ({x} : Set G) := by
    intro s hsS
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hS hsS)).1 x
      (Subgroup.mem_zpowers x)
    exact mem_centralizer_singleton_iff.mpr h1.symm
  have hSE : ∀ s ∈ S, ∀ y ∈ ptKx p x K, y * s = s * y := by
    intro s hsS y hy
    have h2 : s ∈ centralizer ((ptKx p x K : Subgroup G) : Set G) := by
      have h3 := (Subgroup.mem_inf.mp (hS hsS)).2
      rwa [pt_layer_eq_Kx hs hG hl hD] at h3
    exact Subgroup.mem_centralizer_iff.mp h2 y hy
  have hKperf : ⁅K, K⁆ = K := by
    have hq : Group.IsPerfect K := Group.isPerfect_def.mpr hD.red.component.2.2.1
    exact Subgroup.isPerfect_iff.mp hq
  have hmem : ∀ s : S, QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
      (Subgroup.inclusion hSC s) ∈ centralizer (K : Set (RedCent p x)) := by
    intro s
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : k ∈ ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
      rw [ptKx_map p x hKperf]
      exact hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk'
    have hy' : (y : G) ∈ ptKx p x K := Subgroup.mem_subgroupOf.mp hy
    have hcomm : y * Subgroup.inclusion hSC s = Subgroup.inclusion hSC s * y := by
      apply Subtype.ext
      exact hSE (s : G) s.2 (y : G) hy'
    rw [← map_mul, ← map_mul, hcomm]
  let g : S →* centralizer (K : Set (RedCent p x)) :=
    { toFun := fun s => ⟨QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        (Subgroup.inclusion hSC s), hmem s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro s hs1
    have h1 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        (Subgroup.inclusion hSC s) = 1 := congrArg Subtype.val hs1
    have h2 : Subgroup.inclusion hSC s ∈ primeComplementCore (G := centralizer ({x} : Set G)) p :=
      (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := hSp s
    have hk' : (Subgroup.inclusion hSC s) ^ p ^ k = 1 := by
      rw [← map_pow, hk, map_one]
    have h3 : Subgroup.inclusion hSC s = 1 :=
      cyc_eq_one_of_pow_mem_coprime _ hk' h2 (primeComplementCore_coprime p)
    have h4 : ((Subgroup.inclusion hSC s : centralizer ({x} : Set G)) : G) = 1 :=
      congrArg Subtype.val h3
    exact Subtype.ext h4
  haveI : IsCyclic (centralizer (K : Set (RedCent p x))) := hD.isCyclic
  exact isCyclic_of_injective g hinj

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
