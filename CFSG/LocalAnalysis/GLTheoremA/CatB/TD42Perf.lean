module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD42
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem perf_le_core_of_E9 {G : Type} [Group G] [Finite G] {X L F : Subgroup G}
    (hL : GLAPComponent 3 X L) (hE : E9Solv (PSimple 3 L))
    (hFN : F ≤ Subgroup.normalizer (L : Set G)) (hF : IsElemAbelian 3 F)
    (hcard : Nat.card F = 3 ^ 2) (hfaith : ∀ g ∈ F, CentMod 3 L g → g = 1) {K : Subgroup G}
    (hK : K ≤ L ⊓ Subgroup.centralizer (F : Set G)) (hKperf : (⁅K, K⁆ : Subgroup G) = K) :
    K ≤ GLAPPrimeCoreOf 3 L := by
  classical
  have hKL : K ≤ L := hK.trans inf_le_left
  have hKC : ∀ x ∈ K, x ∈ Subgroup.centralizer (F : Set G) := fun x hx => (Subgroup.mem_inf.1 (hK hx)).2
  let φ : ↥F →* MulAut (PSimple 3 L) := (chevAut 3 L).comp (Subgroup.inclusion hFN)
  have hφ : ∀ d : ↥F, φ d = chevAut 3 L ⟨d.1, hFN d.2⟩ := fun d => rfl
  have hker : ∀ d : ↥F, φ d = 1 ↔ d.1 ∈ centModSubgroup 3 L := by
    intro d
    rw [hφ, chevAut_eq_one_iff Nat.prime_three hL (hFN d.2), centMod_iff]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    exact Subtype.ext (hfaith d.1 d.2 (centMod_iff.2 ((hker d).1 hd)))
  have hEcard : Nat.card φ.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]
    norm_num
  have hEel : IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨e, he⟩ := MonoidHom.mem_range.1 b.2
      have hc : d * e = e * d := hF.1.is_comm.comm d e
      apply Subtype.ext
      show (a : MulAut (PSimple 3 L)) * (b : MulAut (PSimple 3 L)) =
        (b : MulAut (PSimple 3 L)) * (a : MulAut (PSimple 3 L))
      rw [← hd, ← he, ← map_mul, ← map_mul, hc]
    · rintro _ ⟨d, rfl⟩
      rw [← map_pow]
      have h3 : d ^ 3 = 1 := Subtype.ext (by simpa using hF.2 d.1 d.2)
      rw [h3, map_one]
  have hsolv : Group.IsSolvable ↥(i269Fix φ.range) := hE φ.range hEel hEcard
  let πK : ↥K →* PSimple 3 L := (chevQuotHom 3 L).comp (Subgroup.inclusion hKL)
  have hrange : πK.range ≤ i269Fix φ.range := by
    intro k hk
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hk
    rw [mem_i269Fix]
    intro α hα
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.1 hα
    rw [hφ]
    exact chevAut_fix_chevQuotHom hFN d.2 (hKL x.2) (hKC x.1 x.2)
  haveI : Group.IsSolvable ↥(i269Fix φ.range) := hsolv
  haveI : Group.IsSolvable ↥πK.range := isSolvable_of_le_isSolvable hrange
  haveI hKp : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hKperf
  haveI : Group.IsPerfect ↥πK.range := Group.IsPerfect.range πK
  have hπ1 : πK = 1 := by
    by_contra hne
    have hbot : πK.range ≠ ⊥ := by
      intro h
      apply hne
      ext x
      have : πK x ∈ πK.range := ⟨x, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      simpa using this
    haveI : Nontrivial ↥πK.range := (Subgroup.nontrivial_iff_ne_bot _).2 hbot
    exact Group.IsPerfect.not_isSolvable (G := ↥πK.range) inferInstance
  let ψK : ↥K →* PQuot 3 L := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hKL)
  have hcent : ∀ x : ↥K, ψK x ∈ Subgroup.center (PQuot 3 L) := by
    intro x
    have h1 : πK x = 1 := by rw [hπ1]; rfl
    exact (QuotientGroup.eq_one_iff _).1 h1
  haveI : Group.IsPerfect ↥ψK.range := Group.IsPerfect.range ψK
  have hψ1 : ψK = 1 := by
    by_contra hne
    have hbot : ψK.range ≠ ⊥ := by
      intro h
      apply hne
      ext x
      have : ψK x ∈ ψK.range := ⟨x, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      simpa using this
    haveI : Nontrivial ↥ψK.range := (Subgroup.nontrivial_iff_ne_bot _).2 hbot
    apply Group.IsPerfect.not_isMulCommutative (G := ↥ψK.range)
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    show (a : PQuot 3 L) * b = b * a
    rw [← hx, ← hy]
    exact ((Subgroup.mem_center_iff.1 (hcent x)) (ψK y)).symm
  intro x hx
  have h1 : ψK ⟨x, hx⟩ = 1 := by rw [hψ1]; rfl
  exact (chev_mem_glaPPrimeCoreOf_iff (hKL hx)).2 ((QuotientGroup.eq_one_iff _).1 h1)

theorem td42PerfAt_holds
    (G : Type) [Group G] [Finite G] : TD42PerfAt G := by
  intro X L F hL hcat hF hFN hcard hfaith K hK hKperf
  exact perf_le_core_of_E9 hL (e9Solv_td4two _ hcat) hFN hF hcard hfaith hK hKperf

end CFSG.LocalAnalysis.GLTheoremA

end
