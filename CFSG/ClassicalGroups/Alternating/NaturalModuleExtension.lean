module

public import CFSG.ClassicalGroups.F2Fixed
public import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.ClassicalGroups.Alternating

open Module Submodule
open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

section Commutator

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

theorem mem_ker_comm {a : G} {m : M} : m ∈ (F2Fixed.comm M a).ker ↔ a • m = m := by
  rw [AddMonoidHom.mem_ker, F2Fixed.comm_apply, sub_eq_zero]

theorem index_finset_inf_le {ι : Type*} (s : Finset ι) (A : ι → AddSubgroup M) (n : ℕ)
    (h : ∀ i ∈ s, (A i).index ≤ n) : (s.inf A).index ≤ n ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert, Finset.card_insert_of_notMem hi, pow_succ']
    exact (AddSubgroup.index_inf_le).trans
      (Nat.mul_le_mul (h i (Finset.mem_insert_self _ _))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

end Commutator

section Natural

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}
variable {M : Type*} [AddCommGroup M] [DistribMulAction (bilinIsometryGroup B) M]

@[expose] def transvectionElt (hB : B.IsAlt) (v : V) : bilinIsometryGroup B :=
  ⟨symplecticTransvection B hB v 1, symplecticTransvection_mem_bilinIsometryGroup hB v 1⟩

@[simp] theorem coe_transvectionElt (hB : B.IsAlt) (v : V) :
    ((transvectionElt hB v : bilinIsometryGroup B) : LinearMap.GeneralLinearGroup K V) =
      symplecticTransvection B hB v 1 := rfl

theorem transvectionElt_mul_self [CharP K 2] (hB : B.IsAlt) (v : V) :
    transvectionElt hB v * transvectionElt hB v = 1 := by
  refine Subtype.ext ?_
  show symplecticTransvection B hB v 1 * symplecticTransvection B hB v 1 = 1
  rw [symplecticTransvection_mul, one_add_one_eq_two, CharTwo.two_eq_zero,
    symplecticTransvection_zero]

theorem transvectionElt_comm (hB : B.IsAlt) {u v : V} (huv : B u v = 0) :
    transvectionElt hB u * transvectionElt hB v = transvectionElt hB v * transvectionElt hB u :=
  Subtype.ext (symplecticTransvection_comm hB huv 1 1)

theorem exists_comm_eq_map_smul [CharP K 2] [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) (h2 : ∀ m : M, m + m = 0) (ι : V →+ M) (hι : Function.Injective ι)
    (hιeq : ∀ (g : bilinIsometryGroup B) (v : V),
      ι (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) = g • ι v)
    (htriv : ∀ (g : bilinIsometryGroup B) (m : M), g • m - m ∈ ι.range)
    {v : V} (hv : v ≠ 0) (m : M) :
    ∃ t : K, F2Fixed.comm M (transvectionElt hB v) m = ι (t • v) := by
  classical
  set a := transvectionElt hB v with ha
  have hφι : ∀ x : V, F2Fixed.comm M a (ι x) = ι (B x v • v) := by
    intro x
    rw [F2Fixed.comm_apply, ← hιeq]
    show ι (((symplecticTransvection B hB v 1 : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) x) - ι x = _
    rw [symplecticTransvection_apply, map_add, one_mul, add_sub_cancel_left]
  have hφφ : ∀ n : M, F2Fixed.comm M a (F2Fixed.comm M a n) = 0 := by
    intro n
    simp only [F2Fixed.comm_apply, smul_sub, ← mul_smul, ha, transvectionElt_mul_self hB v,
      one_smul]
    have e : n - a • n - (a • n - n) = (n + n) - (a • n + a • n) := by abel
    rw [e, h2 n, h2 (a • n), sub_zero]
  obtain ⟨x₀, hx₀⟩ := htriv a m
  have hmφ : F2Fixed.comm M a m = ι x₀ := by rw [F2Fixed.comm_apply]; exact hx₀.symm
  have hBv : B x₀ v = 0 := by
    have h := hφφ m
    rw [hmφ, hφι] at h
    have h0 : B x₀ v • v = 0 := hι (by rw [h, map_zero])
    exact (smul_eq_zero.mp h0).resolve_right hv
  have hu : ∀ u : V, B u v = 0 → u ∉ span K {v} → B x₀ u = 0 := by
    intro u huv hu
    set g := transvectionElt hB u
    have hcomm : g * a = a * g := transvectionElt_comm hB (u := u) (v := v) huv
    obtain ⟨y, hy⟩ := htriv g m
    have hgm : g • m = m + ι y := by rw [hy]; abel
    have h1 : g • F2Fixed.comm M a m = F2Fixed.comm M a (g • m) := by
      simp only [F2Fixed.comm_apply, smul_sub, ← mul_smul, hcomm]
    rw [hmφ, hgm, map_add, hφι, hmφ, ← hιeq] at h1
    have h3 : ι (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x₀) =
        ι x₀ + ι (B y v • v) := h1
    rw [show ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x₀ =
      x₀ + (1 * B x₀ u) • u from symplecticTransvection_apply hB u 1 x₀, map_add] at h3
    have h4 : (1 * B x₀ u) • u = B y v • v := hι (add_left_cancel h3)
    by_contra hne
    apply hu
    have : u = (B x₀ u)⁻¹ • (B y v • v) := by
      rw [← h4, one_mul, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have hx : x₀ ∈ span K {v} := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hBn hB.isRefl (span K {v})]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have hvn : B v n = 0 := (LinearMap.BilinForm.mem_orthogonal_span_singleton_iff B).mp hn
    have hnv : B n v = 0 := by rw [← hB.neg_eq v n, hvn, neg_zero]
    by_cases hnspan : n ∈ span K {v}
    · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hnspan
      rw [map_smul, LinearMap.smul_apply, ← hB.neg_eq x₀ v, hBv]
      simp
    · rw [← hB.neg_eq x₀ n, hu n hnv hnspan, neg_zero]
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨t, hmφ⟩

theorem index_ker_comm_le [CharP K 2] [Finite K] [Finite M] [FiniteDimensional K V]
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (h2 : ∀ m : M, m + m = 0) (ι : V →+ M) (hι : Function.Injective ι)
    (hιeq : ∀ (g : bilinIsometryGroup B) (v : V),
      ι (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) = g • ι v)
    (htriv : ∀ (g : bilinIsometryGroup B) (m : M), g • m - m ∈ ι.range)
    {v : V} (hv : v ≠ 0) :
    (F2Fixed.comm M (transvectionElt hB v)).ker.index ≤ Nat.card K := by
  rw [AddSubgroup.index_ker]
  set Lv : AddSubgroup M := (ι.comp (LinearMap.toSpanSingleton K V v).toAddMonoidHom).range
  have hle : (F2Fixed.comm M (transvectionElt hB v)).range ≤ Lv := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨t, ht⟩ := exists_comm_eq_map_smul hB hBn h2 ι hι hιeq htriv hv m
    exact ⟨t, by simp [ht]⟩
  calc Nat.card (F2Fixed.comm M (transvectionElt hB v)).range ≤ Nat.card Lv :=
        AddSubgroup.card_le_of_le hle
    _ ≤ Nat.card K := Nat.card_le_card_of_surjective _ (AddMonoidHom.rangeRestrict_surjective _)

theorem zsmul_eq_zero_or_self {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0) (k : ℤ)
    (x : M) : k • x = 0 ∨ k • x = x := by
  rcases Int.even_or_odd' k with ⟨r, rfl | rfl⟩
  · left
    rw [mul_smul, two_smul]
    exact h2 _
  · right
    rw [add_smul, mul_smul, two_smul, h2 (r • x), zero_add, one_smul]

theorem eq_zero_of_forall_smul_eq [CharP K 2] [Finite M] [Nontrivial V] [FiniteDimensional K V]
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (h2 : ∀ m : M, m + m = 0) (ι : V →+ M) (hι : Function.Injective ι)
    (hιeq : ∀ (g : bilinIsometryGroup B) (v : V),
      ι (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) = g • ι v)
    (htriv : ∀ (g : bilinIsometryGroup B) (m : M), g • m - m ∈ ι.range)
    (hind : ∀ A A' : AddSubgroup M, (∀ g : bilinIsometryGroup B, ∀ a ∈ A, g • a ∈ A) →
      (∀ g : bilinIsometryGroup B, ∀ a ∈ A', g • a ∈ A') → IsCompl A A' → A = ⊥ ∨ A' = ⊥)
    {m : M} (hm : ∀ g : bilinIsometryGroup B, g • m = m) : m = 0 := by
  classical
  let C : AddSubgroup M := ⨅ g : bilinIsometryGroup B, (F2Fixed.comm M g).ker
  have hmemC : ∀ x : M, x ∈ C ↔ ∀ g : bilinIsometryGroup B, g • x = x := by
    intro x
    simp only [C, AddSubgroup.mem_iInf, mem_ker_comm]
  have hCinv : ∀ g : bilinIsometryGroup B, ∀ a ∈ C, g • a ∈ C := fun g a ha =>
    (hmemC _).mpr fun h => by rw [(hmemC a).mp ha g, (hmemC a).mp ha h]
  have hCι : ∀ x : V, ι x ∈ C → x = 0 := by
    intro x hx
    by_contra hx0
    obtain ⟨u, hu⟩ : ∃ u, B x u ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (hBn.1 x h)
    have h1 := (hmemC _).mp hx (transvectionElt hB u)
    rw [← hιeq] at h1
    have h3 := hι h1
    rw [coe_transvectionElt, symplecticTransvection_apply] at h3
    have h4 : (1 * B x u) • u = 0 := by
      have : x + (1 * B x u) • u = x + 0 := by rw [add_zero]; exact h3
      exact add_left_cancel this
    rcases smul_eq_zero.mp h4 with h | h
    · exact hu (by simpa using h)
    · rw [h, map_zero] at hu
      exact hu rfl
  let S : Set (AddSubgroup M) := {A | ι.range ≤ A ∧
    (∀ g : bilinIsometryGroup B, ∀ a ∈ A, g • a ∈ A) ∧ A ⊓ C = ⊥}
  have hrangeS : ι.range ∈ S := by
    refine ⟨le_rfl, ?_, ?_⟩
    · rintro g _ ⟨x, rfl⟩
      exact ⟨_, hιeq g x⟩
    · rw [eq_bot_iff]
      rintro _ ⟨⟨x, rfl⟩, hxC⟩
      rw [hCι x hxC, map_zero]
      exact zero_mem _
  haveI : Finite (AddSubgroup M) :=
    Finite.of_injective (fun A : AddSubgroup M => (A : Set M)) SetLike.coe_injective
  obtain ⟨A', ⟨hA'ι, hA'inv, hA'C⟩, hmax⟩ := Set.Finite.exists_maximal (Set.toFinite S)
    ⟨ι.range, hrangeS⟩
  have hsup : A' ⊔ C = ⊤ := by
    rw [eq_top_iff]
    intro m' _
    by_contra hm'
    set A'' : AddSubgroup M := A' ⊔ AddSubgroup.zmultiples m' with hA''
    have hA'A'' : A' ≤ A'' := le_sup_left
    have hm'A'' : m' ∈ A'' := AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples m')
    have hA''S : A'' ∈ S := by
      refine ⟨hA'ι.trans hA'A'', ?_, ?_⟩
      · intro g z hz
        obtain ⟨a, ha, n, hn, rfl⟩ := AddSubgroup.mem_sup.mp hz
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hn
        have hgk : g • (k • m') = k • (g • m') :=
          map_zsmul (DistribSMul.toAddMonoidHom M g) k m'
        rw [smul_add, hgk]
        refine A''.add_mem (hA'A'' (hA'inv g a ha)) ?_
        have hgm : g • m' = m' + (g • m' - m') := by abel
        rw [hgm, smul_add]
        refine A''.add_mem (AddSubgroup.mem_sup_right
          (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples m') k)) ?_
        exact hA'A'' (AddSubgroup.zsmul_mem _ (hA'ι (htriv g m')) k)
      · rw [eq_bot_iff]
        rintro c ⟨hcA'', hcC⟩
        obtain ⟨a, ha, n, hn, rfl⟩ := AddSubgroup.mem_sup.mp hcA''
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hn
        rcases zsmul_eq_zero_or_self h2 k m' with hk | hk
        · rw [hk, add_zero] at hcC ⊢
          have : a ∈ A' ⊓ C := ⟨ha, hcC⟩
          rw [hA'C, AddSubgroup.mem_bot] at this
          rw [this]
          exact zero_mem _
        · exfalso
          rw [hk] at hcC
          apply hm'
          have : m' = (a + m') + (-a) := by abel
          rw [this]
          exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_right hcC)
            (AddSubgroup.mem_sup_left (A'.neg_mem ha))
    exact hm' (AddSubgroup.mem_sup_left (hmax hA''S hA'A'' hm'A''))
  have hcompl : IsCompl C A' := (IsCompl.of_eq (by rw [inf_comm]; exact hA'C)
    (by rw [sup_comm]; exact hsup))
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : ι x ∈ A' := hA'ι ⟨x, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at this
    exact hx (hι (this.trans (map_zero ι).symm))
  have hCbot : C = ⊥ := (hind C A' hCinv hA'inv hcompl).resolve_right hA'ne
  have : m ∈ C := (hmemC m).mpr hm
  rw [hCbot, AddSubgroup.mem_bot] at this
  exact this

theorem card_le_of_indecomposable [CharP K 2] [Finite K] [Finite M] [Nontrivial V]
    [FiniteDimensional K V] (hB : B.IsAlt) (hBn : B.Nondegenerate) (hq : 2 < Nat.card K)
    (h2 : ∀ m : M, m + m = 0) (ι : V →+ M) (hι : Function.Injective ι)
    (hιeq : ∀ (g : bilinIsometryGroup B) (v : V),
      ι (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) = g • ι v)
    (htriv : ∀ (g : bilinIsometryGroup B) (m : M), g • m - m ∈ ι.range)
    (hind : ∀ A A' : AddSubgroup M, (∀ g : bilinIsometryGroup B, ∀ a ∈ A, g • a ∈ A) →
      (∀ g : bilinIsometryGroup B, ∀ a ∈ A', g • a ∈ A') → IsCompl A A' → A = ⊥ ∨ A' = ⊥) :
    Nat.card M ≤ Nat.card K * Nat.card V := by
  classical
  obtain ⟨s, hs0, hscard, hsgen⟩ := exists_card_le_closure_symplecticTransvection_eq hq hB hBn
  set Kx : V → AddSubgroup M := fun x => (F2Fixed.comm M (transvectionElt hB x)).ker
  have hidx : ∀ x ∈ s, (Kx x).index ≤ Nat.card K := fun x hx =>
    index_ker_comm_le hB hBn h2 ι hι hιeq htriv (hs0 x hx)
  have hbound := index_finset_inf_le s Kx (Nat.card K) hidx
  have hbot : s.inf Kx = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have hfix : ∀ x ∈ s, transvectionElt hB x • m = m := fun x hx =>
      mem_ker_comm.mp ((Finset.inf_le hx : s.inf Kx ≤ Kx x) hm)
    have hall : ∀ g : bilinIsometryGroup B, g • m = m := by
      intro g
      have hg : (g : LinearMap.GeneralLinearGroup K V) ∈
          Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) := by
        rw [hsgen]
        exact g.2
      let St : Subgroup (LinearMap.GeneralLinearGroup K V) :=
        (MulAction.stabilizer (bilinIsometryGroup B) m).map (bilinIsometryGroup B).subtype
      have hle : Subgroup.closure ((fun x => symplecticTransvection B hB x 1) '' (s : Set V)) ≤
          St := by
        rw [Subgroup.closure_le]
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨transvectionElt hB x, hfix x hx, rfl⟩
      obtain ⟨h, hh, hhg⟩ := hle hg
      have : h = g := Subtype.ext hhg
      rw [← this]
      exact hh
    have hm0 := eq_zero_of_forall_smul_eq hB hBn h2 ι hι hιeq htriv hind hall
    rw [hm0]
    exact zero_mem _
  rw [hbot, AddSubgroup.index_bot] at hbound
  calc Nat.card M ≤ Nat.card K ^ s.card := hbound
    _ ≤ Nat.card K ^ (finrank K V + 1) := Nat.pow_le_pow_right Nat.card_pos hscard
    _ = Nat.card K * Nat.card V := by
      rw [pow_succ', Module.natCard_eq_pow_finrank (K := K) (V := V)]

theorem stroth_2_2 [CharP K 2] [Finite K] [Finite M] [FiniteDimensional K V]
    (hB : B.IsAlt) (hBn : B.Nondegenerate) (hq : 2 < Nat.card K) (hn : 4 ≤ Module.finrank K V)
    (h2 : ∀ m : M, m + m = 0) (ι : V →+ M) (hι : Function.Injective ι)
    (hιeq : ∀ (g : bilinIsometryGroup B) (v : V),
      ι (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) = g • ι v)
    (htriv : ∀ (g : bilinIsometryGroup B) (m : M), g • m - m ∈ ι.range)
    (hind : ∀ A A' : AddSubgroup M, (∀ g : bilinIsometryGroup B, ∀ a ∈ A, g • a ∈ A) →
      (∀ g : bilinIsometryGroup B, ∀ a ∈ A', g • a ∈ A') → IsCompl A A' → A = ⊥ ∨ A' = ⊥) :
    Nat.card M ≤ Nat.card K * Nat.card V := by
  haveI : Nontrivial V := Module.finrank_pos_iff.mp (show 0 < finrank K V by omega)
  exact card_le_of_indecomposable hB hBn hq h2 ι hι hιeq htriv hind

end Natural

end CFSG.ClassicalGroups.Alternating
