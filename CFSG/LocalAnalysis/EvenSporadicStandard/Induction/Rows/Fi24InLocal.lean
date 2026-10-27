module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

abbrev Fi24InCoverBase (L K : Subgroup H) (u : H) (huL : u ∈ L) : Prop :=
  Fi24InBase (↥L ⧸ center ↥L) ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) (bar (K.subgroupOf L))

theorem fi24in_solomonLocalQ_of_base (hL : CFSG.IsQuasisimple ↥L)
    (hodd : Odd (Nat.card (center ↥L))) (hKq : CFSG.IsQuasisimple ↥K) (huL : u ∈ L)
    (hnc : u ∉ centralizer (L : Set H))
    (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hbase : Fi24InCoverBase L K u huL) : SolomonLocalQ L K u := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hKu' := central_subgroupOf huL hKu
  refine
  { u_order := hu2
    u_mem := Subgroup.le_normalizer huL
    u_not_central := hnc
    K_le := hKL
    u_mem_centralizer_K := mem_centralizer_iff.2 hKu
    standard_in_L := ?_
    autCentralizer_two := ?_ }
  · refine ⟨stdBare_of_bar hodd hK' hbase.stdBare,
      ⟨u, huL⟩, by rw [Subgroup.orderOf_mk]; exact hu2, ?_⟩
    have hle : K.subgroupOf L ≤ centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) := fun k hk =>
      mem_centralizer_singleton_iff.2 (hKu' k hk)
    have hqK : CFSG.IsQuasisimple ↥(K.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm hKq
    have hC : centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) ≤ normalizer (K.subgroupOf L : Set ↥L) :=
      fi24in_centralizer_le_normalizer_of_bar hodd hK' hu1 hbase.centralizer_le_normalizer
    exact isCompIn_of_normal hle hqK ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hC)
  · exact twoAdic_autCentralizer_le_of_cover hL.1 hbase.outTwo hbase.card_centralizer_le

theorem fi24in_mem_of_base (hodd : Odd (Nat.card (center ↥L))) (huL : u ∈ L) (hu2 : orderOf u = 2)
    (hbase : Fi24InCoverBase L K u huL) : u ∈ K := by
  have hu1 := sq_of_orderOf_two huL hu2
  exact Subgroup.mem_subgroupOf.1 (mem_of_mk_mem hodd hu1 hbase.u_mem)

theorem fi24in_le_of_perfect_of_base (huL : u ∈ L) {P : Subgroup H} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ L ⊓ centralizer ({u} : Set H)) (hbase : Fi24InCoverBase L K u huL) : P ≤ K := by
  have hPL : P ≤ L := fun x hx => (hPC hx).1
  set P' := P.subgroupOf L with hP'
  have hP'map : P'.map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hP'map, hP]
  have hP'C : P' ≤ centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) := fun x hx =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 (hPC hx).2))
  have hbarP : ⁅bar P', bar P'⁆ = bar P' := by
    unfold bar
    rw [← Subgroup.map_commutator, hP'perf]
  have hbarPC : bar P' ≤
      centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      mem_centralizer_singleton_iff.1 (hP'C hx)]
  have hle := hbase.le_of_perfect_le_centralizer hbarP hbarPC
  have hsup : P' ≤ K.subgroupOf L ⊔ center ↥L := by
    intro x hx
    obtain ⟨k, hk, z, hz, hxz⟩ := mem_bar_iff_exists_mem_mul.1 (hle (mk_mem_bar_of_mem hx))
    exact (mem_sup_central le_rfl).2 ⟨k, hk, z, hz, hxz.symm⟩
  have hP'K := le_of_perfect_le_sup_central (Z' := center ↥L) le_rfl hP'perf hsup
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (hP'K (show (⟨x, hPL hx⟩ : ↥L) ∈ P' from hx))

theorem fi24in_characteristic_of_base (hKq : CFSG.IsQuasisimple ↥K) (huL : u ∈ L) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hbase : Fi24InCoverBase L K u huL) :
    (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic := by
  set C : Subgroup H := L ⊓ centralizer ({u} : Set H) with hC
  have hKC : K ≤ C := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hperf := commutator_subgroupOf_eq_self hKC hKq
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  set P : Subgroup H := ((K.subgroupOf C).map φ.toMonoidHom).map C.subtype with hP
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hperf]
  have hPC : P ≤ C := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hPK := fi24in_le_of_perfect_of_base huL hPperf hPC hbase
  intro y hy
  exact Subgroup.mem_subgroupOf.2 (hPK (show (y : H) ∈ P from ⟨y, hy, rfl⟩))

theorem fi24in_inducedByCentralizer_of_base (hodd : Odd (Nat.card (center ↥L)))
    (hKq : CFSG.IsQuasisimple ↥K) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hbase : Fi24InCoverBase L K u huL) : InducedByCentralizer L K u := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  refine inducedByCentralizer_of_forall_aut fun α => ?_
  let ε : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  obtain ⟨y, hy, hα⟩ :=
    fi24in_exists_conj_of_aut_cover hodd hK' hu1 hbase ((ε.trans α).trans ε.symm)
  refine ⟨(y : H), ⟨y.2, ?_⟩, fun k => ?_⟩
  · exact mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy))
  · exact congrArg Subtype.val (hα (ε.symm k))

theorem fi24in_sol78Fusion39_of_base (hodd : Odd (Nat.card (center ↥L)))
    (hKq : CFSG.IsQuasisimple ↥K) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (h35 : K = componentProduct K u) (hbase : Fi24InCoverBase L K u huL) :
    Sol78Fusion39 L K u :=
  sol78Fusion39_of_induced hKu
    (fun _ hg => Solomon78.mem_normalizer_iff_map_conj_eq.2 (map_conj_eq_of_hyp35 h35 hg).2)
    (fi24in_inducedByCentralizer_of_base hodd hKq huL hu2 hKL hbase)

end CFSG.EvenSporadicStandard.Induction
