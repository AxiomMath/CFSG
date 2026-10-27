module

public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.TwoM12Check
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasASplit

public section

namespace CFSG.GH74.KGroups.TwoM12

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.GH74.E2 (Shape2M12)

variable {L : Type} [Group L]

structure IsCover (t : L) (π : L →* NativeSporadic.M12) : Prop where
  orderOf_t : orderOf t = 2
  center_eq : center L = zpowers t
  surjective : Function.Surjective π
  ker_eq : π.ker = zpowers t

theorem IsCover.t_mem_center {t : L} {π : L →* NativeSporadic.M12} (h : IsCover t π) :
    t ∈ center L :=
  h.center_eq ▸ mem_zpowers t

theorem exists_isCover (h : Shape2M12 L) :
    ∃ (t : L) (π : L →* NativeSporadic.M12), IsCover t π := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  let e' : L ⧸ center L ≃* NativeSporadic.M12 := e
  let π : L →* NativeSporadic.M12 := e'.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (center L) := isCyclic_of_prime_card hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := center L)
  have hgtop : zpowers g = ⊤ := eq_top_iff.mpr fun x _ => hg x
  have hg2 : orderOf g = 2 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hc]
  have hZt : center L = zpowers ((g : center L) : L) := by
    have h1 : (zpowers g).map (center L).subtype = zpowers ((g : center L) : L) :=
      MonoidHom.map_zpowers _ _
    rw [← h1, hgtop, ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨((g : center L) : L), π, ?_, hZt, hπ, hkerZ.trans hZt⟩
  rw [Subgroup.orderOf_coe, hg2]

variable [Finite L] {t : L} {π : L →* NativeSporadic.M12}

omit [Finite L] in
theorem conj_data {u : L} {P : Subgroup L} (g : L) (hP : ⁅P, P⁆ = P)
    (hPu : ∀ x ∈ P, x * u = u * x) :
    ⁅P.map (MulAut.conj g⁻¹).toMonoidHom, P.map (MulAut.conj g⁻¹).toMonoidHom⁆ =
        P.map (MulAut.conj g⁻¹).toMonoidHom ∧
      (∀ y ∈ P.map (MulAut.conj g⁻¹).toMonoidHom, y * (g⁻¹ * u * g) = (g⁻¹ * u * g) * y) ∧
      Nat.card (P.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card P := by
  refine ⟨?_, ?_, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective⟩
  · rw [← Subgroup.map_commutator, hP]
  · rintro _ ⟨x, hx, rfl⟩
    have h := hPu x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * u * g) = g⁻¹ * (x * u) * g := by group
      _ = g⁻¹ * (u * x) * g := by rw [h]
      _ = g⁻¹ * u * g * (g⁻¹ * x * g) := by group

theorem card_le_two_of_comm_r
    (hc : IsCover t π) {u : L} (hu : π u = elemR) {P : Subgroup L}
    (hP : ⁅P, P⁆ = P) (hPu : ∀ x ∈ P, x * u = u * x) : Nat.card P ≤ 2 := by
  have hπP : P.map π ≤ centralizer ({elemR} : Set NativeSporadic.M12) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hu, ← map_mul, ← map_mul, hPu x hx]
  have hsolv : Group.IsSolvable ↥(P.map π) := by
    have := solvable_centralizer_elemR
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hπP)
  have hperf : Group.IsPerfect ↥(P.map π) :=
    Subgroup.isPerfect_iff.2 (by rw [← Subgroup.map_commutator, hP])
  have hbot : P.map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(P.map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable _ hsolv
  have hPker : P ≤ π.ker := (Subgroup.map_eq_bot_iff P).1 hbot
  rw [hc.ker_eq] at hPker
  calc Nat.card P ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hPker
    _ = 2 := by rw [Nat.card_zpowers, hc.orderOf_t]

theorem card_le_sixty_of_comm_z
    (hc : IsCover t π) {u : L} (hu : π u = elemZ) {P : Subgroup L}
    (hP : ⁅P, P⁆ = P) (hPu : ∀ x ∈ P, x * u = u * x) : Nat.card P ≤ 60 := by
  have hπP : P.map π ≤ centralizer ({elemZ} : Set NativeSporadic.M12) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hu, ← map_mul, ← map_mul, hPu x hx]
  have hD : P.map π ≤ fixedD := by
    have h1 : ⁅P.map π, P.map π⁆ = P.map π := by rw [← Subgroup.map_commutator, hP]
    calc P.map π = ⁅P.map π, P.map π⁆ := h1.symm
      _ ≤ ⁅centralizer ({elemZ} : Set NativeSporadic.M12),
            centralizer ({elemZ} : Set NativeSporadic.M12)⁆ :=
          Subgroup.commutator_mono hπP hπP
      _ ≤ fixedD := commutator_centralizer_elemZ_le
  have hPR : P ≤ fixedD.comap π := Subgroup.map_le_iff_le_comap.1 hD
  obtain ⟨-, hDD, hD60, hz2, hzc, -, hW, hWD, -, -, -, -, hWsq, -, hS, hinv, -, hh⟩ :=
    fusionData_pinned
  obtain ⟨W, hWW⟩ := hS
  have hrD : elemR ∈ fixedD := hWD (by rw [hW]; exact Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨-, ⟨e, -, -⟩, -⟩ :=
    CentralCover.central_double_cover_splits_over_perfect_factor_from_involution_fusion π
      hc.surjective hc.ker_eq hc.orderOf_t hc.t_mem_center (Subgroup.isPerfect_iff.2 hDD) W
      (fun w hw => by
        rw [hWW, mem_subgroupOf] at hw
        exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hWsq _ hw))
      hrD (fun q hq hq2 => by
        obtain ⟨d, hd, hqd⟩ := hinv q hq hq2
        exact ⟨d, hd, hqd.symm⟩) hzc hz2 ⟨_, hh⟩
  have hcard : Nat.card ↥⁅fixedD.comap π, fixedD.comap π⁆ = 60 := by
    rw [Nat.card_congr e.toEquiv, hD60]
  calc Nat.card P = Nat.card ↥⁅P, P⁆ := by rw [hP]
    _ ≤ Nat.card ↥⁅fixedD.comap π, fixedD.comap π⁆ :=
        Subgroup.card_le_of_le (Subgroup.commutator_mono hPR hPR)
    _ = 60 := hcard

theorem card_le_sixty_of_inner
    (hc : IsCover t π) {u : L} (hu : orderOf (π u) = 2)
    {P : Subgroup L} (hP : ⁅P, P⁆ = P) (hPu : ∀ x ∈ P, x * u = u * x) : Nat.card P ≤ 60 := by
  rcases m12_involution_conj_elemR_or_elemZ (π u) hu with ⟨g, hg⟩ | ⟨g, hg⟩
  · obtain ⟨g', rfl⟩ := hc.surjective g
    obtain ⟨hP', hPu', hcard⟩ := conj_data (u := u) g' hP hPu
    have hu' : π (g'⁻¹ * u * g') = elemR := by
      rw [map_mul, map_mul, map_inv, ← hg]
      group
    rw [← hcard]
    have := card_le_two_of_comm_r hc hu' hP' hPu'
    omega
  · obtain ⟨g', rfl⟩ := hc.surjective g
    obtain ⟨hP', hPu', hcard⟩ := conj_data (u := u) g' hP hPu
    have hu' : π (g'⁻¹ * u * g') = elemZ := by
      rw [map_mul, map_mul, map_inv, ← hg]
      group
    rw [← hcard]
    exact card_le_sixty_of_comm_z hc hu' hP' hPu'

end CFSG.GH74.KGroups.TwoM12
