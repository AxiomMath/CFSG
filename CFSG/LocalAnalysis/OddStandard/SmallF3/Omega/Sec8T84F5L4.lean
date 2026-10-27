module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E1Lem35
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84_conj_not_mem (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (hrk : ∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → ¬ IsElemAb2 R 8) :
    ∀ s ∈ T1 ⊔ T2, s ≠ 1 → s * s = 1 → ¬ IsConj t s := by
  intro s hs hs1 hs2 hconj
  rw [isConj_iff] at hconj
  obtain ⟨c, hc⟩ := hconj
  obtain ⟨R, hRle, hR8⟩ := D.rank8 s hs hs2 hs1
  have hR'le : R.map (MulAut.conj c⁻¹).toMonoidHom ≤ centralizer ({t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hrs : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.mp (hRle hr)
    calc
      c⁻¹ * r * c * t = c⁻¹ * (r * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * r) * c := by rw [hc, hrs]
      _ = t * (c⁻¹ * r * c) := by group
  have hR'card : Nat.card ↥(R.map (MulAut.conj c⁻¹).toMonoidHom) = 2 ^ 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact hR8.2
  exact hrk _ hR'le ⟨hR8.1.map _, hR'card⟩

theorem sec8t84_normalizer_decomp (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (hrk : ∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → ¬ IsElemAb2 R 8) :
    ∀ n ∈ normalizer (T : Set G), ∃ a ∈ T1, a⁻¹ * n ∈ centralizer ({t} : Set G) := by
  intro n hn
  have hn' := Subgroup.mem_normalizer_iff.mp hn
  have htT : t ∈ T := by
    rw [D.T_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hstT : n * t * n⁻¹ ∈ T := (hn' t).mp htT
  have hst2 : (n * t * n⁻¹) * (n * t * n⁻¹) = 1 := by
    rw [show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, D.t_sq]
    group
  have hst1 : n * t * n⁻¹ ≠ 1 := by
    intro h
    have h2 := congrArg (fun z => n⁻¹ * z * n) h
    have ht1 : t = 1 := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h2]
        _ = 1 := by group
    have hmem : t ∈ T1 ⊔ T2 := by rw [ht1]; exact (T1 ⊔ T2).one_mem
    exact D.t_not hmem
  have hstconj : IsConj t (n * t * n⁻¹) := isConj_iff.mpr ⟨n, rfl⟩
  have hstnot : n * t * n⁻¹ ∉ T1 ⊔ T2 := fun hmem =>
    (sec8t84_conj_not_mem D hrk (n * t * n⁻¹) hmem hst1 hst2) hstconj
  obtain ⟨a, ha, haeq⟩ :=
    sec8t84_lemma35 D.t_sq rfl D.T_eq D.comm D.inf D.swap1 D.swap2
      (n * t * n⁻¹) hstT hst2 hstnot
  refine ⟨a, ha, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : (a⁻¹ * n) * t * (a⁻¹ * n)⁻¹ = t := by
    calc
      (a⁻¹ * n) * t * (a⁻¹ * n)⁻¹ = a⁻¹ * (n * t * n⁻¹) * a := by group
      _ = a⁻¹ * (a * t * a⁻¹) * a := by rw [haeq]
      _ = t := by group
  exact mul_inv_eq_iff_eq_mul.mp hconj

end TData

end CFSG.OddStandard.SmallF3.Omega
