module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono map_perfectCore
  le_perfectCore_of_perfect perfectCore_eq_self_of_perfect)

section General

variable {G : Type*} [Group G]

@[expose] def IsCoreLeviDecomp (X Q M : Subgroup G) : Prop :=
  perfectCore X = Q ⊔ M ∧ IsPGroup 2 Q ∧ M ≤ normalizer (Q : Set G) ∧ Disjoint Q M ∧
    ∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥

theorem mem_centralizer_subtype_iff {H : Subgroup G} {x g : H} :
    g ∈ centralizer ({x} : Set H) ↔ (g : G) ∈ centralizer ({(x : G)} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem centralizer_subtype_eq {H : Subgroup G} (x : H) :
    centralizer ({x} : Set H) = (centralizer ({(x : G)} : Set G)).subgroupOf H := by
  ext g
  rw [mem_subgroupOf]
  exact mem_centralizer_subtype_iff

theorem centralizer_conj_eq_map (n x : G) :
    centralizer ({n * x * n⁻¹} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom := by
  ext g
  constructor
  · intro hg
    have hg' : g * (n * x * n⁻¹) = n * x * n⁻¹ * g := mem_centralizer_singleton_iff.1 hg
    have hmem : n⁻¹ * g * n ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc n⁻¹ * g * n * x = n⁻¹ * (g * (n * x * n⁻¹)) * n := by group
        _ = n⁻¹ * (n * x * n⁻¹ * g) * n := by rw [hg']
        _ = x * (n⁻¹ * g * n) := by group
    exact ⟨n⁻¹ * g * n, hmem, by simp [MulAut.conj_apply]; group⟩
  · rintro ⟨h, hh, rfl⟩
    have hh' : h * x = x * h := mem_centralizer_singleton_iff.1 hh
    rw [mem_centralizer_singleton_iff]
    change n * h * n⁻¹ * (n * x * n⁻¹) = n * x * n⁻¹ * (n * h * n⁻¹)
    calc n * h * n⁻¹ * (n * x * n⁻¹) = n * (h * x) * n⁻¹ := by group
      _ = n * (x * h) * n⁻¹ := by rw [hh']
      _ = n * x * n⁻¹ * (n * h * n⁻¹) := by group

theorem eq_inf_sup_of_le_sup {P Q M : Subgroup G} (hP : P ≤ Q ⊔ M) (hMP : M ≤ P)
    (hMN : M ≤ normalizer (Q : Set G)) : P = (P ⊓ Q) ⊔ M := by
  refine le_antisymm (fun g hg => ?_) (sup_le inf_le_left hMP)
  have hg' : g ∈ ((Q ⊔ M : Subgroup G) : Set G) := hP hg
  rw [coe_mul_of_right_le_normalizer_left Q M hMN] at hg'
  obtain ⟨q, hq, m, hm, rfl⟩ := hg'
  have hqP : q ∈ P := by
    have e : q = q * m * m⁻¹ := by group
    rw [e]
    exact mul_mem hg (inv_mem (hMP hm))
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨hqP, hq⟩)) (mem_sup_right hm)

theorem le_normalizer_inf_of_le {P Q M : Subgroup G} (hMP : M ≤ P)
    (hMN : M ≤ normalizer (Q : Set G)) : M ≤ normalizer ((P ⊓ Q : Subgroup G) : Set G) :=
  le_trans (le_inf (hMP.trans le_normalizer) hMN) inf_normalizer_le_normalizer_inf

theorem isCoreLeviDecomp_of_le_sup [Finite G] {X Q M : Subgroup G}
    (hle : perfectCore X ≤ Q ⊔ M) (hMX : M ≤ X) (hM : ⁅M, M⁆ = M) (hQ : IsPGroup 2 Q)
    (hMN : M ≤ normalizer (Q : Set G)) (hQM : Disjoint Q M)
    (hO2 : ∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥) :
    IsCoreLeviDecomp X (perfectCore X ⊓ Q) M := by
  have hMP : M ≤ perfectCore X := le_perfectCore_of_perfect hMX hM
  exact ⟨eq_inf_sup_of_le_sup hle hMP hMN, hQ.to_le inf_le_right,
    le_normalizer_inf_of_le hMP hMN, hQM.mono_left inf_le_right, hO2⟩

theorem forall_normal_isPGroup_eq_bot_of_mulEquiv' {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hA : ∀ N : Subgroup A, N.Normal → IsPGroup 2 N → N = ⊥) (N : Subgroup B)
    (hN : N.Normal) (hNp : IsPGroup 2 N) : N = ⊥ := by
  have h := hA (N.comap e.toMonoidHom) (hN.comap _) (hNp.comap_of_injective _ e.injective)
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ N.comap e.toMonoidHom := by
    change e (e.symm x) ∈ N
    rw [MulEquiv.apply_symm_apply]
    exact hx
  rw [h, mem_bot] at hx'
  rw [mem_bot, ← e.apply_symm_apply x, hx', map_one]

theorem IsCoreLeviDecomp.map [Finite G] {X Q M : Subgroup G} (h : IsCoreLeviDecomp X Q M)
    (e : G ≃* G) :
    IsCoreLeviDecomp (X.map e.toMonoidHom) (Q.map e.toMonoidHom) (M.map e.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h2.map _, (map_mono h3).trans (le_normalizer_map _), disjoint_map e.injective h4,
    forall_normal_isPGroup_eq_bot_of_mulEquiv' (M.equivMapOfInjective _ e.injective) h5⟩
  rw [← map_perfectCore, h1, Subgroup.map_sup]

theorem subgroupOf_le_map_conj {G : Type*} [Group G] {C J M : Subgroup G} (n : C)
    (hJ : ∀ x ∈ J, (n : G)⁻¹ * x * n ∈ M) :
    J.subgroupOf C ≤ (M.subgroupOf C).map (MulAut.conj n).toMonoidHom := by
  intro g hg
  rw [mem_map_equiv, mem_subgroupOf, MulAut.conj_symm_apply]
  simpa only [coe_mul, coe_inv] using hJ g (mem_subgroupOf.1 hg)

theorem mem_map_conj_iff {G : Type*} [Group G] {H : Subgroup G} {n x : G} :
    x ∈ H.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * x * n ∈ H := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

end General

end CFSG.SeitzReduction.TwistedE6Pilot
