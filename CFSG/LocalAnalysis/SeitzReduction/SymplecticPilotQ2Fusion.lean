module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotAutU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvection
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Field K]

theorem twoCentralElt_mem_wRadical {n : ℕ} (a b : K) :
    twoCentralElt (n + 3) 1 2 a b ∈ wRadical K (1 : Fin (n + 3)) 2 := by
  rw [twoCentralElt_eq_siegDiag_mul_siegPair]
  exact mul_mem (siegDiag_mem_wRadical (Or.inl rfl) a) (siegPair_mem_wRadical (Or.inl rfl) b)

theorem mem_perfectCore_centralizer_of_commute_sylow_of_rep [Finite K] [CharP K 2] {n : ℕ}
    (hrep : ∀ κ : SpTwoCentral,
      spRep (K := K) n κ ∈ perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))))
    {X : Type*} [Group X] (e : X ≃* StatedSp (n + 3) K) {z : X} (hz : z ≠ 1)
    {U : Sylow 2 X} (hzU : ∀ u ∈ (U : Subgroup X), u * z = z * u) :
    z ∈ perfectCore (centralizer ({z} : Set X)) := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_spRep_of_mulEquiv e hz hzU
  set f : StatedSp (n + 3) K →* X := (MulAut.conj c⁻¹).toMonoidHom.comp e.symm.toMonoidHom
  have hf : f (spRep n κ) = z := by
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hc]
    group
  have h := LinearPilot.map_mem_perfectCore_centralizer f (hrep κ)
  rwa [hf] at h

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_forall_commute_sylow_conj_of_rep (hset : SeitzSetting G L) {n : ℕ} [Finite K]
    [CharP K 2]
    (hrep : ∀ κ : SpTwoCentral,
      spRep (K := K) n κ ∈ perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))))
    (e : L ≃* StatedSp (n + 3) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  set w : L := ⟨g⁻¹ * t * g, hgL⟩ with hw
  have hw1 : w ≠ 1 := by
    intro h
    have h1 : g⁻¹ * t * g = 1 := congrArg Subtype.val h
    have ht1 : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by decide)
  have hcore := mem_perfectCore_centralizer_of_commute_sylow_of_rep hrep e hw1 (U := U)
    fun u hu => Subtype.ext (hcomm u hu)
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  refine LinearPilot.conj_not_mem_perfect hset.standardSetting hOut hset.center_eq_bot htC ht g
    (P := (perfectCore (centralizer ({w} : Set L))).map L.subtype) ?_ ?_ ?_ ⟨w, hcore, rfl⟩
  · rw [← map_commutator, perfectCore_perfect]
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩
    have h := mem_centralizer_singleton_iff.1 (perfectCore_le _ hx)
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h

theorem exists_conj_eq_mul_twoCentral_twoSided_of_rep (hset : SeitzSetting G L) {n : ℕ}
    [Finite K] [CharP K 2]
    (hrep : ∀ κ : SpTwoCentral,
      spRep (K := K) n κ ∈ perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))))
    (e : L ≃* StatedSp (n + 3) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ :=
  exists_conj_eq_mul_twoCentral_twoSided_of_hnot hset (by omega) e ht hKt
    (not_forall_commute_sylow_conj_of_rep hset hrep e
      (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht)

end CFSG.SeitzReduction.SymplecticPilot
