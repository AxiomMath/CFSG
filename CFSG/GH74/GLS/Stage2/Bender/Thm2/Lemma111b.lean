module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Lemma111a
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Main111

variable {G : Type} [Group G] [Finite G]

theorem commutator_lt_of_pgroup {p : ℕ} (hp : p.Prime) {V : Subgroup G} (hV : IsPGroup p ↥V) (hne : V ≠ ⊥) :
    ⁅V, V⁆ < V := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent ↥V := hV.isNilpotent
  have : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hne
  rw [← V.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator, Subgroup.map_subtype_lt_map_subtype]
  exact Group.IsSolvable.commutator_lt_top_of_nontrivial ↥V

end Main111

theorem lemma11_1_star_thm : Lemma11_1_star := by
  intro G _ _ p hp hp2 z t Q hz ht hzt hQ hCQ hzCt hQz hB
  have hzC : z ∈ Cen z := mem_Cen_self z
  have htC : t ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hzN : z ∈ normalizer (Q : Set G) := hCQ hzC
  have hz1 : z ≠ 1 := fun h => hQz fun x _ => by
    rw [h]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hz2 : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨V, hVdef⟩ : ∃ V : Subgroup G, V = ⁅Q, zpowers z⁆ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = ⁅V, V⁆ := ⟨_, rfl⟩
  have hVQ : V ≤ Q := by
    rw [hVdef]
    exact commutator_le_of_normalizes (Subgroup.zpowers_le.mpr hzN)
  have hVp : IsPGroup p ↥V := hQ.to_le hVQ
  have hVne : V ≠ ⊥ := fun hb => hQz (commutator_zpowers_eq_bot_iff.mp (by rw [← hVdef]; exact hb))
  have hVV : ⁅V, zpowers z⁆ = V := by
    rw [hVdef]
    exact commutator_zpowers_idem hz2 hp hp2 hQ hzN
  have hcomm_z : ∀ c ∈ Cen z, c * z = z * c := fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc
  have hCV : ∀ c ∈ Cen z, c ∈ normalizer (V : Set G) := fun c hc => by
    rw [hVdef]
    exact mem_normalizer_commutator (hCQ hc) (mem_normalizer_zpowers_of_comm (hcomm_z c hc))
  have hDV : D ≤ V := by
    rw [hDdef]
    exact commutator_le_of_normalizes Subgroup.le_normalizer
  have hVD : ∀ v ∈ V, v ∈ normalizer (D : Set G) := fun v hv => by
    rw [hDdef]
    exact mem_normalizer_commutator (Subgroup.le_normalizer hv) (Subgroup.le_normalizer hv)
  have hCD : ∀ c ∈ Cen z, c ∈ normalizer (D : Set G) := fun c hc => by
    rw [hDdef]
    exact mem_normalizer_commutator (hCV c hc) (hCV c hc)
  have hDlt : D < V := by
    rw [hDdef]
    exact commutator_lt_of_pgroup hp hVp hVne
  have hVodd : ∀ v ∈ V, Odd (orderOf v) := odd_orderOf_of_pgroup hp hpodd hVp
  have hDodd : ∀ d ∈ D, Odd (orderOf d) := fun d hd => hVodd d (hDV hd)
  have hzV : z ∈ normalizer (V : Set G) := hCV z hzC
  have htV : t ∈ normalizer (V : Set G) := hCV t htC
  have htD : t ∈ normalizer (D : Set G) := hCD t htC
  have hVW : V ≤ invModSub V D z hzV hDdef.ge hVD := by
    refine hVV.symm.le.trans ?_
    rw [Subgroup.commutator_le]
    intro v hv y hy
    rcases eq_one_or_eq_of_mem_zpowers hz hy with h1 | h1
    · rw [h1, commutatorElement_one_right]
      exact one_mem _
    · rw [h1]
      have hg : ⁅v, z⁆ ∈ V := by
        have := Subgroup.commutator_mem_commutator hv (mem_zpowers z)
        rwa [hVV] at this
      refine mem_invModSub.mpr ⟨hg, ?_⟩
      have e : ⁅v, z⁆ = v⁻¹⁻¹ * (z * v⁻¹ * z⁻¹) := by simp [commutatorElement_def, mul_assoc]
      have h2 : z * ⁅v, z⁆ * z⁻¹ = ⁅v, z⁆⁻¹ := by
        rw [e]
        exact conj_inv_elt hz v⁻¹
      show z * ⁅v, z⁆ * z⁻¹ * ⁅v, z⁆ ∈ D
      rw [h2, inv_mul_cancel]
      exact one_mem D
  have hPz : ∀ v ∈ V, z * v * z⁻¹ * v ∈ D := fun v hv => (mem_invModSub.mp (hVW hv)).2
  have hT : ∀ y ∈ V, y * (t * y * t⁻¹) ∈ D := by
    intro y hy
    obtain ⟨s, hs⟩ : ∃ s : G, s = t * y * t⁻¹ := ⟨_, rfl⟩
    have hsV : s ∈ V := by
      rw [hs]
      exact (Subgroup.mem_normalizer_iff.mp htV y).mp hy
    have hts : t * s * t⁻¹ = y := by
      rw [hs]
      exact conj_conj_of_mul_self ht y
    have hvV : y * s ∈ V := mul_mem hy hsV
    have hfix : t * (y * s) * t⁻¹ * (y * s)⁻¹ ∈ D := by
      have e : t * (y * s) * t⁻¹ * (y * s)⁻¹ = ⁅s, y⁆ := by
        calc t * (y * s) * t⁻¹ * (y * s)⁻¹ = (t * y * t⁻¹) * (t * s * t⁻¹) * (y * s)⁻¹ := by group
          _ = s * y * (y * s)⁻¹ := by rw [← hs, hts]
          _ = ⁅s, y⁆ := by simp only [commutatorElement_def]; group
      rw [e, hDdef]
      exact Subgroup.commutator_mem_commutator hsV hy
    obtain ⟨u, huV, hvu, htu⟩ := lift_fixed ht hDV hVD hDodd hvV hfix
    have hut : u * t = t * u := by
      calc u * t = (t * u * t⁻¹) * t := by rw [htu]
        _ = t * u := by group
    have huB : u ∈ Q ⊓ centralizer ({t} : Set G) :=
      ⟨hVQ huV, Subgroup.mem_centralizer_singleton_iff.mpr hut⟩
    have huz : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.mp (hB huB)
    have hzu : z * u * z⁻¹ = u := by
      calc z * u * z⁻¹ = (u * z) * z⁻¹ := by rw [← huz]
        _ = u := by group
    have hxV : z * (y * s) * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hzV _).mp hvV
    have hzd : z * ((y * s)⁻¹ * u)⁻¹ * z⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hCD z hzC) _).mp (inv_mem hvu)
    have h1 : u * ((z * ((y * s)⁻¹ * u)⁻¹ * z⁻¹) * ((y * s)⁻¹ * u)) * u⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hVD u huV) _).mp (mul_mem hzd hvu)
    have e0 : z * (y * s) * z⁻¹ = (z * u * z⁻¹) * (z * ((y * s)⁻¹ * u)⁻¹ * z⁻¹) := by group
    have e1 : z * (y * s) * z⁻¹ * (y * s)⁻¹ =
        u * ((z * ((y * s)⁻¹ * u)⁻¹ * z⁻¹) * ((y * s)⁻¹ * u)) * u⁻¹ := by
      rw [e0, hzu]
      group
    have hE1 : z * (y * s) * z⁻¹ * (y * s)⁻¹ ∈ D := by
      rw [e1]
      exact h1
    have hE2 : z * (y * s) * z⁻¹ * (y * s) ∈ D := hPz _ hvV
    have hsq : (y * s) * (y * s) ∈ D := sq_mem_of_mul_mem hVD hxV hE2 hE1
    have hvD : y * s ∈ D := mem_of_sq_mem (hVodd _ hvV) hsq
    rw [← hs]
    exact hvD
  have hK : ∀ c ∈ Cen z, ⁅c, t⁆ ∈ centralizerSection V D := by
    intro c hc
    refine ⟨?_, ?_, ?_⟩
    · show c * t * c⁻¹ * t⁻¹ ∈ normalizer (V : Set G)
      exact mul_mem (mul_mem (mul_mem (hCV c hc) htV) (inv_mem (hCV c hc))) (inv_mem htV)
    · show c * t * c⁻¹ * t⁻¹ ∈ normalizer (D : Set G)
      exact mul_mem (mul_mem (mul_mem (hCD c hc) htD) (inv_mem (hCD c hc))) (inv_mem htD)
    · intro x hx
      exact commutator_mem_of_cong hVD hx (comm_acts_trivially ht hVD hT htV htD (hCV c hc) (hCD c hc) hx)
  have hzK : z ∈ centralizerSection V D := by
    have hle : ⁅Cen z, zpowers t⁆ ≤ centralizerSection V D := by
      rw [Subgroup.commutator_le]
      intro c hc u hu
      rcases eq_one_or_eq_of_mem_zpowers ht hu with h1 | h1
      · rw [h1, commutatorElement_one_right]
        exact one_mem _
      · rw [h1]
        exact hK c hc
    exact hle hzCt
  apply hDlt.not_ge
  intro v hv
  have h1 : ⁅v, z⁆ ∈ D := hzK.2.2 v hv
  have hx : z * v * z⁻¹ * v⁻¹ ∈ D := by
    have e : z * v * z⁻¹ * v⁻¹ = ⁅v, z⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h1
  have hxV : z * v * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hzV _).mp hv
  exact mem_of_sq_mem (hVodd v hv) (sq_mem_of_mul_mem hVD hxV (hPz v hv) hx)

end CFSG.GH74.GLS.Stage2.Bender.Thm2
