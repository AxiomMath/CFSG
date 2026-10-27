module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem core_conj_aux {c : G} (hc : c ∈ Subgroup.normalizer (J : Set G)) {o : G}
    (ho : o ∈ rankThreePrimeCore p J) : c * o * c⁻¹ ∈ rankThreePrimeCore p J := by
  have hJ : J.map (MulAut.conj c).toMonoidHom = J := Subgroup.mem_normalizer_iff_map_conj_eq.mp hc
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hnorm : J ≤ Subgroup.normalizer (rankThreePrimeCore p J : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p J
  have hcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hmap : (rankThreePrimeCore p J).map (MulAut.conj c).toMonoidHom ≤ rankThreePrimeCore p J := by
    refine CFSG.AGLEmbedding.le_glbPrimeCore (p := p) (H := J)
      (N := (rankThreePrimeCore p J).map (MulAut.conj c).toMonoidHom) ?_ ?_ ?_
    · exact (Subgroup.map_mono hOJ).trans hJ.le
    · calc J = J.map (MulAut.conj c).toMonoidHom := hJ.symm
        _ ≤ (Subgroup.normalizer (rankThreePrimeCore p J : Set G)).map (MulAut.conj c).toMonoidHom :=
            Subgroup.map_mono hnorm
        _ ≤ Subgroup.normalizer
              (((rankThreePrimeCore p J).map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) :=
            Subgroup.le_normalizer_map _
    · rwa [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact hmap ⟨o, ho, rfl⟩

@[expose] def u3K0 (p : ℕ) (x : G) (J : Subgroup G) : Subgroup G where
  carrier := {c | c ∈ Subgroup.centralizer ({x} : Set G) ∧ c ∈ Subgroup.normalizer (J : Set G) ∧
    ∀ j ∈ J, c * j * c⁻¹ * j⁻¹ ∈ rankThreePrimeCore p J}
  mul_mem' := by
    rintro a b ⟨haC, haN, haO⟩ ⟨hbC, hbN, hbO⟩
    refine ⟨mul_mem haC hbC, mul_mem haN hbN, fun j hj => ?_⟩
    have h1 : a * (b * j * b⁻¹ * j⁻¹) * a⁻¹ ∈ rankThreePrimeCore p J :=
      core_conj_aux haN (hbO j hj)
    have h2 := mul_mem h1 (haO j hj)
    have e : a * (b * j * b⁻¹ * j⁻¹) * a⁻¹ * (a * j * a⁻¹ * j⁻¹) = a * b * j * (a * b)⁻¹ * j⁻¹ := by
      group
    rwa [e] at h2
  one_mem' := by
    refine ⟨one_mem _, one_mem _, fun j hj => ?_⟩
    simpa using one_mem (rankThreePrimeCore p J)
  inv_mem' := by
    rintro a ⟨haC, haN, haO⟩
    refine ⟨inv_mem haC, inv_mem haN, fun j hj => ?_⟩
    have hj' : a⁻¹ * j * a ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem haN) j).mp hj
      simpa using this
    have h1 := inv_mem (haO (a⁻¹ * j * a) hj')
    have e : (a * (a⁻¹ * j * a) * a⁻¹ * (a⁻¹ * j * a)⁻¹)⁻¹ = a⁻¹ * j * a⁻¹⁻¹ * j⁻¹ := by
      group
    rwa [e] at h1

theorem u3_core_conj {c : G} (hc : c ∈ Subgroup.normalizer (J : Set G)) {o : G}
    (ho : o ∈ rankThreePrimeCore p J) : c * o * c⁻¹ ∈ rankThreePrimeCore p J :=
  core_conj_aux hc ho

theorem u3K0_conj_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) :
    ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ k ∈ u3K0 p x J, c * k * c⁻¹ ∈ u3K0 p x J := by
  intro c hcC k hk
  obtain ⟨hkC, hkN, hkO⟩ := hk
  have hcN : c ∈ Subgroup.normalizer (J : Set G) := hc.cent_le hcC
  refine ⟨mul_mem (mul_mem hcC hkC) (inv_mem hcC), mul_mem (mul_mem hcN hkN) (inv_mem hcN),
    fun j hj => ?_⟩
  have hj' : c⁻¹ * j * c ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcN) j).mp hj
    simpa using this
  have h1 := u3_core_conj hcN (hkO (c⁻¹ * j * c) hj')
  have e : c * (k * (c⁻¹ * j * c) * k⁻¹ * (c⁻¹ * j * c)⁻¹) * c⁻¹ =
      c * k * c⁻¹ * j * (c * k * c⁻¹)⁻¹ * j⁻¹ := by
    group
  rwa [e] at h1

theorem u3_core_le_K0_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) : rankThreePrimeCore p J ≤ u3K0 p x J := by
  intro o ho
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  refine ⟨hc.le_cent (hOJ ho), Subgroup.le_normalizer (hOJ ho), fun j hj => ?_⟩
  have h1 : j * o⁻¹ * j⁻¹ ∈ rankThreePrimeCore p J :=
    u3_core_conj (Subgroup.le_normalizer hj) (inv_mem ho)
  have h2 := mul_mem ho h1
  have e : o * (j * o⁻¹ * j⁻¹) = o * j * o⁻¹ * j⁻¹ := by group
  rwa [e] at h2

theorem x_mem_u3K0_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) : x ∈ u3K0 p x J := by
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨hxC, hc.cent_le hxC, fun j hj => ?_⟩
  have h : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.mp (hc.le_cent hj)
  have e : x * j * x⁻¹ * j⁻¹ = 1 := by rw [← h]; group
  rw [e]
  exact one_mem _

theorem u3_T_inf_K0_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig Typ G p P M x J) : u3T P x J ⊓ u3K0 p x J = ⊥ := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  set O : Subgroup G := rankThreePrimeCore p J with hO
  have hOJ : O ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOcop : p.Coprime (Nat.card O) := CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  have hPO : (P : Subgroup G) ⊓ O = ⊥ := by
    have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ O) := P.isPGroup'.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hdvd : Nat.card ((P : Subgroup G) ⊓ O : Subgroup G) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have : p ∣ Nat.card O := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
      exact (hp.coprime_iff_not_dvd.mp hOcop) this
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  rw [eq_bot_iff]
  rintro t ⟨htT, htK⟩
  obtain ⟨⟨htP, htC⟩, htJ⟩ := htT
  obtain ⟨-, -, htO⟩ := htK
  have hcentral : ψ ⟨t, htJ⟩ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    have hmem : (⟨t, htJ⟩ * j * (⟨t, htJ⟩ : J)⁻¹ * j⁻¹ : J) ∈ ψ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact htO (j : G) j.2
    have h1 : ψ ⟨t, htJ⟩ * ψ j * (ψ ⟨t, htJ⟩)⁻¹ * (ψ j)⁻¹ = 1 := by
      have := MonoidHom.mem_ker.mp hmem
      simpa using this
    have h2 : ψ ⟨t, htJ⟩ * ψ j = ψ j * ψ ⟨t, htJ⟩ := by
      have := mul_inv_eq_one.mp h1
      exact mul_inv_eq_iff_eq_mul.mp this
    exact h2.symm
  rw [hZ, Subgroup.mem_bot] at hcentral
  have htker : (⟨t, htJ⟩ : J) ∈ ψ.ker := hcentral
  rw [hker, Subgroup.mem_subgroupOf] at htker
  have : t ∈ (P : Subgroup G) ⊓ O := ⟨htP, htker⟩
  rw [hPO] at this
  exact this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
