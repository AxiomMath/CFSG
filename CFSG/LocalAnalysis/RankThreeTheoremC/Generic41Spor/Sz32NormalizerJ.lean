module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32SharedProp31
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

private theorem nj_solvable_of_regular_mem {p : ℕ} [Fact p.Prime] {K O : Subgroup G}
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hodd : ¬ 2 ∣ Nat.card O)
    (hreg : ∀ k ∈ K, Nat.Coprime p (orderOf k) → k ∈ O) : Group.IsSolvable ↥K := by
  have hp : p.Prime := Fact.out
  have hNK : O ⊓ K ≤ K := inf_le_right
  haveI hNnormal : ((O ⊓ K).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNK]
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hO := Subgroup.mem_normalizer_iff.mp (hKO hn) h
    constructor
    · intro hh
      rw [Subgroup.mem_inf] at hh ⊢
      exact ⟨hO.mp hh.1, K.mul_mem (K.mul_mem hn hh.2) (K.inv_mem hn)⟩
    · intro hh
      rw [Subgroup.mem_inf] at hh ⊢
      refine ⟨hO.mpr hh.1, ?_⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hn) hh.2) hn
      simpa [mul_assoc] using this
  haveI hsolN : Group.IsSolvable ↥(O ⊓ K) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have h1 : Nat.card ↥(O ⊓ K) ∣ Nat.card ↥O := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Odd (Nat.card ↥O) := Nat.odd_iff.mpr (by omega)
    exact h2.of_dvd_nat h1
  have hpgrp : IsPGroup p (↥K ⧸ (O ⊓ K).subgroupOf K) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (k : G)).ne' p hp.one_lt.ne'
    have hdvd : p ^ a ∣ orderOf (k : G) := hord ▸ dvd_mul_right _ _
    have hord' : orderOf ((k : G) ^ p ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero a hp.ne_zero) hdvd, hord,
        Nat.mul_div_cancel_left m (pow_pos hp.pos a)]
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
    have hmemO : (k : G) ^ p ^ a ∈ O := hreg _ (pow_mem k.2 _) (by rw [hord']; exact hcop)
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨hmemO, pow_mem k.2 _⟩
  haveI : Finite (↥K ⧸ (O ⊓ K).subgroupOf K) := inferInstance
  haveI := hpgrp.isNilpotent
  haveI : Group.IsSolvable (↥K ⧸ (O ⊓ K).subgroupOf K) := inferInstance
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNK)
    (QuotientGroup.mk' ((O ⊓ K).subgroupOf K)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.inclusion_range]

private theorem nj_derived_le {C J K₀ : Subgroup G} {A : Type*} [Group A] [Group.IsSolvable A]
    [Group.IsSolvable ↥K₀] (hJC : J ≤ C) (hCJ : C ≤ Subgroup.normalizer (J : Set G)) (hKC : K₀ ≤ C)
    (φ : ↥C →* A) (hφJ : ∀ (j : G) (hj : j ∈ J), φ ⟨j, hJC hj⟩ = 1)
    (hker : ∀ c : ↥C, φ c = 1 → ∃ k ∈ K₀, ∃ j ∈ J, (c : G) = k * j) :
    ∃ m, (derivedSeries ↥C m).map C.subtype ≤ J := by
  haveI hJn : (J.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJC]; exact hCJ
  let f : ↥K₀ →* ↥C ⧸ J.subgroupOf C :=
    (QuotientGroup.mk' (J.subgroupOf C)).comp (Subgroup.inclusion hKC)
  let g : (↥C ⧸ J.subgroupOf C) →* A :=
    QuotientGroup.lift (J.subgroupOf C) φ (fun c hc => hφJ c hc)
  have hsolv : Group.IsSolvable (↥C ⧸ J.subgroupOf C) := by
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro q hq
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    have hφc : φ c = 1 := hq
    obtain ⟨k, hk, j, hj, hcj⟩ := hker c hφc
    refine ⟨⟨k, hk⟩, ?_⟩
    show QuotientGroup.mk (⟨k, hKC hk⟩ : ↥C) = (QuotientGroup.mk c : ↥C ⧸ J.subgroupOf C)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hcj] using hj
  obtain ⟨m, hm⟩ := (Group.isSolvable_def _).mp hsolv
  refine ⟨m, ?_⟩
  have h1 : (derivedSeries ↥C m).map (QuotientGroup.mk' (J.subgroupOf C)) = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _)]; exact hm
  have h2 : derivedSeries ↥C m ≤ J.subgroupOf C := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1; exact h1
  rintro _ ⟨c, hc, rfl⟩
  exact h2 hc

private theorem nj_normalizes {C J : Subgroup G} [Group.IsPerfect J] (hJC : J ≤ C) {n : G}
    (hn : C.map (MulAut.conj n).toMonoidHom = C)
    (hres : ∃ m, (derivedSeries ↥C m).map C.subtype ≤ J) :
    n ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨m, hm⟩ := hres
  have hCtop : (⊤ : Subgroup ↥C).map C.subtype = C := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hJD : ∀ k, J ≤ (derivedSeries ↥C k).map C.subtype := by
    intro k
    induction k with
    | zero => rw [derivedSeries_zero, hCtop]; exact hJC
    | succ k ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator]
      calc J = ⁅J, J⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ _ := Subgroup.commutator_mono ih ih
  have hDinv : ∀ k, ((derivedSeries ↥C k).map C.subtype).map (MulAut.conj n).toMonoidHom =
      (derivedSeries ↥C k).map C.subtype := by
    intro k
    induction k with
    | zero => rw [derivedSeries_zero, hCtop]; exact hn
    | succ k ih => rw [derivedSeries_succ, Subgroup.map_commutator, Subgroup.map_commutator, ih]
  have hJeq : (derivedSeries ↥C m).map C.subtype = J := le_antisymm hm (hJD m)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc J.map (MulAut.conj n).toMonoidHom
      = ((derivedSeries ↥C m).map C.subtype).map (MulAut.conj n).toMonoidHom := by rw [hJeq]
    _ = (derivedSeries ↥C m).map C.subtype := hDinv m
    _ = J := hJeq

private theorem nj_map_conj_centralizer {x n : G}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.centralizer ({x} : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G),
      ∀ c ∈ Subgroup.centralizer ({x} : Set G),
        m * c * m⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro m hm c hc
    have h1 : m⁻¹ * x * m ∈ Subgroup.zpowers x := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) x).mp (Subgroup.mem_zpowers x)
      simpa using this
    have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (hc x rfl).symm
    have h2 : m⁻¹ * x * m ∈ Subgroup.centralizer ({c} : Set G) :=
      (Subgroup.zpowers_le.mpr hxc) h1
    rw [Subgroup.mem_centralizer_iff] at h2 ⊢
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have h3 := h2 c rfl
    calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [← h3]
      _ = m * c * m⁻¹ * x := by group
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    exact key n hn c hc
  · intro c hc
    refine ⟨n⁻¹ * c * n, ?_, ?_⟩
    · have := key n⁻¹ (inv_mem hn) c hc
      simpa using this
    · simp [mul_assoc]

theorem sz32_normalizer_le_normalizer_J (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hSz : Sz32Facts) (hc : PointConfig IsSz32Type G 5 P M x J) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  intro n hn
  haveI : Group.IsPerfect J := hc.perfect
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hJC : J ≤ Subgroup.centralizer ({x} : Set G) := hc.le_cent
  obtain ⟨Q, _, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  obtain ⟨ρ, hρ⟩ := sps_exists_action (p := 5) hc.cent_le ψ hψ hker
  have hout : Nat.card (Outer Q) = 5 := hSz.outer Q hQ
  haveI : Group.IsSolvable (Outer Q) := by
    haveI : IsCyclic (Outer Q) := isCyclic_of_prime_card hout
    infer_instance
  have hprop := point_prop31_ii hS hD1 hU0 hc
  have hodd := odd_card_pPrimeCoreIn_of_not_le hS hD1 hc.sigma hc.core hc.generic.2.2.2.ge
    hc.generic.2.1.2.2.2.2
  have hKC : u3K0 5 x J ≤ Subgroup.centralizer ({x} : Set G) := fun k hk => hk.1
  haveI hKsolv : Group.IsSolvable ↥(u3K0 5 x J) :=
    nj_solvable_of_regular_mem (p := 5)
      (O := CFSG.ABGTheoremB.pPrimeCoreIn 5 (Subgroup.centralizer ({x} : Set G)))
      (fun k hk => CFSG.ABGTheoremB.le_normalizer_map_subtype _ (CFSG.pPrimeCore 5 _) (hKC hk))
      hodd hprop.2
  have hρJ : ∀ (j : ↥J), ρ ⟨j, hJC j.2⟩ = MulAut.conj (ψ j) := by
    intro j
    ext q
    obtain ⟨j', rfl⟩ := hψ q
    have hj : ((⟨(j : G), hJC j.2⟩ : ↥(Subgroup.centralizer ({x} : Set G))) : G) * (j' : G) *
        ((⟨(j : G), hJC j.2⟩ : ↥(Subgroup.centralizer ({x} : Set G))) : G)⁻¹ ∈ J :=
      mul_mem (mul_mem j.2 j'.2) (inv_mem j.2)
    rw [hρ ⟨j, hJC j.2⟩ j' hj]
    have h1 : (⟨(j : G) * (j' : G) * (j : G)⁻¹, hj⟩ : ↥J) = j * j' * j⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  let φ : ↥(Subgroup.centralizer ({x} : Set G)) →* Outer Q :=
    (QuotientGroup.mk' (inner Q)).comp ρ
  have hφJ : ∀ (j : G) (hj : j ∈ J), φ ⟨j, hJC hj⟩ = 1 := by
    intro j hj
    show QuotientGroup.mk' (inner Q) (ρ ⟨j, hJC hj⟩) = 1
    rw [show ρ ⟨j, hJC hj⟩ = MulAut.conj (ψ ⟨j, hj⟩) from hρJ ⟨j, hj⟩]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨ψ ⟨j, hj⟩, rfl⟩
  have hkerφ : ∀ c : ↥(Subgroup.centralizer ({x} : Set G)), φ c = 1 →
      ∃ k ∈ u3K0 5 x J, ∃ j ∈ J, (c : G) = k * j := by
    intro c hc1
    obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff _).mp hc1
    obtain ⟨j₀, rfl⟩ := hψ q
    obtain ⟨k', hk'⟩ : ∃ k' : ↥(Subgroup.centralizer ({x} : Set G)),
        k' = c * (⟨j₀, hJC j₀.2⟩ : ↥(Subgroup.centralizer ({x} : Set G)))⁻¹ := ⟨_, rfl⟩
    have hk'1 : ρ k' = 1 := by
      rw [hk', map_mul, map_inv, hρJ j₀, ← hq, mul_inv_cancel]
    refine ⟨(k' : G), ⟨k'.2, hc.cent_le k'.2, fun j hj => ?_⟩, (j₀ : G), j₀.2, ?_⟩
    · have hmem : (k' : G) * j * (k' : G)⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hc.cent_le k'.2) j).mp hj
      have h1 := hρ k' ⟨j, hj⟩ hmem
      rw [hk'1] at h1
      have h2 : ψ (⟨(k' : G) * j * (k' : G)⁻¹, hmem⟩ * ⟨j, hj⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, ← h1]
        simp
      have h3 : (⟨(k' : G) * j * (k' : G)⁻¹, hmem⟩ * ⟨j, hj⟩⁻¹ : ↥J) ∈ ψ.ker := h2
      rw [hker, Subgroup.mem_subgroupOf] at h3
      simpa using h3
    · rw [hk']; simp
  exact nj_normalizes hJC (nj_map_conj_centralizer hn)
    (nj_derived_le hJC hc.cent_le hKC φ hφJ hkerφ)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
