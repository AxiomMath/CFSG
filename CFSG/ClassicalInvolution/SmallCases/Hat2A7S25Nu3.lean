module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N1
public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25V30
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Nu

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.Eps

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped commutatorElement

section Nu

variable {G : Type} [Group G] {K : Subgroup G} {π : OddQuot K →* A7} {zE : OddQuot K}
  (cov : IsDoubleCoverA7 π zE)

theorem nuG_eq_one_iff_comm {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    nuG cov n = 1 ↔ ∀ l ∈ K, ⁅n, l⁆ ∈ oddCoreOf K := by
  have hmem : ∀ x : ↥K, ⁅n, (x : G)⁆ ∈ K := fun x => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hn x).mp x.2) (Subgroup.inv_mem _ x.2)
  have e1 : ∀ x : ↥K, (⟨⁅n, (x : G)⁆, hmem x⟩ : ↥K) = conjOn K n hn x * x⁻¹ := fun x => by
    apply Subtype.ext
    show ⁅n, (x : G)⁆ = (n * x * n⁻¹) * (x : G)⁻¹
    rw [commutatorElement_def]
  have key : ∀ x : ↥K, ((conjOn K n hn x : ↥K) : OddQuot K) = (x : OddQuot K) ↔
      ⁅n, (x : G)⁆ ∈ oddCoreOf K := fun x => by
    rw [mem_oddCoreOf_iff]
    constructor
    · intro h
      refine ⟨hmem x, ?_⟩
      rw [e1]
      apply (QuotientGroup.eq_one_iff _).mp
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, mul_inv_cancel]
    · rintro ⟨hK, h⟩
      rw [e1] at h
      have h1 := (QuotientGroup.eq_one_iff _).mpr h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h1
      exact h1
  rw [nuG_eq_one_iff cov hn]
  constructor
  · intro h l hl
    have h1 := congrArg (fun β : MulAut (OddQuot K) => β ((⟨l, hl⟩ : ↥K) : OddQuot K)) h
    simp only [MulAut.one_apply] at h1
    rw [oddQuotAut_mk] at h1
    exact (key ⟨l, hl⟩).mp h1
  · intro h
    refine MulEquiv.ext (fun e => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective e
    rw [oddQuotAut_mk, MulAut.one_apply]
    exact (key x).mpr (h x x.2)

end Nu

section Triv

variable {G : Type} [Group G] {K : Subgroup G} {π : OddQuot K →* A7} {zE : OddQuot K}
  (cov : IsDoubleCoverA7 π zE) (z t' : G) (ht2 : t' * t' = 1)

@[expose] def Triv : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (K : Set G) ∧ y * z = z * y ∧
    t' * y * t' ∈ Subgroup.normalizer (K : Set G) ∧ nuG cov y = 1 ∧
    nuG cov (t' * y * t') = 1}
  mul_mem' := by
    rintro y₁ y₂ ⟨hN₁, hz₁, hN₁', hν₁, hν₁'⟩ ⟨hN₂, hz₂, hN₂', hν₂, hν₂'⟩
    have e1 : t' * (y₁ * y₂) * t' = (t' * y₁ * t') * (t' * y₂ * t') := by
      calc t' * (y₁ * y₂) * t' = t' * y₁ * (t' * t') * y₂ * t' := by rw [ht2]; group
        _ = (t' * y₁ * t') * (t' * y₂ * t') := by group
    refine ⟨Subgroup.mul_mem _ hN₁ hN₂, ?_, ?_, ?_, ?_⟩
    · exact (Commute.mul_left (show Commute y₁ z from hz₁) (show Commute y₂ z from hz₂))
    · rw [e1]
      exact Subgroup.mul_mem _ hN₁' hN₂'
    · rw [nuG_mul cov hN₁ hN₂, hν₁, hν₂, one_mul]
    · rw [e1, nuG_mul cov hN₁' hN₂', hν₁', hν₂', one_mul]
  one_mem' := by
    have h1 : t' * (1 : G) * t' = 1 := by rw [mul_one, ht2]
    exact ⟨Subgroup.one_mem _, by rw [one_mul, mul_one], by rw [h1]; exact Subgroup.one_mem _,
      nuG_one cov, by rw [h1]; exact nuG_one cov⟩
  inv_mem' := by
    rintro y ⟨hN, hz, hN', hν, hν'⟩
    have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
    have e1 : t' * y⁻¹ * t' = (t' * y * t')⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hti]
      group
    refine ⟨Subgroup.inv_mem _ hN, (show Commute y z from hz).inv_left, ?_, ?_, ?_⟩
    · rw [e1]
      exact Subgroup.inv_mem _ hN'
    · rw [nuG_inv cov hN, hν, inv_one]
    · rw [e1, nuG_inv cov hN', hν', inv_one]

variable {cov z t' ht2}

theorem triv_swap (htz : t' * z = z * t') {y : G} (hy : y ∈ Triv cov z t' ht2) :
    t' * y * t' ∈ Triv cov z t' ht2 := by
  obtain ⟨hN, hz, hN', hν, hν'⟩ := hy
  have e0 : t' * (t' * y * t') * t' = y := by
    calc t' * (t' * y * t') * t' = (t' * t') * y * (t' * t') := by group
      _ = y := by rw [ht2]; group
  refine ⟨hN', ?_, ?_, hν', ?_⟩
  · have h1 : Commute t' z := htz
    exact (h1.mul_left (show Commute y z from hz)).mul_left h1
  · rw [e0]
    exact hN
  · rw [e0]
    exact hν

theorem triv_conj_of_normalizer {c y : G} (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hcz : c * z = z * c) (hct : t' * c * t' ∈ Subgroup.normalizer (K : Set G))
    (hy : y ∈ Triv cov z t' ht2) : c * y * c⁻¹ ∈ Triv cov z t' ht2 := by
  obtain ⟨hN, hz, hN', hν, hν'⟩ := hy
  have hti : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
  have e2 : (t' * c * t')⁻¹ = t' * c⁻¹ * t' := by
    rw [mul_inv_rev, mul_inv_rev, hti]
    group
  have e1 : t' * (c * y * c⁻¹) * t' = (t' * c * t') * (t' * y * t') * (t' * c * t')⁻¹ := by
    rw [e2]
    calc t' * (c * y * c⁻¹) * t' = t' * c * (t' * t') * y * (t' * t') * c⁻¹ * t' := by
          rw [ht2]; group
      _ = (t' * c * t') * (t' * y * t') * (t' * c⁻¹ * t') := by group
  have hc' : Commute c z := hcz
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hN) (Subgroup.inv_mem _ hcN),
    (hc'.mul_left (show Commute y z from hz)).mul_left hc'.inv_left, ?_, ?_, ?_⟩
  · rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hct hN') (Subgroup.inv_mem _ hct)
  · rw [nuG_conj cov hcN hN, hν, mul_one, mul_inv_cancel]
  · rw [e1, nuG_conj cov hct hN', hν', mul_one, mul_inv_cancel]

end Triv

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' : G}
  {π : OddQuot K →* A7} {zE : OddQuot K}

theorem nuG_z_eq_one (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE) :
    nuG cov z = 1 := by
  refine (nuG_eq_one_iff_comm cov (Subgroup.le_normalizer h.hz.mem)).mpr (fun l hl => ?_)
  have : ⁅z, l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (h.hz.commute_of_mem hl)
  rw [this]
  exact Subgroup.one_mem _

theorem conj_t'_mem_normalizer (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {x : G}
    (hxz : x * z = z * x) (hxK : conjSub x K = K) :
    t' * x * t' ∈ Subgroup.normalizer (K : Set G) := by
  have hxK' : conjSub x K' = K' := (N.cz_fix_iff h hxz).mp hxK
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub_mul, conjSub_mul, N.conjSub_t'_K h, hxK', N.conjSub_t'_K' h]

theorem triv_conj_mem (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE)
    {c y : G} (hcz : c * z = z * c) (hy : y ∈ Triv cov z t' h.ht'2) :
    c * y * c⁻¹ ∈ Triv cov z t' h.ht'2 := by
  have htz : t' * z = z * t' := N.t'_comm_z h
  rcases N.cz_cover h hcz with hc | hc
  · exact triv_conj_of_normalizer (mem_normalizer_iff_conjSub_eq.mpr hc) hcz
      (conj_t'_mem_normalizer h hcz hc) hy
  · have hc0z : (c * t') * z = z * (c * t') := by
      calc c * t' * z = c * (t' * z) := by rw [mul_assoc]
        _ = c * (z * t') := by rw [htz]
        _ = (c * z) * t' := by rw [mul_assoc]
        _ = (z * c) * t' := by rw [hcz]
        _ = z * (c * t') := by rw [mul_assoc]
    have e1 : c * y * c⁻¹ = (c * t') * (t' * y * t') * (c * t')⁻¹ := by
      rw [mul_inv_rev, h.ht'inv]
      calc c * y * c⁻¹ = c * (t' * t') * y * (t' * t') * c⁻¹ := by rw [h.ht'2]; group
        _ = (c * t') * (t' * y * t') * (t' * c⁻¹) := by group
    rw [e1]
    exact triv_conj_of_normalizer (mem_normalizer_iff_conjSub_eq.mpr hc) hc0z
      (conj_t'_mem_normalizer h hc0z hc) (triv_swap htz hy)

theorem conjSub_R_of_mem (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K) : conjSub s R = R := by
  rcases h.perm_R hsS with h1 | h1
  · exact h1
  · exfalso
    have hR'K : R' ≤ K := by
      rw [← h1, ← hsK]
      exact conjSub_mono h.hRsyl.1
    have := h.hΩ.eq_of_le_of_le h.hK' h.hK h.hR'syl.2.1
      (by have := h.hqR'.eight_le; omega) h.hR'syl.1 hR'K
    exact h.hs.hne this

theorem commutes_R_of_nuG_eq_one (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (cov : IsDoubleCoverA7 π zE) {s : G} (hsS : s ∈ (S : Subgroup G))
    (hsN : s ∈ Subgroup.normalizer (K : Set G)) (hν : nuG cov s = 1) :
    ∀ r ∈ R, s * r = r * s := by
  intro r hr
  have hsR : conjSub s R = R := conjSub_R_of_mem h hsS (mem_normalizer_iff_conjSub_eq.mp hsN)
  have h1 : ⁅s, r⁆ ∈ oddCoreOf K := (nuG_eq_one_iff_comm cov hsN).mp hν r (h.hRsyl.1 hr)
  have h2 : ⁅s, r⁆ ∈ R := by
    have h3 : s * r * s⁻¹ ∈ R := by
      have := conj_mem_conjSub (n := s) hr
      rwa [hsR] at this
    rw [commutatorElement_def]
    exact R.mul_mem h3 (R.inv_mem hr)
  have h4 : ⁅s, r⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
    (h.hRsyl.2.1.to_le (Subgroup.zpowers_le.mpr h2))
  exact commutatorElement_eq_one_iff_mul_comm.mp h4

theorem eq_one_or_eq_z_of_mem_S (h11 : Hat2A7M.Asc77.C25_11)
    (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hs : s ∈ Triv cov z t' h.ht'2) : s = 1 ∨ s = z := by
  obtain ⟨hsN, -, hsN', hsν, hsν'⟩ := hs
  have hc1 := commutes_R_of_nuG_eq_one h cov hsS hsN hsν
  have hS2 : t' * s * t' ∈ (S : Subgroup G) := S.mul_mem (S.mul_mem h.ht'S hsS) h.ht'S
  have hc2 := commutes_R_of_nuG_eq_one h cov hS2 hsN' hsν'
  have hcent : s ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : R ⊔ R' ≤ Subgroup.centralizer ({s} : Set G) := by
      refine sup_le (fun r hr => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc1 r hr).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hr' : r ∈ conjSub t' R := by
          rw [h.ht'R]
          exact hr
        have hr0 : t' * r * t' ∈ R := by
          have := mem_conjSub_iff.mp hr'
          rwa [h.ht'inv] at this
        have e3 := hc2 (t' * r * t') hr0
        have e4 : t' * (s * r) * t' = t' * (r * s) * t' := by
          calc t' * (s * r) * t' = t' * s * t' * (t' * r * t') := by
                calc t' * (s * r) * t' = t' * s * (t' * t') * r * t' := by rw [h.ht'2]; group
                  _ = t' * s * t' * (t' * r * t') := by group
            _ = t' * r * t' * (t' * s * t') := e3
            _ = t' * (r * s) * t' := by
                calc t' * r * t' * (t' * s * t') = t' * r * (t' * t') * s * t' := by group
                  _ = t' * (r * s) * t' := by rw [h.ht'2]; group
        exact (mul_left_cancel (mul_right_cancel e4)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hmem : s ∈ Subgroup.zpowers z := by
    rw [← h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp]
    exact Subgroup.mem_inf.mpr ⟨hsS, hcent⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact C25H.zpow_eq_one_or_self h.hz.sq j

theorem eq_one_or_eq_z_of_triv (h11 : Hat2A7M.Asc77.C25_11)
    (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (cov : IsDoubleCoverA7 π zE) {y : G}
    (hy : y ∈ Triv cov z t' h.ht'2) {i : ℕ} (hord : orderOf y = 2 ^ i) : y = 1 ∨ y = z := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hmemC : ∀ g : G, g ∈ C ↔ g * z = z * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmemC s).mpr (h.hyp.hzS s hs)
  have hyC : y ∈ C := (hmemC y).mpr hy.2.1
  obtain ⟨c, hcC, hcS⟩ := C25V.exists_conj_mem_sylow S hSC hyC hord
  have hcz : c * z = z * c := (hmemC c).mp hcC
  have hy1 := triv_conj_mem h cov hcz hy
  rcases eq_one_or_eq_z_of_mem_S h11 h cov hcS hy1 with h1 | h1
  · left
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  · right
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [h1]
      _ = c⁻¹ * (z * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group

end Main

end CFSG.ClassicalInvolution.Hat2A7S.Eps
