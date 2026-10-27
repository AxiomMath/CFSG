module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

section Tools

theorem kl5_normal_le_center_or_eq_top {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (W : Subgroup Q) [W.Normal] :
    W ≤ Subgroup.center Q ∨ W = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hQ
  have hnorm : (W.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q ⧸ Subgroup.center Q) _ hsimple
    (W.map (QuotientGroup.mk' (Subgroup.center Q))) hnorm with h0 | h1
  · left
    intro n hn
    have : QuotientGroup.mk' (Subgroup.center Q) n ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := by
      rw [← h0]
      exact ⟨n, hn, rfl⟩
    simpa using this
  · right
    have hcov : ∀ g : Q, ∃ c ∈ Subgroup.center Q,
        (QuotientGroup.mk g : Q ⧸ W) = QuotientGroup.mk c := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center Q) g ∈
          W.map (QuotientGroup.mk' (Subgroup.center Q)) := by rw [h1]; trivial
      obtain ⟨n, hn, hng⟩ := hg
      have hc : n⁻¹ * g ∈ Subgroup.center Q := by
        have : (QuotientGroup.mk' (Subgroup.center Q)) (n⁻¹ * g) = 1 := by
          rw [map_mul, map_inv, hng, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff _).mp this
      refine ⟨n⁻¹ * g, hc, ?_⟩
      rw [QuotientGroup.eq]
      have := ‹W.Normal›.conj_mem n⁻¹ (W.inv_mem hn) g⁻¹
      simpa [mul_assoc] using this
    have hcomm : IsMulCommutative (Q ⧸ W) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      induction x using QuotientGroup.induction_on with | _ a => ?_
      induction y using QuotientGroup.induction_on with | _ b => ?_
      obtain ⟨c, hc, hca⟩ := hcov a
      obtain ⟨d, hd, hdb⟩ := hcov b
      rw [hca, hdb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        (Subgroup.mem_center_iff.mp hd) c]
    have hle : commutator Q ≤ W :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
    rw [hperf] at hle
    exact top_le_iff.mp hle

variable {Y : Type*} [Group Y]

theorem kl5_le_centralizer_of_perfect {B L : Subgroup Y} (hperf : ⁅L, L⁆ = L)
    (hLB : L ≤ Subgroup.normalizer (B : Set Y)) (hBL : B ≤ Subgroup.normalizer (L : Set Y))
    (hc : B ⊓ L ≤ Subgroup.centralizer (L : Set Y)) :
    L ≤ Subgroup.centralizer (B : Set Y) := by
  have h1 : ⁅L, B⁆ ≤ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.commutator_le]
    intro l hl b hb
    refine hc ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLB hl) b).mp hb) (B.inv_mem hb)
    · rw [commutatorElement_def, show l * b * l⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) by group]
      exact L.mul_mem hl ((Subgroup.mem_normalizer_iff.mp (hBL hb) l⁻¹).mp (L.inv_mem hl))
  have h2 : ⁅⁅L, B⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
  have h3 : ⁅⁅B, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm B L]; exact h2
  have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L) (H₃ := B) h2 h3
  rw [hperf] at h4
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h4

theorem kl5_eq_bot_of_perfect_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite Y] {L : Subgroup Y}
    (hperf : ⁅L, L⁆ = L) (hp : IsPGroup p L) : L = ⊥ := by
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hperf
  have : Group.IsNilpotent L := hp.isNilpotent
  by_contra hne
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hne
  exact Group.IsPerfect.not_isNilpotent L inferInstance

theorem kl5_range_le_or_le_centralizer {Γ Λ : Type*} [Group Γ] [Group Λ] {ρ : Γ →* Λ}
    (hρ : Function.Surjective ρ) (hΛ : CFSG.Open.IsQuasisimple Λ) {φ : Γ →* Y}
    (hker : ρ.ker ≤ φ.ker) {B : Subgroup Y}
    (hLB : φ.range ≤ Subgroup.normalizer (B : Set Y))
    (hBL : B ≤ Subgroup.normalizer (φ.range : Set Y)) (hperf : ⁅φ.range, φ.range⁆ = φ.range) :
    φ.range ≤ B ∨ φ.range ≤ Subgroup.centralizer (B : Set Y) := by
  have hW : (B.comap φ).Normal := ⟨fun w hw g => by
    rw [Subgroup.mem_comap] at hw ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hLB ⟨g, rfl⟩) (φ w)).mp hw⟩
  have : ((B.comap φ).map ρ).Normal := hW.map ρ hρ
  have hfac : ∀ a b : Γ, ρ a = ρ b → φ a = φ b := fun a b hab => by
    have h1 : φ (a⁻¹ * b) = 1 := hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hab,
      inv_mul_cancel])
    rwa [map_mul, map_inv, inv_mul_eq_one] at h1
  rcases kl5_normal_le_center_or_eq_top hΛ ((B.comap φ).map ρ) with hz | htop
  · right
    refine kl5_le_centralizer_of_perfect hperf hLB hBL ?_
    rintro _ ⟨hxB, w, rfl⟩
    have hwW : ρ w ∈ Subgroup.center Λ := hz ⟨w, hxB, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨γ, rfl⟩
    have h := hfac (γ * w) (w * γ) (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hwW (ρ γ))
    rwa [map_mul, map_mul] at h
  · left
    rintro _ ⟨γ, rfl⟩
    obtain ⟨w, hw, hwγ⟩ : ρ γ ∈ (B.comap φ).map ρ := by rw [htop]; trivial
    rw [← hfac w γ hwγ]
    exact hw

end Tools

section Reduction

variable {G : Type} [Group G]

theorem kl5_exists_barM_hom {M L : Subgroup G} (hLM : L ≤ M) :
    ∃ ρ : ↥L →* ↥(barM M L), Function.Surjective ρ ∧
      ∀ l : ↥L, ρ l = 1 → (l : G) ∈ pCoreOf 2 M := by
  let f : ↥L →* ↥(barM M L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)).codRestrict (barM M L)
      (fun x => ⟨⟨x, hLM x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  refine ⟨f, ?_, fun l hl => ?_⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  · have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM l.2⟩ = 1 := congrArg Subtype.val hl
    exact coe_mem_pCoreOf_two_of_mk_eq_one _ h1

end Reduction

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_barM_of_le_inf {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hph : D1PhaseThree p P M H R) (hXel : IsElemAbelian p X)
    (hY₀B : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer
        (((X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)))
    (hC : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer
        (((X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)))
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) : ¬ p ∣ Nat.card (barM M L) := by
  have hp : p.Prime := Fact.out
  have hLH : L ≤ H := hLK.trans inf_le_left
  have hQ : pCoreOf 2 M ≤ GLBPrimeCore p H := hph.twoCore_M_le_glbPrimeCore
  obtain ⟨ρ, hρs, hρk⟩ := kl5_exists_barM_hom hL.le
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set B := (X.subgroupOf H).map π
  set Y₀ := ((H ⊓ M).subgroupOf H).map π
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥L →* H ⧸ primeComplementCore (G := H) p,
      ∀ l : ↥L, φ l = π ⟨(l : G), hLH l.2⟩ :=
    ⟨π.comp (Subgroup.inclusion hLH), fun l => rfl⟩
  have hker : ρ.ker ≤ φ.ker := by
    intro l hl
    have h1 : (l : G) ∈ GLBPrimeCore p H := hQ (hρk l (MonoidHom.mem_ker.mp hl))
    have h2 : (⟨(l : G), hLH l.2⟩ : H) ∈ primeComplementCore (G := H) p := by
      rw [← glbPrimeCore_subgroupOf p H]
      exact h1
    rw [MonoidHom.mem_ker, hφ]
    exact (QuotientGroup.eq_one_iff _).mpr h2
  have hY₀le : φ.range ≤ Y₀ := by
    rintro _ ⟨l, rfl⟩
    rw [hφ]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr (hLK l.2))
  have hLB : φ.range ≤ Subgroup.normalizer (B : Set (H ⧸ primeComplementCore (G := H) p)) :=
    hY₀le.trans hY₀B
  have hBL : B ≤ Subgroup.normalizer (φ.range : Set (H ⧸ primeComplementCore (G := H) p)) := by
    refine le_normalizer_of_forall_mul_mul_inv_mem ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨l, rfl⟩
    have hxl : (x : G) * (l : G) * (x : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hXL (Subgroup.mem_subgroupOf.mp hx)) _).mp l.2
    refine ⟨⟨(x : G) * (l : G) * (x : G)⁻¹, hxl⟩, ?_⟩
    rw [hφ, hφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.perfect
  have hperf : ⁅φ.range, φ.range⁆ = φ.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range φ)
  have hres := kl5_range_le_or_le_centralizer hρs hL.component.2.2 hker hLB hBL hperf
  have hpgrp : IsPGroup p φ.range := by
    rcases hres with h | h
    ·
      intro g
      obtain ⟨x, hx, hxg⟩ := h g.2
      have hxp : x ^ p = 1 := Subtype.ext (hXel.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))
      refine ⟨1, Subtype.ext ?_⟩
      have h1 : (g : H ⧸ primeComplementCore (G := H) p) ^ p = 1 := by
        rw [← hxg, ← map_pow, hxp, map_one]
      simpa using h1
    · exact Rbar.isPGroup'.to_le ((le_inf hY₀le h).trans hC)
  have hbot : φ.range = ⊥ := kl5_eq_bot_of_perfect_of_isPGroup hperf hpgrp
  have hLN : L ≤ GLBPrimeCore p H := by
    intro l hl
    have h1 : φ ⟨l, hl⟩ = 1 := by
      have hmem : φ ⟨l, hl⟩ ∈ φ.range := ⟨_, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    rw [hφ] at h1
    have h2 : (⟨l, hLH hl⟩ : H) ∈ primeComplementCore (G := H) p :=
      (QuotientGroup.eq_one_iff _).mp h1
    rw [← glbPrimeCore_subgroupOf p H] at h2
    exact h2
  have hd1 : Nat.card ↥(barM M L) ∣ Nat.card ↥L := Subgroup.card_dvd_of_surjective hρs
  have hd2 : Nat.card ↥L ∣ Nat.card ↥(GLBPrimeCore p H) := Subgroup.card_dvd_of_le hLN
  intro hpd
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (glbPrimeCore_coprime p H) dvd_rfl
    (hpd.trans (hd1.trans hd2)))

end CFSG.LocalAnalysis.RankThreeTheoremC
