module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I91

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem inf_cs_le_of_glaPComponent {p : ℕ} {B X D J : Subgroup Ω}
    (hJ : GLAPComponent p (X ⊓ cs D) J) (hDJ : D = B ⊓ cs J) : B ⊓ cs X ≤ D := by
  have hJX : J ≤ X := hJ.1.trans inf_le_left
  rw [hDJ]
  exact inf_le_inf_left B (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hJX))

theorem exists_mem_notMem_cs {p : ℕ} {B X D : Subgroup Ω} (hp : p.Prime) (hD : IsE2 p B D)
    (hcard : Nat.card ↥(B ⊓ cs X) = p) : ∃ x ∈ D, x ∉ cs X := by
  by_contra hcon
  have hle : D ≤ B ⊓ cs X := fun x hx =>
    ⟨hD.1 hx, by_contra fun h => hcon ⟨x, hx, h⟩⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [hD.2.2, hcard] at h1
  have h2 := hp.two_le
  nlinarith

theorem eq_sup_zpowers_of_notMem_cs {p : ℕ} {B X D : Subgroup Ω} {x : Ω} (hp : p.Prime)
    (hD : IsE2 p B D) (hcard : Nat.card ↥(B ⊓ cs X) = p) (hCD : B ⊓ cs X ≤ D) (hxD : x ∈ D)
    (hxc : x ∉ cs X) : D = (B ⊓ cs X) ⊔ Subgroup.zpowers x := by
  have hCS : B ⊓ cs X ≤ (B ⊓ cs X) ⊔ Subgroup.zpowers x := le_sup_left
  have hSD : (B ⊓ cs X) ⊔ Subgroup.zpowers x ≤ D := sup_le hCD (Subgroup.zpowers_le.2 hxD)
  have hxS : x ∈ (B ⊓ cs X) ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hd1 := Subgroup.card_dvd_of_le hCS
  have hd2 : Nat.card ↥((B ⊓ cs X) ⊔ Subgroup.zpowers x) ∣ p ^ 2 :=
    hD.2.2 ▸ Subgroup.card_dvd_of_le hSD
  obtain ⟨k, hk, hSk⟩ := (Nat.dvd_prime_pow hp).1 hd2
  rw [hcard, hSk] at hd1
  interval_cases k
  · exact absurd (Nat.le_of_dvd one_pos (by simpa using hd1)) (by have := hp.two_le; omega)
  · have hCS' : B ⊓ cs X = (B ⊓ cs X) ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hCS (by rw [hcard, hSk]; simp)
    exact absurd (hCS' ▸ hxS : x ∈ B ⊓ cs X).2 hxc
  · exact (Subgroup.eq_of_le_of_card_ge hSD (by rw [hD.2.2, hSk])).symm

theorem glaPComponent_inf_cx_of_eq_sup {p : ℕ} {B X D J : Subgroup Ω} {x : Ω}
    (hD : D = (B ⊓ cs X) ⊔ Subgroup.zpowers x) (hJ : GLAPComponent p (X ⊓ cs D) J) :
    GLAPComponent p (X ⊓ cx x) J := by
  have hxD : x ∈ D := hD ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have h : X ⊓ cs D = X ⊓ cx x := by
    apply le_antisymm
    · exact inf_le_inf_left X (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD))
    · intro g hg
      refine Subgroup.mem_inf.2 ⟨hg.1, ?_⟩
      have hDg : D ≤ Subgroup.centralizer ({g} : Set Ω) := by
        rw [hD]
        refine sup_le ?_ ?_
        · intro c hc
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hc.2 g hg.1).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hg.2).symm
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.1 (hDg hd)
  rw [h] at hJ
  exact hJ

theorem notMem_cs_of_fieldOn {p : ℕ} {d : Ω} {X : Subgroup Ω} (hp : p.Prime) (h : FieldOn p d X) :
    d ∉ cs X := by
  intro hc
  obtain ⟨-, lab, -, R, _, I, F, θ, -, -, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists h.2
  obtain ⟨-, f, -, u, -, hord, hind⟩ := hP
  have key : ∀ l : PQuot p X,
      (u * f * u⁻¹) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l) := by
    intro l
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective l
    refine hind _ _ ⟨a, a, rfl, rfl, ?_⟩
    have hac : (a : Ω) * d = d * (a : Ω) := Subgroup.mem_centralizer_iff.1 hc (a : Ω) a.2
    rw [mul_assoc, hac, inv_mul_cancel_left]
  have h1 : u * f * u⁻¹ = 1 := by
    refine MulEquiv.ext fun r => ?_
    obtain ⟨s, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective s
    simpa using key l
  have hf1 : f = 1 := by simpa using h1
  rw [hf1, orderOf_one] at hord
  exact hp.one_lt.ne hord

theorem glaPComponent_self_of_nontrivial {p : ℕ} {X : Subgroup Ω} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hnt : Nontrivial (PSimple p X)) : GLAPComponent p X X := by
  have hOne : GLAPPrimeCore p ↥X ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PQuot p X) := by
      show Subsingleton (↥X ⧸ GLAPPrimeCore p ↥X)
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hsub2 : Subsingleton (PSimple p X) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p X))).subsingleton
    exact (not_subsingleton_iff_nontrivial.2 hnt) hsub2
  have hOZ : GLAPPrimeCore p ↥X ≤ Subgroup.center ↥X :=
    le_center_of_normal_of_isQuasisimple hX (GLAPPrimeCore.normal p ↥X) hOne
  have hQ : CFSG.Open.IsQuasisimple (↥X ⧸ GLAPPrimeCore p ↥X) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient hX _ hOZ
  obtain ⟨I, hI, hbar⟩ := exists_glaPComponent_of_isQuasisimple hQ
  have hIX : I = X := S12.eq_of_barX_top_of_central hX hOZ hI.1 hbar
  rw [hIX] at hI
  exact hI

section I91


theorem fieldOn_or_triality_of_not_innDiagOn {p : ℕ} {X : Subgroup Ω} {x : Ω} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : CFSG.Open.IsQuasisimple ↥X) (hchev : IsChevSimple 2 (PSimple p X))
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxp : x ^ p = 1)
    (hnon : ¬ InnDiagOn p (Subgroup.zpowers x) X) :
    FieldOn p x X ∨ (p = 3 ∧ (catalogIs (PSimple 3 X) isD4any ∨ IsTD4 3 X)) := by
  have hnt : Nontrivial (PSimple p X) := by
    rcases CFSG.StandardType.ChevTwo.chevTwo_cases hchev with ⟨t, n, f, hm⟩ | he | h33
    · exact (CFSG.LieType.Catalog.lieModel_finite_simple _ t n 2 f hm).2.1
    · obtain ⟨e⟩ := he
      haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      haveI := e.isSimpleGroup
      infer_instance
    · exact (CFSG.LieType.Catalog.lieModel_finite_simple _ .PSU 3 3 1
        (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], h33⟩)).2.1
  exact i91_holds Ω p hp hp2 X X x (glaPComponent_self_of_nontrivial hX hnt) hchev hxN hxp
    ⟨hxN, hnon⟩

end I91

end CFSG.LocalAnalysis.GLTheoremA.I167

end
