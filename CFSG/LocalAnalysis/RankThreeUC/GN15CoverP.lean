module

public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverStep

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem eq_three_of_dvd_relIndex_of_pow_mem {p : ℕ} (hp : p.Prime) {A D : Subgroup X}
    (hD : D.Normal) (h3 : ∀ a ∈ A, ∃ k : ℕ, a ^ 3 ^ k ∈ D) (hpd : p ∣ D.relIndex A) : p = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (D.subgroupOf A).Normal := hD.subgroupOf A
  have hpg : IsPGroup 3 (↥A ⧸ D.subgroupOf A) := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h3 a.1 a.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  have hcard : Nat.card (↥A ⧸ D.subgroupOf A) = D.relIndex A := by
    rw [← Subgroup.index_eq_card]; rfl
  rw [hcard] at hn
  rw [hn] at hpd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hpd)

theorem gnCoverP_of_JOutCentralAt (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral)
    (hJ : JOutCentralAt T) (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) :
    GNCoverP T T₁ T₂ := by
  intro p hp hp2 A B hA hB hCB hBA hAL hpd
  induction A using WellFoundedLT.induction with
  | _ A ih =>
    rcases eq_or_lt_of_le hBA with hAB | hlt
    · exfalso
      subst hAB
      rw [Subgroup.relIndex_self] at hpd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpd)
    · obtain ⟨D, hBD, hmax⟩ :=
        (Set.toFinite {K : Subgroup X | K.Normal ∧ B ≤ K ∧ K < A}).exists_le_maximal
          ⟨hB, le_rfl, hlt⟩
      obtain ⟨hDn, -, hDA⟩ := hmax.1
      have hchief : ∀ E : Subgroup X, E.Normal → D ≤ E → E ≤ A → E = D ∨ E = A := by
        intro E hE hDE hEA
        by_cases hEA' : E = A
        · exact Or.inr hEA'
        · exact Or.inl (le_antisymm (hmax.2 ⟨hE, hBD.trans hDE, lt_of_le_of_ne hEA hEA'⟩ hDE) hDE)
      have hmul : B.relIndex D * D.relIndex A = B.relIndex A :=
        Subgroup.relIndex_mul_relIndex B D A hBD hDA.le
      rw [← hmul] at hpd
      rcases (Nat.Prime.dvd_mul hp).1 hpd with hpd₁ | hpd₂
      ·
        obtain ⟨x, hxD, hrest⟩ :=
          ih D hDA hDn hBD ((inf_le_inf_right _ hDA.le).trans hAL) hpd₁
        exact ⟨x, hDA.le hxD, hrest⟩
      ·
        have hCD : gnC T ≤ D := hCB.trans hBD
        have hAD : A ⊓ gnDPre T ≤ D :=
          (inf_le_inf_left A gnDPre_le_gnLayerPre_cover).trans (hAL.trans hBD)
        rcases cover_cases_of_chief hI59 hJ3 hJ hX hP hA hDn hDA.le hCD hAD hchief with
          h | h | ⟨h3, x, hxA, hxD, hxo, hxc⟩
        · obtain ⟨x, hx, hxD, hxo⟩ := exists_pElement_of_cover hp hDn h hpd₂
          exact ⟨x, hx.1, fun hxB => hxD (hBD hxB), hxo, Or.inl hx.2⟩
        · obtain ⟨x, hx, hxD, hxo⟩ := exists_pElement_of_cover hp hDn h hpd₂
          exact ⟨x, hx.1, fun hxB => hxD (hBD hxB), hxo, Or.inr hx.2⟩
        · have hp3 : p = 3 := eq_three_of_dvd_relIndex_of_pow_mem hp hDn h3 hpd₂
          subst hp3
          exact ⟨x, hxA, fun hxB => hxD (hBD hxB), hxo, hxc⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
