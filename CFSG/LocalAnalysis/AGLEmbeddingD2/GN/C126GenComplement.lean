module

public import CFSG.Quasithin.Background.B6Sections
import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {X : Type*} [Group X] [Finite X]

theorem eq_bot_of_abelian_complement {T M R L C : Subgroup X}
    (h : MinParabolic (⊤ : Subgroup X) T M) [R.Normal] [IsMulCommutative R]
    (hRodd : Odd (Nat.card R)) (hRM : R ≤ M) (hLn : L.Normal) (hX : L ⊔ T = ⊤)
    (hRC : R ⊓ C = ⊥) (hL : R ⊔ C = L) : R = ⊥ := by
  by_contra hRne
  have hq : IsPGroup 2 (X ⧸ L) := by
    refine h.isSylow.2.1.of_surjective ((QuotientGroup.mk' L).comp T.subtype) fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ L ⊔ T := hX ▸ Subgroup.mem_top x
    obtain ⟨l, hl, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    refine ⟨⟨t, ht⟩, ?_⟩
    simp [(QuotientGroup.eq_one_iff l).2 hl]
  obtain ⟨k, hk⟩ := hq.exists_card_eq
  have hcop : Nat.Coprime L.index (Nat.card R) := by
    rw [Subgroup.index, hk]
    exact (Nat.coprime_two_left.2 hRodd).pow_left k
  obtain ⟨D, hcompl, hRD, hRD'⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting R L C hcop hRC hL
  have hodd : ¬ 2 ∣ D.relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right, hcompl.index_eq_card]
    exact Nat.prime_two.coprime_iff_not_dvd.1 (Nat.coprime_two_left.2 hRodd)
  obtain ⟨g, -, hg⟩ := B6.exists_conj_le_of_odd_relIndex h.isSylow le_top hodd
  have hTD' : T ≤ B6.conjSub g⁻¹ D := by
    have := (B6.conjSub g⁻¹).le_iff_le.mpr hg
    rwa [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at this
  have hRN : ∀ x : X, x ∈ Subgroup.normalizer (R : Set X) := fun x =>
    (Subgroup.normalizer_eq_top_iff.2 inferInstance : Subgroup.normalizer (R : Set X) = ⊤) ▸
      Subgroup.mem_top x
  have hD'top : B6.conjSub g⁻¹ D ≠ ⊤ := by
    intro htop
    apply hRne
    have hD : D = ⊤ := by
      have := congrArg (B6.conjSub g) htop
      rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one, OrderIso.map_top] at this
    rw [← inf_top_eq R, ← hD, hRD]
  have hD'M : B6.conjSub g⁻¹ D ≤ M := h.le_of_lt hTD' (lt_top_iff_ne_top.2 hD'top)
  have hsup : R ⊔ B6.conjSub g⁻¹ D = ⊤ := by
    have := congrArg (B6.conjSub g⁻¹) hRD'
    rwa [OrderIso.map_sup, OrderIso.map_top, B6.conjSub_eq_self (hRN g⁻¹)] at this
  have hXM : (⊤ : Subgroup X) ≤ M := hsup ▸ sup_le hRM hD'M
  exact absurd (lt_of_le_of_lt hXM h.maximal.1) (lt_irrefl _)

theorem eq_bot_of_solvable_complement {T M R L C : Subgroup X}
    (h : MinParabolic (⊤ : Subgroup X) T M) [R.Normal] (hRs : Group.IsSolvable R)
    (hRodd : Odd (Nat.card R)) (hRM : R ≤ M) (hLn : L.Normal) (hX : L ⊔ T = ⊤)
    (hRC : R ⊓ C = ⊥) (hL : R ⊔ C = L) : R = ⊥ := by
  by_contra hRne
  have hRR : ⁅R, R⁆ < R := by
    refine lt_of_le_of_ne (Subgroup.commutator_le_self R) fun heq => ?_
    have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.2 heq
    have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).2 hRne
    exact Group.IsPerfect.not_isSolvable ↥R hRs
  have hR'n : (⁅R, R⁆ : Subgroup X).Normal := Subgroup.commutator_normal R R
  set π := QuotientGroup.mk' (⁅R, R⁆ : Subgroup X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ M := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Subgroup.commutator_le_self R).trans hRM
  have hbar := h.map_of_surjective hπs hker
  have hRab : IsMulCommutative (R.map π) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    refine Subtype.ext ?_
    show (a : X ⧸ ⁅R, R⁆) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hc := Subgroup.commutator_mem_commutator (R.inv_mem hb') (R.inv_mem ha')
    rw [commutatorElement_def] at hc
    convert hc using 1
    group
  have hRodd' : Odd (Nat.card (R.map π)) := hRodd.of_dvd_nat (Subgroup.card_map_dvd R π)
  have hRne' : R.map π ≠ ⊥ := by
    intro h0
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h0
    exact absurd (lt_of_lt_of_le hRR h0) (lt_irrefl _)
  have hRn' : (R.map π).Normal := ‹R.Normal›.map π hπs
  have hLn' : (L.map π).Normal := hLn.map π hπs
  have hX' : L.map π ⊔ T.map π = ⊤ := by
    rw [← Subgroup.map_sup, hX, Subgroup.map_top, MonoidHom.range_eq_top.2 hπs]
  have hRC' : R.map π ⊓ C.map π = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨⟨r, hr, rfl⟩, ⟨c, hc, hcr⟩⟩ := hy
    have hmem : c⁻¹ * r ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcr, inv_mul_cancel]
    have hcR : c ∈ R := by
      have h1 : c⁻¹ * r ∈ R := (Subgroup.commutator_le_self R)
        (by rwa [hπ, QuotientGroup.ker_mk'] at hmem)
      have := R.mul_mem hr (R.inv_mem h1)
      simpa using this
    have hc1 : c ∈ R ⊓ C := ⟨hcR, hc⟩
    rw [hRC, Subgroup.mem_bot] at hc1
    rw [Subgroup.mem_bot, ← hcr, hc1, map_one]
  have hL' : R.map π ⊔ C.map π = L.map π := by rw [← Subgroup.map_sup, hL]
  exact hRne' (eq_bot_of_abelian_complement hbar hRodd' (Subgroup.map_mono hRM) hLn' hX' hRC' hL')

end CFSG.AGLEmbeddingD2.GN
