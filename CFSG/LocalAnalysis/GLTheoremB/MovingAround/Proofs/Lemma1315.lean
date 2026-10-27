module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1110

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

variable {G : Type} [Group G] [Finite G]

theorem mem_centerOf_iff' {R : Subgroup G} {z : G} :
    z ∈ centerOf R ↔ z ∈ R ∧ ∀ r ∈ R, r * z = z * r := by
  unfold centerOf
  constructor
  · intro hz
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hz
    refine ⟨t.2, fun r hr => ?_⟩
    have h := Subgroup.mem_center_iff.1 ht ⟨r, hr⟩
    exact congrArg Subtype.val h
  · rintro ⟨hzR, hc⟩
    refine Subgroup.mem_map.2 ⟨⟨z, hzR⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    rintro ⟨g, hg⟩
    exact Subtype.ext (hc g hg)

theorem conj_mem_omegaOne {p : ℕ} {R : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (R : Set G)) {n : G} (hn : n ∈ omegaOne p (centerOf R)) :
    y * n * y⁻¹ ∈ omegaOne p (centerOf R) := by
  have hy' : ∀ h : G, h ∈ R ↔ y * h * y⁻¹ ∈ R := fun h => Subgroup.mem_set_normalizer_iff.1 hy h
  have hS : ∀ s ∈ {x : G | x ∈ centerOf R ∧ x ^ p = 1},
      MulAut.conj y s ∈ {x : G | x ∈ centerOf R ∧ x ^ p = 1} := by
    rintro s ⟨hs, hsp⟩
    rw [mem_centerOf_iff'] at hs
    refine ⟨mem_centerOf_iff'.2 ⟨(hy' s).1 hs.1, fun r hr => ?_⟩, ?_⟩
    ·
      have hh : y⁻¹ * r * y ∈ R := (hy' _).2 (by simpa [mul_assoc] using hr)
      have hcomm : (y⁻¹ * r * y) * s = s * (y⁻¹ * r * y) := hs.2 _ hh
      show r * (y * s * y⁻¹) = (y * s * y⁻¹) * r
      calc r * (y * s * y⁻¹) = y * ((y⁻¹ * r * y) * s) * y⁻¹ := by group
        _ = y * (s * (y⁻¹ * r * y)) * y⁻¹ := by rw [hcomm]
        _ = (y * s * y⁻¹) * r := by group
    · show (y * s * y⁻¹) ^ p = 1
      rw [← MulAut.conj_apply, ← map_pow, hsp, map_one]
  have key : omegaOne p (centerOf R) ≤
      (omegaOne p (centerOf R)).comap (MulAut.conj y).toMonoidHom := by
    unfold omegaOne
    refine (Subgroup.closure_le _).2 ?_
    intro s hs
    exact Subgroup.mem_comap.2 (Subgroup.subset_closure (hS s hs))
  exact Subgroup.mem_comap.1 (key hn)

theorem mem_normalizer_omegaOne {p : ℕ} {R : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (R : Set G)) :
    y ∈ Subgroup.normalizer ((omegaOne p (centerOf R) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · exact conj_mem_omegaOne hy
  · intro hn
    have h := conj_mem_omegaOne (inv_mem hy) hn
    have e : y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n := by group
    rwa [e] at h

theorem sylow_of_central_rank_two {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsEkIn p 2 B U)
    (hUZ : U ≤ centerOf R) : IsSylowIn p ⊤ R := by
  have hβ : p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ m ≤ GLATwoLocalRank p G := h.standing.beta
  have hp : p.Prime := hβ.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBSC : IsSCp p ⊤ B := lemma23_proved G m p h.standing B h.bOne
  have hBR : B ≤ R := le_trans le_sup_right h.hR.2
  have hRM : IsSylowIn p M R := h.hR.1
  have hZB : omegaOne p (centerOf R) ≤ B := l1110_omegaOne_centerOf_le hBSC hBR
  have hUZ' : U ≤ omegaOne p (centerOf R) := fun u hu =>
    Subgroup.subset_closure ⟨hUZ hu, hU.2.1.2 u hu⟩
  have h2 : 2 ≤ CFSG.Open.pRank p (omegaOne p (centerOf R)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hUZ' hU.2.1 hU.2.2
  have hmemS : Subgroup.normalizer ((omegaOne p (centerOf R) : Subgroup G) : Set G) ∈
      {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ B ∧ 2 ≤ CFSG.Open.pRank p Q ∧
        N = Subgroup.normalizer (Q : Set G)} :=
    ⟨omegaOne p (centerOf R), hZB, h2, rfl⟩
  have hNZ : Subgroup.normalizer ((omegaOne p (centerOf R) : Subgroup G) : Set G) ≤ M :=
    le_trans (le_sSup hmemS) h.uniq.clause_d
  refine ⟨le_top, hRM.2.1, fun R' _ hR'p hRR' => ?_⟩
  by_contra hne
  have hlt : R < R' := lt_of_le_of_ne hRR' (Ne.symm hne)
  haveI : Group.IsNilpotent ↥R' := IsPGroup.isNilpotent hR'p
  have hKne : R.subgroupOf R' ≠ ⊤ := by
    intro hK
    apply hlt.ne'
    refine le_antisymm ?_ hlt.le
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥R') ∈ R.subgroupOf R' := by
      rw [hK]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem
  have hgrow : R.subgroupOf R' <
      Subgroup.normalizer ((R.subgroupOf R' : Subgroup ↥R') : Set ↥R') :=
    Group.normalizerCondition_of_isNilpotent (G := ↥R') (R.subgroupOf R') (lt_top_iff_ne_top.2 hKne)
  obtain ⟨-, x, hxN, hxK⟩ := SetLike.lt_iff_le_and_exists.1 hgrow
  have hxiff : ∀ k : ↥R', k ∈ R.subgroupOf R' ↔ x * k * x⁻¹ ∈ R.subgroupOf R' := fun k =>
    Subgroup.mem_set_normalizer_iff.1 hxN k
  set g : G := (x : G) with hg
  have hgR : g ∉ R := fun hgr => hxK (Subgroup.mem_subgroupOf.2 hgr)
  have hnorm : g ∈ Subgroup.normalizer (R : Set G) := by
    refine Subgroup.mem_set_normalizer_iff.2 (fun h => ⟨fun hh => ?_, fun hh => ?_⟩)
    · have hh' : h ∈ R' := hRR' hh
      exact Subgroup.mem_subgroupOf.1 ((hxiff ⟨h, hh'⟩).1 (Subgroup.mem_subgroupOf.2 hh))
    · have hgR' : g * h * g⁻¹ ∈ R' := hRR' hh
      have hh' : h ∈ R' := by
        have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [e]
        exact R'.mul_mem (R'.mul_mem (R'.inv_mem x.2) hgR') x.2
      exact Subgroup.mem_subgroupOf.1 ((hxiff ⟨h, hh'⟩).2 (Subgroup.mem_subgroupOf.2 hh))
  have hYM : Subgroup.normalizer (R : Set G) ⊓ R' ≤ M := fun y hy =>
    hNZ (mem_normalizer_omegaOne hy.1)
  have hYp : IsPGroup p ↥(Subgroup.normalizer (R : Set G) ⊓ R') :=
    IsPGroup.to_le hR'p inf_le_right
  have hRY : R ≤ Subgroup.normalizer (R : Set G) ⊓ R' :=
    le_inf Subgroup.le_normalizer hRR'
  have hY : Subgroup.normalizer (R : Set G) ⊓ R' = R := hRM.2.2 _ hYM hYp hRY
  have hgY : g ∈ Subgroup.normalizer (R : Set G) ⊓ R' := ⟨hnorm, x.2⟩
  rw [hY] at hgY
  exact hgR hgY

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315
