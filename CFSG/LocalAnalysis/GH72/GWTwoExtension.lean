module

public import CFSG.LocalAnalysis.GH72.GWForm

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.GorensteinWalter (HasDihedralSylowTwo IsOddPrimePower PSL2 PGL2)

theorem card_psl2_galoisField {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hk : k ≠ 0) :
    Nat.card (PSL(2, GaloisField p k)) = p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
  rw [CFSG.GorensteinWalter.psl2_card_formula _
    ⟨p, k, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hk,
      GaloisField.card p k hk⟩, GaloisField.card p k hk]

theorem commutator_eq_top_of_isL2OrA7 {L : Type*} [Group L] {qmin : ℕ} (hq : 5 ≤ qmin)
    (h : IsL2OrA7 L qmin) : commutator L = ⊤ := by
  have key : ∀ {M : Type} [Group M], commutator M = ⊤ → ∀ e : L ≃* M, commutator L = ⊤ := by
    intro M _ hM e
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ commutator M := hM ▸ mem_top _
    rw [_root_.commutator_def] at hx ⊢
    have := Subgroup.mem_map_of_mem e.symm.toMonoidHom hx
    rw [map_commutator, map_top_of_surjective _ e.symm.surjective] at this
    simpa using this
  rcases h with ⟨⟨e⟩⟩ | ⟨p, k, _, hp2, hpk, ⟨e⟩⟩
  · exact key (commutator_alternatingGroup_eq_top (by simp)) e
  · have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hpk
      omega
    refine key (CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three _ ?_).commutator_eq_top e
    rw [GaloisField.card p k hk]
    omega

theorem isSimpleGroup_of_isL2OrA7 {L : Type*} [Group L] {qmin : ℕ} (hq : 5 ≤ qmin)
    (h : IsL2OrA7 L qmin) : IsSimpleGroup L := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, k, _, hp2, hpk, ⟨e⟩⟩
  · haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  · have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hpk
      omega
    haveI : IsSimpleGroup (PSL(2, GaloisField p k)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [GaloisField.card p k hk]; omega)
    exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance

theorem sixty_le_card_of_isL2OrA7 {L : Type*} [Group L] {qmin : ℕ} (hq : 5 ≤ qmin)
    (h : IsL2OrA7 L qmin) : 60 ≤ Nat.card L := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, k, _, hp2, hpk, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hpk
      omega
    rw [Nat.card_congr e.toEquiv, card_psl2_galoisField hp2 hk]
    set q := p ^ k
    have h5 : 5 ≤ q := le_trans hq hpk
    have h24 : 24 ≤ q ^ 2 - 1 := by
      have : 25 ≤ q ^ 2 := by nlinarith
      omega
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith

theorem le_of_commutator_eq_top_of_odd_index {X : Type*} [Group X] [Finite X] (M : Subgroup X)
    [M.Normal] (hM : Odd M.index) (F : Subgroup X) (hF : commutator F = ⊤) : F ≤ M := by
  have hsolv : Group.IsSolvable (X ⧸ M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hM
  set F' := F.map (QuotientGroup.mk' M)
  have hF' : ⁅F', F'⁆ = F' := by
    have h : (commutator F).map F.subtype = ⁅F, F⁆ := by
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [hF, ← MonoidHom.range_eq_map, range_subtype] at h
    rw [← map_commutator, ← h]
  have hbot : F' = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hF'
  intro x hx
  have h1 : QuotientGroup.mk' M x ∈ F' := mem_map_of_mem _ hx
  rw [hbot, mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

theorem gw_isL2OrA7_or_pgl2_of_isPGroup_quotient
    {L : Type} [Group L] [Finite L] (F : Subgroup L) [F.Normal] (hF : IsL2OrA7 F 5)
    (h2 : IsPGroup 2 (L ⧸ F)) (hD : HasDihedralSylowTwo L) :
    IsL2OrA7 L 5 ∨ ∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 5 ≤ p ^ k ∧
      Nonempty (L ≃* PGL2 (GaloisField p k)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFperf : commutator F = ⊤ := commutator_eq_top_of_isL2OrA7 le_rfl hF
  haveI hFsimp : IsSimpleGroup F := isSimpleGroup_of_isL2OrA7 le_rfl hF
  have hF60 : 60 ≤ Nat.card F := sixty_le_card_of_isL2OrA7 le_rfl hF
  have hFns : ¬ Group.IsSolvable F := by
    intro hs
    haveI : Group.IsPerfect F := ⟨hFperf⟩
    exact Group.IsPerfect.not_isSolvable F hs
  have hO : CFSG.oddCore L = ⊥ := by
    set O := CFSG.oddCore L
    have hOodd : Odd (Nat.card O) := CFSG.ABGDGroups.odd_card_oddCore L
    have hOF : Disjoint O F := by
      rw [← subgroupOf_eq_bot]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.subgroupOf F) with h | h
      · exact h
      · exfalso
        have hFO : F ≤ O := by
          intro x hx
          have : (⟨x, hx⟩ : F) ∈ O.subgroupOf F := h ▸ mem_top _
          exact this
        have hodd : Odd (Nat.card F) := Odd.of_dvd_nat hOodd (card_dvd_of_le hFO)
        exact hFns (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
    have hinj : Function.Injective ((QuotientGroup.mk' F).comp O.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact (mem_bot).2 (Subtype.ext ((disjoint_def.mp hOF) x.2 hx))
    have hO2 : IsPGroup 2 O := h2.of_injective _ hinj
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact (card_eq_one).mp hn
    · rw [hn, pow_succ] at hOodd
      exact absurd hOodd (Nat.not_odd_iff_even.mpr (even_two.mul_left _))
  rcases CFSG.QuasiDihedralFusion.gw_cases hD hO with hP | ⟨⟨e7⟩⟩ | ⟨K, _, _, hK, M, hMn, hModd, hM⟩
  · haveI : Group.IsNilpotent F := (hP.to_subgroup F).isNilpotent
    exact absurd (inferInstance : Group.IsSolvable F) hFns
  · exact Or.inl (Or.inl ⟨e7⟩)
  · haveI := hMn
    have hFM : F ≤ M := le_of_commutator_eq_top_of_odd_index M hModd F hFperf
    have hMtop : M = ⊤ := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h2
      have hdvd : M.index ∣ 2 ^ a := ha ▸ index_dvd_of_le hFM
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases b with _ | b
      · exact index_eq_one.mp (by rw [hb, pow_zero])
      · rw [hb, pow_succ] at hModd
        exact absurd hModd (Nat.not_odd_iff_even.mpr (even_two.mul_left _))
    let eM : L ≃* M := (MulEquiv.subgroupCongr hMtop.symm).symm.trans topEquiv |>.symm
    have hLF : Nat.card F ≤ Nat.card L := card_le_card_group F
    obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd hpodd (by decide)
    have hq5 : 5 ≤ p ^ n := by
      by_contra hlt
      have hq3 : Nat.card K = 3 := by
        have hodd : Odd (p ^ n) := hpodd.pow
        have hone : 1 < Nat.card K := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      have hL24 : Nat.card L ≤ 24 := by
        rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        · rw [Nat.card_congr (eM.trans e).toEquiv, CFSG.GorensteinWalter.psl2_card_formula K
            ⟨p, n, hp, hpodd, hn, hq⟩, hq3]
          norm_num
        · rw [Nat.card_congr (eM.trans e).toEquiv, CFSG.GorensteinWalter.pgl2_card_formula K,
            hq3]
          norm_num
      omega
    obtain ⟨eK⟩ := nonempty_ringEquiv_galoisField (p := p) (n := n) (by omega) hq
    rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl (Or.inr ⟨p, n, ⟨hp⟩, hp2, hq5,
        ⟨(eM.trans e).trans (CFSG.GorensteinWalter.psl2RingEquiv eK)⟩⟩)
    · exact Or.inr ⟨p, n, ⟨hp⟩, hp2, hq5,
        ⟨(eM.trans e).trans (CFSG.GorensteinWalter.pgl2RingEquiv eK)⟩⟩

theorem gw_isL2PGL2OrA7OrV4_of_isPGroup_quotient
    {L : Type} [Group L] [Finite L] (F : Subgroup L) [F.Normal] (hF : IsL2OrA7 F 5)
    (h2 : IsPGroup 2 (L ⧸ F)) (hD : HasDihedralSylowTwo L) : IsL2PGL2OrA7OrV4 L := by
  rcases gw_isL2OrA7_or_pgl2_of_isPGroup_quotient F hF h2 hD with h | ⟨p, k, hp, hp2, h5, e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨p, k, hp, hp2, by omega, e⟩)

end CFSG.GH72
