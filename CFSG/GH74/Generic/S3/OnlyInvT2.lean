module

public import CFSG.GH74.Generic.S3.OnlyInvT1
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsRootCenter

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp BenderSuzuki.MatrixGroups
open CFSG.GorensteinWalter

section Core

variable {F : Type} [Field F] [Finite F] {r φ : ℕ} [Fact r.Prime]

theorem false_of_cover_in_psl2 (hF : Nat.card F = r ^ φ) (hr2 : r ≠ 2)
    {H : Subgroup (PSL2MatrixGroup F)} {K₀ : Type} [Group K₀] {p f : ℕ}
    (hc : IsL3Cover ↥H K₀ p f) : False := by
  have hsolv := hc.not_isSolvable
  obtain ⟨π, hπ, hker⟩ := hc.cover
  obtain ⟨hK124, hKle, hKdvd⟩ := hc.card_bounds
  have hle : Nat.card K₀ ≤ Nat.card H := hc.card_le
  have hsolvH : Group.IsSolvable ↥H → False := fun hH => by
    have := hH
    exact hsolv (Group.isSolvable_of_surjective hπ)
  have hr1 := (Fact.out : r.Prime)
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    simp at h1
  rcases dickson_psl2_subgroup_list hF H with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨ed⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, hm1, hmf, ht1, ht2, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, hfaith, ψ, hψ,
        ⟨eS⟩⟩ | ⟨m, hmf, ⟨eL⟩⟩ | ⟨m, hmf, ⟨eG⟩⟩
  ·
    exact hsolvH (Group.isSolvable_of_comm fun a b => hel.toIsMulCommutative.is_comm.comm a b)
  ·
    exact hsolvH (Group.isSolvable_of_comm fun a b => hcyc.commGroup.mul_comm a b)
  ·
    have : NeZero z := ⟨by omega⟩
    have : Group.IsSolvable (DihedralGroup z) :=
      CFSG.ProperTwoGeneratedCore.UnitaryKernels.isSolvable_dihedralGroup z
    exact hsolvH (Group.isSolvable_of_surjective (f := ed.symm.toMonoidHom) ed.symm.surjective)
  ·
    have := Nat.card_congr eA4.toEquiv
    rw [card_alternatingFour'] at this
    omega
  ·
    have := Nat.card_congr eS4.toEquiv
    rw [card_permFour] at this
    omega
  ·
    have := Nat.card_congr eA5.toEquiv
    rw [card_alternatingFive'] at this
    omega
  ·
    have hEn : E.Normal := hE
    have hEcomm : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.toIsMulCommutative.is_comm.comm a b
    have : Group.IsSolvable ↥E := Group.isSolvable_of_comm hEcomm
    have hq : ∀ a b : ↥H ⧸ E, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with | H a' => ?_
      induction b using QuotientGroup.induction_on with | H b' => ?_
      have hmem := overgroup_comm_mem E C hCcyc hsup b'⁻¹ a'⁻¹
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : (a' * b')⁻¹ * (b' * a') = b'⁻¹ * a'⁻¹ * b'⁻¹⁻¹ * a'⁻¹⁻¹ := by group
      rw [e]
      exact hmem
    have : Group.IsSolvable (↥H ⧸ E) := Group.isSolvable_of_comm hq
    refine hsolvH (Group.isSolvable_of_ker_le_range E.subtype (QuotientGroup.mk' E) ?_)
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hφ0 (zero_dvd_iff.1 hmf)
    have hcardH : Nat.card H = r ^ m * (r ^ (2 * m) - 1) / 2 := by
      rw [Nat.card_congr eL.toEquiv]
      exact card_psl2_galoisField hr2 hm0
    have hm3 : 3 ≤ r ^ m := by
      have h1 : 3 ≤ r := by
        have := hr1.two_le
        omega
      calc 3 ≤ r := h1
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ m := Nat.pow_le_pow_right hr1.pos (by omega)
    have hsq : r ^ (2 * m) = (r ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    by_cases h4 : 4 ≤ r ^ m
    · have hsimple : IsSimpleGroup ↥H := by
        have : IsSimpleGroup (PSL2MatrixGroup (GaloisField r m)) :=
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
            (by rw [GaloisField.card r m hm0]; exact h4)
        exact eL.isSimpleGroup
      have hcenH : Subgroup.center ↥H = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥H) with h0 | h1
        · exact h0
        · exfalso
          have hcomm : ∀ a b : ↥H, a * b = b * a := fun a b => by
            have : a ∈ Subgroup.center ↥H := by rw [h1]; exact Subgroup.mem_top a
            exact (Subgroup.mem_center_iff.1 this b).symm
          exact hsolv (by
            have := hc.simple
            have hKc : ∀ a b : K₀, a * b = b * a := by
              intro a b
              obtain ⟨a', rfl⟩ := hπ a
              obtain ⟨b', rfl⟩ := hπ b
              rw [← map_mul, ← map_mul, hcomm]
            exact IsSimpleGroup.comm_iff_isSolvable.1 hKc)
      have hπinj : Function.Injective π :=
        (MonoidHom.ker_eq_bot_iff π).1 (eq_bot_iff.2 (hker.trans hcenH.le))
      have hcard : Nat.card H = Nat.card K₀ :=
        Nat.card_congr (Equiv.ofBijective π ⟨hπinj, hπ⟩)
      have hq' : Odd (r ^ m) := (hr1.odd_of_ne_two hr2).pow
      have hord : CFSG.Open.ordA 1 (r ^ m) = Nat.card K₀ := by
        have h2 := L3Ord.two_mul_ordA_one hq'
        rw [← hcard, hcardH, hsq]
        omega
      exact L3Ord.ordA_one_ne hc.prime hc.ne_two hc.big hKle (by omega) hKdvd hq' hord
    · have h3 : r ^ m = 3 := by omega
      have : Nat.card H = 12 := by
        rw [hcardH, hsq, h3]
        norm_num
      omega
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hφ0 (zero_dvd_iff.1 (by simpa using hmf))
    have hperf : Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 2) (GaloisField r m)) := by
      have := hc.perfect
      exact Group.IsPerfect.ofSurjective (f := eG.toMonoidHom) eG.surjective
    have hcomm := pgl2_commutator_le_psl2_range (GaloisField r m)
    rw [hperf.commutator_eq_top] at hcomm
    have hrange : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := GaloisField r m)).range = ⊤ := top_le_iff.1 hcomm
    have h1 : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField r m)) ≤
        Nat.card (PSL2MatrixGroup (GaloisField r m)) := by
      have := Nat.card_le_card_of_surjective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField r m)).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
      rwa [hrange, Subgroup.card_top] at this
    rw [card_pgl2_galoisField hm0, card_psl2_galoisField hr2 hm0] at h1
    have hm3 : 3 ≤ r ^ m := by
      have h1 : 3 ≤ r := by
        have := hr1.two_le
        omega
      calc 3 ≤ r := h1
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ m := Nat.pow_le_pow_right hr1.pos (by omega)
    have hpos : 0 < r ^ m * (r ^ (2 * m) - 1) := by
      have : 9 ≤ r ^ (2 * m) := by
        rw [show r ^ (2 * m) = (r ^ m) ^ 2 by rw [← pow_mul, mul_comm]]
        nlinarith
      exact Nat.mul_pos (by omega) (by omega)
    have := Nat.div_lt_self hpos (by norm_num : 1 < 2)
    omega

theorem false_of_cover_hom_psl2 (hF : Nat.card F = r ^ φ)
    (hr2 : r ≠ 2) {B : Type} [Group B] [Finite B] {K₀ : Type} [Group K₀] {p f : ℕ}
    (hc : IsL3Cover B K₀ p f) (ρ : B →* PSL2MatrixGroup F) (hker : ρ.ker ≤ Subgroup.center B) :
    False := by
  obtain ⟨π, hπ, hkerπ⟩ := hc.cover
  have hle : ρ.rangeRestrict.ker ≤ π.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker.trans (hc.center_le_ker π hπ)
  obtain ⟨π', hπ'⟩ := exists_factor_of_ker_le ρ.rangeRestrict ρ.rangeRestrict_surjective π hle
  have hperf : Group.IsPerfect ↥ρ.range := by
    have := hc.perfect
    exact Group.IsPerfect.range ρ
  refine false_of_cover_in_psl2 hF hr2 (H := ρ.range)
    ⟨hc.prime, hc.ne_two, hc.big, hperf, hc.model, π', ?_, ?_⟩
  · intro k
    obtain ⟨b, rfl⟩ := hπ k
    exact ⟨ρ.rangeRestrict b, by rw [hπ']⟩
  · intro h hh
    rw [MonoidHom.mem_ker] at hh
    obtain ⟨b, rfl⟩ := ρ.rangeRestrict_surjective h
    have hb : b ∈ π.ker := by rw [MonoidHom.mem_ker, ← hπ']; exact hh
    have hbc : b ∈ Subgroup.center B := hkerπ hb
    rw [Subgroup.mem_center_iff] at hbc ⊢
    intro c
    obtain ⟨c', rfl⟩ := ρ.rangeRestrict_surjective c
    rw [← map_mul, ← map_mul, hbc c']

theorem false_of_cover_psl2 (hF : Nat.card F = r ^ φ) (hr2 : r ≠ 2)
    {L : Type} [Group L] [Finite L] (e : L ≃* PSL2MatrixGroup F) {A : Subgroup L} {K₀ : Type}
    [Group K₀] {p f : ℕ} (hc : IsL3Cover ↥A K₀ p f) : False := by
  refine false_of_cover_hom_psl2 hF hr2 hc (e.toMonoidHom.comp A.subtype) ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (e.injective.comp A.subtype_injective)]
  exact bot_le

theorem false_of_cover_sl2 (hF : Nat.card F = r ^ φ) (hr2 : r ≠ 2)
    {L : Type} [Group L] [Finite L] (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {A : Subgroup L} {K₀ : Type} [Group K₀] {p f : ℕ}
    (hc : IsL3Cover ↥A K₀ p f) : False := by
  let ρ : ↥A →* PSL2MatrixGroup F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
      (e.toMonoidHom.comp A.subtype)
  refine false_of_cover_hom_psl2 hF hr2 hc ρ ?_
  intro a ha
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at ha
  rw [Subgroup.mem_center_iff]
  intro b
  apply Subtype.ext
  apply e.injective
  have := Subgroup.mem_center_iff.1 ha (e b)
  simpa using this

end Core

end CFSG.GH74.Generic.S3
