module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5FieldPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5FieldCentre

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Field

theorem exists_ne_one_of_card_ne_one {K : Type} [Group K] [Finite K] {A : Subgroup K}
    (h : Nat.card A ≠ 1) : ∃ x ∈ A, x ≠ 1 := by
  by_contra hno
  apply h
  have hA : A = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact hno ⟨x, hx, hx1⟩
  rw [hA, Subgroup.card_bot]

theorem card_eq_three_of_ne_bot {K : Type} [Group K] [Finite K] {F : Subgroup K}
    (hFel : IsElemAbelian 3 F) (hFle : Nat.card F ≤ 3) (hF : F ≠ ⊥) : Nat.card F = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : Nat.card F ≠ 1 := by
    intro h1
    exact hF (Subgroup.eq_bot_of_card_eq F h1)
  obtain ⟨x, hxF, hx1⟩ := exists_ne_one_of_card_ne_one hne
  have hx3 : x ^ 3 = 1 := hFel.2 x hxF
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd : orderOf (⟨x, hxF⟩ : F) ∣ Nat.card F := orderOf_dvd_natCard _
  have hord' : orderOf (⟨x, hxF⟩ : F) = 3 := by
    rw [Subgroup.orderOf_mk, hord]
  rw [hord'] at hdvd
  have hpos : 0 < Nat.card F := Nat.card_pos
  omega

theorem pRank_center_le_of_surjective {L K : Type} [Group L] [Group K] [Finite L] [Finite K]
    [Group.IsPerfect L] [IsCyclic (Subgroup.center L)] [IsCyclic (Subgroup.center K)]
    (π : L →* K) (hs : Function.Surjective π) (hk : ∀ x : L, π x = 1 → x ∈ Subgroup.center L) :
    CFSG.Open.pRank 3 (Subgroup.center K) ≤ CFSG.Open.pRank 3 (Subgroup.center L) := by
  have hr1 : CFSG.Open.pRank 3 (Subgroup.center K) ≤ 1 := pRank_three_le_one_of_isCyclic _
  rcases Nat.eq_zero_or_pos (CFSG.Open.pRank 3 (Subgroup.center K)) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · obtain ⟨A, hAZ, hAel, hAcard⟩ := exists_card_pRank_three (Subgroup.center K)
    have h3A : 3 ∣ Nat.card A := by
      rw [hAcard]
      exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hpos)
    have h3K : 3 ∣ Nat.card (Subgroup.center K) :=
      dvd_trans h3A (Subgroup.card_dvd_of_le hAZ)
    have hsurjc : Function.Surjective (centerMap π hs hk) := centerMap_surjective π hs hk
    have hdiv : Nat.card (Subgroup.center K) ∣ Nat.card (Subgroup.center L) :=
      Subgroup.card_dvd_of_surjective hsurjc
    have h3L : 3 ∣ Nat.card (Subgroup.center L) := dvd_trans h3K hdiv
    have hm1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.center L) :=
      one_le_pRank_three_of_three_dvd _ h3L
    omega


theorem kd264I5Field_of_pieces (hC : KD264I5CoverLift) (hU : KD264I5Universal) :
    KD264I5Field := by
  intro K _ _ hK e k hb hiso β hβ3 hβout
  obtain ⟨L, _, _, π, βL, hs, hk, hLu, hβL3, hcomm⟩ := hC e k hb K hK hiso β hβ3 hβout
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr hLu.1.1
  have hLcyc : IsCyclic (Subgroup.center L) := hLu.2.2.1
  obtain ⟨θ, hθ⟩ := exists_quotient_equiv π hs hk
  have hβLout : onCenterQuotient βL ∉ innAutDerived (L ⧸ Subgroup.center L) := by
    intro hmem
    apply hβout
    rw [← congr_onCenterQuotient θ π βL β hθ hcomm]
    exact (mem_innAutDerived_congr θ).mpr hmem
  obtain ⟨E, hEfix, hEel, hEkm⟩ := hU e k hb L hLu βL hβL3 hβLout
  obtain ⟨E₀, hE₀E, hE₀el, hE₀card⟩ := exists_card_pRank_three E
  have hE₀fix : ∀ x ∈ E₀, βL x = x := fun x hx => hEfix (hE₀E hx)
  haveI hKcyc : IsCyclic (Subgroup.center K) := isCyclic_center_of_surjective π hs hk
  have hr1 : CFSG.Open.pRank 3 (Subgroup.center K) ≤ 1 := pRank_three_le_one_of_isCyclic _
  have hrm : CFSG.Open.pRank 3 (Subgroup.center K) ≤ CFSG.Open.pRank 3 (Subgroup.center L) :=
    pRank_center_le_of_surjective π hs hk
  have hFle : E₀ ⊓ π.ker ≤ Subgroup.center L := fun x hx =>
    hk x (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hx).2)
  have hFel : IsElemAbelian 3 (E₀ ⊓ π.ker) := isElemAbelian_mono hE₀el inf_le_left
  have hFcard_le : Nat.card ↥(E₀ ⊓ π.ker) ≤ 3 := card_le_three_of_isElemAbelian_le hFle hFel
  have hE₁el : IsElemAbelian 3 (E₀.map π) := I5Field.isElemAbelian_map hE₀el π
  have hE₁fix : E₀.map π ≤ fixSubgroup β := by
    rintro _ ⟨x, hx, rfl⟩
    show β (π x) = π x
    rw [← hcomm x, hE₀fix x hx]
  have hsplit := card_map_mul_card_inf_ker π E₀
  rw [hE₀card] at hsplit
  by_cases hF : E₀ ⊓ π.ker = ⊥
  ·
    rw [hF, Subgroup.card_bot, mul_one] at hsplit
    refine ⟨E₀.map π, hE₁fix, hE₁el, ?_⟩
    have hle := le_pRank_three_of_card (le_refl (E₀.map π)) hE₁el
      (m := CFSG.Open.pRank 3 E) hsplit
    omega
  ·
    have hFcard : Nat.card ↥(E₀ ⊓ π.ker) = 3 := card_eq_three_of_ne_bot hFel hFcard_le hF
    have h3L : 3 ∣ Nat.card ↥(Subgroup.center L) := by
      rw [← hFcard]
      exact Subgroup.card_dvd_of_le hFle
    have hm1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.center L) :=
      one_le_pRank_three_of_three_dvd _ h3L
    obtain ⟨q, hq⟩ : ∃ q, CFSG.Open.pRank 3 E = q + 1 := ⟨CFSG.Open.pRank 3 E - 1, by omega⟩
    have hcardE₁ : Nat.card ↥(E₀.map π) = 3 ^ q := by
      rw [hFcard, hq, pow_succ] at hsplit
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) hsplit
    rcases Nat.lt_or_ge (CFSG.Open.pRank 3 (Subgroup.center K)) 1 with hr0 | hr1'
    ·
      refine ⟨E₀.map π, hE₁fix, hE₁el, ?_⟩
      have hle := le_pRank_three_of_card (le_refl (E₀.map π)) hE₁el (m := q) hcardE₁
      omega
    ·
      have hr : CFSG.Open.pRank 3 (Subgroup.center K) = 1 := by omega
      obtain ⟨A, hAZ, hAel, hAcard⟩ := exists_card_pRank_three (Subgroup.center K)
      rw [hr] at hAcard
      obtain ⟨z, hzA, hz1⟩ := exists_ne_one_of_card_ne_one (A := A) (by rw [hAcard]; norm_num)
      have hzc : z ∈ Subgroup.center K := hAZ hzA
      have hz3 : z ^ 3 = 1 := hAel.2 z hzA
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
      have hzE₁ : z ∉ E₀.map π := by
        rintro ⟨x, hx, hxz⟩
        have hxL : x ∈ Subgroup.center L := (mem_center_iff_of_surjective_ker π hs hk x).mp
          (hxz ▸ hzc)
        have hx3 : x ^ 3 = 1 := hE₀el.2 x hx
        have hxF : x ∈ E₀ ⊓ π.ker :=
          mem_of_three_torsion_le hFle hFel hFcard hxL hx3
        have hπx : π x = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hxF).2
        rw [hπx] at hxz
        rw [← hxz] at hzord
        simp at hzord
      have hβz : β z = z := apply_eq_self_of_orderOf_three β hβ3 hzc hzord
      have hzfix : Subgroup.zpowers z ≤ fixSubgroup β := by
        rw [Subgroup.zpowers_le]
        exact hβz
      have hBnorm : Subgroup.zpowers z ≤
          Subgroup.normalizer ((E₀.map π : Subgroup K) : Set K) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
        intro h
        have e : z * h * z⁻¹ = h := by
          rw [← Subgroup.mem_center_iff.mp hzc h]
          group
        rw [e]
      have hinf : E₀.map π ⊓ Subgroup.zpowers z = ⊥ := by
        have hdvd : Nat.card ↥(E₀.map π ⊓ Subgroup.zpowers z) ∣ Nat.card ↥(Subgroup.zpowers z) :=
          Subgroup.card_dvd_of_le inf_le_right
        rw [Nat.card_zpowers, hzord] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          have heq : E₀.map π ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [Nat.card_zpowers, hzord, h3])
          have hzmem : z ∈ E₀.map π ⊓ Subgroup.zpowers z := by
            rw [heq]
            exact Subgroup.mem_zpowers z
          exact hzE₁ (Subgroup.mem_inf.mp hzmem).1
      have hcardE : Nat.card ↥(E₀.map π ⊔ Subgroup.zpowers z) = 3 ^ (q + 1) := by
        have hmul := card_sup_mul_card_inf_of_le_normalizer hBnorm
        rw [hinf, Subgroup.card_bot, mul_one, hcardE₁, Nat.card_zpowers, hzord] at hmul
        rw [hmul, pow_succ]
      have hEel : IsElemAbelian 3 (E₀.map π ⊔ Subgroup.zpowers z) :=
        I5Field.isElemAbelian_sup_zpowers hE₁el hzc hz3
      have hzfix' : Subgroup.zpowers z ≤ fixSubgroup β := hzfix
      refine ⟨E₀.map π ⊔ Subgroup.zpowers z, sup_le hE₁fix hzfix', hEel, ?_⟩
      have hle := le_pRank_three_of_card (le_refl (E₀.map π ⊔ Subgroup.zpowers z)) hEel
        (m := q + 1) hcardE
      omega
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
