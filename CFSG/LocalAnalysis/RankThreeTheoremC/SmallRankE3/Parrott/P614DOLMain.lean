module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DeltaDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DOLModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open Subgroup
open scoped MatrixGroups

namespace P614DOL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

section Action

variable {X : Type*} [Group X] {N : Subgroup X} [N.Normal] {P : Type*} [Group P]

@[expose] def actHom (e : N ≃* P) : X →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem actHom_apply (e : N ≃* P) (x : X) (p : P) :
    actHom e x p = e (MulAut.conjNormal x (e.symm p)) :=
  rfl

theorem actHom_coe (e : N ≃* P) (n : N) : actHom e n = MulAut.conj (e n) := by
  ext p
  rw [actHom_apply, MulAut.conjNormal_val, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulEquiv.apply_symm_apply]

theorem actHom_injective (e : N ≃* P) (hC : centralizer (N : Set X) = ⊥) :
    Function.Injective (actHom e) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : x ∈ centralizer (N : Set X) := by
    rw [mem_centralizer_iff]
    intro n hn
    have h1 := congrArg (fun φ : MulAut P => e.symm (φ (e ⟨n, hn⟩))) hx
    simp only [actHom_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    calc n * x = x * n * x⁻¹ * x := by rw [h2]
      _ = x * n := by group
  rw [hC] at hmem
  exact hmem

theorem actHom_trans (e : N ≃* P) (g : MulAut P) (x : X) :
    actHom (e.trans g) x = g * actHom e x * g⁻¹ := by
  ext p
  rfl

end Action

variable {k : Type*} [Field k]

theorem xD_mem_normalizer (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    xD u ∈ normalizer (((eZero k).map
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) :
        Subgroup (MulAut (projectiveSL 3 k))) : Set (MulAut (projectiveSL 3 k))) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨xD u p, xD_mem_eZero hk hu hp,
      (CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv _ _).symm⟩
  · rintro ⟨p, hp, hpe⟩
    refine ⟨(xD u)⁻¹ p, ?_, ?_⟩
    · rw [xD_inv]
      exact xD_mem_eZero hk (inv_ne_one.mpr hu) hp
    · change MulAut.conj ((xD u)⁻¹ p) = h
      rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, inv_inv]
      change (xD u)⁻¹ * (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) p *
        xD u = h
      rw [hpe]
      group

theorem exists_of_model (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) {X : Type*} [Group X]
    {N : Subgroup X} [N.Normal] (Q : Subgroup X) (e : N ≃* projectiveSL 3 k)
    (hinj : Function.Injective (actHom e)) (hxQ : xD u ∈ Q.map (actHom e))
    (hEQ : ∀ p ∈ eZero k, MulAut.conj p ∈ Q.map (actHom e)) {z : X} (hz3 : z ^ 3 = 1)
    (hzc : ∀ q ∈ Q, q * z = z * q) :
    ∃ d ∈ Q, orderOf d = 3 ∧ d ∉ zpowers z ∧
      ∃ t ∈ N, t * d = d * t ∧ t * z * t⁻¹ = z⁻¹ ∧
        N ≤ (N ⊓ normalizer ((Q ⊓ N : Subgroup X) : Set X)) ⊔
          (N ⊓ centralizer ({d} : Set X)) := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨d, hdQ, hd⟩ := hxQ
  have hw3 : actHom e z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hwE : ∀ p ∈ eZero k, actHom e z * MulAut.conj p = MulAut.conj p * actHom e z := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := hEQ p hp
    rw [← hqp, ← map_mul, ← map_mul, hzc q hq]
  have hwx : actHom e z * xD u = xD u * actHom e z := by
    rw [← hd, ← map_mul, ← map_mul, hzc d hdQ]
  obtain ⟨e₀, he₀, hze⟩ := exists_eq_conj_of_commute hk hw3 hwE
  have hψt : actHom e ((e.symm tP : N) : X) = MulAut.conj tP := by
    rw [actHom_coe, MulEquiv.apply_symm_apply]
  refine ⟨d, hdQ, ?_, ?_, (e.symm tP : N), (e.symm tP).2, ?_, ?_, ?_⟩
  · rw [← orderOf_injective (actHom e) hinj d, hd, orderOf_xD hk hu]
  · intro hdz
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hdz
    apply xD_not_mem_zpowers hk hu he₀
    rw [← hd, ← hn, map_zpow, hze]
    exact zpow_mem (mem_zpowers _) n
  · apply hinj
    rw [map_mul, map_mul, hψt, hd]
    have h := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv (xD u) (tP : projectiveSL 3 k)
    rw [xD_tP] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · apply hinj
    rw [map_mul, map_mul, map_inv, map_inv, hψt]
    exact conj_tP_mul_mul_inv hk hu hw3 hwE hwx
  · set H := (N ⊓ normalizer ((Q ⊓ N : Subgroup X) : Set X)) ⊔
      (N ⊓ centralizer ({d} : Set X)) with hH
    set K : Subgroup (projectiveSL 3 k) := H.comap (N.subtype.comp e.symm.toMonoidHom) with hK
    have hb : bP ∈ K := by
      change ((e.symm bP : N) : X) ∈ H
      refine mem_sup_left ⟨(e.symm bP).2, le_normalizer ⟨?_, (e.symm bP).2⟩⟩
      obtain ⟨q, hq, hqb⟩ := hEQ bP bP_mem_eZero
      have hqe : q = ((e.symm bP : N) : X) := hinj (by
        rw [hqb, actHom_coe, MulEquiv.apply_symm_apply])
      rw [← hqe]
      exact hq
    have hfix : ∀ p, xD u p = p → p ∈ K := by
      intro p hp
      change ((e.symm p : N) : X) ∈ H
      refine mem_sup_right ⟨(e.symm p).2, mem_centralizer_singleton_iff.mpr ?_⟩
      apply hinj
      rw [map_mul, map_mul, hd, actHom_coe, MulEquiv.apply_symm_apply]
      have h := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv (xD u) p
      rw [hp] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have hKtop := eq_top_of_bP_mem hb hfix
    intro n hn
    have hmem : e ⟨n, hn⟩ ∈ K := by rw [hKtop]; exact mem_top _
    change ((e.symm (e ⟨n, hn⟩) : N) : X) ∈ H at hmem
    rwa [MulEquiv.symm_apply_apply] at hmem

end P614DOL

open P614DOL CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

theorem kFactL34DiagGen_holds : KFactL34DiagGen := by
  intro X _ _ N Q hN ⟨e₀⟩ hC hQ z _ hz3 hzc
  haveI := hN
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (projectiveSL 3 (GaloisField 2 2))) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  let e₁ : N ≃* projectiveSL 3 (GaloisField 2 2) :=
    e₀.trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 (GaloisField 2 2))).symm
  have hfac : (Nat.card (MulAut (projectiveSL 3 (GaloisField 2 2)))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  have hcard : Nat.card ((Q : Subgroup X).map (actHom e₁)) =
      3 ^ (Nat.card (MulAut (projectiveSL 3 (GaloisField 2 2)))).factorization 3 := by
    rw [Subgroup.card_map_of_injective (actHom_injective e₁ hC), hQ, hfac]
    norm_num
  have hS : IsPGroup 3 (zpowers (xD u) ⊔ (eZero (GaloisField 2 2)).map
      (MulAut.conj : projectiveSL 3 (GaloisField 2 2) →*
        MulAut (projectiveSL 3 (GaloisField 2 2))) :
          Subgroup (MulAut (projectiveSL 3 (GaloisField 2 2)))) := by
    have hp1 : IsPGroup 3 (zpowers (xD u)) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, pow_one, orderOf_xD hk hu])
    have hp2 : IsPGroup 3 (eZero (GaloisField 2 2)) :=
      IsPGroup.of_card (n := 2) (by rw [card_eZero hk]; norm_num)
    exact hp1.to_sup_of_normal_right' (hp2.map _) (zpowers_le.mpr (xD_mem_normalizer hk hu))
  obtain ⟨R, hR⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map hcard R
  have hmap : (Q : Subgroup X).map (actHom (e₁.trans g)) = R := by
    have h : actHom (e₁.trans g) = (MulAut.conj g).toMonoidHom.comp (actHom e₁) :=
      MonoidHom.ext fun x => actHom_trans e₁ g x
    rw [hg, Subgroup.map_map, h]
  refine exists_of_model hk hu (Q : Subgroup X) (e₁.trans g) (actHom_injective _ hC) ?_ ?_
    (by rw [← hz3]; exact pow_orderOf_eq_one z) hzc
  · rw [hmap]
    exact hR (mem_sup_left (mem_zpowers _))
  · intro p hp
    rw [hmap]
    exact hR (mem_sup_right ⟨p, hp, rfl⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
