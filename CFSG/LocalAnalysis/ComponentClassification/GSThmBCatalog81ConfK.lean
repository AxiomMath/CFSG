module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfT
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81L0
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfA

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4 GorensteinWalter

namespace ConfK

theorem dihedral_of_equiv {G : Type*} [Group G] [Finite G] {L : Subgroup G} {E : Type}
    [Field E] [Finite E] (hE : IsOddPrimePower (Nat.card E)) (ψ : ↥L ≃* PSL2 E)
    {D : Subgroup G} (hDL : D ≤ L) (hDc : Nat.card D = 2 ^ (Nat.card L).factorization 2)
    (h8 : 8 ≤ Nat.card D) :
    Nat.card ↥(D ⊓ centralizer (D : Set G)) = 2 ∧
      ∃ t ∈ D, t * t ≠ 1 ∧ t * t ∈ centralizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD'c : Nat.card (D.subgroupOf L) = 2 ^ (Nat.card ↥L).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv, hDc]
  let S : Sylow 2 ↥L := Sylow.ofCard (D.subgroupOf L) hD'c
  have hS : (S : Subgroup ↥L) = D.subgroupOf L := Sylow.coe_ofCard _ _
  obtain ⟨m, -, ⟨φ⟩⟩ := AutL2Facts.sylow_two_dihedral_of_equiv ψ hE S
  let χ : ↥D ≃* DihedralGroup (2 ^ m) :=
    ((subgroupOfEquivOfLe hDL).symm.trans (MulEquiv.subgroupCongr hS.symm)).trans φ
  have hcard : Nat.card D = 2 ^ (m + 1) := by
    rw [Nat.card_congr χ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hm : 2 ≤ m := by
    rw [hcard] at h8
    by_contra h
    push Not at h
    interval_cases m <;> norm_num at h8
  obtain ⟨h1, h2, -⟩ := AutL2Facts.dihedral_sylow_conclusions D hm χ
  exact ⟨h1, h2⟩

theorem facts_psp {K₀ : Type} [Group K₀] [Finite K₀] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK₀ : Blueprint.LieModel K₀ .PSp 2 p f) (α : MulAut K₀)
    (hα : Cat8.IsAdmQ K₀ (p ^ f) α) : ConfA.Facts K₀ (p ^ f) α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hK₀
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨-, u, w, huw⟩ := cfSec8Simple K₀ p f hp hp2 hf (Or.inl hK₀)
  have hc : ∀ z : K₀, z ∈ center K₀ → z = 1 := by
    intro z hz
    have hn : (center K₀).Normal := inferInstance
    obtain ⟨hsimp, -⟩ := cfSec8Simple K₀ p f hp hp2 hf (Or.inl hK₀)
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [h, mem_bot] at hz
      exact hz
    · exfalso
      have hu : u ∈ center K₀ := h ▸ mem_top u
      exact huw (mem_center_iff.mp hu w).symm
  have hconj_inj : Function.Injective (MulAut.conj : K₀ →* MulAut K₀) :=
    fun g h hgh => conj_injective_of_center hc hgh
  have hcommG : ∀ β : MulAut K₀, ∀ x, e (β x) = MulAut.congr e β (e x) := fun β x => by
    simp [MulAut.congr_apply]
  have hfixc : ∀ β : MulAut K₀,
      Nat.card (fixOf (MulAut.congr e β)) = Nat.card (Eight.fixSubgroup β) := by
    intro β
    rw [← map_fixOf_of_comm (hcommG β), ← Nat.card_congr ((fixOf β).equivMapOfInjective _
      e.injective).toEquiv]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have hcongr_conj : ∀ t : K₀, MulAut.congr e (MulAut.conj t) = MulAut.conj (e t) := by
    intro t
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hout : MulAut.congr e α ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
    rintro ⟨v, hv⟩
    apply hα.out
    refine ⟨e.symm v, ?_⟩
    ext x
    apply e.injective
    rw [hcommG α, ← hv]
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨A, hA, d, hd0, hdsq, hAA, hμ⟩ := exists_typeII_of_admissible hp hp2 hf hK
    (MulAut.congr e α) (by rw [← map_mul, hα.sq, map_one]) hout (by rw [hfixc]; exact hα.dvd)
  obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A hd0 hdsq hAA hμ
  have hθα : ∀ g, MulAut.congr e α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
    rw [hA, conjAut_proj]
  have heq := L0Psp.commutator_fixOf_eq (conjSp 2 K A) hθα hQ.1
  have hL0 : Cat8.L0 K₀ α = (⁅fixOf α, fixOf α⁆).map (MulAut.conj : K₀ →* MulAut K₀) := by
    show ⁅Cat8.Inn K₀ ⊓ centralizer ({α} : Set (MulAut K₀)),
      Cat8.Inn K₀ ⊓ centralizer ({α} : Set (MulAut K₀))⁆ = _
    rw [← map_conj_fixOf hc α, Subgroup.map_commutator]
  have hcomm' : (⁅fixOf α, fixOf α⁆ : Subgroup K₀).map e.toMonoidHom =
      (fixOf (conjSp 2 K A)).map (proj 2 K) := by
    rw [Subgroup.map_commutator, map_fixOf_of_comm (hcommG α), heq]
  have hcardL0 := L0Psp.card_L0_psp hp hp2 hf hK₀ α hα
  refine ⟨?_, hcardL0, ?_, ?_⟩
  ·
    have h1 : Nat.card (Cat8.innFix K₀ α) = Nat.card (Eight.fixSubgroup α) := by
      show Nat.card ↥(Cat8.Inn K₀ ⊓ centralizer ({α} : Set (MulAut K₀))) = _
      rw [← map_conj_fixOf hc α, card_map_of_injective hconj_inj]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
    have h3 := card_fixOf_dvd h2 (conjSp 2 K A) hθα
    rw [hcard, hfixc] at h3
    rw [h1]
    refine h3.trans (dvd_of_eq ?_)
    have hqodd : Odd (p ^ f) := hK ▸ hodd
    have hev : 2 ∣ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) := by
      apply Dvd.dvd.mul_left
      obtain ⟨r, hr⟩ := (hqodd.pow : Odd ((p ^ f) ^ 2)).pow (n := 2)
      exact ⟨r, by omega⟩
    exact (Nat.mul_div_cancel' hev).symm
  ·
    intro τ hτI hτα hτ2 hτ1 hadm
    obtain ⟨t, rfl⟩ := hτI
    have htfix : α t = t := by
      have hmem : MulAut.conj t ∈ (fixOf α).map (MulAut.conj : K₀ →* MulAut K₀) := by
        rw [map_conj_fixOf hc α]
        exact ⟨⟨t, rfl⟩, mem_centralizer_singleton_iff.mpr hτα⟩
      obtain ⟨s, hs, hst⟩ := hmem
      rw [← hconj_inj hst]
      exact hs
    have htt : t * t = 1 := hconj_inj (by rw [map_mul, hτ2, map_one])
    have ht1 : t ≠ 1 := fun h => hτ1 (by rw [h, map_one])
    obtain ⟨T, hT⟩ := proj_surjective (e t)
    have hTfix : conjAut 2 K A (proj 2 K T) = proj 2 K T := by
      rw [hT, ← hA, ← hcommG α t, htfix]
    have hTT : proj 2 K T * proj 2 K T = 1 := by rw [hT, ← map_mul, htt, map_one]
    have hT1 : proj 2 K T ≠ 1 := by
      rw [hT]
      exact fun h => ht1 (e.injective (h.trans (map_one e).symm))
    have hadm' : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ∣
        Nat.card (fixOf (conjAut 2 K A * MulAut.conj (proj 2 K T))) := by
      have h1 : conjAut 2 K A * MulAut.conj (proj 2 K T) =
          MulAut.congr e (α * MulAut.conj t) := by
        rw [map_mul, hA, hcongr_conj, hT]
      rw [h1, hfixc]
      exact hadm.dvd
    obtain ⟨hnot, hconjT⟩ := ConfP.type_model hp hp2 hf hK A hd0 hdsq hAA hμ T hTfix hTT hT1
      hadm'
    refine ⟨?_, ?_⟩
    · rw [hL0]
      rintro ⟨s, hs, hst⟩
      have hst' : s = t := hconj_inj hst
      subst hst'
      apply hnot
      rw [hT, ← hcomm']
      exact mem_map_of_mem _ hs
    · rw [hL0]
      rintro _ ⟨s, hs, rfl⟩ hss hs1
      have hes : e s ∈ (fixOf (conjSp 2 K A)).map (proj 2 K) := by
        rw [← hcomm']
        exact mem_map_of_mem _ hs
      obtain ⟨Z, hZ, hZs⟩ := hes
      have hss' : s * s = 1 := hconj_inj (by rw [map_mul, hss, map_one])
      have hs1' : s ≠ 1 := fun h => hs1 (by rw [h, map_one])
      obtain ⟨g, hg⟩ := hconjT Z hZ (by rw [hZs, ← map_mul, hss', map_one])
        (by rw [hZs]; exact fun h => hs1' (e.injective (h.trans (map_one e).symm)))
      refine ⟨MulAut.conj (e.symm g), ⟨e.symm g, rfl⟩, ?_⟩
      have hkey : (e.symm g)⁻¹ * s * e.symm g = t := by
        apply e.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hZs, hg, hT]
      rw [← hkey, map_mul, map_mul, map_inv]
  ·
    intro D hDL _ hDc
    obtain ⟨E, _, _, hE, ⟨ψ₄⟩⟩ := ConfP.exists_map_fixOf_equiv_PSL2 hp hp2 hf hK A hd0 hdsq hAA hμ
    let ψ : ↥(Cat8.L0 K₀ α) ≃* PSL2 E :=
      ((MulEquiv.subgroupCongr hL0).trans
        ((⁅fixOf α, fixOf α⁆ : Subgroup K₀).equivMapOfInjective _ hconj_inj).symm).trans
      ((((⁅fixOf α, fixOf α⁆ : Subgroup K₀).equivMapOfInjective e.toMonoidHom
        e.injective).trans (MulEquiv.subgroupCongr hcomm')).trans ψ₄)
    have hEodd : IsOddPrimePower (Nat.card E) :=
      ⟨p, f * 2, hp, hp.odd_of_ne_two hp2, by omega, by rw [hE, pow_mul]⟩
    have hpos : Cat8.ordL2 ((p ^ f) ^ 2) ≠ 0 := by
      rw [← hcardL0]
      exact Nat.card_pos.ne'
    refine dihedral_of_equiv hEodd ψ hDL (by rw [hDc, hcardL0]) ?_
    rw [hDc]
    have h := (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp
      (show 2 ^ 3 ∣ Cat8.ordL2 ((p ^ f) ^ 2) from
        ConfA.eight_dvd_ordL2 ((hp.odd_of_ne_two hp2).pow))
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (Cat8.ordL2 ((p ^ f) ^ 2)).factorization 2 := Nat.pow_le_pow_right (by norm_num) h

end ConfK

end CFSG.ComponentClassification.GSThmB
