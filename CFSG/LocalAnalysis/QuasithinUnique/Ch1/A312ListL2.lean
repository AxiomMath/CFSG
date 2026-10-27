module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.Quasithin.Background.DicksonPerfectPSL2
public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Quasithin CFSG.Quasithin.Dickson CFSG.Assembly.LowTwoRank

theorem equiv_psl2_zmod_of_model {S : Type} [Group S] {p : ℕ} [Fact p.Prime] (h : IsPSL 2 p 1 S) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod p) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod p := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2)))⟩

theorem card_sl2_zmod' (p : ℕ) [hp : Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have hq : 1 < p := hp.out.one_lt
  have := Fintype.ofFinite (ZMod p)
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ZMod.card, show p ^ 2 - p = p * (p - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem two_mul_card_psl2 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * 2 = p * (p ^ 2 - 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.out.two_le
    omega
  rw [← card_sl2_zmod' p, CFSG.RankThree.SubgroupLists.natCard_sl2_eq h2]

theorem sixteen_dvd_of_mod_eight' {p : ℕ} (h : p % 8 = 1 ∨ p % 8 = 7) : 16 ∣ p * (p ^ 2 - 1) := by
  have h16 : p % 16 = 1 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 15 := by omega
  have hsq : p ^ 2 % 16 = 1 := by
    rcases h16 with h | h | h | h <;> simp [Nat.pow_mod, h]
  have hle : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  exact Dvd.dvd.mul_left (by omega) p

theorem l2p_psl2 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hq : CFSG.IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
    (hmodel : IsPSL 2 p 1 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) :
    A312For (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))))
  have hTsyl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) = T at hTsyl
  refine A312For.of_sylow T hTsyl fun B hB hBtop => ?_
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB'
  have hBne : B ≠ ⊥ := ne_bot_of_mem_cComp hB'
  rcases perfect_subgroup_psl2_prime hp2 B hBperf hBne with hBt | ⟨⟨eB⟩, hp5⟩
  · exact absurd hBt hBtop
  have hB60 : Nat.card B = 60 := (Nat.card_congr eB.toEquiv).trans card_alt_five
  have hG2 := two_mul_card_psl2 hp2
  have hp5ne : 5 ∣ p ^ 2 - 1 := by
    rcases hp5 with h | h
    · exfalso
      subst h
      apply hBtop
      apply Subgroup.eq_top_of_card_eq
      have h120 : (5 : ℕ) * (5 ^ 2 - 1) = 120 := by norm_num
      rw [h120] at hG2
      rw [hB60]
      omega
    · exact h
  have hsq : p ^ 2 % 5 = 1 := by
    have hle : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    generalize p ^ 2 = n at hp5ne hle ⊢
    omega
  have hMne : B ⊔ T ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  rcases overgroup_alternating_five_psl2_prime hp2 (le_sup_left : B ≤ B ⊔ T) ⟨eB⟩ with
    hMtop | hM60
  · exact absurd hMtop hMne
  have hBM : B = B ⊔ T := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hM60, hB60])
  have hTB : T ≤ B := by
    have := le_sup_right (a := B) (b := T)
    rwa [← hBM] at this
  have hmod8 : p % 8 = 3 ∨ p % 8 = 5 := by
    by_contra hcon
    have hodd : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp.out with h | h
      · exact absurd h hp2
      · exact h
    have h18 : p % 8 = 1 ∨ p % 8 = 7 := by omega
    have h16 := sixteen_dvd_of_mod_eight' h18
    rw [← hG2] at h16
    have h8G : 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by omega
    obtain ⟨k, hk⟩ := hTsyl.2.1.exists_card_eq
    have hidx : ¬ 2 ∣ T.index := by
      have := hTsyl.2.2
      rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right _] at this
    have hXS := (Subgroup.card_mul_index T).symm
    rw [hk] at hXS
    rw [hXS] at h8G
    have hcop : Nat.Coprime (2 ^ 3) T.index :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
    have h8 : 2 ^ 3 ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right (by simpa using h8G)
    have hT60 : Nat.card T ∣ 60 := hB60 ▸ Subgroup.card_dvd_of_le hTB
    rw [hk] at hT60
    have := h8.trans hT60
    norm_num at this
  have hLmodel : IsPSL 2 p 1 ↥(⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (ZMod p))) := IsPSL.of_mulEquiv Subgroup.topEquiv.symm hmodel
  iterate 6 right
  left
  right
  exact ⟨⟨eB⟩, p, hp.out, hLmodel, hsq, hmod8⟩

theorem l2p : FamL2p := by
  intro X _ _ p hq hp hp2 hX
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := equiv_psl2_zmod_of_model hX
  exact A312For.of_mulEquiv e
    (l2p_psl2 hp2 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq) (IsPSL.of_mulEquiv e hX))

end CFSG.QuasithinUnique.Vol2Native.A312L
