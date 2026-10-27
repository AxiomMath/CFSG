module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem22D
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem22E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem21O2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20Coprime

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem12222Frattini_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H P U I : Subgroup G) (h : G) (n p : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h p → U ≤ pCoreOf 2 H → ¬ IsCyclic ↥P → frattini ↥P = ⊥

theorem lem12222_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h325 : Stmt3_2_5_F4) (h1216 : Stmt12_2_16_F4) (h12218 : Stmt12_2_18_F4)
    (hI62 : ASInputs.AS_I_6_2_twoCases) (hres : Lem12222Frattini_F4) : Lem12222_F4 := by
  intro G _ _ T L V H P U I h n p hyp hNE hC hpre hUO
  have hP := hpre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hΦ, -⟩ := hP
  obtain ⟨h', v, hh'P, hh'M, hh'p, hvV, hvh, hvN, hidx⟩ :=
    coprimePick_of_F4 h331 h1222 h325 h1216 h12218 hI62 G T L V H P p hyp hNE hHs hsol hp hp2 hPp
      hPH hPi hHPT hΦ
  have hh'1 : h' ≠ 1 := fun h1 => hh'M (h1 ▸ Subgroup.one_mem _)
  have hΦ1 : frattini ↥P = ⊥ := by
    by_cases hcyc : IsCyclic ↥P
    · refine Lem22.frattini_eq_bot_of_isCyclic hp hPp hcyc hh'P hh'p hh'1 fun hm => hh'M ?_
      rw [← hΦ] at hm
      exact hm.2
    · exact hres G T L V H P U I h n p hyp hNE hC hpre hUO hcyc
  have hcard := Lem22.card_eq_of_frattini_F4 h331 h1222 hyp hNE hC hpre hUO hΦ1
  obtain ⟨U', I', hI', hU', hUdec', hUinf', hUe', hUc', hD', hidx', ⟨hcV', htr'⟩, hU'V, hCU',
    hh'I⟩ := pre12_2_21_of_inv_F4 h1222 h1216 hI62 hyp hNE hp hp2 hh'M hh'p hvV hvh hvN hidx
  have hpre' : Pre12_2_21 T L V H P U' I' h' p :=
    ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hΦ, hh'P, hh'M, hI', hU', hUdec', hUinf', hUe',
      hUc', hD', hidx', hcV', htr'⟩
  have hU'O := lem12221_of_F4 h331 h1222 G T L V H P U' I' h' n p hyp hNE hC hpre'
  have hvU' : v ∉ U' := fun hv => hvN (by
    have h1 : v ∈ U' ⊓ V := ⟨hv, hvV⟩
    rw [hU'V] at h1
    exact h1.2)
  exact ⟨P, U', I', conjClosure U' P, h', v, hpre', hU'O,
    Lem22.data_of_card_eq_prime_F4 h331 h1222 hyp hpre' hU'O hcard hvV hvU' hvh hh'I hCU'⟩

theorem lem12223_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hres : Lem12222Frattini_F4) :
    Lem12223_F4 := by
  intro G _ _ T L V H P U I W h v n p hyp hNE hC hpre hUO hdata
  have hP := hpre
  obtain ⟨-, -, hp, -, hPp, -⟩ := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htri⟩ := hdata
  by_cases hcyc : IsCyclic ↥P
  · rcases htri with h1 | ⟨-, hE⟩ | ⟨-, hnc⟩
    · exact h1
    · have : Fact p.Prime := ⟨hp⟩
      have : Fact (IsPGroup p ↥P) := ⟨hPp⟩
      refine Lem22.card_eq_of_frattini_F4 h331 h1222 hyp hNE hC hpre hUO ?_
      refine (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥P) (p := p)).mpr ?_
      exact
        { toIsMulCommutative := hE.1
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (by simpa using hE.2 x x.2) }
    · exfalso
      apply hnc
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥P)
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
      exact zpow_mul_comm g i j
  · exact Lem22.card_eq_of_frattini_F4 h331 h1222 hyp hNE hC hpre hUO
      (hres G T L V H P U I h n p hyp hNE hC hpre hUO hcyc)

end CFSG.Quasithin.H13
