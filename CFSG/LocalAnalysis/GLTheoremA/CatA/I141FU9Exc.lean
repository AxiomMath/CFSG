module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Exc2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LabHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgE6Res2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgTriality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FU9Ex

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem excU9_two_cases {d : TauCeti.ValidLieTypeIndex} (hd : I141F.u9FamExc (.lie d))
    (h2 : KD264Lie.fieldSize d.1 = 2) :
    (∃ q : TauCeti.PrimePower, (d.1 = .E7 q ∨ d.1 = .E8 q) ∧ q.card = 2) ∨
      lieOrderFormula d.1 = CFSG.Open.orderF4 2 ∨
      lieOrderFormula d.1 = CFSG.Open.orderTrialityD4 2 := by
  obtain ⟨idx, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases idx with
  | E7 q => exact Or.inl ⟨q, Or.inl rfl, h2⟩
  | E8 q => exact Or.inl ⟨q, Or.inr rfl, h2⟩
  | F4 q =>
    right; left
    show CFSG.Open.orderF4 q.card = _
    rw [show q.card = 2 from h2]
  | G2 q =>
    have h3 : 3 ≤ q.card := hr
    have h2' : q.card = 2 := h2
    omega
  | trialityD4 q =>
    right; right
    show CFSG.Open.orderTrialityD4 q.card = _
    rw [show q.card = 2 from h2]
  | _ => simp [I141F.u9FamExc, onLie] at hd

private theorem excU9_ne_twistedA {d : TauCeti.ValidLieTypeIndex} (hd : I141F.u9FamExc (.lie d))
    (q : TauCeti.PrimePower) : d.1 ≠ .twistedA 2 q := by
  obtain ⟨idx, hv⟩ := d
  rintro (rfl : idx = _)
  simp [I141F.u9FamExc, onLie] at hd

section Main


private theorem excU9_compAlgAt {d : TauCeti.ValidLieTypeIndex} (hd : I141F.u9FamExc (.lie d))
    (h8 : KD264Lie.fieldSize d.1 = 8) : KD264Lie.CompAlgAt (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | E7 q => exact KD264Lie.lieCompAlg_excUntwisted_kd264e6 ⟨_, hv⟩ trivial h8
  | E8 q => exact KD264Lie.lieCompAlg_excUntwisted_kd264e6 ⟨_, hv⟩ trivial h8
  | F4 q => exact KD264Lie.lieCompAlg_excUntwisted_kd264e6 ⟨_, hv⟩ trivial h8
  | G2 q => exact KD264Lie.lieCompAlg_excUntwisted_kd264e6 ⟨_, hv⟩ trivial h8
  | trialityD4 q => exact KD264Lie.lieCompAlg_triality ⟨_, hv⟩ trivial h8
  | _ => simp [I141F.u9FamExc, onLie] at hd

private theorem i141U9Fam_exc_of_e78 : I141F.I141U9Fam I141F.u9FamExc := by
  have hE78 := CFSG.LocalAnalysis.GLTheoremA.I141FU9Ex.e78TwoNoU38_holds
  intro Γ _ _ K J x a hQ hx ha hxa _ hI1 hI2 hJ hJU _ hF
  exfalso
  obtain ⟨i, hi, ⟨eS⟩⟩ := hQ
  cases i with
  | cyclic p hp => simp [I141F.u9FamExc, onLie] at hi
  | alternating n hn => simp [I141F.u9FamExc, onLie] at hi
  | sporadic s => simp [I141F.u9FamExc, onLie] at hi
  | lie d =>
  have hcardS : Nat.card (PSimple 3 K) = lieOrderFormula d.1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d _ ⟨eS⟩
  obtain ⟨-, -, ⟨eJ⟩⟩ := I141F.u9_transfer_chev hx hI1 hJ
  have hdvd : 5515776 ∣ Nat.card (PSimple 3 K) :=
    I141F.u9_dvd_card CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      (I2018.catalogIs_congr' eJ hJU)
  obtain ⟨hchar, hcase⟩ := I141F.u9_lie_cases hx hI1 hJ hJU eS
  rcases hcase with ⟨-, hc⟩ | ⟨hβ1, hfs2 | hfs8 | ⟨q, hq, -⟩⟩
  ·
    exact excU9_order_ne hi (hcardS.symm.trans hc)
  ·
    rcases excU9_two_cases hi hfs2 with ⟨q, hq, hq2⟩ | hF4 | hD4
    ·
      obtain ⟨hs, hnc⟩ := I141F.u9_simple_nonabelian hI1
      haveI := hs
      have hxN : x ∈ Subgroup.normalizer (K : Set Γ) := hI1.1 (Subgroup.mem_zpowers x)
      have hβ3 : chevAut 3 K ⟨x, hxN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx
      have hJp : GLAPComponent 3 (fixSubgroup (chevAut 3 K ⟨x, hxN⟩)) (chevTransfer 3 K J) :=
        glaPComponent_chevTransfer Nat.prime_three hxN
          (CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hx) hJ
      have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
        (PSimple 3 K) hs hnc d ⟨eS⟩ 3 Nat.prime_three (by norm_num) (by rw [hchar]; norm_num) _ hβ3 hβ1
      have hJc : CFSG.Open.IsComponentOf (chevTransfer 3 K J) (fixSubgroup (chevAut 3 K ⟨x, hxN⟩)) :=
        (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJp
          (hpil _ hJp.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJp))).1
      obtain ⟨e₂⟩ := I141F.centerQuot_equiv_pSimple Nat.prime_three hJp hJc.2.2
      exact hE78 (PSimple 3 K) d q hq hq2 ⟨eS⟩ _ hβ3 hβ1 _ hJc
        (I2018.catalogIs_congr' (eJ.trans e₂.symm) hJU)
    ·
      rw [hcardS, hF4] at hdvd
      have h19 : 19 ∣ CFSG.Open.orderF4 2 := dvd_trans (by norm_num) hdvd
      revert h19
      decide
    ·
      rw [hcardS, hD4] at hdvd
      have h19 : 19 ∣ CFSG.Open.orderTrialityD4 2 := dvd_trans (by norm_num) hdvd
      revert h19
      decide
  ·
    exact I141F.u9Gf8Absurd_holds Γ K J x a hx ha hxa hI1 hI2 hJ hJU hF d ⟨eS⟩ hchar hfs8
      (excU9_compAlgAt hi hfs8) hβ1
  ·
    exact excU9_ne_twistedA hi q hq

theorem i141U9Fam_exc : I141F.I141U9Fam I141F.u9FamExc :=
  i141U9Fam_exc_of_e78

end Main

end CFSG.LocalAnalysis.GLTheoremA.I141FU9Ex

end
