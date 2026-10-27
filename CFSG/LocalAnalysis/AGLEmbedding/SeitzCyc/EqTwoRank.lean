module

public import CFSG.LieType.SeitzGeneration.ExcTorusF4
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Six
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6Three
import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.OrderSix

public section

namespace CFSG.AGLEmbedding.SeitzCyc

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration TauCeti
  CFSG.TauCetiBridge
open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube (dvd_sq_add_add_one_of_orderOf_eq_three
  dvd_sq_sub_add_one_of_orderOf_eq_six)

theorem not_rankLE1_of_sylowTorus_two {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : SylowTorus G p 2) : ¬ RankLE1 p G := by
  intro h1
  obtain ⟨E, hE, hc⟩ := h.exists_elemAbelian
  have hle := h1 E hE
  rw [hc] at hle
  have h2 := hp.two_le
  have : p * 2 ≤ p * p := Nat.mul_le_mul_left p h2
  nlinarith


theorem sylowTorus_cat_F4_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcnt : degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    SylowTorus (Cat ⟨.F4 q, hv⟩) p 2 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  rw [← hK] at hcnt
  refine SylowTorus.of_mulEquiv ?_ e.symm
  rcases degCount_F4_eq_two hcnt with h3 | h4 | h6
  · exact sylowTorus_F4_three K hp hp3 (dvd_sq_add_add_one_of_orderOf_eq_three hp h3).1
  · exact sylowTorus_F4_four K hp hp3 (dvd_sq_add_one_of_orderOf_eq_four hp h4)
  · exact sylowTorus_F4_six K hp hp3 (dvd_sq_sub_add_one_of_orderOf_eq_six hp h6).1

theorem sylowTorus_cat_E6_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    SylowTorus (Cat ⟨.E6 q, hv⟩) p 2 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at hcnt
  refine SylowTorus.of_mulEquiv ?_ e.symm
  rcases degCount_E6_eq_two hcnt with h4 | h6
  · exact sylowTorus_E6_four K hp h4
  · exact sylowTorus_E6_six K hp h6

theorem sylowTorus_cat_E7_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    SylowTorus (Cat ⟨.E7 q, hv⟩) p 2 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at hcnt
  exact (sylowTorus_E7_four K hp (degCount_E7_eq_two hcnt)).of_mulEquiv e.symm

theorem sylowTorus_cat_E8_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    SylowTorus (Cat ⟨.E8 q, hv⟩) p 2 := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at hcnt
  refine SylowTorus.of_mulEquiv ?_ e.symm
  rcases degCount_E8_eq_two hcnt with h5 | h8 | h10 | h12
  · exact sylowTorus_E8_five K hp h5
  · exact sylowTorus_E8_eight K hp h8
  · exact sylowTorus_E8_ten K hp h10
  · exact sylowTorus_E8_twelve K hp h12

theorem sylowTorus_cat_twistedE6_of_eqTwo (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime)
    (hcnt : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    SylowTorus (Cat ⟨.twistedE6 q, hv⟩) p 2 := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at hcnt
  obtain ⟨n, hn⟩ : ∃ n, orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = n := ⟨_, rfl⟩
  rw [hn] at hcnt
  refine SylowTorus.of_mulEquiv ?_ e.symm
  rcases degCountTw_eq_two hcnt with rfl | rfl
  · exact sylowTorus_twistedE6_three q.prime_p q.exponent_pos K hK σ hσ hp hn
  · exact sylowTorus_twistedE6_four q.prime_p q.exponent_pos K hK σ hσ hp hn

theorem not_rankLE1_cat_F4_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcnt : degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    ¬ RankLE1 p (Cat ⟨.F4 q, hv⟩) :=
  not_rankLE1_of_sylowTorus_two hp (sylowTorus_cat_F4_of_eqTwo q hv hp hp3 hcnt)

theorem not_rankLE1_cat_E6_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    ¬ RankLE1 p (Cat ⟨.E6 q, hv⟩) :=
  not_rankLE1_of_sylowTorus_two hp (sylowTorus_cat_E6_of_eqTwo q hv hp hcnt)

theorem not_rankLE1_cat_E7_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    ¬ RankLE1 p (Cat ⟨.E7 q, hv⟩) :=
  not_rankLE1_of_sylowTorus_two hp (sylowTorus_cat_E7_of_eqTwo q hv hp hcnt)

theorem not_rankLE1_cat_E8_of_eqTwo (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    ¬ RankLE1 p (Cat ⟨.E8 q, hv⟩) :=
  not_rankLE1_of_sylowTorus_two hp (sylowTorus_cat_E8_of_eqTwo q hv hp hcnt)

theorem not_rankLE1_cat_twistedE6_of_eqTwo (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime)
    (hcnt : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 2) :
    ¬ RankLE1 p (Cat ⟨.twistedE6 q, hv⟩) :=
  not_rankLE1_of_sylowTorus_two hp (sylowTorus_cat_twistedE6_of_eqTwo q hv hp hcnt)

end CFSG.AGLEmbedding.SeitzCyc
