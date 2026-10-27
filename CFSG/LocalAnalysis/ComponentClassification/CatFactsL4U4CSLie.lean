module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSUg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentE
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CenterRow

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSL

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank

theorem false_of_omegaMinus {G : Type} [Group G] [Finite G] {N : Subgroup G} {α : G}
    {J R : Subgroup G} {τ : G} (hcfg : OutInv.CenterSylowConfig G N α J R τ) {p f e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hαN : α ∈ N) (hJN : J ≤ N) (he : f = 2 * e)
    (hO : Blueprint.LieModel ↥N .POmegaMinus 4 p e)
    (hJ : Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p (2 * f)) : False := by
  classical
  obtain ⟨-, -, hα2, hJα, -, -, -, -, -, -, -, -, -⟩ := hcfg
  obtain ⟨-, K', _, _, hK', b, c, hbc, ⟨eO⟩⟩ :=
    statedClassicalModel_of_lieModel_ne_zero (by norm_num) hO
  let : Fintype K' := Fintype.ofFinite K'
  have hKq : Fintype.card K' = p ^ e := by rw [Fintype.card_eq_nat_card, hK']
  have hJtype : IsSec8JType (↥J ⧸ center ↥J) p f := Or.inl hJ
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJtype
  have := Fact.mk hs
  obtain ⟨⟨y, hyJ⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) s
    (hsJ.trans (Subgroup.card_quotient_dvd_card _))
  rw [Subgroup.orderOf_mk] at hys
  have hyN := hJN hyJ
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα2
    norm_num at hα2
  have hyα : y * α = α * y := mem_centralizer_singleton_iff.mp (hJα hyJ)
  have h4 : (p ^ e) ^ 4 = (p ^ f) ^ 2 := by rw [he, ← pow_mul, ← pow_mul]; ring_nf
  apply false_of_omegaMinus_eight (K := K') (hKq ▸ (hp.odd_of_ne_two hp2).pow) hbc hs hs2
    (by rw [hKq, h4]; exact hsq) (eO ⟨α, hαN⟩) (eO ⟨y, hyN⟩)
  · rw [Ne, MulEquiv.map_eq_one_iff]
    intro h1
    exact hα1 (congrArg Subtype.val h1)
  · rw [← map_pow, sq]
    convert map_one eO
    exact Subtype.ext hαα
  · rw [← map_pow]
    convert map_one eO
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hys, pow_orderOf_eq_one]
    rfl
  · rw [Ne, MulEquiv.map_eq_one_iff]
    intro h1
    have hy1 : y = 1 := congrArg Subtype.val h1
    rw [hy1, orderOf_one] at hys
    exact hs.one_lt.ne hys
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyα.symm

theorem centerSylowLie : OutInv.CenterSylowLie := by
  intro G _ _ N α J R τ hcfg p f hp hp2 hf hαN hJN htype hJ
  rcases htype with hL | hU | ⟨e, he, hO⟩
  · exact centerSylow_L4 hcfg hp hp2 hf hαN hL hJ
  · exact CSU.centerSylow_U4 hcfg hp hp2 hf hαN hU hJ
  · exact (false_of_omegaMinus hcfg hp hp2 hf hαN hJN he hO hJ).elim

end CSL

namespace OutInv

open CFSG CFSG.ComponentClassification.GSThmB

theorem cfProp23Center_of_suz
    (hCent : OuterL2Cent) (hSuz : CenterSylowSuz) :
    CFProp23Center :=
  cfProp23Center_of hCent AltCent.centerSylowAlt CSL.centerSylowLie hSuz

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
