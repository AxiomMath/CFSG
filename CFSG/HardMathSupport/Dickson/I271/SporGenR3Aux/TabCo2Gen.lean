module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthChev

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth
open scoped commutatorElement

theorem not_prime_pow_four_dvd_360 {p : ℕ} (hp : p.Prime) : ¬ p ^ 4 ∣ 360 := by
  intro h
  have hle : p ^ 4 ≤ 360 := Nat.le_of_dvd (by norm_num) h
  have hp5 : p ≤ 4 := by
    by_contra hlt
    have : 5 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  have hp2 := hp.two_le
  interval_cases p <;> first | exact absurd h (by decide) | exact absurd hp (by decide)

theorem leafType_of_pow_four_dvd {p : ℕ} (hp : p.Prime) {T : Type} [Group T]
    (hC : IsChevSimple p T) (h4 : p ^ 4 ∣ Nat.card T) : LeafType p T := by
  refine Or.inl ⟨hC, fun hL => ?_, ?_⟩
  · rw [card_of_isLTwoTwentySeven hL] at h4
    exact not_prime_pow_four_dvd_9828 hp h4
  · rintro ⟨f⟩
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup] at h4
    exact not_prime_pow_four_dvd_360 hp (by simpa [Nat.factorial] using h4)

theorem isQuasisimple_of_simple_nonab {J : Type} [Group J] [IsSimpleGroup J]
    (hnab : ∃ a b : J, a * b ≠ b * a) : CFSG.Open.IsQuasisimple J := by
  have hZ : Subgroup.center J = ⊥ := center_eq_bot_of_simple_nonab hnab
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
  · exact h

theorem shapeRkAt_of_subgroup_data_nq {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (P : Subgroup G) [Finite P] (x : ↥P) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P)
    (hLn : ∀ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    (hcent : ∀ c ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, (∀ l ∈ L, l * c = c * l) →
      c ^ p = 1)
    (hG : Good ↥L) (hR : Rk ↥L) : ShapeRkAt p Good Rk x := by
  have hLP : L ≤ P := fun l hl => (hLC hl).2
  haveI : Finite ↥L := Finite.of_injective (Subgroup.inclusion hLP) (Subgroup.inclusion_injective hLP)
  let C' : Subgroup ↥P := Subgroup.centralizer ({x} : Set ↥P)
  let L' : Subgroup ↥P := L.comap P.subtype
  have hmapC : C'.map P.subtype = Subgroup.centralizer ({(x : G)} : Set G) ⊓ P :=
    map_centralizer_subtype' P x
  have hL'C : L' ≤ C' := by
    intro l hl
    have hl1 : (l : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := hLC hl
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hl1).1
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hc)
  let E : Subgroup ↥C' := L'.subgroupOf C'
  have hEn : E.Normal := by
    refine ⟨fun e he g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at he ⊢
    have hgC : ((g : ↥P) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
      rw [← hmapC]
      exact ⟨g, g.2, rfl⟩
    have := hLn _ hgC _ he
    exact this
  haveI := hEn
  have hEmap : E.map C'.subtype = L' := Subgroup.map_subgroupOf_eq_of_le hL'C
  have eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLP
  have eE : ↥(E.map C'.subtype) ≃* ↥L := (MulEquiv.subgroupCongr hEmap).trans eL
  have hsE : IsSimpleGroup ↥(E.map C'.subtype) := eE.isSimpleGroup_congr.2 hs
  have hnabE : ∃ a b : ↥(E.map C'.subtype), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eE.symm a, eE.symm b, fun h => hab (by simpa using congrArg eE h)⟩
  have hpE : p ∣ Nat.card ↥(E.map C'.subtype) := by
    rw [Nat.card_congr eE.toEquiv]; exact hpL
  have hZE : Subgroup.center ↥(E.map C'.subtype) = ⊥ := by
    haveI := hsE
    exact center_eq_bot_of_simple_nonab hnabE
  have hcoreE : GLAPPrimeCore p ↥(E.map C'.subtype) = ⊥ := by
    haveI := hsE
    exact glaPPrimeCore_eq_bot_of_simple hp hpE
  have hLC' : E.map C'.subtype ≤ Subgroup.centralizer ({x} : Set ↥P) := Subgroup.map_subtype_le E
  have hLn' : ∀ g ∈ Subgroup.centralizer ({x} : Set ↥P), ∀ l ∈ E.map C'.subtype,
      g * l * g⁻¹ ∈ E.map C'.subtype := by
    rintro g hg _ ⟨e, he, rfl⟩
    exact ⟨⟨g, hg⟩ * e * ⟨g, hg⟩⁻¹, hEn.conj_mem e he ⟨g, hg⟩, rfl⟩
  have hLq : CFSG.Open.IsQuasisimple ↥(E.map C'.subtype) := by
    haveI := hsE
    exact isQuasisimple_of_simple_nonab hnabE
  have hcentP : IsPGroup p ↥(Subgroup.centralizer ({x} : Set ↥P) ⊓
      Subgroup.centralizer ((E.map C'.subtype : Subgroup ↥P) : Set ↥P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcP : ((c : ↥P) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
      rw [← hmapC]
      exact ⟨c.1, (Subgroup.mem_inf.1 c.2).1, rfl⟩
    have hcomm : ∀ l ∈ L, l * ((c : ↥P) : G) = ((c : ↥P) : G) * l := by
      intro l hl
      have hlE : (⟨l, hLP hl⟩ : ↥P) ∈ E.map C'.subtype := by
        rw [hEmap]
        exact hl
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 _ hlE
      exact congrArg Subtype.val this
    have h0 := hcent _ hcP hcomm
    have h1 : (c : ↥P) ^ p = 1 := Subtype.ext (by simpa using h0)
    have h2 : c ^ p = 1 := Subtype.ext h1
    rw [pow_one]
    exact h2
  exact shapeRkAt_of_normal_quasisimple hp hLC' hLn' hLq hpE hcentP
    (hGood ↥L _ ((pSimpleEquivSelf (E.map C'.subtype) hcoreE hZE).trans eE).symm hG)
    (hRk ↥L _ ((pQuotEquivSelf (E.map C'.subtype) hcoreE).trans eE).symm hR)

end CFSG.HardMathSupport.Dickson.I271
