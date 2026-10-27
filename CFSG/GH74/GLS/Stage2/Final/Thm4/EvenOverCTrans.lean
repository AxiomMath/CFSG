module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCPair
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Elem

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Aux

variable {G : Type} [Group G]

private theorem mem_Cen_conj_iff_aux (z g x : G) :
    x ∈ Cen (g * z * g⁻¹) ↔ g⁻¹ * x * g ∈ Cen z := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : g⁻¹ * (x * (g * z * g⁻¹)) * g = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := h1
      _ = z * (g⁻¹ * x * g) := by group
  · intro h
    have h1 : g * (g⁻¹ * x * g * z) * g⁻¹ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    calc x * (g * z * g⁻¹) = g * (g⁻¹ * x * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := h1
      _ = (g * z * g⁻¹) * x := by group

private theorem map_conj_Cen (z c : G) :
    (Cen z).map (MulAut.conj c).toMonoidHom = Cen (c * z * c⁻¹) := by
  ext x
  rw [mem_Cen_conj_iff_aux, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
    exact hy
  · intro h
    refine ⟨c⁻¹ * x * c, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end Aux

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem pairData_bar (ctx : Stage2Ctx G z k S) (hk : ∃ ε : Bool, k = Kind.l4 ε) :
    PairData (CentralizerBar z) := by
  obtain ⟨ε, rfl⟩ := hk
  have hd := ctx.data
  cases hd with
  | l4 _ h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    have hp := h.pair
    obtain ⟨hsup, hcomm, -⟩ := hp.prod
    have hlayer : layer (CentralizerBar z) = L₁ ⊔ L₂ := by
      simp only [CFSG.layer.eq_sSup]
      rw [hp.comps, sSup_pair]
    refine ⟨CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2, ?_, L₁, L₂, hp.ne, hp.comps, hcomm, ?_⟩
    · rw [hp.fitting, hlayer, hsup]
    · obtain ⟨s, -, hsC, hs1, hs2⟩ := hp.swap
      exact ⟨toBar z ⟨s, hsC⟩, hs1, hs2⟩

noncomputable def cenEquivBar (hO : pPrimeCoreOf 2 (Cen z) = ⊥) : ↥(Cen z) ≃* CentralizerBar z :=
  MulEquiv.ofBijective (toBar z)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [ker_toBar]; exact (pPrimeCoreOf_eq_bot_iff _).mp hO),
      toBar_surjective z⟩

theorem pairData_Cen (ctx : Stage2Ctx G z k S) (hk : ∃ ε : Bool, k = Kind.l4 ε)
    (hO : pPrimeCoreOf 2 (Cen z) = ⊥) : PairData ↥(Cen z) :=
  (pairData_bar ctx hk).of_equiv (cenEquivBar hO).symm

noncomputable def cenConjEquiv {t : G} (ht : IsConj z t) : ↥(Cen z) ≃* ↥(Cen t) :=
  (MulEquiv.subgroupMap (MulAut.conj (Classical.choose (isConj_iff.mp ht))) (Cen z)).trans
    (MulEquiv.subgroupCongr
      ((map_conj_Cen z (Classical.choose (isConj_iff.mp ht))).trans
        (congrArg Cen (Classical.choose_spec (isConj_iff.mp ht)))))

theorem pairData_Cen_conj (ctx : Stage2Ctx G z k S) (hk : ∃ ε : Bool, k = Kind.l4 ε)
    (hO : pPrimeCoreOf 2 (Cen z) = ⊥) {t : G} (ht : IsConj z t) : PairData ↥(Cen t) :=
  (pairData_Cen ctx hk hO).of_equiv (cenConjEquiv ht)

theorem PairData.pCore_eq_bot {Y : Type} [Group Y] [Finite Y] (h : PairData Y) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : pCore p Y = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p) (G := Y))
  refine pPrimeCore_eq_bot_iff.mp h.oddCore _ CFSG.pCore_normal ?_
  rw [hn]
  exact ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_right n

theorem PairData.sec {Y : Type} [Group Y] [Finite Y] (h : PairData Y) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : PairData (Y ⧸ pCore p Y) :=
  h.of_equiv (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (h.pCore_eq_bot hp hp2).symm))

end CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver
