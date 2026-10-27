module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Transfer
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Cover
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem ThompsonPreFrame.pPrimeCore_eq {p : ℕ} {Y : Type} [Group Y] [Finite Y] {K D : Subgroup Y}
    [K.Normal] (h : ThompsonPreFrame p K D) : CFSG.pPrimeCore p Y = K := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, h.coprime⟩)
  exact h.max _ inferInstance (CFSG.pPrimeCore_coprime_card)

theorem ThompsonFrame.component_data {p : ℕ} {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hF : ThompsonFrame p D) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    L.Normal ∧ center L = ⊥ ∧ centralizer (L : Set X) = ⊥ ∧ IsSimpleGroup L ∧
      (∃ a b : L, a * b ≠ b * a) := by
  classical
  have hp := hF.prime
  have : Fact p.Prime := ⟨hp⟩
  have hZ := ths_center_eq_bot hp hF.pCore_eq_bot hF.pPrimeCore_eq_bot hL
  have huniq : ∀ L' : Subgroup X, CFSG.IsComponent L' → L' = L := fun L' h =>
    hF.component_unique h hL
  have hlayer : CFSG.layer X = L := by
    simp only [CFSG.layer.eq_sSup]
    have : {K : Subgroup X | CFSG.IsComponent K} = {L} :=
      Set.ext fun K => ⟨fun hK => huniq K hK, fun hK => hK ▸ hL⟩
    rw [this, sSup_singleton]
  have hLn : L.Normal := by
    rw [← hlayer]
    have := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  have hF0 : CFSG.fittingSubgroup X = ⊥ := by
    rw [CFSG.Fitting_eq_pcore X p hF.pPrimeCore_eq_bot, hF.pCore_eq_bot]
  have hgf : CFSG.generalizedFitting X = L := by
    rw [CFSG.generalizedFitting, hF0, hlayer, bot_sup_eq]
  have hCle : Subgroup.centralizer (L : Set X) ≤ L := by
    have := CFSG.centralizer_generalizedFitting_le X
    rwa [hgf] at this
  have hC : centralizer (L : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgL : g ∈ L := hCle hg
    have hgc : (⟨g, hgL⟩ : L) ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (mem_centralizer_iff.mp hg h.1 h.2)
    rw [hZ, Subgroup.mem_bot] at hgc
    have := congrArg Subtype.val hgc
    simpa using this
  obtain ⟨-, hS, hN⟩ := hL.1
  let q1 : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hS
  refine ⟨hLn, hZ, hC, q1.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hN
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem ThompsonFrame.dvd_card_join_of_pClosed {p : ℕ} {X : Type} [Group X] [Finite X]
    {D : Subgroup X} (hF : ThompsonFrame p D) {L : Subgroup X} (hLn : L.Normal)
    (hcl : ∀ P : Sylow p (X ⧸ L), (P : Subgroup (X ⧸ L)).Normal) :
    p ∣ Nat.card (invariantTwoJoinIn D L) := by
  have hp := hF.prime
  have : Fact p.Prime := ⟨hp⟩
  have hDp : IsPGroup p D := IsPGroup.of_card hF.card
  obtain ⟨P, hDP⟩ := (hDp.map (QuotientGroup.mk' L)).exists_le_sylow
  set L' : Subgroup X := (P : Subgroup (X ⧸ L)).comap (QuotientGroup.mk' L) with hL'
  have hL'n : L'.Normal := by
    have := hcl P
    exact Subgroup.Normal.comap this _
  have hDL' : D ≤ L' := fun x hx => hDP ⟨x, hx, rfl⟩
  have hjoin : invariantTwoJoinIn D L' ≤ invariantTwoJoinIn D L := by
    refine invariantTwoJoinIn_le_of_forall fun U hUL' hU hDU => ?_
    have hUL : U ≤ L := by
      intro u hu
      rw [← QuotientGroup.eq_one_iff]
      obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
      have h1 : orderOf ((QuotientGroup.mk' L) u) ∣ 2 ^ k := by
        have : (QuotientGroup.mk' L u) ^ 2 ^ k = 1 := by
          rw [← map_pow]
          have : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
          rw [this, map_one]
        exact orderOf_dvd_of_pow_eq_one this
      have hmem : (QuotientGroup.mk' L) u ∈ (P : Subgroup (X ⧸ L)) := hUL' hu
      obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
      have h2 : orderOf ((QuotientGroup.mk' L) u) ∣ p ^ m := by
        rw [← hm]
        exact (Subgroup.orderOf_dvd_natCard _ hmem)
      have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hF.odd))
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    exact le_invariantTwoJoinIn hUL hU hDU
  exact (thr_dvd_card_invariantTwoJoinIn hF hL'n hDL').trans (Subgroup.card_dvd_of_le hjoin)

theorem zj_not_covers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    {K D : Subgroup Y} [K.Normal] (hK : p.Coprime (Nat.card K)) (hD : IsPGroup p D)
    {L : Subgroup (Y ⧸ K)}
    (hL : p ∣ Nat.card (invariantTwoJoinIn (D.map (QuotientGroup.mk' K)) L))
    {Z : Subgroup Y} (hDZ : D ≤ normalizer (Z : Set Y))
    (hZ : ¬ p ∣ Nat.card (invariantTwoJoinIn D (normalizer (Z : Set Y)))) :
    ¬ L ≤ (normalizer (Z : Set Y)).map (QuotientGroup.mk' K) := by
  intro hLN
  have hπs : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  have hker : p.Coprime (Nat.card (QuotientGroup.mk' K).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hK
  have hle : invariantTwoJoinIn (D.map (QuotientGroup.mk' K)) L ≤
      (invariantTwoJoinIn D (normalizer (Z : Set Y))).map (QuotientGroup.mk' K) := by
    refine invariantTwoJoinIn_le_of_forall fun W hWL hW2 hDW => ?_
    obtain ⟨B, hBN, hB2, hDB, hBπ⟩ := exists_invariantTwo_lift hp hp2 (QuotientGroup.mk' K)
      hπs hker hDZ hD hW2 hDW (hWL.trans hLN)
    rw [← hBπ]
    exact Subgroup.map_mono (le_invariantTwoJoinIn hBN hB2 hDB)
  exact hZ (hL.trans ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _)))

def zjq_conjAut {Y : Type} [Group Y] {V : Subgroup Y} {g : Y} (hg : g ∈ normalizer (V : Set Y)) :
    MulAut ↥V where
  toFun x := ⟨g * (x : Y) * g⁻¹, (mem_normalizer_iff.mp hg _).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : Y) * g, by simpa using (mem_normalizer_iff.mp (inv_mem hg) _).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    change g⁻¹ * (g * (x : Y) * g⁻¹) * g = x
    group
  right_inv x := by
    apply Subtype.ext
    change g * (g⁻¹ * (x : Y) * g) * g⁻¹ = x
    group
  map_mul' x y := by
    apply Subtype.ext
    change g * ((x : Y) * (y : Y)) * g⁻¹ = g * (x : Y) * g⁻¹ * (g * (y : Y) * g⁻¹)
    group

theorem zjq_normalizer_le {Y : Type} [Group Y] {V Z : Subgroup Y} (hZV : Z ≤ V)
    (hZc : (Z.subgroupOf V).Characteristic) :
    normalizer (V : Set Y) ≤ normalizer (Z : Set Y) := by
  have key : ∀ g ∈ normalizer (V : Set Y), ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    have hmem : (⟨z, hZV hz⟩ : ↥V) ∈ Z.subgroupOf V := hz
    have hfix := hZc.fixed (zjq_conjAut hg)
    have : zjq_conjAut hg ⟨z, hZV hz⟩ ∈ Z.subgroupOf V := by
      rw [← hfix] at hmem
      exact hmem
    exact this
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC
