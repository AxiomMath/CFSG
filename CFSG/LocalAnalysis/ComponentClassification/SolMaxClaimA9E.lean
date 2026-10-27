module

public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup
open scoped commutatorElement

theorem eq_top_of_sup_center_of_perfect {H : Type*} [Group H] (hperf : commutator H = ⊤)
    {U : Subgroup H} (hU : U ⊔ center H = ⊤) : U = ⊤ := by
  have hcl : ∀ x y z : H, z ∈ center H → ⁅x * z, y⁆ = ⁅x, y⁆ := by
    intro x y z hz
    rw [commutatorElement_def, commutatorElement_def, mul_assoc x z y,
      ← mem_center_iff.mp hz y, ← mul_assoc]
    group
  have hcr : ∀ x y z : H, z ∈ center H → ⁅x, y * z⁆ = ⁅x, y⁆ := by
    intro x y z hz
    rw [← commutatorElement_inv, hcl _ _ _ hz, commutatorElement_inv]
  have hprod : ∀ g : H, ∃ m ∈ U, ∃ z ∈ center H, g = m * z := by
    intro g
    have hg : g ∈ (↑(U ⊔ center H) : Set H) := by
      rw [hU]
      exact mem_top g
    rw [mul_normal] at hg
    obtain ⟨m, hm, z, hz, rfl⟩ := Set.mem_mul.mp hg
    exact ⟨m, hm, z, hz, rfl⟩
  rw [eq_top_iff, ← hperf, _root_.commutator_def, commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := hprod x
  obtain ⟨m', hm', z', hz', rfl⟩ := hprod y
  rw [hcl _ _ _ hz, hcr _ _ _ hz', commutatorElement_def]
  exact U.mul_mem (U.mul_mem (U.mul_mem hm hm') (U.inv_mem hm)) (U.inv_mem hm')

theorem center_coreQuot_eq_bot_of_le {G : Type*} [Group G] [Finite G] (hG : commutator G = ⊤)
    {T : Subgroup G} {k : ℕ} (hk : 5 ≤ k)
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin k))
    (eG : G ⧸ Open.fusionZStar G ≃* alternatingGroup (Fin k)) :
    center (G ⧸ pPrimeCore 2 G) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 G with hOdef
  set q : G →* G ⧸ O := QuotientGroup.mk' O with hqdef
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective O
  set c : (G ⧸ O) ⧸ center (G ⧸ O) ≃* alternatingGroup (Fin k) :=
    (Sol78.coreQuotientCenterEquiv G).trans eG with hcdef
  set p : G ⧸ O →* alternatingGroup (Fin k) :=
    c.toMonoidHom.comp (QuotientGroup.mk' (center (G ⧸ O))) with hpdef
  have hpker : ∀ g, p g = 1 ↔ g ∈ center (G ⧸ O) := fun g => by
    rw [hpdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set φ : ↥T →* alternatingGroup (Fin k) := p.comp (q.comp T.subtype) with hφdef
  set OT := pPrimeCore 2 ↥T with hOTdef
  set πT : ↥T →* alternatingGroup (Fin k) :=
    eT.toMonoidHom.comp (QuotientGroup.mk' OT) with hπTdef
  have hπTs : Function.Surjective πT := eT.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπTker : ∀ x, πT x = 1 ↔ x ∈ OT := fun x => by
    rw [hπTdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsimple : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have hperfA : Group.IsPerfect (alternatingGroup (Fin k)) := Sol78.alt_isPerfect hk
  have hTO : O.comap T.subtype ≤ OT := by
    refine le_sSup ⟨Normal.comap inferInstance T.subtype, ?_⟩
    have h1 : Nat.card ↥(O.comap T.subtype) ∣ Nat.card ↥O := by
      let g : ↥(O.comap T.subtype) →* ↥O :=
        (T.subtype.comp (O.comap T.subtype).subtype).codRestrict O fun x => x.2
      refine card_dvd_of_injective g fun a b h => ?_
      have h' : ((a : ↥T) : G) = ((b : ↥T) : G) := congrArg (fun z : ↥O => (z : G)) h
      exact Subtype.ext (Subtype.ext h')
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hK : φ.ker ≤ OT := by
    have hnorm : (φ.ker.map πT).Normal := Normal.map inferInstance πT hπTs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map πT) with h | h
    · intro x hx
      have h1 : πT x ∈ φ.ker.map πT := ⟨x, hx, rfl⟩
      rw [h, mem_bot] at h1
      exact (hπTker x).mp h1
    · exfalso
      have hcomm : ⁅φ.ker, φ.ker⁆ ≤ OT := by
        rw [commutator_le]
        intro a ha b hb
        apply hTO
        rw [mem_comap]
        have ha' : q (T.subtype a) ∈ center (G ⧸ O) := (hpker _).mp ha
        have hb' : q (T.subtype b) ∈ center (G ⧸ O) := (hpker _).mp hb
        have h1 : q (T.subtype ⁅a, b⁆) = 1 := by
          rw [map_commutatorElement, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact (mem_center_iff.mp ha' _).symm
        exact (QuotientGroup.eq_one_iff _).mp h1
      have h2 : (⁅φ.ker, φ.ker⁆).map πT = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        rw [mem_bot]
        exact (hπTker x).mpr (hcomm hx)
      rw [map_commutator, h, ← _root_.commutator_def, hperfA.commutator_eq_top] at h2
      exact bot_ne_top h2.symm
  have hsurj : Function.Surjective φ := by
    have h1 : Nat.card ↥T = Nat.card φ.range * Nat.card φ.ker := by
      rw [card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have h2 : Nat.card ↥T = Nat.card (alternatingGroup (Fin k)) * Nat.card OT := by
      rw [card_eq_card_quotient_mul_card_subgroup OT, Nat.card_congr eT.toEquiv]
    have h3 : Nat.card φ.ker ≤ Nat.card OT := card_le_of_le hK
    have h4 : Nat.card (alternatingGroup (Fin k)) ≤ Nat.card φ.range := by
      have h5 : 0 < Nat.card OT := Nat.card_pos
      have h6 : Nat.card (alternatingGroup (Fin k)) * Nat.card OT ≤
          Nat.card φ.range * Nat.card OT := by
        rw [← h2, h1]
        exact Nat.mul_le_mul_left _ h3
      exact Nat.le_of_mul_le_mul_right h6 h5
    exact MonoidHom.range_eq_top.mp (eq_top_of_le_card _ h4)
  have hGb : commutator (G ⧸ O) = ⊤ := by
    have h1 := map_commutator (⊤ : Subgroup G) ⊤ q
    rw [← _root_.commutator_def, hG, map_top_of_surjective q hqs, ← _root_.commutator_def] at h1
    exact h1.symm
  have hsup : T.map q ⊔ center (G ⧸ O) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hx⟩ := hsurj (p g)
    have hz : (q (T.subtype x))⁻¹ * g ∈ center (G ⧸ O) := by
      rw [← hpker, map_mul, map_inv]
      change (φ x)⁻¹ * p g = 1
      rw [hx, inv_mul_cancel]
    have h1 : g = q (T.subtype x) * ((q (T.subtype x))⁻¹ * g) := by group
    rw [h1]
    exact mul_mem (mem_sup_left ⟨_, x.2, rfl⟩) (mem_sup_right hz)
  have hTb : T.map q = ⊤ := eq_top_of_sup_center_of_perfect hGb hsup
  have hZle : center (G ⧸ O) ≤ (OT.map T.subtype).map q := by
    intro z hz
    have hzT : z ∈ T.map q := hTb ▸ mem_top z
    obtain ⟨g, hgT, rfl⟩ := hzT
    have hx : (⟨g, hgT⟩ : ↥T) ∈ φ.ker := (hpker _).mpr hz
    exact ⟨g, ⟨⟨g, hgT⟩, hK hx, rfl⟩, rfl⟩
  have hZodd : Nat.Coprime 2 (Nat.card ↥(center (G ⧸ O))) := by
    have h1 : Nat.card ↥(center (G ⧸ O)) ∣ Nat.card ↥OT := by
      refine (card_dvd_of_le hZle).trans ((card_map_dvd _ _).trans ?_)
      rw [card_map_of_injective T.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  exact (pPrimeCore_eq_bot_iff.mp (pPrimeCore_quotient_eq_bot Nat.prime_two)) _
    inferInstance hZodd

variable {X : Type} [Group X]

theorem nonempty_coreQuot_of_le [Finite X] {M T : Subgroup X} (hTM : T ≤ M) (hM : ⁅M, M⁆ = M)
    {k : ℕ} (hk : 5 ≤ k) (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin k))
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin k)) :
    Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin k)) := by
  have hG : commutator ↥M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hM
  let eT' : ↥(T.subgroupOf M) ⧸ pPrimeCore 2 ↥(T.subgroupOf M) ≃* alternatingGroup (Fin k) :=
    (Sol78.coreQuotCongr (subgroupOfEquivOfLe hTM)).trans eT
  have hZ : Open.fusionZStar ↥M = pPrimeCore 2 ↥M :=
    (Sol78.fusionZStar_eq_iff _).mpr (center_coreQuot_eq_bot_of_le hG hk eT' eM)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eM⟩

end CFSG.ComponentClassification.SolMax
