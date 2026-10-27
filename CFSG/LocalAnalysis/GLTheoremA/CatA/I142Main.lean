module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Lift2
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isElemAbelian_subgroupOf_of {X : Type} [Group X] {p : ℕ} {E N : Subgroup X}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf N) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have ha : (a : X) ∈ E := Subgroup.mem_subgroupOf.1 a.2
    have hb : (b : X) ∈ E := Subgroup.mem_subgroupOf.1 b.2
    exact Subtype.ext (Subtype.ext (isElemAbelian_commute hE ha hb))
  · have hx' : (x : X) ∈ E := Subgroup.mem_subgroupOf.1 hx
    have := hE.2 x hx'
    exact Subtype.ext (by simpa using this)

theorem isElemAbelian_map_of {X Y : Type} [Group X] [Group Y] {p : ℕ} {A : Subgroup X}
    (f : X →* Y) (hA : IsElemAbelian p A) : IsElemAbelian p (A.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.1 b.2
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← hxa, ← hzb, ← map_mul, ← map_mul, isElemAbelian_commute hA hx hz]
  · obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    rw [← hxy, ← map_pow, hA.2 x hx, map_one]

theorem exists_component_dvd_of_pComp [Finite G] {p : ℕ} [hp : Fact p.Prime] {K E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (K : Set G)) (hE : IsElemAbelian p E)
    {Y J₀ : Subgroup G} (hY : Y ≤ K ⊓ Subgroup.centralizer (E : Set G))
    (hJ₀ : GLAPComponent p Y J₀)
    (hS : ∀ P : Subgroup (PSimple p K), P ≤ centFix (Ebar p K E) → ⁅P, P⁆ = P →
      P ≤ GLALayer (centFix (Ebar p K E))) :
    ∃ M : Subgroup (PSimple p K), CFSG.Open.IsComponentOf M (centFix (Ebar p K E)) ∧
      p ∣ Nat.card ↥M := by
  classical
  have hY' : (Y.subgroupOf K).map K.subtype = Y := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 (hY.trans inf_le_left)
  have hJ₀' : GLAPComponent p ((Y.subgroupOf K).map K.subtype) J₀ := by
    rw [hY']; exact hJ₀
  have hker0 : p.Coprime (Nat.card ↥((Y.subgroupOf K) ⊓ K.subtype.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff K.subtype).2 K.subtype_injective, inf_bot_eq,
      Subgroup.card_bot]
    exact Nat.coprime_one_right p
  obtain ⟨J₁, hJ₁, -⟩ := exists_glaPComponent_map_eq hp.out K.subtype hker0 hJ₀'
  have hker1 : p.Coprime (Nat.card ↥((Y.subgroupOf K) ⊓ (pQuotHom p K).ker)) :=
    coprime_card_inf_ker_pQuotHom hp.out K _
  have hJb : GLAPComponent p ((Y.subgroupOf K).map (pQuotHom p K))
      (J₁.map (pQuotHom p K)) := glaPComponent_map hp.out (pQuotHom p K) hker1 hJ₁
  have hsub1 : Y.subgroupOf K ≤ (K ⊓ Subgroup.centralizer (E : Set G)).subgroupOf K :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hY (Subgroup.mem_subgroupOf.1 hx))
  have hJble : J₁.map (pQuotHom p K) ≤ Cbar p K E :=
    hJb.1.trans (Subgroup.map_mono hsub1)
  have hJbperf : ⁅J₁.map (pQuotHom p K), J₁.map (pQuotHom p K)⁆ = J₁.map (pQuotHom p K) :=
    glaPComponent_perfect hJb
  have hJbq := isQuasisimple_pQuot_of_glaPComponent hp.out hJb
  let π : PQuot p K →* PSimple p K := QuotientGroup.mk' (Subgroup.center (PQuot p K))
  have hPS_le : (J₁.map (pQuotHom p K)).map π ≤ centFix (Ebar p K E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact cbar_le_centFix x (hJble hx)
  have hPS_perf : ⁅(J₁.map (pQuotHom p K)).map π, (J₁.map (pQuotHom p K)).map π⁆ =
      (J₁.map (pQuotHom p K)).map π := by
    rw [← Subgroup.map_commutator, hJbperf]
  have hpP : p ∣ Nat.card ↥((J₁.map (pQuotHom p K)).map π) := by
    let f : ↥(J₁.map (pQuotHom p K)) →* ↥((J₁.map (pQuotHom p K)).map π) :=
      (π.comp (J₁.map (pQuotHom p K)).subtype).codRestrict _
        (fun t => Subgroup.mem_map_of_mem π t.2)
    have hf : Function.Surjective f := by
      intro s
      obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.1 s.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxs⟩
    have hPidx : Nat.card ↥((J₁.map (pQuotHom p K)).map π) = f.ker.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toEquiv
    have hbur := dvd_card_center_quot_of_pPrimeCore_eq_bot (p := p) hJbq
      (CFSG.pPrimeCore_quotient_eq_bot hp.out)
    have hbur' : p ∣ (Subgroup.center (↥(J₁.map (pQuotHom p K)) ⧸
        GLAPPrimeCore p ↥(J₁.map (pQuotHom p K)))).index := by
      rw [Subgroup.index_eq_card]
      exact hbur
    let Zt : Subgroup ↥(J₁.map (pQuotHom p K)) :=
      (Subgroup.center (↥(J₁.map (pQuotHom p K)) ⧸
        GLAPPrimeCore p ↥(J₁.map (pQuotHom p K)))).comap
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(J₁.map (pQuotHom p K))))
    have hZt : f.ker ≤ Zt := by
      intro t ht
      rw [MonoidHom.mem_ker] at ht
      have ht' : π t.1 = 1 := congrArg Subtype.val ht
      have htc : t.1 ∈ Subgroup.center (PQuot p K) := (QuotientGroup.eq_one_iff _).1 ht'
      have htT : t ∈ Subgroup.center ↥(J₁.map (pQuotHom p K)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.1 htc g.1)
      exact map_mem_center_of_surj _ (QuotientGroup.mk'_surjective _) htT
    have hidx : Zt.index = (Subgroup.center (↥(J₁.map (pQuotHom p K)) ⧸
        GLAPPrimeCore p ↥(J₁.map (pQuotHom p K)))).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [← hidx] at hbur'
    rw [hPidx]
    exact dvd_trans hbur' (Subgroup.index_dvd_of_le hZt)
  by_contra hno
  have hno' : ∀ M : Subgroup (PSimple p K), CFSG.Open.IsComponentOf M (centFix (Ebar p K E)) →
      ¬ p ∣ Nat.card ↥M := fun M hM hd => hno ⟨M, hM, hd⟩
  have hlay := not_dvd_card_sSup_components (centFix (Ebar p K E)) hno'
  have hle := hS _ hPS_le hPS_perf
  exact hlay (dvd_trans hpP (Subgroup.card_dvd_of_le hle))

theorem i142At_of_E (h : LieSemisimpleCentE) (G : Type) [Group G] [Finite G] :
    I142At G := by
  unfold I142At
  intro p' X K E Y hp hp2 hX hK hS hE hEN hY hYlay
  haveI : Fact p'.Prime := ⟨hp⟩
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Subgroup G, GLAPComponent p' Y J₀ := by
    by_contra hne
    apply hYlay
    apply le_bot_iff.mp
    apply sSup_le
    intro L hL
    exact absurd ⟨L, show GLAPComponent p' Y L from hL⟩ hne
  have hsimple : IsSimpleGroup (PSimple p' K) := (chev_pSimple_simple_nonabelian hp hK).1
  have hnc : ∃ a b : PSimple p' K, a * b ≠ b * a := (chev_pSimple_simple_nonabelian hp hK).2
  have hEbar : IsElemAbelian p' (Ebar p' K E) :=
    isElemAbelian_map_of (chevAut p' K) (isElemAbelian_subgroupOf_of hE)
  have hS' : ∀ P : Subgroup (PSimple p' K), P ≤ centFix (Ebar p' K E) → ⁅P, P⁆ = P →
      P ≤ GLALayer (centFix (Ebar p' K E)) :=
    h (PSimple p' K) hsimple hnc hS p' hp hp2 (Ebar p' K E) hEbar
  obtain ⟨M, hM, hpM⟩ := exists_component_dvd_of_pComp hEN hE hY hJ₀ hS'
  exact glaPLayer_ne_bot_of_component hEN hE hM hpM

end CFSG.LocalAnalysis.GLTheoremA.I142
