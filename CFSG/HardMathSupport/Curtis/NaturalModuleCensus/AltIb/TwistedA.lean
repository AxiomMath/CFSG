module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Shared
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.TwistedAPlus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.TwistedACore
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedACore

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

theorem altIbBarAt_twistedA {G : Type} [Group G] [Finite G] {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hG : IsLieOf (IdxTwistedANoPlus p) G) : AltIbBarAt G p := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hG
  cases d with
  | twistedA r q =>
    obtain ⟨hq2, hnp⟩ := hd
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    have hpq : ¬ p ∣ 2 ^ q.exponent + 1 := by rwa [hqc] at hnp
    have hc := SQTK.statedClassicalModel_twistedA r q hv e
    rw [hq2] at hc
    obtain ⟨⟨-, hf, -, -⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
    have h := ToralCensus.unitaryFieldData_of_card_eq_sq hcard hf
    have : CharP K 2 := h.charP
    have hn : 1 ≤ r + 1 := by omega
    let φ : unitaryPSU h (r + 1) ≃* G := (unitaryPSUEquiv h hn).trans e'.symm
    let π : unitarySU 2 q.exponent K (r + 1) →* G :=
      φ.toMonoidHom.comp (unitaryProj h (r + 1))
    have hπ : Function.Surjective π :=
      φ.surjective.comp (unitaryProj_surjective h (r + 1))
    have hπker : ∀ g, π g = 1 ↔ g ∈ unitaryScalars h (r + 1) := fun g => by
      change φ (unitaryProj h (r + 1) g) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]
    have hkereq : π.ker = unitaryScalars h (r + 1) := by
      ext g
      exact hπker g
    have hker : π.ker ≤ Subgroup.center (unitarySU 2 q.exponent K (r + 1)) :=
      hkereq ▸ unitaryScalars_le_center h (r + 1)
    have hpk : ¬ p ∣ Nat.card π.ker := by
      rw [hkereq, card_unitaryScalars h hn]
      exact fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
    intro Jb _ _ _ hA1 hA2 x hxp hfix V E _ hVC hV hEV hEel hEcard
    obtain ⟨t, htx, htp, Vh, Eh, hVh, hVhC, -, hEhV, hEhel, -, hEhcard⟩ :=
      exists_lift_data hp hπ hker hpk hxp hVC hV hEV hEel
    have hsq : Squarefree (minpoly K (Matrix.mulVecLin
        ((t : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K))) := by
      have h1 : (t : GL (Fin (r + 1)) K) ^ p =
          Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (1 : Kˣ) := by
        rw [← Subgroup.coe_pow, htp, map_one]
        rfl
      have h2 := ToralCensus.squarefree_minpoly_toLin_of_pow_eq_scalar (t : GL (Fin (r + 1)) K)
        (m := p) (ToralCensus.natCast_ne_zero_of_odd_of_charTwo (hp.odd_of_ne_two hp2)) h1
      rwa [show ((Matrix.GeneralLinearGroup.toLin (t : GL (Fin (r + 1)) K) :
        Module.End K (Fin (r + 1) → K))) = Matrix.mulVecLin
          ((t : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) from
        Matrix.GeneralLinearGroup.coe_toLin _] at h2
    exact false_of_blocks_su hcard hf hp57 hpq π hker hpk Jb hA1 hA2 t hsq htp
      (by rw [htx]; exact hfix) Vh Eh hVhC hVh hEhV hEhel.2 (hEhcard.trans hEcard)
  | _ => exact hd.elim

section Cell


theorem altIbCell_twistedA (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) : AltIbCell (IsLieOf IdxTwistedA) := by
  intro Y _ _ L J hL htype hX hpar hJL hnB p hp57 hAlt x hxL hxp hfix W hW hWN hWx hE
  obtain ⟨E, hEW, hEel, hEcard⟩ := hE
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  rcases isLieOf_twistedA_cases hp5 hX with h | h
  · exact altIbCell_twistedA_plus hGA hL htype hpar hJL hnB hp57 hxL hxp hfix h
  · have : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
    exact altIb_reduce_to_bar hSch ⟨hL, htype, hpar, hJL, hnB⟩ hp57 hAlt
      (not_dvd_card_center_twistedA hGA hp hp2 h) hxL hxp hfix hW hWN hWx hEW hEel hEcard
      (altIbBarAt_twistedA hp57 h)

end Cell

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
