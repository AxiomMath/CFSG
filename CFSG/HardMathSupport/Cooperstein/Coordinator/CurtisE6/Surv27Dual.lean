module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E6Rep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

@[expose] abbrev e6n5 : Fin TwistTag.E6.tag.rank := ⟨5, by decide⟩

theorem rho_aux : ∀ s : Fin (Tag.rank .E6),
    (TwistedE6.rhoPerm s = ⟨0, by decide⟩ ↔ s = ⟨5, by decide⟩) ∧
      TwistedE6.rhoPerm (TwistedE6.rhoPerm s) = s := by decide

@[expose] abbrev n0T : Fin (Tag.rank .E6) := ⟨0, by decide⟩
@[expose] abbrev n5T : Fin (Tag.rank .E6) := ⟨5, by decide⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6Chi27_hmT (s : Fin (Tag.rank .E6)) (u : Kˣ) :
    e6Chi27 (e6Data_valid.hm K s u) = ((u ^ (if s = n0T then (1 : ℤ) else 0) : Kˣ) : K) :=
  e6Chi27_hm s u

theorem e6_wt_zeroT (s : Fin (Tag.rank .E6)) :
    e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d)) s = if s = n0T then 1 else 0 :=
  e6_wt_zero_aux s

variable (K) in
@[expose] def e6Graph : ↥(e6Data_valid.minGroup K) →* ↥(e6Data_valid.minGroup K) :=
  TwistedE6.sigma K (RingHom.id K)

theorem e6Graph_xm (i : Fin (Tag.rank .E6)) (c : K) :
    e6Graph K (e6Data_valid.xm K (Pi.single i 1) c) =
      e6Data_valid.xm K (Pi.single (TwistedE6.rhoPerm i) 1) c :=
  TwistedE6.sigma_xm_single (RingHom.id K) i c

theorem e6Graph_nm (i : Fin (Tag.rank .E6)) :
    e6Graph K (e6Data_valid.nm K i) = e6Data_valid.nm K (TwistedE6.rhoPerm i) :=
  TwistedE6.sigma_nm (RingHom.id K) i

theorem e6Graph_hm (i : Fin (Tag.rank .E6)) (t : Kˣ) :
    e6Graph K (e6Data_valid.hm K i t) = e6Data_valid.hm K (TwistedE6.rhoPerm i) t :=
  TwistedE6.sigma_hm (RingHom.id K) i t

theorem e6Graph_involutive (g : ↥(e6Data_valid.minGroup K)) : e6Graph K (e6Graph K g) = g :=
  TwistedE6.sigma_sigma (RingHom.id K) (fun _ => rfl) g

variable (K) in
@[expose] def e6Rep27s : Representation K ↥(e6Data_valid.minGroup K) (Fin e6Data.d →₀ K) :=
  pullRep e6Data_valid (e6Graph K)

theorem e6_hXs (i : Fin Tag.E6.rank) :
    ∃ g ∈ (e6CoverData K).datum.U, e6Graph K g = e6Data_valid.xm K (Pi.single i 1) 1 :=
  ⟨e6Data_valid.xm K (Pi.single (TwistedE6.rhoPerm i) 1) 1, e6_xm_mem_U _, by
    rw [e6Graph_xm, (rho_aux i).2]⟩

theorem e6Y27_mem_fixU_s :
    (e6Y27 : Fin e6Data.d →₀ K) ∈ (e6CoverData K).datum.fixU (e6Rep27s K) :=
  single_mem_fixU (hV := e6Data_valid) (K := K) (e6Graph K) (e6CoverData K).datum e6_hXs
    e6_dominant

@[expose] def e6Chi27s (g : ↥(e6Data_valid.minGroup K)) : K :=
  e6Rep27s K g (e6Y27 : Fin e6Data.d →₀ K) ⟨0, by decide⟩

theorem e6Chi27s_eq (g : ↥(e6Data_valid.minGroup K)) :
    e6Chi27s g = e6Chi27 (e6Graph K g) := rfl

theorem e6Chi27s_hmT (s : Fin (Tag.rank .E6)) (u : Kˣ) :
    e6Chi27s (e6Data_valid.hm K s u) = ((u ^ (if s = n5T then (1 : ℤ) else 0) : Kˣ) : K) := by
  have h := e6Chi27_hmT (K := K) (TwistedE6.rhoPerm s) u
  have e : e6Chi27s (e6Data_valid.hm K s u) =
      e6Chi27 (e6Data_valid.hm K (TwistedE6.rhoPerm s) u) := by
    rw [e6Chi27s_eq]
    exact congrArg e6Chi27 (e6Graph_hm s u)
  rw [e]
  by_cases hs : s = n5T
  · have hr : TwistedE6.rhoPerm s = n0T := ((rho_aux s).1).2 hs
    rw [if_pos hs]
    rw [if_pos hr] at h
    exact h
  · have hr : ¬ TwistedE6.rhoPerm s = n0T := fun h' => hs (((rho_aux s).1).1 h')
    rw [if_neg hs]
    rw [if_neg hr] at h
    exact h

theorem e6Chi27s_hm (s : Fin TwistTag.E6.tag.rank) (u : Kˣ) :
    e6Chi27s (e6Data_valid.hm K s u) =
      ((u ^ (if s = e6n5 then (1 : ℤ) else 0) : Kˣ) : K) := e6Chi27s_hmT s u

theorem e6Rep27s_H (h : ↥(e6Data_valid.minGroup K))
    (hh : h ∈ (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K)) :
    e6Rep27s K h e6Y27 = e6Chi27s h • e6Y27 :=
  pullRep_H_smul (hV := e6Data_valid) (K := K) (e6Graph K) (e6CoverData K).datum e6_hXs
    e6_dominant hh

theorem e6_heckeT_ys (s : Fin TwistTag.E6.tag.rank) [Fintype K] :
    (e6CoverData K).datum.heckeT (e6Rep27s K) s e6Y27 =
      ∑ c : K, minRep e6Data_valid K (e6Data_valid.xm K (Pi.single (TwistedE6.rhoPerm s) 1) c *
        e6Data_valid.nm K (TwistedE6.rhoPerm s)) e6Y27 := by
  rw [(e6CoverRankOne K).heckeT_datum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have key : ∀ s' : Fin (Tag.rank .E6), e6Graph K (e6Data_valid.xm K (Pi.single s' 1) c *
      e6Data_valid.nm K s') = e6Data_valid.xm K (Pi.single (TwistedE6.rhoPerm s') 1) c *
        e6Data_valid.nm K (TwistedE6.rhoPerm s') := fun s' => by
    rw [map_mul, e6Graph_xm, e6Graph_nm]
  have h1 : e6Rep27s K ((e6CoverRankOne K).x s c * (e6CoverData K).nhat s) e6Y27 =
      minRep e6Data_valid K (e6Graph K (e6Data_valid.xm K (Pi.single s 1) c *
        e6Data_valid.nm K s)) e6Y27 :=
    congrArg (fun z => minRep e6Data_valid K (e6Graph K z) e6Y27)
      (congrArg (fun z => e6Data_valid.xm K (Pi.single s 1) c * z) (nhat_e6 s))
  exact h1.trans (congrArg (fun z => minRep e6Data_valid K z e6Y27) (key s))

theorem e6Rep27s_isCoverType :
    IsCoverType (e6CoverRankOne K) (e6Rep27s K) e6Y27 e6Chi27s (Finset.univ.erase e6n5) := by
  have := Fintype.ofFinite K
  refine ⟨e6Y27_mem_fixU_s, e6Y27_ne_zero, e6Rep27s_H, fun s => ?_⟩
  by_cases hs : s = e6n5
  · subst hs
    refine ⟨fun h => absurd rfl (Finset.mem_erase.1 h).1, fun h => ?_⟩
    exfalso
    obtain ⟨h1, h2⟩ := h
    have h1' : ∀ u : Kˣ, (u : K) = 1 := fun u => by
      have := h1 u
      change e6Chi27s (e6Data_valid.hm K e6n5 u) = 1 at this
      rwa [e6Chi27s_hm, if_pos rfl, zpow_one] at this
    have hr : TwistedE6.rhoPerm e6n5 = e6n0 := ((rho_aux e6n5).1).2 rfl
    have h3 : (e6CoverData K).datum.heckeT (e6Rep27s K) e6n5 e6Y27 = -(∑ c : K, c) • e6Y27 :=
      (e6_heckeT_ys e6n5).trans (by
        rw [hr]
        exact sum_xm_nm_of_wt_one (hV := e6Data_valid) (a₀ := ⟨0, by decide⟩) (s := e6n0)
          e6_wt_one)
    have h4 : -(∑ c : K, c) • (e6Y27 : Fin e6Data.d →₀ K) = 0 := h3.symm.trans h2
    rw [sum_eq_one_of_units_eq_one h1'] at h4
    exact e6Y27_ne_zero (by simpa using h4)
  · have hne : ¬ TwistedE6.rhoPerm s = n0T := fun h => hs (((rho_aux s).1).1 h)
    have hw : e6Data.wt (↑(⟨0, by decide⟩ : Fin e6Data.d)) (TwistedE6.rhoPerm s) = 0 := by
      have := e6_wt_zeroT (TwistedE6.rhoPerm s)
      rw [if_neg hne] at this
      exact this
    refine ⟨fun _ => ⟨fun u => ?_, ?_⟩, fun _ => Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩⟩
    · change e6Chi27s (e6Data_valid.hm K s u) = 1
      rw [e6Chi27s_hm, if_neg hs, zpow_zero]
      rfl
    · exact (e6_heckeT_ys s).trans (sum_xm_nm_of_wt_zero (hV := e6Data_valid)
        (a₀ := ⟨0, by decide⟩) (s := TwistedE6.rhoPerm s) hw)

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min
