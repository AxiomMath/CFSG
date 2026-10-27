module

public import CFSG.Quasithin.H13.A5S1327zn
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Offender

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open Equiv Equiv.Perm
open scoped Pointwise

variable {X : Type} [Group X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

namespace SixCtx

variable (c : SixCtx T L)

abbrev imgS (K : Subgroup (X ⧸ gnC T)) : Subgroup (Perm (Fin 7)) :=
  (K.subgroupOf (nLs T L)).map c.θs

theorem mem_imgS {K : Subgroup (X ⧸ gnC T)} (hK : K ≤ nLs T L) {σ : Perm (Fin 7)} :
    σ ∈ c.imgS K ↔ ∃ (y : X ⧸ gnC T) (hy : y ∈ K), c.θs ⟨y, hK hy⟩ = σ := by
  constructor
  · rintro ⟨⟨y, hy'⟩, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hK hy⟩, hy, rfl⟩

theorem imgS_map (R : Subgroup X) (hR : R ≤ nL T L) :
    c.imgS (R.map (QuotientGroup.mk' (gnC T))) = c.img R := by
  ext σ
  have hRs : R.map (QuotientGroup.mk' (gnC T)) ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hR hr
  rw [c.mem_imgS hRs, c.mem_img hR]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, rfl⟩

@[expose] def wP (P : Subgroup (Perm (Fin 7))) : Subgroup (X ⧸ gnC T) :=
  (P.comap ((alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom)).map L.subtype

theorem mem_wP {P : Subgroup (Perm (Fin 7))} {x : X ⧸ gnC T} :
    x ∈ c.wP P ↔ ∃ hx : x ∈ L, ((c.eL ⟨x, hx⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ P := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyP, rfl⟩
    exact ⟨hy, hyP⟩
  · rintro ⟨hx, hxP⟩
    exact ⟨⟨x, hx⟩, hxP, rfl⟩

theorem wP_le_L (P : Subgroup (Perm (Fin 7))) : c.wP P ≤ L := fun _ hx => ((c.mem_wP).1 hx).1

theorem θs_of_mem_L {y : ↥(nLs T L)} (hy : (y : X ⧸ gnC T) ∈ L) :
    c.θs y = c.eL ⟨y, hy⟩ :=
  c.hθsL y ⟨y, hy⟩ rfl

theorem minParabolic_wP {Rs : Subgroup (X ⧸ gnC T)} (hRL : Rs ≤ nLs T L) (hRp : IsPGroup 2 Rs)
    {Q P : Subgroup (Perm (Fin 7))} (hQ : c.imgS Rs = Q) (hQP : Q ≤ P)
    (hcard : Nat.card P = 3 * Nat.card Q) (hodd : ∃ q ∈ Q, q ∉ alternatingGroup (Fin 7))
    (hnn : ∃ g ∈ P ⊓ alternatingGroup (Fin 7), ∃ e ∈ Q, g * e * g⁻¹ ∉ Q)
    (hQL : ∀ σ ∈ Q ⊓ alternatingGroup (Fin 7), ∃ (y : X ⧸ gnC T) (hy : y ∈ Rs ⊓ L),
      c.θs ⟨y, hRL hy.1⟩ = σ) :
    MinParabolic (c.wP P ⊔ Rs) Rs Rs ∧ c.imgS (c.wP P ⊔ Rs) = P ∧
      ∀ (h : X ⧸ gnC T) (hh : h ∈ c.wP P ⊔ Rs), c.θs ⟨h, sup_le ((c.wP_le_L P).trans
        Subgroup.le_normalizer) hRL hh⟩ = 1 → h ∈ Rs := by
  classical
  set W := c.wP P with hW
  have hWL : W ≤ nLs T L := (c.wP_le_L P).trans Subgroup.le_normalizer
  have hHL : W ⊔ Rs ≤ nLs T L := sup_le hWL hRL
  have hRW : Rs ≤ Subgroup.normalizer (W : Set (X ⧸ gnC T)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ Rs, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      intro g hg w hw
      obtain ⟨hwL, hwP⟩ := (c.mem_wP).1 hw
      have hgw : g * w * g⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hRL hg) w).1 hwL
      refine (c.mem_wP).2 ⟨hgw, ?_⟩
      rw [c.hθs ⟨g, hRL hg⟩ ⟨w, hwL⟩ ⟨_, hgw⟩ rfl]
      have hgQ : c.θs ⟨g, hRL hg⟩ ∈ Q := hQ ▸ ⟨⟨g, hRL hg⟩, hg, rfl⟩
      exact P.mul_mem (P.mul_mem (hQP hgQ) hwP) (P.inv_mem (hQP hgQ))
    intro w
    constructor
    · exact key r hr w
    · intro h
      have := key r⁻¹ (Rs.inv_mem hr) _ h
      simpa [mul_assoc] using this
  have hmul : ((W : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) =
      ((W ⊔ Rs : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left W Rs hRW).symm
  have hdecomp : ∀ h ∈ W ⊔ Rs, ∃ w ∈ W, ∃ r ∈ Rs, h = w * r := by
    intro h hh
    have : h ∈ ((W : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) := by rw [hmul]; exact hh
    obtain ⟨w, hw, r, hr, rfl⟩ := this
    exact ⟨w, hw, r, hr, rfl⟩
  have hθRQ : ∀ (r : X ⧸ gnC T) (hr : r ∈ Rs), c.θs ⟨r, hRL hr⟩ ∈ Q := fun r hr =>
    hQ ▸ ⟨⟨r, hRL hr⟩, hr, rfl⟩
  have hker : ∀ (h : X ⧸ gnC T) (hh : h ∈ W ⊔ Rs), c.θs ⟨h, hHL hh⟩ = 1 → h ∈ Rs := by
    intro h hh h1
    obtain ⟨w, hw, r, hr, rfl⟩ := hdecomp h hh
    obtain ⟨hwL, -⟩ := (c.mem_wP).1 hw
    have hθ : c.θs ⟨w, hWL hw⟩ * c.θs ⟨r, hRL hr⟩ = 1 := by
      rw [← map_mul]; exact h1
    have hθw : c.θs ⟨w, hWL hw⟩ = c.eL ⟨w, hwL⟩ := c.θs_of_mem_L hwL
    have hrA : c.θs ⟨r, hRL hr⟩ ∈ Q ⊓ alternatingGroup (Fin 7) := by
      refine ⟨hθRQ r hr, ?_⟩
      have : c.θs ⟨r, hRL hr⟩ = (c.θs ⟨w, hWL hw⟩)⁻¹ := eq_inv_of_mul_eq_one_right hθ
      rw [this, hθw]
      exact (alternatingGroup (Fin 7)).inv_mem (c.eL ⟨w, hwL⟩).2
    obtain ⟨y, hy, hyθ⟩ := hQL _ hrA
    have hwy : w * y ∈ L := L.mul_mem hwL hy.2
    have hθwy : c.θs ⟨w * y, hHL (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
        (Subgroup.mem_sup_right hy.1))⟩ = 1 := by
      have e : (⟨w * y, hHL (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
          (Subgroup.mem_sup_right hy.1))⟩ : ↥(nLs T L)) = ⟨w, hWL hw⟩ * ⟨y, hRL hy.1⟩ := rfl
      rw [e, map_mul, hyθ, hθ]
    have h2 : (c.eL ⟨w * y, hwy⟩ : Perm (Fin 7)) = 1 := by
      rw [← c.θs_of_mem_L (y := ⟨w * y, hHL (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
        (Subgroup.mem_sup_right hy.1))⟩) hwy]
      exact hθwy
    have h3 : c.eL ⟨w * y, hwy⟩ = 1 := Subtype.ext h2
    have h4 : (⟨w * y, hwy⟩ : ↥L) = 1 := c.eL.injective (h3.trans (map_one c.eL).symm)
    have h5 : w * y = 1 := congrArg Subtype.val h4
    have hwR : w ∈ Rs := by
      rw [eq_inv_of_mul_eq_one_left h5]
      exact Rs.inv_mem hy.1
    exact Rs.mul_mem hwR hr
  have himg : c.imgS (W ⊔ Rs) = P := by
    apply le_antisymm
    · rintro _ ⟨⟨h, hh'⟩, hh, rfl⟩
      obtain ⟨w, hw, r, hr, rfl⟩ := hdecomp h hh
      obtain ⟨hwL, hwP⟩ := (c.mem_wP).1 hw
      have e : (⟨w * r, hh'⟩ : ↥(nLs T L)) = ⟨w, hWL hw⟩ * ⟨r, hRL hr⟩ := rfl
      rw [e, map_mul, c.θs_of_mem_L hwL]
      exact P.mul_mem hwP (hQP (hθRQ r hr))
    · intro σ hσ
      have hA : ∀ τ ∈ P, τ ∈ alternatingGroup (Fin 7) → τ ∈ c.imgS (W ⊔ Rs) := by
        intro τ hτP hτA
        set w : ↥L := c.eL.symm ⟨τ, hτA⟩ with hwdef
        have hwW : (w : X ⧸ gnC T) ∈ W := by
          refine (c.mem_wP).2 ⟨w.2, ?_⟩
          rw [show (⟨(w : X ⧸ gnC T), w.2⟩ : ↥L) = w from rfl, hwdef, MulEquiv.apply_symm_apply]
          exact hτP
        refine ⟨⟨w, hWL hwW⟩, Subgroup.mem_sup_left hwW, ?_⟩
        rw [c.θs_of_mem_L w.2]
        rw [show (⟨(w : X ⧸ gnC T), w.2⟩ : ↥L) = w from rfl, hwdef, MulEquiv.apply_symm_apply]
      by_cases hσA : σ ∈ alternatingGroup (Fin 7)
      · exact hA σ hσ hσA
      · obtain ⟨q, hqQ, hqA⟩ := hodd
        have hsq : σ * q⁻¹ ∈ alternatingGroup (Fin 7) := by
          rw [Equiv.Perm.mem_alternatingGroup] at hσA hqA ⊢
          rw [map_mul, map_inv]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
          · exact absurd h hσA
          rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h' | h'
          · exact absurd h' hqA
          rw [h, h']; decide
        have h1 := hA (σ * q⁻¹) (P.mul_mem hσ (P.inv_mem (hQP hqQ))) hsq
        have h2 : q ∈ c.imgS (W ⊔ Rs) := by
          rw [← hQ] at hqQ
          obtain ⟨⟨r, hr'⟩, hr, rfl⟩ := hqQ
          exact ⟨⟨r, hr'⟩, Subgroup.mem_sup_right hr, rfl⟩
        have := (c.imgS (W ⊔ Rs)).mul_mem h1 h2
        simpa using this
  have hRH : Rs ≤ W ⊔ Rs := le_sup_right
  have h3 : Rs.relIndex (W ⊔ Rs) = 3 := by
    let f : ↥(W ⊔ Rs) →* Perm (Fin 7) := c.θs.comp (Subgroup.inclusion hHL)
    have hkerf : f.ker ≤ Rs.subgroupOf (W ⊔ Rs) := by
      intro h hh
      exact hker h h.2 hh
    have hmap : (Rs.subgroupOf (W ⊔ Rs)).map f = Q := by
      rw [← hQ]
      ext σ
      constructor
      · rintro ⟨⟨r, hr'⟩, hr, rfl⟩
        exact ⟨⟨r, hHL hr'⟩, hr, rfl⟩
      · rintro ⟨⟨r, hr'⟩, hr, rfl⟩
        exact ⟨⟨r, hRH hr⟩, hr, rfl⟩
    have htop : (⊤ : Subgroup ↥(W ⊔ Rs)).map f = P := by
      rw [← himg]
      ext σ
      constructor
      · rintro ⟨⟨h, hh'⟩, -, rfl⟩
        exact ⟨⟨h, hHL hh'⟩, hh', rfl⟩
      · rintro ⟨⟨h, hh'⟩, hh, rfl⟩
        exact ⟨⟨h, hh⟩, Subgroup.mem_top _, rfl⟩
    have h1 := Subgroup.relIndex_map_map f (Rs.subgroupOf (W ⊔ Rs)) ⊤
    rw [hmap, htop, sup_eq_left.mpr hkerf, top_sup_eq, Subgroup.relIndex_top_right] at h1
    have h2 := Subgroup.relIndex_mul_card Q P
    rw [inf_eq_left.mpr hQP, hcard] at h2
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have h4 : Q.relIndex P = 3 := Nat.eq_of_mul_eq_mul_right hQpos h2
    rw [Subgroup.relIndex, ← h1, h4]
  have hSyl : IsSylowTwoOf Rs (W ⊔ Rs) := by
    refine ⟨hRH, hRp, ?_⟩
    show ¬ 2 ∣ Rs.relIndex (W ⊔ Rs)
    rw [h3]; decide
  have hN : ¬ W ⊔ Rs ≤ Subgroup.normalizer (Rs : Set (X ⧸ gnC T)) := by
    intro hle
    obtain ⟨g, ⟨hgP, hgA⟩, e, he, hge⟩ := hnn
    set w : ↥L := c.eL.symm ⟨g, hgA⟩ with hwdef
    have hwW : (w : X ⧸ gnC T) ∈ W := by
      refine (c.mem_wP).2 ⟨w.2, ?_⟩
      rw [show (⟨(w : X ⧸ gnC T), w.2⟩ : ↥L) = w from rfl, hwdef, MulEquiv.apply_symm_apply]
      exact hgP
    have heR := he
    rw [← hQ] at heR
    obtain ⟨⟨r, hr'⟩, hr, rfl⟩ := heR
    have hconj : (w : X ⧸ gnC T) * r * (w : X ⧸ gnC T)⁻¹ ∈ Rs :=
      (Subgroup.mem_normalizer_iff.1 (hle (Subgroup.mem_sup_left hwW)) r).1 hr
    apply hge
    have h1 := hθRQ _ hconj
    have e : (⟨(w : X ⧸ gnC T) * r * (w : X ⧸ gnC T)⁻¹, hRL hconj⟩ : ↥(nLs T L)) =
        ⟨w, hWL hwW⟩ * ⟨r, hr'⟩ * (⟨w, hWL hwW⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, c.θs_of_mem_L w.2] at h1
    rw [show (⟨(w : X ⧸ gnC T), w.2⟩ : ↥L) = w from rfl, hwdef, MulEquiv.apply_symm_apply] at h1
    exact h1
  exact ⟨CFSG.Quasithin.H13.A5.minParabolic_of_relIndex_three hSyl h3 hN, himg, hker⟩

end SixCtx

variable [Finite X]

theorem exists_minParabolic_lift (hX : GNSetting X T) {R : Subgroup X} (hRT : R ≤ T)
    (hCR : T ⊓ gnC T ≤ R) (hQR : pCoreOf 2 (⊤ : Subgroup X) ≤ R) {Hs : Subgroup (X ⧸ gnC T)}
    (hmin : MinParabolic Hs (R.map (QuotientGroup.mk' (gnC T)))
      (R.map (QuotientGroup.mk' (gnC T)))) :
    ∃ H M : Subgroup X, MinParabolic H R M ∧ CharTwo H ∧ R ≤ H ∧
      H.map (QuotientGroup.mk' (gnC T)) = Hs :=
  Tits.GN516.exists_minParabolic_lift_of_le hX hRT hCR hQR hmin

theorem isSolvable_of_minParabolic {R H M : Subgroup X} (hmin : MinParabolic H R M)
    (hsolv : Group.IsSolvable ↥(H.map (QuotientGroup.mk' (gnC T))))
    (hne : H.map (QuotientGroup.mk' (gnC T)) ≠ R.map (QuotientGroup.mk' (gnC T))) :
    Group.IsSolvable ↥H :=
  Tits.GN516.isSolvable_of_minParabolic_of_map hmin _ hsolv hne

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
