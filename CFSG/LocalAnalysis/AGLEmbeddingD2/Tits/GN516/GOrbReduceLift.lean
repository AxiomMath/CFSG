module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbReduceBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

namespace GOrbReduce

open scoped commutatorElement

variable {Y Y' : Type} [Group Y] [Group Y']

theorem mem_normalizer_of_map_mem_normalizer (f : Y →* Y') {L P : Subgroup Y} (hPL : P ≤ L)
    (hZP : ∀ z ∈ L, f z = 1 → z ∈ P) {r : Y} (hrL : r ∈ Subgroup.normalizer (L : Set Y))
    (hr : f r ∈ Subgroup.normalizer ((P.map f : Subgroup Y') : Set Y')) :
    r ∈ Subgroup.normalizer (P : Set Y) := by
  have key : ∀ r ∈ Subgroup.normalizer (L : Set Y),
      f r ∈ Subgroup.normalizer ((P.map f : Subgroup Y') : Set Y') →
        ∀ x ∈ P, r * x * r⁻¹ ∈ P := by
    intro r hrL hr x hx
    have hxL : r * x * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hrL x).1 (hPL hx)
    have h1 : f (r * x * r⁻¹) ∈ P.map f := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hr _).1 ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hpx⟩ := h1
    have h2 : f (p⁻¹ * (r * x * r⁻¹)) = 1 := by
      rw [map_mul, map_inv, hpx, inv_mul_cancel]
    have h3 : p⁻¹ * (r * x * r⁻¹) ∈ P :=
      hZP _ (L.mul_mem (L.inv_mem (hPL hp)) hxL) h2
    have : r * x * r⁻¹ = p * (p⁻¹ * (r * x * r⁻¹)) := by group
    rw [this]
    exact P.mul_mem hp h3
  refine B6.mem_normalizer_of_forall_mem (key r hrL hr) (fun x hx => ?_)
  have hr' : f r⁻¹ ∈ Subgroup.normalizer ((P.map f : Subgroup Y') : Set Y') := by
    rw [map_inv]
    exact inv_mem hr
  simpa using key r⁻¹ (inv_mem hrL) hr' x hx

variable [Finite Y] [Finite Y']

theorem gOrbConcl_of_map (h : KFactChevGraphOrbitSimple) (f : Y →* Y') {L R P : Subgroup Y}
    (hRN : R ≤ Subgroup.normalizer (L : Set Y)) (hPL : P ≤ L)
    (hker : ∀ k : Y, f k = 1 → ∀ l ∈ L, l * k = k * l)
    (hZP : ∀ z ∈ L, f z = 1 → z ∈ P)
    (hLs : IsSimpleGroup ↥(L.map f)) (hLc : IsChevTwo ↥(L.map f))
    (hR2 : IsPGroup 2 R) (hSyl : IsSylowTwoOf (R ⊓ L) L)
    (hMin : IsMinOverBorel (L.map f) ((R ⊓ L).map f) (P.map f))
    (hnP : ¬ R ≤ Subgroup.normalizer (P : Set Y)) : GOrbConcl R P := by
  obtain ⟨heq, hSylBar⟩ := inf_map_eq_map_inf f hR2 hSyl
  have hnPbar : ¬ R.map f ≤ Subgroup.normalizer ((P.map f : Subgroup Y') : Set Y') := by
    intro hle
    apply hnP
    intro r hr
    exact mem_normalizer_of_map_mem_normalizer f hPL hZP (hRN hr) (hle ⟨r, hr, rfl⟩)
  have hres := h Y' (L.map f) (R.map f) (P.map f) hLs hLc
    (by
      rintro x ⟨r, hr, rfl⟩
      exact Subgroup.le_normalizer_map f ⟨r, hRN hr, rfl⟩)
    (hR2.map f) hSylBar (by rw [heq]; exact hMin) hnPbar
  have hX : conjClosure (P.map f) (R.map f) = (conjClosure P R).map f :=
    (map_conjClosure f P R).symm
  have hWbar : pElementSubgroup 2 (conjClosure (P.map f) (R.map f)) =
      (pElementSubgroup 2 (conjClosure P R)).map f := by
    rw [hX]
    exact (map_pElementSubgroup_two f _).symm
  rw [hWbar] at hres
  unfold GOrbConcl
  have hXL : conjClosure P R ≤ L := conjClosure_le fun r hr z hz =>
    (Subgroup.mem_normalizer_iff.1 (hRN hr) z).1 (hPL hz)
  have hRX : R ≤ Subgroup.normalizer ((conjClosure P R : Subgroup Y) : Set Y) :=
    le_normalizer_conjClosure P R
  have hWL : pElementSubgroup 2 (conjClosure P R) ≤ L := (pElementSubgroup_le _).trans hXL
  have hRW : R ≤
      Subgroup.normalizer ((pElementSubgroup 2 (conjClosure P R) : Subgroup Y) : Set Y) :=
    fun r hr => normalizer_le_normalizer_pElementSubgroup 2 _ (hRX hr)
  set W := pElementSubgroup 2 (conjClosure P R) with hW
  have hc : ∀ k ∈ W, f k = 1 → ∀ w ∈ W, k * w = w * k := fun k _ hk w hw =>
    (hker k hk w (hWL hw)).symm
  have hW2 : W ≤ pElementSubgroup 2 W := (pElementSubgroup_pElementSubgroup 2 _).ge
  rcases hres with hs | ⟨Cb, hCb2, hCbW, hWN, hWgen, hcomm⟩ | hq
  · exact Or.inl (isSolvable_of_map_of_central f W hc hs)
  · right
    left
    set C : Subgroup Y := W ⊓ Cb.comap f with hC
    have hCW : C ≤ W := inf_le_left
    have hCmap : C.map f = Cb := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx.2
      · intro hy
        obtain ⟨w, hw, rfl⟩ := hCbW hy
        exact ⟨w, ⟨hw, hy⟩, rfl⟩
    have hkerC : ∀ k ∈ W, f k = 1 → k ∈ C := fun k hk hk1 =>
      Subgroup.mem_inf.2 ⟨hk, Subgroup.mem_comap.2 (by rw [hk1]; exact Cb.one_mem)⟩
    have hkey : ∀ w ∈ W, ∀ x ∈ C, w * x * w⁻¹ ∈ C := by
      intro w hw x hx
      refine Subgroup.mem_inf.2 ⟨W.mul_mem (W.mul_mem hw (Subgroup.mem_inf.1 hx).1) (W.inv_mem hw),
        Subgroup.mem_comap.2 ?_⟩
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hWN ⟨w, hw, rfl⟩) _).1
        (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2)
    have hWNC : W ≤ Subgroup.normalizer (C : Set Y) := fun w hw =>
      B6.mem_normalizer_of_forall_mem (hkey w hw)
        (fun x hx => by simpa using hkey w⁻¹ (W.inv_mem hw) x hx)
    have hDW : conjClosure C R ≤ W := conjClosure_le fun r hr z hz =>
      (Subgroup.mem_normalizer_iff.1 (hRW hr) z).1 (hCW hz)
    have hWD : W ≤ conjClosure C R := by
      intro w hw
      have h1 : f w ∈ (conjClosure C R).map f := by
        rw [map_conjClosure, hCmap]
        exact hWgen ⟨w, hw, rfl⟩
      obtain ⟨d, hd, hdw⟩ := h1
      have h2 : d⁻¹ * w ∈ C :=
        hkerC _ (W.mul_mem (W.inv_mem (hDW hd)) hw) (by rw [map_mul, map_inv, hdw, inv_mul_cancel])
      have h3 : w = d * (d⁻¹ * w) := by group
      rw [h3]
      exact (conjClosure C R).mul_mem hd (le_conjClosure C R h2)
    refine ⟨C, hCW, hWNC, hWD, ?_⟩
    intro r hr hrP
    have hfr : f r ∉ Subgroup.normalizer ((P.map f : Subgroup Y') : Set Y') := fun hn =>
      hrP (mem_normalizer_of_map_mem_normalizer f hPL hZP (hRN hr) hn)
    have h1 := hcomm (f r) ⟨r, hr, rfl⟩ hfr
    set C₀ := pElementSubgroup 2 C with hC₀
    have hC₀C : C₀ ≤ C := pElementSubgroup_le C
    have hC₀map : C₀.map f = Cb := by
      rw [map_pElementSubgroup_two, hCmap]
      exact le_antisymm (pElementSubgroup_le Cb) hCb2
    have hC₀2 : C₀ ≤ pElementSubgroup 2 C₀ := (pElementSubgroup_pElementSubgroup 2 C).ge
    have hC'W : B6.conjSub r C ≤ W := by
      have := (B6.conjSub r).monotone hCW
      rwa [B6.conjSub_eq_self (hRW hr)] at this
    have hmap : ⁅C₀.map f, (B6.conjSub r C).map f⁆ ≤ pCoreOf 2 (W.map f) := by
      rw [hC₀map, map_conjSub, hCmap]
      exact h1
    have h2 := commutator_le_pCoreOf_of_map f hc (hC₀C.trans hCW) hC'W hC₀2 hmap
    refine le_trans ?_ h2
    rw [Subgroup.commutator_le]
    intro c hcC c' hc'
    have hfc : f c ∈ C₀.map f := by
      rw [hC₀map, ← hCmap]
      exact ⟨c, hcC, rfl⟩
    obtain ⟨c₀, hc₀, hfc₀⟩ := hfc
    have hkW : c₀⁻¹ * c ∈ W := W.mul_mem (W.inv_mem ((hC₀C.trans hCW) hc₀)) (hCW hcC)
    have hk1 : f (c₀⁻¹ * c) = 1 := by rw [map_mul, map_inv, hfc₀, inv_mul_cancel]
    have hkc' : (c₀⁻¹ * c) * c' = c' * (c₀⁻¹ * c) := hc _ hkW hk1 c' (hC'W hc')
    have e : (c₀⁻¹ * c) * c' * (c₀⁻¹ * c)⁻¹ = c' := by
      rw [hkc', mul_inv_cancel_right]
    have hcomm' : ⁅c, c'⁆ = ⁅c₀, c'⁆ := by
      calc ⁅c, c'⁆ = c * c' * c⁻¹ * c'⁻¹ := rfl
        _ = c₀ * ((c₀⁻¹ * c) * c' * (c₀⁻¹ * c)⁻¹) * c₀⁻¹ * c'⁻¹ := by group
        _ = c₀ * c' * c₀⁻¹ * c'⁻¹ := by rw [e]
        _ = ⁅c₀, c'⁆ := rfl
    rw [hcomm']
    exact Subgroup.commutator_mem_commutator hc₀ hc'
  · exact Or.inr (Or.inr (quasisimpleModTwoNonab_twoResidual_of_map f hc hW2 hq))

end GOrbReduce

end CFSG.AGLEmbeddingD2.Tits.GN516
