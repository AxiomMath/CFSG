module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigW
public import CFSG.Mathlib.GroupTheory.CoprimeCentralizerFactors
public import CFSG.Mathlib.GroupTheory.CoprimeComponentNormalizer

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem map_centralizer_singleton (φ : G ≃* G) (b : G) :
    (centralizer ({b} : Set G)).map φ.toMonoidHom = centralizer ({φ b} : Set G) := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, hy, map_mul]
  · intro hx
    refine ⟨φ.symm x, ?_, by simp⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx]

theorem map_theta (φ : G ≃* G) (U : Subgroup G) (b : G) :
    (theta U b).map φ.toMonoidHom = theta (U.map φ.toMonoidHom) (φ b) := by
  rw [theta, theta, Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, map_oddCoreIn φ, map_oddCoreIn φ,
    map_centralizer_singleton φ, map_centralizer φ]

theorem map_wGroup (φ : G ≃* G) (E U : Subgroup G) :
    (wGroup E U).map φ.toMonoidHom = wGroup (E.map φ.toMonoidHom) (U.map φ.toMonoidHom) := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    rw [← map_le_iff_le_comap, map_theta]
    exact theta_le_wGroup ⟨e, he, rfl⟩ (fun h => he1 (φ.injective (by rw [h, map_one])))
  · refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    obtain ⟨e', he', rfl⟩ := he
    have he'1 : e' ≠ 1 := fun h => he1 (by rw [h]; simp)
    rw [show φ.toMonoidHom e' = φ e' from rfl, ← map_theta]
    exact map_mono (theta_le_wGroup he' he'1)

theorem le_normalizer_wGroup {E U : Subgroup G} {g : G} (hgE : g ∈ normalizer (E : Set G))
    (hgU : g ∈ normalizer (U : Set G)) : g ∈ normalizer (wGroup E U : Set G) := by
  have hE : E.map (MulAut.conj g).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.mp hgE
  have hU : U.map (MulAut.conj g).toMonoidHom = U := mem_normalizer_iff_map_conj_eq.mp hgU
  have h := map_wGroup (MulAut.conj g) E U
  rw [hE, hU] at h
  exact mem_normalizer_iff_map_conj_eq.mpr h

section SameWOddLocalData

variable [Finite G]

theorem le_normalizer_wGroup_of_odd_of_local_data
    {E F X : Subgroup G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEF : E ≤ centralizer (F : Set G))
    (hEFfix : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({v} : Set G)))
    (hFEfix : ∀ v ∈ F, v ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      theta E v ⊓ centralizer ({b} : Set G) ≤
        oddCoreIn (centralizer ({b} : Set G)))
    (hlocal : ∀ b ∈ E, b ≠ 1 →
      let C := centralizer ({b} : Set G)
      let π := QuotientGroup.mk' (pPrimeCore 2 ↥C)
      ∃ S : Subgroup (↥C ⧸ pPrimeCore 2 ↥C),
        CFSG.IsComponent S ∧ IsSimpleGroup ↥S ∧
        (F.subgroupOf C).map π ≤ S ∧
        (E.subgroupOf C).map π ≤ centralizer (S : Set _))
    (hX : Nat.Coprime 2 (Nat.card X))
    (hEX : E ≤ normalizer (X : Set G))
    (hFX : F ≤ normalizer (X : Set G)) :
    X ≤ normalizer (wGroup E F : Set G) := by
  have hEc := comm_of_isKleinFour hE
  have hFc := comm_of_isKleinFour hF
  have hWswap : wGroup E F = wGroup F E :=
    wGroup_eq_swap_of_fixed_bounds hE hF hEF hEFfix hFEfix
  set H : Subgroup G := normalizer (wGroup E F : Set G) with hH
  have hwEFzp : ∀ v ∈ F, v ≠ 1 → wGroup E F = wGroup E (zpowers v) := by
    intro v hv hv1
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
      rw [theta_eq_theta_zpowers_of_fixed_bound hF
        (fun f hf => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hEF hb)) f hf))
        hv hv1 (hEFfix b hb hb1 v hv hv1)]
      exact theta_le_wGroup hb hb1
    · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
      exact (theta_mono (Subgroup.zpowers_le.mpr hv) (isPGroup_of_isKleinFour hF)
        hFc (fun f hf => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hEF hb)) f hf))).trans (theta_le_wGroup hb hb1)
  have hwFEzb : ∀ b ∈ E, b ≠ 1 → wGroup F E = wGroup F (zpowers b) := by
    intro b hb hb1
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
      rw [theta_eq_theta_zpowers_of_fixed_bound hE
        (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hEF he)) v hv).symm)
        hb hb1 (hFEfix v hv hv1 b hb hb1)]
      exact theta_le_wGroup hv hv1
    · refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
      exact (theta_mono (Subgroup.zpowers_le.mpr hb) (isPGroup_of_isKleinFour hE)
        hEc (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hEF he)) v hv).symm)).trans (theta_le_wGroup hv hv1)
  have hCEv : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      centralizer (E : Set G) ⊓ centralizer ({v} : Set G) ≤ H := by
    intro b hb hb1 v hv hv1 g hg
    rw [hH, hwEFzp v hv hv1]
    refine le_normalizer_wGroup (E := E) (U := zpowers v) ?_ ?_
    · exact Subgroup.centralizer_le_normalizer (E : Set G) hg.1
    · exact Subgroup.centralizer_le_normalizer ((zpowers v : Subgroup G) : Set G)
        (by rw [centralizer_zpowers_eq]; exact hg.2)
  have hCFb : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      centralizer (F : Set G) ⊓ centralizer ({b} : Set G) ≤ H := by
    intro b hb hb1 v hv hv1 g hg
    rw [hH, hWswap, hwFEzb b hb hb1]
    refine le_normalizer_wGroup (E := F) (U := zpowers b) ?_ ?_
    · exact Subgroup.centralizer_le_normalizer (F : Set G) hg.1
    · exact Subgroup.centralizer_le_normalizer ((zpowers b : Subgroup G) : Set G)
        (by rw [centralizer_zpowers_eq]; exact hg.2)
  have hYleH : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      ((X ⊓ centralizer ({b} : Set G)) ⊓ centralizer ({v} : Set G)) ≤ H := by
    intro b hb hb1 v hv hv1
    let C : Subgroup G := centralizer ({b} : Set G)
    let Y : Subgroup G := (X ⊓ C) ⊓ centralizer ({v} : Set G)
    let P : Subgroup ↥C := pPrimeCore 2 ↥C
    let π : ↥C →* (↥C ⧸ P) := QuotientGroup.mk' P
    change Y ≤ H
    have hEC : E ≤ C := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (hEc e he b hb)
    have hFC : F ≤ C := fun f hf =>
      Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp (hEF hb)) f hf)
    have hYC : Y ≤ C := (inf_le_left.trans inf_le_right : Y ≤ C)
    have hECv : E ≤ centralizer ({v} : Set G) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (((Subgroup.mem_centralizer_iff.mp (hEF he)) v hv).symm)
    have hFCv : F ≤ centralizer ({v} : Set G) := fun f hf =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hFc f hf v hv)
    have hY_odd : Nat.Coprime 2 (Nat.card Y) :=
      Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left : Y ≤ X)) hX
    have hYleCv : Y ≤ centralizer ({v} : Set G) := (inf_le_right : Y ≤ _)
    have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
      have h1 : E ≤ Subgroup.normalizer ((X ⊓ C : Subgroup G) : Set G) :=
        (le_inf hEX (hEC.trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have h2 : E ≤ Subgroup.normalizer (centralizer ({v} : Set G) : Set G) :=
        hECv.trans Subgroup.le_normalizer
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hFY : F ≤ Subgroup.normalizer (Y : Set G) := by
      have h1 : F ≤ Subgroup.normalizer ((X ⊓ C : Subgroup G) : Set G) :=
        (le_inf hFX (hFC.trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have h2 : F ≤ Subgroup.normalizer (centralizer ({v} : Set G) : Set G) :=
        hFCv.trans Subgroup.le_normalizer
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hFZ : F ≤ Subgroup.normalizer (⁅Y, E⁆ : Subgroup G) := by
      intro f hf
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hYmap : Y.map (MulAut.conj f).toMonoidHom = Y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hFY hf)
      have hfNE : f ∈ Subgroup.normalizer (E : Set G) :=
        Subgroup.centralizer_le_normalizer (E : Set G)
          (Subgroup.mem_centralizer_iff.mpr fun e he =>
            ((Subgroup.mem_centralizer_iff.mp (hEF he)) f hf).symm)
      have hEmap : E.map (MulAut.conj f).toMonoidHom = E :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hfNE
      rw [Subgroup.map_commutator]
      erw [hYmap, hEmap]
    obtain ⟨S, hS, hSs, hFS, hES⟩ := hlocal b hb hb1
    let u : ↥C ⧸ P := π ⟨v, hFC hv⟩
    have hu_order : orderOf u = 2 := by
      change orderOf (QuotientGroup.mk' P ⟨v, hFC hv⟩) = 2
      exact CFSG.ComponentClassification.UnbalancedLayer.orderOf_mk_eq_two
        (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥C)))
        (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_two_of_isKleinFour hF hv hv1)
    have hScenter : center ↥S = ⊥ :=
      @CFSG.ComponentClassification.Sol76.center_eq_bot_of_simple_nonab ↥S _ hSs
        (CFSG.ComponentClassification.FooteLit.exists_mul_ne_mul_of_isQuasisimple hS.1)
    have huS : u ∈ S := hFS (Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr hv))
    have huZ : u ∉ Subgroup.centralizer (S : Set (↥C ⧸ P)) := by
      intro huCent
      have hmem : (⟨u, huS⟩ : ↥S) ∈ center ↥S := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp huCent) y y.2)
      rw [hScenter, Subgroup.mem_bot] at hmem
      have hu1 : u = 1 := by simpa using congrArg Subtype.val hmem
      rw [hu1, orderOf_one] at hu_order
      norm_num at hu_order
    have hcardYc : Nat.card ↥(Y.subgroupOf C) = Nat.card Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv
    have hcardYbar : Nat.card ↥((Y.subgroupOf C).map π) ∣ Nat.card Y := by
      have h := Subgroup.card_map_dvd (H := Y.subgroupOf C) π
      rwa [hcardYc] at h
    have hYbar_odd : Nat.Coprime 2 (Nat.card ↥((Y.subgroupOf C).map π)) :=
      Nat.Coprime.coprime_dvd_right hcardYbar hY_odd
    have hcop : Nat.Coprime (orderOf u) (Nat.card ↥((Y.subgroupOf C).map π)) := by
      rw [hu_order]
      exact hYbar_odd
    have hFcYc : F.subgroupOf C ≤
        Subgroup.normalizer ((Y.subgroupOf C : Subgroup ↥C) : Set ↥C) :=
      (Subgroup.comap_mono (f := C.subtype) hFY).trans
        (Subgroup.le_normalizer_comap (H := Y) C.subtype)
    have huYc : (⟨v, hFC hv⟩ : ↥C) ∈
        Subgroup.normalizer ((Y.subgroupOf C : Subgroup ↥C) : Set ↥C) :=
      hFcYc (Subgroup.mem_subgroupOf.mpr hv)
    have huYbar : u ∈ Subgroup.normalizer
        (((Y.subgroupOf C).map π : Subgroup (↥C ⧸ P)) : Set (↥C ⧸ P)) := by
      have h := (Subgroup.le_normalizer_map (H := Y.subgroupOf C) π)
        (Subgroup.mem_map_of_mem π huYc)
      change (π ⟨v, hFC hv⟩) ∈ Subgroup.normalizer
        (((Y.subgroupOf C).map π : Subgroup (↥C ⧸ P)) : Set (↥C ⧸ P))
      exact h
    have hB := CFSG.GroupTheory.mixed_commutator_eq_bot_of_component_action
      (G := ↥C ⧸ P) (S := S) (Y := (Y.subgroupOf C).map π)
      (E := (E.subgroupOf C).map π) (F := (F.subgroupOf C).map π) (u := u)
      hS huS huZ huYbar hcop hFS hES
    have hUcP : ⁅⁅Y.subgroupOf C, E.subgroupOf C⁆, F.subgroupOf C⁆ ≤ P := by
      have hmap : ((⁅⁅Y.subgroupOf C, E.subgroupOf C⁆, F.subgroupOf C⁆).map π) = ⊥ := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator, hB]
      have hker : π.ker = P := by
        change (QuotientGroup.mk' P).ker = P
        exact QuotientGroup.ker_mk' P
      rwa [Subgroup.map_eq_bot_iff, hker] at hmap
    have hU_le : ⁅⁅Y, E⁆, F⁆ ≤ oddCoreIn C := by
      have hmap : ((⁅⁅Y.subgroupOf C, E.subgroupOf C⁆, F.subgroupOf C⁆).map C.subtype) =
          ⁅⁅Y, E⁆, F⁆ := by
        rw [Subgroup.map_commutator, Subgroup.map_commutator,
          Subgroup.map_subgroupOf_eq_of_le hYC,
          Subgroup.map_subgroupOf_eq_of_le hEC,
          Subgroup.map_subgroupOf_eq_of_le hFC]
      rw [← hmap]
      exact Subgroup.map_mono (f := C.subtype) hUcP
    have hOF : ⁅oddCoreIn C, F⁆ ≤ H := by
      rw [hH]
      have htheta : ⁅oddCoreIn C, F⁆ ≤ theta F b := by
        change ⁅oddCoreIn (centralizer ({b} : Set G)), F⁆ ≤
          ⁅oddCoreIn (centralizer ({b} : Set G)), F⁆ ⊔
            (oddCoreIn (centralizer ({b} : Set G)) ⊓
              oddCoreIn (centralizer (F : Set G)))
        exact le_sup_left
      exact (htheta.trans (theta_le_wGroup hb hb1)).trans Subgroup.le_normalizer
    have hCE : Y ⊓ Subgroup.centralizer (E : Set G) ≤ H :=
      (le_inf inf_le_right (inf_le_left.trans hYleCv)).trans (hCEv b hb hb1 v hv hv1)
    have hZleCb : ⁅Y, E⁆ ≤ C :=
      (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y E hEY).trans hYC
    have hCF : ⁅Y, E⁆ ⊓ Subgroup.centralizer (F : Set G) ≤ H :=
      (le_inf inf_le_right (inf_le_left.trans hZleCb)).trans (hCFb b hb hb1 v hv hv1)
    exact CFSG.GroupTheory.le_of_coprime_centralizer_factors
      (p := 2) (q := 2) Nat.prime_two Nat.prime_two
      (isPGroup_of_isKleinFour hE) (isPGroup_of_isKleinFour hF)
      hEY hFZ hY_odd hY_odd hCE hCF hU_le hOF
  have hgenE : X ≤ ⨆ (b : G) (_ : b ∈ E) (_ : b ≠ 1),
      X ⊓ centralizer ({b} : Set G) :=
    le_iSup_inf_centralizer_of_isKleinFour hE hEX hX
  refine hgenE.trans ?_
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  have hXb_odd : Nat.Coprime 2 (Nat.card ↥(X ⊓ centralizer ({b} : Set G))) :=
    Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le (inf_le_left : X ⊓ centralizer ({b} : Set G) ≤ X)) hX
  have hFCb : F ≤ centralizer ({b} : Set G) := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hEF hb)) f hf)
  have hFXb : F ≤ Subgroup.normalizer
      ((X ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    (le_inf hFX (hFCb.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine (le_iSup_inf_centralizer_of_isKleinFour hF hFXb hXb_odd).trans ?_
  refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
  exact hYleH b hb hb1 v hv hv1

theorem le_normalizer_wGroup_oddCoreIn_centralizer
    {E F : Subgroup G} {s : G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEF : E ≤ centralizer (F : Set G))
    (hEs : E ≤ centralizer ({s} : Set G))
    (hFs : F ≤ centralizer ({s} : Set G))
    (hEFfix : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({v} : Set G)))
    (hFEfix : ∀ v ∈ F, v ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      theta E v ⊓ centralizer ({b} : Set G) ≤
        oddCoreIn (centralizer ({b} : Set G)))
    (hlocal : ∀ b ∈ E, b ≠ 1 →
      let C := centralizer ({b} : Set G)
      let π := QuotientGroup.mk' (pPrimeCore 2 ↥C)
      ∃ S : Subgroup (↥C ⧸ pPrimeCore 2 ↥C),
        CFSG.IsComponent S ∧ IsSimpleGroup ↥S ∧
        (F.subgroupOf C).map π ≤ S ∧
        (E.subgroupOf C).map π ≤ centralizer (S : Set _)) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup E F : Set G) :=
  le_normalizer_wGroup_of_odd_of_local_data hE hF hEF hEFfix hFEfix hlocal
    (coprime_card_oddCoreIn (centralizer ({s} : Set G)))
    (hEs.trans (le_normalizer_oddCoreIn _))
    (hFs.trans (le_normalizer_oddCoreIn _))

end SameWOddLocalData

variable [Finite G] {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

omit [Finite G] in
theorem le_centralizer_singleton_of_mem {B V : Subgroup G} (hBV : B ≤ centralizer (V : Set G))
    {b : G} (hb : b ∈ B) : V ≤ centralizer ({b} : Set G) := fun w hw =>
  mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBV hb)) w hw)

theorem wGroup_eq_of_le (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B) (hE : IsKleinFour E)
    (hEB : E ≤ B) : wGroup E V = wGroup B V := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hbalance : ∀ b ∈ B, b ≠ 1 → ∀ e ∈ E, e ≠ 1 →
      theta V b ⊓ centralizer ({e} : Set G) ≤ theta V e := by
    intro b hb hb1 e he he1
    have hb2 : orderOf b = 2 := orderOf_eq_prime (hB.2 b hb) hb1
    have he2 : orderOf e = 2 := orderOf_eq_prime (hB.2 e (hEB he)) he1
    have hbe : e * b = b * e := (hBc b hb e (hEB he)).symm
    exact theta_inf_le_theta h32 hG hN hK hK' hne hV hVK' (hBK (hEB he)) he2 (hBK hb) hb2
      hbe (le_centralizer_singleton_of_mem hBV (hEB he)) (le_centralizer_singleton_of_mem hBV hb)
  exact (wGroup_eq_of_cross_balance hE hEB hBc hBV hbalance).symm

theorem le_normalizer_wGroup_of_mem (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B) (hE : IsKleinFour E)
    (hEB : E ≤ B) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) {g : G}
    (hgE : g ∈ normalizer (E : Set G)) (hgv : g ∈ centralizer ({v} : Set G)) :
    g ∈ normalizer (wGroup B V : Set G) := by
  rw [← wGroup_eq_of_le h32 hG hN hK hK' hne hV hVK' hBK hBV hB hE hEB,
    wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV hVK' hE (hEB.trans hBK) (hEB.trans hBV)
      hv hv1]
  refine le_normalizer_wGroup hgE ?_
  rw [← centralizer_zpowers_eq] at hgv
  exact Subgroup.centralizer_le_normalizer ((zpowers v : Subgroup G) : Set G) hgv

theorem le_normalizer_wGroup_of_odd (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B X : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hXodd : Nat.Coprime 2 (Nat.card X))
    (hBX : B ≤ normalizer (X : Set G)) (hVX : V ≤ normalizer (X : Set G)) :
    X ≤ normalizer (wGroup B V : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B X hB (by rw [hB8]; norm_num) hBX hXodd
  refine hgen.symm.le.trans (iSup₂_le fun S hS => ?_)
  obtain ⟨hSB, hScard⟩ := hS
  have hSK : IsKleinFour S :=
    isKleinFour_of_card_eq_four (by rw [hScard]; norm_num) fun x hx => hB.2 x (hSB hx)
  set Y := X ⊓ centralizer (S : Set G) with hY
  have hVS : V ≤ centralizer (S : Set G) := fun v hv => mem_centralizer_iff.mpr fun s hs =>
    ((mem_centralizer_iff.mp (hBV (hSB hs))) v hv).symm
  have hVY : V ≤ normalizer (Y : Set G) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro y
    rw [hY, mem_inf, mem_inf, mem_normalizer_iff.mp (hVX hv),
      mem_normalizer_iff.mp (le_normalizer (hVS hv))]
  have hYodd : Nat.Coprime 2 (Nat.card Y) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hXodd
  have hgen2 := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two V Y (isElemAbelian_of_isKleinFour hV) (by rw [hV.card_four]; norm_num) hVY
    hYodd
  refine hgen2.symm.le.trans (iSup₂_le fun T hT => ?_)
  obtain ⟨hTV, hTcard⟩ := hT
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥T)
  have ht1 : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
  intro y hy
  have hyS : y ∈ normalizer (S : Set G) :=
    Subgroup.centralizer_le_normalizer (S : Set G) hy.1.2
  have hyt : y ∈ centralizer ({(t : G)} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr t.2) hy.2
  exact le_normalizer_wGroup_of_mem h32 hG hN hK hK' hne hV hVK' hBK hBV hB hSK hSB (hTV t.2)
    ht1 hyS hyt

end CFSG.ComponentClassification.Sol76.Sig
