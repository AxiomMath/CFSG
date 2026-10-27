module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module

theorem isElemAbelian_map_hom {G H : Type*} [Group G] [Group H] (p : ℕ) (φ : G →* H)
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map φ) := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    change (a : H) * (b : H) = (b : H) * (a : H)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    have hc : (⟨x, hx⟩ : E) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := hcomm.is_comm.comm _ _
    exact congrArg Subtype.val hc
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow, hexp z' hz', map_one]

theorem isElemAbelian_mono_of_le {G : Type*} [Group G] {p : ℕ} {E E' : Subgroup G} (h : E' ≤ E)
    (hE : IsElemAbelian p E) : IsElemAbelian p E' := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hexp x (h hx)⟩
  have hc : a.1 * b.1 = b.1 * a.1 :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨a.1, h a.2⟩ : E) ⟨b.1, h b.2⟩)
  exact Subtype.ext hc

theorem pow_inj_of_plane {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {ρ : W ≃ₗ[ZMod 2] W}
    {x : W} (hx : x ≠ 0) (hfix : ρ x = x → x = 0)
    (hcyc : ρ (ρ x) + ρ x + x = 0) (s t : Fin 3)
    (h : (ρ ^ (s : ℕ)) x = (ρ ^ (t : ℕ)) x) : s = t := by
  have hA : ρ x ≠ x := fun h' => hx (hfix h')
  have hxx : x + x = 0 := by
    have h2 : ((1 : ZMod 2) + 1) • x = 0 := by
      rw [show ((1 : ZMod 2) + 1) = 0 from rfl, zero_smul]
    rwa [add_smul, one_smul] at h2
  have hB : ρ (ρ x) ≠ x := by
    intro h'
    apply hx
    have h2 : x + ρ x + x = 0 := by
      have h5 := hcyc
      rw [h'] at h5
      exact h5
    have h3 : ρ x = 0 := by linear_combination (norm := module) h2 - hxx
    exact ρ.injective (h3.trans (map_zero ρ).symm)
  have hC : ρ (ρ x) ≠ ρ x := fun h' => hA (ρ.injective h')
  have e0 : (ρ ^ (0 : ℕ)) x = x := by simp
  have e1 : (ρ ^ (1 : ℕ)) x = ρ x := by simp
  have e2 : (ρ ^ (2 : ℕ)) x = ρ (ρ x) := by
    rw [pow_two, LinearEquiv.mul_apply]
  fin_cases s <;> fin_cases t
  · rfl
  · exfalso
    apply hA
    rw [show ((⟨0, by norm_num⟩ : Fin 3) : ℕ) = 0 from rfl, show ((⟨1, by norm_num⟩ : Fin 3) : ℕ) = 1 from rfl, e0, e1] at h
    exact h.symm
  · exfalso
    apply hB
    rw [show ((⟨0, by norm_num⟩ : Fin 3) : ℕ) = 0 from rfl, show ((⟨2, by norm_num⟩ : Fin 3) : ℕ) = 2 from rfl, e0, e2] at h
    exact h.symm
  · exfalso
    apply hA
    rw [show ((⟨1, by norm_num⟩ : Fin 3) : ℕ) = 1 from rfl, show ((⟨0, by norm_num⟩ : Fin 3) : ℕ) = 0 from rfl, e0, e1] at h
    exact h
  · rfl
  · exfalso
    apply hC
    rw [show ((⟨1, by norm_num⟩ : Fin 3) : ℕ) = 1 from rfl, show ((⟨2, by norm_num⟩ : Fin 3) : ℕ) = 2 from rfl, e1, e2] at h
    exact h.symm
  · exfalso
    apply hB
    rw [show ((⟨2, by norm_num⟩ : Fin 3) : ℕ) = 2 from rfl, show ((⟨0, by norm_num⟩ : Fin 3) : ℕ) = 0 from rfl, e0, e2] at h
    exact h
  · exfalso
    apply hC
    rw [show ((⟨2, by norm_num⟩ : Fin 3) : ℕ) = 2 from rfl, show ((⟨1, by norm_num⟩ : Fin 3) : ℕ) = 1 from rfl, e1, e2] at h
    exact h
  · rfl


section Main

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem sp_core_G (f : LinearMap.BilinForm (ZMod 2) W) (hfalt : f.IsAlt)
    (hfnd : f.Nondegenerate) (n : ℕ) (hn : 4 ≤ n) (hdim : Module.finrank (ZMod 2) W = 2 * n)
    (E' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f)) [Fintype E']
    (hE' : IsElemAbelian 3 E') (hcard : Fintype.card E' = 3 ^ n) :
    ∃ F' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f), F' ≤ E' ∧ IsElemAbelian 3 F' ∧
      2 ≤ CFSG.Open.pRank 3 F' ∧ ∃ L' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f),
        CFSG.Open.IsSubnormal L'
          (Subgroup.centralizer (F' : Set ↥(TauCeti.BilinForm.isometryGroup f))) ∧
        Nonempty (↥L' ≃* alternatingGroup (Fin 6)) := by
  classical
  let EΓ : Subgroup (W ≃ₗ[ZMod 2] W) := E'.map (TauCeti.BilinForm.isometryGroup f).subtype
  haveI : Fintype EΓ := Fintype.ofFinite _
  have hEΓ : IsElemAbelian 3 EΓ :=
    isElemAbelian_map_hom 3 (TauCeti.BilinForm.isometryGroup f).subtype hE'
  have hcardΓ : Fintype.card EΓ = 3 ^ n := by
    rw [← hcard]
    exact (Fintype.card_congr (Subgroup.equivMapOfInjective E'
      (TauCeti.BilinForm.isometryGroup f).subtype Subtype.val_injective).toEquiv).symm
  have hGmem : ∀ g ∈ EΓ, g ∈ TauCeti.BilinForm.isometryGroup f := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact y.2
  have hEf : ∀ g ∈ EΓ, ∀ x y, f (g x) (g y) = f x y := by
    intro g hg x y
    exact (TauCeti.BilinForm.mem_isometryGroup_iff.1 (hGmem g hg)) x y
  obtain ⟨X, ρ, hdim2, hind, hsup, hinv, hmem, hcyc, hfix, hpow, hsep⟩ :=
    sp_struct EΓ hEΓ n hdim hcardΓ
  choose e heE hact using hsep
  let D : PlaneData EΓ n :=
    { X := X, ρ := ρ, e := e, dim2 := hdim2, indep := hind, sup_eq := hsup, inv := hinv,
      memE := hmem, cyc := hcyc, fixfree := hfix, pow := hpow, emem := heE, eact := hact }
  have hn2 : 2 ≤ n := by omega
  have hSub : CFSG.Open.IsSubnormal (D.Lg f hn2) (D.Cg f) :=
    D.isSubnormal_Lg_Cg f hEf hfalt hfnd hEΓ hn2
  have hIso := D.Lg_iso_alt f hEf hfalt hfnd hn2
  have hCG : D.Cg f ≤ TauCeti.BilinForm.isometryGroup f := inf_le_right
  have hLG : D.Lg f hn2 ≤ TauCeti.BilinForm.isometryGroup f :=
    le_trans (le_trans (Subgroup.map_le_range _ _) (D.Hg_le_Cg f hEf hfalt hn2)) hCG
  let F' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f) :=
    D.fixU.subgroupOf (TauCeti.BilinForm.isometryGroup f)
  have hfixE : ∀ g ∈ D.fixU, g ∈ EΓ := fun g hg => hg.1
  have hF'E : F' ≤ E' := by
    intro x hx
    have hx' : (x : W ≃ₗ[ZMod 2] W) ∈ D.fixU := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'.1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  have hi23 : i2 ≠ i3 := by
    intro h
    have := congrArg Fin.val h
    simp [i2, i3] at this
  have hi32 : i3 ≠ i2 := Ne.symm hi23
  have hi2 : 2 ≤ i2.val := by simp [i2]
  have hi3 : 2 ≤ i3.val := by simp [i3]
  let a : ↥(TauCeti.BilinForm.isometryGroup f) := ⟨e i2, hGmem _ (heE i2)⟩
  let b : ↥(TauCeti.BilinForm.isometryGroup f) := ⟨e i3, hGmem _ (heE i3)⟩
  have haF : a ∈ F' := Subgroup.mem_subgroupOf.2 (D.e_mem_fixU i2 hi2)
  have hbF : b ∈ F' := Subgroup.mem_subgroupOf.2 (D.e_mem_fixU i3 hi3)
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hEΓ.2 _ (heE i2)
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hEΓ.2 _ (heE i3)
  have hab : a * b = b * a := by
    have hcomm' : e i2 * e i3 = e i3 * e i2 :=
      congrArg Subtype.val (hEΓ.1.is_comm.comm ⟨e i2, heE i2⟩ ⟨e i3, heE i3⟩)
    apply Subtype.ext
    exact hcomm'
  have hprod : ∀ s t : Fin 3, ((a ^ (s : ℕ) * b ^ (t : ℕ) : ↥(TauCeti.BilinForm.isometryGroup f)) :
      W ≃ₗ[ZMod 2] W) = e i2 ^ (s : ℕ) * e i3 ^ (t : ℕ) := by
    intro s t
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
  have hinj : ∀ s t s' t' : Fin 3, a ^ (s : ℕ) * b ^ (t : ℕ) = a ^ (s' : ℕ) * b ^ (t' : ℕ) →
      s = s' ∧ t = t' := by
    intro s t s' t' h
    have h' : e i2 ^ (s : ℕ) * e i3 ^ (t : ℕ) = e i2 ^ (s' : ℕ) * e i3 ^ (t' : ℕ) := by
      rw [← hprod, ← hprod, h]
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := D.X i2) (by
      intro h0
      have := D.dim2 i2
      rw [h0, finrank_bot] at this
      omega)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := D.X i3) (by
      intro h0
      have := D.dim2 i3
      rw [h0, finrank_bot] at this
      omega)
    have L : ∀ s t : ℕ, (D.e i2 ^ s * D.e i3 ^ t) x = (D.ρ i2 ^ s) x := by
      intro s t
      rw [LinearEquiv.mul_apply, D.ea_trivial i2 i3 hi23 t x hx, D.ea_pow_plane i2 s x hx]
    have M : ∀ s t : ℕ, (D.e i2 ^ s * D.e i3 ^ t) y = (D.ρ i3 ^ t) y := by
      intro s t
      rw [LinearEquiv.mul_apply, D.ea_pow_plane i3 t y hy,
        D.ea_trivial i3 i2 hi32 s _ (D.rho_pow_mem i3 t y hy)]
    have h'' : D.e i2 ^ (s : ℕ) * D.e i3 ^ (t : ℕ) = D.e i2 ^ (s' : ℕ) * D.e i3 ^ (t' : ℕ) := h'
    have hs : (D.ρ i2 ^ (s : ℕ)) x = (D.ρ i2 ^ (s' : ℕ)) x := by
      rw [← L (s : ℕ) (t : ℕ), ← L (s' : ℕ) (t' : ℕ), h'']
    have ht : (D.ρ i3 ^ (t : ℕ)) y = (D.ρ i3 ^ (t' : ℕ)) y := by
      rw [← M (s : ℕ) (t : ℕ), ← M (s' : ℕ) (t' : ℕ), h'']
    exact ⟨pow_inj_of_plane hx0 (D.fixfree i2 x hx) (D.cyc i2 x hx) s s' hs,
      pow_inj_of_plane hy0 (D.fixfree i3 y hy) (D.cyc i3 y hy) t t' ht⟩
  have hpRank : 2 ≤ CFSG.Open.pRank 3 F' :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.Gen.two_le_pRank_of_pair haF hbF ha3 hb3 hab hinj
  have hFel : IsElemAbelian 3 F' := isElemAbelian_mono_of_le hF'E hE'
  have hcent : Subgroup.centralizer (F' : Set ↥(TauCeti.BilinForm.isometryGroup f)) =
      (D.Cg f).subgroupOf (TauCeti.BilinForm.isometryGroup f) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 (fun h hh => ?_), x.2⟩
      have hhG : h ∈ TauCeti.BilinForm.isometryGroup f := hGmem h (hfixE h hh)
      have hhF : (⟨h, hhG⟩ : ↥(TauCeti.BilinForm.isometryGroup f)) ∈ F' :=
        Subgroup.mem_subgroupOf.2 hh
      exact congrArg Subtype.val (hx _ hhF)
    · intro hx y hy
      apply Subtype.ext
      have hyΓ : (y : W ≃ₗ[ZMod 2] W) ∈ D.fixU := Subgroup.mem_subgroupOf.1 hy
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).1) _ hyΓ
  obtain ⟨ι⟩ := hIso
  refine ⟨F', hF'E, hFel, hpRank, (D.Lg f hn2).subgroupOf (TauCeti.BilinForm.isometryGroup f), ?_, ?_⟩
  · rw [hcent]
    exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.Gen.isSubnormal_subgroupOf _ hSub hCG
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hLG).trans ι⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
