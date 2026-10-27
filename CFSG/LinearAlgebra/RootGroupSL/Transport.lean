module

public import CFSG.LinearAlgebra.RootGroupSL.NoOuter
public import CFSG.LinearAlgebra.RootGroupSL.FpfNoCentral
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open CFSG.StandardType

open scoped commutatorElement

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  {G : Type} [Group G]

private theorem pCoreOf_le_self (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

private theorem le_pCoreOf_of_normal (p : ℕ) {G : Type*} [Group G] {N H : Subgroup G}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) :
    N ≤ pCoreOf p H := by
  have hsub : IsPGroup p (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : N.subgroupOf H ≤ CFSG.pCore p H := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (N.subgroupOf H) (le_iSup_of_le hN (le_iSup_of_le hsub le_rfl))
  rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
  unfold pCoreOf
  exact Subgroup.map_mono hcore

private theorem normalizer_le_normalizer_normalizer {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (Subgroup.normalizer (R : Set G)).mul_mem
      ((Subgroup.normalizer (R : Set G)).mul_mem hy hx)
      ((Subgroup.normalizer (R : Set G)).inv_mem hy)
  · intro hx
    have : y⁻¹ * (y * x * y⁻¹) * y ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).mul_mem
        ((Subgroup.normalizer (R : Set G)).mul_mem
          ((Subgroup.normalizer (R : Set G)).inv_mem hy) hx) hy
    convert this using 1 <;> group

theorem map_normalizer_eq_inf_normalizer_map {S : Type} [Group S] (ι : S →* G)
    (hι : Function.Injective ι) (R : Subgroup S) :
    ι.range ⊓ Subgroup.normalizer ((R.map ι : Subgroup G) : Set G) =
      (Subgroup.normalizer (R : Set S)).map ι := by
  let e : S ≃* ι.range := MonoidHom.ofInjective (f := ι) hι
  have hsub : ι.range.subtype.comp e.toMonoidHom = ι := by
    ext x
    rfl
  have hR : R.map e.toMonoidHom = (R.map ι).comap ι.range.subtype := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem ι hr)
    · intro hx
      obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
      refine ⟨r, hr, ?_⟩
      apply Subtype.ext
      exact hrx
  have hnorm : (Subgroup.normalizer (R : Set S)).map e.toMonoidHom =
      (Subgroup.normalizer ((R.map ι : Subgroup G) : Set G)).comap ι.range.subtype := by
    rw [Subgroup.map_equiv_normalizer_eq, hR]
    exact (Subgroup.comap_normalizer_eq_of_le_range (f := ι.range.subtype)
      (H := (R.map ι : Subgroup G))
      ((Subgroup.map_le_range (f := ι) (H := R)).trans
        (le_of_eq (Subgroup.range_subtype ι.range).symm))).symm
  have hlhs : ι.range ⊓ Subgroup.normalizer ((R.map ι : Subgroup G) : Set G) =
      Subgroup.map ι.range.subtype
        (Subgroup.comap ι.range.subtype
          (Subgroup.normalizer ((R.map ι : Subgroup G) : Set G))) := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
  rw [hlhs, ← hnorm, Subgroup.map_map, hsub]

theorem pCoreOf_map_of_injective {S : Type} [Group S] (ι : S →* G)
    (hι : Function.Injective ι) (p : ℕ) (H : Subgroup S) :
    pCoreOf p (H.map ι) = (pCoreOf p H).map ι := by
  have h := CFSG.pCore_map_iso p (Subgroup.equivMapOfInjective H ι hι)
  unfold pCoreOf
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

variable [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

private theorem finrank_pos_of_star (hdX : Module.finrank k E ≤ Module.finrank k X)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X)) :
    0 < Module.finrank k X := by
  rcases hstar with h | ⟨_, _, hX⟩
  · exact lt_of_lt_of_le (by norm_num) (le_trans h hdX)
  · exact lt_of_lt_of_le (by norm_num) hX

private theorem mem_rootSL_iff_map (ι : SpecialLinearGroup k (DSpace E X) →* G)
    (hι : Function.Injective ι) (z : SpecialLinearGroup k (DSpace E X)) :
    z ∈ rootSL k E X ↔ ι z ∈ (rootSL k E X).map ι := by
  constructor
  · intro hz
    exact Subgroup.mem_map_of_mem ι hz
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    rwa [hι hwz] at hw

theorem pCoreOf_inf_normalizer_eq_map_QK (hX : 0 < Module.finrank k X)
    (ι : SpecialLinearGroup k (DSpace E X) →* G) (hι : Function.Injective ι) :
    pCoreOf 2 (ι.range ⊓ Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G)) =
      (QK k E X).map ι := by
  rw [map_normalizer_eq_inf_normalizer_map ι hι (rootSL k E X),
    pCoreOf_map_of_injective ι hι 2 (Subgroup.normalizer (rootSL k E X)),
    pCoreOf_normalizer_rootSL hX]

theorem ggRootNoCentralAt_map (hdX : Module.finrank k E ≤ Module.finrank k X)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X))
    (ι : SpecialLinearGroup k (DSpace E X) →* G) (hι : Function.Injective ι) :
    GGRootNoCentralAt ι.range ((rootSL k E X).map ι) := by
  unfold GGRootNoCentralAt
  intro A B' hRA hAB hB hNA hNB hc
  let D : Subgroup G := ι.range ⊓
    Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G)
  let DS : Subgroup (SpecialLinearGroup k (DSpace E X)) :=
    Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))
  have hX : 0 < Module.finrank k X := finrank_pos_of_star hdX hstar
  have hQKmap : pCoreOf 2 D = (QK k E X).map ι :=
    pCoreOf_inf_normalizer_eq_map_QK hX ι hι
  have hcore_le : pCoreOf 2 D ≤ (pCoreOf 2 DS).map ι := by
    rw [hQKmap]
    exact Subgroup.map_mono (f := ι) (QK_le_pCoreOf_normalizer)
  have hRA' : rootSL k E X ≤ Subgroup.comap ι A := by
    intro z hz
    exact Subgroup.mem_comap.mpr (hRA (Subgroup.mem_map_of_mem ι hz))
  have hAB' : Subgroup.comap ι A ≤ Subgroup.comap ι B' := Subgroup.comap_mono hAB
  have hB'' : Subgroup.comap ι B' ≤ pCoreOf 2 DS := by
    intro x hx
    have hx' : ι x ∈ (pCoreOf 2 DS).map ι := hcore_le (hB hx)
    obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hx'
    rwa [hι hw'] at hw
  have hNA' : DS ≤ Subgroup.normalizer (Subgroup.comap ι A : Set
      (SpecialLinearGroup k (DSpace E X))) := by
    intro x hx
    have hxG : ι x ∈ D :=
      ⟨⟨x, rfl⟩, Subgroup.le_normalizer_map (f := ι) (Subgroup.mem_map_of_mem ι hx)⟩
    have hxA : ι x ∈ Subgroup.normalizer (A : Set G) := hNA hxG
    rw [Subgroup.mem_normalizer_iff] at hxA ⊢
    intro a
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    have := hxA (ι a)
    simpa [map_mul, map_inv] using this
  have hNB' : DS ≤ Subgroup.normalizer (Subgroup.comap ι B' : Set
      (SpecialLinearGroup k (DSpace E X))) := by
    intro x hx
    have hxG : ι x ∈ D :=
      ⟨⟨x, rfl⟩, Subgroup.le_normalizer_map (f := ι) (Subgroup.mem_map_of_mem ι hx)⟩
    have hxB : ι x ∈ Subgroup.normalizer (B' : Set G) := hNB hxG
    rw [Subgroup.mem_normalizer_iff] at hxB ⊢
    intro a
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    have := hxB (ι a)
    simpa [map_mul, map_inv] using this
  have hc' : ⁅Subgroup.comap ι B', DS⁆ ≤ Subgroup.comap ι A := by
    rw [Subgroup.commutator_le]
    intro x hx h hh
    rw [Subgroup.mem_comap]
    have hx' : ι x ∈ B' := hx
    have hh' : ι h ∈ D :=
      ⟨⟨h, rfl⟩, Subgroup.le_normalizer_map (f := ι) (Subgroup.mem_map_of_mem ι hh)⟩
    have hcomm := hc (Subgroup.commutator_mem_commutator (H₁ := B') (H₂ := D) hx' hh')
    simpa using hcomm
  have hBA' := rootNoCentral_rootSL hdX hstar (Subgroup.comap ι A) (Subgroup.comap ι B')
    hRA' hAB' hB'' hNA' hNB' hc'
  intro z hz
  have hzrange : z ∈ ι.range := ((pCoreOf_le_self 2 D).trans inf_le_left) (hB hz)
  obtain ⟨w, rfl⟩ := hzrange
  exact hBA' (show w ∈ Subgroup.comap ι B' from hz)

theorem mem_sup_centralizer_of_two_element
    (hdX : Module.finrank k E ≤ Module.finrank k X)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X))
    (ι : SpecialLinearGroup k (DSpace E X) →* G) (hι : Function.Injective ι)
    (y : G) (hy : ∃ m : ℕ, y ^ (2 ^ m) = 1) (hyK : y ∈ Subgroup.normalizer (ι.range : Set G))
    (hyR : y ∈ Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G))
    (hc : ∀ h ∈ ι.range ⊓ Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G),
      y * h * y⁻¹ * h⁻¹ ∈
        pCoreOf 2 (ι.range ⊓ Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G))) :
    y ∈ ι.range ⊔ Subgroup.centralizer (ι.range : Set G) := by
  have hX : 0 < Module.finrank k X := finrank_pos_of_star hdX hstar
  let e : SpecialLinearGroup k (DSpace E X) ≃* ι.range := MonoidHom.ofInjective (f := ι) hι
  let c : MulAut ι.range := (ι.range).normalizerMonoidHom ⟨y, hyK⟩
  let α : MulAut (SpecialLinearGroup k (DSpace E X)) := (e.trans c).trans e.symm
  have hval : ∀ s : SpecialLinearGroup k (DSpace E X), ι (α s) = y * ι s * y⁻¹ := by
    intro s
    have h1 : e (α s) = c (e s) := by
      simp [α]
    have h2 : ((e (α s) : ι.range) : G) = ι (α s) := rfl
    rw [← h2, h1]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (ι.range) ⟨y, hyK⟩ (e s)
  have hpow : ∀ n : ℕ, ∀ s : SpecialLinearGroup k (DSpace E X),
      ι ((α ^ n) s) = y ^ n * ι s * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
        intro s
        simp
    | succ n ih =>
        intro s
        rw [pow_succ, MulAut.mul_apply, ih (α s), hval s, pow_succ]
        group
  have hfix : ∀ s : SpecialLinearGroup k (DSpace E X),
      α s ∈ rootSL k E X ↔ s ∈ rootSL k E X := by
    intro s
    rw [mem_rootSL_iff_map ι hι (α s), mem_rootSL_iff_map ι hι s, hval s]
    exact ((Subgroup.mem_normalizer_iff.mp hyR) (ι s)).symm
  have hR : (rootSL k E X).map α.toMonoidHom = rootSL k E X := by
    apply le_antisymm
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      exact (hfix s).mpr hs
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨α.symm x, ?_, ?_⟩
      · have hx' : α (α.symm x) ∈ rootSL k E X := by
          rw [MulEquiv.apply_symm_apply]
          exact hx
        exact (hfix (α.symm x)).mp hx'
      · exact MulEquiv.apply_symm_apply α x
  have hQKmap : pCoreOf 2 (ι.range ⊓ Subgroup.normalizer
      (((rootSL k E X).map ι : Subgroup G) : Set G)) = (QK k E X).map ι :=
    pCoreOf_inf_normalizer_eq_map_QK hX ι hι
  have hC : ∀ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      α h * h⁻¹ ∈ QK k E X ⊔ Subgroup.center (SpecialLinearGroup k (DSpace E X)) := by
    intro h hh
    have hmem : ι h ∈ ι.range ⊓
        Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G) :=
      ⟨⟨h, rfl⟩, Subgroup.le_normalizer_map (f := ι) (Subgroup.mem_map_of_mem ι hh)⟩
    have hcc : y * ι h * y⁻¹ * (ι h)⁻¹ ∈
        pCoreOf 2 (ι.range ⊓
          Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G)) :=
      hc (ι h) hmem
    have hcc' : ι (α h * h⁻¹) ∈ (QK k E X).map ι := by
      rw [hQKmap] at hcc
      simpa [map_mul, map_inv, hval h] using hcc
    have hmemQK : α h * h⁻¹ ∈ QK k E X := by
      obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp hcc'
      rwa [hι hw'] at hw
    exact Subgroup.mem_sup_left hmemQK
  have h2 : ∃ m : ℕ, α ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hy
    refine ⟨m, ?_⟩
    refine MulEquiv.ext ?_
    intro s
    apply hι
    rw [hpow (2 ^ m) s, hm]
    simp
  obtain ⟨g, hg⟩ := exists_conj_of_two_element_mem_Y hdX hstar α hR hC h2
  have hconj : ∀ s : SpecialLinearGroup k (DSpace E X),
      ι (α s) = ι g * ι s * (ι g)⁻¹ := by
    intro s
    rw [hg]
    simp [MulAut.conj_apply, map_mul]
  have hcent : (ι g)⁻¹ * y ∈ Subgroup.centralizer (ι.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨s, rfl⟩ := hh
    have h2s := hconj s
    rw [hval s] at h2s
    have hc' : ((ι g)⁻¹ * y) * ι s * ((ι g)⁻¹ * y)⁻¹ = ι s := by
      calc ((ι g)⁻¹ * y) * ι s * ((ι g)⁻¹ * y)⁻¹
          = (ι g)⁻¹ * (y * ι s * y⁻¹) * ι g := by group
        _ = (ι g)⁻¹ * (ι g * ι s * (ι g)⁻¹) * ι g := by rw [h2s]
        _ = ι s := by group
    have hcomm : ((ι g)⁻¹ * y) * ι s = ι s * ((ι g)⁻¹ * y) := by
      calc ((ι g)⁻¹ * y) * ι s
          = (((ι g)⁻¹ * y) * ι s * ((ι g)⁻¹ * y)⁻¹) * ((ι g)⁻¹ * y) := by group
        _ = ι s * ((ι g)⁻¹ * y) := by rw [hc']
    exact hcomm.symm
  have hy_eq : y = ι g * ((ι g)⁻¹ * y) := by group
  rw [hy_eq]
  exact Subgroup.mul_mem_sup ⟨g, rfl⟩ hcent

theorem item_three_map (hdX : Module.finrank k E ≤ Module.finrank k X)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X))
    (ι : SpecialLinearGroup k (DSpace E X) →* G) (hι : Function.Injective ι)
    (Y : Subgroup G) (hY : IsPGroup 2 Y) (hYG : Y ≤ Subgroup.normalizer (ι.range : Set G))
    (hYR : Y ≤ Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G))
    (hc : ⁅Y, ι.range ⊓ Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G)⁆ ≤
      pCoreOf 2 (ι.range ⊓ Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G))) :
    Y ≤ ι.range ⊔ Subgroup.centralizer (ι.range : Set G) := by
  intro y hy
  obtain ⟨m, hm⟩ := hY ⟨y, hy⟩
  have hy_pow : y ^ (2 ^ m) = 1 := by
    simpa using congrArg (fun z : Y => (z : G)) hm
  have hc' : ∀ h ∈ ι.range ⊓ Subgroup.normalizer
        (((rootSL k E X).map ι : Subgroup G) : Set G),
      y * h * y⁻¹ * h⁻¹ ∈
        pCoreOf 2 (ι.range ⊓
          Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G)) := by
    intro h hh
    have hcm := hc (Subgroup.commutator_mem_commutator (H₁ := Y) (H₂ := _) hy hh)
    simpa [commutatorElement_def] using hcm
  exact mem_sup_centralizer_of_two_element hdX hstar ι hι y ⟨m, hy_pow⟩ (hYG hy) (hYR hy) hc'

theorem ggRootInnerAt_map (hdX : Module.finrank k E ≤ Module.finrank k X)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X))
    (ι : SpecialLinearGroup k (DSpace E X) →* G) (hι : Function.Injective ι) :
    GGRootInnerAt ι.range ((rootSL k E X).map ι) := by
  unfold GGRootInnerAt
  intro Y hY hYG hYR hnorm
  let D : Subgroup G := ι.range ⊓
    Subgroup.normalizer (((rootSL k E X).map ι : Subgroup G) : Set G)
  have hcommYD : ⁅Y, D⁆ ≤ Y ⊓ D := by
    rw [Subgroup.commutator_le]
    intro y hy h hh
    constructor
    · have hhN : h ∈ Subgroup.normalizer (Y : Set G) := hnorm hh
      have hmem : h * y⁻¹ * h⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp hhN y⁻¹).mp (Y.inv_mem hy)
      have heq : ⁅y, h⁆ = y * (h * y⁻¹ * h⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [heq]
      exact Y.mul_mem hy hmem
    · have hyK : y ∈ Subgroup.normalizer (ι.range : Set G) := hYG hy
      have hyR : y ∈ Subgroup.normalizer
          (((rootSL k E X).map ι : Subgroup G) : Set G) := hYR hy
      have hyhyK : y * h * y⁻¹ ∈ ι.range :=
        (Subgroup.mem_normalizer_iff.mp hyK h).mp hh.1
      have hyhyR : y * h * y⁻¹ ∈ Subgroup.normalizer
          (((rootSL k E X).map ι : Subgroup G) : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_normalizer
          (((rootSL k E X).map ι : Subgroup G)) hyR) h).mp hh.2
      have heq : ⁅y, h⁆ = (y * h * y⁻¹) * h⁻¹ := by
        simp only [commutatorElement_def]
      rw [heq]
      exact D.mul_mem ⟨hyhyK, hyhyR⟩ (D.inv_mem hh)
  have hNnorm : ((Y ⊓ D).subgroupOf D).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer_inf (H := Y) (K := D)).mpr ?_
    exact (le_inf hnorm Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Y) (K := D))
  have hYp : IsPGroup 2 (↥(Y ⊓ D)) := IsPGroup.to_inf_left (K := D) hY
  have hYDcore : Y ⊓ D ≤ pCoreOf 2 D :=
    le_pCoreOf_of_normal 2 (show Y ⊓ D ≤ D from inf_le_right) hNnorm hYp
  have hc : ⁅Y, D⁆ ≤ pCoreOf 2 D := hcommYD.trans hYDcore
  exact item_three_map hdX hstar ι hι Y hY hYG hYR hc

end CFSG.LinearAlgebra.RootGroupSL