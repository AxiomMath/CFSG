module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphFix
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairMat
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Tri
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOResGrp

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.D4
open scoped Pointwise

section Sit

variable {K : Type} [Field K] {d : ℕ}

section Defs

variable (Q : QuadraticForm K (Fin d → K))

structure ClO.D4Sit (t : MulAut (StatedProj (matrixDerived Q)))
    (Ro : Subgroup (MulAut (StatedProj (matrixDerived Q))))
    (y : MulAut (StatedProj (matrixDerived Q))) : Prop where
  inj : Function.Injective (MulAut.conj : StatedProj (matrixDerived Q) →*
    MulAut (StatedProj (matrixDerived Q)))
  odd : Odd (Nat.card Ro)
  comm : ∀ r ∈ Ro, r * t = t * r
  norm : ∀ s, t s = s → Odd (orderOf s) → ∀ r ∈ Ro,
    MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ Ro
  mem : y ∈ Ro
  move : y • ptFam Q ≠ ptFam Q
  geom : D4Geom Q
  rigid : PtRigid Q

end Defs

variable {Q : QuadraticForm K (Fin d → K)}

theorem ClO.congr_conj_eq {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (x : G) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext z
  simp [MulAut.conj_apply]

section Transport

variable {Q' : QuadraticForm K (Fin d → K)} (S : GL (Fin d) K) (ν : Kˣ)
  (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)

theorem ClO.D4Sit.transport {t y : MulAut (StatedProj (matrixDerived Q))}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived Q)))} (h : ClO.D4Sit Q t Ro y) :
    ClO.D4Sit Q' (MulAut.congr (oTransport S ν hS) t)
      (Ro.map (MulAut.congr (oTransport S ν hS)).toMonoidHom)
      (MulAut.congr (oTransport S ν hS) y) := by
  set Θ := oTransport S ν hS with hΘ
  refine ⟨fun x x' hxx' => ?_, ?_, ?_, ?_, ⟨y, h.mem, rfl⟩,
    (smul_ptFam_ne_iff S ν hS y).2 h.move, h.geom.transport S ν hS, h.rigid.transport S ν hS⟩
  · obtain ⟨x, rfl⟩ := Θ.surjective x
    obtain ⟨x', rfl⟩ := Θ.surjective x'
    rw [← ClO.congr_conj_eq, ← ClO.congr_conj_eq] at hxx'
    rw [h.inj ((MulAut.congr Θ).injective hxx')]
  · rw [Subgroup.card_map_of_injective (MulAut.congr Θ).injective]
    exact h.odd
  · rintro _ ⟨r, hr, rfl⟩
    change MulAut.congr Θ r * MulAut.congr Θ t = MulAut.congr Θ t * MulAut.congr Θ r
    rw [← map_mul, ← map_mul, h.comm r hr]
  · rintro s hs hso _ ⟨r, hr, rfl⟩
    obtain ⟨s, rfl⟩ := Θ.surjective s
    have hs' : t s = s := by
      have := congrArg Θ.symm hs
      simpa [MulAut.congr_apply] using this
    have hso' : Odd (orderOf s) := by rwa [MulEquiv.orderOf_eq] at hso
    refine ⟨_, h.norm s hs' hso' r hr, ?_⟩
    change MulAut.congr Θ (MulAut.conj s * r * (MulAut.conj s)⁻¹) = _
    rw [map_mul, map_mul, map_inv, ClO.congr_conj_eq]
    rfl

end Transport

theorem ClO.D4Sit.gram {R R' H : GL (Fin d) K}
    (hgram : (H : Matrix (Fin d) (Fin d) K)ᵀ * R * H = R')
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} {g : similarityPairs (oQ R)}
    (h : ClO.D4Sit (oQ R) (oκ _ g) Ro y) (hg1 : g.val.right = 1) :
    ∃ (Ro' : Subgroup (MulAut (StatedProj (matrixDerived (oQ R')))))
      (y' : MulAut (StatedProj (matrixDerived (oQ R')))) (g' : similarityPairs (oQ R')),
      ClO.D4Sit (oQ R') (oκ _ g') Ro' y' ∧ g'.val.right = 1 ∧
        g'.val.left = H⁻¹ * g.val.left * H := by
  obtain ⟨hS, hl, hr⟩ := exists_transport_of_gram hgram hg1
  have h' := h.transport H⁻¹ 1 hS
  rw [oTransport_kappa] at h'
  exact ⟨_, _, transPair H⁻¹ 1 hS g, h', hr, hl⟩

theorem ClO.D4Sit.exists_commute {t y : MulAut (StatedProj (matrixDerived Q))}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived Q)))} (h : ClO.D4Sit Q t Ro y)
    {x : StatedProj (matrixDerived Q)} (hx : x * x = 1)
    (hxR : ∀ r ∈ Ro, MulAut.conj x * r * (MulAut.conj x)⁻¹ ∈ Ro) :
    ∃ y', ClO.D4Sit Q t Ro y' ∧ MulAut.conj x * y' = y' * MulAut.conj x := by
  set e := MulAut.conj x with he
  have hee : e * e = 1 := by rw [he, ← map_mul, hx, map_one]
  set u := y⁻¹ * (e * y * e⁻¹) with hu
  have huO : u ∈ Ro := mul_mem (inv_mem h.mem) (hxR y h.mem)
  obtain ⟨j, hj⟩ := ClSp.odd_orderOf_of_mem h.odd huO
  have hu1 : u ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one u
  have huN : u ∈ MulAction.stabilizer (MulAut (StatedProj (matrixDerived Q))) (ptFam Q) :=
    commutator_smul_ptFam y x
  set y' := y * u ^ (j + 1) with hy'
  have hφφ : ∀ z, e * (e * z * e⁻¹) * e⁻¹ = z := fun z => by
    calc e * (e * z * e⁻¹) * e⁻¹ = (e * e) * z * (e * e)⁻¹ := by group
      _ = z := by rw [hee]; group
  have heu : e * u * e⁻¹ = u⁻¹ := by
    rw [hu]
    calc e * (y⁻¹ * (e * y * e⁻¹)) * e⁻¹ = (e * y * e⁻¹)⁻¹ * (e * (e * y * e⁻¹) * e⁻¹) := by
          group
      _ = (e * y * e⁻¹)⁻¹ * y := by rw [hφφ]
      _ = (y⁻¹ * (e * y * e⁻¹))⁻¹ := by group
  have hpow : u * (u⁻¹) ^ (j + 1) = u ^ (j + 1) := by
    rw [inv_pow, mul_inv_eq_iff_eq_mul, ← pow_add]
    calc u = u ^ (2 * j + 1) * u := by rw [hu1, one_mul]
      _ = u ^ (j + 1 + (j + 1)) := by
          rw [← pow_succ]
          congr 1
          ring
  have hcomm : e * y' * e⁻¹ = y' := by
    have h1 : e * y * e⁻¹ = y * u := by rw [hu]; group
    calc e * y' * e⁻¹ = (e * y * e⁻¹) * (e * u * e⁻¹) ^ (j + 1) := by
          rw [hy', ← MulAut.conj_apply, map_mul, map_pow, MulAut.conj_apply, MulAut.conj_apply]
      _ = y * (u * (u⁻¹) ^ (j + 1)) := by rw [h1, heu, mul_assoc]
      _ = y' := by rw [hpow]
  refine ⟨y', ⟨h.inj, h.odd, h.comm, h.norm, mul_mem h.mem (pow_mem huO _), fun hF => h.move ?_,
    h.geom, h.rigid⟩, ?_⟩
  · have hpF : u ^ (j + 1) • ptFam Q = ptFam Q := pow_mem huN (j + 1)
    calc y • ptFam Q = y • (u ^ (j + 1) • ptFam Q) := by rw [hpF]
      _ = y' • ptFam Q := by rw [hy', mul_smul]
      _ = ptFam Q := hF
  · calc e * y' = e * y' * e⁻¹ * e := by group
      _ = y' * e := by rw [hcomm]

end Sit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {H : Subgroup (GL ι K)}

theorem ClO.fix_of_compData
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {t : MulAut (StatedProj H)} {Ro : Subgroup (MulAut (StatedProj H))}
    (hRodd : Odd (Nat.card Ro)) (hRi : ∀ r ∈ Ro, r * t = t * r)
    (hRc : ∀ s, t s = s → Odd (orderOf s) → ∀ r ∈ Ro,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ Ro)
    (φ : H →* H) (hφi : Function.Injective φ) (hφ : ∀ g, t (projH H g) = projH H (φ g))
    {F₀ : Subgroup (GL ι K)} (hF₀H : F₀ ≤ H)
    (hF₀φ : ∀ X (hX : X ∈ F₀), φ ⟨X, hF₀H hX⟩ = ⟨X, hF₀H hX⟩)
    (hF₀n : ∀ h : H, φ h = h → ∀ X ∈ F₀, (h : GL ι K) * X * (h : GL ι K)⁻¹ ∈ F₀)
    (hcd : CompData F₀) {y : MulAut (StatedProj H)} (hy : y ∈ Ro)
    {X : GL ι K} (hX : X ∈ F₀) : y (projH H ⟨X, hF₀H hX⟩) = projH H ⟨X, hF₀H hX⟩ := by
  set F₀' := F₀.subgroupOf H with hF₀'
  have hF₀'F : F₀' ≤ MonoidHom.eqLocus φ (MonoidHom.id H) := by
    intro Y hY
    have hY' : (Y : GL ι K) ∈ F₀ := mem_subgroupOf.1 hY
    exact hF₀φ Y hY'
  have hF₀'n : ∀ x ∈ MonoidHom.eqLocus φ (MonoidHom.id H), ∀ q ∈ F₀', x * q * x⁻¹ ∈ F₀' := by
    intro x hx q hq
    have := hF₀n x hx _ (mem_subgroupOf.1 hq)
    exact mem_subgroupOf.2 (by simpa using this)
  obtain ⟨-, m, L, hsup, hL⟩ := hcd
  have hfixL : ∀ i, ∀ Y : H, (Y : GL ι K) ∈ L i → y (projH H Y) = projH H Y := by
    intro i Y hY
    obtain ⟨hq, hLI, hLn⟩ := hL i
    set Lh := (L i).subgroupOf H with hLh
    have hLhq : IsQuasisimple Lh :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hLI.trans hF₀H)).symm hq
    have hLF : Lh ≤ F₀' := fun Z hZ => mem_subgroupOf.2 (hLI (mem_subgroupOf.1 hZ))
    have hLn' : ∀ x ∈ F₀', ∀ l ∈ Lh, x * l * x⁻¹ ∈ Lh := by
      intro x hx l hl
      have hx' : (x : GL ι K) ∈ F₀ := mem_subgroupOf.1 hx
      have hl' : (l : GL ι K) ∈ L i := mem_subgroupOf.1 hl
      exact mem_subgroupOf.2 (by simpa using hLn _ hx' _ hl')
    exact ClU.fix_of_lift_sub hinj hRodd hRi hRc φ hφi hφ hF₀'F hF₀'n hLF hLn' hLhq hy
      (mem_subgroupOf.2 hY)
  have hF₀sup : F₀' ≤ MonoidHom.eqLocus (y.toMonoidHom.comp (projH H)) (projH H) := by
    intro Y hY
    have hY' : (Y : GL ι K) ∈ ⨆ i, L i := by rw [hsup]; exact mem_subgroupOf.1 hY
    have hmap : (⨆ i, (L i).subgroupOf H).map H.subtype = ⨆ i, L i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans hF₀H)]
    rw [← hmap] at hY'
    obtain ⟨Y', hY'L, e⟩ := hY'
    rw [← Subtype.ext e]
    refine (iSup_le fun i Z hZ => ?_ : (⨆ i, (L i).subgroupOf H) ≤ _) hY'L
    exact hfixL i Z (mem_subgroupOf.1 hZ)
  exact hF₀sup (mem_subgroupOf.2 hX)

end CFSG.ComponentClassification.Foote5.OddLieCore
