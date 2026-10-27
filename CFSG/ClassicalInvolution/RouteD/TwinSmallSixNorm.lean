module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallLeafSpin
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLocal
public import CFSG.ClassicalInvolution.RouteD.LocalTwinAdapt
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts (map_longSL2_range)
open scoped MatrixGroups

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Spin

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {KY : Type} [Group KY] {𝓕 : Set (Subgroup KY)}
  {Z' : Subgroup (V ≃ₗ[F] V)} {π : KY →* (V ≃ₗ[F] V)}

omit [Finite F] in
theorem normalizes_of_image_normalizes (cq : CentralQuot π 𝓕 (fundSet Q) Z') {R : Subgroup KY}
    (hR : R ∈ 𝓕) {r : KY}
    (hN : π r ∈ Subgroup.normalizer ((R.map π : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V))) :
    ∀ y ∈ R, r * y * r⁻¹ ∈ R := by
  refine conj_mem_of_perfect (cq.perf R hR).ge r fun x hx => ?_
  have hmem : π (r * x * r⁻¹) ∈ R.map π := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hN (π x)).mp ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hye⟩ := hmem
  refine ⟨y, hy, y⁻¹ * (r * x * r⁻¹), cq.ker_le ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hye, inv_mul_cancel]

end Spin

section Leaf

variable {p f : ℕ} [Fact p.Prime]

theorem exists_leaf_subgroup_norm (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 4 ≤ m)
    {i j : Fin (m - 1)} (hij : i ≠ j) (s t : Bool) :
    ∃ R : Subgroup (SpinM p f m),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)) ∧
      (∀ (k l : ℕ) (hk : k < m - 1) (hl : l < m - 1) (hkl : k ≠ l), k ≠ i.val → k ≠ j.val →
        l ≠ i.val → l ≠ j.val → ∀ s' t' : Bool,
          Commutes R (rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2) k l hk hl hkl
            s' t')) ∧
      ¬ Commutes (rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2) i.val j.val i.isLt
        j.isLt (fun h => hij (Fin.ext h)) s t) R ∧
      R ≠ rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2) i.val j.val i.isLt
        j.isLt (fun h => hij (Fin.ext h)) s t ∧
      (∀ r', InvOf R r' → ∀ y ∈ rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2)
        i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)) s t,
          r' * y * r'⁻¹ ∈ rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2)
            i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)) s t) ∧
      (∀ r r', InvOf R r → InvOf (rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2)
        i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)) s t) r' → r * r' = r' * r) := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have cq := Exotic.centralQuot_minus hp2 hq ⟨Fact.out, hf1, hm⟩
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨F_N, hv₀, hα, hperp, hcomm, hfin, hncomm, hne⟩ :=
    exists_leaf_frame (minusCoeffs_irr p f) hodd hij s t
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hL : F_N.La.range ∈ fundSet (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) := ⟨F_N.La (-1), IsFundamental.of_frame F_N⟩
  obtain ⟨R, hR, hRmap⟩ := cq.surj _ hL
  have hD : rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2) i.val j.val i.isLt
      j.isLt (fun h => hij (Fin.ext h)) s t ∈
      fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr p f)) :=
    rootSL2_mem_fund hq hm hp2 i.isLt j.isLt (fun h => hij (Fin.ext h)) s t
  have hDmap : (rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2) i.val j.val i.isLt
      j.isLt (fun h => hij (Fin.ext h)) s t).map (spinAction (quadMinus m (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2)) =
      ((minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2).toFrame hij s t).La.range :=
    map_longSL2_range _ hij s t
  have hFD : IsFundamental (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (((minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2).toFrame hij
        s t).La.range) (((minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2).toFrame hij s t).La
          (-1)) := IsFundamental.of_frame _
  have hFN : IsFundamental (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) F_N.La.range (F_N.La (-1)) := IsFundamental.of_frame _
  have hN : F_N.La (-1) ∈ Subgroup.normalizer
      ((((minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2).toFrame hij s t).La.range :
        Subgroup _) : Set _) := by
    refine (mem_normalizer_iff_even hodd hFD hFN hcomm).mpr ?_
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2, hfin]
    exact ⟨1, rfl⟩
  refine ⟨R, hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro k l hk hl hkl hki hkj hli hlj s' t'
    have hkl' : (⟨k, hk⟩ : Fin (m - 1)) ≠ ⟨l, hl⟩ := fun h => hkl (congrArg Fin.val h)
    have hmap : (rootSL2 (minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2) k l hk hl hkl
        s' t').map (spinAction (quadMinus m (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)) =
        ((minusHyp m (minusCoeffs p f).1 (minusCoeffs p f).2).toFrame hkl' s' t').La.range :=
      map_longSL2_range _ hkl' s' t'
    refine (cq.commutes_iff hR).mp ?_
    rw [hRmap, hmap]
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    refine Frame.La_comm_of_orth (fun X Y => ?_) A B
    have hkI : (⟨k, hk⟩ : Fin (m - 1)) ≠ i := fun h => hki (congrArg Fin.val h)
    have hkJ : (⟨k, hk⟩ : Fin (m - 1)) ≠ j := fun h => hkj (congrArg Fin.val h)
    have hlI : (⟨l, hl⟩ : Fin (m - 1)) ≠ i := fun h => hli (congrArg Fin.val h)
    have hlJ : (⟨l, hl⟩ : Fin (m - 1)) ≠ j := fun h => hlj (congrArg Fin.val h)
    have hx : F_N.incl X ∈ F_N.span := ⟨X, rfl⟩
    generalize F_N.incl X = x at hx ⊢
    have h1 := hperp x hx ⟨k, hk⟩ hkI hkJ
    have h2' := hperp x hx ⟨l, hl⟩ hlI hlJ
    simp only [Frame.incl_apply, polar_add_right, polar_smul_right]
    simp [HypFrame.toFrame, h1, h2']
  · intro hc
    have := (cq.commutes_iff hR).mpr (commutes_symm hc)
    rw [hRmap, hDmap] at this
    exact hncomm (commutes_symm this)
  · intro h
    have := congrArg (Subgroup.map (spinAction (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))) h
    rw [hRmap, hDmap] at this
    exact hne this.symm
  · intro r' hr' y hy
    have hFN' : IsFundamental (quadMinus m (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) (R.map (spinAction (quadMinus m (GaloisField p f)
          (minusCoeffs p f).1 (minusCoeffs p f).2))) (F_N.La (-1)) := by
      rw [hRmap]
      exact hFN
    have hπr' : spinAction (quadMinus m (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) r' = F_N.La (-1) := map_invOf_eq hodd cq hR hFN' hr'
    exact normalizes_of_image_normalizes cq hD (r := r') (by rw [hπr', hDmap]; exact hN) y hy
  · intro r r' hr hr'
    have := invs_commute_of_normalizes hodd cq hD hR (i := ((minusHyp m (minusCoeffs p f).1
      (minusCoeffs p f).2).toFrame hij s t).La (-1)) (i' := F_N.La (-1))
      (by rw [hDmap]; exact hFD) (by rw [hRmap]; exact hFN) (by rw [hDmap]; exact hN) r' r hr' hr
    exact this.symm

end Leaf

section Glue

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G} {x : G}

theorem conjSub_eq_of_normalizes (cx : TCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w' : G}
    (hw' : IsClassicalMember p f L' w')
    (hnorm : ∀ r', InvOf R' r' → ∀ y ∈ R, r' * y * r'⁻¹ ∈ R) : conjSub w' L = L := by
  have hwx : w' ∈ locLayer Ω x := le_centralizingLayer hL' hw'.mem
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund cx hL' hR' hLR' hw'
  have hw'x : w' * x * w'⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hL'.2 hw'.mem)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmem : conjSub w' L ∈ centralizingMembers Ω {x} := by
    have h := centralizingMembers_conj cx.hΩ.conjInvariant w' x
    rw [hw'x] at h
    rw [h]
    exact ⟨L, hL, rfl⟩
  refine cx.eq_of_locImg_eq hmem hL ?_
  rw [locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w', hwx⟩, hLR]
  have hψ : locMk Ω x ⟨w', hwx⟩ = cx.d.ψ r' := hψr'.symm
  rw [hψ, map_conj_map_hom]
  congr 1
  have hrr : r' * r' = 1 := by
    have := pow_orderOf_eq_one r'
    rwa [hr'.2, pow_two] at this
  have hri : r'⁻¹ = r' := inv_eq_of_mul_eq_one_right hrr
  ext y
  rw [mem_conjSub_iff, hri]
  constructor
  · intro h
    have := hnorm r' hr' _ h
    rw [hri] at this
    rwa [show r' * (r' * y * r') * r' = y by
      calc r' * (r' * y * r') * r' = (r' * r') * y * (r' * r') := by group
        _ = y := by rw [hrr]; group] at this
  · intro h
    have := hnorm r' hr' y h
    rwa [hri] at this

end Glue

end CFSG.ClassicalInvolution.RouteD.TwinSmall
