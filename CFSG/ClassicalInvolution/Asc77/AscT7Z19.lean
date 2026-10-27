module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z18
public import CFSG.ClassicalInvolution.Asc77.AscT7Z9
public import CFSG.ClassicalInvolution.Asc77.AscT7L24

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr)
open scoped commutatorElement MatrixGroups

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]


theorem ySide6_model (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {ω : GaloisField p f} (hω : ω * ω = -1)
    {Φ : Set (Subgroup G)} (P : ModelLayer .PSU 4 p f Φ) {J J' : Subgroup G} {t a b : G}
    (hJ : J ∈ Φ) (hJ' : J' ∈ Φ) (eJ : Nonempty (↥J ≃* SL(2, GaloisField p f)))
    (eJ' : Nonempty (↥J' ≃* SL(2, GaloisField p f))) (hne : J ≠ J')
    (hcomm : Commutes J J') (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t)
    (ha : a ∈ J) (hb : b ∈ J') (haa : a * a = t) (hbb : b * b = t) :
    ∃ K₃ : Subgroup G, (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V J K₃) ∧
      K₃ ≤ Subgroup.centralizer ({a * b} : Set G) ∧ K₃ ≤ ⁅K₃, K₃⁆ ∧
      omegaGen Φ ≤ J ⊔ K₃ ∧ K₃ ≤ omegaGen Φ := by
  classical
  have := fact_shortField (minusCoeffs_irr p f)
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf0⟩
  have : NeZero (2 * f) := ⟨by omega⟩
  have hadm : StatedLieAdmissible .PSU 4 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf0, by norm_num, fun h => by
      have := congrArg Prod.fst h
      simp at this⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq
  have h2K : (2 : GaloisField p (2 * f)) ≠ 0 :=
    two_ne_zero_of_charP_ne_two (K := GaloisField p (2 * f)) (p := p) hp2
  obtain ⟨φ, hφ⟩ := RouteD.psu_model_equiv hp2 hadm
  have hfin : Finite (modelUniv .PSU 4 p f Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (by trivial) hadm
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund J hJ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund J' hJ'
  have hi₁ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ hJR eJ
  have hi₂ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ' hJ'R eJ'
  have hperf : RJ ≤ ⁅RJ, RJ⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 (by trivial) hadm (by omega) RJ hRJ
  obtain ⟨a₀, ha₀, hψa⟩ := (hJR ▸ ha : a ∈ RJ.map P.ψ)
  obtain ⟨b₀, hb₀, hψb⟩ := (hJ'R ▸ hb : b ∈ RJ'.map P.ψ)
  have hcomm' : Commutes RJ RJ' := by
    refine commutes_of_map_commutes P.ψ P.ker_le hperf ?_
    rw [← hJR, ← hJ'R]
    exact hcomm
  have hxR : a₀ * a₀ ∈ RJ := RJ.mul_mem ha₀ ha₀
  have hx'R : b₀ * b₀ ∈ RJ' := RJ'.mul_mem hb₀ hb₀
  have hψx : P.ψ (a₀ * a₀) = t := by rw [map_mul, hψa, haa]
  have hψx' : P.ψ (b₀ * b₀) = t := by rw [map_mul, hψb, hbb]
  have hx2 : (a₀ * a₀) * (a₀ * a₀) = 1 := hi₁ _ (RJ.mul_mem hxR hxR) (by
    rw [map_mul, hψx, htJ.sq])
  have hx'2 : (b₀ * b₀) * (b₀ * b₀) = 1 := hi₂ _ (RJ'.mul_mem hx'R hx'R) (by
    rw [map_mul, hψx', htJ'.sq])
  have hx1 : a₀ * a₀ ≠ 1 := fun h => htJ.ne_one (by rw [← hψx, h, map_one])
  have hx'1 : b₀ * b₀ ≠ 1 := fun h => htJ'.ne_one (by rw [← hψx', h, map_one])
  have hc : (b₀ * b₀) * (a₀ * a₀)⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p f Fact.out).K := by
    refine P.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψx, hψx', mul_inv_cancel]
  have hne' : RJ ≠ RJ' := by
    intro h
    apply hne
    rw [hJR, hJ'R, h]
  have hR₁ : RJ.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by norm_num : 2 ≤ 4) := (hφ RJ).mp hRJ
  have hR₁' : RJ'.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p)
      (f := f) (by norm_num : 2 ≤ 4) := (hφ RJ').mp hRJ'
  have hne₁ : RJ.map φ.toMonoidHom ≠ RJ'.map φ.toMonoidHom := fun h =>
    hne' (Subgroup.map_injective φ.injective h)
  have hc₁ : φ (b₀ * b₀) * (φ (a₀ * a₀))⁻¹ ∈
      Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    rw [← map_inv, ← map_mul]
    exact (MulEquivClass.apply_mem_center_iff φ).2 hc
  obtain ⟨c₁, hxc₁, habc₁⟩ := T7L.exists_conj_x0_u0_su hK hp2 hR₁ hR₁' hne₁
    (x := φ (a₀ * a₀)) (x' := φ (b₀ * b₀)) ⟨_, hxR, rfl⟩ (by rw [← map_mul, hx2, map_one])
    (fun h => hx1 (φ.injective (h.trans (map_one φ).symm))) ⟨_, hx'R, rfl⟩
    (by rw [← map_mul, hx'2, map_one])
    (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc₁ (a := φ a₀) (b := φ b₀)
    ⟨a₀, ha₀, rfl⟩ (by rw [← map_mul]) ⟨b₀, hb₀, rfl⟩ (by rw [← map_mul])
  obtain ⟨e, Rs', x, x', a', b', hRs, hRs', hne2, hxRs, hx2', hx1', hx'Rs', hx'2', hx'1',
    hxc2, ha'Rs, ha'a', hb'Rs', hb'b', hS2, hsup2⟩ := spin_adapted hp2 hq hω
  obtain ⟨c₂, hxc₂, habc₂⟩ := T7L.exists_conj_x0_u0_su hK hp2 hRs hRs' hne2 hxRs hx2' hx1'
    hx'Rs' hx'2' hx'1' hxc2 ha'Rs ha'a' hb'Rs' hb'b'
  set g : Su (GaloisField p (2 * f)) p f 4 := c₁ * c₂⁻¹ with hg
  have hgx : g * x * g⁻¹ = φ (a₀ * a₀) := by
    rw [hg, hxc₂, hxc₁]
    group
  have hgab : g * (a' * b') * g⁻¹ = φ a₀ * φ b₀ := by
    rw [hg, habc₂, habc₁]
    group
  set Rs : Subgroup (Su (GaloisField p (2 * f)) p f 4) :=
    (spinMinusModel (minusCoeffs_irr p f)).lb.range.map e.toMonoidHom with hRsdef
  have hord : ∀ y : Su (GaloisField p (2 * f)) p f 4, y * y = 1 → y ≠ 1 → orderOf y = 2 :=
    fun y hy2 hy1 => orderOf_eq_prime (by rwa [pow_two]) hy1
  have hRsg : Rs.map (MulAut.conj g).toMonoidHom = RJ.map φ.toMonoidHom := by
    obtain ⟨i, hi⟩ := hRs
    obtain ⟨i₁, hi₁'⟩ := hR₁
    have hxi : x = i := hi.eq_of_orderOf_eq_two hK hp2 hxRs (hord x hx2' hx1')
    have hxi₁ : φ (a₀ * a₀) = i₁ := hi₁'.eq_of_orderOf_eq_two hK hp2 ⟨_, hxR, rfl⟩
      (hord _ (by rw [← map_mul, hx2, map_one])
        (fun h => hx1 (φ.injective (h.trans (map_one φ).symm))))
    rw [(hi.conj g).eq_longRootGroupSU h2K, hi₁'.eq_longRootGroupSU h2K, ← hxi₁, ← hgx, hxi]
  let Θ : spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ≃*
      (modelUniv .PSU 4 p f Fact.out).K := e.trans ((MulAut.conj g).trans φ.symm)
  have hΘ : ∀ y, Θ y = φ.symm (g * e y * g⁻¹) := fun y => rfl
  have hlb : (spinMinusModel (minusCoeffs_irr p f)).lb.range.map Θ.toMonoidHom = RJ := by
    have h1 : (spinMinusModel (minusCoeffs_irr p f)).lb.range.map Θ.toMonoidHom =
        (Rs.map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom := by
      rw [hRsdef, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hRsg, Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext y
      simp
    rw [this, Subgroup.map_id]
  have hΘinj : Function.Injective Θ := Θ.injective
  have h2F : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hlbinj : Function.Injective (spinMinusModel (minusCoeffs_irr p f)).lb :=
    RouteD.injective_minusLongBlock (minusCoeffs_irr p f) h2F
  set θ : spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) →* G :=
    P.ψ.comp Θ.toMonoidHom with hθ
  have hpair : TwistedB2BlockPair (minusCoeffs_irr p f) θ.range J
      ((spinMinusModel (minusCoeffs_irr p f)).sb.range.map θ) := by
    refine ⟨θ, rfl, ?_, ?_, ?_, rfl⟩
    · intro y hy
      have hy' : P.ψ (Θ y) = 1 := hy
      exact (MulEquivClass.apply_mem_center_iff Θ).1 (P.ker_le (MonoidHom.mem_ker.mpr hy'))
    · intro A B hAB
      have hmem : ∀ C, Θ ((spinMinusModel (minusCoeffs_irr p f)).lb C) ∈ RJ := fun C => by
        rw [← hlb]
        exact ⟨_, ⟨C, rfl⟩, rfl⟩
      have h1 : P.ψ (Θ ((spinMinusModel (minusCoeffs_irr p f)).lb A)) =
          P.ψ (Θ ((spinMinusModel (minusCoeffs_irr p f)).lb B)) := hAB
      have h2' : (Θ ((spinMinusModel (minusCoeffs_irr p f)).lb A))⁻¹ *
          Θ ((spinMinusModel (minusCoeffs_irr p f)).lb B) = 1 := by
        apply hi₁
        · exact RJ.mul_mem (RJ.inv_mem (hmem A)) (hmem B)
        · rw [map_mul, map_inv, h1, inv_mul_cancel]
      exact hlbinj (hΘinj (inv_mul_eq_one.mp h2'))
    · rw [← Subgroup.map_map, hlb, ← hJR]
  have hg6 : RouteD.SpinMinus6Generated (minusCoeffs_irr p f) :=
    RouteD.spinMinus6Generated_galois hp2
  have hF4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf0]
    omega
  have hψab : P.ψ (a₀ * b₀) = a * b := by rw [map_mul, hψa, hψb]
  refine ⟨(spinMinusModel (minusCoeffs_irr p f)).sb.range.map θ, ⟨_, hpair⟩, ?_,
    (RouteD.twistedB2BlockPair_perfect hF4 hpair).2, ?_, ?_⟩
  · rintro _ ⟨s, ⟨B, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : e ((spinMinusModel (minusCoeffs_irr p f)).sb B) * (a' * b') =
        (a' * b') * e ((spinMinusModel (minusCoeffs_irr p f)).sb B) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hS2 ⟨_, ⟨B, rfl⟩, rfl⟩)
    have h2' : Θ ((spinMinusModel (minusCoeffs_irr p f)).sb B) * (a₀ * b₀) =
        (a₀ * b₀) * Θ ((spinMinusModel (minusCoeffs_irr p f)).sb B) := by
      apply φ.injective
      rw [map_mul, map_mul, map_mul, hΘ, MulEquiv.apply_symm_apply, map_mul, ← hgab]
      calc g * e ((spinMinusModel (minusCoeffs_irr p f)).sb B) * g⁻¹ * (g * (a' * b') * g⁻¹)
          = g * (e ((spinMinusModel (minusCoeffs_irr p f)).sb B) * (a' * b')) * g⁻¹ := by group
        _ = g * ((a' * b') * e ((spinMinusModel (minusCoeffs_irr p f)).sb B)) * g⁻¹ := by
          rw [h1]
        _ = g * (a' * b') * g⁻¹ * (g * e ((spinMinusModel (minusCoeffs_irr p f)).sb B) * g⁻¹) := by
          group
    have h3 := congrArg P.ψ h2'
    simp only [map_mul, hψa, hψb] at h3
    exact h3
  ·
    rw [← P.range_eq]
    have htop : (spinMinusModel (minusCoeffs_irr p f)).lb.range.map Θ.toMonoidHom ⊔
        (spinMinusModel (minusCoeffs_irr p f)).sb.range.map Θ.toMonoidHom = ⊤ := by
      rw [← Subgroup.map_sup, hg6, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr Θ.surjective
    rw [hlb] at htop
    have h5 : J ⊔ (spinMinusModel (minusCoeffs_irr p f)).sb.range.map θ = P.ψ.range := by
      rw [hJR, hθ, ← Subgroup.map_map, ← Subgroup.map_sup, htop, Subgroup.map_top]
    exact h5.ge
  · rw [← P.range_eq]
    rintro _ ⟨s, ⟨B, rfl⟩, rfl⟩
    exact ⟨Θ _, rfl⟩

end T7Z

end CFSG.ClassicalInvolution.Asc77
