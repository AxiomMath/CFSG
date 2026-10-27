module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem J₁_mul_self : (J₁ : Matrix (Fin 2) (Fin 2) K) * J₁ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁]

theorem kron_neg_one_neg_one : kron (-1 : Matrix (Fin 2) (Fin 2) K) (-1) = 1 := by
  rw [← kron_one_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp [kron]

theorem u2_mul_w0_conj (h2 : (2 : K) ≠ 0) :
    ∃ g : StatedProj (StatedSp 2 K), g⁻¹ * (u2 K * w0 K) * g = u1 K := by
  set T : StatedSp 2 K := T2 K * diagSL K J₁SL with hT
  have hTm : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      kron J₁ J₁ := by
    rw [hT, Subgroup.coe_mul, Units.val_mul, coe_T2, coe_diagSL, kron_mul, Matrix.one_mul,
      Matrix.mul_one]
    rfl
  have hTT : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [hTm, kron_mul, J₁_mul_self, kron_neg_one_neg_one]
  have h1 : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 1 := by
    rw [hTm]
    intro h
    have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
    simp [kron, J₁] at this
  have hm : ((T : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ -1 := by
    rw [hTm]
    intro h
    have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
    simp [kron, J₁] at this
  obtain ⟨g, hg⟩ := exists_conj_T1 h2 T hTT h1 hm
  refine ⟨proj 2 K g, ?_⟩
  rw [u2, w0, ← map_mul, ← map_inv, ← map_mul, ← map_mul, ← hT, hg, u1]

theorem exists_conj_u2_mul [Finite K] (h2 : (2 : K) ≠ 0)
    (hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    {w : StatedProj (StatedSp 2 K)} (hw : w ∈ Lsub K) (hord : orderOf w = 2) :
    ∃ g : StatedProj (StatedSp 2 K), g⁻¹ * (u2 K * w) * g = u1 K := by
  obtain ⟨l, hl, hlw⟩ := exists_conj_w0 hpp hw hord
  obtain ⟨g, hg⟩ := u2_mul_w0_conj h2
  have hlu : l * u2 K = u2 K * l := mem_centralizer_singleton_iff.mp (Lsub_le_centralizer hl)
  have hlu' : l⁻¹ * u2 K * l = u2 K := by rw [mul_assoc, ← hlu, inv_mul_cancel_left]
  refine ⟨l * g, ?_⟩
  rw [← hlw]
  calc (l * g)⁻¹ * (u2 K * (l * w0 K * l⁻¹)) * (l * g)
      = g⁻¹ * ((l⁻¹ * u2 K * l) * w0 K) * g := by group
    _ = u1 K := by rw [hlu', hg]

theorem exists_sl2_component_P [Finite K] (hodd : Odd (Nat.card K))
    (hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    {t w : StatedProj (StatedSp 2 K)} (ht : orderOf t = 2) (hw : orderOf w = 2) (hwt : w ≠ t)
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hMt : M ≤ centralizer {t})
    (hM : CFSG.IsPComponent 2 (M.subgroupOf (centralizer {t}))) (hwM : w ∈ M) :
    ∃ N : Subgroup (StatedProj (StatedSp 2 K)), N ≤ centralizer {t * w} ∧
      CFSG.IsPComponent 2 (N.subgroupOf (centralizer {t * w})) ∧ t * w ∈ N ∧
      Nonempty (↥N ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd ht
  have hM' := isPComponent_map_subgroupOf 2 φ hMt hM
  have hMX' := Subgroup.map_mono (f := φ.toMonoidHom) hMt
  rw [map_centralizer_singleton] at hM' hMX'
  have hw' : φ w ∈ M.map φ.toMonoidHom := mem_map_of_mem _ hwM
  have hwo' : orderOf (φ w) = 2 := by rw [MulEquiv.orderOf_eq, hw]
  rcases hφ with h | h <;> rw [h] at hM' hMX'
  · exfalso
    obtain ⟨hE | hE, -⟩ := CatFactsSp4.pComponent_centralizer_u1 hodd hMX' hM' <;>
      rw [hE] at hw'
    · exact hwt (φ.injective ((eq_u1_of_mem_E1 h2 hw' hwo').trans h.symm))
    · exact hwt (φ.injective ((eq_u1_of_mem_E2 h2 hw' hwo').trans h.symm))
  · obtain ⟨hL, h5⟩ := CatFactsSp4.pComponent_centralizer_u2 hodd hMX' hM'
    rw [hL] at hw'
    obtain ⟨g, hg⟩ := exists_conj_u2_mul h2 hpp hw' hwo'
    set ψ : StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 K) :=
      φ.trans (MulAut.conj g⁻¹) with hψ
    have hψtw : ψ (t * w) = u1 K := by
      rw [hψ, MulEquiv.trans_apply, map_mul, h, MulAut.conj_apply, inv_inv, hg]
    have hψs : ψ.symm (u1 K) = t * w := by rw [← hψtw, MulEquiv.symm_apply_apply]
    have h4 : 4 ≤ Nat.card K := by omega
    have hE1 := isPComponent_map_subgroupOf 2 ψ.symm (E1_le_centralizer_u1 h2)
      (isPComponent_E1 h2 h4)
    have hE1X := Subgroup.map_mono (f := ψ.symm.toMonoidHom) (E1_le_centralizer_u1 h2)
    rw [map_centralizer_singleton, hψs] at hE1 hE1X
    refine ⟨(E1 K).map ψ.symm.toMonoidHom, hE1X, hE1, ?_, ?_⟩
    · rw [← hψs]
      exact mem_map_of_mem _ u1_mem_E1
    · exact ⟨((E1 K).equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).symm.trans
        (E1Equiv h2).symm⟩

noncomputable def slRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := Subtype.ext (by ext i j; simp)
  right_inv A := Subtype.ext (by ext i j; simp)
  map_mul' A B := map_mul _ A B

theorem exists_sl2_galoisField_card [Finite K] (hK : ringChar K ≠ 2) :
    ∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* SL(2, GaloisField p n)) ∧
      p ^ n = Nat.card K := by
  have := Fintype.ofFinite K
  set p := ringChar K with hpdef
  have hp : p.Prime := CharP.char_is_prime K p
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, -, hcard⟩ := FiniteField.card K p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have hKc : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  exact ⟨p, f, inferInstance, hK, f.pos, ⟨slRingEquiv
    (GaloisField.algEquivGaloisField p f hKc).toRingEquiv⟩, hKc.symm⟩

theorem exists_sl2_galoisField [Finite K] (hK : ringChar K ≠ 2) :
    ∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* SL(2, GaloisField p n)) := by
  obtain ⟨p, n, hp, hp2, hn, he, -⟩ := exists_sl2_galoisField_card hK
  exact ⟨p, n, hp, hp2, hn, he⟩

theorem cfSp4Prod :
    ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel Y .PSp 2 p f → ∀ t w : Y, orderOf t = 2 → orderOf w = 2 → w ≠ t →
        ∀ M : Subgroup Y, M ≤ centralizer ({t} : Set Y) →
          IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) → w ∈ M →
          ∃ N : Subgroup Y, N ≤ centralizer ({t * w} : Set Y) ∧
            IsPComponent 2 (N.subgroupOf (centralizer ({t * w} : Set Y))) ∧ t * w ∈ N ∧
            ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
              Nonempty (↥N ≃* SL(2, GaloisField p' n)) := by
  intro Y _ _ p f hp hp2 hf hY t w ht hw hwt M hMt hM hwM
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hodd := odd_card_of_card_eq hp hp2 hK
  have hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩
  have hM' := isPComponent_map_subgroupOf 2 e hMt hM
  have hMX' := Subgroup.map_mono (f := e.toMonoidHom) hMt
  rw [map_centralizer_singleton] at hM' hMX'
  have hwt' : e w ≠ e t := fun h => hwt (e.injective h)
  obtain ⟨N, hNt, hN, htwN, ⟨eN⟩⟩ := exists_sl2_component_P hodd hpp
    (by rw [MulEquiv.orderOf_eq, ht]) (by rw [MulEquiv.orderOf_eq, hw]) hwt' hMX' hM'
    (mem_map_of_mem _ hwM)
  have hs : e.symm (e t * e w) = t * w := by rw [← map_mul, MulEquiv.symm_apply_apply]
  have hN' := isPComponent_map_subgroupOf 2 e.symm hNt hN
  have hNX' := Subgroup.map_mono (f := e.symm.toMonoidHom) hNt
  rw [map_centralizer_singleton, hs] at hN' hNX'
  have h2 := two_ne_zero_of_odd_card hodd
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have h3 : ((2 : ℕ) : K) = 0 := (ringChar.spec K 2).mpr (by simp [h])
    exact_mod_cast h3
  obtain ⟨p', n, hp', hp'2, hn, ⟨eK⟩⟩ := exists_sl2_galoisField hchar
  refine ⟨N.map e.symm.toMonoidHom, hNX', hN', ?_, p', n, hp', hp'2, hn, ⟨?_⟩⟩
  · rw [← hs]
    exact mem_map_of_mem _ htwN
  · exact ((N.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eN).trans eK

end CFSG.ComponentClassification.CatFactsSp4
