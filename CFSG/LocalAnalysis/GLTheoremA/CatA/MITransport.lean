module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIFunct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExc
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Assembly CFSG.StandardType

section Abstract

variable {M M' : Type} [Group M] [Group M']

@[expose] noncomputable def centerQuotCongr (Ψ : M ≃* M') {H : Subgroup M} {H' : Subgroup M'}
    (hH : H.map Ψ.toMonoidHom = H') : LargeEvenCenterQuot H ≃* LargeEvenCenterQuot H' :=
  QuotientGroup.congr (Subgroup.center ↥H) (Subgroup.center ↥H')
    ((Ψ.subgroupMap H).trans (MulEquiv.subgroupCongr hH)) (Subgroup.map_center_eq _)

theorem centerQuotCongr_mk (Ψ : M ≃* M') {H : Subgroup M} {H' : Subgroup M'}
    (hH : H.map Ψ.toMonoidHom = H') (h : H) (h' : H') (hh : (h' : M') = Ψ h) :
    centerQuotCongr Ψ hH (LargeEvenCenterMk H h) = LargeEvenCenterMk H' h' := by
  change QuotientGroup.mk (((Ψ.subgroupMap H).trans (MulEquiv.subgroupCongr hH)) h) = _
  congr 1
  exact Subtype.ext hh.symm

theorem congr_conj (τ : M ≃* M') (r : M) : MulAut.congr τ (MulAut.conj r) = MulAut.conj (τ r) := by
  ext s
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem parentConj_transport (Ψ : M ≃* M') {P H : Subgroup M} {P' H' : Subgroup M'}
    (hP : P.map Ψ.toMonoidHom = P') (hH : H.map Ψ.toMonoidHom = H')
    {φ : MulAut (LargeEvenCenterQuot H)} (hφ : φ ∈ LargeEvenParentConjImage P H) :
    MulAut.congr (centerQuotCongr Ψ hH) φ ∈ LargeEvenParentConjImage P' H' := by
  obtain ⟨g, hgP, hgN, hact⟩ := hφ
  have hmemH : ∀ x : M, x ∈ H ↔ Ψ x ∈ H' := fun x => by
    rw [← hH]; exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => Ψ.injective hyx ▸ hy⟩
  refine ⟨Ψ g, hP ▸ ⟨g, hgP, rfl⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hgN ⊢
    intro x'
    obtain ⟨x, rfl⟩ := Ψ.surjective x'
    rw [← hmemH, ← map_mul, ← map_inv, ← map_mul, ← hmemH]
    exact hgN x
  · intro h₁
    set x : H := ⟨Ψ.symm h₁, (hmemH _).2 (by simpa using h₁.2)⟩ with hx
    obtain ⟨x', hx'v, hφx⟩ := hact x
    have hx1 : (h₁ : M') = Ψ (x : M) := by simp [hx]
    refine ⟨⟨Ψ x', (hmemH _).1 x'.2⟩, ?_, ?_⟩
    · show Ψ (x' : M) = Ψ g * (h₁ : M') * (Ψ g)⁻¹
      rw [hx'v, hx1, map_mul, map_mul, map_inv]
    · have e1 : centerQuotCongr Ψ hH (LargeEvenCenterMk H x) = LargeEvenCenterMk H' h₁ :=
        centerQuotCongr_mk Ψ hH x h₁ hx1
      have e2 : centerQuotCongr Ψ hH (LargeEvenCenterMk H x') =
          LargeEvenCenterMk H' ⟨Ψ x', (hmemH _).1 x'.2⟩ :=
        centerQuotCongr_mk Ψ hH x' ⟨Ψ x', (hmemH _).1 x'.2⟩ rfl
      rw [MulAut.congr_apply, ← e1, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply, hφx, e2]

end Abstract

section Chev

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {K L : Type} [Field K] [Field L]

theorem chevParentID_congr (hK : Nat.card K = 2)
    {P H : Subgroup (LargeEvenChevGL A K)} {P' H' : Subgroup (LargeEvenChevGL A L)}
    (Ψ : LargeEvenChevGL A K ≃* LargeEvenChevGL A L) (hP : P.map Ψ.toMonoidHom = P')
    (hH : H.map Ψ.toMonoidHom = H') {φ : MulAut (LargeEvenCenterQuot H)}
    (hφ : φ ∈ LargeEvenChevParentIDImage A K P H) :
    MulAut.congr (centerQuotCongr Ψ hH) φ ∈ LargeEvenChevParentIDImage A L P' H' := by
  have hle : (Subgroup.closure (LargeEvenChevIDImage A K H ∪ LargeEvenParentConjImage P H)).map
      (MulAut.congr (centerQuotCongr Ψ hH)).toMonoidHom ≤
      Subgroup.closure (LargeEvenChevIDImage A L H' ∪ LargeEvenParentConjImage P' H') := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨ψ, hψ | hψ, rfl⟩
    · have hψ' : ψ ∈ (MulAut.conj : LargeEvenCenterQuot H →* _).range := by
        rw [← chevID_closure_eq_inn_of_card_two hK H]
        exact hψ
      obtain ⟨x, rfl⟩ := hψ'
      refine Subgroup.subset_closure (Or.inl ?_)
      rw [MulEquiv.coe_toMonoidHom, congr_conj]
      exact conj_mem_chevIDImage H' _
    · exact Subgroup.subset_closure (Or.inr (parentConj_transport Ψ hP hH hψ))
  exact hle ⟨φ, hφ, rfl⟩

end Chev

theorem normal_of_outComm {R : Type} [Group R] (hO : GGOutComm R) {J : Subgroup (MulAut R)}
    (hJ : ∀ r : R, MulAut.conj r ∈ J) (α : MulAut R) {φ : MulAut R} (hφ : φ ∈ J) :
    α * φ * α⁻¹ ∈ J := by
  obtain ⟨r, hr⟩ := hO α φ
  have h1 : α * φ * α⁻¹ = MulAut.conj r * φ := by
    rw [hr]; group
  rw [h1]
  exact J.mul_mem (hJ r) hφ

theorem congr_trans_eq {R R' : Type} [Group R] [Group R'] (σ : R ≃* R') (τ : R ≃* R')
    (φ : MulAut R) :
    MulAut.congr σ φ =
      MulAut.congr τ (MulAut.congr (σ.trans τ.symm) φ) := by
  ext y
  simp [MulAut.congr_apply]

theorem congr_self_eq {R : Type} [Group R] (α : R ≃* R) (φ : MulAut R) :
    MulAut.congr α φ = α * φ * α⁻¹ := by
  ext y
  simp [MulAut.congr_apply]

theorem g2der_transport {K L : Type} [Field K] [Finite K]
    [Field L] [Finite L] (hK : Nat.card K = 2) (hL : Nat.card L = 2)
    (hR : ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x)
    (σ : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true) ≃*
      LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 L true))
    {φ : MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))}
    (hφ : φ ∈ LargeEvenChevParentIDImage LargeEvenCartanG2 K
      (LargeEvenChevGroup LargeEvenCartanG2 K) (LargeEvenChevH LargeEvenCartanG2 K true)) :
    MulAut.congr σ φ ∈ LargeEvenChevParentIDImage LargeEvenCartanG2 L
      (LargeEvenChevGroup LargeEvenCartanG2 L) (LargeEvenChevH LargeEvenCartanG2 L true) := by
  let f : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  have hP := chevGroup_map_eq LargeEvenCartanG2 f
  have hH := chevH_true_map_eq LargeEvenCartanG2 f
  have hO := InndiagCommRest.ggOutComm_g2der hK hR
  set τ := centerQuotCongr (chevCongr LargeEvenCartanG2 f) hH with hτ
  have hJ : ∀ r : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true),
      MulAut.conj r ∈ Subgroup.closure (LargeEvenChevIDImage LargeEvenCartanG2 K
        (LargeEvenChevH LargeEvenCartanG2 K true) ∪ LargeEvenParentConjImage
        (LargeEvenChevGroup LargeEvenCartanG2 K) (LargeEvenChevH LargeEvenCartanG2 K true)) :=
    fun r => Subgroup.subset_closure (Or.inl (conj_mem_chevIDImage _ r))
  have hn := normal_of_outComm hO hJ (σ.trans τ.symm) hφ
  rw [congr_trans_eq σ τ, congr_self_eq]
  exact chevParentID_congr LargeEvenCartanG2 hK (chevCongr LargeEvenCartanG2 f) hP hH hn

section TwF4


theorem twF4der_transport {K L : Type} [Field K] [Finite K] [Field L] [Finite L]
    (hK : Nat.card K = 2) (hL : Nat.card L = 2)
    (σ : LargeEvenCenterQuot (LargeEvenTwF4H 0 K) ≃* LargeEvenCenterQuot (LargeEvenTwF4H 0 L))
    {φ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H 0 K))}
    (hφ : φ ∈ LargeEvenChevParentIDImage LargeEvenCartanF4 K (LargeEvenTwF4Parent 0 K)
      (LargeEvenTwF4H 0 K)) :
    MulAut.congr σ φ ∈ LargeEvenChevParentIDImage LargeEvenCartanF4 L (LargeEvenTwF4Parent 0 L)
      (LargeEvenTwF4H 0 L) := by
  let f : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  have hP := twF4Parent_map_eq 0 f
  have hH := twF4H_map_eq 0 f
  have hO := InndiagCommRest.ggOutComm_twF4der (K := K) rfl (by simpa using hK)
  set τ := centerQuotCongr (chevCongr LargeEvenCartanF4 f) hH with hτ
  have hJ : ∀ r : LargeEvenCenterQuot (LargeEvenTwF4H 0 K),
      MulAut.conj r ∈ Subgroup.closure (LargeEvenChevIDImage LargeEvenCartanF4 K
        (LargeEvenTwF4H 0 K) ∪ LargeEvenParentConjImage (LargeEvenTwF4Parent 0 K)
        (LargeEvenTwF4H 0 K)) :=
    fun r => Subgroup.subset_closure (Or.inl (conj_mem_chevIDImage _ r))
  have hn := normal_of_outComm hO hJ (σ.trans τ.symm) hφ
  rw [congr_trans_eq σ τ, congr_self_eq]
  exact chevParentID_congr LargeEvenCartanF4 hK (chevCongr LargeEvenCartanF4 f) hP hH hn

theorem twF4der_transport_if {a : ℕ} (ha : a = 0) {K L : Type} [Field K] [Finite K] [Field L]
    [Finite L] (hK : Nat.card K = 2 ^ (2 * a + 1)) (hL : Nat.card L = 2 ^ (2 * a + 1))
    (σ : LargeEvenCenterQuot (LargeEvenTwF4H a K) ≃* LargeEvenCenterQuot (LargeEvenTwF4H a L))
    {φ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))}
    (hφ : φ ∈ (if a = 0 then LargeEvenChevParentIDImage LargeEvenCartanF4 K
        (LargeEvenTwF4Parent a K) (LargeEvenTwF4H a K)
      else LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))) :
    MulAut.congr σ φ ∈ (if a = 0 then LargeEvenChevParentIDImage LargeEvenCartanF4 L
        (LargeEvenTwF4Parent a L) (LargeEvenTwF4H a L)
      else LargeEvenChevIDImage LargeEvenCartanF4 L (LargeEvenTwF4H a L)) := by
  subst ha
  rw [if_pos rfl] at hφ ⊢
  exact twF4der_transport (by simpa using hK) (by simpa using hL) σ hφ

end TwF4

end MI

end CFSG.LocalAnalysis.GLTheoremA
