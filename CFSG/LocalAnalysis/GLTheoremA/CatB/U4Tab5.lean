module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem card_of_catalogIs_u4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) :
    Nat.card S = 25920 := by
  obtain ⟨e⟩ := bridge_u4two h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Multipliers.U42.card_PSp43]

theorem card_le_card_range_of_ker_le {J A B : Type} [Group J] [Group A] [Group B] [Finite J]
    (Φ : J →* A) (Ψ : J →* B) (hΨ : Function.Surjective Ψ) (hker : Φ.ker ≤ Ψ.ker) :
    Nat.card B ≤ Nat.card Φ.range := by
  have h1 : Nat.card Φ.ker * Φ.ker.index = Nat.card J := Subgroup.card_mul_index Φ.ker
  have h2 : Nat.card Ψ.ker * Ψ.ker.index = Nat.card J := Subgroup.card_mul_index Ψ.ker
  have hidx1 : Φ.ker.index = Nat.card Φ.range := Subgroup.index_ker Φ
  have hidx2 : Ψ.ker.index = Nat.card B := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hΨ, Subgroup.card_top]
  have hle : Nat.card Φ.ker ≤ Nat.card Ψ.ker := Subgroup.card_le_of_le hker
  have hpos : 0 < Nat.card Ψ.ker := Nat.card_pos
  rw [hidx1] at h1
  rw [hidx2] at h2
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card Ψ.ker * Nat.card B = Nat.card J := h2
    _ = Nat.card Φ.ker * Nat.card Φ.range := h1.symm
    _ ≤ Nat.card Ψ.ker * Nat.card Φ.range := Nat.mul_le_mul_right _ hle

theorem mulAut_mul_conj_mul_inv {Q : Type} [Group Q] (φ : MulAut Q) (g : Q) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem conj_central_mul {Q : Type} [Group Q] {c : Q} (hc : c ∈ Subgroup.center Q) (g : Q) :
    MulAut.conj (c * g) = MulAut.conj g := by
  ext x
  have hcx := Subgroup.mem_center_iff.1 hc (g * x * g⁻¹)
  simp only [MulAut.conj_apply, mul_inv_rev]
  calc c * g * x * (g⁻¹ * c⁻¹) = c * (g * x * g⁻¹) * c⁻¹ := by group
    _ = (g * x * g⁻¹) * c * c⁻¹ := by rw [← hcx]
    _ = g * x * g⁻¹ := by group

theorem aut_mem_center {Q : Type} [Group Q] (v : MulAut Q) {z : Q} (hz : z ∈ Subgroup.center Q) :
    v z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro h
  obtain ⟨h', rfl⟩ := v.surjective h
  have := congrArg v (hz h')
  simpa [map_mul] using this

theorem innerAut_mulEquiv_quot (Q : Type) [Group Q] :
    Nonempty (Q ⧸ Subgroup.center Q ≃* innerAut Q) := by
  have hker : (MulAut.conj : Q →* MulAut Q).ker = Subgroup.center Q := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have hx : g * x * g⁻¹ = x := by
        have := congrArg (fun φ : MulAut Q => φ x) h
        simpa [MulAut.conj_apply] using this
      calc x * g = (g * x * g⁻¹) * g := by rw [hx]
        _ = g * x := by group
    · intro h
      ext x
      show g * x * g⁻¹ = x
      rw [← h x, mul_inv_cancel_right]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange MulAut.conj)⟩

theorem glaPrimeCoreOf_innerAut_eq_bot {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hS : Nat.card (Q ⧸ Subgroup.center Q) = 25920) :
    GLAPPrimeCoreOf 3 (innerAut Q) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨e⟩ := innerAut_mulEquiv_quot Q
  have hcardI : Nat.card (innerAut Q) = 25920 := by
    rw [← hS, Nat.card_congr e.toEquiv]
  haveI : IsSimpleGroup (innerAut Q) := e.symm.isSimpleGroup
  have hcore : GLAPPrimeCore 3 ↥(innerAut Q) = ⊥ := by
    refine CFSG.pPrimeCore_eq_bot_iff.2 ?_
    intro K hK hcop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top, hcardI] at hcop
      norm_num at hcop
  show (GLAPPrimeCore 3 ↥(innerAut Q)).map (innerAut Q).subtype = ⊥
  rw [hcore, Subgroup.map_bot]

theorem u4two_inner {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (hZ : catalogIs (Q ⧸ Subgroup.center Q) S9.isU4two) (v : MulAut Q) (hU : U4Hyp v) :
    GLAPPrimeCoreOf 3 (innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨J, hJsub, _hJq, hJcat⟩ := hU
  have hSn : Nat.card (Q ⧸ Subgroup.center Q) = 25920 := card_of_catalogIs_u4two hZ
  have hPn : Nat.card (PSimple 3 J) = 25920 := card_of_catalogIs_u4two hJcat
  let Φ : ↥J →* (Q ⧸ Subgroup.center Q) :=
    (QuotientGroup.mk' (Subgroup.center Q)).comp J.subtype
  let Ψ : ↥J →* PSimple 3 J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
  have hΨ : Function.Surjective Ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : Φ.ker ≤ Ψ.ker := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj ⊢
    have hjc : (j : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff (j : Q)).1 hj
    have hx : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) j : PQuot 3 J) ∈
        Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective r
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hjc (k : Q)
    exact (QuotientGroup.eq_one_iff _).2 hx
  have htop : Φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hge := card_le_card_range_of_ker_le Φ Ψ hΨ hker
    have hle : Nat.card Φ.range ≤ Nat.card (Q ⧸ Subgroup.center Q) :=
      Subgroup.card_le_card_group _
    rw [hPn] at hge
    rw [hSn] at hle ⊢
    omega
  have hJZ : ∀ q : Q, ∃ j : Q, j ∈ J ∧ ∃ z ∈ Subgroup.center Q, q = j * z := by
    intro q
    have hmem : (QuotientGroup.mk' (Subgroup.center Q) q : Q ⧸ Subgroup.center Q) ∈ Φ.range := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨j, hj⟩ := (MonoidHom.mem_range).1 hmem
    have hz : (j : Q)⁻¹ * q ∈ Subgroup.center Q := (QuotientGroup.eq).1 hj
    exact ⟨(j : Q), j.2, (j : Q)⁻¹ * q, hz, by group⟩
  have hvJ : ∀ j ∈ J, v j = j := fun j hj => hJsub.le hj
  have hfix : ∀ g : Q, v g * g⁻¹ ∈ Subgroup.center Q := by
    intro g
    obtain ⟨j, hj, z, hz, rfl⟩ := hJZ g
    have hc : v z * z⁻¹ ∈ Subgroup.center Q := mul_mem (aut_mem_center v hz) (inv_mem hz)
    have key : j * (v z * z⁻¹) * j⁻¹ = v z * z⁻¹ := by
      rw [Subgroup.mem_center_iff.1 hc j]
      group
    have e : v (j * z) * (j * z)⁻¹ = v z * z⁻¹ := by
      rw [map_mul, hvJ j hj]
      calc j * v z * (j * z)⁻¹ = j * (v z * z⁻¹) * j⁻¹ := by group
        _ = v z * z⁻¹ := key
    rw [e]
    exact hc
  have hcomm : innerAut Q ≤ Subgroup.centralizer ({v} : Set (MulAut Q)) := by
    rintro φ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have hconj : MulAut.conj (v g) = MulAut.conj g := by
      have := conj_central_mul (hfix g) g
      rw [show v g * g⁻¹ * g = v g from by group] at this
      exact this
    have hcj := mulAut_mul_conj_mul_inv v g
    rw [hconj] at hcj
    calc v * MulAut.conj g = (v * MulAut.conj g * v⁻¹) * v := by group
      _ = MulAut.conj g * v := by rw [hcj]
  rw [inf_eq_left.2 hcomm]
  exact glaPrimeCoreOf_innerAut_eq_bot hQ hSn

@[expose] def U4InnRest : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (v : MulAut Q), CFSG.Open.IsQuasisimple Q →
    GLAPPrimeCore 3 Q = ⊥ →
      catalogIs (Q ⧸ Subgroup.center Q) (fun i => S9.isTableU4 i ∧ ¬ S9.isU4two i) → v ^ 3 = 1 →
        U4Hyp v → GLAPPrimeCoreOf 3 (innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))) = ⊥

theorem u4InnS_of_rest (h : U4InnRest) : U4InnS := by
  intro Q _ _ v hQ hO hcat hv3 hU
  by_cases h2 : catalogIs (Q ⧸ Subgroup.center Q) S9.isU4two
  · exact u4two_inner hQ h2 v hU
  · refine h Q v hQ hO ?_ hv3 hU
    obtain ⟨i, hi, e⟩ := hcat
    exact ⟨i, ⟨hi, fun h' => h2 ⟨i, h', e⟩⟩, e⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
