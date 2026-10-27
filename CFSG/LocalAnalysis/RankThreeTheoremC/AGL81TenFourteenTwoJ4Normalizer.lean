module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Normalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenNarrow
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4StrongAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo.J4Gamma

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
open CFSG.Open
open scoped Matrix commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev e₁ : Fin 2 → ZMod 11 := ![1, 0]

theorem map_closure_actHom_eq_range :
    (Subgroup.closure {(⟨nrm₁, nrm₁_mem_normalizer⟩ : Subgroup.normalizer (Q11 : Set J)),
      ⟨nrm₂, nrm₂_mem_normalizer⟩}).map heisData.actHom = heisData.actHom.range := by
  set n₁ : Subgroup.normalizer (Q11 : Set J) := ⟨nrm₁, nrm₁_mem_normalizer⟩
  set n₂ : Subgroup.normalizer (Q11 : Set J) := ⟨nrm₂, nrm₂_mem_normalizer⟩
  set R := (Subgroup.closure {n₁, n₂}).map heisData.actHom with hR
  have hle : R ≤ heisData.actHom.range := Subgroup.map_le_range _ _
  have h1 : ((heisData.actHom n₁ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
      Matrix (Fin 2) (Fin 2) (ZMod 11)) = Sporadic.J4Schreier.matA := by
    rw [heisData.coe_actHom, actMat_nrm₁]; rfl
  have h2 : ((heisData.actHom n₂ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
      Matrix (Fin 2) (Fin 2) (ZMod 11)) = Sporadic.J4Schreier.matB := by
    rw [heisData.coe_actHom, actMat_nrm₂]; rfl
  have hn₁ : heisData.actHom n₁ ∈ R :=
    ⟨n₁, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
  have hn₂ : heisData.actHom n₂ ∈ R :=
    ⟨n₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
  have htrans : ∀ w : Fin 2 → ZMod 11, w ≠ 0 → ∃ g ∈ R, g • e₁ = w := by
    intro w hw
    have he : e₁ ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp only [e₁] at this
      exact absurd this (by decide)
    obtain ⟨g, hg, hgw⟩ := matAB_transitive _ w he hw
    have key : ∀ m ∈ Submonoid.closure ({Sporadic.J4Schreier.matA, Sporadic.J4Schreier.matB} :
        Set (Matrix (Fin 2) (Fin 2) (ZMod 11))),
        ∃ γ ∈ R, ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
          Matrix (Fin 2) (Fin 2) (ZMod 11)) = m := by
      intro m hm
      induction hm using Submonoid.closure_induction with
      | mem x hx =>
        rcases hx with rfl | rfl
        · exact ⟨_, hn₁, h1⟩
        · exact ⟨_, hn₂, h2⟩
      | one => exact ⟨1, one_mem _, rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨γ₁, hγ₁, e₁'⟩ := hx
        obtain ⟨γ₂, hγ₂, e₂'⟩ := hy
        exact ⟨γ₁ * γ₂, mul_mem hγ₁ hγ₂, by rw [Units.val_mul, e₁', e₂']⟩
    obtain ⟨γ, hγ, hγg⟩ := key g hg
    exact ⟨γ, hγ, by rw [← hgw, ← hγg]; rfl⟩
  have horb : MulAction.orbit R e₁ = {v | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩ h0
      have h0' : ((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
          Matrix (Fin 2) (Fin 2) (ZMod 11)) *ᵥ e₁ = 0 := h0
      have h3 := congrArg (fun u => (((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11))⁻¹ :
          Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11)) *ᵥ u) h0'
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h3
      have := congrFun h3 0
      simp only [e₁] at this
      exact absurd this (by decide)
    · intro hv
      obtain ⟨g, hg, hgv⟩ := htrans v hv
      exact ⟨⟨g, hg⟩, hgv⟩
  have hcard : (MulAction.orbit R e₁).ncard = 120 := by
    rw [horb, ← Nat.card_coe_set_eq]
    exact card_nonzero_eleven
  have hRS := Subgroup.card_mul_index (MulAction.stabilizer R e₁)
  rw [MulAction.index_stabilizer, hcard] at hRS
  set s : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11) :=
    heisData.actHom n₂ * heisData.actHom n₂ * heisData.actHom n₁ * heisData.actHom n₂ *
      heisData.actHom n₁ * heisData.actHom n₂ * heisData.actHom n₂ with hs
  have hsR : s ∈ R := by
    simp only [hs]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hn₂ hn₂) hn₁) hn₂) hn₁) hn₂) hn₂
  have hsval : ((s : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
      Matrix (Fin 2) (Fin 2) (ZMod 11)) = !![1, 5; 0, 10] := by
    simp only [hs, Units.val_mul, h1, h2]
    decide
  have hsfix : (⟨s, hsR⟩ : R) ∈ MulAction.stabilizer R e₁ := by
    rw [MulAction.mem_stabilizer_iff]
    show ((s : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11)) *ᵥ
      e₁ = e₁
    rw [hsval]
    decide
  have hs1 : (⟨s, hsR⟩ : R) ≠ 1 := by
    intro h
    have := congrArg (fun r : R => ((r : Matrix.GeneralLinearGroup (Fin 2) (ZMod 11)) :
      Matrix (Fin 2) (Fin 2) (ZMod 11))) h
    simp only [OneMemClass.coe_one, Units.val_one] at this
    rw [hsval] at this
    exact absurd this (by decide)
  have hstab : 2 ≤ Nat.card (MulAction.stabilizer R e₁) := by
    have : Nontrivial (MulAction.stabilizer R e₁) :=
      ⟨⟨⟨_, hsfix⟩, 1, fun h => hs1 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hdvd : Nat.card R ∣ 240 := card_range_actHom_Q11 ▸ Subgroup.card_dvd_of_le hle
  have hR240 : Nat.card R = 240 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hR240, card_range_actHom_Q11])

theorem normalizer_Q11_le :
    Subgroup.normalizer (Q11 : Set J) ≤ Q11 ⊔ Subgroup.closure {nrm₁, nrm₂} := by
  intro n hn
  set N := Subgroup.normalizer (Q11 : Set J)
  have hmem : heisData.actHom ⟨n, hn⟩ ∈
      (Subgroup.closure {(⟨nrm₁, nrm₁_mem_normalizer⟩ : N), ⟨nrm₂, nrm₂_mem_normalizer⟩}).map
        heisData.actHom := by
    rw [map_closure_actHom_eq_range]
    exact ⟨_, rfl⟩
  obtain ⟨m, hm, hmn⟩ := hmem
  have h1 : heisData.actMat (m⁻¹ * ⟨n, hn⟩) = 1 := by
    rw [heisData.actMat_mul, ← heisData.coe_actHom, ← heisData.coe_actHom, map_inv, hmn,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hq := actMat_eq_one_mem _ h1
  have hmJ : (m : J) ∈ Subgroup.closure ({nrm₁, nrm₂} : Set J) := by
    have := Subgroup.mem_map_of_mem N.subtype hm
    rw [MonoidHom.map_closure] at this
    simpa [Set.image_insert_eq, Set.image_singleton] using this
  have e : n = (m : J) * ((m⁻¹ * ⟨n, hn⟩ : N) : J) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmJ) (Subgroup.mem_sup_left hq)

@[expose] noncomputable def vElt : J := qx * qy ^ 2

theorem vElt_mem : vElt ∈ Q11 := Q11.mul_mem qx_mem (Q11.pow_mem qy_mem 2)

@[expose] noncomputable def eSub : Subgroup J := Subgroup.centralizer ({vElt} : Set J) ⊓ Q11

theorem π_vElt :
    Multiplicative.toAdd (heisData.π ⟨vElt, vElt_mem⟩) = ![1, 2] := by
  have e : (⟨vElt, vElt_mem⟩ : Q11) = heisData.x * heisData.y ^ 2 := by
    rw [heisData_x, heisData_y]
    rfl
  rw [e, map_mul, map_pow, heisData.π_x, heisData.π_y]
  ext k
  fin_cases k <;> simp

theorem vElt_not_mem_zpowers :
    vElt ∉ Subgroup.zpowers qz := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  have e : (⟨vElt, vElt_mem⟩ : Q11) = ⟨qz, qz_mem⟩ ^ k := Subtype.ext (by simp [hk])
  have h1 := π_vElt
  rw [e, map_zpow, π_qz, one_zpow] at h1
  have := congrFun h1 0
  simp at this
  exact absurd this (by decide)

theorem card_eSub :
    Nat.card eSub = 11 ^ 2 := by
  have h := @card_centralizer_of_noncentral J (Subgroup.toGroup J) _ Q11 qz vElt orderOf_qz
    Q11_commutator_mem_zpowers (fun q hq => qz_commute_of_mem hq) Q11_mem_zpowers_of_central
    vElt_mem vElt_not_mem_zpowers
  rw [eSub, h, card_Q11]
  norm_num

private theorem eSub_comm
    {a b : J} (ha : a ∈ eSub) (hb : b ∈ eSub) : a * b = b * a := by
  have hc := @IsPGroup.isMulCommutative_of_card_eq_prime_sq 11 eSub _ ⟨by norm_num⟩ card_eSub
  have h2 := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h2

theorem isElemAbelian_eSub :
    IsElemAbelian 11 eSub :=
  ⟨⟨⟨fun a b => Subtype.ext (eSub_comm a.2 b.2)⟩⟩, fun _ hx => pow_eleven_of_mem hx.2⟩

private theorem nrm₁_commute_qz :
    nrm₁ * qz = qz * nrm₁ := by
  have h := nrm₁_qz
  calc nrm₁ * qz = nrm₁ * qz * nrm₁⁻¹ * nrm₁ := by group
    _ = qz * nrm₁ := by rw [h]

private theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G}
    (hH : Nat.card H ≠ 0) {g : G} (h : ∀ a ∈ H, g * a * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  haveI : Finite H := Nat.finite_of_card_ne_zero hH
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨h a, fun ha => ?_⟩
  rw [← heq] at ha
  obtain ⟨b, hb, hba⟩ := ha
  have hba' : g * b * g⁻¹ = g * a * g⁻¹ := hba
  have hab : b = a := by rwa [mul_left_inj, mul_right_inj] at hba'
  exact hab ▸ hb

private theorem commute_of_mul_commute {G : Type*} [Group G] {b c w : G}
    (h1 : b * (c * w) = c * w * b) (hcc : b * c = c * b) : b * w = w * b := by
  have h2 : c * (b * w) = c * (w * b) := by
    calc c * (b * w) = b * c * w := by rw [hcc, mul_assoc]
      _ = b * (c * w) := mul_assoc _ _ _
      _ = c * w * b := h1
      _ = c * (w * b) := mul_assoc _ _ _
  exact mul_left_cancel h2

private theorem commute_of_pow_three {G : Type*} [Group G] {b v : G}
    (h : b * v ^ 3 = v ^ 3 * b) (hv : v ^ 11 = 1) : b * v = v * b := by
  have h4 := (show Commute b (v ^ 3) from h).pow_right 4
  rw [← pow_mul, show 3 * 4 = 11 + 1 by norm_num, pow_add, hv, one_mul, pow_one] at h4
  exact h4.eq

private theorem mul_zpow_comm {G : Type*} [Group G] {q z : G} (h : q * z = z * q) (k : ℤ) :
    q * z ^ k = z ^ k * q :=
  ((show Commute q z from h).zpow_right k).eq

private theorem conj_mem_eSub
    {g c : J} (hgQ : ∀ a ∈ Q11, g * a * g⁻¹ ∈ Q11) (hcz : ∀ q ∈ Q11, q * c = c * q)
    (hgv : g * vElt * g⁻¹ = c * vElt ^ 3) {a : J} (ha : a ∈ eSub) : g * a * g⁻¹ ∈ eSub := by
  have haC : a ∈ Subgroup.centralizer ({vElt} : Set J) := ha.1
  have haQ' : g * a * g⁻¹ ∈ Q11 := hgQ a ha.2
  refine Subgroup.mem_inf.2 ⟨?_, haQ'⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at haC ⊢
  have h1 : g * a * g⁻¹ * (c * vElt ^ 3) = c * vElt ^ 3 * (g * a * g⁻¹) := by
    rw [← hgv]
    calc g * a * g⁻¹ * (g * vElt * g⁻¹) = g * (a * vElt) * g⁻¹ := by group
      _ = g * (vElt * a) * g⁻¹ := by rw [haC]
      _ = g * vElt * g⁻¹ * (g * a * g⁻¹) := by group
  have h3 := @commute_of_mul_commute J (Subgroup.toGroup J) _ _ _ h1 (hcz _ haQ')
  exact @commute_of_pow_three J (Subgroup.toGroup J) _ _ h3 (pow_eleven_of_mem vElt_mem)

theorem gElt_mem_normalizer :
    nrm₁ ^ 2 * nrm₂ ∈ Subgroup.normalizer (eSub : Set J) := by
  set N := Subgroup.normalizer (Q11 : Set J)
  set g : N := ⟨nrm₁, nrm₁_mem_normalizer⟩ ^ 2 * ⟨nrm₂, nrm₂_mem_normalizer⟩ with hg
  have hgJ : (g : J) = nrm₁ ^ 2 * nrm₂ := rfl
  have hM : heisData.actMat g = !![6, 4; 7, 5] := by
    rw [hg, heisData.actMat_mul, pow_two, heisData.actMat_mul, actMat_nrm₁, actMat_nrm₂]
    decide
  have hπ : heisData.π (Q11.normalizerMonoidHom g ⟨vElt, vElt_mem⟩ *
      (⟨vElt, vElt_mem⟩ ^ 3)⁻¹) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, map_pow, toAdd_mul, toAdd_inv, toAdd_pow, heisData.π_conj, hM,
      π_vElt]
    decide
  have hc : Q11.normalizerMonoidHom g ⟨vElt, vElt_mem⟩ * (⟨vElt, vElt_mem⟩ ^ 3)⁻¹ ∈
      Subgroup.center Q11 := by
    rw [← heisData.ker_eq]; exact hπ
  set c := Q11.normalizerMonoidHom g ⟨vElt, vElt_mem⟩ * (⟨vElt, vElt_mem⟩ ^ 3)⁻¹ with hcdef
  have hgv : (g : J) * vElt * (g : J)⁻¹ = (c : J) * vElt ^ 3 := by
    have : Q11.normalizerMonoidHom g ⟨vElt, vElt_mem⟩ = c * ⟨vElt, vElt_mem⟩ ^ 3 := by
      rw [hcdef]; group
    have h2 := congrArg Subtype.val this
    simpa using h2
  rw [center_Q11_eq] at hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hcJ : (c : J) = qz ^ k := by rw [← hk, Subgroup.coe_zpow]
  have hcz : ∀ q ∈ Q11, q * (c : J) = (c : J) * q := fun q hq => by
    rw [hcJ]
    exact @mul_zpow_comm J (Subgroup.toGroup J) _ _ (qz_commute_of_mem hq) k
  rw [← hgJ]
  have hgQ : ∀ x ∈ Q11, (g : J) * x * (g : J)⁻¹ ∈ Q11 := fun x hx =>
    (@Subgroup.mem_normalizer_iff J (Subgroup.toGroup J) _ _ |>.1 g.2 x).1 hx
  exact @mem_normalizer_of_conj_mem J (Subgroup.toGroup J) eSub (by rw [card_eSub]; norm_num) _
    fun a ha => conj_mem_eSub hgQ hcz hgv ha

theorem normalizer_Q11_le_narrowGamma
    [Finite J] : Subgroup.normalizer (Q11 : Set J) ≤ RankOneCent.narrowGamma 11 Q11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hEQ : eSub ≤ Q11 := inf_le_right
  have hEz : eSub ≤ Q11 ⊓ Subgroup.centralizer ({qz} : Set J) := fun a ha =>
    ⟨ha.2, Subgroup.mem_centralizer_singleton_iff.2 (qz_commute_of_mem ha.2)⟩
  have hCz : Subgroup.centralizer ({qz} : Set J) ≤ RankOneCent.narrowGamma 11 Q11 :=
    RankOneCent.centralizer_le_narrowGamma qz_mem orderOf_qz
      (CFSG.SectionRank.le_pRank (by norm_num) hEz isElemAbelian_eSub card_eSub)
  have hNE : Subgroup.normalizer (eSub : Set J) ≤ RankOneCent.narrowGamma 11 Q11 :=
    RankOneCent.normalizer_le_narrowGamma hEQ isElemAbelian_eSub card_eSub
  have hQ : Q11 ≤ RankOneCent.narrowGamma 11 Q11 := fun q hq =>
    hCz (Subgroup.mem_centralizer_singleton_iff.2 (qz_commute_of_mem hq))
  have h1 : nrm₁ ∈ RankOneCent.narrowGamma 11 Q11 := by
    exact hCz (Subgroup.mem_centralizer_singleton_iff.2 nrm₁_commute_qz)
  have h2 : nrm₂ ∈ RankOneCent.narrowGamma 11 Q11 := by
    have hg := hNE gElt_mem_normalizer
    have e : nrm₂ = (nrm₁ ^ 2)⁻¹ * (nrm₁ ^ 2 * nrm₂) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ h1 2)) hg
  refine (normalizer_Q11_le).trans (sup_le hQ ?_)
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact h1
  · exact h2

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo.J4Gamma
