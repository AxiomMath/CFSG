module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs
public import CFSG.GH74.Generic.BProg.B3.S3L3Facts

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.Generic.BProg.B1.PilotS3
  CFSG.GH74.Generic.BProg.B1.PilotS5 Subgroup
open scoped MatrixGroups commutatorElement

namespace S3Ctx29K26

variable {G : Type} [Group G] [Finite G]

theorem model_centerless_of_ctx {x : G} {K : Subgroup G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    center ↥(S3.imgBar x K) = ⊥ ∧
      ∃ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) ∧ p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
        LieModel ↥(S3.imgBar x K) t 3 p f := by
  obtain ⟨eK⟩ := hat_equiv_imgBar hK
  have hcomp := isComponent_imgBar hK
  have hKnab : ∃ a b : ↥(S3.imgBar x K), a * b ≠ b * a :=
    S45.exists_noncomm_of_isQuasisimple hcomp.1
  have hsimple : IsSimpleGroup ↥(S3.imgBar x K) :=
    (MulEquiv.isSimpleGroup_congr eK).mp (isSimpleGroup_of_qShape3 h3)
  have hcen : center ↥(S3.imgBar x K) = ⊥ := center_eq_bot_of_isSimpleGroup hsimple hKnab
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := h3
  have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have := Nat.odd_iff.mp hpodd
    omega
  refine ⟨hcen, ?_⟩
  rcases hmod with hm | hm
  · exact ⟨.PSL, p, f, Or.inl rfl, hp, hp2, h5, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eK hm⟩
  · exact ⟨.PSU, p, f, Or.inr rfl, hp, hp2, h5, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eK hm⟩

theorem exists_layerHyp' {x : G} {K : Subgroup G} {y : G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) (hyK : y ∈ K) (hy : orderOf y = 2)
    (hcen : center ↥(S3.imgBar x K) = ⊥)
    (hmodel : ∃ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) ∧ p.Prime ∧ p ≠ 2 ∧
      5 ≤ p ^ f ∧ LieModel ↥(S3.imgBar x K) t 3 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup ↥(S3.imgBar x K)),
      S3L3Lift.LayerHyp x hK.1 hyK S F ∧
      (∀ σ : MulAut ↥(S3.imgBar x K), σ * σ = 1 → (∀ s ∈ S, σ s = s) →
        σ = 1 ∨ σ = MulAut.conj (S3L3Lift.yK x hK.1 hyK)) := by
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := hmodel
  have hq3 : QShape3 ↥(S3.imgBar x K) := by
    refine ⟨p, f, hp, hp2, by omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  have hZ : ∀ z : ↥(S3.imgBar x K), (∀ g : ↥(S3.imgBar x K), g * z = z * g) → z = 1 := by
    intro z hz
    have hmem : z ∈ center ↥(S3.imgBar x K) := Subgroup.mem_center_iff.2 fun g => hz g
    rw [hcen, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨F, hF, hFin, S, hodd, h5', e, huS, -, hcomm, hSc, hB4⟩ :=
    S3L3KGroup.exists_sl2_component hq3 hZ (S3L3Lift.orderOf_yK x hK.1 hyK hy)
  exact ⟨F, hF, hFin, S, ⟨hodd, by omega, e, huS, hSc, fun M hM =>
    S3L3Lift.eq_of_isPCompIn_centralizer hSc hcomm hM⟩, hB4⟩

end S3Ctx29K26

theorem k26_proved (G : Type) [Group G] [Finite G] : K26 G := by
  intro x K A E y hterm h3 hsrc hEK hAE hyE hy1
  have hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K := hterm.1.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hyK : y ∈ K := hEK hyE
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hsrc.2.1
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := Th2Sig6.isElementaryAbelian_of_le hAel hEA
  have hy2 : y * y = 1 := by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) y hyE
  have hy : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  obtain ⟨hcen, hmodel⟩ := S3Ctx29K26.model_centerless_of_ctx hK h3
  obtain ⟨F, hF, hFin, S, hS, hB4⟩ := S3Ctx29K26.exists_layerHyp' hK hyK hy hcen hmodel
  obtain ⟨L, hL, -⟩ := hS.exists_comp hy
  have hLy : pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) = L := hS.pLayerOf_eq hy hL
  have hyL : y ∈ L := hLy ▸ hS.mem_layer hy
  obtain ⟨ψ, hψs, hψk, hψc⟩ := hS.psi_data hy hL
  subst hLy
  have hycS : y ∈ cSec (Ly29 K y) := by
    have hyN : y ∈ normalizer ((Ly29 K y : Subgroup G) : Set G) := Subgroup.le_normalizer hyL
    refine ⟨hyN, TwoThin.mem_normalizer_pPrimeCoreOf hyN, fun l hl => ?_⟩
    have h1 : ⁅l, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hL.1 hl)).2)
    rw [h1]
    exact one_mem _
  refine ⟨hL, hyL, ?_, ?_⟩
  · obtain ⟨e⟩ := hS.equiv
    refine ⟨F, hF, hFin, ⟨hS.odd, ?_⟩, ⟨?_⟩⟩
    · have h4 := hS.big
      obtain ⟨k, hk⟩ := hS.odd
      omega
    · exact ((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans
          (e.trans (specialLinearGroupEquivStatedSL 2 F))
  · apply le_antisymm
    · intro e he
      obtain ⟨heE, hec⟩ := Subgroup.mem_inf.1 he
      have heK : e ∈ K := hEK heE
      have heC : e ∈ centralizer ({x} : Set G) := hKC heK
      have hEp : IsPGroup 2 ↥E := CFSG.IsElementaryAbelian.isPGroup 2 ↥E
      have hEC : E ≤ centralizer ({x} : Set G) := hEK.trans hKC
      have he2 : e * e = 1 := by
        rw [← sq]
        exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e heE
      have hinj : ∀ a ∈ E, ∀ b ∈ E, piC x a = piC x b → a = b := by
        intro a ha b hb hab
        have h1 : piC x (a⁻¹ * b) = 1 := by
          rw [piC_mul x (hEC (E.inv_mem ha)) (hEC hb), piC_inv x (hEC ha), hab, inv_mul_cancel]
        have := eq_one_of_piC_eq_one hEp hEC (E.mul_mem (E.inv_mem ha) hb) h1
        exact inv_mul_eq_one.mp this
      set tK : ↥(S3.imgBar x K) := S3L3Lift.yK x hKC heK with htK
      set yK' : ↥(S3.imgBar x K) := S3L3Lift.yK x hKC hyK with hyK'
      have htK2 : tK * tK = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, S3L3Lift.yK_coe, ← piC_mul x heC heC, he2, piC_one]
        rfl
      have hcent : ∀ s ∈ S,
          (s : CentralizerBar x) * piC x e = piC x e * (s : CentralizerBar x) := by
        intro s hs
        obtain ⟨⟨l, hl⟩, hls⟩ := hψs ⟨s, hs⟩
        have hs_eq : (s : CentralizerBar x) = piC x l := by
          rw [← hψc l hl, hls]
        have hlC : l ∈ centralizer ({x} : Set G) := hKC (Subgroup.mem_inf.1 (hL.1 hl)).1
        have hc1 : ⁅l, e⁆ ∈ pPrimeCoreOf 2 (Ly29 K y) := hec.2.2 l hl
        have h1 : piC x ⁅l, e⁆ = 1 := by
          obtain ⟨z, hz, hzv⟩ := hc1
          have hzk : z ∈ ψ.ker := hψk ▸ hz
          have h2 := hψc (z : G) z.2
          have h3 : ψ ⟨(z : G), z.2⟩ = 1 := hzk
          rw [h3] at h2
          rw [← hzv]
          exact h2.symm
        rw [S3L3Facts.piC_commutator x hlC heC, ← hs_eq, commutatorElement_eq_one_iff_mul_comm]
          at h1
        exact h1
      have hconj : ∀ a b : ↥(S3.imgBar x K), MulAut.conj a = MulAut.conj b → a = b := by
        intro a b hab
        have hmem : b⁻¹ * a ∈ center ↥(S3.imgBar x K) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := congrArg (fun τ : MulAut ↥(S3.imgBar x K) => τ g) hab
          simp only [MulAut.conj_apply] at this
          calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
            _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [this]
            _ = b⁻¹ * a * g := by group
        rw [hcen, Subgroup.mem_bot] at hmem
        exact (inv_mul_eq_one.1 hmem).symm
      have hσσ : MulAut.conj tK * MulAut.conj tK = 1 := by
        rw [← map_mul, htK2, map_one]
      have hσS : ∀ s ∈ S, (MulAut.conj tK : MulAut ↥(S3.imgBar x K)) s = s := by
        intro s hs
        apply Subtype.ext
        rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          S3L3Lift.yK_coe, mul_inv_eq_iff_eq_mul]
        exact (hcent s hs).symm
      rcases hB4 (MulAut.conj tK) hσσ hσS with h1 | h2
      · have h1' : tK = 1 := hconj tK 1 (h1.trans (map_one MulAut.conj).symm)
        have h2 : piC x e = piC x 1 := by
          rw [piC_one]
          exact congrArg Subtype.val h1'
        rw [hinj e heE 1 E.one_mem h2]
        exact one_mem _
      · have h1' : tK = yK' := hconj tK yK' h2
        have h2' : piC x e = piC x y := congrArg Subtype.val h1'
        rw [hinj e heE y hyE h2']
        exact Subgroup.mem_zpowers y
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨hyE, hycS⟩

end CFSG.GH74.Generic.BProg.B3
