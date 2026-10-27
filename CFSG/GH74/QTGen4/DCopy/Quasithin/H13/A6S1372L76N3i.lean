module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Oe2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenTilde
public import CFSG.Quasithin.H13.A6S1372L76N3g
public import CFSG.Quasithin.H13.A6S1372L76N3h
public import CFSG.Quasithin.H13.A6S1372L76O

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_c3Hom_F4 (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) (hL1K : S.L1 ≤ K)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1) :
    H ≤ Subgroup.normalizer (K : Set G) ∧
    ∃ Φ : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →* SL3.S,
      (∀ A : SL3.S, ∃ k : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (k : G) ∈ K ∧ Φ k = A) ∧
      (∀ k : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (k : G) ∈ K → Φ k = 1 →
        (k : G) ∈ pCoreOf 2 H) ∧
      (∀ q : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (q : G) ∈ pCoreOf 2 H → Φ q = 1) ∧
      (∀ h : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
        (h : G) * S.v2 * (h : G)⁻¹ * S.v2⁻¹ ∈ fsuV1 T V → SL3.InX1 (Φ h)) ∧
      (∀ k : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (k : G) ∈ K → (k : G) ^ 3 = 1 →
        SL3.InX1 (Φ k) → (k : G) * S.v2 * (k : G)⁻¹ * S.v2⁻¹ ∈ fsuV1 T V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  set Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) with hKt
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have : IsSimpleGroup (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Gam :=
    A6L76A.isSimpleGroup_statedSL (le_refl 3) hF2
  have := S.nontrivial_tilde_of_L1_le hH hKH hL1K
  have hrad := A6L76A.rad_eq_bot_of_surjective
    (Γ := (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Gam)
    (A6L76A.not_isSolvable_statedSL (le_refl 3)) π hπ.1
  have hHK := S.le_normalizer_of_L1_le hH h37 h38 hK hL1K hrad
  refine ⟨hHK, ?_⟩
  obtain ⟨π', hπ'⟩ := A6L76O.realizesVia_zmod hF2 hπ
  obtain ⟨hs, -, β, hβs, hβk, hβe0⟩ := A6L76Z.natRealizes_clean hπ'
  have hβe : ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (u : ↥(commV Kt))
      (hu : ((π' γ : ↥Kt) : MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          (u : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ∈ commV Kt),
      β ⟨_, hu⟩ = A6L76Of.natHom γ (β u) := fun γ u hu => hβe0 γ u hu
  have hmemK : ∀ f : ↥H, (f : G) ∈ K → A6Mod.secAct hHU hHV f ∈ Kt :=
    fun f hf => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨f, hf, rfl⟩

  let ι : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →* ↥H := Subgroup.inclusion inf_le_left
  have key : ∀ x : ↥H, (x : G) ∈ Subgroup.normalizer (K : Set G) →
      ∀ y ∈ Kt, A6Mod.secAct hHU hHV x * y * (A6Mod.secAct hHU hHV x)⁻¹ ∈ Kt := by
    intro x hx y hy
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hy
    refine (A6Mod.mem_autSec_iff hHU hHV hKH).2
      ⟨x * f * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx f).mp hfK, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hσN : ∀ h : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
      A6Mod.secAct hHU hHV (ι h) ∈ Subgroup.normalizer (Kt : Set (MulAut _)) := by
    intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key _ h.2.2 y, fun hy => ?_⟩
    have h2 := key (ι h)⁻¹ (Subgroup.inv_mem _ h.2.2) _ hy
    have e : (A6Mod.secAct hHU hHV (ι h))⁻¹ * (A6Mod.secAct hHU hHV (ι h) * y *
        (A6Mod.secAct hHU hHV (ι h))⁻¹) * (A6Mod.secAct hHU hHV (ι h))⁻¹⁻¹ = y := by group
    rwa [map_inv, e] at h2
  let σ := ((A6Mod.secAct hHU hHV).comp ι).codRestrict _ hσN
  let Φ₀ := (A6L76N3.liftHom hβs hβk).comp σ
  have hΦ₀ : ∀ h u, Φ₀ h (β u) = β ⟨A6Mod.secAct hHU hHV (ι h) u,
      A6L76Of.apply_mem_commV_of_conj (A6L76N3.conj_mem_of_normalizer (hσN h)) u.2⟩ :=
    fun h u => A6L76N3.liftHom_apply hβs hβk (σ h) u

  have hgL1 : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have hgX : (S.cL1 hhat : G) ∈ S.X1375 := by
    rw [S.X1375_of_not_hat hhat]
    exact hgL1
  obtain ⟨a, P, v₂, ha, -, hv₂, -, -, -, -, -, -, ha2, hv⟩ :=
    S.exists_odd_config_of_F4 hH hK rfl h139 h37 h38 h13315 hgX (S.cL1_rho hhat)
  have haY : a ∈ Kt := by
    rw [ha]
    exact hmemK _ (hL1K hgL1)
  have hv₂c : v₂ ∈ commV Kt := by
    have h := A6L76Oe.gen_mem_commV haY (a v₂)
    rwa [ha2, mul_inv_cancel_right] at h
  set x₀ := β ⟨v₂, hv₂c⟩ with hx₀
  have hx₀1 : Multiplicative.toAdd x₀ ≠ 0 := by
    intro h0
    apply hv
    have h1 : x₀ = 1 := toAdd_eq_zero.1 h0
    exact ((hβk _).1 h1).1
  obtain ⟨g₀, hg₀⟩ := A6L76N3.exists_mulVec_eq_e0 _ hx₀1
  have hg₀inv : ((g₀⁻¹ : SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ A6L76N3.e0 =
      Multiplicative.toAdd x₀ := by
    rw [← hg₀, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  let Φ : ↥(H ⊓ Subgroup.normalizer (K : Set G)) →* SL3.S :=
    (MulAut.conj g₀).toMonoidHom.comp (A6L76N3.toSL.toMonoidHom.comp Φ₀)
  have hΦ : ∀ h, Φ h = g₀ * A6L76N3.toSL (Φ₀ h) * g₀⁻¹ := fun h => rfl
  have hΦe0 : ∀ h, ((Φ h : SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ A6L76N3.e0 =
      (g₀ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (Φ₀ h x₀) := by
    intro h
    have h1 := A6L76N3.toSL_mulVec (Φ₀ h) (Multiplicative.toAdd x₀)
    rw [ofAdd_toAdd] at h1
    rw [hΦ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg₀inv]
    congr 1

  have hΦ₀K : ∀ (k : ↥(H ⊓ Subgroup.normalizer (K : Set G))) (γ : _),
      A6Mod.secAct hHU hHV (ι k) = (π' γ).1 → Φ₀ k = A6L76Of.natHom γ := by
    intro k γ hγ
    have hγN : (π' γ).1 ∈ Subgroup.normalizer (Kt : Set (MulAut _)) := by
      rw [← hγ]
      exact hσN k
    have h1 : σ k = ⟨_, hγN⟩ := Subtype.ext hγ
    show A6L76N3.liftHom hβs hβk (σ k) = _
    rw [h1]
    exact A6L76N3.liftHom_of_mem hβs hβk hβe γ hγN
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro A
    obtain ⟨f, hfK, hf⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1
      (π' (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)
        (g₀⁻¹ * A * g₀))).2
    refine ⟨⟨f, f.2, hHK f.2⟩, hfK, ?_⟩
    rw [hΦ, hΦ₀K ⟨f, f.2, hHK f.2⟩ _ hf]
    have h3 : A6L76N3.toSL (A6L76Of.natHom
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2) (g₀⁻¹ * A * g₀))) =
        g₀⁻¹ * A * g₀ := by
      show (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
        (A6L76N3.natHomEquiv.symm (A6L76Of.natHom _)) = _
      rw [← A6L76N3.natHomEquiv_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rw [h3]
    group
  ·
    intro k hkK hk1
    have h1 : A6L76N3.toSL (Φ₀ k) = 1 := by
      rw [hΦ] at hk1
      have e : A6L76N3.toSL (Φ₀ k) = g₀⁻¹ * (g₀ * A6L76N3.toSL (Φ₀ k) * g₀⁻¹) * g₀ := by group
      rw [e, hk1]
      group
    have h2 : Φ₀ k = 1 := (MulEquiv.map_eq_one_iff _).1 h1
    obtain ⟨γ, hγ⟩ := hs ⟨A6Mod.secAct hHU hHV (ι k), hmemK _ hkK⟩
    have h3 := hΦ₀K k γ (congrArg Subtype.val hγ).symm
    rw [h2] at h3
    have h4 : γ = 1 := A6L76N3.natHom_injective (h3.symm.trans (map_one _).symm)
    have h5 : A6Mod.secAct hHU hHV (ι k) = 1 := by
      have h6 : π' γ = 1 := by rw [h4]; exact map_one π'
      have h7 := congrArg Subtype.val hγ
      exact h7.symm.trans (congrArg Subtype.val h6)
    exact (S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH k.2.1).2
      ((A6Mod.secAct_eq_one_iff hHU hHV _).1 h5)
  ·
    intro q hq
    have h1 : A6Mod.secAct hHU hHV (ι q) = 1 := (A6Mod.secAct_eq_one_iff hHU hHV _).2
      ((S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH q.2.1).1 hq)
    have h2 : σ q = 1 := Subtype.ext h1
    have h3 : Φ₀ q = 1 := by
      show A6L76N3.liftHom hβs hβk (σ q) = 1
      rw [h2, map_one]
    have h4 : A6L76N3.toSL (Φ₀ q) = 1 := (MulEquiv.map_eq_one_iff _).2 h3
    rw [hΦ, h4, mul_one, mul_inv_cancel]
  ·
    intro h hh
    have h1 : A6Mod.secAct hHU hHV (ι h) v₂ = v₂ := by
      rw [hv₂, A6Mod.secAct_secMk]
      apply secMk_eq_of_mem_V1
      rw [Setup.rho_apply_coe]
      exact hh
    have h2 : Φ₀ h x₀ = x₀ := by
      rw [hx₀, hΦ₀]
      congr 1
      exact Subtype.ext h1
    rw [A6L76N3.inX1_iff_mulVec, hΦe0, h2, hg₀]
  ·
    intro k hkK hk3 hkX
    have h1 : Φ₀ k x₀ = x₀ := by
      have h2 := (A6L76N3.inX1_iff_mulVec _).1 hkX
      rw [hΦe0, ← hg₀] at h2
      have h3 : Multiplicative.toAdd (Φ₀ k x₀) = Multiplicative.toAdd x₀ := by
        have e := congrArg (fun w => ((g₀⁻¹ : SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) h2
        simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at e
        exact e
      exact Multiplicative.toAdd.injective h3
    rw [hx₀, hΦ₀] at h1
    have h4 : A6Mod.secAct hHU hHV (ι k) v₂ * v₂⁻¹ ∈ fixV Kt := by
      have h5 : β (⟨_, A6L76Of.apply_mem_commV_of_conj (A6L76N3.conj_mem_of_normalizer (hσN k))
          hv₂c⟩ * (⟨v₂, hv₂c⟩ : ↥(commV Kt))⁻¹) = 1 := by
        rw [map_mul, map_inv, h1]
        exact mul_inv_cancel _
      exact ((hβk _).1 h5).1
    obtain ⟨c, hc⟩ : ∃ c, c = A6Mod.secAct hHU hHV (ι k) v₂ * v₂⁻¹ := ⟨_, rfl⟩
    have hbY : A6Mod.secAct hHU hHV (ι k) ∈ Kt := hmemK _ hkK
    have hbc : A6Mod.secAct hHU hHV (ι k) c = c := by
      rw [hc]
      exact h4 _ hbY
    have hbv : A6Mod.secAct hHU hHV (ι k) v₂ = c * v₂ := by rw [hc, inv_mul_cancel_right]
    have hk3' : (ι k) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk3)
    have hb3 : A6Mod.secAct hHU hHV (ι k) ^ 3 = 1 := by rw [← map_pow, hk3', map_one]
    have e3 : (A6Mod.secAct hHU hHV (ι k) ^ 3) v₂ = A6Mod.secAct hHU hHV (ι k)
        (A6Mod.secAct hHU hHV (ι k) (A6Mod.secAct hHU hHV (ι k) v₂)) := by
      rw [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply]
    rw [hb3, MulAut.one_apply] at e3
    have hc3 : c * (c * (c * v₂)) = v₂ := by
      calc c * (c * (c * v₂)) = A6Mod.secAct hHU hHV (ι k)
            (A6Mod.secAct hHU hHV (ι k) (A6Mod.secAct hHU hHV (ι k) v₂)) := by
            rw [hbv, map_mul, hbc, hbv, map_mul, map_mul, hbc, hbv]
        _ = v₂ := e3.symm
    have hW2 : ∀ w : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)), w * w = 1 := by
      intro w
      obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ w
      rw [← map_mul]
      have hu : u * u = 1 := Subtype.ext (by simpa [sq] using hab.2 u u.2)
      rw [hu, map_one]
    have hc1 : c = 1 := by
      have e1 : c * (c * c) * v₂ = 1 * v₂ := by
        rw [one_mul]
        calc c * (c * c) * v₂ = c * (c * (c * v₂)) := by simp only [mul_assoc]
          _ = v₂ := hc3
      have e2 := mul_right_cancel e1
      rw [hW2, mul_one] at e2
      exact e2
    rw [hc1, one_mul, hv₂, A6Mod.secAct_secMk] at hbv
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff, Subgroup.coe_mul,
      Subgroup.coe_inv, Setup.rho_apply_coe] at hbv
    exact hbv

end Setting4

end CFSG.Quasithin.H13.A6
