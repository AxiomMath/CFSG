module

public import CFSG.Quasithin.H13.U3SixAction
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3Local1332

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem u3_six_action_profile_producer_F4
    (h1332 : Stmt13_3_2_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (z : G) [IsElementaryAbelian 2 V],
      QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
      (∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃ l ∈ L, l⁻¹ * x * l = y) ∧
        ∃ b : LinearMap.BilinForm (ZMod 2) (Additive V), b.Nondegenerate ∧ b.IsAlt ∧
          (∀ n : normalizer (V : Set G), ∀ x y : Additive V,
            b (u3ConjLin V _ le_rfl n x) (u3ConjLin V _ le_rfl n y) = b x y) ∧
          QTBinarySixProfile b (u3ConjLin V (normalizer (V : Set G)) le_rfl).range := by
  intro G _ _ T L V z hVe hH hU3 hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hVT, -, hV64, -, -, hLV, hTV, hirr, hnt, hTC, -, -⟩ := id hF
  obtain ⟨-, hVM, -, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332_F4 h1332 hH hF

  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* U33G := e1.trans e2.symm
  let φ := SteinbergBS.normalizerConjOn V L hLV
  have hOL : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    rw [← hTC]
    exact inf_le_right
  have hO : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [ker_normalizerConjOn hLV, mem_subgroupOf]
    refine ⟨x.2, hOL ?_⟩
    rw [← inSubgroup_pCore_eq_pCoreOf]
    exact ⟨x, hx, rfl⟩
  let ψ : U33G →* MulAut V :=
    (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO).comp e.symm.toMonoidHom
  let f : ↥L →* U33G := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψf : ∀ l : ↥L, ψ (f l) = φ l := fun l => by
    change QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO (e.symm (e (l : ↥L ⧸ CFSG.pCore 2 ↥L))) =
      φ l
    rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]

  have hCL : V ⊓ centralizer (L : Set G) = ⊥ := by
    rcases hirr (V ⊓ centralizer (L : Set G)) inf_le_left
        (fun l hl w hw => by
          rw [show l * w * l⁻¹ = w by
            rw [(mem_centralizer_iff.1 hw.2) l hl, mul_inv_cancel_right]]
          exact hw) with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, v, hv, hlv⟩ := hnt
      have hvC : v ∈ centralizer (L : Set G) := (h.symm ▸ hv : v ∈ V ⊓ _).2
      exact hlv (by rw [(mem_centralizer_iff.1 hvC) l hl, mul_inv_cancel_right])
  have hψfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1 := by
    intro v hv
    have hvC : (v : G) ∈ V ⊓ centralizer (L : Set G) := by
      refine ⟨v.2, mem_centralizer_iff.2 fun l hl => ?_⟩
      have h1 := congrArg Subtype.val (hv (f ⟨l, hl⟩))
      rw [hψf] at h1
      change l * v * l⁻¹ = v at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    rw [hCL] at hvC
    exact Subtype.ext ((mem_bot).1 hvC)
  have hV2 : ∀ v : V, v * v = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian _ v.2)

  obtain ⟨F, hFeq⟩ := exists_equiv_u33_module hV2 hV64 ψ hψfix
  refine ⟨?_, ?_⟩
  ·
    intro x hx hx1 y hy hy1
    have hx1' : (⟨x, hx⟩ : V) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hy1' : (⟨y, hy⟩ : V) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
    have hne : ∀ v : V, v ≠ 1 → F.symm v ≠ 1 := fun v hv h =>
      hv (by rw [← F.apply_symm_apply v, h, map_one])
    obtain ⟨g, hg⟩ := psiW_transitive _ (hne _ hx1')
    obtain ⟨h, hh⟩ := psiW_transitive _ (hne _ hy1')
    have hgx : ψ g (F w0) = ⟨x, hx⟩ := by rw [← hFeq, hg, MulEquiv.apply_symm_apply]
    have hhy : ψ h (F w0) = ⟨y, hy⟩ := by rw [← hFeq, hh, MulEquiv.apply_symm_apply]
    obtain ⟨l, hl⟩ := hf (h * g⁻¹)
    refine ⟨(l : G)⁻¹, L.inv_mem l.2, ?_⟩
    have h1 : ψ (h * g⁻¹) ⟨x, hx⟩ = ⟨y, hy⟩ := by
      rw [← hgx, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel_right, hhy]
    rw [← hl, hψf] at h1
    have h2 := congrArg Subtype.val h1
    change (l : G) * x * (l : G)⁻¹ = y at h2
    rw [inv_inv]
    exact h2
  ·
    set Φ := linOfMulEquiv F with hΦ
    set Γ := (u3ConjLin V (normalizer (V : Set G)) le_rfl).range with hΓ

    have hΦψ : ∀ (k : U33G) (x : Additive V),
        Φ (mulAutToLin V (ψ k) x) = glLin (rho6 k) (Φ x) := by
      intro k x
      rw [hΦ, linOfMulEquiv_apply, linOfMulEquiv_apply, mulAutToLin_apply, toMul_ofMul,
        glLin_apply]
      set w := F.symm (Additive.toMul x) with hw
      have h1 : F.symm (ψ k (Additive.toMul x)) = psiW k w := by
        rw [MulEquiv.symm_apply_eq, hFeq, hw, MulEquiv.apply_symm_apply]
      rw [h1]
      show Multiplicative.toAdd (psiW k (Multiplicative.ofAdd (Multiplicative.toAdd w))) = _
      rw [psiW_apply]
      rfl
    have hlinψ : ∀ k : U33G, linConj Φ (mulAutToLin V (ψ k)) = glLin (rho6 k) := by
      intro k
      ext w
      rw [linConj_apply, hΦψ, LinearEquiv.apply_symm_apply]
    have hψu : ∀ l : L, mulAutToLin V (ψ (f l)) = u3ConjLin V L hLV l := fun l => by
      rw [hψf]
      rfl

    have hnl : ∀ (n : normalizer (V : Set G)) (l : L), (n : G) * l * (n : G)⁻¹ ∈ L :=
      fun n l => (mem_normalizer_iff.1 (hVM n.2) l).1 l.2
    have hcomm : ∀ (n : normalizer (V : Set G)) (l : L),
        u3ConjLin V _ le_rfl n * u3ConjLin V L hLV l * (u3ConjLin V _ le_rfl n)⁻¹ =
          u3ConjLin V L hLV ⟨n * l * n⁻¹, hnl n l⟩ := by
      intro n l
      rw [← map_inv]
      refine LinearEquiv.ext fun x => ?_
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, coe_u3ConjLin_apply, coe_u3ConjLin_apply,
        coe_u3ConjLin_apply, coe_u3ConjLin_apply]
      simp only [Subgroup.coe_inv]
      group
    let gN : normalizer (V : Set G) → GL (Fin 6) (ZMod 2) := fun n =>
      glLin.symm (linConj Φ (u3ConjLin V _ le_rfl n))
    have hgN_inv : ∀ n, gN n⁻¹ = (gN n)⁻¹ := fun n => by
      simp only [gN, map_inv]
    have hgN_conj : ∀ (n : normalizer (V : Set G)) (l : L),
        gN n * rho6 (f l) * (gN n)⁻¹ = rho6 (f ⟨n * l * n⁻¹, hnl n l⟩) := by
      intro n l
      apply glLin.injective
      simp only [gN, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← hlinψ, ← hlinψ, hψu, hψu, ← map_inv (linConj Φ), ← map_mul, ← map_mul, hcomm]
    have hgN_mem : ∀ n, gN n ∈ N6 := by
      intro n
      rw [← normalizer_J6_eq, mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨k, rfl⟩
        obtain ⟨l, rfl⟩ := hf k
        exact ⟨_, (hgN_conj n l).symm⟩
      · rintro ⟨k, hk⟩
        obtain ⟨l, rfl⟩ := hf k
        obtain ⟨k', hk'⟩ : ∃ k', gN n⁻¹ * rho6 (f l) * (gN n⁻¹)⁻¹ = rho6 k' :=
          ⟨_, hgN_conj n⁻¹ l⟩
        refine ⟨k', ?_⟩
        rw [← hk', hgN_inv, inv_inv, hk]
        group
    have hle : Γ.map (linConj Φ).toMonoidHom ≤ N6L := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨gN n, hgN_mem n, ?_⟩
      simp only [gN, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have hprof := qtBinarySixProfile_of_map_linConj Φ b0 Γ (qtBinarySixProfile_of_le_N6L hle)
    exact ⟨_, hprof.2.1, hprof.2.2.1, fun n x y => hprof.2.2.2.1 _ ⟨n, rfl⟩ x y, hprof⟩

end CFSG.Quasithin.H13.U3
