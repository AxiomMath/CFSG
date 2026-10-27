module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.NatMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumStar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SymBaum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SymThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.TypeExcl
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Family
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.JPart

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.Quasithin.G6 Equiv

theorem symCoreWith_of_coreAct {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {N : ℕ}
    (θ : ↥L ≃* Perm (Fin N)) (β : ↥(commV L) ≃* ↥(coreMod N))
    (hequiv : ∀ (x : ↥L) (p : ↥(commV L)) (hp : (x : MulAut W) p ∈ commV L),
      β ⟨(x : MulAut W) p, hp⟩ = coreAct N (θ x) (β p)) :
    GN.SymCoreWith L N θ (β.trans (coreModEquivEven N)) := by
  intro h u hu i
  show Multiplicative.toAdd ((β ⟨(h : MulAut W) u, hu⟩ : ↥(coreMod N)) : PermMod N) i =
    Multiplicative.toAdd ((β u : ↥(coreMod N)) : PermMod N) ((θ h)⁻¹ i)
  rw [hequiv h u hu]
  exact permAct_apply N (θ h) (β u) i

section Ambient

variable {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
  (hV : IsElemAbelian 2 (VZ T H)) (hmin : MinParabolic H T M) (hmp : MinPar H T M)
  (hF : CharTwo H) (hred : IsTwoReducedIn H (VZ T H))
  (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G))

include hmin hmp hF hred hJ


theorem autI_twoResidual_le_genD : autI hV (twoResidual H) ≤ genD (autI hV H) :=
  (autI_mono hV (E2.twoResidual_le_thompsonJ hmin hred hJ)).trans
    (autI_thompsonJ_eq_genD hV hmin hmp hF hred hJ).le

theorem famI_type :
    ∀ L ∈ famI M hV, (∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨
      ∃ m : ℕ, 2 ≤ m ∧ GN.IsSymCoreModule L (2 ^ m + 1) := by
  have h51 := hyp51_of_e23 hV hmin hmp hF hred hJ
  have hV2 : ∀ v : IntMod (VZ T H) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hF5 := fiveFive_of_e23 hV hmin hmp hF hred hJ
  have hKD := autI_twoResidual_le_genD hV hmin hmp hF hred hJ
  have hK3 : ∀ x ∈ autI hV H, orderOf x = 3 → x ∈ autI hV (twoResidual H) := fun x hx h3 =>
    E2.mem_autI_twoResidual_of_odd hx (by rw [h3]; decide)
  intro L hL
  have hE := (mem_famI M hV).1 hL
  rcases hF5.type L hE with hSL | hSym
  · obtain ⟨n, hn, hnat, -, -⟩ := hSL
    exact Or.inl ⟨n, isL2Natural_of_slNat (by omega) hnat
      (commV_inf_fixV_eq_of_slType2 h51 hV2 hF5 hE hnat hKD hK3)⟩
  · obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType hSym
    obtain ⟨k, hk⟩ := hF5.two_pow_of_sym h51 hV2 hE hc.three θ i₀ (hc.stab_M hF5 hE)
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hm3 : m = 3 := by
        have := hc.three
        interval_cases k <;> simp at hk <;> omega
      subst hm3
      refine Or.inl ⟨1, E2.isL2Natural_of_actsAsNaturalL2
        (actsAsNaturalL2_of_symData_three hV2 θ β hc.inv hc.surj hc.ker hc.equiv) ?_⟩
      exact commV_inf_fixV_eq_bot_of_symData_three θ β hc.inv hc.ker hc.equiv
        fun x hx h3 => hK3 x (hF5.le_P h51 hV2 hE hx) h3
    · subst hk
      exact Or.inr ⟨k, hk2, isSymCoreModule_of_data θ β hc.surj hc.ker hc.equiv⟩

theorem hnat_of_all
    (hall : ∀ L ∈ famI M hV, ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) :
    ∀ E ∈ compSet (autI hV H) (autI hV M), SLType2 (Hyp51.offSet (autI hV H)) E ∨
      (SymType (genD (autI hV H) ⊓ autI hV M) (Hyp51.offSet (autI hV H)) E ∧ Nat.card E = 6) := by
  have hF5 := fiveFive_of_e23 hV hmin hmp hF hred hJ
  intro E hE
  rcases hF5.type E hE with hSL | hSym
  · exact Or.inl hSL
  · obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType hSym
    by_cases hm : m = 3
    · subst hm
      refine Or.inr ⟨hSym, ?_⟩
      rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    · obtain ⟨n, hn⟩ := hall E ((mem_famI M hV).2 hE)
      exact absurd hn (not_isL2Natural_of_mulEquiv_perm (by have := hc.three; omega) θ)

theorem natCase_baum_sylow
    (hall : ∀ L ∈ famI M hV, ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual H))) n) :
    autI hV (baum T) = autI hV (thompsonJ T) ∧
      IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) := by
  have h51 := hyp51_of_e23 hV hmin hmp hF hred hJ
  have hV2 : ∀ v : IntMod (VZ T H) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hF5 := fiveFive_of_e23 hV hmin hmp hF hred hJ
  have hv := vHyp_of_e23 hV hmin hmp hF hred hJ
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  obtain ⟨hcen, hsyl⟩ := natCore h51 hV2 hF5 (hnat_of_all hV hmin hmp hF hred hJ hall)
    (autI_mono hV hJT) (autI_le_normalizer_autI_thompsonJ hV)
    (exists_offSet_le_autI_thompsonJ hV hmin hmp hF hred hJ)
    (autI_thompsonJ_le_iSup hV hmin hmp hF hred hJ)
  refine ⟨autI_baum_eq hV hv.le_T (hmin.isSylow.1.trans hred.2.1) hcen, ?_⟩
  rw [autI_thompsonJ_eq_genD hV hmin hmp hF hred hJ]
  exact hsyl

theorem hsym_of_all {m : ℕ} (hm : 2 ≤ m)
    (hall : ∀ L ∈ famI M hV, GN.IsSymCoreModule L (2 ^ m + 1)) :
    ∀ E ∈ compSet (autI hV H) (autI hV M),
      SymType (genD (autI hV H) ⊓ autI hV M) (Hyp51.offSet (autI hV H)) E ∧
        120 ≤ Nat.card E := by
  have hF5 := fiveFive_of_e23 hV hmin hmp hF hred hJ
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  intro E hE
  obtain ⟨θ, β, -⟩ := hall E ((mem_famI M hV).2 hE)
  rcases hF5.type E hE with hSL | hSym
  · exact absurd hSL (not_slType2_of_mulEquiv_perm (by omega) θ)
  · refine ⟨hSym, ?_⟩
    rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]
    calc 120 = Nat.factorial 5 := by decide
      _ ≤ Nat.factorial (2 ^ m + 1) := Nat.factorial_le (by omega)

theorem symCase {m : ℕ} (hm : 2 ≤ m)
    (hall : ∀ L ∈ famI M hV, GN.IsSymCoreModule L (2 ^ m + 1)) :
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    autI hV (thompsonJ T) = ⨆ L ∈ famI M hV, (L ⊓ autI hV (thompsonJ T)) ∧
    ∀ L ∈ famI M hV, ∃ (θ : ↥L ≃* Equiv.Perm (Fin (2 ^ m + 1)))
      (β : ↥(commV L) ≃* Multiplicative (evenWeight (2 ^ m + 1))),
      GN.SymCoreWith L (2 ^ m + 1) θ β ∧
      L ⊓ autI hV (thompsonJ T) =
        Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap} := by
  have h51 := hyp51_of_e23 hV hmin hmp hF hred hJ
  have hV2 : ∀ v : IntMod (VZ T H) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hv := vHyp_of_e23 hV hmin hmp hF hred hJ
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  obtain ⟨hXeq, hcomp, hcen⟩ := symBaum bhsSymType h51 hV2
    (hsym_of_all hV hmin hmp hF hred hJ hm hall)
    (autI_mono hV hJT) (autI_le_normalizer_autI_thompsonJ hV)
    (autI_thompsonJ_le_iSup hV hmin hmp hF hred hJ)
    (exists_offSet_le_autI_thompsonJ hV hmin hmp hF hred hJ)
  refine ⟨autI_baum_eq hV hv.le_T (hmin.isSylow.1.trans hred.2.1) hcen, ?_, ?_⟩
  · conv_lhs => rw [hXeq]
    exact le_antisymm
      (iSup₂_le fun E hE => le_iSup₂_of_le (f := fun (L : Subgroup (MulAut (IntMod (VZ T H) hV)))
        (_ : L ∈ famI M hV) => L ⊓ autI hV (thompsonJ T)) E ((mem_famI M hV).2 hE) le_rfl)
      (iSup₂_le fun L hL => le_iSup₂_of_le (f := fun (E : Subgroup (MulAut (IntMod (VZ T H) hV)))
        (_ : E ∈ compSet (autI hV H) (autI hV M)) => E ⊓ autI hV (thompsonJ T)) L
        ((mem_famI M hV).1 hL) le_rfl)
  · intro L hL
    obtain ⟨θ₀, -, -⟩ := hall L hL
    obtain ⟨m', θ, β, hequiv, hcl⟩ := hcomp L ((mem_famI M hV).1 hL)
    have h1 : Nat.card ↥L = Nat.factorial m' := by
      rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_fin]
    have h2 : Nat.card ↥L = Nat.factorial (2 ^ m + 1) := by
      rw [Nat.card_congr θ₀.toEquiv, Nat.card_perm, Nat.card_fin]
    have hm' : m' = 2 ^ m + 1 := by
      have h5 : 1 < 2 ^ m + 1 := by have := Nat.one_le_two_pow (n := m); omega
      exact ((Nat.factorial_inj h5).1 (h2.symm.trans h1)).symm
    subst hm'
    exact ⟨θ, β.trans (coreModEquivEven _), symCoreWith_of_coreAct θ β hequiv, hcl⟩

end Ambient

end CFSG.AGLEmbeddingD2.Tits.E23
