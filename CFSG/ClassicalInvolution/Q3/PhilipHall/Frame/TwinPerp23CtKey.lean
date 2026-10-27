module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23CtData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

theorem exists_sylow_le_normalizer_of_mem_WSet {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨η, ⟨S, -, hS⟩, hWη⟩ := hW
  rw [hWη]
  exact ⟨S, CFSG.ClassicalInvolution.Asc77.Thompson.le_normalizer_biSup_of_acts hS⟩

section Key


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem ct_lift_conj (hT : Thm4RTwinBelow 3 n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) {M : Subgroup Y} (hM : M ∈ Om R)
    (hMe : M ≤ Subgroup.centralizer ({e} : Set Y)) (hM2 : IsPGroup 2 ↥M) :
    ∃ x ∈ Subgroup.centralizer ({e} : Set Y), conjSub x (tightCore R) = M := by
  obtain ⟨h2K, -, -, -, -, hKe, -, -⟩ := ct_data hP hc hno hα
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e := mem_tqMembers3_of_le_centralizer hK hKe
  have hMtq : M ∈ tqMembers3 (Om R) e := mem_tqMembers3_of_le_centralizer hM hMe
  obtain ⟨xb, hxb⟩ := e_trans hT hc hno _ (secImg_mem_secFam hKtq) _ (secImg_mem_secFam hMtq)
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  obtain ⟨g', hg'⟩ := TwinPerpV3.exists_conj_sylow_of_secImg_conj hΩ hc2 hKtq hMtq (isSylow2In_self h2K)
    (isSylow2In_self hM2) hKe hMe x₀ hxb
  exact ⟨((g' : ↥(Subgroup.centralizer ({e} : Set Y))) : Y), (g' : ↥(Subgroup.centralizer ({e} : Set Y))).2,
    hg'⟩

theorem ct_hswap (hT : Thm4RTwinBelow 3 n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∃ σ ∈ Subgroup.centralizer ({t} : Set Y), σ ∈ Subgroup.centralizer ({e} : Set Y) ∧
      conjSub σ (tightCore R) = K' := by
  obtain ⟨-, h2K', -, -, -, -, hK'e, -⟩ := ct_data hP hc hno hα
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨x, hxe, hx⟩ := ct_lift_conj hT hP hc hno hα hc.std.hK'.1 hK'e h2K'
  refine ⟨x, ?_, hxe, hx⟩
  have h1 := hz.conj x
  rw [hx] at h1
  have h2 : t = x * t * x⁻¹ := hz'.eq h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [← h2]

theorem ct_hsyl (hT : Thm4RTwinBelow 3 n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∃ P₁ : Subgroup Y, IsSylow2In P₁ (hZero (tightCore R) t) ∧
      P₁ ≤ Subgroup.centralizer ({e} : Set Y) := by
  obtain ⟨h2K, h2K', q₁, q₂, hcomm, hKe, hK'e, h2⟩ := ct_data hP hc hno hα
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  set H₀ := hZero (tightCore R) t with hH₀
  have hAH : tightCore R ⊔ K' ≤ H₀ := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_)
    · exact mem_hZero_of (le_centralizer_of_unique hz hk) (conjSub_eq_self_of_mem hk)
    · exact mem_hZero_of (le_centralizer_of_unique hz' hk)
        (conjSub_eq_of_mem_of_commutes hk (fun x hx y hy => (hcomm y hy x hx).symm))
  obtain ⟨P₀, hP₀, hAP₀⟩ := IsSylow2In.exists_ge h2 hAH
  obtain ⟨S', hS', hP₀S'⟩ := IsSylow2In.exists_ge hP₀.2.1 (le_top : P₀ ≤ ⊤)
  obtain ⟨S₂, hS₂⟩ := exists_sylow_le_normalizer_of_mem_WSet hc.std.hW
  have hS₂e : (S₂ : Subgroup Y) ≤ Subgroup.centralizer ({e} : Set Y) :=
    hS₂.trans (normalizer_le_centralizer_e hc.data)
  obtain ⟨y, -, hy⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In
    (CFSG.ClassicalInvolution.Asc77.T8.isSylow2In_of_sylow_le S₂ (le_top : (S₂ : Subgroup Y) ≤ ⊤)) hS'
  have hPe' : ∀ x ∈ P₀, x * (y * e * y⁻¹) = (y * e * y⁻¹) * x := by
    intro x hx
    have hx' : x ∈ conjSub y (S₂ : Subgroup Y) := by rw [hy]; exact hP₀S' hx
    rw [mem_conjSub_iff] at hx'
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hS₂e hx')
    calc x * (y * e * y⁻¹) = y * ((y⁻¹ * x * y) * e) * y⁻¹ := by group
      _ = y * (e * (y⁻¹ * x * y)) * y⁻¹ := by rw [h1]
      _ = (y * e * y⁻¹) * x := by group
  have hJ₁e : conjSub y⁻¹ (tightCore R) ≤ Subgroup.centralizer ({e} : Set Y) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hPe' _ (hAP₀ (Subgroup.mem_sup_left hx))
    calc x * e = y⁻¹ * ((y * x * y⁻¹) * (y * e * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * e * y⁻¹) * (y * x * y⁻¹)) * y := by rw [h1]
      _ = e * x := by group
  have hJ₁ : conjSub y⁻¹ (tightCore R) ∈ Om R := hΩ.conjInvariant y⁻¹ _ hK
  obtain ⟨x, hxe, hx⟩ := ct_lift_conj hT hP hc hno hα hJ₁ hJ₁e (isPGroup_conjSub y⁻¹ h2K)
  have hn : conjSub (y * x) (tightCore R) = tightCore R := by
    rw [conjSub_mul, hx, conjSub_conjSub_inv]
  have hnt : y * x ∈ Subgroup.centralizer ({t} : Set Y) := by
    have h1 := hz.conj (y * x)
    rw [hn] at h1
    have h2 : t = (y * x) * t * (y * x)⁻¹ := hz.eq h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y * x) * t = ((y * x) * t * (y * x)⁻¹) * (y * x) := by group
      _ = t * (y * x) := by rw [← h2]
  have hnH : y * x ∈ H₀ := mem_hZero_of hnt hn
  have hxe' : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp hxe
  have he' : (y * x) * e * (y * x)⁻¹ = y * e * y⁻¹ := by
    calc (y * x) * e * (y * x)⁻¹ = y * (x * e) * x⁻¹ * y⁻¹ := by group
      _ = y * (e * x) * x⁻¹ * y⁻¹ := by rw [hxe']
      _ = y * e * y⁻¹ := by group
  refine ⟨conjSub (y * x)⁻¹ P₀, ?_, ?_⟩
  · have h1 := hP₀.conj (y * x)⁻¹
    rwa [conjSub_eq_self_of_mem (H₀.inv_mem hnH)] at h1
  · intro z hz'
    rw [mem_conjSub_iff, inv_inv] at hz'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hPe' _ hz'
    rw [← he'] at h1
    calc z * e = (y * x)⁻¹ * (((y * x) * z * (y * x)⁻¹) * ((y * x) * e * (y * x)⁻¹)) * (y * x) := by group
      _ = (y * x)⁻¹ * (((y * x) * e * (y * x)⁻¹) * ((y * x) * z * (y * x)⁻¹)) * (y * x) := by rw [h1]
      _ = e * z := by group

end Key

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec
