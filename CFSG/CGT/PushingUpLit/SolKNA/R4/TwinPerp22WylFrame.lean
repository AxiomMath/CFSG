module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement

namespace Perp22Wyl

section Prod

variable {Y : Type} [Group Y]

theorem prod_perm {W : Subgroup Y} (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (a : Fin 4 → Y)
    (ha : ∀ i, a i ∈ W) (π : Equiv.Perm (Fin 4)) :
    a (π 0) * a (π 1) * a (π 2) * a (π 3) = a 0 * a 1 * a 2 * a 3 := by
  let _ : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with mul_comm := fun x y => Subtype.ext (hc x x.2 y y.2) }
  let b : Fin 4 → ↥W := fun i => ⟨a i, ha i⟩
  have h1 : ∏ i, b (π i) = ∏ i, b i := Equiv.prod_comp π b
  simp only [Fin.prod_univ_four] at h1
  exact congrArg Subtype.val h1

end Prod

structure WylFrame {Y : Type} [Group Y] [Finite Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y)
    (z : Y) where
  ρ : Fin 4 → Rep Ω W
  σ : Rep Ω W
  S₀ : Sylow 2 Y
  t' : Y
  a : Fin 4 → Y
  hWS : W ≤ (S₀ : Subgroup Y)
  hρS : ∀ i, (ρ i).R ≤ (S₀ : Subgroup Y)
  hz : ∀ i, IsUniqueInvolution (ρ i).K z
  hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K
  hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K
  hcover : ∀ J ∈ Ω, IsUniqueInvolution J z → ∃ i, J = (ρ i).K
  hclos : ∀ (σ' : Rep Ω W) (i : Fin 4), (σ'.K = (ρ i).K ∨ σ'.K ∈ omegaNbr Ω (ρ i).K) →
    ∃ j, σ'.K = (ρ j).K
  ha : ∀ i, a i ∈ (ρ i).R ⊓ W ∧ orderOf (a i) = 4
  ht' : IsUniqueInvolution σ.K t'
  hrel : t' = a 0 * a 1 * a 2 * a 3
  hfar : ∀ i, σ.K ≠ (ρ i).K
  hnc : ¬ DbarConnected Ω W

namespace WylFrame

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W : Subgroup Y} {z : Y}

@[expose] def perm (F : WylFrame Ω W z) (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (π : Equiv.Perm (Fin 4)) :
    WylFrame Ω W z where
  ρ := fun i => F.ρ (π i)
  σ := F.σ
  S₀ := F.S₀
  t' := F.t'
  a := fun i => F.a (π i)
  hWS := F.hWS
  hρS := fun i => F.hρS (π i)
  hz := fun i => F.hz (π i)
  hne := fun i j hij => F.hne (π i) (π j) (fun h => hij (π.injective h))
  hadj := fun i j hij => F.hadj (π i) (π j) (fun h => hij (π.injective h))
  hcover := fun J hJ hz' => by
    obtain ⟨i, hi⟩ := F.hcover J hJ hz'
    exact ⟨π.symm i, by simpa using hi⟩
  hclos := fun σ' i h => by
    obtain ⟨j, hj⟩ := F.hclos σ' (π i) h
    exact ⟨π.symm j, by simpa using hj⟩
  ha := fun i => F.ha (π i)
  ht' := F.ht'
  hrel := by
    rw [F.hrel]
    exact (prod_perm hc F.a (fun i => (F.ha i).1.2) π).symm
  hfar := fun i => F.hfar (π i)
  hnc := F.hnc

end WylFrame


section Exists


variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {K K' K₃ : Subgroup Y}
  {z u₁ u₂ u₃ : Y}

theorem exists_wylFrame (hP : Q3CL.PartIHypG Ω) (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K) (hcard : (twinSet Ω K).ncard = 4)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ W ∈ WSet Ω, Nonempty (WylFrame Ω W z) := by
  classical
  have hΩ := hd.hyp
  have hK : K ∈ Ω := hd.mem
  have hK' : K' ∈ Ω := hd.hK'.1
  have hK₃ : K₃ ∈ Ω := hd.hK₃.1
  have hz : IsUniqueInvolution K z := hd.hz
  have hz' : IsUniqueInvolution K' z := hd.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hd.hzK₃
  have hnc0 : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W :=
    fun W hW ⟨ρ₀, hρ₀⟩ => TwinPerpV3.not_dbarConnected_of_wyl' hP hd hperp hW ρ₀ hρ₀ (hμ W hW)
  obtain ⟨K₄, hK₄, h41, h42, h43⟩ := TwinPerpV3.exists_fourth_twin' hP hd hperp hnc0
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, -, -, c12, c13, c23, c14, c24, c34⟩ :=
    TwinPerpV3.exists_sylow_quad' hd hK₄ h41 h42 h43
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP123 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hPP : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) :=
    hP123.to_sup_of_normal_right' h4.2.1 (sup_le (sup_le
      (T7A.le_normalizer_of_commutes c14.symm) (T7A.le_normalizer_of_commutes c24.symm))
      (T7A.le_normalizer_of_commutes c34.symm))
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup hΩ hPP
  have hD₁ : R₁ ∈ DSet Ω W := hWD R₁ (mem_RSet_of_isSylow2In hK h1)
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hD₂ : R₂ ∈ DSet Ω W := hWD R₂ (mem_RSet_of_isSylow2In hK' h2)
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hD₃ : R₃ ∈ DSet Ω W := hWD R₃ (mem_RSet_of_isSylow2In hK₃ h3)
    (le_sup_right.trans le_sup_left)
  have hD₄ : R₄ ∈ DSet Ω W := hWD R₄ (mem_RSet_of_isSylow2In hK₄Ω h4) le_sup_right
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK h1 hD₁
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK' h2 hD₂
  obtain ⟨ρ₂, hρ₂K, hρ₂R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK₃ h3 hD₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK₄Ω h4 hD₄
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hρR : ∀ i, (ρ i).R = ![R₁, R₂, R₃, R₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀R, hρ₁R, hρ₂R, hρ₃R]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hd.hK'
    · exact hd.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hd.hne.symm
  have hKK₃ : K ≠ K₃ := hd.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hd.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hneK : ∀ i j : Fin 4, i ≠ j → ![K, K', K₃, K₄] i ≠ ![K, K', K₃, K₄] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  have hneρ : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact hneK i j hij
  have hnbrρ : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact TwinPerpV3.adj_of_twins' hd hperp (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    TwinPerpV3.not_dbarConnected_of_wyl' hP hd hperp hW ρ₀ hρ₀K (hμ W hW)
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨σ, t', g, ht', hfar, hg, hrel, -⟩ := c.fuse_frame hP.cls hnc ρ hzρ hneρ hnbrρ
  have hPN : ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ ≤ Subgroup.normalizer (W : Set Y) :=
    sup_le (sup_le (sup_le hD₁.2 hD₂.2) hD₃.2) hD₄.2
  have hPW : IsPGroup 2 ↥((((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) ⊔ W) :=
    hPP.to_sup_of_normal_right' (isPGroup_of_mem_WSet hW) hPN
  obtain ⟨S₀, hS₀⟩ := hPW.exists_le_sylow
  have hR₁S : R₁ ≤ (S₀ : Subgroup Y) := le_sup_left.trans (le_sup_left.trans (le_sup_left.trans
    (le_sup_left.trans hS₀)))
  have hR₂S : R₂ ≤ (S₀ : Subgroup Y) := le_sup_right.trans (le_sup_left.trans (le_sup_left.trans
    (le_sup_left.trans hS₀)))
  have hR₃S : R₃ ≤ (S₀ : Subgroup Y) := le_sup_right.trans (le_sup_left.trans (le_sup_left.trans
    hS₀))
  have hR₄S : R₄ ≤ (S₀ : Subgroup Y) := le_sup_right.trans (le_sup_left.trans hS₀)
  have hWS : W ≤ (S₀ : Subgroup Y) := le_sup_right.trans hS₀
  have hsub : ({K, K', K₃, K₄} : Set (Subgroup Y)) ⊆ twinSet Ω K := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact hTw 0
    · exact hTw 1
    · exact hTw 2
    · exact hTw 3
  have hc4 : ({K, K', K₃, K₄} : Set (Subgroup Y)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hKK', hKK₃, hKK₄]) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simp [hK'K₃, hK'K₄]) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by simp [hK₃K₄]) (Set.toFinite _), Set.ncard_singleton]
  have hset : ({K, K', K₃, K₄} : Set (Subgroup Y)) = twinSet Ω K :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hc4, hcard]) (Set.toFinite _)
  have hcover : ∀ J ∈ Ω, IsUniqueInvolution J z → ∃ i, J = (ρ i).K := by
    intro J hJ hzJ
    have hJt : J ∈ twinSet Ω K := ⟨hJ, z, hz, hzJ⟩
    rw [← hset] at hJt
    rcases hJt with rfl | rfl | rfl | rfl
    · exact ⟨0, (hρK 0).symm⟩
    · exact ⟨1, (hρK 1).symm⟩
    · exact ⟨2, (hρK 2).symm⟩
    · exact ⟨3, (hρK 3).symm⟩
  have hclos : ∀ (σ' : Rep Ω W) (i : Fin 4),
      (σ'.K = (ρ i).K ∨ σ'.K ∈ omegaNbr Ω (ρ i).K) → ∃ j, σ'.K = (ρ j).K := by
    intro σ' i hσ'
    rcases hσ' with h' | h'
    · exact ⟨i, h'⟩
    · have hperpi : KPerp Ω (ρ i).K = twinSet Ω K := by
        rw [A7T22.kPerp_eq_of_twin hΩ hK (by rw [hρK i]; exact hTw i), hperp]
      have hmem : σ'.K ∈ twinSet Ω K := by
        rw [← hperpi]
        exact Set.mem_insert_of_mem _ h'
      obtain ⟨-, w, hw, hwσ⟩ := hmem
      have hwz : w = z := hw.eq hz
      subst hwz
      exact hcover σ'.K σ'.hK hwσ
  have hRW : ∀ i, (ρ i).R ⊓ W = (ρ i).K ⊓ W := fun i =>
    (Q3CL.Thompson.inf_W_of_mem_D hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
  refine ⟨W, hW, ⟨⟨ρ, σ, S₀, t', g, hWS, ?_, hzρ, hneρ, hnbrρ, hcover, hclos, ?_, ht', hrel, ?_, hnc⟩⟩⟩
  · intro i
    rw [hρR i]
    fin_cases i
    · exact hR₁S
    · exact hR₂S
    · exact hR₃S
    · exact hR₄S
  · intro i
    exact ⟨by rw [hRW i]; exact (hg i).1, (hg i).2⟩
  · intro i h'
    exact hfar i (by rw [c.img_eq_of_K_eq σ (ρ i) h'])

end Exists

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
