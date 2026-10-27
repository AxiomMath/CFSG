module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGen
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Mem
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jB
import CFSG.ClassicalInvolution.Q3.Sec13L94Tight
import CFSG.ClassicalInvolution.Q3.Q3CLSeven1
import CFSG.ClassicalInvolution.Q3.Q3CLSeven2
import CFSG.ClassicalInvolution.Q3.Q3CLBasic
import CFSG.ClassicalInvolution.Asc77.AscT7DMu
import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7G

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_conj_of_swap (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4))
    (hφ : ∀ x, x ∈ Asc77.Thompson.muDelta Ω W ↔ (φ x).IsSwap) (ρ₀ ρ₀' ρ₁ : Asc77.Thompson.Rep Ω W)
    (hab : ρ₀.img ≠ ρ₀'.img) (hcomm : ρ₀.img * ρ₀'.img = ρ₀'.img * ρ₀.img)
    (hca : ρ₁.img ≠ ρ₀.img) (hcb : ρ₁.img ≠ ρ₀'.img) {y : ↥(muGroup Ω W)}
    (hy : y ∈ Asc77.Thompson.muDelta Ω W) :
    ∃ g : G, g ∈ ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R ∧ g ∈ Subgroup.normalizer (W : Set G) ∧
      ∃ ρ : Asc77.Thompson.Rep Ω W, (ρ = ρ₀ ∨ ρ = ρ₀' ∨ ρ = ρ₁) ∧
        Asc77.Thompson.piG W g * ρ.img * (Asc77.Thompson.piG W g)⁻¹ =
          ((y : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) := by
  set A := T7D.imgQ ρ₀ with hA
  set B := T7D.imgQ ρ₀' with hB
  set C := T7D.imgQ ρ₁ with hCq
  have hsw : ∀ q : ↥(muGroup Ω W), q ∈ Asc77.Thompson.muDelta Ω W → φ q ∈ Sec13.L94T.swaps4 :=
    fun q hq => Sec13.L94T.mem_swaps4 ((hφ q).mp hq)
  have hab' : φ A ≠ φ B := fun h => hab (congrArg Subtype.val (φ.injective h))
  have hca' : φ C ≠ φ A := fun h => hca (congrArg Subtype.val (φ.injective h))
  have hcb' : φ C ≠ φ B := fun h => hcb (congrArg Subtype.val (φ.injective h))
  have hcomm' : φ A * φ B = φ B * φ A := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hcomm)
  have hr₀N := ρ₀.r_mem_normalizer
  have hr₀'N := ρ₀'.r_mem_normalizer
  have hr₀X : ρ₀.r ∈ ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R := Subgroup.mem_sup_left (Subgroup.mem_sup_left ρ₀.hr)
  have hr₀'X : ρ₀'.r ∈ ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right ρ₀'.hr)
  have h1 : Asc77.Thompson.piG W (1 : G) = 1 := Asc77.Thompson.piG_of_mem_sup (Subgroup.one_mem _)
  have hval : ∀ q : ↥(muGroup Ω W), φ q = φ y → ((q : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) =
      ((y : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) := fun q h => congrArg Subtype.val (φ.injective h)
  rcases Sec13.L94T.s4_swap_orbit _ (hsw A (T7D.imgQ_mem ρ₀)) _ (hsw B (T7D.imgQ_mem ρ₀')) _
      (hsw C (T7D.imgQ_mem ρ₁)) _ (hsw y hy) hab' hcomm' hca' hcb' with h | h | h | h | h | h
  · refine ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, ρ₀, Or.inl rfl, ?_⟩
    rw [h1, one_mul, inv_one, mul_one]
    exact hval A h.symm
  · refine ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, ρ₀', Or.inr (Or.inl rfl), ?_⟩
    rw [h1, one_mul, inv_one, mul_one]
    exact hval B h.symm
  · refine ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, ρ₁, Or.inr (Or.inr rfl), ?_⟩
    rw [h1, one_mul, inv_one, mul_one]
    exact hval C h
  · refine ⟨ρ₀.r, hr₀X, hr₀N, ρ₁, Or.inr (Or.inr rfl), ?_⟩
    have := hval (A * C * A⁻¹) (by rw [map_mul, map_mul, map_inv, h])
    exact this
  · refine ⟨ρ₀'.r, hr₀'X, hr₀'N, ρ₁, Or.inr (Or.inr rfl), ?_⟩
    have := hval (B * C * B⁻¹) (by rw [map_mul, map_mul, map_inv, h])
    exact this
  · refine ⟨ρ₀.r * ρ₀'.r, Subgroup.mul_mem _ hr₀X hr₀'X, Subgroup.mul_mem _ hr₀N hr₀'N, ρ₁,
      Or.inr (Or.inr rfl), ?_⟩
    have := hval (A * B * C * (A * B)⁻¹) (by rw [map_mul, map_mul, map_mul, map_inv, map_mul, h])
    rw [Asc77.Thompson.piG_mul hr₀N hr₀'N]
    exact this

theorem inf_W_le_of_swap (hΩ : HypOmegaGen Ω) (c : Q3CL.Thompson.Ctx Ω W)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4))
    (hφ : ∀ x, x ∈ Asc77.Thompson.muDelta Ω W ↔ (φ x).IsSwap) (ρ₀ ρ₀' ρ₁ : Asc77.Thompson.Rep Ω W)
    (hab : ρ₀.img ≠ ρ₀'.img) (hcomm : ρ₀.img * ρ₀'.img = ρ₀'.img * ρ₀.img)
    (hca : ρ₁.img ≠ ρ₀.img) (hcb : ρ₁.img ≠ ρ₀'.img) (σ : Asc77.Thompson.Rep Ω W) :
    σ.K ⊓ W ≤ ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R := by
  obtain ⟨g, hgX, hgN, ρ, hρ, himg⟩ :=
    exists_conj_of_swap φ hφ ρ₀ ρ₀' ρ₁ hab hcomm hca hcb (T7D.imgQ_mem σ)
  let τ : Asc77.Thompson.Rep Ω W :=
    { K := conjSub g ρ.K
      R := conjSub g ρ.R
      r := g * ρ.r * g⁻¹
      hK := hΩ.conjInvariant g ρ.K ρ.hK
      hR := Q3CL.Thompson.conjSub_mem_D hΩ ρ.hR hgN
      hRK := ρ.hRK.conj g
      hr := conj_mem_conjSub ρ.hr
      hrW := fun h => ρ.hrW ((Asc77.Thompson.mem_normalizer_iff_of_mem hgN _).mp h) }
  have hrN := ρ.r_mem_normalizer
  have hτ : τ.img = σ.img := by
    show Asc77.Thompson.piG W (g * ρ.r * g⁻¹) = σ.img
    rw [Asc77.Thompson.piG_mul (Subgroup.mul_mem _ hgN hrN) (Subgroup.inv_mem _ hgN),
      Asc77.Thompson.piG_mul hgN hrN, Asc77.Thompson.piG_inv hgN]
    exact himg
  have hK : conjSub g ρ.K = σ.K := c.K_eq_of_img_eq τ σ hτ
  have hρX : ρ.R ≤ ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R := by
    rcases hρ with rfl | rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hKW : ρ.K ⊓ W = ρ.R ⊓ W := (Q3CL.Thompson.inf_W_of_mem_D hΩ c.hW ρ.hR ρ.hK ρ.hRK).1.symm
  intro x hx
  have hx1 : g⁻¹ * x * g ∈ ρ.K := by
    have h : x ∈ conjSub g ρ.K := hK ▸ hx.1
    rw [mem_conjSub_iff] at h
    exact h
  have hx2 : g⁻¹ * x * g ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx.2
    simpa using this
  have hx3 : g⁻¹ * x * g ∈ ρ.R := by
    have : g⁻¹ * x * g ∈ ρ.K ⊓ W := ⟨hx1, hx2⟩
    rw [hKW] at this
    exact this.1
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgX (hρX hx3)) (Subgroup.inv_mem _ hgX)

theorem W_le_of_swap (hΩ : HypOmegaGen Ω) (c : Q3CL.Thompson.Ctx Ω W)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4))
    (hφ : ∀ x, x ∈ Asc77.Thompson.muDelta Ω W ↔ (φ x).IsSwap) (ρ₀ ρ₀' ρ₁ : Asc77.Thompson.Rep Ω W)
    (hab : ρ₀.img ≠ ρ₀'.img) (hcomm : ρ₀.img * ρ₀'.img = ρ₀'.img * ρ₀.img)
    (hca : ρ₁.img ≠ ρ₀.img) (hcb : ρ₁.img ≠ ρ₀'.img) : W ≤ ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R := by
  have hW := c.hW
  obtain ⟨η, ⟨S₀, hηS, -⟩, hWη⟩ := hW
  have hWS : W ≤ (S₀ : Subgroup G) := hWη.le.trans (iSup₂_le fun U hU => (hηS.1 hU).2)
  refine hWη.le.trans (iSup₂_le fun U hU => ?_)
  obtain ⟨hUU, hUS⟩ := hηS.1 hU
  obtain ⟨R', hR', hUR', -, -⟩ := id hUU
  obtain ⟨M, hM, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hUM : U ≤ M := hUR'.trans hR'M.1
  obtain ⟨T, hT, hTM⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hΩ c.hW hWS hM hUU hUM hUS
  obtain ⟨σ, hσK, -⟩ := Sec13.L94T.exists_rep hΩ c.hW hM hTM hT
  have hUW : U ≤ W := (le_iSup₂_of_le U hU le_rfl).trans hWη.ge
  refine le_trans ?_ (inf_W_le_of_swap hΩ c φ hφ ρ₀ ρ₀' ρ₁ hab hcomm hca hcb σ)
  rw [hσK]
  exact le_inf hUM hUW

theorem mGrp_le_of_swap (hΩ : HypOmegaGen Ω) (c : Q3CL.Thompson.Ctx Ω W)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4))
    (hφ : ∀ x, x ∈ Asc77.Thompson.muDelta Ω W ↔ (φ x).IsSwap) (ρ₀ ρ₀' ρ₁ : Asc77.Thompson.Rep Ω W)
    (hab : ρ₀.img ≠ ρ₀'.img) (hcomm : ρ₀.img * ρ₀'.img = ρ₀'.img * ρ₀.img)
    (hca : ρ₁.img ≠ ρ₀.img) (hcb : ρ₁.img ≠ ρ₀'.img) :
    MGrp Ω W ≤ (ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R) ⊔ OCW W := by
  set X := ρ₀.R ⊔ ρ₀'.R ⊔ ρ₁.R with hX
  have hWX : W ≤ X := W_le_of_swap hΩ c φ hφ ρ₀ ρ₀' ρ₁ hab hcomm hca hcb
  refine iSup₂_le fun P hP => ?_
  intro p hp
  by_cases hpW : p ∈ W
  · exact Subgroup.mem_sup_left (hWX hpW)
  have hpN : p ∈ Subgroup.normalizer (W : Set G) := hP.2 hp
  have hpμ : Asc77.Thompson.piG W p ∈ muGroup Ω W :=
    Asc77.Thompson.mem_muGroup_iff.mpr
      ⟨p, Subgroup.mem_sup_left (Asc77.Thompson.le_MGrp_of_mem_D hP hp), rfl⟩
  have hyΔ : (⟨_, hpμ⟩ : ↥(muGroup Ω W)) ∈ Asc77.Thompson.muDelta Ω W := ⟨P, hP, p, hp, hpW, rfl⟩
  obtain ⟨g, hgX, hgN, ρ, hρ, himg⟩ := exists_conj_of_swap φ hφ ρ₀ ρ₀' ρ₁ hab hcomm hca hcb hyΔ
  have hρX : ρ.R ≤ X := by
    rcases hρ with rfl | rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hrN := ρ.r_mem_normalizer
  have hqN : g * ρ.r * g⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hrN) (Subgroup.inv_mem _ hgN)
  have hpi : Asc77.Thompson.piG W (g * ρ.r * g⁻¹) = Asc77.Thompson.piG W p := by
    rw [Asc77.Thompson.piG_mul (Subgroup.mul_mem _ hgN hrN) (Subgroup.inv_mem _ hgN),
      Asc77.Thompson.piG_mul hgN hrN, Asc77.Thompson.piG_inv hgN]
    exact himg
  have hw := (Asc77.Thompson.piG_eq_iff hqN hpN).mp hpi
  have hqX : g * ρ.r * g⁻¹ ∈ X :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgX (hρX ρ.hr)) (Subgroup.inv_mem _ hgX)
  have e : p = (g * ρ.r * g⁻¹) * ((g * ρ.r * g⁻¹)⁻¹ * p) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqX) ((sup_le_sup_right hWX _) hw)

theorem rLayer_le_sup_MGrp (hΩ : HypOmegaGen Ω) {e : G}
    (hE : rLayer Ω e ≤ oddCoreOf (rLayer Ω e) ⊔
      (rLayer Ω e ⊓ Subgroup.normalizer (W : Set G))) :
    rLayer Ω e ≤ oddCoreOf (rLayer Ω e) ⊔ MGrp Ω W := by
  have key : ∀ R ∈ RSet Ω, R ≤ Subgroup.centralizer ({e} : Set G) →
      R ≤ oddCoreOf (rLayer Ω e) ⊔ MGrp Ω W := by
    intro R hR hRe
    have hRE : R ≤ rLayer Ω e := F7C.le_rLayer hR hRe
    obtain ⟨J, -, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    obtain ⟨o, ho, hoN⟩ := exists_oddCore_conj_le hE hRJ.2.1 hRE
    have hQN : conjSub o⁻¹ R ≤ Subgroup.normalizer (W : Set G) := by
      intro x hx
      rw [mem_conjSub_iff, inv_inv] at hx
      have := hoN _ hx
      have e : o⁻¹ * (o * x * o⁻¹) * o = x := by group
      rwa [e] at this
    have hQD : conjSub o⁻¹ R ∈ DSet Ω W := ⟨Q3CL.Thompson.conjSub_mem_RSet hΩ hR o⁻¹, hQN⟩
    have hQM := Asc77.Thompson.le_MGrp_of_mem_D hQD
    intro x hx
    have hx' : o⁻¹ * x * o ∈ conjSub o⁻¹ R := by
      rw [mem_conjSub_iff, inv_inv]
      have e : o * (o⁻¹ * x * o) * o⁻¹ = x := by group
      rw [e]
      exact hx
    have e : x = o * (o⁻¹ * x * o) * o⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
      (Subgroup.mem_sup_right (hQM hx'))) (Subgroup.mem_sup_left ((oddCoreOf _).inv_mem ho))
  exact iSup₂_le fun R hR => iSup_le fun hRe => key R hR hRe

end F7G

section Steps

variable {n : ℕ}

theorem p23EGenD_proved : P23EGenD n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Q₀ Q₀' Q₁ hQ₀D hQ₀'D hQ₁D hQ₀ hQ₀' hQ₁
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have hW : W ∈ WSet (Om R) := hd.hW
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hKg : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hzg : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    have := TwinPerpV3.A6jB.isUniqueInvolution_conjSub hz g
    rwa [hd.hgt] at this
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have htrans : ∀ J ∈ Om R, ∃ a : Y, conjSub a (tightCore R) = J := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨φ, hφ⟩ := Sec13.L94.exists_swap_equiv hPG hW hK htrans hz hc.std.hK' hc.std.hne hperp
    hd.hS4
  have c : Q3CL.Thompson.Ctx (Om R) W := Q3CL.T8.ctxOf hPG hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hne_ue⟩ := e_decomp hc
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := Sec13.L94T.exists_rep hΩ hW hK hQ₀ hQ₀D
  obtain ⟨ρ₀', hρ₀'K, hρ₀'R⟩ := Sec13.L94T.exists_rep hΩ hW hK'Ω hQ₀' hQ₀'D
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := Sec13.L94T.exists_rep hΩ hW hKg hQ₁ hQ₁D
  have hab : ρ₀.img ≠ ρ₀'.img := fun h => by
    have := c.K_eq_of_img_eq ρ₀ ρ₀' h
    rw [hρ₀K, hρ₀'K] at this
    exact hc.std.hne this.symm
  have hnbr : K' ∈ omegaNbr (Om R) (tightCore R) := by
    have h : K' ∈ KPerp (Om R) (tightCore R) := by rw [hperp]; exact Or.inr rfl
    rcases h with h | h
    · exact absurd h hc.std.hne
    · exact h
  have hcomm : ρ₀.img * ρ₀'.img = ρ₀'.img * ρ₀.img :=
    Q3CL.Thompson.piG_comm_of_mem_omegaNbr Sec6Gen.l6_2Gen hΩ hW c.hkey hK hK'Ω
      (Ne.symm hc.std.hne) (hρ₀R ▸ ρ₀.hR) (hρ₀'R ▸ ρ₀'.hR) hQ₀ hQ₀' hnbr
      (hρ₀R ▸ ρ₀.hr) (hρ₀'R ▸ ρ₀'.hr) ρ₀.hrW
  have hinv : ∀ {J : Subgroup Y}, IsUniqueInvolution J t → IsUniqueInvolution J (u * e) → False :=
    fun h1 h2 => by
      rcases h1.unique _ h2.mem h2.sq with h | h
      · exact h2.ne_one h
      · exact hne_ue h
  have hca : ρ₁.img ≠ ρ₀.img := fun h => by
    have := c.K_eq_of_img_eq ρ₁ ρ₀ h
    rw [hρ₁K, hρ₀K] at this
    exact hinv hz (this ▸ hzg)
  have hcb : ρ₁.img ≠ ρ₀'.img := fun h => by
    have := c.K_eq_of_img_eq ρ₁ ρ₀' h
    rw [hρ₁K, hρ₀'K] at this
    exact hinv hz' (this ▸ hzg)
  have hMX := F7G.mGrp_le_of_swap hΩ c φ hφ ρ₀ ρ₀' ρ₁ hab hcomm hca hcb
  rw [hρ₀R, hρ₀'R, hρ₁R] at hMX
  set E := rLayer (Om R) e with hEdef
  set X := Q₀ ⊔ Q₀' ⊔ Q₁ with hXdef
  have hNe : Subgroup.normalizer (W : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) :=
    normalizer_le_centralizer_e hd
  have hDE : ∀ P ∈ DSet (Om R) W, P ≤ E := fun P hP => F7C.le_rLayer hP.1 (hP.2.trans hNe)
  have hXE : X ≤ E := sup_le (sup_le (hDE _ hQ₀D) (hDE _ hQ₀'D)) (hDE _ hQ₁D)
  have hXN : X ≤ Subgroup.normalizer ((OCW W : Subgroup Y) : Set Y) :=
    (sup_le (sup_le hQ₀D.2 hQ₀'D.2) hQ₁D.2).trans (Asc77.Thompson.normalizer_le_normalizer_OCW W)
  have hEc : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set Y)) := hE
  have hOCW := F7G.inf_OCW_le hEc
  have hME : MGrp (Om R) W ≤ oddCoreOf E ⊔ X := by
    intro m hm
    have hmE : m ∈ E := (iSup₂_le fun P hP => hDE P hP) hm
    have hm' : m ∈ ((X ⊔ OCW W : Subgroup Y) : Set Y) := hMX hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X (OCW W) hXN] at hm'
    obtain ⟨x, hx, o, ho, rfl⟩ := hm'
    have hoE : o ∈ E := by
      have e : o = x⁻¹ * (x * o) := by group
      rw [e]
      exact E.mul_mem (E.inv_mem (hXE hx)) hmE
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left (hOCW ⟨hoE, ho⟩))
  exact (F7G.rLayer_le_sup_MGrp hΩ hEc).trans (sup_le le_sup_left hME)

theorem p23EGen_proved : P23EGen n := p23EGen_of_genD p23EGenD_proved

theorem p23ECent_proved : P23ECent n := p23ECent_of_gen p23EGen_proved

theorem p23E7Not9C_of_w714' (h714 : P23E7W714 n) (h1 : P23E7LL1 n) (h2 : P23E7LL2 n)
    (h3 : P23E7LL3 n) : P23E7Not9C n :=
  p23E7Not9C_of_w714 h714 p23ECent_proved h1 h2 h3

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
