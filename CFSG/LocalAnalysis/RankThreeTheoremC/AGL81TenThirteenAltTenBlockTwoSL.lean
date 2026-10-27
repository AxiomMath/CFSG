module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenUnique
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenBlockTwoRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenBlockTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenBlockTwoTypes
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenSLThree
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenFourSixTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenOuter
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveInner
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveInnerBlocks
import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.HardMathSupport.Cooperstein.Proving.ConjBarM
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
import CFSG.LargeExtraspecial.S5Comp
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28LinTorus
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Background.F1Models
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open CFSG.Open CFSG.AGLEmbedding Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective ker_barMHomSub
  mem_normalizer_barM)

variable {G : Type} [Group G] [Finite G]

theorem sq_centralizes_of_card_three {Y : Type*} [Group Y] {Z : Subgroup Y} (hZ : Nat.card Z = 3)
    {s : Y} (hs : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z) : ∀ z ∈ Z, s ^ 2 * z * (s ^ 2)⁻¹ = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hcyc : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hog : orderOf (g : Y) = 3 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hZ]
  have hmem : ∀ z ∈ Z, ∃ k : ℤ, z = (g : Y) ^ k := by
    intro z hz
    obtain ⟨k, hk⟩ := hg ⟨z, hz⟩
    have hk' : g ^ k = ⟨z, hz⟩ := hk
    exact ⟨k, by rw [← Subgroup.coe_zpow, hk']⟩
  obtain ⟨k, hk⟩ := hmem _ (hs g g.2)
  have hg3 : (g : Y) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hog, pow_orderOf_eq_one]
  have hgk : ∀ m : ℤ, s * (g : Y) ^ m * s⁻¹ = (g : Y) ^ (k * m) := by
    intro m
    rw [_root_.zpow_mul, ← hk, ← MulAut.conj_apply, map_zpow]
    rfl
  have hfix : s ^ 2 * (g : Y) * (s ^ 2)⁻¹ = (g : Y) := by
    have h1 : s ^ 2 * (g : Y) * (s ^ 2)⁻¹ = s * (s * (g : Y) ^ (1 : ℤ) * s⁻¹) * s⁻¹ := by
      rw [zpow_one, pow_two]; group
    rw [h1, hgk 1, hgk (k * 1)]
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    ·
      exfalso
      obtain ⟨m, hm⟩ : (3 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero h
      have h1 : s * (g : Y) * s⁻¹ = 1 := by
        rw [← zpow_one (g : Y), hgk, hm, mul_one, _root_.zpow_mul, hg3, _root_.one_zpow]
      have h2 : (g : Y) = 1 := by
        have := congrArg (fun w => s⁻¹ * w * s) h1
        simpa [mul_assoc] using this
      rw [h2, orderOf_one] at hog
      omega
    · have hkk : k * (k * 1) % 3 = 1 := by
        rw [mul_one, Int.mul_emod, h]
        norm_num
      have hk' : k * (k * 1) = 3 * (k * (k * 1) / 3) + 1 := by omega
      rw [hk', _root_.zpow_add, _root_.zpow_mul, hg3, _root_.one_zpow, one_mul, zpow_one]
    · have hkk : k * (k * 1) % 3 = 1 := by
        rw [mul_one, Int.mul_emod, h]
        norm_num
      have hk' : k * (k * 1) = 3 * (k * (k * 1) / 3) + 1 := by omega
      rw [hk', _root_.zpow_add, _root_.zpow_mul, hg3, _root_.one_zpow, one_mul, zpow_one]
  intro z hz
  obtain ⟨m, rfl⟩ := hmem z hz
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hfix]

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1
    exact this ▸ hy

theorem map_subgroupOf_eq_range {N I : Subgroup G} (hIN : I ≤ N) {Q : Type*} [Group Q]
    (ψ : ↥N →* Q) : (I.subgroupOf N).map ψ = (ψ.comp (Subgroup.inclusion hIN)).range := by
  ext q
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, Subgroup.mem_subgroupOf.mp hn⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Subgroup.inclusion hIN i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩

theorem mem_normalizer_and_inner_of_map {N I₀ : Subgroup G} {Q : Type*} [Group Q]
    (ψ : ↥N →* Q) (hψ : IsPGroup 2 ψ.ker) (hIN : I₀ ≤ N) (hIs : IsSubnormal I₀ N)
    (hIp : ⁅I₀, I₀⁆ = I₀) {s : G} (hsN : s ∈ normalizer (N : Set G)) (n₀ : ↥N)
    (hs : ∀ x : ↥N, ψ ⟨s * x * s⁻¹, (mem_normalizer_iff.mp hsN x).mp x.2⟩ =
      ψ n₀ * ψ x * (ψ n₀)⁻¹)
    {c : Q} (hc : c ∈ (ψ.comp (Subgroup.inclusion hIN)).range)
    (hcu : ∀ u ∈ (ψ.comp (Subgroup.inclusion hIN)).range, ψ n₀ * u * (ψ n₀)⁻¹ = c * u * c⁻¹) :
    s ∈ normalizer (I₀ : Set G) ∧
      ∃ j ∈ I₀, ∀ x ∈ I₀, s * x * s⁻¹ * (j * x * j⁻¹)⁻¹ ∈ pCoreOf 2 I₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN' : ∀ x ∈ N, s * x * s⁻¹ ∈ N := fun x hx => (mem_normalizer_iff.mp hsN x).mp hx
  have hNs : N.map (MulAut.conj s).toMonoidHom = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hsN' y hy
    · intro hx
      refine ⟨s⁻¹ * x * s, ?_, by simp [mul_assoc]⟩
      apply (mem_normalizer_iff.mp hsN (s⁻¹ * x * s)).mpr
      simpa [mul_assoc] using hx
  have hR : ∀ x (hx : x ∈ I₀), (ψ.comp (Subgroup.inclusion hIN)) ⟨x, hx⟩ ∈
      (ψ.comp (Subgroup.inclusion hIN)).range := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hmem : ∀ x (hx : x ∈ I₀),
      ψ ⟨s * x * s⁻¹, hsN' x (hIN hx)⟩ = c * ψ ⟨x, hIN hx⟩ * c⁻¹ := fun x hx =>
    (hs ⟨x, hIN hx⟩).trans (hcu _ (hR x hx))
  set I₁ := I₀.map (MulAut.conj s).toMonoidHom with hI₁
  have h₁N : I₁ ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsN' x (hIN hx)
  have h₁s : IsSubnormal I₁ N := by
    have := hIs.map (MulAut.conj s).toMonoidHom
    rwa [hNs] at this
  have h₁p : ⁅I₁, I₁⁆ = I₁ := by rw [hI₁, ← Subgroup.map_commutator, hIp]
  have he : (I₁.subgroupOf N).map ψ = (I₀.subgroupOf N).map ψ := by
    rw [map_subgroupOf_eq_range hIN]
    ext q
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨x, hx, hxn⟩ := Subgroup.mem_subgroupOf.mp hn
      have hn' : n = ⟨s * x * s⁻¹, hsN' x (hIN hx)⟩ := Subtype.ext hxn.symm
      rw [hn', hmem x hx]
      obtain ⟨⟨j, hj⟩, rfl⟩ := hc
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR j hj) (hR x hx))
        (Subgroup.inv_mem _ (hR j hj))
    · rintro ⟨i, rfl⟩
      have hv : c⁻¹ * (ψ.comp (Subgroup.inclusion hIN)) i * c ∈
          (ψ.comp (Subgroup.inclusion hIN)).range := by
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) ⟨i, rfl⟩) hc
      obtain ⟨⟨x, hx⟩, hxv⟩ := hv
      refine ⟨⟨s * x * s⁻¹, hsN' x (hIN hx)⟩, Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩, ?_⟩
      rw [hmem x hx]
      change c * (ψ.comp (Subgroup.inclusion hIN)) ⟨x, hx⟩ * c⁻¹ = _
      rw [hxv]
      group
  have hI : I₁ = I₀ := eq_of_map_eq_of_isPGroup_ker ψ hψ h₁N hIN h₁s hIs h₁p hIp he
  have hsI : s ∈ normalizer (I₀ : Set G) := mem_normalizer_of_map_conj_eq hI
  obtain ⟨⟨j, hj⟩, hjc⟩ := hc
  refine ⟨hsI, j, hj, fun x hx => ?_⟩
  have hsx : s * x * s⁻¹ ∈ I₀ := (mem_normalizer_iff.mp hsI x).mp hx
  have hjx : j * x * j⁻¹ ∈ I₀ := I₀.mul_mem (I₀.mul_mem hj hx) (I₀.inv_mem hj)
  have hw : s * x * s⁻¹ * (j * x * j⁻¹)⁻¹ ∈ I₀ := I₀.mul_mem hsx (I₀.inv_mem hjx)
  have hk : (⟨_, hw⟩ : ↥I₀) ∈ (ψ.comp (Subgroup.inclusion hIN)).ker := by
    rw [MonoidHom.mem_ker]
    have e1 : (ψ.comp (Subgroup.inclusion hIN)) ⟨_, hw⟩ =
        ψ ⟨s * x * s⁻¹, hsN' x (hIN hx)⟩ * (ψ ⟨j * x * j⁻¹, hIN hjx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    have e2 : ψ ⟨j * x * j⁻¹, hIN hjx⟩ = c * ψ ⟨x, hIN hx⟩ * c⁻¹ := by
      rw [← hjc]
      have : (⟨j * x * j⁻¹, hIN hjx⟩ : ↥N) =
          ⟨j, hIN hj⟩ * ⟨x, hIN hx⟩ * (⟨j, hIN hj⟩ : ↥N)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      rfl
    rw [e1, e2, hmem x hx, mul_inv_cancel]
  have hkP : IsPGroup 2 (ψ.comp (Subgroup.inclusion hIN)).ker := by
    rw [← MonoidHom.comap_ker]
    exact hψ.comap_of_injective _ (Subgroup.inclusion_injective hIN)
  have hle : (ψ.comp (Subgroup.inclusion hIN)).ker ≤ CFSG.pCore 2 ↥I₀ :=
    le_sSup ⟨MonoidHom.normal_ker _, hkP⟩
  exact ⟨_, hle hk, rfl⟩

theorem inf_centralizer_map_conj {Y : Type*} [Group Y] (A : Subgroup Y) (g : Y) :
    A.map (MulAut.conj g).toMonoidHom ⊓
        centralizer (A.map (MulAut.conj g).toMonoidHom : Set Y) =
      (A ⊓ centralizer (A : Set Y)).map (MulAut.conj g).toMonoidHom := by
  ext w
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    refine ⟨a, ⟨ha, mem_centralizer_iff.mpr fun y hy => ?_⟩, rfl⟩
    have h1 := mem_centralizer_iff.mp hc (g * y * g⁻¹) ⟨y, hy, rfl⟩
    have h1' : g * y * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * y * g⁻¹) := h1
    have h2 : g * (y * a) * g⁻¹ = g * (a * y) * g⁻¹ := by
      calc g * (y * a) * g⁻¹ = g * y * g⁻¹ * (g * a * g⁻¹) := by group
        _ = g * a * g⁻¹ * (g * y * g⁻¹) := h1'
        _ = g * (a * y) * g⁻¹ := by group
    simpa using h2
  · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := mem_centralizer_iff.mp hc y hy
    change g * y * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group

section SLThree

variable {K : Type} [Field K]

theorem card_center_slThree [Finite K] (hK : Nat.card K = 4) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) = 3 := by
  classical
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have htop : rootsOfUnity (Fintype.card (Fin 3)) K = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rw [mem_rootsOfUnity, Fintype.card_fin, ← h3]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top, h3]

theorem card_inf_centralizer_of_bijective [Finite K] (hK : Nat.card K = 4) {Y : Type*} [Group Y]
    {A : Subgroup Y} (ρ : SpecialLinearGroup (Fin 3) K →* ↥A) (hρ : Function.Bijective ρ) :
    Nat.card ↥(A ⊓ centralizer (A : Set Y)) = 3 := by
  rw [← card_center_slThree hK]
  refine Nat.card_congr (Equiv.trans ?_
    (Subgroup.centerCongr (MulEquiv.ofBijective ρ hρ).symm).toEquiv)
  exact
    { toFun := fun w => ⟨⟨w, w.2.1⟩, Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (mem_centralizer_iff.mp w.2.2 y y.2)⟩
      invFun := fun z => ⟨z.1.1, z.1.2, mem_centralizer_iff.mpr fun h hh =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨h, hh⟩)⟩
      left_inv := fun w => rfl
      right_inv := fun z => rfl }

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs in
theorem exists_elemAbelian_nine_of_slThree [Finite K] (hK : Nat.card K = 4) {Y : Type*}
    [Group Y] {A : Subgroup Y} (ρ : SpecialLinearGroup (Fin 3) K →* ↥A)
    (hρ : Function.Injective ρ) :
    ∃ E : Subgroup Y, E ≤ A ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  classical
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hu3 : ∀ u : Kˣ, u ^ 3 = 1 := fun u => by rw [← h3]; exact pow_card_eq_one'
  have h32 : 2 + 1 ≤ 3 := by norm_num
  have hTinj : Function.Injective (linTorus K 2 h32) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    funext j
    have ha' : linTorus K 2 h32 a = linTorus K 2 h32 1 := by rw [ha, map_one]
    have h1 := congrArg (fun M : SpecialLinearGroup (Fin 3) K =>
      (M : Matrix (Fin 3) (Fin 3) K) (Fin.castSucc j) (Fin.castSucc j)) ha'
    simp only [coe_linTorus, Matrix.diagonal_apply_eq, linTorusVec_one, Pi.one_apply,
      Units.val_one] at h1
    have h2 : linTorusVec a (Fin.castSucc j) = a j := by
      rw [linTorusVec, dif_pos (show ((Fin.castSucc j : Fin 3) : ℕ) < 2 from j.isLt)]
      rfl
    rw [h2] at h1
    exact Units.ext (by rw [h1]; rfl)
  let τ : (Fin 2 → Kˣ) →* Y := A.subtype.comp (ρ.comp (linTorus K 2 h32))
  have hτ : Function.Injective τ := A.subtype_injective.comp (hρ.comp hTinj)
  refine ⟨τ.range, ?_, ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact (ρ (linTorus K 2 h32 a)).2
  · obtain ⟨_, a, rfl⟩ := u
    obtain ⟨_, b, rfl⟩ := v
    apply Subtype.ext
    change τ a * τ b = τ b * τ a
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := funext fun j => hu3 (a j)
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv.symm, Nat.card_fun, h3, Nat.card_fin]

end SLThree

theorem pRank_three_top_quotient (X : Subgroup G) :
    Open.pRank 3 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) = Open.pRank 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥X) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X,
    ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥X) hO]

theorem sq_facts_of_slThree {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) {t : G}
    (htX : t ∈ X) (htL : L.map (MulAut.conj t).toMonoidHom ≠ L) (h3 : Open.pRank 3 X ≤ 3)
    (ρ : SpecialLinearGroup (Fin 3) (GaloisField 2 2) →* ↥(barM X L))
    (hρ : Function.Bijective ρ) :
    L.map (MulAut.conj (t ^ 2)).toMonoidHom = L ∧
      ∀ z ∈ barM X L, (∀ y ∈ barM X L, z * y = y * z) →
        (QuotientGroup.mk (⟨t, htX⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ^ 2 * z *
          ((QuotientGroup.mk (⟨t, htX⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) ^ 2)⁻¹ = z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  set tb : ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk (⟨t, htX⟩ : ↥X) with htb
  have hZ3 : Nat.card ↥(barM X L ⊓ centralizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X))) = 3 :=
    card_inf_centralizer_of_bijective hK4 ρ hρ
  set Zb := barM X L ⊓ centralizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) with hZb
  have hcentral : ∀ {A : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} {w}, w ∈ A →
      (∀ y ∈ A, w * y = y * w) → w ∈ A ⊓ centralizer (A : Set _) :=
    fun hw hc => ⟨hw, mem_centralizer_iff.mpr fun y hy => (hc y hy).symm⟩
  have hcomm_of : ∀ {A B : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}, ⁅A, B⁆ = ⊥ →
      ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A B h a ha b hb
    have h1 := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  set L' := L.map (MulAut.conj t).toMonoidHom with hL'
  have hL'c := isTwoPrimeComponent_map_conj hL htX
  have hLb' : barM X L' = (barM X L).map (MulAut.conj tb).toMonoidHom := barM_map_conj hL.le htX
  have h12 := hcomm_of (CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hL.component
    hL'c.component (barM_map_conj_ne hL htX htL))
  have hZb' : barM X L' ⊓ centralizer (barM X L' : Set (↥X ⧸ CFSG.pCore 2 ↥X)) =
      Zb.map (MulAut.conj tb).toMonoidHom := by
    rw [hLb', inf_centralizer_map_conj]
  obtain ⟨E, hEL, hE, hE9⟩ := exists_elemAbelian_nine_of_slThree hK4 ρ hρ.1
  have hEne : E ⊓ barM X L' ≠ ⊥ := fun h => by
    have := four_le_pRank_of_two_blocks_of_inf hL htX htL hEL hE hE9 h
    omega
  obtain ⟨⟨x, hxE, hxL'⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hox : orderOf x = 3 := orderOf_eq_prime (hE.2 x hxE) hx1'
  have hxZ : x ∈ Zb := hcentral (hEL hxE) fun y hy => (h12 y hy x hxL').symm
  have hxZ' : x ∈ barM X L' ⊓ centralizer (barM X L' : Set (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    hcentral hxL' fun y hy => h12 x (hEL hxE) y hy
  have hzc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
  have hZx : Subgroup.zpowers x = Zb :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hxZ) (by rw [hzc, hZ3])
  have hZx' : Subgroup.zpowers x = Zb.map (MulAut.conj tb).toMonoidHom := by
    rw [← hZb']
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hxZ') ?_
    rw [hZb', Subgroup.card_map_of_injective (MulAut.conj tb).injective, hZ3, hzc]
  have hZZ : Zb.map (MulAut.conj tb).toMonoidHom = Zb := hZx'.symm.trans hZx
  have hnorm : ∀ z ∈ Zb, tb * z * tb⁻¹ ∈ Zb := fun z hz => by
    rw [← hZZ]
    exact ⟨z, hz, rfl⟩
  have hsq := sq_centralizes_of_card_three hZ3 hnorm
  refine ⟨?_, fun z hz hc => hsq z (hcentral hz hc)⟩
  by_contra hne
  have ht2X : t ^ 2 ∈ X := X.pow_mem htX 2
  have htb2 : (QuotientGroup.mk (⟨t ^ 2, ht2X⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) = tb ^ 2 := by
    rw [htb, ← QuotientGroup.mk_pow]
    rfl
  set L'' := L.map (MulAut.conj (t ^ 2)).toMonoidHom with hL''
  have hLb'' : barM X L'' = (barM X L).map (MulAut.conj (tb ^ 2)).toMonoidHom := by
    rw [hL'', barM_map_conj hL.le ht2X, htb2]
  have h13 := hcomm_of (CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hL.component
    (isTwoPrimeComponent_map_conj hL ht2X).component (barM_map_conj_ne hL ht2X hne))
  have hL'L'' : L'.map (MulAut.conj t).toMonoidHom = L'' := by
    rw [hL', hL'', Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    change t * (t * y * t⁻¹) * t⁻¹ = t ^ 2 * y * (t ^ 2)⁻¹
    rw [pow_two]
    group
  have hne' : L'.map (MulAut.conj t).toMonoidHom ≠ L' := fun h =>
    htL (Subgroup.map_injective (MulAut.conj t).injective h)
  have h23 := hcomm_of (CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hL'c.component
    (isTwoPrimeComponent_map_conj hL'c htX).component (barM_map_conj_ne hL'c htX hne'))
  rw [hL'L''] at h23
  have hZb'' : barM X L'' ⊓ centralizer (barM X L'' : Set (↥X ⧸ CFSG.pCore 2 ↥X)) =
      Zb.map (MulAut.conj (tb ^ 2)).toMonoidHom := by
    rw [hLb'', inf_centralizer_map_conj]
  obtain ⟨a, haE, haZ⟩ : ∃ a ∈ E, a ∉ Zb := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun b hb => hall b hb : E ≤ Zb)
    rw [hE9, hZ3] at this
    norm_num at this
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Zb.one_mem)
  have hoa : orderOf a = 3 := orderOf_eq_prime (hE.2 a haE) ha1
  have hcon : ∀ g : ↥X ⧸ CFSG.pCore 2 ↥X, orderOf (g * a * g⁻¹) = 3 := fun g => by
    rw [← hoa]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  have hsq' : ∀ z ∈ Zb, (tb ^ 2)⁻¹ * z * tb ^ 2 = z := fun z hz => by
    calc (tb ^ 2)⁻¹ * z * tb ^ 2 = (tb ^ 2)⁻¹ * (tb ^ 2 * z * (tb ^ 2)⁻¹) * tb ^ 2 := by
          rw [hsq z hz]
      _ = z := by group
  have ha₂ : tb * a * tb⁻¹ ∈ barM X L' := by
    rw [hLb']
    exact ⟨a, hEL haE, rfl⟩
  have ha₃ : tb ^ 2 * a * (tb ^ 2)⁻¹ ∈ barM X L'' := by
    rw [hLb'']
    exact ⟨a, hEL haE, rfl⟩
  have hn₂ : tb * a * tb⁻¹ ∉ Zb := by
    intro h
    rw [← hZZ] at h
    obtain ⟨w, hw, hwe⟩ := h
    have h1 : (MulAut.conj tb) w = (MulAut.conj tb) a := hwe
    exact haZ ((MulAut.conj tb).injective h1 ▸ hw)
  have hn₃ : tb ^ 2 * a * (tb ^ 2)⁻¹ ∉ Zb := by
    intro h
    have h1 := hsq' _ h
    have h2 : (tb ^ 2)⁻¹ * (tb ^ 2 * a * (tb ^ 2)⁻¹) * tb ^ 2 = a := by group
    rw [h2] at h1
    apply haZ
    rw [h1]
    exact h
  have h4 := four_le_pRank_of_three_blocks (L₁ := barM X L) (L₂ := barM X L') (L₃ := barM X L'')
    (Z := Zb) h12 h13 h23 (fun w hw y hy => (mem_centralizer_iff.mp hw.2 y hy).symm)
    (fun w hw hc => by
      have := hcentral hw hc
      rwa [hZb', hZZ] at this)
    (fun w hw hc => by
      have := hcentral hw hc
      rw [hZb''] at this
      obtain ⟨w', hw', rfl⟩ := this
      change tb ^ 2 * w' * (tb ^ 2)⁻¹ ∈ Zb
      rw [hsq w' hw']
      exact hw')
    hox hxZ (hEL hxE) (hEL haE) ha₂ ha₃ hoa (hcon tb) (hcon (tb ^ 2))
    (fun h => haZ (hZx ▸ h)) hn₂ hn₃
  rw [pRank_three_top_quotient] at h4
  omega

theorem exists_mem_conj_of_slThree {Y : Type} [Group Y] [Finite Y] {Lb Pb : Subgroup Y}
    (hpar : IsParabolicTwo Lb Pb)
    (ρ : SpecialLinearGroup (Fin 3) (GaloisField 2 2) →* ↥Lb) (hρ : Function.Bijective ρ)
    {i : ℕ} (hi : i = 1 ∨ i = 2)
    (hflag : (Pb.subgroupOf Lb).comap ρ = LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i})
    {s : Y} (hsL : s ∈ normalizer (Lb : Set Y)) (hsP : s ∈ normalizer (Pb : Set Y))
    (hs2 : ∃ k : ℕ, s ^ 2 ^ k = 1)
    (hsZ : ∀ z ∈ Lb, (∀ y ∈ Lb, z * y = y * z) → s * z * s⁻¹ = z) :
    ∃ y ∈ Pb, ∀ x ∈ Lb, s * x * s⁻¹ = y * x * y⁻¹ := by
  classical
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hc : ∀ g ∈ normalizer (Lb : Set Y), ∀ x ∈ Lb, g * x * g⁻¹ ∈ Lb :=
    fun g hg x hx => (mem_normalizer_iff.mp hg x).mp hx
  let γ : ↥Lb ≃* ↥Lb :=
    { toFun := fun x => ⟨s * x * s⁻¹, hc s hsL x x.2⟩
      invFun := fun x => ⟨s⁻¹ * x * s⁻¹⁻¹, hc s⁻¹ (inv_mem hsL) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hγ : ∀ x, (γ x : Y) = s * x * s⁻¹ := fun x => rfl
  have hγpow : ∀ m : ℕ, ∀ x, ((γ ^ m) x : Y) = s ^ m * x * (s ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hγ]
      group
  set e := MulEquiv.ofBijective ρ hρ with he
  let α : MulAut (SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := (e.trans γ).trans e.symm
  have hα : ∀ x, ρ (α x) = γ (ρ x) := fun x => e.apply_symm_apply _
  have hαpow : ∀ m : ℕ, ∀ x, ρ ((α ^ m) x) = (γ ^ m) (ρ x) := by
    intro m
    induction m with
    | zero => intro x; rw [pow_zero, pow_zero]; rfl
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ, MulAut.mul_apply]
  have hα2 : ∃ k : ℕ, α ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hs2
    refine ⟨k, MulEquiv.ext fun x => hρ.1 ?_⟩
    rw [hαpow, MulAut.one_apply]
    apply Subtype.ext
    rw [hγpow, hk]
    group
  have hαZ : ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 2)), α z = z := by
    intro z hz
    apply hρ.1
    rw [hα]
    apply Subtype.ext
    rw [hγ]
    refine hsZ _ (ρ z).2 fun y hy => ?_
    obtain ⟨w, hw⟩ := hρ.2 ⟨y, hy⟩
    have h1 : ρ z * ρ w = ρ w * ρ z := by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz w).symm]
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    rw [hw] at h2
    exact h2
  have hmemQ : ∀ x, x ∈ LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i} ↔ (ρ x : Y) ∈ Pb := by
    intro x
    rw [← hflag, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  have hαQ' : ∀ x, α x ∈ LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i} ↔
      x ∈ LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i} := by
    intro x
    rw [hmemQ, hmemQ, hα, hγ]
    exact (mem_normalizer_iff.mp hsP (ρ x)).symm
  have hαQ : (LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i}).map α.toMonoidHom =
      LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i} := by
    ext x
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro h
      have := (hαQ' (α.symm x)).mpr h
      rwa [MulEquiv.apply_symm_apply] at this
    · intro h
      apply (hαQ' (α.symm x)).mp
      rwa [MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := exists_conj_of_slThree hK4 hi α hα2 hαZ hαQ
  have hconj : ∀ x ∈ Lb, s * x * s⁻¹ = (ρ g : Y) * x * (ρ g : Y)⁻¹ := by
    intro x hx
    obtain ⟨w, hw⟩ := hρ.2 ⟨x, hx⟩
    have h1 : γ (ρ w) = ρ g * ρ w * (ρ g)⁻¹ := by
      rw [← hα, hg, map_mul, map_mul, map_inv]
    have h2 := congrArg Subtype.val h1
    rw [hγ, hw] at h2
    simpa using h2
  refine ⟨(ρ g : Y), ?_, hconj⟩
  apply mem_of_mem_normalizer_of_isParabolicTwo hpar (ρ g).2
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hconj x (hpar.1 hx)]
    exact (mem_normalizer_iff.mp hsP x).mp hx
  · intro hx
    have hxL : x ∈ Lb := by
      have h1 := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem (ρ g).2) (hpar.1 hx)) (ρ g).2
      simpa [mul_assoc] using h1
    rw [← hconj x hxL] at hx
    exact (mem_normalizer_iff.mp hsP x).mpr hx

theorem slThree_fiveComponent_inner {Y : Type} [Group Y] [Finite Y] {Lb Pb : Subgroup Y}
    (hPL : Pb ≤ Lb) (ρ : SpecialLinearGroup (Fin 3) (GaloisField 2 2) →* ↥Lb)
    (hρ : Function.Bijective ρ) {i : ℕ}
    (hflag : (Pb.subgroupOf Lb).comap ρ = LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i})
    {C : Subgroup (↥Pb ⧸ CFSG.pCore 2 ↥Pb)} (hC : IsFiveComponent Pb C) :
    C.Normal ∧ ∀ x, ∃ c ∈ C, ∀ u ∈ C, x * u * x⁻¹ = c * u * c⁻¹ := by
  classical
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hρk : ρ.ker ≤ Subgroup.center _ := by
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hρ.1]
    exact bot_le
  let ι := MulEquiv.subgroupCongr hflag
  let β := (LeviBlock.linLeviHom (GaloisField 2 2) 3 {i}).comp ι.toMonoidHom
  have hrange : β.range = (LeviBlock.linLeviHom (GaloisField 2 2) 3 {i}).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
      ← MonoidHom.range_eq_map]
  have hβ : IsPGroup 2 β.ker := by
    rw [← MonoidHom.comap_ker]
    exact (LeviBlock.isPGroup_ker_linLeviHom (by norm_num)).comap_of_injective _ ι.injective
  exact LeviFive.isFiveComponent_normal_inner hPL ρ hρ.2 hρk
    (LeviBlock.linBlockSL (GaloisField 2 2) 3 {i}) β hβ
    (hrange ▸ LeviBlock.pi_le_range_linLeviHom)
    (hrange ▸ LeviBlock.commutator_range_linLeviHom_le)
    (LeviBlock.isQuasisimple_or_isSolvable_linBlockSL {i})
    (fun a hq h60 q => LeviBlock.linLeviHom_inner_of_sixty hK4 a hq h60 (ι q)) hC

theorem pCore_eq_bot_of_isSubnormal_quotient {Q : Type} [Group Q] [Finite Q]
    {C : Subgroup (Q ⧸ CFSG.pCore 2 Q)} (hC : IsSubnormal C ⊤) : CFSG.pCore 2 ↥C = ⊥ := by
  have h1 := CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hC
  have h2 : pCoreOf 2 (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) = ⊥ := by
    have h3 := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := Q ⧸ CFSG.pCore 2 Q))
    rw [CFSG.GH74.GLS.Stage2.Signalizer.pCore_quotient_pCore (A := Q) 2] at h3
    have h4 : CFSG.pCore 2 ↥(⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h3
    rw [pCoreOf, h4, Subgroup.map_bot]
  have h5 : pCoreOf 2 C = ⊥ := eq_bot_iff.mpr (h1.trans h2.le)
  rw [pCoreOf] at h5
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h5

theorem kFactBlockAFive_two_nineThreeTwo (hOF : KFactCompParabOneFive)
    {X S L I₀ : Subgroup G} (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hI₀ : I₀ ∈ cZero (normalizer (S : Set G) ⊓ L)) (hI₀c : IsTwoPrimeComponent I₀ I₀)
    (f : ↥I₀ →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (h2 : NineThreeTwo X S L) (h3 : Open.pRank 3 X ≤ 3) {t : G} (htX : t ∈ X)
    (htS : t ∈ normalizer (S : Set G)) (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1)
    (htL : L.map (MulAut.conj t).toMonoidHom ≠ L) :
    t ^ 2 ∈ normalizer (I₀ : Set G) ∧
      ∃ j ∈ I₀, ∀ x ∈ I₀, t ^ 2 * x * (t ^ 2)⁻¹ * (j * x * j⁻¹)⁻¹ ∈ pCoreOf 2 I₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := hL.le
  have hNX : normalizer (S : Set G) ⊓ L ≤ X := inf_le_right.trans hLX
  have hI₀N : I₀ ≤ normalizer (S : Set G) ⊓ L := hI₀.le
  have hPL : barM X (normalizer (S : Set G) ⊓ L) ≤ barM X L := Subgroup.map_mono fun y hy => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hy.2
  have hβk : IsPGroup 2 (barMHomSub hNX).ker := by
    rw [ker_barMHomSub]
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp g.2)
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨x, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hthis := congrArg (fun y => ((y : ↥X) : G)) (congrArg Subtype.val hk)
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hthis ⊢
    rw [← hxg]
    exact hthis
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ↥(normalizer (S : Set G) ⊓ L) →*
      ↥(barM X (normalizer (S : Set G) ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM X (normalizer (S : Set G) ⊓ L)),
      ψ = (QuotientGroup.mk' _).comp (barMHomSub hNX) := ⟨_, rfl⟩
  have hψs : Function.Surjective ψ := by
    rw [hψdef]
    exact (QuotientGroup.mk'_surjective _).comp (barMHomSub_surjective hNX)
  have hψk : IsPGroup 2 ψ.ker := by
    rw [hψdef, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.pCore_isPGroup (p := 2)
      (G := ↥(barM X (normalizer (S : Set G) ⊓ L)))).comap_of_ker_isPGroup _ hβk
  set φ₀ := ψ.comp (Subgroup.inclusion hI₀N) with hφ₀
  have hφk : IsPGroup 2 φ₀.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hφ₀, ← MonoidHom.comap_ker]
    exact hψk.comap_of_injective _ (Subgroup.inclusion_injective hI₀N)
  have hφs : Function.Surjective φ₀.rangeRestrict := φ₀.rangeRestrict_surjective
  have hCs : IsSubnormal φ₀.range ⊤ := by
    have h1 : IsSubnormal (I₀.subgroupOf (normalizer (S : Set G) ⊓ L))
        ((normalizer (S : Set G) ⊓ L).subgroupOf (normalizer (S : Set G) ⊓ L)) :=
      hI₀.subnormal.comap (normalizer (S : Set G) ⊓ L).subtype
    rw [Subgroup.subgroupOf_self] at h1
    have h2 := h1.map ψ
    rwa [Subgroup.map_top_of_surjective _ hψs, map_subgroupOf_eq_range hI₀N] at h2
  have hQ : Open.IsQuasisimple (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) := by
    have htop : barM I₀ I₀ = ⊤ := by
      rw [barM, Subgroup.subgroupOf_self,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact Open.IsQuasisimple.of_mulEquiv
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm) hI₀c.component.2.2
  have hCq : Open.IsQuasisimple ↥φ₀.range :=
    isQuasisimple_of_surjective_of_isPGroup_ker hQ φ₀.rangeRestrict hφs hφk
      (pCore_eq_bot_of_isSubnormal_quotient hCs)
  have hCA5 := exists_surjective_alt5_of_ker f hf φ₀.rangeRestrict hφs hφk
  have hC5 : IsFiveComponent (barM X (normalizer (S : Set G) ⊓ L)) φ₀.range :=
    ⟨⟨le_top, hCs, hCq⟩, hCA5⟩
  have hCP : CompParab (barM X L) (barM X (normalizer (S : Set G) ⊓ L)) :=
    ⟨hL.component, h2.1,
      odd_card_center_of_pCore_eq_bot (pCore_barM_eq_bot hL.toIsTwoPrimeComponent),
      h2.2.1, barM_inf_normalizer_ne hA hL, ne_borel_of_alt5 hPL hCA5⟩
  rcases hOF _ _ _ hCP _ hC5 with ⟨E, hEL, hE, hE9, hEC⟩ | ⟨ρ, -, i, hρb, -, hi, hflag⟩
  · have := four_le_pRank_of_two_blocks hL.toIsTwoPrimeComponent htX htL hEL hE hE9 hEC
    omega
  obtain ⟨hLt, hZc⟩ := sq_facts_of_slThree hL.toIsTwoPrimeComponent htX htL h3 ρ hρb
  set tb : ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk (⟨t, htX⟩ : ↥X) with htb
  have ht2X : t ^ 2 ∈ X := X.pow_mem htX 2
  have htb2 : (QuotientGroup.mk (⟨t ^ 2, ht2X⟩ : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) = tb ^ 2 := by
    rw [htb, ← QuotientGroup.mk_pow]
    rfl
  have ht2L : t ^ 2 ∈ normalizer (L : Set G) := mem_normalizer_of_map_conj_eq hLt
  have ht2S : t ^ 2 ∈ normalizer (S : Set G) := pow_mem htS 2
  have ht2N : t ^ 2 ∈ normalizer ((normalizer (S : Set G) ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 := mem_normalizer_iff.mp (Subgroup.le_normalizer ht2S :
      t ^ 2 ∈ normalizer ((normalizer (S : Set G) : Subgroup G) : Set G)) y
    have h2 := mem_normalizer_iff.mp ht2L y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hsL : tb ^ 2 ∈ normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    htb2 ▸ mem_normalizer_barM (z := ⟨t ^ 2, ht2X⟩) ht2L
  have hsP : tb ^ 2 ∈ normalizer (barM X (normalizer (S : Set G) ⊓ L) :
      Set (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    htb2 ▸ mem_normalizer_barM (z := ⟨t ^ 2, ht2X⟩) ht2N
  have hs2 : ∃ k : ℕ, (tb ^ 2) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := ht2
    refine ⟨k, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, htb, ← QuotientGroup.mk_pow]
    have : (⟨t, htX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one, one_pow]
  obtain ⟨y, hyP, hy⟩ := exists_mem_conj_of_slThree h2.2.1 ρ hρb hi hflag hsL hsP hs2 hZc
  obtain ⟨-, hinn⟩ := slThree_fiveComponent_inner hPL ρ hρb hflag hC5
  obtain ⟨c, hc, hcu⟩ := hinn (QuotientGroup.mk ⟨y, hyP⟩)
  obtain ⟨n₀, hn₀⟩ := barMHomSub_surjective hNX ⟨y, hyP⟩
  have hψn₀ : ψ n₀ = QuotientGroup.mk ⟨y, hyP⟩ := by
    rw [hψdef, MonoidHom.comp_apply, hn₀]
    rfl
  refine mem_normalizer_and_inner_of_map ψ hψk hI₀N hI₀.subnormal hI₀c.perfect ht2N n₀ ?_ hc
    fun u hu => by rw [hψn₀]; exact hcu u hu
  intro x
  have hxL : (QuotientGroup.mk (Subgroup.inclusion hNX x) : ↥X ⧸ CFSG.pCore 2 ↥X) ∈ barM X L :=
    hPL (barMHomSub hNX x).2
  have hβx : barMHomSub hNX ⟨t ^ 2 * x * (t ^ 2)⁻¹, (mem_normalizer_iff.mp ht2N x).mp x.2⟩ =
      ⟨y, hyP⟩ * barMHomSub hNX x * (⟨y, hyP⟩ : ↥(barM X (normalizer (S : Set G) ⊓ L)))⁻¹ := by
    apply Subtype.ext
    change (QuotientGroup.mk (Subgroup.inclusion hNX
        ⟨t ^ 2 * x * (t ^ 2)⁻¹, (mem_normalizer_iff.mp ht2N x).mp x.2⟩) :
          ↥X ⧸ CFSG.pCore 2 ↥X) =
      y * QuotientGroup.mk (Subgroup.inclusion hNX x) * y⁻¹
    rw [← hy _ hxL, ← htb2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl
  rw [hψn₀, hψdef, MonoidHom.comp_apply, MonoidHom.comp_apply, hβx, map_mul, map_mul, map_inv]
  rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
