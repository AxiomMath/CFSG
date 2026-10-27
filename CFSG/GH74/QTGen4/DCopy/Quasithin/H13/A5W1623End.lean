module

public import CFSG.Quasithin.H13.A5W1623End
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623Lam
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.A5Model
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
  CFSG.QuasithinUnique.Vol2Native.A312L

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem conj_eq_of_inner_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLvK : S.Lv ≤ K)
    {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)} (hαs : Function.Surjective α)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    {a : G} (ha : a ∈ S.Tv) {k : ↥K}
    (hk : ∀ (l : ↥K) (h : a * l * a⁻¹ ∈ K), α ⟨a * l * a⁻¹, h⟩ = α k * α l * (α k)⁻¹) :
    ∀ w ∈ S.WK K, a * w * a⁻¹ = (k : G) * w * (k : G)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := S.WK K with hW
  set C := Subgroup.centralizer (W : Set G) with hC
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hKG hT
  have hHK := S.HK_eq_sup hLvK
  have hHN : S.HK K ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hT
  have hHC : S.HK K ≤ Subgroup.normalizer (C : Set G) :=
    hR.2.1.trans (normalizer_le_normalizer_centralizer W)

  set D := centralizerMod C (S.HK K) K with hD
  have hDH : D ≤ S.HK K := centralizerMod_le_left C (S.HK K) K
  have hHD : S.HK K ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ S.HK K, ∀ x ∈ D, g * x * g⁻¹ ∈ D := by
      intro g hg x hx
      obtain ⟨hxH, hxN, hxK⟩ := mem_centralizerMod.mp hx
      refine mem_centralizerMod.mpr ⟨(S.HK K).mul_mem ((S.HK K).mul_mem hg hxH)
        ((S.HK K).inv_mem hg), Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHC hg) hxN)
        (Subgroup.inv_mem _ (hHC hg)), fun l hl => ?_⟩
      have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hHN ((S.HK K).inv_mem hg)) l).mp hl
      rw [inv_inv] at hl'
      have h1 := (Subgroup.mem_normalizer_iff.mp (hHC hg) _).mp (hxK _ hl')
      have e : g * (x * (g⁻¹ * l * g) * x⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ =
          g * x * g⁻¹ * l * (g * x * g⁻¹)⁻¹ * l⁻¹ := by group
      rwa [e] at h1
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have h1 := key g⁻¹ ((S.HK K).inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

  have hT2 : IsPGroup 2 ↥S.Tv := (S.isSylowTwoOf_Tv_F4 h1222 h517).2.1
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).mp hT2
  have hD2 : ∀ d ∈ D, ∃ m : ℕ, d ^ 2 ^ m ∈ C := by
    intro d hd
    obtain ⟨hdH, -, hdK⟩ := mem_centralizerMod.mp hd
    rw [hHK] at hdH
    obtain ⟨k₀, hk₀, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hT).mp hdH
    obtain ⟨k', hk', hpow⟩ := CFSG.LieType.Chevalley.exists_mul_pow_eq_mul_pow hk₀ (hT hs) (2 ^ e)
    have hs1 : s ^ 2 ^ e = 1 := by
      have h1 := orderOf_dvd_natCard (⟨s, hs⟩ : ↥S.Tv)
      rw [he, Subgroup.orderOf_mk] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    rw [hs1, mul_one] at hpow
    refine ⟨e, ?_⟩
    rw [hpow]

    have hk'D : k' ∈ D := by
      rw [← hpow]
      exact D.pow_mem hd _
    obtain ⟨-, -, hk'K⟩ := mem_centralizerMod.mp hk'D
    have hcen : α ⟨k', hk'⟩ ∈ Subgroup.center (SpecialLinearGroup (Fin 4) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hαs g
      have h1 := hk'K l l.2
      have hlK : k' * l * k'⁻¹ * l⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem hk' l.2) (K.inv_mem hk')) (K.inv_mem l.2)
      have h2 := (hαC ⟨_, hlK⟩).mpr h1
      have e2 : (⟨k' * l * k'⁻¹ * l⁻¹, hlK⟩ : ↥K) = ⟨k', hk'⟩ * l * ⟨k', hk'⟩⁻¹ * l⁻¹ := rfl
      rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
      calc α l * α ⟨k', hk'⟩ = (α ⟨k', hk'⟩ * α l * (α ⟨k', hk'⟩)⁻¹ * (α l)⁻¹)⁻¹ *
            (α ⟨k', hk'⟩ * α l) := by group
        _ = α ⟨k', hk'⟩ * α l := by rw [h2, inv_one, one_mul]
    obtain ⟨r, hr4, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    have hr1 : r = 1 := zmod_two_eq_one_of_pow_four (by rwa [Fintype.card_fin] at hr4)
    have hα1 : α ⟨k', hk'⟩ = 1 :=
      Ln2P.sl_ext_of_coe (hr.symm.trans (by rw [hr1, map_one]; exact Ln2P.coeM_one.symm))
    exact (hαC ⟨k', hk'⟩).mp hα1
  have hDC := hR.2.2.2 D hDH hHD hD2

  have hkH : (k : G) ∈ S.HK K := by
    rw [hHK]
    exact Subgroup.mem_sup_left k.2
  have haH : a ∈ S.HK K := by
    rw [hHK]
    exact Subgroup.mem_sup_right ha
  have hmem : (k : G)⁻¹ * a ∈ D := by
    refine mem_centralizerMod.mpr ⟨(S.HK K).mul_mem ((S.HK K).inv_mem hkH) haH,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hHC hkH)) (hHC haH), fun l hl => ?_⟩
    have hal : a * l * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hT ha) l).mp hl
    have hx : (k : G)⁻¹ * (a * l * a⁻¹) * k * l⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem k.2) hal) k.2) (K.inv_mem hl)
    have h1 : α ⟨(k : G)⁻¹ * (a * l * a⁻¹) * k * l⁻¹, hx⟩ = 1 := by
      have e2 : (⟨(k : G)⁻¹ * (a * l * a⁻¹) * k * l⁻¹, hx⟩ : ↥K) =
          k⁻¹ * ⟨a * l * a⁻¹, hal⟩ * k * (⟨l, hl⟩ : ↥K)⁻¹ := rfl
      rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv, hk ⟨l, hl⟩ hal]
      group
    have h2 := (hαC _).mp h1
    have e3 : (k : G)⁻¹ * a * l * ((k : G)⁻¹ * a)⁻¹ * l⁻¹ =
        (k : G)⁻¹ * (a * l * a⁻¹) * k * l⁻¹ := by group
    rw [e3]
    exact h2
  intro w hw
  have hc := Subgroup.mem_centralizer_iff.mp (hDC hmem) w hw
  calc a * w * a⁻¹ = (k : G) * ((k : G)⁻¹ * a * w * a⁻¹ * k) * (k : G)⁻¹ := by group
    _ = (k : G) * w * (k : G)⁻¹ := by
      congr 2
      calc (k : G)⁻¹ * a * w * a⁻¹ * k = ((k : G)⁻¹ * a * w) * ((k : G)⁻¹ * a)⁻¹ := by group
        _ = (w * ((k : G)⁻¹ * a)) * ((k : G)⁻¹ * a)⁻¹ := by rw [hc]
        _ = w := by group

theorem exists_conj_of_mem_R_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLvK : S.Lv ≤ K)
    {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥K)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hG1 : ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α =
      flagStabilizer 4 (ZMod 2) {2}) {X R : Subgroup G}
    (hX1 : ∃ (x : G) (hx : x ∈ K), x ∈ X ∧ α ⟨x, hx⟩ = Ln2P.levi1)
    (hX3 : ∃ (x : G) (hx : x ∈ K), x ∈ X ∧ α ⟨x, hx⟩ = Ln2P.levi3)
    (hRT : R ≤ S.Tv) (hR2 : IsPGroup 2 R) (hXR : X ≤ Subgroup.normalizer (R : Set G)) {a : G}
    (ha : a ∈ R) : ∃ k ∈ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)),
      ∀ w ∈ S.WK K, a * w * a⁻¹ = k * w * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haT : a ∈ S.Tv := hRT ha
  obtain ⟨ψ, hψ⟩ := L3316.exists_inducedAut hαs hαk (hT haT)

  have hTK : a ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer haT, hT haT⟩
  have hU : ∀ u ∈ unitriangular 4 (ZMod 2), ψ u ∈ unitriangular 4 (ZMod 2) := by
    intro u hu
    rw [← hmapU] at hu ⊢
    obtain ⟨l, hl, rfl⟩ := hu
    rw [hψ]
    refine ⟨_, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp hTK l).mp (Subgroup.mem_subgroupOf.mp hl))

  have hcomm : ∀ (x : G) (hx : x ∈ K), x ∈ X →
      ∃ e : ℕ, (ψ (α ⟨x, hx⟩) * (α ⟨x, hx⟩)⁻¹) ^ 2 ^ e = 1 := by
    intro x hx hxX
    have haxK : a * x * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hT haT) x).mp hx
    have hcK : a * x * a⁻¹ * x⁻¹ ∈ K := K.mul_mem haxK (K.inv_mem hx)
    have hcR : a * x * a⁻¹ * x⁻¹ ∈ R := by
      have h1 : x * a⁻¹ * x⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hXR hxX) a⁻¹).mp (R.inv_mem ha)
      rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
      exact R.mul_mem ha h1
    obtain ⟨e, he⟩ := hR2 ⟨_, hcR⟩
    refine ⟨e, ?_⟩
    have he' : (⟨a * x * a⁻¹ * x⁻¹, hcK⟩ : ↥K) ^ 2 ^ e = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val he)
    have e2 : (⟨a * x * a⁻¹ * x⁻¹, hcK⟩ : ↥K) = ⟨a * x * a⁻¹, haxK⟩ * (⟨x, hx⟩ : ↥K)⁻¹ := rfl
    have h1 := congrArg α he'
    rw [map_pow, e2, map_mul, map_inv, ← hψ ⟨x, hx⟩, map_one] at h1
    exact h1
  obtain ⟨x₁, hx₁K, hx₁X, hx₁⟩ := hX1
  obtain ⟨x₃, hx₃K, hx₃X, hx₃⟩ := hX3
  rcases Ln2P.mulAut_cases (by norm_num) ψ hU with ⟨u, hu, hcu⟩ | ⟨u, hu, hgu⟩
  ·
    have hrad : u ∈ Ln2P.flagRadical 4 (ZMod 2) 2 := by
      by_contra hR
      rcases Ln2P.pow_twelve_inner hu hR with ⟨h12, h4⟩ | ⟨h12, h4⟩
      · obtain ⟨e, he⟩ := hcomm x₁ hx₁K hx₁X
        rw [hx₁, hcu] at he
        exact Ln2P.false_of_pow_twelve h12 h4 he
      · obtain ⟨e, he⟩ := hcomm x₃ hx₃K hx₃X
        rw [hx₃, hcu] at he
        exact Ln2P.false_of_pow_twelve h12 h4 he
    have huO := Ln2P.flagRadical_le_pCoreOf 4 hrad
    have huQ : u ∈ flagStabilizer 4 (ZMod 2) {2} :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ huO
    rw [← hG1] at huQ
    obtain ⟨k, hk, rfl⟩ := huQ
    have hkz : (k : G) ∈ Subgroup.centralizer ({S.z} : Set G) := (Subgroup.mem_subgroupOf.mp hk).2
    refine ⟨k, S.mem_pCoreOf_of_alpha_mem hαk hG1 hkz huO, ?_⟩
    refine S.conj_eq_of_inner_F4 h1222 h517 hF hKG hT hLvK hαs hαC haT fun l h => ?_
    have := hψ l
    rw [hcu] at this
    rw [← this]
  ·
    exfalso
    obtain ⟨e, he⟩ := hcomm x₁ hx₁K hx₁X
    rw [hx₁, hgu] at he
    obtain ⟨h12, h4⟩ := Ln2P.pow_twelve_graph hu
    exact Ln2P.false_of_pow_twelve h12 h4 he

theorem false_of_lambda2_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hH : S.Hyp1367)
    {K : Subgroup G} (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hLvK : S.Lv ≤ K) (hO3 : K = oPrimeResidualOf 3 (Subgroup.centralizer ({S.v12} : Set G)))
    {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)} (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥K)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hG1 : ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α =
      flagStabilizer 4 (ZMod 2) {2})
    (hG2 : ∀ B : Subgroup G, B ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)) →
      ¬ B ≤ Subgroup.centralizer (S.WK K : Set G) →
      (B ⊓ Subgroup.centralizer (S.WK K : Set G)).relIndex B <
        (S.WK K ⊓ Subgroup.centralizer (B : Set G)).relIndex (S.WK K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hH.hF
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := hYz.1
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set W := S.WK K with hW
  set X := oPrimeResidualOf 3 (Gv ⊓ Subgroup.centralizer ({S.z} : Set G)) with hX
  set R := pCoreOf 2 (X ⊔ S.Tv) with hR
  set P := pCoreOf 2 (S.HK K) with hP
  have hRed := S.isTwoReducedIn_WK_F4 h1222 h517 hF hKG hT
  have hHK := S.HK_eq_sup hLvK

  have hXK : X ≤ K := by
    rw [hX, hO3]
    exact Subgroup.closure_mono fun x hx => ⟨hx.1.1, hx.2⟩
  have hXTv : X ⊔ S.Tv ≤ S.HK K := by
    rw [hHK]
    exact sup_le_sup_right hXK _
  have hHKN : S.HK K ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

  have hTvsyl : IsSylowTwoOf S.Tv (X ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right
      (sup_le (hXK.trans hKG) S.Tv_le_Gv)
  have hRT : R ≤ S.Tv := pCoreOf_two_le_of_isSylowTwoOf hTvsyl
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

  have hPT : P ≤ S.Tv := pCoreOf_two_le_of_isSylowTwoOf (S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hKG)
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hPR : P ≤ R := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hPT.trans le_sup_right) (hXTv.trans hHKN) hP2
  have hWP : W ≤ P := A4.le_pCoreOf_of_isTwoReducedIn hRed

  have hX1 := S.exists_mem_X_of_alpha hKG hαk hG1 Ln2P.levi1_mem Ln2P.levi1_pow_three
  have hX3 := S.exists_mem_X_of_alpha hKG hαk hG1 Ln2P.levi3_mem Ln2P.levi3_pow_three
  have hX1' : ∃ (x : G) (hx : x ∈ K), x ∈ X ∧ α ⟨x, hx⟩ = Ln2P.levi1 := hX1
  have hX3' : ∃ (x : G) (hx : x ∈ K), x ∈ X ∧ α ⟨x, hx⟩ = Ln2P.levi3 := hX3
  have hconj := fun a (ha : a ∈ R) => S.exists_conj_of_mem_R_F4 h1222 h517 hF hKG hT hLvK hαs hαk
    hαC hmapU hG1 hX1' hX3' hRT hR2 hXR ha

  have hCP : S.HK K ⊓ Subgroup.centralizer (W : Set G) ≤ P := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · exact fun h hh => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hh, (hRed.2.1.trans (normalizer_le_normalizer_centralizer W)) hh⟩
    · have hT2 : IsPGroup 2 ↥S.Tv := (S.isSylowTwoOf_Tv_F4 h1222 h517).2.1
      obtain ⟨e, he⟩ := (IsPGroup.iff_card).mp hT2
      rintro ⟨c, hcH, hcW⟩
      rw [hHK] at hcH
      obtain ⟨k₀, hk₀, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hT).mp hcH
      obtain ⟨k', hk', hpow⟩ :=
        CFSG.LieType.Chevalley.exists_mul_pow_eq_mul_pow hk₀ (hT hs) (2 ^ e)
      have hs1 : s ^ 2 ^ e = 1 := by
        have h1 := orderOf_dvd_natCard (⟨s, hs⟩ : ↥S.Tv)
        rw [he, Subgroup.orderOf_mk] at h1
        exact orderOf_dvd_iff_pow_eq_one.mp h1
      rw [hs1, mul_one] at hpow
      have hk'W : k' ∈ Subgroup.centralizer (W : Set G) := by
        rw [← hpow]
        exact Subgroup.pow_mem _ hcW _
      have hk'1 := (hαC ⟨k', hk'⟩).mpr hk'W
      have hk'p : (⟨k', hk'⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
        rw [← hαk]
        exact hk'1
      obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hk'p⟩
      refine ⟨e + b, Subtype.ext ?_⟩
      have h3 : (k' : G) ^ 2 ^ b = 1 := by
        have := congrArg Subtype.val (congrArg Subtype.val hb)
        simpa using this
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_add, pow_mul, hpow, h3]

  have hJRP : thompsonJ R ≤ P := by
    refine GammaExtra.thompsonJ_le fun A hA => ?_
    have hAR : A ≤ R := hA.1
    have hAN : A ≤ Subgroup.normalizer (W : Set G) :=
      (hAR.trans (hRT.trans (S.Tv_le_HK K))).trans hRed.2.1
    have hoff := relIndex_le_of_isMaxElemAbelian (hWP.trans hPR) hRed.2.2.1 hA

    set B := Subgroup.closure {k : G | k ∈ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)) ∧
      ∃ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ = k * w * k⁻¹} with hB
    have hBle : B ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)) :=
      (Subgroup.closure_le _).mpr fun k hk => hk.1
    have hBK : B ≤ K := hBle.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
    have hBN : B ≤ Subgroup.normalizer (W : Set G) :=
      (hBK.trans (by rw [hHK]; exact le_sup_left)).trans hRed.2.1
    have hgen : ∀ a ∈ A, ∃ k ∈ B, ∀ w ∈ W, a * w * a⁻¹ = k * w * k⁻¹ := by
      intro a ha
      obtain ⟨k, hk, hkw⟩ := hconj a (hAR ha)
      exact ⟨k, Subgroup.subset_closure ⟨hk, a, ha, hkw⟩, hkw⟩

    have hCW : W ⊓ Subgroup.centralizer (B : Set G) = W ⊓ Subgroup.centralizer (A : Set G) := by
      ext w
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨hw, hwB⟩
        refine ⟨hw, fun a ha => ?_⟩
        obtain ⟨k, hk, hkw⟩ := hgen a ha
        have h1 := hwB k hk
        have h2 := hkw w hw
        calc a * w = a * w * a⁻¹ * a := by group
          _ = k * w * k⁻¹ * a := by rw [h2]
          _ = w * a := by rw [h1]; group
      · rintro ⟨hw, hwA⟩
        refine ⟨hw, fun k hk => ?_⟩
        have hk' : k ∈ Subgroup.centralizer ({w} : Set G) := by
          refine (Subgroup.closure_le _).mpr ?_ hk
          rintro k ⟨-, a, ha, hkw⟩
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          have h1 := hwA a ha
          have h2 := hkw w hw
          have h3 : k * w * k⁻¹ = w := by rw [← h2, h1]; group
          calc k * w = k * w * k⁻¹ * k := by group
            _ = w * k := by rw [h3]
        exact Subgroup.mem_centralizer_singleton_iff.mp hk'

    have hext : ∀ (g h : ↥(Subgroup.normalizer (W : Set G))),
        (∀ w ∈ W, (g : G) * w * (g : G)⁻¹ = (h : G) * w * (h : G)⁻¹) →
        conjAct W g = conjAct W h := fun g h hgh =>
      MulEquiv.ext fun w => Subtype.ext (by rw [A1b.conjAct_coe, A1b.conjAct_coe, hgh w w.2])
    have hAut : autOn A W = autOn B W := by
      apply le_antisymm
      · intro φ hφ
        obtain ⟨s, hsA, rfl⟩ := mem_autOn_iff.mp hφ
        obtain ⟨k, hkB, hkw⟩ := hgen s hsA
        exact mem_autOn_iff.mpr ⟨⟨k, hBN hkB⟩, hkB, (hext _ _ hkw).symm⟩
      · rw [autOn, Subgroup.map_le_iff_le_comap]
        intro x hx
        have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
        have hM : B ≤ ((autOn A W).comap (conjAct W)).map
            (Subgroup.normalizer (W : Set G)).subtype := by
          rw [hB, Subgroup.closure_le]
          rintro k ⟨hkO, a, ha, hkw⟩
          have hkN : k ∈ Subgroup.normalizer (W : Set G) :=
            hBN (Subgroup.subset_closure ⟨hkO, a, ha, hkw⟩)
          exact ⟨⟨k, hkN⟩, Subgroup.mem_comap.mpr
            (mem_autOn_iff.mpr ⟨⟨a, hAN ha⟩, ha, hext _ _ hkw⟩), rfl⟩
        obtain ⟨y, hy, hyx⟩ := hM hxB
        rw [show y = x from Subtype.ext hyx] at hy
        exact hy
    have hidx : (B ⊓ Subgroup.centralizer (W : Set G)).relIndex B =
        (A ⊓ Subgroup.centralizer (W : Set G)).relIndex A := by
      rw [← card_autOn_eq_relIndex hBN, ← card_autOn_eq_relIndex hAN, hAut]

    have hBW : B ≤ Subgroup.centralizer (W : Set G) := by
      by_contra hBW
      have h1 := hG2 B hBle hBW
      rw [hCW, hidx] at h1
      omega
    have hAW : A ≤ Subgroup.centralizer (W : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, hkB, hkw⟩ := hgen a ha
      have h1 := Subgroup.mem_centralizer_iff.mp (hBW hkB) w hw
      have h2 := hkw w hw
      have h3 : a * w * a⁻¹ = w := by rw [h2, ← h1]; group
      calc w * a = a * w * a⁻¹ * a := by rw [h3]
        _ = a * w := by group
    exact fun x hx => hCP ⟨(hAR.trans (hRT.trans (S.Tv_le_HK K))) hx, hAW hx⟩

  have hJ := GammaExtra.thompsonJ_eq_of_le hJRP hPR

  have hTJ : T ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
    intro t ht
    have htX : t ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_oPrimeResidualOf (S.T_le_normalizer_centralizer_V2 ht)
    have htTv : t ∈ Subgroup.normalizer (S.Tv : Set G) := S.T_le_normalizer_Tv ht
    have htXT : t ∈ Subgroup.normalizer ((X ⊔ S.Tv : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htX,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htTv]
    exact normalizer_le_normalizer_thompsonJ R
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ htXT)
  have hKJ : K ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
    rw [← hJ]
    exact fun k hk => normalizer_le_normalizer_thompsonJ P
      (hHKN (by rw [hHK]; exact Subgroup.mem_sup_left hk))
  have hJ2 : IsPGroup 2 ↥(thompsonJ R) := GammaExtra.isPGroup_thompsonJ hR2
  have hJle : thompsonJ R ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((GammaExtra.thompsonJ_le_self R).trans (hRT.trans (inf_le_left.trans le_sup_right)))
      (sup_le hKJ hTJ) hJ2
  rw [S.pCoreOf_sup_T_eq_bot_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hKG hYz.2.1 hT
    (S.not_le_centralizer_z_of_inYz hYz hT)] at hJle

  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian P
  have hWA := hA₀.2.2 W hWP hRed.2.2.1
  have hA₀J : A₀ ≤ thompsonJ R := hJ ▸ GammaExtra.le_thompsonJ hA₀
  have hA₀1 : A₀ = ⊥ := eq_bot_iff.mpr (hA₀J.trans hJle)
  rw [hA₀1, Subgroup.card_bot] at hWA
  have hz : S.z ∈ W := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hW1 : W = ⊥ := Subgroup.eq_bot_of_card_le W hWA
  rw [hW1, Subgroup.mem_bot] at hz
  exact S.z_ne_one hz

end Setting

theorem end1367L4_of_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hGA : GriessAllModelsStatement) (hO3 : O3Prime1367_F4)
    (hG : Graph1367Lambda2_F4) : End1367L4_F4 := by
  intro G _ _ T L V S hH K hK hYz hT hLvK ⟨e⟩ t ht Y hYK hTY hCY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : ↥(S.plus K) ≃* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    e.trans (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm
  have hq := S.kbar_isQuasisimple_of_sl_F4 h1222 h517 hH.hF h36 h37 h38 hK hYz hT (Or.inl rfl) e'
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  obtain ⟨α, hαs, hαk, hαC⟩ := S.exists_slHom_plus_F4 h1222 h517 hGA hH.hF hYz.1 hT hLv hq
    (by norm_num) (by norm_num) e'

  have hsylH : IsSylowTwoOf S.Tv (K ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right
      (sup_le hYz.1 S.Tv_le_Gv)
  have hSK : IsSylowTwoOf (S.Tv ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hT)
  obtain ⟨α₂, hα₂s, hα₂k, hmapU⟩ := Ln2.exists_unitriangular hSK (n := 4) (by norm_num) hαs hαk
  have hα₂C : ∀ k : ↥K, α₂ k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G) :=
    fun k => by rw [← MonoidHom.mem_ker, hα₂k, ← hαk, MonoidHom.mem_ker, hαC]

  obtain ⟨ψ, hψ⟩ := L3316.exists_inducedAut hα₂s hα₂k (hT ht)
  have hTK : t ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hT ht⟩
  have hU : ∀ u ∈ unitriangular 4 (ZMod 2), ψ u ∈ unitriangular 4 (ZMod 2) := by
    intro u hu
    rw [← hmapU] at hu ⊢
    obtain ⟨l, hl, rfl⟩ := hu
    rw [hψ]
    refine ⟨_, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp hTK l).mp (Subgroup.mem_subgroupOf.mp hl))
  rcases Ln2P.mulAut_cases (by norm_num) ψ hU with ⟨u, hu, hcu⟩ | ⟨u, hu, hgu⟩
  ·
    rw [← hmapU] at hu
    obtain ⟨y', hy', rfl⟩ := hu
    have hy'Y : (y' : G) ∈ Y := hTY (Subgroup.mem_subgroupOf.mp hy')
    refine L3316.mem_normalizer_of_map_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hyK : y ∈ K := hYK hy
    have htyK : t * y * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hT ht) y).mp hyK
    have hcK : ((y' : G) * y * (y' : G)⁻¹)⁻¹ * (t * y * t⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem (K.mul_mem (K.mul_mem y'.2 hyK) (K.inv_mem y'.2))) htyK
    have hc1 : α₂ ⟨_, hcK⟩ = 1 := by
      have e1 : (⟨((y' : G) * y * (y' : G)⁻¹)⁻¹ * (t * y * t⁻¹), hcK⟩ : ↥K) =
          (y' * ⟨y, hyK⟩ * y'⁻¹)⁻¹ * ⟨t * y * t⁻¹, htyK⟩ := rfl
      rw [e1, map_mul, map_inv, map_mul, map_mul, map_inv, ← hψ ⟨y, hyK⟩, hcu]
      group
    have hcY : ((y' : G) * y * (y' : G)⁻¹)⁻¹ * (t * y * t⁻¹) ∈ Y :=
      hCY ⟨hcK, (hα₂C _).mp hc1⟩
    show t * y * t⁻¹ ∈ Y
    have e2 : t * y * t⁻¹ = ((y' : G) * y * (y' : G)⁻¹) *
        (((y' : G) * y * (y' : G)⁻¹)⁻¹ * (t * y * t⁻¹)) := by group
    rw [e2]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy'Y hy) (Y.inv_mem hy'Y)) hcY
  ·
    exfalso
    have hgraph : ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
        α₂ ⟨t * l * t⁻¹, h⟩ = graphAut 4 (u * α₂ l * u⁻¹) := fun l h => by
      rw [← hgu, hψ]
    obtain ⟨hG1, hG2⟩ := hG G T L V S hH K hK hYz hT hLvK α₂ hα₂s hα₂C hmapU
      ⟨t, ht, u, hu, hgraph⟩
    exact S.false_of_lambda2_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hH hYz hT
      hLvK (hO3 G T L V S hH K hK hYz hT ⟨e⟩) hα₂s hα₂k hα₂C hmapU hG1 hG2

theorem lemma13623C_of_lambda2_F4
    (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4)
    (hres : Lem13622Case4Z0_F4) (hGA : GriessAllModelsStatement) (h620 : Lemma13620L45_F4)
    (hO3 : O3Prime1367_F4) (hG : Graph1367Lambda2_F4) : Lemma13623C_F4 :=
  lemma13623C_of_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h36 h37 h38 h39 h132 h134 hres hGA
    h620 (end1367L4_of_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h36 h37 h38 h39 hGA hO3 hG)

end CFSG.Quasithin.H13.A5
