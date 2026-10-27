module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.LieType.ChevTwo.OrthogonalBasic
public import CFSG.LieType.ChevTwo.OrthogonalAutEight
public import CFSG.LieType.ChevTwo.OrthogonalOddCent
import CFSG.LieType.BorelTits.Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.Quasithin.Background.B15P4LayerDict

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal congr_conj inner_map_congr)

namespace OrthAssembly

theorem mul_comm_of_card_le_two {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (hH : Nat.card H ≤ 2) {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) {h : G}
    (hh : h ∈ H) : g * h = h * g := by
  by_contra hne
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hne (by rw [mul_one, one_mul])
  have hc : g * h * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hg h).1 hh
  have hc1 : g * h * g⁻¹ ≠ 1 := by
    intro h'
    apply hh1
    have : g * h = g * 1 :=
      calc g * h = g * h * g⁻¹ * g := by group
        _ = g * 1 := by rw [h']; group
    exact mul_left_cancel this
  have hch : g * h * g⁻¹ ≠ h := by
    intro h'
    apply hne
    calc g * h = g * h * g⁻¹ * g := by group
      _ = h * g := by rw [h']
  let f : Fin 3 → H := ![1, ⟨h, hh⟩, ⟨g * h * g⁻¹, hc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem eq_of_mem_zpowers_of_mul_self {G : Type*} [Group G] {t g : G} (ht : t * t = 1)
    (hg : g ∈ Subgroup.zpowers t) (hg1 : g ≠ 1) : g = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exfalso
    apply hg1
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, ht2, one_zpow]
  · rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, ht2, one_zpow, mul_one, zpow_one]

theorem transvection_mul_self {ι : Type} [Fintype ι] [DecidableEq ι] {t : GL ι (ZMod 2)}
    (ht : IsTransvection t) : t * t = 1 := by
  obtain ⟨v, f, -, -, hfv, ht⟩ := ht
  have key : ∀ x, Matrix.mulVec ((t * t : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) x = x := by
    intro x
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ht, ht x, map_add, map_smul, hfv, smul_zero,
      add_zero, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, key x, Units.val_one, Matrix.one_mulVec]

section Rho

variable {X : Type} [Group X] (K : Subgroup X) [K.Normal]

abbrev rhoK : X →* MulAut ↥K := MulAut.conjNormal

theorem rhoK_injective (hC : Subgroup.centralizer (K : Set X) = ⊥) :
    Function.Injective (rhoK K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut ↥K => (φ ⟨k, hk⟩ : X)) hg
    simp only [rhoK, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * g = (g * k * g⁻¹) * g := by rw [h1]
      _ = g * k := by group
  rw [hC] at hg'
  exact Subgroup.mem_bot.1 hg'

theorem rhoK_coe (k : ↥K) : rhoK K (k : X) = MulAut.conj k := MulAut.conjNormal_val

theorem mem_of_rhoK_mem_inner (hC : Subgroup.centralizer (K : Set X) = ⊥) {g : X}
    (h : rhoK K g ∈ inner ↥K) : g ∈ K := by
  obtain ⟨k, hk⟩ := h
  have : rhoK K g = rhoK K (k : X) := by
    rw [← hk, rhoK_coe]
  exact (rhoK_injective K hC this) ▸ k.2

theorem inducedAutGroup_eq_map (W : Subgroup X) : inducedAutGroup W K = W.map (rhoK K) := by
  ext α
  simp only [inducedAutGroup, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, hw, MulEquiv.ext fun k => Subtype.ext ?_⟩
    simp [rhoK, MulAut.conjNormal_apply]
  · rintro ⟨w, hw, rfl⟩
    have hwN : w ∈ Subgroup.normalizer (K : Set X) := by
      rw [Subgroup.normalizer_eq_top]; trivial
    refine ⟨⟨w, hwN⟩, hw, MulEquiv.ext fun k => Subtype.ext ?_⟩
    simp [rhoK, MulAut.conjNormal_apply]

end Rho

theorem exists_gen {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hcent : Subgroup.centralizer (K : Set X) = ⊥) {p : ℕ}
    {D : Subgroup X} {Sd : X → Subgroup X} (hfam : SignalizerFamily p D Sd)
    (hSK : sigmaFam D Sd ⊓ K = ⊥) (hS : sigmaFam D Sd ≠ ⊥)
    (hcard : ∀ T : Subgroup (MulAut ↥K), IsPGroup 2 T → T ⊓ inner ↥K = ⊥ → Nat.card T ≤ 2) :
    ∃ s d₀ : X, sigmaFam D Sd = Subgroup.zpowers s ∧ s ≠ 1 ∧ s ^ 2 = 1 ∧ s ∉ K ∧ d₀ ∈ D ∧
      d₀ ≠ 1 ∧ s ∈ pCoreOf 2 (Subgroup.centralizer ({d₀} : Set X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρ := rhoK_injective K hcent
  have hSdS : ∀ d ∈ D, d ≠ 1 → Sd d ≤ sigmaFam D Sd := fun d hd hd1 =>
    le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hd1 le_rfl))
  have hW : ∀ W : Subgroup X, W ≤ sigmaFam D Sd → IsPGroup 2 W → Nat.card W ≤ 2 := by
    intro W hWS hW2
    have hTi : W.map (rhoK K) ⊓ inner ↥K = ⊥ := by
      rw [eq_bot_iff]
      intro α hα
      obtain ⟨hα1, hα2⟩ := Subgroup.mem_inf.1 hα
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hα1
      have hwK : w ∈ K := mem_of_rhoK_mem_inner K hcent hα2
      have hw1 : w ∈ sigmaFam D Sd ⊓ K := Subgroup.mem_inf.2 ⟨hWS hw, hwK⟩
      rw [hSK, Subgroup.mem_bot] at hw1
      rw [hw1, map_one]
      exact Subgroup.one_mem _
    have := hcard _ (hW2.map _) hTi
    rwa [Subgroup.card_map_of_injective hρ] at this
  have hA : ∀ d ∈ D, d ≠ 1 → ∀ e ∈ D, ∀ s ∈ Sd d, e * s = s * e := by
    intro d hd hd1 e he s hs
    have h2 : IsPGroup 2 (Sd d) :=
      (BorelTits.pCoreOf_isPGroup 2 _).to_le (hfam.le_pCore d hd hd1)
    exact mul_comm_of_card_le_two (hW _ (hSdS d hd hd1) h2) (hfam.inv_D d hd hd1 e he) hs
  have hB : ∀ d ∈ D, d ≠ 1 → Sd d ≤ pCoreOf 2 (Subgroup.centralizer (D : Set X)) := by
    intro d hd hd1
    have hNp : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ⊓
        Subgroup.centralizer (D : Set X)) :=
      (BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
    have hNle : pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ⊓
        Subgroup.centralizer (D : Set X) ≤ pCoreOf 2 (Subgroup.centralizer (D : Set X)) := by
      refine BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ hNp
      intro c hc
      have hcd : c ∈ Subgroup.centralizer ({d} : Set X) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd) hc
      have hcA := BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) hcd
      have hcC := Subgroup.le_normalizer (H := Subgroup.centralizer (D : Set X)) hc
      rw [Subgroup.mem_normalizer_iff] at hcA hcC ⊢
      intro h
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (hcA h) (hcC h)
    refine le_trans (fun s hs => ?_) hNle
    refine Subgroup.mem_inf.2 ⟨hfam.le_pCore d hd hd1 hs, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hA d hd hd1 e he s hs
  have hS2 : IsPGroup 2 (sigmaFam D Sd) := by
    refine (BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer (D : Set X))).to_le ?_
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hB d hd hd1
  have hScard : Nat.card (sigmaFam D Sd) ≤ 2 := hW _ le_rfl hS2
  obtain ⟨d₀, hd₀, hd₀1, hSd₀⟩ : ∃ d ∈ D, d ≠ 1 ∧ Sd d ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hS
    rw [eq_bot_iff]
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => (h d hd hd1).le
  obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSd₀
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hsS : s ∈ sigmaFam D Sd := hSdS d₀ hd₀ hd₀1 hs
  have hsK : s ∉ K := by
    intro h
    have : s ∈ sigmaFam D Sd ⊓ K := Subgroup.mem_inf.2 ⟨hsS, h⟩
    rw [hSK, Subgroup.mem_bot] at this
    exact hs1' this
  have hzS : Subgroup.zpowers s ≤ sigmaFam D Sd := Subgroup.zpowers_le.2 hsS
  have hord : orderOf s = 2 := by
    have h1 : orderOf s ≤ 2 := by
      rw [← Nat.card_zpowers]
      exact (Subgroup.card_le_of_le hzS).trans hScard
    have h2 : orderOf s ≠ 1 := fun h => hs1' (orderOf_eq_one_iff.1 h)
    have h3 : 0 < orderOf s := orderOf_pos s
    omega
  refine ⟨s, d₀, ?_, hs1', ?_, hsK, hd₀, hd₀1, hfam.le_pCore d₀ hd₀ hd₀1 hs⟩
  · symm
    apply Subgroup.eq_of_le_of_card_ge hzS
    rw [Nat.card_zpowers, hord]
    exact hScard
  · rw [← hord]
    exact pow_orderOf_eq_one s

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → ZMod 2) → ZMod 2}

theorem kappa_mem_of_le (hQ : GoodQ Q) {X' : Subgroup (MulAut ↥(StatedOmega Q))}
    (hX' : inner ↥(StatedOmega Q) ≤ X') {g₀ : isoGrp Q} (hg₀X : kappa Q g₀ ∈ X')
    (hg₀Ω : (g₀ : GL ι (ZMod 2)) ∉ StatedOmega Q) (c : isoGrp Q) : kappa Q c ∈ X' := by
  set P : Subgroup (GL ι (ZMod 2)) := (X'.comap (kappa Q)).map (isoGrp Q).subtype with hP
  have hΩP : StatedOmega Q ≤ P := by
    intro x hx
    exact ⟨⟨x, statedOmega_le_isoGrp Q hx⟩, hX' ((hQ.kappa_mem_inner_iff _).2 hx), rfl⟩
  have hg₀P : (g₀ : GL ι (ZMod 2)) ∈ P := ⟨g₀, hg₀X, rfl⟩
  have hOP : isoGrp Q ≤ P := by
    rw [← hQ.isoGrp_eq_sup g₀.2 hg₀Ω]
    exact sup_le hΩP (Subgroup.zpowers_le.2 hg₀P)
  obtain ⟨c', hc', hcc'⟩ := hOP c.2
  have : c' = c := Subtype.ext hcc'
  rw [← this]
  exact hc'

theorem core_induced (hQ : GoodQ Q) {ε : Bool} {n : ℕ}
    (hComm : ∀ (g : GL ι (ZMod 2)) (hg : g ∈ isoGrp Q), g ∉ StatedOmega Q →
      ∀ a : MulAut ↥(StatedOmega Q), a * kappa Q ⟨g, hg⟩ = kappa Q ⟨g, hg⟩ * a →
        InducedByIso Q a)
    (hL3 : OrthOddCentCoreStrong Q ε n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (X' : Subgroup (MulAut ↥(StatedOmega Q))) (hX' : inner ↥(StatedOmega Q) ≤ X')
    (a : MulAut ↥(StatedOmega Q)) (hap : a ^ p = 1) (ha1 : a ≠ 1)
    (g₀ : isoGrp Q) (hg₀X : kappa Q g₀ ∈ X') (hg₀i : kappa Q g₀ ∉ inner ↥(StatedOmega Q))
    (R : Subgroup (MulAut ↥(StatedOmega Q))) (hR2 : IsPGroup 2 R)
    (hRa : R ≤ Subgroup.centralizer ({a} : Set (MulAut ↥(StatedOmega Q))))
    (hRn : X' ⊓ Subgroup.centralizer ({a} : Set (MulAut ↥(StatedOmega Q))) ≤
      Subgroup.normalizer (R : Set (MulAut ↥(StatedOmega Q))))
    (hg₀R : kappa Q g₀ ∈ R) :
    IsTransvection (g₀ : GL ι (ZMod 2)) ∧ HasFixedPointFreeOrder ε n p := by
  have hκ := hQ.kappa_injective
  have hg₀Ω : (g₀ : GL ι (ZMod 2)) ∉ StatedOmega Q := fun h =>
    hg₀i ((hQ.kappa_mem_inner_iff g₀).2 h)
  have hag : a * kappa Q g₀ = kappa Q g₀ * a :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hRa hg₀R)).symm
  obtain ⟨d, rfl⟩ := (inducedByIso_iff_mem_range Q a).1 (hComm g₀ g₀.2 hg₀Ω a hag)
  have hdp : (d : GL ι (ZMod 2)) ^ p = 1 := by
    have : d ^ p = 1 := hκ (by rw [map_pow, hap, map_one])
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hd1 : (d : GL ι (ZMod 2)) ≠ 1 := by
    intro h
    apply ha1
    have : d = 1 := Subtype.ext h
    rw [this, map_one]
  have hκO := kappa_mem_of_le hQ hX' hg₀X hg₀Ω
  set N : Subgroup (GL ι (ZMod 2)) := (R.comap (kappa Q)).map (isoGrp Q).subtype with hN
  have hmemN : ∀ m : isoGrp Q, (m : GL ι (ZMod 2)) ∈ N ↔ kappa Q m ∈ R := by
    intro m
    constructor
    · rintro ⟨m', hm', hmm'⟩
      have : m' = m := Subtype.ext hmm'
      rw [← this]
      exact hm'
    · intro hm
      exact ⟨m, hm, rfl⟩
  have hNle : N ≤ isoGrp Q ⊓
      Subgroup.centralizer ({(d : GL ι (ZMod 2))} : Set (GL ι (ZMod 2))) := by
    rintro _ ⟨m, hm, rfl⟩
    refine Subgroup.mem_inf.2 ⟨m.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : kappa Q m * kappa Q d = kappa Q d * kappa Q m :=
      Subgroup.mem_centralizer_singleton_iff.1 (hRa hm)
    have h2 : m * d = d * m := hκ (by rw [map_mul, map_mul, h1])
    exact congrArg Subtype.val h2
  have hNn : (N.subgroupOf (isoGrp Q ⊓
      Subgroup.centralizer ({(d : GL ι (ZMod 2))} : Set (GL ι (ZMod 2))))).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxO : (x : GL ι (ZMod 2)) ∈ isoGrp Q := (Subgroup.mem_inf.1 x.2).1
    have hcO : (c : GL ι (ZMod 2)) ∈ isoGrp Q := (Subgroup.mem_inf.1 c.2).1
    have hcd : (c : GL ι (ZMod 2)) * d = d * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2
    have hx' : kappa Q ⟨x, hxO⟩ ∈ R := (hmemN ⟨x, hxO⟩).1 hx
    have hc'd : (⟨c, hcO⟩ : isoGrp Q) * d = d * ⟨c, hcO⟩ := Subtype.ext hcd
    have hc'C : kappa Q ⟨c, hcO⟩ ∈
        Subgroup.centralizer ({kappa Q d} : Set (MulAut ↥(StatedOmega Q))) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc'd]
    have hc'N := hRn (Subgroup.mem_inf.2 ⟨hκO ⟨c, hcO⟩, hc'C⟩)
    have h3 : kappa Q (⟨c, hcO⟩ * ⟨x, hxO⟩ * (⟨c, hcO⟩ : isoGrp Q)⁻¹) ∈ R := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hc'N _).1 hx'
    exact (hmemN _).2 h3
  have hN2 : IsPGroup 2 N := (hR2.comap_of_injective (kappa Q) hκ).map _
  have hg₀N : (g₀ : GL ι (ZMod 2)) ∈ N := (hmemN g₀).2 hg₀R
  have hg₀1 : (g₀ : GL ι (ZMod 2)) ≠ 1 := fun h => hg₀Ω (h ▸ (StatedOmega Q).one_mem)
  have hN1 : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hg₀N
    exact hg₀1 hg₀N
  obtain ⟨⟨t, -, htT, hNt⟩, hF⟩ :=
    hL3 p hp hp2 (d : GL ι (ZMod 2)) d.2 hd1 hdp N hNle hNn hN2 hN1
  refine ⟨?_, hF⟩
  have hg₀t : (g₀ : GL ι (ZMod 2)) ∈ Subgroup.zpowers t := hNt ▸ hg₀N
  rw [eq_of_mem_zpowers_of_mul_self (transvection_mul_self htT) hg₀t hg₀1]
  exact htT

theorem core (hQ : GoodQ Q) {ε : Bool} {n : ℕ}
    (hFix : ∀ r : MulAut ↥(StatedOmega Q), r ^ 2 = 1 →
      ∃ τ : MulAut ↥(StatedOmega Q), InducedByIso Q (τ * r * τ⁻¹))
    (hComm : ∀ (g : GL ι (ZMod 2)) (hg : g ∈ isoGrp Q), g ∉ StatedOmega Q →
      ∀ a : MulAut ↥(StatedOmega Q), a * kappa Q ⟨g, hg⟩ = kappa Q ⟨g, hg⟩ * a →
        InducedByIso Q a)
    (hL3 : OrthOddCentCoreStrong Q ε n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (X' : Subgroup (MulAut ↥(StatedOmega Q))) (hX' : inner ↥(StatedOmega Q) ≤ X')
    (a r : MulAut ↥(StatedOmega Q)) (hap : a ^ p = 1) (ha1 : a ≠ 1) (hrX : r ∈ X')
    (hr2 : r ^ 2 = 1) (hri : r ∉ inner ↥(StatedOmega Q))
    (R : Subgroup (MulAut ↥(StatedOmega Q))) (hR2 : IsPGroup 2 R)
    (hRa : R ≤ Subgroup.centralizer ({a} : Set (MulAut ↥(StatedOmega Q))))
    (hRn : X' ⊓ Subgroup.centralizer ({a} : Set (MulAut ↥(StatedOmega Q))) ≤
      Subgroup.normalizer (R : Set (MulAut ↥(StatedOmega Q))))
    (hrR : r ∈ R) :
    (∃ (τ : MulAut ↥(StatedOmega Q)) (g : GL ι (ZMod 2)) (hg : g ∈ isoGrp Q),
      IsTransvection g ∧ τ * r * τ⁻¹ = kappa Q ⟨g, hg⟩) ∧ HasFixedPointFreeOrder ε n p := by
  obtain ⟨τ, hτ⟩ := hFix r hr2
  obtain ⟨g₀, hg₀⟩ := (inducedByIso_iff_mem_range Q _).1 hτ
  set φ : MulAut ↥(StatedOmega Q) →* MulAut ↥(StatedOmega Q) := (MulAut.conj τ).toMonoidHom
    with hφ
  have hφapp : ∀ x, φ x = τ * x * τ⁻¹ := fun x => rfl
  have hφinj : Function.Injective φ := (MulAut.conj τ).injective
  have hX'' : inner ↥(StatedOmega Q) ≤ X'.map φ := by
    intro y hy
    refine ⟨τ⁻¹ * y * τ, hX' ?_, ?_⟩
    · have := (inner_normal _).conj_mem _ hy τ⁻¹
      rwa [inv_inv] at this
    · rw [hφapp]
      group
  have hap' : φ a ^ p = 1 := by rw [← map_pow, hap, map_one]
  have ha1' : φ a ≠ 1 := by
    intro h
    apply ha1
    apply hφinj
    rw [h, map_one]
  have hg₀X : kappa Q g₀ ∈ X'.map φ := by
    rw [hg₀]
    exact Subgroup.mem_map_of_mem φ hrX
  have hg₀i : kappa Q g₀ ∉ inner ↥(StatedOmega Q) := by
    rw [hg₀]
    intro h
    apply hri
    have := (inner_normal _).conj_mem _ h τ⁻¹
    rwa [inv_inv, show τ⁻¹ * (τ * r * τ⁻¹) * τ = r by group] at this
  have hRa' : R.map φ ≤ Subgroup.centralizer ({φ a} : Set (MulAut ↥(StatedOmega Q))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (hRa hx)]
  have hRn' : X'.map φ ⊓ Subgroup.centralizer ({φ a} : Set (MulAut ↥(StatedOmega Q))) ≤
      Subgroup.normalizer ((R.map φ : Subgroup _) : Set (MulAut ↥(StatedOmega Q))) := by
    intro c hc
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hc1
    have : c' * a = a * c' := hφinj (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hc2)
    have hc'N := hRn (Subgroup.mem_inf.2 ⟨hc', Subgroup.mem_centralizer_singleton_iff.2 this⟩)
    exact Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hc'N)
  have hg₀R : kappa Q g₀ ∈ R.map φ := by
    rw [hg₀]
    exact Subgroup.mem_map_of_mem φ hrR
  obtain ⟨hT, hF⟩ := core_induced hQ hComm hL3 hp hp2 (X'.map φ) hX'' (φ a) hap' ha1' g₀ hg₀X
    hg₀i (R.map φ) (hR2.map φ) hRa' hRn' hg₀R
  exact ⟨⟨τ, g₀, g₀.2, hT, hg₀.symm⟩, hF⟩

theorem assembly_of_iso (hQ : GoodQ Q) {ε : Bool} {n : ℕ}
    (hFix : ∀ r : MulAut ↥(StatedOmega Q), r ^ 2 = 1 →
      ∃ τ : MulAut ↥(StatedOmega Q), InducedByIso Q (τ * r * τ⁻¹))
    (hComm : ∀ (g : GL ι (ZMod 2)) (hg : g ∈ isoGrp Q), g ∉ StatedOmega Q →
      ∀ a : MulAut ↥(StatedOmega Q), a * kappa Q ⟨g, hg⟩ = kappa Q ⟨g, hg⟩ * a →
        InducedByIso Q a)
    (hL3 : OrthOddCentCoreStrong Q ε n)
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hcent : Subgroup.centralizer (K : Set X) = ⊥) (e₀ : ↥K ≃* ↥(StatedOmega Q))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (S : Subgroup X) (s d₀ : X)
    (hS : S = Subgroup.zpowers s) (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) (hsK : s ∉ K)
    (hd₀1 : d₀ ≠ 1) (hd₀p : d₀ ^ p = 1)
    (hsP : s ∈ pCoreOf 2 (Subgroup.centralizer ({d₀} : Set X))) :
    (∃ e : ↥K ≃* ↥(StatedOmega Q), Nat.card (inducedAutGroup S K) = 2 ∧
      ActsLikeTransvection Q S K e) ∧ HasFixedPointFreeOrder ε n p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ : X →* MulAut ↥(StatedOmega Q) := (MulAut.congr e₀).toMonoidHom.comp (rhoK K) with hθ
  have hθinj : Function.Injective θ :=
    (MulAut.congr e₀).injective.comp (rhoK_injective K hcent)
  have hθK : ∀ k : ↥K, θ k = MulAut.conj (e₀ k) := by
    intro k
    rw [hθ, MonoidHom.comp_apply, rhoK_coe]
    exact congr_conj e₀ k
  set C := Subgroup.centralizer ({d₀} : Set X) with hC
  set R : Subgroup (MulAut ↥(StatedOmega Q)) := (pCoreOf 2 C).map θ with hR
  have hX' : inner ↥(StatedOmega Q) ≤ θ.range := by
    rintro _ ⟨y, rfl⟩
    refine ⟨(e₀.symm y : X), ?_⟩
    rw [hθK, MulEquiv.apply_symm_apply]
  have hri : θ s ∉ inner ↥(StatedOmega Q) := by
    intro h
    rw [← inner_map_congr e₀] at h
    have h' : rhoK K s ∈ inner ↥K :=
      (Subgroup.mem_map_iff_mem (MulAut.congr e₀).injective).1 h
    exact hsK (mem_of_rhoK_mem_inner K hcent h')
  have hRa : R ≤ Subgroup.centralizer ({θ d₀} : Set (MulAut ↥(StatedOmega Q))) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (BorelTits.pCoreOf_le 2 C hx)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, this]
  have hRn : θ.range ⊓ Subgroup.centralizer ({θ d₀} : Set (MulAut ↥(StatedOmega Q))) ≤
      Subgroup.normalizer (R : Set (MulAut ↥(StatedOmega Q))) := by
    intro c hc
    obtain ⟨⟨x, rfl⟩, hc2⟩ := Subgroup.mem_inf.1 hc
    have hxd : x * d₀ = d₀ * x := hθinj (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hc2)
    have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hxd
    exact Subgroup.le_normalizer_map θ
      (Subgroup.mem_map_of_mem θ (BorelTits.le_normalizer_pCoreOf 2 C hxC))
  obtain ⟨⟨τ, g, hg, hgT, hτ⟩, hF⟩ := core hQ hFix hComm hL3 hp hp2 θ.range hX' (θ d₀) (θ s)
    (by rw [← map_pow, hd₀p, map_one]) (fun h => hd₀1 (hθinj (h.trans (map_one θ).symm)))
    (MonoidHom.mem_range.2 ⟨s, rfl⟩) (by rw [← map_pow, hs2, map_one]) hri R
    ((BorelTits.pCoreOf_isPGroup 2 C).map θ) hRa hRn (Subgroup.mem_map_of_mem θ hsP)
  refine ⟨⟨e₀.trans τ, ?_, g, isoGrp_le_normalizer Q hg, hg, hgT, ?_⟩, hF⟩
  · rw [inducedAutGroup_eq_map, Subgroup.card_map_of_injective (rhoK_injective K hcent), hS,
      Nat.card_zpowers]
    exact orderOf_eq_prime hs2 hs1
  · unfold ActsLike
    have h1 : ((MulAut.congr (e₀.trans τ)).toMonoidHom.comp (rhoK K)) s = τ * θ s * τ⁻¹ := by
      refine MulEquiv.ext fun x => ?_
      simp [hθ, MulAut.congr_apply]
    have h2 : kappa Q ⟨g, hg⟩ =
        (StatedOmega Q).normalizerMonoidHom ⟨g, isoGrp_le_normalizer Q hg⟩ :=
      MulEquiv.ext fun x => Subtype.ext (by
        rw [kappa_apply_val, Subgroup.normalizerMonoidHom_apply_apply_coe])
    rw [inducedAutGroup_eq_map, hS, Subgroup.map_map, MonoidHom.map_zpowers, h1, hτ, h2]

end Core

section Induced

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → ZMod 2) → ZMod 2}

theorem fix_of_induced (h : OmegaTwoAutInduced Q) :
    ∀ r : MulAut ↥(StatedOmega Q), r ^ 2 = 1 →
      ∃ τ : MulAut ↥(StatedOmega Q), InducedByIso Q (τ * r * τ⁻¹) :=
  fun _ _ => ⟨1, h _⟩

theorem comm_of_induced (h : OmegaTwoAutInduced Q) :
    ∀ (g : GL ι (ZMod 2)) (hg : g ∈ isoGrp Q), g ∉ StatedOmega Q →
      ∀ a : MulAut ↥(StatedOmega Q), a * kappa Q ⟨g, hg⟩ = kappa Q ⟨g, hg⟩ * a →
        InducedByIso Q a :=
  fun _ _ _ a _ => h a

end Induced

end OrthAssembly

theorem input19_20_3_assembly
    (h1 : OmegaTwoAutTwoPart)
    (h2 : (∀ n : ℕ, 1 ≤ n → OmegaTwoAutInduced (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ∧
      (∀ n : ℕ, 2 ≤ n → n ≠ 3 → OmegaTwoAutInduced (StatedQuadPlus (n + 1) (ZMod 2))))
    (h2' : OmegaPlusEightInvolutions) :
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) [K.Normal], IsSimpleGroup ↥K →
      Subgroup.centralizer (K : Set X) = ⊥ → ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∀ (D : Subgroup X) (Sd : X → Subgroup X), SignalizerFamily p D Sd →
          sigmaFam D Sd ⊓ K = ⊥ → ∀ (n : ℕ) (ε : Bool), 1 ≤ n → IsOmegaTwo ε (n + 1) ↥K →
            sigmaFam D Sd ≠ ⊥ →
              ActsAsTransvectionAt ε n (sigmaFam D Sd) K ∧ HasFixedPointFreeOrder ε n p := by
  intro X _ _ K _ hs hcent p hp hp2 D Sd hfam hSK n ε hn hK hS
  obtain ⟨s, d₀, hSs, hs1, hs2, hsK, hd₀, hd₀1, hsP⟩ :=
    OrthAssembly.exists_gen K hcent hfam hSK hS (h1 ε n hn ↥K hs hK)
  have hd₀p : d₀ ^ p = 1 := hfam.elemAbelian.2 d₀ hd₀
  cases ε with
  | false =>
    obtain ⟨e₀⟩ := hK
    exact OrthAssembly.assembly_of_iso (goodQ_minus hn)
      (OrthAssembly.fix_of_induced (h2.1 n hn)) (OrthAssembly.comm_of_induced (h2.1 n hn))
      (orthOddCentCoreStrong n hn).2 K hcent e₀ hp hp2 _ s d₀ hSs hs1 hs2 hsK hd₀1 hd₀p hsP
  | true =>
    obtain ⟨e₀⟩ := hK
    rcases (show n = 1 ∨ n = 3 ∨ (2 ≤ n ∧ n ≠ 3) by omega) with rfl | rfl | ⟨hn2, hn3⟩
    · haveI := hs
      exact absurd e₀.symm.isSimpleGroup not_isSimpleGroup_statedOmega_plus_two
    · exact OrthAssembly.assembly_of_iso (goodQ_plus (by norm_num)) h2'
        (fun g hg hgΩ a ha => commute_plusEight hg hgΩ a ha)
        (orthOddCentCoreStrong 3 (by norm_num)).1 K hcent e₀ hp hp2 _ s d₀ hSs hs1 hs2 hsK
        hd₀1 hd₀p hsP
    · exact OrthAssembly.assembly_of_iso (goodQ_plus hn2)
        (OrthAssembly.fix_of_induced (h2.2 n hn2 hn3))
        (OrthAssembly.comm_of_induced (h2.2 n hn2 hn3))
        (orthOddCentCoreStrong n hn).1 K hcent e₀ hp hp2 _ s d₀ hSs hs1 hs2 hsK hd₀1 hd₀p hsP

end CFSG.LieType.ChevTwo
