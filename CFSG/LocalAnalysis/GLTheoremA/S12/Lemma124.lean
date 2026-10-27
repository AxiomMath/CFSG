module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma124B
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75Z1
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma124A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

abbrev Xc (p : ℕ) (M : Subgroup G) : Subgroup G := ⁅M, GLAPPrimeCoreOf p M⁆

theorem hyperplane_cases (h : Cfg12 G m p B x L D K) {B' : Subgroup G}
    (hB' : B' ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p D) :
    B' = Subgroup.zpowers x ∨ ∃ y ∈ D, y ∉ Subgroup.zpowers x ∧ B' = Subgroup.zpowers y := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card B' = p := by
    have h1 := hB'.2
    rw [h.card_D, sq] at h1
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h1).symm
  obtain ⟨a, haD, ha1, hae⟩ := CFSG.SignalizerFunctorTheorem.McBride.exists_zpowers_eq_of_mem_signalizerFunctorEk_one hp
    (A := D) (⟨hB'.1, by rw [hcard, pow_one]⟩ : B' ∈ CFSG.Open.signalizerFunctorEk p 1 D)
  by_cases hax : a ∈ Subgroup.zpowers x
  · left
    rw [← hae]
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hax) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (h.elem.2 a haD) ha1,
      orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one]
  · exact Or.inr ⟨a, haD, hax, hae.symm⟩

theorem hyper_data (h : Cfg12 G m p B x L D K) {y : G} (hy : y ∈ D) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTD : D ≤ Subgroup.normalizer (T : Set G)) :
    IsPGroup 2 (⁅T ⊓ Subgroup.centralizer ({y} : Set G), Subgroup.zpowers x⁆ : Subgroup G) ∧
      (⁅T ⊓ Subgroup.centralizer ({y} : Set G), Subgroup.zpowers x⁆ : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) ∧
      D ≤ Subgroup.normalizer
        ((⁅T ⊓ Subgroup.centralizer ({y} : Set G), Subgroup.zpowers x⁆ : Subgroup G) : Set G) ∧
      (⁅T ⊓ Subgroup.centralizer ({y} : Set G), Subgroup.zpowers x⁆ : Subgroup G) =
        ⁅(⁅T ⊓ Subgroup.centralizer ({y} : Set G), Subgroup.zpowers x⁆ : Subgroup G), Subgroup.zpowers x⁆ := by
  have hDy : D ≤ Subgroup.normalizer ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) :=
    (isElemAbelian_le_centralizer h.elem hy).trans Subgroup.le_normalizer
  have hDT₁ : D ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hTD hDy
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (hDT₁ h.xD)
  have hT₁2 : IsPGroup 2 (T ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := hT2.to_le inf_le_left
  have hle : (⁅T ⊓ Subgroup.centralizer ({y} : Set G), Subgroup.zpowers x⁆ : Subgroup G) ≤
      T ⊓ Subgroup.centralizer ({y} : Set G) := commutator_le_left_of_normalizes hxN
  have hDx : D ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := fun d hd => by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [S3.centralizer_zpowers x]
    exact Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.elem hd h.xD)
  refine ⟨hT₁2.to_le hle, hle.trans inf_le_right, le_normalizer_commutator hDT₁ hDx, ?_⟩
  exact (commutator_commutator_eq_of_isPGroup h.prime (isPGroup_zpowers_of_mem h.elem h.xD) hT₁2 h.odd hxN).symm

theorem T_normalizes {y : G} {T : Subgroup G} (hTy : T ≤ Subgroup.centralizer ({y} : Set G)) (hxy : x ∈ Subgroup.centralizer ({y} : Set G))
    (hx : ∀ M : Subgroup G, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M → x ∈ Subgroup.normalizer (M : Set G))
    (hTx : T = ⁅T, Subgroup.zpowers x⁆) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) : T ≤ Subgroup.normalizer (M : Set G) := by
  have hcomm : ∀ w ∈ Subgroup.centralizer ({y} : Set G), ∀ b ∈ Subgroup.zpowers x, ∀ J : Subgroup G,
      GLAPComponent p (Subgroup.centralizer ({y} : Set G)) J → w * b * w⁻¹ * b⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
    intro w hw b hb J hJ
    have hJ₁ : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) (GLBConj w J) := by
      have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ w
      rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hw)] at this
    have hbJ : b ∈ Subgroup.normalizer (J : Set G) := (Subgroup.zpowers_le.2 (hx J hJ)) hb
    have hbJ₁ : b ∈ Subgroup.normalizer ((GLBConj w J : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.2 (hx _ hJ₁)) hb
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have h1 : b⁻¹ * z * b ∈ J := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hbJ) z).1 hz
      simpa using this
    have h2 : w⁻¹ * (b⁻¹ * z * b) * w ∈ GLBConj w J := by
      rw [mem_gLBConj]
      have : w * (w⁻¹ * (b⁻¹ * z * b) * w) * w⁻¹ = b⁻¹ * z * b := by group
      rw [this]
      exact h1
    have h3 : b * (w⁻¹ * (b⁻¹ * z * b) * w) * b⁻¹ ∈ GLBConj w J :=
      (Subgroup.mem_normalizer_iff.1 hbJ₁ _).1 h2
    have h4 : w * (b * (w⁻¹ * (b⁻¹ * z * b) * w) * b⁻¹) * w⁻¹ ∈ J := mem_gLBConj.1 h3
    have : w * b * w⁻¹ * b⁻¹ * z * (w * b * w⁻¹ * b⁻¹)⁻¹ =
        w * (b * (w⁻¹ * (b⁻¹ * z * b) * w) * b⁻¹) * w⁻¹ := by group
    rw [this]
    exact h4
  rw [hTx, Subgroup.commutator_le]
  intro t ht g hg
  rw [commutatorElement_def]
  exact hcomm t (hTy ht) g hg M hM

theorem cover_X {X' M A : Subgroup G} (hM : GLAPComponent p X' M) (hAM : A ≤ M)
    (hcov : M = A ⊔ GLAPPrimeCoreOf p M) : A ⊔ Xc p M = M := by
  have hOM : GLAPPrimeCoreOf p M ≤ M := Subgroup.map_subtype_le _
  have hJO : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p M)
  have hJX : M ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer hJO
  refine le_antisymm (sup_le hAM ((comm_primeCore_le_core M).trans hOM)) ?_
  exact L62.le_sup_of_perfect_cover (glaPComponent_perfect hM) hAM hcov.symm hOM hJO hJX le_rfl

theorem comm_le_of_cover {K M X V : Subgroup G} (hKX : K ⊔ X = M) (hKN : K ≤ Subgroup.normalizer (X : Set G))
    (hVN : V ≤ Subgroup.normalizer (X : Set G)) (hKV : ∀ k ∈ K, ∀ y ∈ V, k * y = y * k) :
    (⁅M, V⁆ : Subgroup G) ≤ X := by
  rw [Subgroup.commutator_le]
  intro m hm y hy
  have hm' : m ∈ (K ⊔ X : Subgroup G) := by rw [hKX]; exact hm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K X hKN] at hm'
  obtain ⟨k, hk, u, hu, rfl⟩ := Set.mem_mul.mp hm'
  have hky : k * y = y * k := hKV k hk y hy
  have hkk : k⁻¹ * y⁻¹ = y⁻¹ * k⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hky]
  have e : ⁅k * u, y⁆ = k * ⁅u, y⁆ * k⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    rw [hkk]
  rw [e]
  have hu' : ⁅u, y⁆ ∈ X := by
    have h1 : y * u⁻¹ * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hVN hy) u⁻¹).1 (inv_mem hu)
    have : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem hu h1
  exact (Subgroup.mem_normalizer_iff.1 (hKN hk) _).1 hu'

theorem comm_M_T {M T : Subgroup G} (hKx : K ≤ Subgroup.centralizer ({x} : Set G)) (hKX : K ⊔ Xc p M = M)
    (hxM : x ∈ Subgroup.normalizer (M : Set G)) (hTM : T ≤ Subgroup.normalizer (M : Set G))
    (hTx : T = ⁅T, Subgroup.zpowers x⁆) : (⁅M, T⁆ : Subgroup G) ≤ Xc p M := by
  have hNO : Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p M
  have hMO : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) := Subgroup.le_normalizer.trans hNO
  have hMX : M ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer hMO
  have hTX : T ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator hTM (hTM.trans hNO)
  have hVM : Subgroup.zpowers x ≤ Subgroup.normalizer (M : Set G) := Subgroup.zpowers_le.2 hxM
  have hVX : Subgroup.zpowers x ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator hVM (hVM.trans hNO)
  have hKM : K ≤ M := le_sup_left.trans hKX.le
  have hKN : K ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) := hKM.trans hMX
  have hMV : (⁅M, Subgroup.zpowers x⁆ : Subgroup G) ≤ Xc p M := by
    refine comm_le_of_cover hKX hKN hVX fun k hk y hy => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hkx : k * x = x * k := Subgroup.mem_centralizer_singleton_iff.1 (hKx hk)
    exact (Commute.zpow_right (show Commute k x from hkx) j).eq
  have h1 : (⁅(⁅Subgroup.zpowers x, M⁆ : Subgroup G), T⁆ : Subgroup G) ≤ Xc p M := by
    rw [Subgroup.commutator_comm (Subgroup.zpowers x) M]
    exact (Subgroup.commutator_mono hMV le_rfl).trans
      (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ T hTX)
  have h2 : (⁅(⁅M, T⁆ : Subgroup G), Subgroup.zpowers x⁆ : Subgroup G) ≤ Xc p M :=
    (Subgroup.commutator_mono (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing M T hTM) le_rfl).trans hMV
  have h3 := three_subgroups_mod hVX hMX hTX h1 h2
  rw [← hTx] at h3
  rwa [Subgroup.commutator_comm]

theorem cover_cs {M T : Subgroup G} (hT2 : IsPGroup 2 T) (hp : p.Prime) (hDp : IsElemAbelian p D)
    (hTD : D ≤ Subgroup.normalizer (T : Set G)) (hKD : K ≤ Subgroup.centralizer (D : Set G))
    (hKX : K ⊔ Xc p M = M) (hTM : T ≤ Subgroup.normalizer (M : Set G)) (hDM : D ≤ Subgroup.normalizer (M : Set G))
    (hodd : Odd (Nat.card ↥(Xc p M))) (hMT : (⁅M, T⁆ : Subgroup G) ≤ Xc p M) :
    M = (M ⊓ Subgroup.centralizer ((T ⊔ D : Subgroup G) : Set G)) ⊔ Xc p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNO : Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p M
  have hMX : M ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer (Subgroup.le_normalizer.trans hNO)
  have hTX : T ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator hTM (hTM.trans hNO)
  have hDX : D ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator hDM (hDM.trans hNO)
  have hKM : K ≤ M := le_sup_left.trans hKX.le
  have hKN : K ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) := hKM.trans hMX
  have hXO : Xc p M ≤ GLAPPrimeCoreOf p M := comm_primeCore_le_core M
  have hXM : Xc p M ≤ M := hXO.trans (Subgroup.map_subtype_le _)
  have hMD : (⁅M, D⁆ : Subgroup G) ≤ Xc p M :=
    comm_le_of_cover hKX hKN hDX fun k hk d hd => (Subgroup.mem_centralizer_iff.1 (hKD hk) d hd).symm
  have hX2 : ¬ 2 ∣ Nat.card ↥(Xc p M) := by
    have := Nat.odd_iff.1 hodd
    omega
  have hXp : ¬ p ∣ Nat.card ↥(Xc p M) := fun h =>
    not_dvd_card_glaPPrimeCoreOf hp M (h.trans (Subgroup.card_dvd_of_le hXO))
  refine le_antisymm ?_ (sup_le inf_le_left hXM)
  intro g hg
  have hgT : ∀ a ∈ T, a * g * a⁻¹ * g⁻¹ ∈ Xc p M := fun a ha => by
    have h1 : ⁅a, g⁆ ∈ (⁅T, M⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ha hg
    rw [Subgroup.commutator_comm] at h1
    exact hMT h1
  have hgD : ∀ a ∈ D, a * g * a⁻¹ * g⁻¹ ∈ Xc p M := fun a ha => by
    have h1 : ⁅a, g⁆ ∈ (⁅D, M⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ha hg
    rw [Subgroup.commutator_comm] at h1
    exact hMD h1
  let αT : ↥T →* MulAut G := MulAut.conj.comp T.subtype
  obtain ⟨c₀, hc₀X, hc₀T⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hT2 αT (Xc p M) hX2 g).1
    (by
      intro a x hx
      show (a : G) * x * (a : G)⁻¹ * g⁻¹ ∈ Xc p M
      have h1 : (a : G) * (x * g⁻¹) * (a : G)⁻¹ ∈ Xc p M := (Subgroup.mem_normalizer_iff.1 (hTX a.2) _).1 hx
      have h2 : (a : G) * x * (a : G)⁻¹ * g⁻¹ =
          ((a : G) * (x * g⁻¹) * (a : G)⁻¹) * ((a : G) * g * (a : G)⁻¹ * g⁻¹) := by group
      rw [h2]
      exact mul_mem h1 (hgT a a.2))
  have hc₀T' : ∀ a ∈ T, a * c₀ * a⁻¹ = c₀ := fun a ha => hc₀T ⟨a, ha⟩
  set F : Set G := {c | c * g⁻¹ ∈ Xc p M ∧ ∀ a ∈ T, a * c * a⁻¹ = c} with hF
  let αD : ↥D →* MulAut G := MulAut.conj.comp D.subtype
  have hFinv : ∀ d : ↥D, ∀ c ∈ F, αD d c ∈ F := by
    rintro d c ⟨hcX, hcT⟩
    refine ⟨?_, ?_⟩
    · show (d : G) * c * (d : G)⁻¹ * g⁻¹ ∈ Xc p M
      have h1 : (d : G) * (c * g⁻¹) * (d : G)⁻¹ ∈ Xc p M := (Subgroup.mem_normalizer_iff.1 (hDX d.2) _).1 hcX
      have h2 : (d : G) * c * (d : G)⁻¹ * g⁻¹ =
          ((d : G) * (c * g⁻¹) * (d : G)⁻¹) * ((d : G) * g * (d : G)⁻¹ * g⁻¹) := by group
      rw [h2]
      exact mul_mem h1 (hgD d d.2)
    · intro a ha
      have ha' : (d : G)⁻¹ * a * (d : G)⁻¹⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.1 (hTD (inv_mem d.2)) a).1 ha
      have h3 := hcT _ ha'
      show a * ((d : G) * c * (d : G)⁻¹) * a⁻¹ = (d : G) * c * (d : G)⁻¹
      calc a * ((d : G) * c * (d : G)⁻¹) * a⁻¹
          = (d : G) * (((d : G)⁻¹ * a * (d : G)⁻¹⁻¹) * c * ((d : G)⁻¹ * a * (d : G)⁻¹⁻¹)⁻¹) * (d : G)⁻¹ := by group
        _ = (d : G) * c * (d : G)⁻¹ := by rw [h3]
  have mem1 : ∀ c ∈ F, c * c₀⁻¹ ∈ Xc p M ⊓ Subgroup.centralizer (T : Set G) := by
    rintro c ⟨hcX, hcT⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have : c * c₀⁻¹ = (c * g⁻¹) * (c₀ * g⁻¹)⁻¹ := by group
      rw [this]
      exact mul_mem hcX (inv_mem hc₀X)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := hcT a ha
      have h2' : a * c₀⁻¹ * a⁻¹ = c₀⁻¹ := by
        calc a * c₀⁻¹ * a⁻¹ = (a * c₀ * a⁻¹)⁻¹ := by group
          _ = c₀⁻¹ := by rw [hc₀T' a ha]
      calc a * (c * c₀⁻¹) = (a * c * a⁻¹) * (a * c₀⁻¹ * a⁻¹) * a := by group
        _ = c * c₀⁻¹ * a := by rw [h1, h2']
  have mem2 : ∀ u ∈ Xc p M ⊓ Subgroup.centralizer (T : Set G), u * c₀ ∈ F := by
    intro u hu
    obtain ⟨huX, huT⟩ := Subgroup.mem_inf.1 hu
    refine ⟨?_, ?_⟩
    · have : u * c₀ * g⁻¹ = u * (c₀ * g⁻¹) := by group
      rw [this]
      exact mul_mem huX hc₀X
    · intro a ha
      have h1 : a * u = u * a := Subgroup.mem_centralizer_iff.1 huT a ha
      have h2 := hc₀T' a ha
      calc a * (u * c₀) * a⁻¹ = (a * u * a⁻¹) * (a * c₀ * a⁻¹) := by group
        _ = u * c₀ := by rw [h2, h1]; group
  have hFcard : ¬ p ∣ Nat.card F := by
    let e : F ≃ ↥(Xc p M ⊓ Subgroup.centralizer (T : Set G)) :=
      { toFun := fun c => ⟨c.1 * c₀⁻¹, mem1 c.1 c.2⟩
        invFun := fun u => ⟨u.1 * c₀, mem2 u.1 u.2⟩
        left_inv := fun c => Subtype.ext (by simp)
        right_inv := fun u => Subtype.ext (by simp) }
    rw [Nat.card_congr e]
    exact fun h => hXp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨c, hcF, hcD⟩ := CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant p
    (isPGroup_of_isElemAbelian hDp) αD F hFinv hFcard
  obtain ⟨hcX, hcT⟩ := hcF
  have hcD' : ∀ d ∈ D, d * c * d⁻¹ = c := fun d hd => hcD ⟨d, hd⟩
  have hcC : c ∈ Subgroup.centralizer ((T ⊔ D : Subgroup G) : Set G) := by
    have hle : (T ⊔ D : Subgroup G) ≤ Subgroup.centralizer ({c} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun d hd => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc a * c = (a * c * a⁻¹) * a := by group
          _ = c * a := by rw [hcT a ha]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc d * c = (d * c * d⁻¹) * d := by group
          _ = c * d := by rw [hcD' d hd]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have hcM : c ∈ M := by
    have : c = (c * g⁻¹) * g := by group
    rw [this]
    exact mul_mem (hXM hcX) hg
  have hgcX : g * c⁻¹ ∈ Xc p M := by
    have : g * c⁻¹ = (c * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hcX
  have key : g * c⁻¹ * c ∈ (Xc p M ⊔ (M ⊓ Subgroup.centralizer ((T ⊔ D : Subgroup G) : Set G)) : Subgroup G) :=
    Subgroup.mul_mem_sup hgcX ⟨hcM, hcC⟩
  rw [inv_mul_cancel_right, sup_comm] at key
  exact key

theorem F_cover (hp : p.Prime) {X' M A : Subgroup G} (hM : GLAPComponent p X' M)
    (hcs : M = (M ⊓ Subgroup.centralizer (A : Set G)) ⊔ Xc p M) :
    GLAPLayer p (M ⊓ Subgroup.centralizer (A : Set G)) ⊔ Xc p M = M := by
  have hOM : Xc p M ≤ GLAPPrimeCoreOf p M := comm_primeCore_le_core M
  have hOle : GLAPPrimeCoreOf p M ≤ M := Subgroup.map_subtype_le _
  have hcov : M = (M ⊓ Subgroup.centralizer (A : Set G)) ⊔ GLAPPrimeCoreOf p M :=
    le_antisymm (calc M = (M ⊓ Subgroup.centralizer (A : Set G)) ⊔ Xc p M := hcs
        _ ≤ _ := sup_le_sup_left hOM _) (sup_le inf_le_left hOle)
  exact cover_X hM ((layer_le_self p _).trans inf_le_left) (layer_covers hp hM inf_le_left hcov)

theorem F_le_K (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {M A : Subgroup G}
    (hKM : K ≤ M) (hcov : M = K ⊔ GLAPPrimeCoreOf p M) (hDA : D ≤ A) :
    GLAPLayer p (M ⊓ Subgroup.centralizer (A : Set G)) ≤ K := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set Y := Subgroup.centralizer (D : Set G) with hY
  set O := GLAPPrimeCoreOf p M with hO
  set F := GLAPLayer p (M ⊓ Subgroup.centralizer (A : Set G)) with hF
  have hKY : K ≤ Y := h.K_le_cs
  have hKlay : GLAPLayer p Y = K := std_layer h hin
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hKlay]
    exact fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hMO : M ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p M)
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := hKM.trans hMO
  set Θ := O ⊓ Y with hΘ
  have hΘp : ¬ p ∣ Nat.card Θ := fun hd =>
    not_dvd_card_glaPPrimeCoreOf hp M (hd.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hΘK : Θ ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans hYK
  have hMY : M ⊓ Y ≤ K ⊔ Θ := by
    intro g hg
    have hg' : g ∈ (K ⊔ O : Subgroup G) := by rw [← hcov]; exact hg.1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K O hKO] at hg'
    obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.mp hg'
    have hoY : o ∈ Y := by
      have : o = k⁻¹ * (k * o) := by group
      rw [this]
      exact mul_mem (inv_mem (hKY hk)) hg.2
    exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨ho, hoY⟩))
  have hFle : F ≤ K ⊔ Θ :=
    (layer_le_self p _).trans ((inf_le_inf_left M (Subgroup.centralizer_le (show (D : Set G) ⊆ A from hDA))).trans hMY)
  have hFY : F ≤ Y := hFle.trans (sup_le hKY inf_le_right)
  have hFN : F ≤ Subgroup.normalizer (K : Set G) := hFY.trans hYK
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hKFpos : 0 < Nat.card ↥(K ⊓ F) := Nat.card_pos
  have h1 := card_sup_mul_card_inf_of_le_normalizer hFN
  have h2 : K.relIndex F * Nat.card ↥(K ⊓ F) = Nat.card F := Subgroup.relIndex_mul_card K F
  have h3 := card_sup_mul_card_inf_of_le_normalizer hΘK
  have h4 : Nat.card ↥(K ⊔ F) ∣ Nat.card ↥(K ⊔ Θ) := Subgroup.card_dvd_of_le (sup_le le_sup_left hFle)
  have e1 : Nat.card ↥(K ⊔ F) = Nat.card K * K.relIndex F := by
    refine Nat.eq_of_mul_eq_mul_right hKFpos ?_
    rw [h1, ← h2]
    ring
  obtain ⟨t, ht⟩ := h4
  have e2 : Nat.card K * (K.relIndex F * (t * Nat.card ↥(K ⊓ Θ))) = Nat.card K * Nat.card Θ := by
    rw [← h3, ht, e1]
    ring
  have hr : K.relIndex F ∣ Nat.card Θ :=
    Dvd.intro _ (Nat.eq_of_mul_eq_mul_left hKpos e2)
  have hrp : Nat.Coprime (K.relIndex F) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hΘp (hd.trans hr)).symm
  have hnorm : ((K ⊓ F).subgroupOf F).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hFN
  have hidx : Nat.Coprime ((K ⊓ F).relIndex F) p := by
    rw [Subgroup.inf_relIndex_right]
    exact hrp
  exact inf_eq_right.1 (pPrimePerfect_glaPLayer p (M ⊓ Subgroup.centralizer (A : Set G)) (K ⊓ F) inf_le_right hnorm hidx)

theorem K_le_of_cover (hp : p.Prime) {X M F : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K) (hKc : GLAPComponent p X K)
    (hKM : K ≤ M) (hFK : F ≤ K) (hcov : M = F ⊔ Xc p M) : K ≤ F := by
  have hMO : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p M)
  have hMX : M ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer hMO
  have hFN : F ≤ Subgroup.normalizer ((Xc p M : Subgroup G) : Set G) := hFK.trans (hKM.trans hMX)
  have hKFZ : K = F ⊔ (K ⊓ Xc p M) := by
    refine le_antisymm ?_ (sup_le hFK inf_le_left)
    intro k hk
    have hk' : k ∈ (F ⊔ Xc p M : Subgroup G) := hcov ▸ hKM hk
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right F (Xc p M) hFN] at hk'
    obtain ⟨f, hf, x', hx', hfx⟩ := Set.mem_mul.mp hk'
    have hx'K : x' ∈ K := by
      have : x' = f⁻¹ * k := by rw [← hfx]; group
      rw [this]
      exact K.mul_mem (K.inv_mem (hFK hf)) hk
    rw [← hfx]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf) (Subgroup.mem_sup_right ⟨hx'K, hx'⟩)
  have hOK : (⁅K, GLAPPrimeCoreOf p K⁆ : Subgroup G) = ⊥ := S9.commutator_eq_bot_of_isQuasisimple hp hKc hq
  have hOK' : GLAPPrimeCoreOf p K ≤ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.commutator_comm] at hOK
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hOK
  have hZ : ∀ z ∈ K ⊓ Xc p M, ∀ m ∈ K, z * m = m * z := fun z hz m hm => by
    have hzO : z ∈ GLAPPrimeCoreOf p K :=
      inf_primeCore_le hp hKM ⟨hz.1, comm_primeCore_le_core M hz.2⟩
    exact (Subgroup.mem_centralizer_iff.1 (hOK' hzO) m hm).symm
  exact (HardMathSupport.Solomon.UniquenessMaximal.eq_of_perfect_sup_central hFK hKFZ hZ
    (glaPComponent_perfect hKc)).ge

theorem core124 (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) (hnn : NoNbr12 p B x L D K) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTy : T ≤ Subgroup.centralizer ({y} : Set G)) (hTD : D ≤ Subgroup.normalizer (T : Set G))
    (hTx : T = ⁅T, Subgroup.zpowers x⁆) : T ≤ Subgroup.centralizer (K : Set G) := by
  have hcom := hin.l122.l121.common
  have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ Subgroup.one_mem _)
  obtain ⟨M, hM, hMeq, hc⟩ := Ky_single h hcom hnn hy hyx
  have hcov : M = K ⊔ GLAPPrimeCoreOf p M := cover_of_centMod h hcom hy hyx hM hMeq hc
  have hKM : K ≤ M := by
    rw [← hMeq]
    exact le_closureIn_self K _
  have hBM : B ≤ Subgroup.normalizer (M : Set G) := by
    rw [← hMeq]
    exact ky_norm h hy
  have hxy : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute h.elem h.xD hy
  have hTM : T ≤ Subgroup.normalizer (M : Set G) :=
    T_normalizes hTy hxy (fun M' hM' => x_norm_comps h hcom hnn hy hyx hM') hTx hM
  have hDM : D ≤ Subgroup.normalizer (M : Set G) := fun d hd => hBM (h.DB hd)
  have hodd : Odd (Nat.card ↥(Xc p M)) :=
    oddCore_of_cover h hin.l122.l121 hin.i1810 hy hy1 hM hKM hBM hcov
  have hKX : K ⊔ Xc p M = M := cover_X hM hKM hcov
  have hKx : K ≤ Subgroup.centralizer ({x} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (h.K_le_cs hk) x h.xD).symm
  have hKD : K ≤ Subgroup.centralizer (D : Set G) := h.K_le_cs
  have hxM : x ∈ Subgroup.normalizer (M : Set G) := hc.1
  have hMT := comm_M_T hKx hKX hxM hTM hTx
  have hcs := cover_cs hT2 h.prime h.elem hTD hKD hKX hTM hDM hodd hMT
  have hF := F_cover h.prime hM hcs
  have hFK := F_le_K h hcom hKM hcov (le_sup_right : D ≤ T ⊔ D)
  have hKF := K_le_of_cover h.prime h.K_qs (std_pcomp' h hcom) hKM hFK hF.symm
  have hFcs : GLAPLayer p (M ⊓ Subgroup.centralizer ((T ⊔ D : Subgroup G) : Set G)) ≤
      Subgroup.centralizer ((T ⊔ D : Subgroup G) : Set G) :=
    (layer_le_self p _).trans inf_le_right
  have hKT : K ≤ Subgroup.centralizer (T : Set G) :=
    (hKF.trans hFcs).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_sup_left : T ≤ T ⊔ D)))
  exact Subgroup.le_centralizer_iff.1 hKT

theorem lemma124 (h : Cfg12 G m p B x L D K) (hin : Inputs124 G p) (hnn : NoNbr12 p B x L D K) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTD : D ≤ Subgroup.normalizer (T : Set G)) :
    (⁅T, Subgroup.zpowers x⁆ : Subgroup G) ≤ Subgroup.centralizer (K : Set G) := by
  have hp := h.prime
  have hcop : Nat.Coprime p (Nat.card T) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 h.odd)
  have hsolv : Group.IsSolvable T := by
    haveI := IsPGroup.isNilpotent hT2
    infer_instance
  have hgen := CFSG.SignalizerFunctorTheorem.Coprime.commutator_eq_iSup_hyperplanes hp h.elem
    (by rw [h.card_D]) hTD hcop hsolv h.xD
  rw [hgen]
  refine iSup₂_le fun B' hB' => ?_
  rcases hyperplane_cases h hB' with rfl | ⟨y, hy, hyx, rfl⟩
  ·
    have : (⁅T ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G), Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    rw [this]
    exact bot_le
  · obtain ⟨h2, hcy, hD, hT'⟩ := hyper_data h hy hT2 hTD
    rw [S3.centralizer_zpowers y]
    exact core124 h hin hnn hy hyx h2 hcy hD hT'

end S12

end CFSG.LocalAnalysis.GLTheoremA
