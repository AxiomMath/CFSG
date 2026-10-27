module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBlock
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTorus

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Polynomial

section Group

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem le_pRank_centralizer_of_sylow_abelian [Fact p.Prime]
    (hab : ∀ P : Sylow p G, IsMulCommutative (P : Subgroup G)) {r : ℕ}
    (hr : r ≤ CFSG.Open.pRank p (⊤ : Subgroup G)) {x : G} (hx : x ^ p = 1) :
    r ≤ CFSG.Open.pRank p (centralizer ({x} : Set G)) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hzp : IsPGroup p (Subgroup.zpowers x) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hxP : x ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers x)
  haveI : IsMulCommutative (P : Subgroup G) := hab P
  have hrk := (CFSG.SectionRank.pRank_sylow P).1
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact setLike_mul_comm hz hxP
  calc r ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := hr
    _ = CFSG.Open.pRank p (P : Subgroup G) := hrk.symm
    _ ≤ CFSG.Open.pRank p (centralizer ({x} : Set G)) :=
        CFSG.SectionRank.pRank_mono hp1 hPC

end Group

section Block

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
  {W C : Submodule K V}

noncomputable def prodMapOne (K W C : Type) [Field K] [AddCommGroup W] [Module K W]
    [AddCommGroup C] [Module K C] : Module.End K W →* Module.End K (W × C) where
  toFun g := g.prodMap (1 : Module.End K C)
  map_one' := LinearMap.prodMap_one
  map_mul' g g' := by rw [LinearMap.prodMap_mul, mul_one]

noncomputable def blockEnd (hWC : IsCompl W C) : Module.End K W →* Module.End K V :=
  ((LinearEquiv.conjAlgEquiv K (Submodule.prodEquivOfIsCompl W C hWC)).toMulEquiv.toMonoidHom).comp
    (prodMapOne K W C)

theorem blockEnd_injective (hWC : IsCompl W C) : Function.Injective (blockEnd hWC) := by
  intro g g' h
  have h1 : g.prodMap (1 : Module.End K C) = g'.prodMap (1 : Module.End K C) :=
    (LinearEquiv.conjAlgEquiv K (Submodule.prodEquivOfIsCompl W C hWC)).injective h
  ext w
  have := congrArg (fun F => (F (w, 0)).1) h1
  simpa using this

theorem conjAlgEquiv_prodMap_restrict (hWC : IsCompl W C) {y : Module.End K V}
    (hW : ∀ x ∈ W, y x ∈ W) (hC : ∀ x ∈ C, y x ∈ C) :
    LinearEquiv.conjAlgEquiv K (Submodule.prodEquivOfIsCompl W C hWC)
      ((y.restrict hW).prodMap (y.restrict hC)) = y := by
  ext v
  obtain ⟨⟨w, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W C hWC).surjective v
  simp [LinearEquiv.conjAlgEquiv_apply, Submodule.coe_prodEquivOfIsCompl', map_add]

theorem blockEnd_comm (hWC : IsCompl W C) {y : Module.End K V} (hW : ∀ x ∈ W, y x ∈ W)
    (hC : ∀ x ∈ C, y x ∈ C) (g : Module.End K W) (hg : g * y.restrict hW = y.restrict hW * g) :
    blockEnd hWC g * y = y * blockEnd hWC g := by
  set Φ := LinearEquiv.conjAlgEquiv K (Submodule.prodEquivOfIsCompl W C hWC) with hΦ
  have hy := conjAlgEquiv_prodMap_restrict hWC hW hC
  calc blockEnd hWC g * y = Φ (g.prodMap 1) * Φ ((y.restrict hW).prodMap (y.restrict hC)) := by
        rw [hy]; rfl
    _ = Φ ((g * y.restrict hW).prodMap (1 * y.restrict hC)) := by
        rw [← map_mul, LinearMap.prodMap_mul]
    _ = Φ ((y.restrict hW * g).prodMap (y.restrict hC * 1)) := by
        rw [hg, one_mul, mul_one]
    _ = Φ ((y.restrict hW).prodMap (y.restrict hC)) * Φ (g.prodMap 1) := by
        rw [← map_mul, LinearMap.prodMap_mul]
    _ = y * blockEnd hWC g := by rw [hy]; rfl

theorem pRank_centralizer_le_of_window {p : ℕ} [Fact p.Prime] (hWC : IsCompl W C)
    {y : Module.End K V} (hW : ∀ x ∈ W, y x ∈ W) (hC : ∀ x ∈ C, y x ∈ C)
    (uW : (Module.End K W)ˣ) (huW : (uW : Module.End K W) = y.restrict hW)
    (u : (Module.End K V)ˣ) (hu : (u : Module.End K V) = y) :
    CFSG.Open.pRank p (centralizer ({uW} : Set (Module.End K W)ˣ)) ≤
      CFSG.Open.pRank p (centralizer ({u} : Set (Module.End K V)ˣ)) := by
  let ι : (Module.End K W)ˣ →* (Module.End K V)ˣ := Units.map (blockEnd hWC)
  have hι : Function.Injective ι := Units.map_injective (blockEnd_injective hWC)
  refine (CFSG.SectionRank.pRank_le_map (Fact.out : p.Prime).one_lt ι hι _).trans
    (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt ?_)
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hg' : (g : Module.End K W) * y.restrict hW = y.restrict hW * (g : Module.End K W) := by
    rw [← huW, ← Units.val_mul, ← Units.val_mul, hg]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hu]
  exact blockEnd_comm hWC hW hC _ hg'

end Block

section Main

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem natCast_ne_zero_of_not_dvd_card {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) :
    (p : K) ≠ 0 := by
  intro h
  obtain ⟨ch, hch⟩ := CharP.exists K
  have hchp : ch ∣ p := (CharP.cast_eq_zero_iff K ch p).1 h
  have hch' := CharP.char_is_prime K ch
  obtain rfl : ch = p := (Nat.prime_dvd_prime_iff_eq hch' hp).1 hchp
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K ch
  apply hpK
  rw [Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self ch n.ne_zero

theorem le_pRank_centralizer_GL {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) {c : ℕ} (hc : c < p)
    (hcn : c * e ≤ Module.finrank K V) {u : (Module.End K V)ˣ} (hu : u ^ p = 1) :
    c ≤ CFSG.Open.pRank p (centralizer ({u} : Set (Module.End K V)ˣ)) := by
  have hp2 : Odd p := hp.out.odd_of_ne_two (by omega)
  have hp0 := natCast_ne_zero_of_not_dvd_card hp.out hpK
  set y : Module.End K V := (u : Module.End K V) with hy
  have hyp : y ^ p = 1 := by rw [hy, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ p - 1 → f.natDegree ≤ e :=
    fun f hf hfP => natDegree_le_of_dvd_X_pow_sub_one he ((hpe e).2 dvd_rfl) hf hfP
  obtain ⟨W, C, hW, hC, hWC, hcW, hWlt⟩ := exists_window hyp hp0 hp.out.pos he hdeg hcn
  have hyWp : (y.restrict hW) ^ p = 1 := by
    have h' : ∀ x ∈ W, (y ^ p) x ∈ W := fun x hx => by rw [hyp]; simpa using hx
    rw [Module.End.pow_restrict p hW h']
    ext x
    simp [hyp]
  let uW : (Module.End K W)ˣ := Units.ofPowEqOne (y.restrict hW) p hyWp hp.out.ne_zero
  have huW : uW ^ p = 1 := Units.ext (by simpa [uW] using hyWp)
  have hne : Module.finrank K W / e < p :=
    lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul he).2 hWlt) (Nat.succ_le_of_lt hc)
  have hab : ∀ P : Sylow p (Module.End K W)ˣ, IsMulCommutative (P : Subgroup _) := fun P =>
    isMulCommutative_of_isPGroup_GL hp2 hpK he hpe hne P.isPGroup'
  have hrank : c ≤ CFSG.Open.pRank p (⊤ : Subgroup (Module.End K W)ˣ) :=
    le_pRank_GL hpK he hpe hcW
  exact (le_pRank_centralizer_of_sylow_abelian hab hrank huW).trans
    (pRank_centralizer_le_of_window hWC hW hC uW rfl u rfl)

end Main

end CFSG.LocalAnalysis.RankFourTheoremC
