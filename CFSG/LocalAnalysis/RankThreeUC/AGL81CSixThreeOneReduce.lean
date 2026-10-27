module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutModel
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

theorem nonempty_quot_pCore_oPPrimeHull_of_surjective {p : ℕ} [Fact p.Prime] {M N : Type}
    [Group M] [Finite M] [Group N] (π : M →* N) (hπ : Function.Surjective π)
    (hker : IsPGroup p π.ker) (hN : CFSG.pCore p N = ⊥) :
    Nonempty (↥(oPPrimeHull p (⊤ : Subgroup M)) ⧸
        CFSG.pCore p ↥(oPPrimeHull p (⊤ : Subgroup M)) ≃*
      ↥(oPPrimeHull p (⊤ : Subgroup N))) := by
  classical
  haveI : Finite N := Finite.of_surjective π hπ
  let HM : Subgroup M := oPPrimeHull p (⊤ : Subgroup M)
  let Y : Subgroup N := oPPrimeHull p (⊤ : Subgroup N)
  have hY : HM.map π = Y := by
    rw [map_oPPrimeHull, Subgroup.map_top_of_surjective π hπ]
  let f : ↥HM →* ↥Y := (π.comp HM.subtype).codRestrict Y fun x => by
    rw [← hY]; exact Subgroup.mem_map_of_mem π x.2
  have hfs : Function.Surjective f := by
    intro y
    have hy : (y : N) ∈ HM.map π := by rw [hY]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hfk : IsPGroup p f.ker := by
    intro x
    have hx1 : f (x : ↥HM) = 1 := x.2
    have hxker : ((x : ↥HM) : M) ∈ π.ker := by
      have h2 : π ((x : ↥HM) : M) = 1 := by
        have := congrArg (fun y : ↥Y => (y : N)) hx1
        simpa [f] using this
      exact MonoidHom.mem_ker.mpr h2
    obtain ⟨n, hn⟩ := hker ⟨_, hxker⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  obtain ⟨e⟩ := nonempty_quot_pCore_mulEquiv_of_surjective (p := p) f hfs hfk
  have hYpc : CFSG.pCore p ↥Y = ⊥ := by
    haveI : Y.Normal := oPPrimeHull_top_normal p
    haveI : (CFSG.pCore p ↥Y).Characteristic := CFSG.pCore_characteristic
    have hKn : ((CFSG.pCore p ↥Y).map Y.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hKp : IsPGroup p ↥((CFSG.pCore p ↥Y).map Y.subtype) :=
      CFSG.pCore_isPGroup.map Y.subtype
    have hle : (CFSG.pCore p ↥Y).map Y.subtype ≤ CFSG.pCore p N := le_sSup ⟨hKn, hKp⟩
    rw [hN] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp (le_bot_iff.mp hle)
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hYpc).trans QuotientGroup.quotientBot)⟩

theorem nonempty_quot_pCore_oPPrimeHull_map_subtype {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    (R : Subgroup G) [Finite ↥R] :
    Nonempty (↥(oPPrimeHull p (⊤ : Subgroup ↥R)) ⧸
        CFSG.pCore p ↥(oPPrimeHull p (⊤ : Subgroup ↥R)) ≃*
      ↥(oPPrimeHull p R) ⧸ CFSG.pCore p ↥(oPPrimeHull p R)) := by
  have hmap : (oPPrimeHull p (⊤ : Subgroup ↥R)).map R.subtype = oPPrimeHull p R := by
    rw [map_oPPrimeHull, Subgroup.map_top, Subgroup.range_subtype]
  exact nonempty_quot_pCore_mulEquiv_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ R.subtype R.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap))

theorem nonempty_oPPrimeHull_quot_pCore_mulEquiv {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    [Finite X] {G : Type} [Group G] (φ : X →* G) (hφ : φ.ker ≤ CFSG.pCore p X) :
    Nonempty (↥(oPPrimeHull p (⊤ : Subgroup (X ⧸ CFSG.pCore p X))) ≃*
      (↥(oPPrimeHull p φ.range) ⧸ CFSG.pCore p ↥(oPPrimeHull p φ.range))) := by
  classical
  let Q : Subgroup X := CFSG.pCore p X
  haveI hQn : Q.Normal := CFSG.pCore_normal
  haveI : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hker : IsPGroup p φ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (CFSG.pCore_isPGroup.to_subgroup ((φ.ker).subgroupOf Q)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hφ)
  obtain ⟨e⟩ := nonempty_quot_pCore_mulEquiv_of_surjective (p := p) φ.rangeRestrict
    φ.rangeRestrict_surjective hker
  let Y : Subgroup (↥φ.range ⧸ CFSG.pCore p ↥φ.range) := oPPrimeHull p ⊤
  have hEY : (oPPrimeHull p (⊤ : Subgroup (X ⧸ Q))).map e = Y := by
    rw [map_oPPrimeHull,
      Subgroup.map_top_of_surjective (e : X ⧸ Q →* ↥φ.range ⧸ CFSG.pCore p ↥φ.range) e.surjective]
  have e₁ : ↥(oPPrimeHull p (⊤ : Subgroup (X ⧸ Q))) ≃* ↥Y :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hEY)
  obtain ⟨e₂⟩ := nonempty_quot_pCore_oPPrimeHull_of_surjective (p := p)
    (QuotientGroup.mk' (CFSG.pCore p ↥φ.range))
    (QuotientGroup.mk'_surjective (CFSG.pCore p ↥φ.range))
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
    (CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥φ.range) p)
  obtain ⟨e₃⟩ := nonempty_quot_pCore_oPPrimeHull_map_subtype (p := p) φ.range
  exact ⟨e₁.trans (e₂.symm.trans e₃)⟩

theorem exists_pow_mem_centralizer_of_ker {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    {Q : Subgroup X} [Q.Normal] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : MulAut ↥Q →* (Module.End (ZMod p) V)ˣ)
    (hρ : ∀ y : MulAut ↥Q, ρ y = 1 → ∃ k : ℕ, y ^ (p ^ k) = 1) {x : X}
    (hx : ρ (MulAut.conjNormal x) = 1) :
    ∃ k : ℕ, x ^ p ^ k ∈ Subgroup.centralizer (Q : Set X) := by
  obtain ⟨k, hk⟩ := hρ (MulAut.conjNormal x) hx
  refine ⟨k, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 : MulAut.conjNormal (H := Q) (x ^ p ^ k) ⟨q, hq⟩ = ⟨q, hq⟩ := by
    rw [map_pow, hk, MulAut.one_apply]
  have h2 := congrArg (fun y : ↥Q => (y : X)) h1
  rw [MulAut.conjNormal_apply] at h2
  have h3 : x ^ p ^ k * q = q * x ^ p ^ k := by
    calc x ^ p ^ k * q = x ^ p ^ k * q * (x ^ p ^ k)⁻¹ * x ^ p ^ k := by group
      _ = q * x ^ p ^ k := by rw [h2]
  exact h3.symm

theorem ker_le_pCore_of_exists_pow_mem {p : ℕ} [Fact p.Prime] {X M : Type} [Group X]
    [Finite X] [Group M] (φ : X →* M)
    (hkey : ∀ x ∈ φ.ker, ∃ k : ℕ, x ^ p ^ k ∈ CFSG.pCore p X) :
    φ.ker ≤ CFSG.pCore p X := by
  intro x hx
  have hNp : IsPGroup p ((φ.ker).map (QuotientGroup.mk' (CFSG.pCore p X))) := by
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨k, hk⟩ := hkey z hz
    refine ⟨k, Subtype.ext ?_⟩
    change (y : X ⧸ CFSG.pCore p X) ^ p ^ k = 1
    rw [← hzy]
    show ((QuotientGroup.mk' (CFSG.pCore p X)) z) ^ p ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  haveI hNn : ((φ.ker).map (QuotientGroup.mk' (CFSG.pCore p X))).Normal :=
    (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective _)
  have hNle : (φ.ker).map (QuotientGroup.mk' (CFSG.pCore p X)) ≤
      CFSG.pCore p (X ⧸ CFSG.pCore p X) := le_sSup ⟨hNn, hNp⟩
  rw [CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot'] at hNle
  have hxN : (QuotientGroup.mk' (CFSG.pCore p X)) x ∈
      (φ.ker).map (QuotientGroup.mk' (CFSG.pCore p X)) := Subgroup.mem_map_of_mem _ hx
  have hx1 : (QuotientGroup.mk' (CFSG.pCore p X)) x = 1 := by
    have := hNle hxN
    simpa using this
  exact (QuotientGroup.eq_one_iff x).mp hx1

theorem exists_smallSymp_rep {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    (hC : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hQ : CFSG.Open.pRank p (CFSG.pCore p X) ≤ 3) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod p) W) (_ : Module.Finite (ZMod p) W)
      (φ : X →* (Module.End (ZMod p) W)ˣ), φ.ker ≤ CFSG.pCore p X ∧
      (Module.finrank (ZMod p) W ≤ 3 ∨
        (Module.finrank (ZMod p) W = 4 ∧ ∃ B : LinearMap.BilinForm (ZMod p) W,
          (∀ u : W, (∀ v : W, B u v = 0) → u = 0) ∧ (∀ w : W, B w w = 0) ∧
          ∀ x : X, ∃ c : ZMod p, ∀ u v : W,
            B ((φ x : Module.End (ZMod p) W) u) ((φ x : Module.End (ZMod p) W) v) =
              c * B u v)) := by
  classical
  let Q : Subgroup X := CFSG.pCore p X
  haveI hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup p ↥Q := CFSG.pCore_isPGroup
  have hr : CFSG.Open.pRank p (⊤ : Subgroup ↥Q) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hQ
  obtain ⟨W, hWac, hWmod, hWfin, ρ, hρker, hdim⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.AutSection.hasSmallSympModel (q := p) hp2 hQp hr
  letI : AddCommGroup W := hWac
  letI : Module (ZMod p) W := hWmod
  letI : Module.Finite (ZMod p) W := hWfin
  let κ : X →* MulAut ↥Q := MulAut.conjNormal
  let φ : X →* (Module.End (ZMod p) W)ˣ := ρ.comp κ
  have hkey : ∀ x ∈ φ.ker, ∃ k : ℕ, x ^ p ^ k ∈ CFSG.pCore p X := by
    intro x hx
    have hx1 : ρ (κ x) = 1 := by
      have := (MonoidHom.mem_ker.mp hx : φ x = 1)
      simpa [φ] using this
    obtain ⟨k, hk⟩ := exists_pow_mem_centralizer_of_ker ρ hρker hx1
    exact ⟨k, hC hk⟩
  refine ⟨W, hWac, hWmod, hWfin, φ, ker_le_pCore_of_exists_pow_mem φ hkey, ?_⟩
  rcases hdim with h3 | ⟨h4, B, hBnd, hBalt, hBsim⟩
  · exact Or.inl h3
  · exact Or.inr ⟨h4, B, hBnd, hBalt, fun x => hBsim (κ x)⟩

theorem sixThreeOneAt_of_lists {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : LinearListAt p)
    (hS : SympListAt p) : SixThreeOneAt p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro X _ _ hC hQ hXrank
  obtain ⟨W, hWac, hWmod, hWfin, φ, hker, hdim⟩ := exists_smallSymp_rep hp2 hC hQ
  letI : AddCommGroup W := hWac
  letI : Module (ZMod p) W := hWmod
  letI : Module.Finite (ZMod p) W := hWfin
  let H : Subgroup (Module.End (ZMod p) W)ˣ := oPPrimeHull p φ.range
  have hH : oPPrimeHull p H = H := oPPrimeHull_oPPrimeHull p φ.range
  have hlist : SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H) := by
    rcases hdim with h3 | ⟨h4, B, hBnd, hBalt, hBsim⟩
    · exact @hL W hWac hWmod hWfin h3 H hH
    · refine @hS W hWac hWmod hWfin h4 B hBnd hBalt H hH ?_
      intro x hx
      have hxr : x ∈ φ.range := (Subgroup.closure_le φ.range).mpr (fun y hy => hy.1) hx
      obtain ⟨y, hy⟩ := hxr
      obtain ⟨c, hc⟩ := hBsim y
      exact ⟨c, fun u v => by rw [← hy]; exact hc u v⟩
  obtain ⟨e⟩ := nonempty_oPPrimeHull_quot_pCore_mulEquiv (p := p) φ hker
  exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.SixThreeOneList.of_mulEquiv e.symm hlist

theorem sixThreeOne_of_forall (h : ∀ p : ℕ, p.Prime → p ≠ 2 → SixThreeOneAt p) : SixThreeOne := by
  intro p hp hp2
  exact h p hp hp2

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
