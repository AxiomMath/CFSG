module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

set_option linter.unusedSectionVars false


theorem exists_langSetup_conj_of_inndiag_twE6_phi {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ twistedE6InndiagGL K σ)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) h := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h with hu
  have huF : u ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h, hh, rfl⟩
  have huG : u ∈ adjointGroup TwistTag.E6.tag L := huF.1
  have hufix : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) u = u := huF.2
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.E6 f hf hufix hconj
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    rw [hι₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL TwistTag.E6.tag K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hconjι, hg0⟩ :=
    exists_langSetup_conj_of_toral_datum hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ β hβ' hmem
      hup hu1
  exact ⟨S, a, ι, hDq, ⟨iterateFrobenius L ℓ f, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconjι, hg0⟩


section Rho

@[expose] noncomputable def w0E6 : WeylGroup Tag.E6 := twE6W0

theorem w0E6_smul (z : Fin Tag.E6.rank → ℤ) : w0E6 • z = -(permLattice e6Graph z) :=
  twE6W0_smul z

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem exists_weyl_rho_eq_neg (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) :
    ∃ u : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -(u • γ) := by
  classical
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hq0 : 0 < S.D.q := by
    obtain ⟨r, e, hr, -, he, hq⟩ := S.exists_char_pow
    rw [hq]
    exact pow_pos hr.pos e
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
        twistHom TwistTag.E6 L Fr g * (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹
      rw [hΦ, hn]
      rfl
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  refine ⟨w * w0E6, fun γ hγ => ?_⟩
  rw [hρw γ hγ, mul_smul, w0E6_smul, smul_neg, neg_neg]

theorem rootChar_neg_aux {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ)
    (v : Fin Tag.E6.rank → ℤ) : rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem rootChar_pow_eq_one_aux {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ) {p : ℕ}
    (hap : ∀ i, a i ^ p = 1) (v : Fin Tag.E6.rank → ℤ) : rootChar a v ^ p = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast (a i ^ v i) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap i,
    one_zpow]

theorem mem_rootCharStabilizer_of_rho_eq_neg (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1) {u : WeylGroup Tag.E6}
    (hu : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -(u • γ)) : u ∈ rootCharStabilizerSubgroup a := by
  intro v
  refine rootChar_smul_eq_of_forall_isRoot (fun α hα => ?_) v
  have h1 : u • α = -(S.ρ α) := by rw [hu α hα, neg_neg]
  have h2 := S.frob.rootChar_eq a hT α hα
  have h3 : rootChar a α ^ (S.D.q + 1) = 1 := by
    obtain ⟨k, hk⟩ := h3q
    rw [hk, pow_mul, rootChar_pow_eq_one_aux a hap α, one_pow]
  rw [h1, rootChar_neg_aux, h2]
  have h4 : rootChar a α ^ S.D.q * rootChar a α = 1 := by rw [← pow_succ]; exact h3
  exact inv_eq_of_mul_eq_one_right h4

end Rho

section Conn

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem exists_rho_neg_weyl_of_conn (S : LangSetup Tag.E6 L p₀)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1)
    (hk : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 30, 40} : Set ℕ)) :
    ∃ u ∈ kernelReflectionGroup a, ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -(u • γ) := by
  obtain ⟨u, hu⟩ := exists_weyl_rho_eq_neg S hFr hΦ
  exact ⟨u, e6_stab_le_kernelReflectionGroup_of_conn a hap hk
    (mem_rootCharStabilizer_of_rho_eq_neg S hT hap h3q hu), hu⟩

end Conn

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
