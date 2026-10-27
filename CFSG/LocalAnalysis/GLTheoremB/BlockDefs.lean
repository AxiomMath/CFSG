module

public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsChiefFactorOf (L V U : Subgroup G) : Prop :=
  V < U ∧ L ≤ Subgroup.normalizer (V : Set G) ∧ L ≤ Subgroup.normalizer (U : Set G) ∧
    ∀ W : Subgroup G, V ≤ W → W ≤ U → L ≤ Subgroup.normalizer (W : Set G) → W = V ∨ W = U

@[expose] def IsChiefSeriesIn (L R : Subgroup G) {n : ℕ} (S : Fin (n + 1) → Subgroup G) : Prop :=
  S 0 = ⊥ ∧ S (Fin.last n) = R ∧ ∀ i : Fin n, IsChiefFactorOf L (S i.castSucc) (S i.succ)

@[expose] def IsNoncentralChiefFactor (L R V U : Subgroup G) : Prop :=
  IsChiefFactorOf L V U ∧ U ≤ R ∧ ¬ ⁅U, L⁆ ≤ V

structure IsGLBlock (M L : Subgroup G) : Prop where
  le : L ≤ M
  subnormal : IsSubnormal L M
  residual : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤
  simple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)
  commutator_le : ∀ x ∈ ⁅L, pCoreOf 2 L⁆,
    x ∈ pCoreOf 2 L ∧ x ^ 2 = 1 ∧ ∀ r ∈ pCoreOf 2 L, x * r = r * x
  unique_noncentral : ∀ (n : ℕ) (S : Fin (n + 1) → Subgroup G), IsChiefSeriesIn L (pCoreOf 2 L) S →
    ∃! i : Fin n, ¬ ⁅S i.succ, L⁆ ≤ S i.castSucc

@[expose] def barMap (p : ℕ) {M L : Subgroup G} (hLM : L ≤ M) : ↥L →* ↥(barX p M L) :=
  ((QuotientGroup.mk' (GLAPPrimeCore p ↥M)).comp (Subgroup.inclusion hLM)).codRestrict
    (barX p M L) fun ℓ => ⟨Subgroup.inclusion hLM ℓ, ℓ.2, rfl⟩

@[expose] def inducedAutGroup {Y : Type*} [Group Y] (W A : Subgroup Y) : Subgroup (MulAut ↥A) :=
  (W.subgroupOf (Subgroup.normalizer (A : Set Y))).map A.normalizerMonoidHom

@[expose] def ActsLike {Y : Type*} [Group Y] {K : Type*} [Group K] (W A : Subgroup Y)
    (e : ↥A ≃* K) (S : Subgroup (MulAut K)) : Prop :=
  (inducedAutGroup W A).map (MulAut.congr e).toMonoidHom = S

@[expose] def ChiefFactorIso {A N : Type*} [Group A] [AddCommGroup N] (L U V : Subgroup G)
    (ρ : ↥L →* A)
    (a : A → N → N) : Prop :=
  ∃ φ : ↥U →* Multiplicative N, Function.Surjective φ ∧ (∀ u : ↥U, φ u = 1 ↔ (u : G) ∈ V) ∧
    ∀ (ℓ : ↥L) (u u' : ↥U), (u' : G) = (ℓ : G) * u * (ℓ : G)⁻¹ →
      φ u' = Multiplicative.ofAdd (a (ρ ℓ) (Multiplicative.toAdd (φ u)))

@[expose] def evenWt (m : ℕ) : AddSubgroup (Fin m → ZMod 2) :=
  AddMonoidHom.ker (∑ i : Fin m, Pi.evalAddMonoidHom (fun _ : Fin m => ZMod 2) i)

@[expose] def constWt (m : ℕ) : AddSubgroup (Fin m → ZMod 2) :=
  AddSubgroup.zmultiples (fun _ : Fin m => (1 : ZMod 2))

instance (m : ℕ) : AddCommGroup ↥(evenWt m) := AddSubgroupClass.toAddCommGroup (evenWt m)

abbrev AltHeart (m : ℕ) : Type :=
  ↥(evenWt m) ⧸ ((constWt m ⊓ evenWt m).addSubgroupOf (evenWt m))

instance (m : ℕ) : AddCommGroup (AltHeart m) := QuotientAddGroup.Quotient.addCommGroup _

@[expose] def permAct (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    (Fin m → ZMod 2) →+ (Fin m → ZMod 2) :=
  AddMonoidHom.mk' (fun v i => v (σ⁻¹ i)) fun _ _ => rfl

@[expose] def permEven (m : ℕ) (σ : Equiv.Perm (Fin m)) : ↥(evenWt m) →+ ↥(evenWt m) :=
  ((permAct m σ).comp (evenWt m).subtype).codRestrict (evenWt m) fun v => by
    have h := v.2
    simp only [evenWt, AddMonoidHom.mem_ker, AddMonoidHom.finsetSum_apply,
      Pi.evalAddMonoidHom_apply] at h ⊢
    rw [← h]
    exact Equiv.sum_comp σ⁻¹ (fun i => (v : Fin m → ZMod 2) i)

@[expose] def altHeartAct (m : ℕ) (σ : Equiv.Perm (Fin m)) : AltHeart m → AltHeart m :=
  QuotientAddGroup.map _ _ (permEven m σ) (by
    intro x hx
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf] at hx ⊢
    obtain ⟨hc, he⟩ := hx
    refine ⟨?_, (permEven m σ x).2⟩
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hc
    have hx' : (x : Fin m → ZMod 2) = k • (fun _ : Fin m => (1 : ZMod 2)) := hk.symm
    have : (permEven m σ x : Fin m → ZMod 2) = (x : Fin m → ZMod 2) := by
      funext i
      change (x : Fin m → ZMod 2) (σ⁻¹ i) = (x : Fin m → ZMod 2) i
      rw [hx']
      simp
    rw [this]
    exact hc)

@[expose] def IsTransvection {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι (ZMod 2)) : Prop :=
  ∃ (v : ι → ZMod 2) (f : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2), v ≠ 0 ∧ f ≠ 0 ∧ f v = 0 ∧
    ∀ x, Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x = x + f x • v

@[expose] def ActsLikeTransvection {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2) {Y : Type*} [Group Y] (W A : Subgroup Y)
    (e : ↥A ≃* ↥(StatedOmega Q)) : Prop :=
  ∃ (t : GL ι (ZMod 2)) (ht : t ∈ Subgroup.normalizer (StatedOmega Q : Set (GL ι (ZMod 2)))),
    (∀ x, Q (Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x) = Q x) ∧ IsTransvection t ∧
      ActsLike W A e (Subgroup.zpowers ((StatedOmega Q).normalizerMonoidHom ⟨t, ht⟩))

@[expose] def ActsLikeRootFourGroup {Y : Type*} [Group Y] (W A : Subgroup Y)
    (e : ↥A ≃* ↥(alternatingGroup (Fin 7))) : Prop :=
  ∃ V : Subgroup ↥(alternatingGroup (Fin 7)), Nat.card V = 4 ∧ (∀ v ∈ V, v ^ 2 = 1) ∧
    Nat.card {i : Fin 7 // ∀ v ∈ V, (v : Equiv.Perm (Fin 7)) i = i} = 3 ∧
      ActsLike W A e (V.map (MulAut.conj : ↥(alternatingGroup (Fin 7)) →* _))

end CFSG.LocalAnalysis.GLTheoremB
