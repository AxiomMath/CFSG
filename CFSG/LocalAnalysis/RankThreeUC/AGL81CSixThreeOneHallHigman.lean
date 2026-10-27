module

public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.HardMathSupport.Dickson.I271.Support.CyclicHH
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.SignalizerFunctorTheorem.CatalogBridge.HallHigman

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Matrix Polynomial Subgroup
open scoped MatrixGroups

private theorem natDegree_minpoly_le_finrank {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (f : V →ₗ[F] V) :
    (minpoly F f).natDegree ≤ Module.finrank F V := by
  have hdvd := LinearMap.minpoly_dvd_charpoly f
  have hne : f.charpoly ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  rwa [LinearMap.charpoly_natDegree] at hle

theorem pow_prime_eq_one_of_pow_prime_pow_eq_one {p : ℕ} [Fact p.Prime] {F V : Type*}
    [Field F] [CharP F p] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : Module.finrank F V < p) {x : LinearMap.GeneralLinearGroup F V} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ^ p = 1 := by
  have hx' : (x : Module.End F V) ^ p ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hnil : ((x : Module.End F V) - 1) ^ p ^ k = 0 := by
    have := CFSG.GroupTheory.HallHigmanB.sub_one_pow_char_pow (K := F) (V := V)
      (p := p) (a := (x : Module.End F V)) k
    simpa [hx'] using this
  have hfin : ((x : Module.End F V) - 1) ^ Module.finrank F V = 0 := by
    apply LinearMap.ext
    intro v
    have hle := Module.End.ker_pow_le_ker_pow_finrank ((x : Module.End F V) - 1) (p ^ k)
    have htop : LinearMap.ker (((x : Module.End F V) - 1) ^ p ^ k) = ⊤ := by
      rw [hnil]
      exact LinearMap.ker_zero
    have hv : v ∈ LinearMap.ker (((x : Module.End F V) - 1) ^ p ^ k) := by
      rw [htop]
      exact Submodule.mem_top
    exact hle hv
  have hpow : ((x : Module.End F V) - 1) ^ (p - 1) = 0 :=
    pow_eq_zero_of_le (by omega : Module.finrank F V ≤ p - 1) hfin
  have hxEnd : (x : Module.End F V) ^ p = 1 :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.pow_eq_one_of_sub_one_pow_eq_zero
      (K := F) (A := Module.End F V) (ℓ := p) (a := (x : Module.End F V)) hpow
  apply Units.ext
  simpa [Units.val_pow_eq_pow_val] using hxEnd

theorem pow_prime_eq_one_of_card_lt {p : ℕ} [Fact p.Prime] {σ : Type} [Fintype σ]
    [DecidableEq σ] (hσ : Fintype.card σ < p) {G : Subgroup (GL σ (ZMod p))} {x : ↥G} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ^ p = 1 := by
  let e : GL σ (ZMod p) ≃* LinearMap.GeneralLinearGroup (ZMod p) (σ → ZMod p) :=
    Matrix.GeneralLinearGroup.toLin
  let x' : LinearMap.GeneralLinearGroup (ZMod p) (σ → ZMod p) := e (x : GL σ (ZMod p))
  have hxGL : (x : GL σ (ZMod p)) ^ p ^ k = 1 := by
    simpa using congrArg (fun z : ↥G => (z : GL σ (ZMod p))) hx
  have hx' : x' ^ p ^ k = 1 := by
    rw [show x' = e (x : GL σ (ZMod p)) from rfl, ← map_pow, hxGL, map_one]
  have hV : Module.finrank (ZMod p) (σ → ZMod p) < p := by
    rwa [Module.finrank_fintype_fun_eq_card]
  have hp' : x' ^ p = 1 := pow_prime_eq_one_of_pow_prime_pow_eq_one hV (x := x') hx'
  apply Subtype.ext
  have hxGLp : (x : GL σ (ZMod p)) ^ p = 1 := by
    apply e.injective
    simpa [x'] using hp'
  simpa using hxGLp

theorem five_eq_of_hallHigman {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {σ : Type} [Fintype σ]
    [DecidableEq σ] (hσ : Fintype.card σ ≤ 4) (H : Subgroup (GL σ (ZMod p)))
    (hH : CFSG.HallHigman.IsPSolvable p ↥H) (hO : CFSG.pCore p ↥H = ⊥)
    (hp : p ∣ Nat.card ↥H) :
    p = 5 ∧ ∀ S : Sylow 2 ↥H, ∃ a ∈ (S : Subgroup ↥H), ∃ b ∈ (S : Subgroup ↥H), a * b ≠ b * a := by
  classical
  let e : GL σ (ZMod p) ≃* LinearMap.GeneralLinearGroup (ZMod p) (σ → ZMod p) :=
    Matrix.GeneralLinearGroup.toLin
  let H' : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) (σ → ZMod p)) := H.map e.toMonoidHom
  let eH : ↥H ≃* ↥H' := Subgroup.equivMapOfInjective H e.toMonoidHom e.injective
  haveI : Finite ↥H' := Finite.of_injective (fun y : ↥H' => eH.symm y) eH.symm.injective
  have hH' : CFSG.HallHigman.IsPSolvable p ↥H' :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      e.toMonoidHom hH
  have hO' : CFSG.piCore {q : Nat.Primes | q.val = p} ↥H' = ⊥ := by
    have h := CFSG.pCore_map_iso p eH
    rw [hO] at h
    have hbot : CFSG.pCore p ↥H' = ⊥ := by simpa [Subgroup.map_bot] using h.symm
    rwa [← CFSG.pCore_eq_piCore (G := ↥H') p]
  have hp' : p ∣ Nat.card ↥H' := by
    rwa [← Nat.card_congr eH.toEquiv]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H') p hp'
  obtain ⟨r, hr1, hrle, hmin, -, hexc, -⟩ :=
    CFSG.GroupTheory.HallHigmanB.hall_higman_theorem_B_minimal_polynomial
      (F := ZMod p) (V := σ → ZMod p) H' hH' hO' x
      (n := 1) le_rfl (by rw [pow_one]; exact hx)
  let f : (σ → ZMod p) →ₗ[ZMod p] (σ → ZMod p) :=
    ((x : LinearMap.GeneralLinearGroup (ZMod p) (σ → ZMod p)) :
      (σ → ZMod p) →ₗ[ZMod p] (σ → ZMod p))
  have hdeg : (minpoly (ZMod p) f).natDegree ≤ 4 :=
    (natDegree_minpoly_le_finrank f).trans (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact hσ)
  have hmin' : minpoly (ZMod p) f = (X - 1) ^ r := hmin
  have hr4 : r ≤ 4 := by
    have hX1 : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
    have hdeg' : (minpoly (ZMod p) f).natDegree = r := by
      rw [hmin', hX1, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rwa [hdeg'] at hdeg
  have hrlt : r < p ^ 1 := by rw [pow_one]; omega
  rcases hexc hrlt with ⟨_, hsyl, hbound⟩ | ⟨hp2, _⟩
  · have hbound' : p - 1 ≤ r := by simpa using hbound
    have hple : p ≤ 5 := by omega
    refine ⟨by omega, ?_⟩
    intro S
    let S' : Sylow 2 ↥H' := Sylow.mapSurjective (f := eH.toMonoidHom) eH.surjective S
    obtain ⟨a', ha', b', hb', hab⟩ := hsyl S'
    have hcoe : (S' : Subgroup ↥H') = (S : Subgroup ↥H).map eH.toMonoidHom :=
      Sylow.coe_mapSurjective (f := eH.toMonoidHom) eH.surjective S
    rw [hcoe, Subgroup.mem_map] at ha' hb'
    obtain ⟨a, haS, rfl⟩ := ha'
    obtain ⟨b, hbS, rfl⟩ := hb'
    exact ⟨a, haS, b, hbS, fun h => hab (by simpa using congrArg eH h)⟩
  · omega

private theorem pCore_eq_bot_of_normal {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hO : CFSG.pCore p G = ⊥) (M : Subgroup G) [M.Normal] :
    CFSG.pCore p ↥M = ⊥ := by
  let K : Subgroup ↥M := CFSG.pCore p ↥M
  have hKchar : K.Characteristic := CFSG.pCore_characteristic
  haveI : K.Characteristic := hKchar
  have hKnormal : (K.map M.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hKp : IsPGroup p ↥(K.map M.subtype) := CFSG.pCore_isPGroup.map M.subtype
  have hle : K.map M.subtype ≤ CFSG.pCore p G := le_sSup ⟨hKnormal, hKp⟩
  rw [hO] at hle
  have hbot : K.map M.subtype = ⊥ := le_bot_iff.mp hle
  exact Subgroup.map_injective M.subtype_injective (by rw [hbot, Subgroup.map_bot])

private theorem isPGroup_two_le_of_odd_index {K : Type*} [Group K] [Finite K] {N : Subgroup K}
    [N.Normal] (hodd : Odd N.index) {P : Subgroup K} (hP : IsPGroup 2 P) : P ≤ N := by
  classical
  have hq2 : IsPGroup 2 (P.map (QuotientGroup.mk' N)) := hP.map _
  obtain ⟨n, hn⟩ := hq2.exists_card_eq
  have hdvd : 2 ^ n ∣ N.index := by
    rw [Subgroup.index_eq_card, ← hn]
    exact Subgroup.card_subgroup_dvd_card _
  have hn0 : n = 0 := by
    by_contra hnne
    exact hodd.not_two_dvd_nat (dvd_trans (dvd_pow_self 2 hnne) hdvd)
  have hcard : Nat.card ↥(P.map (QuotientGroup.mk' N)) = 1 := by
    rw [hn, hn0, pow_zero]
  have hbot : P.map (QuotientGroup.mk' N) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  have hle := (Subgroup.map_eq_bot_iff P).1 hbot
  rwa [QuotientGroup.ker_mk'] at hle

private theorem not_dvd_card_of_solvable_normal {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {σ : Type} [Fintype σ] [DecidableEq σ] (hσ : Fintype.card σ ≤ 4)
    {G : Subgroup (GL σ (ZMod p))} (hO : CFSG.pCore p ↥G = ⊥) (M : Subgroup ↥G) [M.Normal]
    (hM : IsSolvable ↥M)
    (hM2 : p = 5 → ∀ S : Sylow 2 ↥M, ∀ a ∈ (S : Subgroup ↥M), ∀ b ∈ (S : Subgroup ↥M),
      a * b = b * a) : ¬ p ∣ Nat.card ↥M := by
  intro hpM
  have hcoreM : CFSG.pCore p ↥M = ⊥ := pCore_eq_bot_of_normal hO M
  let H : Subgroup (GL σ (ZMod p)) := M.map G.subtype
  let eM : ↥M ≃* ↥H := Subgroup.equivMapOfInjective M G.subtype G.subtype_injective
  have hHps : CFSG.HallHigman.IsPSolvable p ↥H :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      G.subtype
      (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5.isPSolvable_of_isSolvable
        Fact.out hM)
  have hHO : CFSG.pCore p ↥H = ⊥ := by
    have h := CFSG.pCore_map_iso p eM
    rw [hcoreM] at h
    simpa [Subgroup.map_bot] using h.symm
  have hHdvd : p ∣ Nat.card ↥H := by
    rw [Subgroup.card_map_of_injective G.subtype_injective]
    exact hpM
  obtain ⟨hp_eq, hsylH⟩ := five_eq_of_hallHigman hp5 hσ H hHps hHO hHdvd
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  obtain ⟨aH, haH, bH, hbH, habH⟩ := hsylH S
  let P : Subgroup ↥M := ((S : Subgroup ↥H).map eM.symm.toMonoidHom)
  have hP2 : IsPGroup 2 P := S.isPGroup'.map eM.symm.toMonoidHom
  have haP : eM.symm aH ∈ P := Subgroup.mem_map.2 ⟨aH, haH, rfl⟩
  have hbP : eM.symm bH ∈ P := Subgroup.mem_map.2 ⟨bH, hbH, rfl⟩
  have hPnab : (eM.symm aH) * (eM.symm bH) ≠ (eM.symm bH) * (eM.symm aH) := by
    intro h
    exact habH (by simpa using congrArg eM h)
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  exact hPnab (hM2 hp_eq Q (eM.symm aH) (hPQ haP) (eM.symm bH) (hPQ hbP))

private theorem exists_nonabelian_two_subgroup_le_of_piCore_eq_bot {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {σ : Type} [Fintype σ] [DecidableEq σ] (hσ : Fintype.card σ ≤ 4)
    {G : Subgroup (GL σ (ZMod p))} (M : Subgroup ↥G) [M.Normal]
    {x : ↥G} (hxp : x ^ p = 1) (hxM : x ∉ M)
    {K : Subgroup ↥G} (N : Subgroup ↥K) (hN : N = M.subgroupOf K) [N.Normal]
    (xK : ↥K) (hxK : (xK : ↥G) = x) (hxKp : xK ^ p = 1)
    (hNcop : ¬ p ∣ Nat.card ↥N) (hidx : N.index ∣ p)
    (hpi : CFSG.piCore {q : Nat.Primes | q.val = p} ↥K = ⊥) :
    p = 5 ∧ ∃ P : Subgroup ↥K, IsPGroup 2 P ∧ P ≤ N ∧
      ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  have hKcore : CFSG.pCore p ↥K = ⊥ := by
    rwa [CFSG.pCore_eq_piCore (G := ↥K) p]
  have hidx_ne1 : N.index ≠ 1 := by
    intro h
    have htop : N = ⊤ := Subgroup.index_eq_one.mp h
    have hxN : xK ∈ N := by rw [htop]; exact Subgroup.mem_top _
    rw [hN] at hxN
    exact hxM (hxK ▸ Subgroup.mem_subgroupOf.mp hxN)
  have hidx_eq : N.index = p := by
    rcases (Nat.dvd_prime Fact.out).1 hidx with h | h
    · exact absurd h hidx_ne1
    · exact h
  have hKps : CFSG.HallHigman.IsPSolvable p ↥K :=
    CFSG.HardMathSupport.Dickson.I271.isPSolvable_of_normal_index_dvd hNcop hidx
  let H : Subgroup (GL σ (ZMod p)) := K.map G.subtype
  let eK : ↥K ≃* ↥H := Subgroup.equivMapOfInjective K G.subtype G.subtype_injective
  have hHps : CFSG.HallHigman.IsPSolvable p ↥H :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      G.subtype hKps
  have hHO : CFSG.pCore p ↥H = ⊥ := by
    have h := CFSG.pCore_map_iso p eK
    rw [hKcore] at h
    simpa [Subgroup.map_bot] using h.symm
  have hHdvd : p ∣ Nat.card ↥H := by
    rw [Subgroup.card_map_of_injective G.subtype_injective]
    rw [← Subgroup.card_mul_index N, hidx_eq]
    exact ⟨Nat.card ↥N, by rw [mul_comm]⟩
  obtain ⟨hp_eq, hsylH⟩ := five_eq_of_hallHigman hp5 hσ H hHps hHO hHdvd
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  obtain ⟨aH, haH, bH, hbH, habH⟩ := hsylH S
  let P : Subgroup ↥K := (S : Subgroup ↥H).map eK.symm.toMonoidHom
  have hP2 : IsPGroup 2 P := S.isPGroup'.map eK.symm.toMonoidHom
  have haP : eK.symm aH ∈ P := Subgroup.mem_map.2 ⟨aH, haH, rfl⟩
  have hbP : eK.symm bH ∈ P := Subgroup.mem_map.2 ⟨bH, hbH, rfl⟩
  have hPnab : (eK.symm aH) * (eK.symm bH) ≠ (eK.symm bH) * (eK.symm aH) := by
    intro h
    exact habH (by simpa using congrArg eK h)
  have hodd : Odd N.index := by rw [hidx_eq, hp_eq]; norm_num
  exact ⟨hp_eq, P, hP2, isPGroup_two_le_of_odd_index hodd hP2,
    eK.symm aH, haP, eK.symm bH, hbP, hPnab⟩

private theorem false_of_nonabelian_two_subgroup_le {p : ℕ} [Fact p.Prime] {σ : Type}
    [Fintype σ] [DecidableEq σ] {G : Subgroup (GL σ (ZMod p))} {M : Subgroup ↥G} [M.Normal]
    (hM2 : p = 5 → ∀ S : Sylow 2 ↥M, ∀ a ∈ (S : Subgroup ↥M), ∀ b ∈ (S : Subgroup ↥M),
      a * b = b * a)
    {K : Subgroup ↥G} (hMK : M ≤ K) (hp_eq : p = 5)
    {P : Subgroup ↥K} (hP2 : IsPGroup 2 P) (hPN : P ≤ M.subgroupOf K)
    (hnab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) : False := by
  obtain ⟨aK, haP, bK, hbP, hab⟩ := hnab
  let eM : ↥(M.subgroupOf K) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMK
  let aM : ↥M := eM ⟨aK, hPN haP⟩
  let bM : ↥M := eM ⟨bK, hPN hbP⟩
  have haM : aM ∈ (P.subgroupOf (M.subgroupOf K)).map eM.toMonoidHom :=
    Subgroup.mem_map.2 ⟨⟨aK, hPN haP⟩, Subgroup.mem_subgroupOf.2 haP, rfl⟩
  have hbM : bM ∈ (P.subgroupOf (M.subgroupOf K)).map eM.toMonoidHom :=
    Subgroup.mem_map.2 ⟨⟨bK, hPN hbP⟩, Subgroup.mem_subgroupOf.2 hbP, rfl⟩
  have hP'2 : IsPGroup 2 ((P.subgroupOf (M.subgroupOf K)).map eM.toMonoidHom) :=
    (IsPGroup.of_equiv hP2 (Subgroup.subgroupOfEquivOfLe hPN).symm).map _
  have hMnab : aM * bM ≠ bM * aM := by
    intro h
    have h' : (⟨aK, hPN haP⟩ : ↥(M.subgroupOf K)) * ⟨bK, hPN hbP⟩ =
        ⟨bK, hPN hbP⟩ * ⟨aK, hPN haP⟩ := eM.injective h
    refine hab ?_
    have h2 := congrArg (fun z : ↥(M.subgroupOf K) => (z : ↥K)) h'
    simpa only [Subgroup.coe_mul] using h2
  obtain ⟨Q, hPQ⟩ := hP'2.exists_le_sylow
  exact hMnab (hM2 hp_eq Q aM (hPQ haM) bM (hPQ hbM))

private theorem commute_of_pow_prime_of_solvable_normal {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {σ : Type} [Fintype σ] [DecidableEq σ] (hσ : Fintype.card σ ≤ 4)
    {G : Subgroup (GL σ (ZMod p))} (hO : CFSG.pCore p ↥G = ⊥) (M : Subgroup ↥G) [M.Normal]
    (hM : IsSolvable ↥M)
    (hM2 : p = 5 → ∀ S : Sylow 2 ↥M, ∀ a ∈ (S : Subgroup ↥M), ∀ b ∈ (S : Subgroup ↥M),
      a * b = b * a)
    {x : ↥G} (hxp : x ^ p = 1) : ∀ m ∈ M, x * m = m * x := by
  classical
  have hcopM := not_dvd_card_of_solvable_normal hp5 hσ hO M hM hM2
  by_cases hxM : x ∈ M
  · have hx1 : x = 1 := by
      have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
      have hdvdM : orderOf x ∣ Nat.card ↥M := Subgroup.orderOf_dvd_natCard M hxM
      have hcop : Nat.Coprime p (Nat.card ↥M) :=
        (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcopM
      have hgcd : orderOf x ∣ Nat.gcd p (Nat.card ↥M) := Nat.dvd_gcd hdvd hdvdM
      rw [hcop.gcd_eq_one] at hgcd
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
    intro m _
    rw [hx1, one_mul, mul_one]
  · let K : Subgroup ↥G := Subgroup.zpowers x ⊔ M
    let N : Subgroup ↥K := M.subgroupOf K
    haveI hN : N.Normal := Subgroup.Normal.subgroupOf inferInstance K
    have hMK : M ≤ K := le_sup_right
    let xK : ↥K := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩
    have hxK : (xK : ↥G) = x := rfl
    have hxKp : xK ^ p = 1 := Subtype.ext (by simpa [hxK] using hxp)
    have hcardN : Nat.card ↥N = Nat.card ↥M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMK).toEquiv
    have hNcop : ¬ p ∣ Nat.card ↥N := by rwa [hcardN]
    have hxo : orderOf x = p :=
      orderOf_eq_prime hxp (by intro h; exact hxM (h ▸ M.one_mem))
    have hidx : N.index ∣ p := by
      have hq := QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers x) M
        (Subgroup.le_normalizer_of_normal : Subgroup.zpowers x ≤ Subgroup.normalizer (M : Set ↥G))
      have h1 : Nat.card (↥K ⧸ N) =
          Nat.card (↥(Subgroup.zpowers x) ⧸ M.subgroupOf (Subgroup.zpowers x)) :=
        (Nat.card_congr hq.toEquiv).symm
      rw [Subgroup.index_eq_card, h1]
      have h2 := Subgroup.card_quotient_dvd_card (M.subgroupOf (Subgroup.zpowers x))
      rwa [Nat.card_zpowers, hxo] at h2
    rcases CFSG.HardMathSupport.Dickson.I271.piCore_eq_bot_or_commute (G := ↥K) (p := p)
        (N := N) hNcop hidx (x := xK) hxKp with hpi | hcomm
    · obtain ⟨hp_eq, P, hP2, hPN, hnab⟩ :=
        exists_nonabelian_two_subgroup_le_of_piCore_eq_bot hp5 hσ M hxp hxM N rfl xK hxK hxKp
          hNcop hidx hpi
      exact (false_of_nonabelian_two_subgroup_le hM2 hMK hp_eq hP2 hPN hnab).elim
    · intro m hm
      have hmK : (⟨m, Subgroup.mem_sup_right hm⟩ : ↥K) ∈ N :=
        Subgroup.mem_subgroupOf.2 hm
      have h : m * x = x * m := by
        simpa using congrArg (fun z : ↥K => (z : ↥G))
          (hcomm ⟨m, Subgroup.mem_sup_right hm⟩ hmK)
      exact h.symm

theorem commute_of_solvable_normal {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {σ : Type} [Fintype σ]
    [DecidableEq σ] (hσ : Fintype.card σ ≤ 4) {G : Subgroup (GL σ (ZMod p))}
    (hO : CFSG.pCore p ↥G = ⊥) (M : Subgroup ↥G) [M.Normal] (hM : IsSolvable ↥M)
    (hM2 : p = 5 → ∀ S : Sylow 2 ↥M, ∀ a ∈ (S : Subgroup ↥M), ∀ b ∈ (S : Subgroup ↥M),
      a * b = b * a)
    {x : ↥G} {k : ℕ} (hx : x ^ p ^ k = 1) : ∀ m ∈ M, x * m = m * x := by
  have hxp : x ^ p = 1 := pow_prime_eq_one_of_card_lt (by omega) hx
  exact commute_of_pow_prime_of_solvable_normal hp5 hσ hO M hM hM2 hxp

theorem le_center_of_solvable_normal {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {σ : Type}
    [Fintype σ] [DecidableEq σ] (hσ : Fintype.card σ ≤ 4) {G : Subgroup (GL σ (ZMod p))}
    (hG : oPPrimeHull p G = G) (hO : CFSG.pCore p ↥G = ⊥) (M : Subgroup ↥G) [M.Normal]
    (hM : IsSolvable ↥M)
    (hM2 : p = 5 → ∀ S : Sylow 2 ↥M, ∀ a ∈ (S : Subgroup ↥M), ∀ b ∈ (S : Subgroup ↥M),
      a * b = b * a) :
    M ≤ Subgroup.center ↥G := by
  have hle : oPPrimeHull p (⊤ : Subgroup ↥G) ≤ Subgroup.centralizer (M : Set ↥G) := by
    rw [oPPrimeHull, Subgroup.closure_le]
    rintro x ⟨-, k, hk⟩
    have hxk : x ^ p ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    exact Subgroup.mem_centralizer_iff.2 fun m hm =>
      (commute_of_solvable_normal hp5 hσ hO M hM hM2 hxk m hm).symm
  rw [oPPrimeHull_top_of_eq hG] at hle
  intro m hm
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top g)) m hm).symm

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
