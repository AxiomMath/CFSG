module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.LocalAnalysis.GLTheoremA.T173X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {l : ℕ} {U : Fin l → Submodule F V}
  {ρ : Fin l → ↥(orthDerived Q)} {i j : Fin l} {A : Subgroup ↥(orthDerived Q)} {d : ↥(orthDerived Q)}

theorem oddOrderIsometry_of_std (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : IsStdElt p A d) : OddOrderIsometry Q p (d : V ≃ₗ[F] V) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hord : orderOf d = p := orderOf_eq_prime hd.2.2.1 hd.2.1
  exact oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord

theorem mem_zpowers_of_fixed_layer
    (hcd : A ⊓ Subgroup.centralizer (stdLayer d : Set ↥(orthDerived Q)) = Subgroup.zpowers d)
    {P : Submodule F V} (hP : (QuadraticMap.polarBilin (Q.comp P.subtype)).Nondegenerate)
    {e : ↥(orthDerived Q)} (he : e ∈ A) (hfix : ∀ g ∈ stdLayer d, ∀ v ∈ P, (g : V ≃ₗ[F] V) v = v)
    (heP : ∀ x ∈ P, (e : V ≃ₗ[F] V) x ∈ P) (hperp : ∀ x ∈ polarPerp Q P, (e : V ≃ₗ[F] V) x = x) :
    e ∈ Subgroup.zpowers d := by
  have hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  have : e ∈ A ⊓ Subgroup.centralizer (stdLayer d : Set ↥(orthDerived Q)) :=
    Subgroup.mem_inf.2 ⟨he, Subgroup.mem_centralizer_iff.2 fun g hg =>
      Subtype.ext (commute_of_apply_eq hP (hOg g) (hfix g hg) heP hperp)⟩
  rwa [hcd] at this

theorem fixes_of_layer_su {h k : Polynomial F} (hk : k ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hkh : k ≠ h)
    (hkh' : k ≠ reciprocalPolynomial h)
    (hL : stdLayer d = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    ∀ g ∈ stdLayer d, ∀ v ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap k, (g : V ≃ₗ[F] V) v = v := by
  intro g hg v hv
  rw [hL] at hg
  exact apply_eq_of_mem_specialBlock hk hkh hkh' (Subgroup.mem_subgroupOf.1 hg) hv

theorem fixes_of_layer_omega {G : Subgroup (V ≃ₗ[F] V)} (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    {k : Polynomial F} (hk : k ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hk1 : k ≠ X - 1)
    (hL : stdLayer d = G.subgroupOf (orthDerived Q)) :
    ∀ g ∈ stdLayer d, ∀ v ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap k, (g : V ≃ₗ[F] V) v = v := by
  intro g hg v hv
  rw [hL] at hg
  exact apply_eq_of_mem_supportedFixedDerived hk hk1 (hGle (Subgroup.mem_subgroupOf.1 hg)) hv

theorem le_primaryComponent_of_ne (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {h : Polynomial F}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : stdLayer d = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    ∀ k, k ≠ i → k ≠ j → U k ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  intro k hki hkj
  by_contra hk
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) := oddOrderIsometry_of_std hQ hp hp2 hd
  have hself : reciprocalPolynomial h = h := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1
  obtain ⟨k', hk', hUk'⟩ :=
    hM.frame.exists_le_primaryComponent hp hp2 hpq (hM.le_torus hd.1) k
  have hk'h : k' ≠ h := fun hkh => hk (hkh ▸ hUk')
  have hfix : ∀ g ∈ stdLayer d, ∀ v ∈ U k, (g : V ≃ₗ[F] V) v = v := by
    intro g hg v hv
    exact fixes_of_layer_su hk' hk'h (by rw [hself]; exact hk'h) hL g hg v (hUk' hv)
  have hρd : ρ k ∈ Subgroup.zpowers d :=
    mem_zpowers_of_fixed_layer hd.2.2.2.2 (hM.frame.nondeg k) (hM.rho_mem hki hkj) hfix
      (hM.frame.maps_to k) (hM.frame.apply_of_perp k)
  obtain ⟨i', hi'⟩ :=
    hM.frame.exists_le_primaryComponent_of_mem hp hp2 hpq (hM.le_torus hd.1) hh hh1
  have hi'k : i' ≠ k := fun hik => hk (hik ▸ hi')
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i') (hM.frame.finrank_eq i')
  exact hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 (hi' hv)
    ((hM.frame.apply_eq_of_mem_zpowers hp (hM.le_torus hd.1) hρd) i' hi'k v hv))

private theorem le_primaryComponent_pair_aux1 (hM : IsMixedFrame Q p U ρ i j A) :
    (∀ x ∈ U i ⊔ U j, ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈ U i ⊔ U j) ∧
      ∀ x ∈ polarPerp Q (U i ⊔ U j), ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  constructor
  · intro x hx
    obtain ⟨xi, hxi, xj, hxj, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : (ρ i : V ≃ₗ[F] V) xi ∈ U i := hM.frame.maps_to i xi hxi
    have h2 : (ρ j : V ≃ₗ[F] V) xj ∈ U j := hM.frame.maps_to j xj hxj
    have h3 : (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) xj) = (ρ j : V ≃ₗ[F] V) xj :=
      hM.frame.apply_of_perp i _ (mem_polarPerp_iff.2 fun y hy => hM.frame.perp i j hM.ne y hy _ h2)
    have h4 : (ρ j : V ≃ₗ[F] V) xi = xi :=
      hM.frame.apply_of_perp j xi (mem_polarPerp_iff.2 fun y hy =>
        hM.frame.perp j i (Ne.symm hM.ne) y hy xi hxi)
    show (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) (xi + xj)) ∈ U i ⊔ U j
    rw [map_add, h4, map_add, h3]
    exact Submodule.add_mem_sup h1 h2
  · intro x hx
    have hxi : x ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy =>
      mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy)
    have hxj : x ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy =>
      mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy)
    show (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) x) = x
    rw [hM.frame.apply_of_perp j x hxj, hM.frame.apply_of_perp i x hxi]

private theorem le_primaryComponent_pair_aux2 (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {h : Polynomial F}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : stdLayer d = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hcon : ¬ U i ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hconj : ¬ U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) :
    ρ i * ρ j ∈ Subgroup.zpowers d := by
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) := oddOrderIsometry_of_std hQ hp hp2 hd
  have hself : reciprocalPolynomial h = h := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1
  obtain ⟨ki, hki, hUki⟩ := hM.frame.exists_le_primaryComponent hp hp2 hpq (hM.le_torus hd.1) i
  obtain ⟨kj, hkj, hUkj⟩ := hM.frame.exists_le_primaryComponent hp hp2 hpq (hM.le_torus hd.1) j
  have hkih : ki ≠ h := fun e => hcon (e ▸ hUki)
  have hkjh : kj ≠ h := fun e => hconj (e ▸ hUkj)
  have hfixi : ∀ g ∈ stdLayer d, ∀ v ∈ U i, (g : V ≃ₗ[F] V) v = v := by
    intro g hg v hv
    exact fixes_of_layer_su hki hkih (by rw [hself]; exact hkih) hL g hg v (hUki hv)
  have hfixj : ∀ g ∈ stdLayer d, ∀ v ∈ U j, (g : V ≃ₗ[F] V) v = v := by
    intro g hg v hv
    exact fixes_of_layer_su hkj hkjh (by rw [hself]; exact hkjh) hL g hg v (hUkj hv)
  have hfixP : ∀ g ∈ stdLayer d, ∀ v ∈ U i ⊔ U j, (g : V ≃ₗ[F] V) v = v := by
    intro g hg v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hfixi g hg x hx, hfixj g hg y hy]
  have hP : (QuadraticMap.polarBilin (Q.comp (U i ⊔ U j).subtype)).Nondegenerate := by
    have e : (⨆ k ∈ ({i, j} : Finset (Fin l)), U k : Submodule F V) = U i ⊔ U j := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [← e]
    exact hM.frame.toIsPlaneSystem.nondeg_biSup ({i, j} : Finset (Fin l))
  obtain ⟨heP, hperp⟩ := le_primaryComponent_pair_aux1 hM
  exact mem_zpowers_of_fixed_layer hd.2.2.2.2 hP (hM.pair_mem) hfixP heP hperp

private theorem le_primaryComponent_pair_aux3 (hM : IsMixedFrame Q p U ρ i j A) (hp : p.Prime)
    (hd : IsStdElt p A d) (hπmem : ρ i * ρ j ∈ Subgroup.zpowers d) :
    d ∈ Subgroup.zpowers (ρ i * ρ j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hπ1 : ρ i * ρ j ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hM.frame.finrank_eq i)
    have hju : (ρ j : V ≃ₗ[F] V) u = u :=
      hM.frame.apply_of_perp j u (mem_polarPerp_iff.2 fun y hy =>
        hM.frame.perp j i (Ne.symm hM.ne) y hy u hu)
    have hthis : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) u = u := by rw [h1]; rfl
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hju] at hthis
    exact hu0 (hM.frame.eq_zero_of_apply_eq i u hu hthis)
  have hord_d : orderOf d = p := orderOf_eq_prime hd.2.2.1 hd.2.1
  have hdvd : orderOf (ρ i * ρ j) ∣ p := hord_d ▸ orderOf_dvd_of_mem_zpowers hπmem
  have hordπ : orderOf (ρ i * ρ j) = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf (ρ i * ρ j)) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hπ1
    · exact h
  have hle : Subgroup.zpowers (ρ i * ρ j) ≤ Subgroup.zpowers d := (Subgroup.zpowers_le).2 hπmem
  have hcard : Nat.card (Subgroup.zpowers d) ≤ Nat.card (Subgroup.zpowers (ρ i * ρ j)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord_d, hordπ]
  have heq : Subgroup.zpowers (ρ i * ρ j) = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact Subgroup.mem_zpowers d

private theorem le_primaryComponent_pair_aux4 (hM : IsMixedFrame Q p U ρ i j A)
    (hπd : d ∈ Subgroup.zpowers (ρ i * ρ j)) :
    ∀ m, m ≠ i → m ≠ j → ∀ v ∈ U m, (d : V ≃ₗ[F] V) v = v := by
  intro m hmi hmj v hv
  have hπv : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) v = v := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    have hvi : v ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy =>
      hM.frame.perp i m (fun h => hmi h.symm) y hy v hv
    have hvj : v ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy =>
      hM.frame.perp j m (fun h => hmj h.symm) y hy v hv
    rw [hM.frame.apply_of_perp j v hvj, hM.frame.apply_of_perp i v hvi]
  have hstab : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ MulAction.stabilizer (V ≃ₗ[F] V) v :=
    (MulAction.mem_stabilizer_iff).2 hπv
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hπd
  have hmem : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers (((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V)) := by
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [← Subgroup.coe_zpow, hn]
  exact (MulAction.mem_stabilizer_iff).1
    ((Subgroup.zpowers_le (H := MulAction.stabilizer (V ≃ₗ[F] V) v)).2 hstab hmem)

theorem le_primaryComponent_pair (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {h : Polynomial F}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : stdLayer d = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hout : ∀ k, k ≠ i → k ≠ j → U k ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) :
    U i ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h ∧ U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  have hi : U i ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
    by_contra hcon
    have hconj : ¬ U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
      intro hle
      apply hcon
      intro x hx
      exact mem_primaryComponent.mpr
        ((hM.aeval_eq_zero_iff hp hp2 hpq hd.1 h).mpr
          (fun y hy => mem_primaryComponent.mp (hle hy)) x hx)
    have hπmem := le_primaryComponent_pair_aux2 hM hQ hp hp2 hpq hd hh hh1 hL hcon hconj
    have hπd := le_primaryComponent_pair_aux3 hM hp hd hπmem
    have htriv := le_primaryComponent_pair_aux4 hM hπd
    obtain ⟨i', hi'⟩ :=
      hM.frame.exists_le_primaryComponent_of_mem hp hp2 hpq (hM.le_torus hd.1) hh hh1
    have hi'i : i' ≠ i := fun e => hcon (e ▸ hi')
    have hi'j : i' ≠ j := fun e => hconj (e ▸ hi')
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i') (hM.frame.finrank_eq i')
    exact hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 (hi' hv) (htriv i' hi'i hi'j v hv))
  have hae : ∀ x ∈ U i, Polynomial.aeval (d : V ≃ₗ[F] V).toLinearMap h x = 0 :=
    fun x hx => mem_primaryComponent.mp (hi hx)
  have haej := (hM.aeval_eq_zero_iff hp hp2 hpq hd.1 h).mp hae
  exact ⟨hi, fun y hy => mem_primaryComponent.mpr (haej y hy)⟩

theorem fullSupport_of_su (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {h : Polynomial F}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : stdLayer d = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    ∀ k, U k ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  have hout := le_primaryComponent_of_ne hM hQ hdim hl hp hp2 hpq hd hh hh1 hL
  obtain ⟨hi, hj⟩ := le_primaryComponent_pair hM hQ hdim hl hp hp2 hpq hd hh hh1 hL hout
  intro k
  by_cases hki : k = i
  · exact hki ▸ hi
  by_cases hkj : k = j
  · exact hkj ▸ hj
  exact hout k hki hkj

theorem weightOne_of_omega (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {G : Subgroup (V ≃ₗ[F] V)}
    (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hGdim : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) ≤ 4 ∨ G = supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : stdLayer d = G.subgroupOf (orthDerived Q)) {k : Fin l} (hki : k ≠ i) (hkj : k ≠ j)
    (hk : ¬ ∀ x ∈ U k, (d : V ≃ₗ[F] V) x = x) :
    d ∈ Subgroup.zpowers (ρ k) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U k) ∧
      stdLayer d = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
  obtain ⟨k', hk', hUk'⟩ := hM.frame.exists_le_primaryComponent hp hp2 hpq (hM.le_torus hd.1) k
  have hk'1 : k' ≠ X - 1 := by
    rintro rfl
    refine hk fun x hx => ?_
    have hx' := hUk' hx
    rw [← fixedSpace_eq_primaryComponent] at hx'
    exact mem_fixedSpace.1 hx'
  have hfixk : ∀ g ∈ stdLayer d, ∀ v ∈ U k, (g : V ≃ₗ[F] V) v = v :=
    fun g hg v hv => fixes_of_layer_omega hGle hk' hk'1 hL g hg v (hUk' hv)
  have hρd : ρ k ∈ Subgroup.zpowers d :=
    mem_zpowers_of_fixed_layer hd.2.2.2.2 (hM.frame.nondeg k) (hM.rho_mem hki hkj) hfixk
      (hM.frame.maps_to k) (hM.frame.apply_of_perp k)
  have htriv : ∀ m, m ≠ k → ∀ x ∈ U m, (d : V ≃ₗ[F] V) x = x :=
    hM.frame.apply_eq_of_mem_zpowers hp (hM.le_torus hd.1) hρd
  have hdz : d ∈ Subgroup.zpowers (ρ k) :=
    hM.frame.mem_zpowers_of_apply_eq (hM.le_torus hd.1) k htriv
  have hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U k) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hdz
    have hzp : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers (ρ k : V ≃ₗ[F] V) :=
      Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hn]; simp⟩
    have hord' : orderOf (ρ k : V ≃ₗ[F] V) = p := by
      rw [Subgroup.orderOf_coe]
      exact hM.frame.orderOf_eq k
    have hd1' : (d : V ≃ₗ[F] V) ≠ 1 := fun h1 => hd.2.1 (Subtype.ext h1)
    rw [fixedSpace_eq_of_mem_zpowers hp hord' hzp hd1']
    exact hM.frame.fixedSpace_eq_polarPerp k
  have hfd : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * (l - 1) := by
    rw [hfs, finrank_polarPerp hQ (U k), hM.frame.finrank_eq k, hdim]
    omega
  have hGeq : G = supportedFixedDerived Q (d : V ≃ₗ[F] V) :=
    hGdim.resolve_left (by rw [hfd]; omega)
  exact ⟨hdz, hfs, by rw [hL, hGeq]⟩

private theorem mem_zpowers_pair_aux1 (hM : IsMixedFrame Q p U ρ i j A)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d)
    {G : Subgroup (V ≃ₗ[F] V)} (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : stdLayer d = G.subgroupOf (orthDerived Q)) {m : Fin l}
    (hm : ¬ ∀ x ∈ U m, (d : V ≃ₗ[F] V) x = x) :
    ∀ g ∈ stdLayer d, ∀ v ∈ U m, (g : V ≃ₗ[F] V) v = v := by
  intro g hg v hv
  obtain ⟨k, hk, hUk⟩ := hM.frame.exists_le_primaryComponent hp hp2 hpq (hM.le_torus hd.1) m
  have hk1 : k ≠ X - 1 := by
    rintro rfl
    refine hm fun x hx => ?_
    have hx' := hUk hx
    rw [← fixedSpace_eq_primaryComponent] at hx'
    exact mem_fixedSpace.1 hx'
  exact fixes_of_layer_omega hGle hk hk1 hL g hg v (hUk hv)

theorem mem_zpowers_pair (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {G : Subgroup (V ≃ₗ[F] V)}
    (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V)) (hL : stdLayer d = G.subgroupOf (orthDerived Q))
    (hall : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ U k, (d : V ≃ₗ[F] V) x = x) :
    d ∈ Subgroup.zpowers (ρ i * ρ j) := by
  have hni : ¬ ∀ x ∈ U i, (d : V ≃ₗ[F] V) x = x := by
    intro hi
    have hj : ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x :=
      (hM.apply_eq_iff hp hp2 hpq hd.1).mp hi
    refine hd.2.1 (hM.frame.eq_one_of_forall_apply_eq (hM.le_torus hd.1) ?_)
    intro m x hx
    by_cases hmi : m = i
    · subst hmi; exact hi x hx
    by_cases hmj : m = j
    · subst hmj; exact hj x hx
    exact hall m hmi hmj x hx
  have hnj : ¬ ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x := by
    intro hj
    exact hni ((hM.apply_eq_iff hp hp2 hpq hd.1).mpr hj)
  have hfixi := mem_zpowers_pair_aux1 hM hp hp2 hpq hd hGle hL hni
  have hfixj := mem_zpowers_pair_aux1 hM hp hp2 hpq hd hGle hL hnj
  have hfixP : ∀ g ∈ stdLayer d, ∀ v ∈ U i ⊔ U j, (g : V ≃ₗ[F] V) v = v := by
    intro g hg v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hfixi g hg x hx, hfixj g hg y hy]
  have hP : (QuadraticMap.polarBilin (Q.comp (U i ⊔ U j).subtype)).Nondegenerate := by
    have he : (⨆ m ∈ ({i, j} : Finset (Fin l)), U m : Submodule F V) = U i ⊔ U j := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [← he]
    exact hM.frame.toIsPlaneSystem.nondeg_biSup ({i, j} : Finset (Fin l))
  obtain ⟨heP, hperp⟩ := le_primaryComponent_pair_aux1 hM
  exact le_primaryComponent_pair_aux3 hM hp hd
    (mem_zpowers_of_fixed_layer hd.2.2.2.2 hP (hM.pair_mem) hfixP heP hperp)

private theorem fixedSpace_pair_aux1 (hM : IsMixedFrame Q p U ρ i j A) (hp : p.Prime) :
    orderOf (ρ i * ρ j) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : ρ i * ρ j ∈ Subgroup.closure (Set.range ρ) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) (Subgroup.subset_closure ⟨j, rfl⟩)
  have hp1 : (ρ i * ρ j) ^ p = 1 := hM.frame.isElemAbelian.2 _ hmem
  have hne : ρ i * ρ j ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hM.frame.finrank_eq i)
    have hju : (ρ j : V ≃ₗ[F] V) u = u :=
      hM.frame.apply_of_perp j u (mem_polarPerp_iff.2 fun y hy =>
        hM.frame.perp j i (Ne.symm hM.ne) y hy u hu)
    have hthis : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) u = u := by rw [h1]; rfl
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hju] at hthis
    exact hu0 (hM.frame.eq_zero_of_apply_eq i u hu hthis)
  exact orderOf_eq_prime hp1 hne

private theorem fixedSpace_pair_aux2 (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    fixedSpace ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ≤ polarPerp Q (U i ⊔ U j) := by
  intro x hx
  have hP : (QuadraticMap.polarBilin (Q.comp (U i ⊔ U j).subtype)).Nondegenerate := by
    have e : (⨆ k ∈ ({i, j} : Finset (Fin l)), U k : Submodule F V) = U i ⊔ U j := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [← e]
    exact hM.frame.toIsPlaneSystem.nondeg_biSup ({i, j} : Finset (Fin l))
  have hxsup : x ∈ (U i ⊔ U j) ⊔ polarPerp Q (U i ⊔ U j) := by
    rw [(isCompl_polarPerp (Q := Q) hP).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hxsup
  have hwfix : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) w = w :=
    (le_primaryComponent_pair_aux1 hM).2 w hw
  have hufix : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) u = u := by
    have h := mem_fixedSpace.1 hx
    rw [map_add, hwfix] at h
    exact add_right_cancel h
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hu
  have hx₁perp : x₁ ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy =>
    hM.frame.perp j i (Ne.symm hM.ne) y hy x₁ hx₁
  have hρjx₂perp : (ρ j : V ≃ₗ[F] V) x₂ ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy =>
    hM.frame.perp i j hM.ne y hy ((ρ j : V ≃ₗ[F] V) x₂) (hM.frame.maps_to j x₂ hx₂)
  have hπ : (ρ i : V ≃ₗ[F] V) x₁ + (ρ j : V ≃ₗ[F] V) x₂ = x₁ + x₂ := by
    have h := hufix
    rw [map_add, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hM.frame.apply_of_perp j x₁ hx₁perp,
      hM.frame.apply_of_perp i ((ρ j : V ≃ₗ[F] V) x₂) hρjx₂perp] at h
    exact h
  have hdisj : Disjoint (U i) (U j) := by
    have h := hM.frame.toIsPlaneSystem.disjoint_biSup (Q := Q) (a := i) (s := {j})
      (by simpa using hM.ne)
    simpa using h
  have hz : (ρ i : V ≃ₗ[F] V) x₁ - x₁ = x₂ - (ρ j : V ≃ₗ[F] V) x₂ := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm x₂ x₁]
    exact hπ
  have hzmem : (ρ i : V ≃ₗ[F] V) x₁ - x₁ ∈ U i ⊓ U j :=
    Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (hM.frame.maps_to i x₁ hx₁) hx₁,
      hz ▸ Submodule.sub_mem _ hx₂ (hM.frame.maps_to j x₂ hx₂)⟩
  have hz0 : (ρ i : V ≃ₗ[F] V) x₁ - x₁ = 0 := by
    have hbot : (ρ i : V ≃ₗ[F] V) x₁ - x₁ ∈ (⊥ : Submodule F V) := by
      rwa [disjoint_iff.mp hdisj] at hzmem
    exact (Submodule.mem_bot F).mp hbot
  have hx₁fix : (ρ i : V ≃ₗ[F] V) x₁ = x₁ := sub_eq_zero.mp hz0
  have hx₂fix : (ρ j : V ≃ₗ[F] V) x₂ = x₂ := by
    have hz0' : x₂ - (ρ j : V ≃ₗ[F] V) x₂ = 0 := by rw [← hz]; exact hz0
    exact (sub_eq_zero.mp hz0').symm
  have hx₁0 : x₁ = 0 := hM.frame.eq_zero_of_apply_eq i x₁ hx₁ hx₁fix
  have hx₂0 : x₂ = 0 := hM.frame.eq_zero_of_apply_eq j x₂ hx₂ hx₂fix
  simpa [hx₁0, hx₂0] using hw

theorem fixedSpace_pair (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hp : p.Prime)
    (hdz : d ∈ Subgroup.zpowers (ρ i * ρ j)) (hd1 : d ≠ 1) :
    fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j) ∧
      Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) + 4 = 2 * l := by
  have hordπ := fixedSpace_pair_aux1 hM hp
  have hfspi : fixedSpace ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      polarPerp Q (U i ⊔ U j) :=
    le_antisymm (fixedSpace_pair_aux2 hM hQ)
      fun x hx => mem_fixedSpace.2 ((le_primaryComponent_pair_aux1 hM).2 x hx)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hdz
  have hzp : (d : V ≃ₗ[F] V) ∈
      Subgroup.zpowers ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
    Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hn]; simp⟩
  have hordπ' : orderOf ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) = p := by
    rw [Subgroup.orderOf_coe]; exact hordπ
  have hd1' : (d : V ≃ₗ[F] V) ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hfsd : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j) := by
    rw [fixedSpace_eq_of_mem_zpowers hp hordπ' hzp hd1', hfspi]
  have hfin : Module.finrank F ↥(U i ⊔ U j) = 4 := by
    have e : (⨆ k ∈ ({i, j} : Finset (Fin l)), U k : Submodule F V) = U i ⊔ U j := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [← e, hM.frame.toIsPlaneSystem.finrank_biSup ({i, j} : Finset (Fin l)),
      Finset.card_pair hM.ne]
  have h4 : 4 ≤ 2 * l := by
    have hle := Submodule.finrank_le (U i ⊔ U j)
    rw [hfin, hdim] at hle
    exact hle
  refine ⟨hfsd, ?_⟩
  rw [hfsd, finrank_polarPerp hQ (U i ⊔ U j), hdim, hfin]
  omega

private theorem not_quasisimple_of_four_aux1 (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl4 : l = 4) :
    (QuadraticMap.polarBilin (Q.comp (polarPerp Q (U i ⊔ U j)).subtype)).Nondegenerate ∧
      Module.finrank F (polarPerp Q (U i ⊔ U j)) = 4 ∧
      IsPlusType (Q.comp (polarPerp Q (U i ⊔ U j)).subtype) := by
  have hreg : (QuadraticMap.polarBilin (Q.comp (U i ⊔ U j).subtype)).Nondegenerate := by
    have e : (⨆ k ∈ ({i, j} : Finset (Fin l)), U k : Submodule F V) = U i ⊔ U j := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [← e]
    exact hM.frame.toIsPlaneSystem.nondeg_biSup ({i, j} : Finset (Fin l))
  have hfin : Module.finrank F ↥(U i ⊔ U j) = 4 := by
    have e : (⨆ k ∈ ({i, j} : Finset (Fin l)), U k : Submodule F V) = U i ⊔ U j := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [← e, hM.frame.toIsPlaneSystem.finrank_biSup ({i, j} : Finset (Fin l)),
      Finset.card_pair hM.ne]
  have hdimW : Module.finrank F (polarPerp Q (U i ⊔ U j)) = 4 := by
    rw [finrank_polarPerp hQ (U i ⊔ U j), hdim, hfin]
    omega
  refine ⟨nondeg_comp_polarPerp hQ hreg, hdimW, ?_⟩
  have hle : (⨆ k ∈ ({i, j} : Finset (Fin l))ᶜ, U k) ≤ polarPerp Q (U i ⊔ U j) := by
    refine iSup₂_le fun k hk x hx => mem_polarPerp_iff.2 fun y hy => ?_
    have hk' : k ∉ ({i, j} : Finset (Fin l)) := Finset.mem_compl.1 hk
    have hki : k ≠ i := fun h => hk' (by rw [h]; exact Finset.mem_insert_self i {j})
    have hkj : k ≠ j := fun h =>
      hk' (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
    obtain ⟨yi, hyi, yj, hyj, rfl⟩ := Submodule.mem_sup.1 hy
    rw [polar_add_left, hM.frame.perp i k (Ne.symm hki) yi hyi x hx,
      hM.frame.perp j k (Ne.symm hkj) yj hyj x hx, add_zero]
  have hcard : (({i, j} : Finset (Fin l))ᶜ).card = 2 := by
    rw [Finset.card_compl, Finset.card_pair hM.ne, Fintype.card_fin, hl4]
  have heq : (⨆ k ∈ ({i, j} : Finset (Fin l))ᶜ, U k : Submodule F V) =
      polarPerp Q (U i ⊔ U j) := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [hM.frame.toIsPlaneSystem.finrank_biSup ({i, j} : Finset (Fin l))ᶜ, hcard, hdimW]
  rw [← heq]
  exact (hM.frame.toIsPlaneSystem.isPlusType_biSup_iff _).2 (by rw [hcard]; exact even_two)

private theorem not_quasisimple_of_four_aux2 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {W : Submodule F V} (hW : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : Module.finrank F W = 4) (hWplus : IsPlusType (Q.comp W.subtype)) (hF2 : Nat.card F = 2) :
    Nat.card ↥(orthDerived (Q.comp W.subtype)) ∣ 2 ^ 3 * 3 ^ 2 := by
  have he : Nonempty ((Q.comp W.subtype).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadPlus 2 F)) := by
    rcases exists_isometry_quadPlus_or_quadMinus (Q.comp W.subtype) hW (n := 2) (by omega)
      (by rw [hWdim]) with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
    · exact ⟨e⟩
    · exact absurd ((isPlusType_congr e).1 hWplus)
        (not_isPlusType_quadMinus (n := 2) (by omega) hirr)
  obtain ⟨e⟩ := he
  have h72 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 2 F)) : ℤ) = 72 := by
    rw [natCard_orthogonalGroup_quadPlus (K := F) 1, hF2]
    norm_num [Finset.Icc_self]
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)) = 72 := by
    rw [natCard_orthogonalGroup_congr e]
    exact_mod_cast h72
  have hdiv : Nat.card ↥(orthDerived (Q.comp W.subtype)) ∣
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (orthDerived_le_orthogonalGroup (Q := Q.comp W.subtype))).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hO] at hdiv
  exact hdiv.trans (by norm_num)

theorem not_quasisimple_of_four (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl4 : l = 4)
    (hF2 : Nat.card F = 2) (hp : p.Prime) (hp2 : p ≠ 2) (hd : IsStdElt p A d)
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j)) {G : Subgroup (V ≃ₗ[F] V)}
    (hGq : CFSG.IsQuasisimple ↥G) (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V)) : False := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite ↥G := Finite.of_injective (fun g : ↥G => (g : V ≃ₗ[F] V)) Subtype.coe_injective
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) := oddOrderIsometry_of_std hQ hp hp2 hd
  obtain ⟨hWreg, hWdim, hWplus⟩ := not_quasisimple_of_four_aux1 hM hQ hdim hl4
  have hdvd : Nat.card ↥(orthDerived (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)) ∣
      2 ^ 3 * 3 ^ 2 := by
    rw [hfs]
    exact not_quasisimple_of_four_aux2 hQ hWreg hWdim hWplus hF2
  have hsd : Nat.card ↥(supportedFixedDerived Q (d : V ≃ₗ[F] V)) =
      Nat.card ↥(orthDerived (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)) :=
    Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv
  have hcardG : Nat.card ↥G ∣ Nat.card ↥(supportedFixedDerived Q (d : V ≃ₗ[F] V)) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGle).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvdG : Nat.card ↥G ∣ 2 ^ 3 * 3 ^ 2 := hcardG.trans (hsd.symm ▸ hdvd)
  have hsolv : Group.IsSolvable ↥G :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three hdvdG
  haveI : IsSimpleGroup (↥G ⧸ Subgroup.center ↥G) := hGq.2.1
  haveI : Nontrivial ↥G := (QuotientGroup.mk'_surjective (Subgroup.center ↥G)).nontrivial
  haveI : Group.IsPerfect ↥G := hGq.1
  exact Group.IsPerfect.not_isSolvable ↥G hsolv

theorem pair_of_omega (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hq : l = 4 → Nat.card F = 2) (hd : IsStdElt p A d)
    {G : Subgroup (V ≃ₗ[F] V)} (hGq : CFSG.IsQuasisimple ↥G) (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hGdim : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) ≤ 4 ∨ G = supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : stdLayer d = G.subgroupOf (orthDerived Q))
    (hall : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ U k, (d : V ≃ₗ[F] V) x = x) :
    5 ≤ l ∧ d ∈ Subgroup.zpowers (ρ i * ρ j) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j) ∧
      stdLayer d = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
  have hdz := mem_zpowers_pair hM hQ hdim hl hp hp2 hpq hd hGle hL hall
  obtain ⟨hfs, hfd⟩ := fixedSpace_pair hM hQ hdim hp hdz hd.2.1
  by_cases hl5 : 5 ≤ l
  · have hGeq : G = supportedFixedDerived Q (d : V ≃ₗ[F] V) := hGdim.resolve_left (by omega)
    exact ⟨hl5, hdz, hfs, by rw [hL, hGeq]⟩
  · exact (not_quasisimple_of_four hM hQ hdim (by omega) (hq (by omega)) hp hp2 hd hfs hGq hGle).elim

theorem standard_trichotomy (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hq : l = 4 → Nat.card F = 2) (hd : IsStdElt p A d) :
    (∃ k, k ≠ i ∧ k ≠ j ∧ d ∈ Subgroup.zpowers (ρ k) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U k) ∧
        stdLayer d = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ∨
    (5 ≤ l ∧ d ∈ Subgroup.zpowers (ρ i * ρ j) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j) ∧
        stdLayer d = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ∨
    (∃ h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap, h ≠ X - 1 ∧
        (∀ k, U k ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) ∧
        stdLayer d = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf d = p := orderOf_eq_prime hd.2.2.1 hd.2.1
  rcases comp_cases_orthDerived_gen hQ hp hp2 hpq hord hd.2.2.2.1 with
    ⟨h, hh, hh1, hquasi, hL⟩ | ⟨G, hGq, hGle, -, hGdim, hL⟩
  · exact Or.inr (Or.inr ⟨h, hh, hh1, fullSupport_of_su hM hQ hdim hl hp hp2 hpq hd hh hh1 hL, hL, hquasi⟩)
  · by_cases hex : ∃ k, k ≠ i ∧ k ≠ j ∧ ¬ ∀ x ∈ U k, (d : V ≃ₗ[F] V) x = x
    · obtain ⟨k, hki, hkj, hk⟩ := hex
      exact Or.inl ⟨k, hki, hkj, weightOne_of_omega hM hQ hdim hl hp hp2 hpq hd hGle hGdim hL hki hkj hk⟩
    · push Not at hex
      exact Or.inr (Or.inl (pair_of_omega hM hQ hdim hl hp hp2 hpq hq hd hGq hGle hGdim hL hex))

end CFSG.LocalAnalysis.GLTheoremA.T173M

end
