module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentRot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.K159

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem mem_zpowers_of_commute_of_frame {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} {L : Subgroup ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer (L : Set ↥(orthDerived Q)) = Subgroup.zpowers d) (j : Fin m)
    (h : ∀ g ∈ L, g * e j = e j * g) : e j ∈ Subgroup.zpowers d := by
  have : e j ∈ Bb ⊓ Subgroup.centralizer (L : Set ↥(orthDerived Q)) :=
    Subgroup.mem_inf.2 ⟨hF.mem j, Subgroup.mem_centralizer_iff.2 h⟩
  rwa [hcd] at this

theorem exists_planeFrame_of_pow_le_card (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {Bb : Subgroup ↥(orthDerived Q)} (hBb : IsElemAbelian p Bb) (hcard : p ^ n ≤ Nat.card Bb) :
    Nat.card Bb = p ^ n ∧ ∃ (U : Fin n → Submodule F V) (e : Fin n → ↥(orthDerived Q)),
      IsPlaneFrame Q p U e Bb := by
  have hreg : RegOn Q ⊤ := fun u _ h =>
    hQ.1 u fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using h w Submodule.mem_top
  obtain ⟨r, U, hU⟩ :=
    exists_planeDecomp hQ hp hp2 hpq hBb ⊤ hreg fun _ _ _ _ => Submodule.mem_top
  have hle : p ^ n ≤ p ^ r := hcard.trans (hU.card_le_pow hBb hp)
  have hnr : n ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have hrn : r ≤ n := by
    have h1 := hU.toIsPlaneSystem.finrank_biSup Finset.univ
    have h2 := Submodule.finrank_le (⨆ j ∈ (Finset.univ : Finset (Fin r)), U j)
    rw [h1, Finset.card_univ, Fintype.card_fin, hdim] at h2
    omega
  have hr : r = n := le_antisymm hrn hnr
  subst n
  have hcard' : Nat.card Bb = p ^ r := le_antisymm (hU.card_le_pow hBb hp) hcard
  obtain ⟨e, he⟩ := hU.exists_planeFrame hBb hp hcard'
  exact ⟨hcard', U, e, he⟩

theorem le_primaryComponent_of_eq_specialBlock (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {m : ℕ} {U : Fin m → Submodule F V} {e : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) {L : Subgroup ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer (L : Set ↥(orthDerived Q)) = Subgroup.zpowers d)
    (hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V)) {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : L = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  have hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  intro j
  by_contra hj
  have hself := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1
  obtain ⟨k, hk, hUk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd j
  have hkh : k ≠ h := fun hkh => hj (hkh ▸ hUk)
  have hfix : ∀ g ∈ specialBlock Q (d : V ≃ₗ[F] V) h, ∀ v ∈ U j, g v = v := fun g hg v hv =>
    apply_eq_of_mem_specialBlock hk hkh (by rw [hself]; exact hkh) hg (hUk hv)
  have hej : e j ∈ Subgroup.zpowers d := by
    refine mem_zpowers_of_commute_of_frame hF hcd j fun g hg => ?_
    rw [hL] at hg
    have hgs := Subgroup.mem_subgroupOf.1 hg
    exact Subtype.ext (commute_of_apply_eq (hF.nondeg j) (hOg g) (hfix _ hgs)
      (hF.maps_to j) (hF.apply_of_perp j))
  obtain ⟨i, hi⟩ := hF.exists_le_primaryComponent_of_mem hp hp2 hpq hd hh hh1
  have hij : i ≠ j := fun hij => hj (hij ▸ hi)
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hF.finrank_eq i)
  exact hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 (hi hv)
    (hF.apply_eq_of_mem_zpowers hp hd hej i hij v hv))

theorem apply_eq_of_le_supportedFixedDerived (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {m : ℕ} {U : Fin m → Submodule F V} {e : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) {L : Subgroup ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer (L : Set ↥(orthDerived Q)) = Subgroup.zpowers d)
    {G : Subgroup (V ≃ₗ[F] V)} (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : L = G.subgroupOf (orthDerived Q)) :
    ∀ j, ¬ (∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) →
      ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v := by
  have hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  intro j hj
  have hfixj : ∀ g ∈ supportedFixedDerived Q (d : V ≃ₗ[F] V), ∀ v ∈ U j, g v = v := by
    intro g hg v hv
    obtain ⟨k, hk, hUk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd j
    have hk1 : k ≠ X - 1 := by
      rintro rfl
      refine hj fun w hw => ?_
      have := hUk hw
      rw [← fixedSpace_eq_primaryComponent] at this
      exact mem_fixedSpace.1 this
    exact apply_eq_of_mem_supportedFixedDerived hk hk1 hg (hUk hv)
  have hej : e j ∈ Subgroup.zpowers d := by
    refine mem_zpowers_of_commute_of_frame hF hcd j fun g hg => ?_
    rw [hL] at hg
    have hgs := hGle (Subgroup.mem_subgroupOf.1 hg)
    exact Subtype.ext (commute_of_apply_eq (hF.nondeg j) (hOg g) (hfixj _ hgs)
      (hF.maps_to j) (hF.apply_of_perp j))
  exact hF.apply_eq_of_mem_zpowers hp hd hej

theorem weightOne_of_le_supportedFixedDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime)
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (hd1 : d ≠ 1)
    {G : Subgroup (V ≃ₗ[F] V)} {L : Subgroup ↥(orthDerived Q)}
    (hGdim : finrank F (fixedSpace (d : V ≃ₗ[F] V)) ≤ 4 ∨
      G = supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : L = G.subgroupOf (orthDerived Q))
    (hsupp : ∀ j, ¬ (∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) →
      ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v) :
    ∃ j, d ∈ Subgroup.zpowers (e j) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j) ∧
      L = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ¬ (∀ v ∈ U j₀, (d : V ≃ₗ[F] V) v = v) := by
    by_contra hno
    push Not at hno
    exact hd1 (hF.eq_one_of_forall_apply_eq hd hno)
  have hdz : d ∈ Subgroup.zpowers (e j₀) := hF.mem_zpowers_of_apply_eq hd j₀ (hsupp j₀ hj₀)
  have hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j₀) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdz
    have hzp : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers (e j₀ : V ≃ₗ[F] V) :=
      Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk]; simp⟩
    have hord' : orderOf (e j₀ : V ≃ₗ[F] V) = p := by
      rw [Subgroup.orderOf_coe]
      exact hF.orderOf_eq j₀
    have hd1' : (d : V ≃ₗ[F] V) ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
    rw [fixedSpace_eq_of_mem_zpowers hp hord' hzp hd1']
    exact hF.fixedSpace_eq_polarPerp j₀
  have hfd : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * (n - 1) := by
    rw [hfs, finrank_polarPerp hQ (U j₀), hF.finrank_eq j₀, hdim]
    omega
  have hGeq : G = supportedFixedDerived Q (d : V ≃ₗ[F] V) :=
    hGdim.resolve_left (by rw [hfd]; omega)
  exact ⟨j₀, hdz, hfs, by rw [hL, hGeq]⟩

theorem standard_dichotomy_full (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) {L : Subgroup ↥(orthDerived Q)}
    (hL : IsComponentOf L (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
    (hcd : Bb ⊓ Subgroup.centralizer (L : Set ↥(orthDerived Q)) = Subgroup.zpowers d) :
    (∃ j, d ∈ Subgroup.zpowers (e j) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j) ∧
        L = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ∨
    (∃ h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap, h ≠ X - 1 ∧
        (∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) ∧
        L = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  rcases comp_cases_orthDerived_gen hQ hp hp2 hpq hord hL with
    ⟨h, hh, hh1, -, hLh⟩ | ⟨G, -, hGle, -, hGdim, hLG⟩
  · refine Or.inr ⟨h, hh, hh1, ?_, hLh⟩
    exact le_primaryComponent_of_eq_specialBlock hp hp2 hpq hF hd hcd hx hh hh1 hLh
  · refine Or.inl (weightOne_of_le_supportedFixedDerived hQ hdim hn hp hF hd hd1 hGdim hLG ?_)
    exact apply_eq_of_le_supportedFixedDerived hp hp2 hpq hF hd hcd hGle hLG

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
