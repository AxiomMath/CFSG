module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem mem_zpowers_of_commute {n : ℕ} {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d) (j : Fin (n - 1))
    (h : ∀ g ∈ GLALayer (Subgroup.centralizer {d}), g * e j = e j * g) : e j ∈ Subgroup.zpowers d := by
  have : e j ∈ Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) :=
    Subgroup.mem_inf.2 ⟨hF.mem j, Subgroup.mem_centralizer_iff.2 h⟩
  rwa [hcd] at this

private lemma exists_primary_of_layerIs_aux1 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n f : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hf : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hb : CatDistinct.OrderBridge)
    {d : ↥(orthDerived Q)}
    (hLd : LayerIs p (Subgroup.centralizer {d}) (isUnA (n - 1) (Nat.card F))) : d ≠ 1 := by
  rintro rfl
  apply not_layerIs_top_isUnA hQ hdim hn hf hf1 hb hp hp2 hpq
  have : Subgroup.centralizer ({1} : Set ↥(orthDerived Q)) = ⊤ := by simp
  rw [this] at hLd
  exact hLd

private lemma exists_primary_of_layerIs_aux2 {n : ℕ}
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d) (hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V))
    (htriv : ∀ j, e j ∈ Subgroup.zpowers d → ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v)
    (hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : d ∈ Bb)
    {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  intro j
  by_contra hj
  have hself := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1
  obtain ⟨k, hk, hUk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd j
  have hkh : k ≠ h := fun hkh => hj (hkh ▸ hUk)
  have hfix : ∀ g ∈ specialBlock Q (d : V ≃ₗ[F] V) h, ∀ v ∈ U j, g v = v := fun g hg v hv =>
    apply_eq_of_mem_specialBlock hk hkh (by rw [hself]; exact hkh) hg (hUk hv)
  have hej : e j ∈ Subgroup.zpowers d := by
    refine mem_zpowers_of_commute hF hcd j fun g hg => ?_
    rw [hL] at hg
    have hgs := Subgroup.mem_subgroupOf.1 hg
    exact Subtype.ext (commute_of_apply_eq (hF.nondeg j) (hOg g) (hfix _ hgs)
      (hF.maps_to j) (hF.apply_of_perp j))
  obtain ⟨i, hi⟩ := hF.exists_le_primaryComponent_of_mem hp hp2 hpq hd hh hh1
  have hij : i ≠ j := fun hij => hj (hij ▸ hi)
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hF.finrank_eq i)
  exact hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 (hi hv) (htriv j hej i hij v hv))

private lemma exists_primary_of_layerIs_aux3 {n : ℕ}
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d)
    (htriv : ∀ j, e j ∈ Subgroup.zpowers d → ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v)
    (hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : d ∈ Bb)
    {G : Subgroup (V ≃ₗ[F] V)} (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : GLALayer (Subgroup.centralizer {d}) = G.subgroupOf (orthDerived Q)) :
    ∀ j, ¬ (∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) →
      ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v := by
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
  refine htriv j (mem_zpowers_of_commute hF hcd j fun g hg => ?_)
  rw [hL] at hg
  have hgs := hGle (Subgroup.mem_subgroupOf.1 hg)
  exact Subtype.ext (commute_of_apply_eq (hF.nondeg j) (hOg g) (hfixj _ hgs)
    (hF.maps_to j) (hF.apply_of_perp j))

private lemma exists_primary_of_layerIs_aux4 {n : ℕ}
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) (hp : p.Prime)
    (hsupp : ∀ j, ¬ (∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) →
      ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v) :
    ∃ j₀, fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j₀) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ¬ (∀ v ∈ U j₀, (d : V ≃ₗ[F] V) v = v) := by
    by_contra hno
    push Not at hno
    exact hd1 (hF.eq_one_of_forall_apply_eq hd hno)
  refine ⟨j₀, ?_⟩
  have hdz : d ∈ Subgroup.zpowers (e j₀) := hF.mem_zpowers_of_apply_eq hd j₀ (hsupp j₀ hj₀)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdz
  have hzp : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers (e j₀ : V ≃ₗ[F] V) :=
    Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk]; simp⟩
  have hord' : orderOf (e j₀ : V ≃ₗ[F] V) = p := by
    rw [Subgroup.orderOf_coe]
    exact hF.orderOf_eq j₀
  have hd1' : (d : V ≃ₗ[F] V) ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  rw [fixedSpace_eq_of_mem_zpowers hp hord' hzp hd1']
  exact hF.fixedSpace_eq_polarPerp j₀

private lemma exists_primary_of_layerIs_aux5 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) (hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V))
    {Q₁ : TauCeti.CFSGIndex → Prop}
    (hQ₁ : ∀ j, catalogIs (PSimple p (⊤ : Subgroup
      ↥(orthDerived (Q.comp (polarPerp Q (U j)).subtype)))) Q₁)
    (hexcl : ∀ (S : Type) [Group S] [Finite S],
      catalogIs S (isUnA (n - 1) (Nat.card F)) → catalogIs S Q₁ → False)
    {G : Subgroup (V ≃ₗ[F] V)}
    (hGdim : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) ≤ 4 ∨
      G = supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : GLALayer (Subgroup.centralizer {d}) = G.subgroupOf (orthDerived Q))
    (hLd : LayerIs p (Subgroup.centralizer {d}) (isUnA (n - 1) (Nat.card F)))
    (hsupp : ∀ j, ¬ (∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) →
      ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v) : False := by
  obtain ⟨j₀, hfs⟩ := exists_primary_of_layerIs_aux4 hF hd hd1 hp hsupp
  have hfd : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * (n - 1) := by
    rw [hfs, finrank_polarPerp hQ (U j₀), hF.finrank_eq j₀, hdim]
    omega
  have hGeq : G = supportedFixedDerived Q (d : V ≃ₗ[F] V) :=
    hGdim.resolve_left (by rw [hfd]; omega)
  have h1 : catalogIs (PSimple p (GLALayer (Subgroup.centralizer {d})))
      (isUnA (n - 1) (Nat.card F)) := hLd.2
  rw [hL, hGeq] at h1
  have h2 : catalogIs (PSimple p ((supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf
      (orthDerived Q))) Q₁ := by
    refine catalogIs_pSimple_supportedFixedDerived hx ?_
    rw [hfs]
    exact hQ₁ j₀
  exact hexcl _ h1 h2

theorem exists_primary_of_layerIs (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n f : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hf : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hb : CatDistinct.OrderBridge)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {Q₁ : TauCeti.CFSGIndex → Prop}
    (hQ₁ : ∀ j, catalogIs (PSimple p (⊤ : Subgroup
      ↥(orthDerived (Q.comp (polarPerp Q (U j)).subtype)))) Q₁)
    (hexcl : ∀ (S : Type) [Group S] [Finite S],
      catalogIs S (isUnA (n - 1) (Nat.card F)) → catalogIs S Q₁ → False)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hLd : LayerIs p (Subgroup.centralizer {d}) (isUnA (n - 1) (Nat.card F)))
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d) :
    ∃ h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap, h ≠ X - 1 ∧
      ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hd1 : d ≠ 1 := exists_primary_of_layerIs_aux1 hQ hdim hn hf hf1 hp hp2 hpq hb hLd
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have htriv : ∀ j, e j ∈ Subgroup.zpowers d → ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v :=
    fun j hj => hF.apply_eq_of_mem_zpowers hp hd hj
  have hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  rcases comp_cases_orthDerived_gen hQ hp hp2 hpq hord hLd.1 with
    ⟨h, hh, hh1, -, hL⟩ | ⟨G, -, hGle, -, hGdim, hL⟩
  · exact ⟨h, hh, hh1, exists_primary_of_layerIs_aux2 hF hcd hx htriv hOg hp hp2 hpq hd hh hh1 hL⟩
  · exfalso
    exact exists_primary_of_layerIs_aux5 hQ hdim hn hp hF hd hd1 hx hQ₁ hexcl hGdim hL hLd
      (exists_primary_of_layerIs_aux3 hF hcd htriv hOg hp hp2 hpq hd hGle hL)

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
