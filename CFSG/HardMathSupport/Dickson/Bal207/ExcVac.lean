module

public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
import CFSG.HardMathSupport.Solomon.Coordinator.B3LieQuasi
import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
  CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

theorem bal207PlusFamClauses_of_noComp {X : Type} [Group X] {p : ℕ} {K B A : Subgroup X}
    (hA : ¬ IsCyclic ↥A)
    (hno : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    Bal207PlusFamClauses p K B A := by
  have hbot : A ≠ ⊥ := by
    rintro rfl
    exact hA inferInstance
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  unfold Bal207PlusFamClauses
  refine ⟨fun b hb hb1 J hJ => absurd hJ (hno b hb hb1 J),
    fun b hb hb1 J hJ _ => absurd hJ (hno b hb hb1 J), ?_⟩
  exact ⟨a, haA, ha1', fun w _ _ _ J hJ => absurd hJ (hno a haA ha1' J)⟩

theorem excVac_false_of_solvable {G : Type} [Group G] [Finite G] {p : ℕ} {X I : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hI : GLAPComponent p X I) : False := by
  have hIX : I ≤ X := hI.1
  haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hI)
  haveI : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIX)
      (Subgroup.inclusion_injective hIX)
  haveI : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).2 (glaPComponent_ne_bot' hI)
  exact Group.IsPerfect.not_isSolvable (G := ↥I) inferInstance

theorem excVac_mulAut_eq_one {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    (α : MulAut Y) (h : ∀ x : Y, x⁻¹ * α x ∈ Subgroup.center Y) : α = 1 := by
  let c : Y →* Subgroup.center Y :=
    { toFun := fun x => ⟨x⁻¹ * α x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hx := Subgroup.mem_center_iff.1 (h x) y⁻¹
        change (x * y)⁻¹ * α (x * y) = (x⁻¹ * α x) * (y⁻¹ * α y)
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by rw [map_mul]; group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hx]
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group }
  have hle : commutator Y ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [hperf] at hle
  ext x
  have h1 : c x = 1 := hle (Subgroup.mem_top x)
  have h2 : x⁻¹ * α x = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  calc α x = x * (x⁻¹ * α x) := by group
    _ = x := by rw [h2, mul_one]

theorem excVac_false_of_glaPComponent {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K : Subgroup X} (hK : CFSG.Open.IsQuasisimple ↥K)
    (hS : ∀ β : MulAut (↥K ⧸ Subgroup.center ↥K), β ^ p = 1 → β ≠ 1 →
      Group.IsSolvable ↥(fixSubgroup β))
    {a : X} (ha : a ∈ Subgroup.normalizer (K : Set X))
    (hap : a ^ p ∈ Subgroup.centralizer (K : Set X)) (haK : a ∉ Subgroup.centralizer (K : Set X))
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    False := by
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨a, ha⟩
  have hα₀ : ∀ k : ↥K, ((α₀ k : ↥K) : X) = a * k * a⁻¹ := fun k => rfl
  have hα₀p : α₀ ^ p = 1 := by
    ext k
    have : (α₀ ^ p : MulAut ↥K) = K.normalizerMonoidHom (⟨a, ha⟩ ^ p) := by rw [map_pow]
    rw [this]
    have hk : ((K.normalizerMonoidHom (⟨a, ha⟩ ^ p) k : ↥K) : X) = a ^ p * k * (a ^ p)⁻¹ := rfl
    rw [MulAut.one_apply, hk]
    have := Subgroup.mem_centralizer_iff.1 hap (k : X) k.2
    calc a ^ p * (k : X) * (a ^ p)⁻¹ = (k : X) * a ^ p * (a ^ p)⁻¹ := by rw [← this]
      _ = (k : X) := by group
  let Z := Subgroup.center ↥K
  let π : ↥K →* (↥K ⧸ Z) := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hmapZ : ∀ γ : MulAut ↥K, Z.map γ.toMonoidHom = Z := fun γ =>
    Subgroup.characteristic_iff_map_eq.1 inferInstance γ
  let bar : MulAut ↥K → MulAut (↥K ⧸ Z) := fun γ => QuotientGroup.congr Z Z γ (hmapZ γ)
  have hbar : ∀ γ k, π (γ k) = bar γ (π k) := fun γ k => rfl
  have hβp : bar α₀ ^ p = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rw [← b3Lie_intertwine_pow π α₀ (bar α₀) (hbar α₀), hα₀p]
    rfl
  have hβ1 : bar α₀ ≠ 1 := by
    intro h1
    apply haK
    have hα1 : α₀ = 1 := by
      refine excVac_mulAut_eq_one hK.1 α₀ fun k => hker ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbar, h1, MulAut.one_apply, inv_mul_cancel]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg Subtype.val (congrArg (fun γ : MulAut ↥K => γ ⟨k, hk⟩) hα1)
    simp only [MulAut.one_apply] at this
    rw [hα₀] at this
    calc k * a = a * k * a⁻¹ * a := by rw [this]
      _ = a * k := by group
  have hJ₁ := glaPComponent_fixSubgroup hp ha hJ
  have hJβ := glaPComponent_map_fixSubgroup π hker α₀ (bar α₀) (hbar α₀) hπ hp hJ₁
  exact excVac_false_of_solvable (hS _ hβp hβ1) hJβ

theorem bal207PlusFamClauses_of_fix_solvable {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    {X : Type} [Group X] [Finite X] {p : ℕ} {K B A : Subgroup X}
    (ctx : Bal207PlusCtx G p K B A)
    (hS : ∀ β : MulAut (↥K ⧸ Subgroup.center ↥K), β ^ p = 1 → β ≠ 1 →
      Group.IsSolvable ↥(fixSubgroup β)) :
    Bal207PlusFamClauses p K B A := by
  refine bal207PlusFamClauses_of_noComp ctx.noncyc fun a haA ha1 J hJ => ?_
  have haB : a ∈ B := ctx.le haA
  have haN : a ∈ Subgroup.normalizer (K : Set X) := ctx.norm haB
  have hap : a ^ p ∈ Subgroup.centralizer (K : Set X) := by
    rw [ctx.scp.2.1.2 a haB]
    exact one_mem _
  have haK : a ∉ Subgroup.centralizer (K : Set X) :=
    not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1
  exact excVac_false_of_glaPComponent ctx.prime ctx.comp.2.2 hS haN hap haK hJ

end CFSG.HardMathSupport.Dickson.Bal207

end
