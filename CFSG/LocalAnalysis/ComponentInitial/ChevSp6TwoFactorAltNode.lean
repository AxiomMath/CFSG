module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAltCore
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightNextNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianTools
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module CFSG.EvenSmallLie.Child3
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

section Layer

variable {G : Type} [Group G] (C : Subgroup G) (z : G) (lev : GL (Fin 3) (ZMod 2) →* G)

@[expose] def layQstar : Subgroup (LayF C) := normalClosure (layJL C lev : Set (LayF C))

@[expose] def LayerTwoFactor : Prop :=
  ∃ D₁ D₂ : Subgroup (LayY C), CFSG.IsComponent D₁ ∧ CFSG.IsComponent D₂ ∧ D₁ ≠ D₂ ∧
    IsSimpleGroup D₁ ∧ (∃ x y : D₁, x * y ≠ y * x) ∧
    IsSimpleGroup D₂ ∧ (∃ x y : D₂, x * y ≠ y * x) ∧
    D₁ ⊔ D₂ = layDstar C lev ∧ D₁ ⊓ D₂ = ⊥ ∧ ⁅D₁, D₂⁆ = ⊥ ∧
    D₁.map (MulAut.conj (layaBar C z)⁻¹).toMonoidHom = D₂ ∧
    layJLBar C lev = layDstar C lev ⊓ centralizer ({layaBar C z} : Set (LayY C)) ∧
    ∃ ψ : layDstar C lev ≃* layJLBar C lev × layJLBar C lev,
      (∀ (j : LayY C) (hjJ : j ∈ layJLBar C lev) (hjD : j ∈ layDstar C lev),
        ψ ⟨j, hjD⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩)) ∧
      ∀ (d : LayY C) (hd : d ∈ layDstar C lev)
        (hda : (layaBar C z)⁻¹ * d * layaBar C z ∈ layDstar C lev),
        ψ ⟨(layaBar C z)⁻¹ * d * layaBar C z, hda⟩ = (ψ ⟨d, hd⟩).swap

theorem le_layX_of_conj {N : Subgroup G} (h : ∀ g ∈ N, ∀ c ∈ C, g * c * g⁻¹ ∈ C) :
    N ≤ layX C := by
  intro g hg
  change g ∈ normalizer (C : Set G)
  rw [mem_normalizer_iff]
  intro c
  refine ⟨h g hg c, fun hc => ?_⟩
  have h' := h g⁻¹ (inv_mem hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at h'

end Layer

section Setting

variable {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
  (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G)

theorem sp6A₂_le_of_coords [Finite G] {C : Subgroup G}
    (Ψ : Multiplicative ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) ≃* C)
    (hΨ : ∀ u v w, (Ψ (Multiplicative.ofAdd (u, v, w)) : G) ∈ sp6A₂ φ e ↔ u = 0)
    (hcard : Nat.card (sp6A₂ φ e) = 2 ^ 6) : sp6A₂ φ e ≤ C := by
  let f : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) → (sp6A₂ φ e ⊓ C : Subgroup G) := fun p =>
    ⟨Ψ (Multiplicative.ofAdd (0, p.1, p.2)), mem_inf.2 ⟨(hΨ 0 p.1 p.2).2 rfl,
      (Ψ (Multiplicative.ofAdd (0, p.1, p.2))).2⟩⟩
  have hinj : Function.Injective f := by
    intro p q h
    have h0 := congrArg Subtype.val h
    have h1 : Ψ (Multiplicative.ofAdd (0, p.1, p.2)) = Ψ (Multiplicative.ofAdd (0, q.1, q.2)) :=
      Subtype.ext h0
    have h2 := congrArg Multiplicative.toAdd (Ψ.injective h1)
    simp only [toAdd_ofAdd, Prod.mk.injEq, true_and] at h2
    exact Prod.ext h2.1 h2.2
  have hle : Nat.card ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) ≤
      Nat.card (sp6A₂ φ e ⊓ C : Subgroup G) := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, natCard_vecThree] at hle
  have heq : sp6A₂ φ e ⊓ C = sp6A₂ φ e :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard]; exact le_trans (by norm_num) hle)
  rw [← heq]
  exact inf_le_right

theorem alt8C₂_eq {C : Subgroup G} (hCD : C ≤ sp6D₂ φ e z)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hCc : Nat.card C = 512)
    (huniq : ∀ F : Subgroup G, F ≤ sp6D₂ φ e z → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) →
      Nat.card F = 512 → F = C) : alt8C₂ φ e z = C := by
  have hspec : ∃ C' : Subgroup G, C' ≤ sp6D₂ φ e z ∧ IsMulCommutative C' ∧ Nat.card C' = 512 :=
    ⟨C, hCD, ⟨⟨fun x y => Subtype.ext (hCab x x.2 y y.2)⟩⟩, hCc⟩
  obtain ⟨h1, h2, h3⟩ := Classical.epsilon_spec hspec
  exact huniq _ h1 (fun x hx y hy => congrArg Subtype.val (h2.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) h3

end Setting

theorem standard_binary_symplectic_six_alternating_eight_two_factor_ambient_exclusion
    (hD : CFSG.LocalAnalysis.SteinbergBV.DirectSimpleInvolutionCentralizerLayerStmt)
    {G : Type} [Group G] [Finite G] (hGs : IsSimpleGroup G) (hGnab : ∃ x y : G, x * y ≠ y * x)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hG : CFSG.oddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (halt : conjClass (sp6N₂ φ e z) z = z • tauSet φ e (fun B => ∀ i, B i i = 0)) :
    (alt8C₂ φ e z ≤ sp6D₂ φ e z ∧
      (∀ x ∈ alt8C₂ φ e z, ∀ y ∈ alt8C₂ φ e z, x * y = y * x) ∧ Nat.card (alt8C₂ φ e z) = 512 ∧
      ∀ F : Subgroup G, F ≤ sp6D₂ φ e z → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) →
        Nat.card F = 512 → F = alt8C₂ φ e z) ∧
    IsElementaryAbelian 2 (alt8C₂ φ e z) ∧
    (∀ g ∈ sp6N₂ φ e z, ∀ c ∈ alt8C₂ φ e z, g * c * g⁻¹ ∈ alt8C₂ φ e z) ∧
    layX (alt8C₂ φ e z) ≠ ⊤ ∧ CFSG.SectionRank.IsKGroupCat (LayF (alt8C₂ φ e z)) ∧
    (∃ hzX : z ∈ layX (alt8C₂ φ e z), laya (alt8C₂ φ e z) z = layπ (alt8C₂ φ e z) ⟨z, hzX⟩) ∧
    (∃ hLX : ∀ g, leviHom φ he g ∈ layX (alt8C₂ φ e z),
      Function.Injective (layLeviHom (alt8C₂ φ e z) (leviHom φ he) hLX) ∧
      (layLeviHom (alt8C₂ φ e z) (leviHom φ he) hLX).range =
        layJL (alt8C₂ φ e z) (leviHom φ he)) ∧
    orderOf (laya (alt8C₂ φ e z) z) = 2 ∧
    layJL (alt8C₂ φ e z) (leviHom φ he) ≤ centralizer {laya (alt8C₂ φ e z) z} ∧
    zpowers (laya (alt8C₂ φ e z) z) ⊓ layJL (alt8C₂ φ e z) (leviHom φ he) = ⊥ ∧
    zpowers (laya (alt8C₂ φ e z) z) ⊔ layJL (alt8C₂ φ e z) (leviHom φ he) =
      centralizer {laya (alt8C₂ φ e z) z} ∧
    centralizer (alt8C₂ φ e z : Set G) = alt8C₂ φ e z ⊔ layK (alt8C₂ φ e z) ∧
    alt8C₂ φ e z ⊓ layK (alt8C₂ φ e z) = ⊥ ∧ Odd (Nat.card (layK (alt8C₂ φ e z))) ∧
    (∀ x ∈ layK (alt8C₂ φ e z), ∀ y ∈ layK (alt8C₂ φ e z), x * y = y * x) ∧
    (∀ g ∈ layX (alt8C₂ φ e z), ∀ k ∈ layK (alt8C₂ φ e z),
      g * k * g⁻¹ ∈ layK (alt8C₂ φ e z)) ∧
    (∀ k ∈ layK (alt8C₂ φ e z), z * k * z⁻¹ = k⁻¹) ∧
    sp6A₂ φ e ≤ alt8C₂ φ e z ∧ (∀ c ∈ alt8C₂ φ e z, c * z = z * c ↔ c ∈ sp6A₂ φ e) ∧
    Nat.card (sp6A₂ φ e) = 2 ^ 6 ∧
    {x | ∃ c ∈ alt8C₂ φ e z, c⁻¹ * z⁻¹ * c * z = x} = tauSet φ e (fun B => ∀ i, B i i = 0) ∧
    Nat.card (tauSet φ e (fun B => ∀ i, B i i = 0)) = 2 ^ 3 ∧
    layDstar (alt8C₂ φ e z) (leviHom φ he) = CFSG.layer (LayY (alt8C₂ φ e z)) ∧
    LayerSimple (alt8C₂ φ e z) z (leviHom φ he) ∧
    ¬ LayerTwoFactor (alt8C₂ φ e z) z (leviHom φ he) ∧
    IsMulCommutative (layRo (alt8C₂ φ e z)) ∧
    (∀ r ∈ layRo (alt8C₂ φ e z),
      (laya (alt8C₂ φ e z) z)⁻¹ * r * laya (alt8C₂ φ e z) z = r⁻¹) ∧
    layRo (alt8C₂ φ e z) ⊓ centralizer {laya (alt8C₂ φ e z) z} = ⊥ ∧
    Set.InjOn (layθ (alt8C₂ φ e z)) (centralizer {laya (alt8C₂ φ e z) z}) ∧
    orderOf (layaBar (alt8C₂ φ e z) z) = 2 ∧
    layJLBar (alt8C₂ φ e z) (leviHom φ he) ≤ centralizer {layaBar (alt8C₂ φ e z) z} ∧
    zpowers (layaBar (alt8C₂ φ e z) z) ⊓ layJLBar (alt8C₂ φ e z) (leviHom φ he) = ⊥ ∧
    zpowers (layaBar (alt8C₂ φ e z) z) ⊔ layJLBar (alt8C₂ φ e z) (leviHom φ he) =
      centralizer {layaBar (alt8C₂ φ e z) z} ∧
    (layQstar (alt8C₂ φ e z) (leviHom φ he)).Normal ∧
    ⁅layQstar (alt8C₂ φ e z) (leviHom φ he), layQstar (alt8C₂ φ e z) (leviHom φ he)⁆ =
      layQstar (alt8C₂ φ e z) (leviHom φ he) ∧
    (layQstar (alt8C₂ φ e z) (leviHom φ he)).map (layθ (alt8C₂ φ e z)) =
      layDstar (alt8C₂ φ e z) (leviHom φ he) ∧
    (layDstar (alt8C₂ φ e z) (leviHom φ he)).comap (layθ (alt8C₂ φ e z)) =
      layRo (alt8C₂ φ e z) ⊔ layQstar (alt8C₂ φ e z) (leviHom φ he) ∧
    (∀ x ∈ (layDstar (alt8C₂ φ e z) (leviHom φ he)).comap (layθ (alt8C₂ φ e z)),
      ∀ r ∈ layRo (alt8C₂ φ e z), x * r = r * x) ∧
    (center (layQstar (alt8C₂ φ e z) (leviHom φ he))).map
        (layQstar (alt8C₂ φ e z) (leviHom φ he)).subtype =
      layQstar (alt8C₂ φ e z) (leviHom φ he) ⊓ layRo (alt8C₂ φ e z) ∧
    centralizer (layQstar (alt8C₂ φ e z) (leviHom φ he) : Set (LayF (alt8C₂ φ e z))) =
      layRo (alt8C₂ φ e z) ∧
    (∃ eQ : ↥(layQstar (alt8C₂ φ e z) (leviHom φ he)) ⧸
        (layRo (alt8C₂ φ e z)).subgroupOf (layQstar (alt8C₂ φ e z) (leviHom φ he)) ≃*
          layDstar (alt8C₂ φ e z) (leviHom φ he),
      ∀ q : layQstar (alt8C₂ φ e z) (leviHom φ he),
        (eQ (QuotientGroup.mk q) : LayY (alt8C₂ φ e z)) = layθ (alt8C₂ φ e z) q) ∧
    layKBar (alt8C₂ φ e z) ≤ layRo (alt8C₂ φ e z) ∧
    Odd (Nat.card (layQstar (alt8C₂ φ e z) (leviHom φ he) ⊓ layRo (alt8C₂ φ e z) :
      Subgroup (LayF (alt8C₂ φ e z)))) ∧
    ∀ r ∈ layQstar (alt8C₂ φ e z) (leviHom φ he) ⊓ layRo (alt8C₂ φ e z),
      (laya (alt8C₂ φ e z) z)⁻¹ * r * laya (alt8C₂ φ e z) z = r⁻¹ := by
  classical
  obtain ⟨-, hzC, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{0} hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨C₂, hC₂D, hC₂ab, hC₂c, hC₂u, hC₂e, hC₂N, -, -, -, ⟨hzX, -, -, ⟨ψ, hψ⟩, hsyl, -⟩,
      hcen, hCK, hKodd, hKab, hKn, hKinv, ⟨κ, hκ1, hκ2⟩, hfixz, hA₂c, hcomm, hI₂c,
      ⟨Ψc, -, hΨc2, -⟩, hXne⟩ :=
    standard_binary_symplectic_six_alternating_eight_next_normalizer hG hL hLn hZ hmodel T hT hzT
      hz hH hb hnd hV φ e he halt
  have hCeq : alt8C₂ φ e z = C₂ := alt8C₂_eq φ e z hC₂D hC₂ab hC₂c hC₂u
  rw [hCeq]
  have hN₂X : sp6N₂ φ e z ≤ layX C₂ := le_layX_of_conj C₂ hC₂N
  have hLX : ∀ g, leviHom φ he g ∈ layX C₂ := fun g =>
    hN₂X (leviHom_mem_normalizer_radSub φ he hzC hz g)
  obtain ⟨ha2, hinj, hrange, hJC, hinfJ, hsupJ⟩ :=
    lay_centralizer_facts C₂ z (leviHom φ he) hz hLX hzX ψ hψ
  have hXne' : layX C₂ ≠ ⊤ := hXne hGs hGnab
  have hKX := CFSG.QuasithinUnique.isKGroupCat_of_kProper hKP hXne'
  have hKF : CFSG.SectionRank.IsKGroupCat (LayF C₂) := hKX.quotient _
  let eJ : GL (Fin 3) (ZMod 2) ≃* layJL C₂ (leviHom φ he) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hJs : IsSimpleGroup (layJL C₂ (leviHom φ he)) := by
    have := isSimpleGroup_GL_three_two
    exact eJ.symm.isSimpleGroup
  have hJn : ∃ x y : layJL C₂ (leviHom φ he), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := SteinbergBU.exists_mul_ne_mul_GL_three_two
    exact ⟨eJ x, eJ y, fun h => hxy (eJ.injective (by rw [map_mul, map_mul, h]))⟩
  have hJ4 : ∃ E : Subgroup (LayF C₂), E ≤ layJL C₂ (leviHom φ he) ∧
      CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hEa, hEc⟩ := SteinbergBU.exists_four_subgroup_of_injective hinj
    exact ⟨E, hrange ▸ hE, hEa, hEc⟩
  have ha := laya_eq C₂ z hzX
  have hsylA : ∀ S : Sylow 2 (LayF C₂), laya C₂ z ∈ S →
      ∃ s ∈ S, s * laya C₂ z ≠ laya C₂ z * s := by
    rw [ha]
    exact hsyl
  obtain ⟨⟨hR1, hR2, hR3⟩, ⟨hθ1, hθ2, hθ3⟩, -, ⟨hc1, hc2, hc3⟩, -, -,
      ⟨-, -, -, hl4, hl5, hl6, -⟩, ⟨hq1, -⟩, ⟨hQ1, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7⟩,
      ⟨hodd1, hodd2⟩, -, -⟩ :=
    hD (LayF C₂) hKF (layJL C₂ (leviHom φ he)) hJs hJn hJ4 (laya C₂ z) ha2 hJC hinfJ hsupJ hsylA
  have haC : laya C₂ z ∈ centralizer {laya C₂ z} := mem_centralizer_singleton_iff.mpr rfl
  have ha1 : laya C₂ z ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haBar : orderOf (layaBar C₂ z) = 2 := by
    apply orderOf_eq_prime
    · change layθ C₂ (laya C₂ z) ^ 2 = 1
      rw [← map_pow, ← ha2, pow_orderOf_eq_one, map_one]
    · intro h
      exact ha1 (hθ2 haC (one_mem _) (h.trans (map_one _).symm))
  have hθι : Function.Injective ((layθ C₂).comp (layLeviHom C₂ (leviHom φ he) hLX)) := by
    intro g g' h
    apply hinj
    exact hθ1 (by rw [SetLike.mem_coe, ← hrange]; exact ⟨g, rfl⟩)
      (by rw [SetLike.mem_coe, ← hrange]; exact ⟨g', rfl⟩) h
  have hθrange : ((layθ C₂).comp (layLeviHom C₂ (leviHom φ he) hLX)).range =
      layJLBar C₂ (leviHom φ he) := by
    rw [MonoidHom.range_comp, hrange]
    rfl
  let κ' : GL (Fin 3) (ZMod 2) ≃* layJLBar C₂ (leviHom φ he) :=
    (MonoidHom.ofInjective hθι).trans (MulEquiv.subgroupCongr hθrange)
  have hκ' : ∀ g, (κ' g : LayY C₂) = layθ C₂ (layLeviHom C₂ (leviHom φ he) hLX g) :=
    fun g => rfl
  have hxor := SteinbergBU.xor_layer_alternatives_of
    (fun g => layθ C₂ (layLeviHom C₂ (leviHom φ he) hLX g)) κ' hκ' hl5 hl6
  obtain ⟨hKBR, κF, hκF1, hκFker⟩ := lay_kernel_facts C₂ hKodd hKn κ hκ1 hκ2
  have hA₂C : sp6A₂ φ e ≤ C₂ := sp6A₂_le_of_coords φ e Ψc hΨc2 hA₂c
  have hsimple : LayerSimple C₂ z (leviHom φ he) := by
    rcases hxor with ⟨hA, -⟩ | ⟨⟨D₁, D₂, -, -, -, -, -, -, -, -, -, -, -, -, -, Ψ, hΨ1, hΨ2⟩, -⟩
    · exact hA
    · exact (alt8_two_factor_false φ he z hGs hGnab hzC hsup hinf hz hb hnd hV hC₂e hC₂c hA₂C
        hfixz hzX hLX hrange ha2 hθ3 haBar hc1 hc3 hl5 hq1 hQ2 hQ3 hQ4 hQ5 hCK hKodd hKn κF
        hκF1 hκFker hKBR Ψ hΨ1 hΨ2).elim
  have hnot : ¬ LayerTwoFactor C₂ z (leviHom φ he) := by
    rcases hl6 with ⟨-, hB⟩ | ⟨-, hA⟩
    · exact hB
    · exact absurd hsimple hA
  exact ⟨⟨hC₂D, hC₂ab, hC₂c, hC₂u⟩, hC₂e, hC₂N, hXne', hKF, ⟨hzX, ha⟩, ⟨hLX, hinj, hrange⟩, ha2,
    hJC, hinfJ, hsupJ, hcen, hCK, hKodd, hKab, hKn, hKinv, hA₂C, hfixz, hA₂c, hcomm, hI₂c, hl4,
    hsimple, hnot, hR1, hR2, hR3, hθ2, haBar, hc1, hc2, hc3, hQ1, hQ2, hQ3, hQ4, hq1, hQ5, hQ6,
    hQ7, hKBR, hodd1, hodd2⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
