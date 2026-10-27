module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3AltEightL34
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelDefs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAltNode

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

namespace AltEight

open scoped IsMulCommutative

theorem card_mulAut_eq_card_GL {p : ℕ} [Fact p.Prime] {E : Type} [Group E] [Finite E]
    [CFSG.IsElementaryAbelian p E] {n : ℕ} (hE : Nat.card E = p ^ n) :
    Nat.card (MulAut E) = Nat.card (GL (Fin n) (ZMod p)) := by
  classical
  have hfin : Module.finrank (ZMod p) (Additive E) = n := by
    have h := FiniteField.pow_finrank_eq_natCard p (Additive E)
    have h' : Nat.card (Additive E) = p ^ n := hE
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h.trans h')
  let bas := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hfin
  let e1 : MulAut E ≃ (Additive E ≃+ Additive E) := MulEquiv.toAdditive
  let e2 : (Additive E ≃+ Additive E) ≃ (Additive E ≃ₗ[ZMod p] Additive E) :=
    { toFun := fun σ => σ.toLinearEquiv (ZMod.map_smul σ)
      invFun := fun σ => σ.toAddEquiv
      left_inv := fun σ => by ext; rfl
      right_inv := fun σ => by ext; rfl }
  let e3 : (Additive E ≃ₗ[ZMod p] Additive E) ≃*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive E) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm
  let e4 : LinearMap.GeneralLinearGroup (ZMod p) (Additive E) ≃* GL (Fin n) (ZMod p) :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv bas).toMulEquiv
  exact Nat.card_congr (e1.trans (e2.trans (e3.trans e4).toEquiv))

end AltEight

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

structure Alt8LayerFacts (C : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ x y : G, x * y ≠ y * x
  mem_centralizer : z ∈ centralizer (L : Set G)
  sup_zpowers : L ⊔ zpowers z = centralizer ({z} : Set G)
  inf_zpowers : L ⊓ zpowers z = ⊥
  orderOf_z : orderOf z = 2
  el : IsElementaryAbelian 2 C
  card : Nat.card C = 512
  A₂_le : sp6A₂ φ e ≤ C
  fix_z : ∀ c ∈ C, c * z = z * c ↔ c ∈ sp6A₂ φ e
  card_A₂ : Nat.card (sp6A₂ φ e) = 2 ^ 6
  comm_z : {x | ∃ c ∈ C, c⁻¹ * z⁻¹ * c * z = x} = tauSet φ e (fun B => ∀ i, B i i = 0)
  le_N₂ : C ≤ sp6N₂ φ e z
  uniq_N₂ : ∀ F : Subgroup G, F ≤ sp6N₂ φ e z → IsElementaryAbelian 2 F → Nat.card F = 512 →
    F = C
  z_mem : z ∈ layX C
  levi_mem : ∀ g, leviHom φ he g ∈ layX C
  centralizer_a : centralizer {laya C z} = ((sp6N₂ φ e z).subgroupOf (layX C)).map (layπ C)
  levi_injective : Function.Injective (layLeviHom C (leviHom φ he) levi_mem)
  levi_range : (layLeviHom C (leviHom φ he) levi_mem).range = layJL C (leviHom φ he)
  orderOf_a : orderOf (laya C z) = 2
  JL_le : layJL C (leviHom φ he) ≤ centralizer {laya C z}
  Ro_inv : ∀ r ∈ layRo C, (laya C z)⁻¹ * r * laya C z = r⁻¹
  injOn_θ : Set.InjOn (layθ C) (centralizer {laya C z})
  orderOf_aBar : orderOf (layaBar C z) = 2
  JLBar_le : layJLBar C (leviHom φ he) ≤ centralizer {layaBar C z}
  JLBar_inf : zpowers (layaBar C z) ⊓ layJLBar C (leviHom φ he) = ⊥
  JLBar_sup : zpowers (layaBar C z) ⊔ layJLBar C (leviHom φ he) = centralizer {layaBar C z}
  Dstar_centralizer : centralizer (layDstar C (leviHom φ he) : Set (LayY C)) = ⊥
  Q_map : (normalClosure (layJL C (leviHom φ he) : Set (LayF C))).map (layθ C) =
    layDstar C (leviHom φ he)
  Q_comap : (layDstar C (leviHom φ he)).comap (layθ C) =
    layRo C ⊔ normalClosure (layJL C (leviHom φ he) : Set (LayF C))
  Q_center : (center (normalClosure (layJL C (leviHom φ he) : Set (LayF C)))).map
    (normalClosure (layJL C (leviHom φ he) : Set (LayF C))).subtype =
      normalClosure (layJL C (leviHom φ he) : Set (LayF C)) ⊓ layRo C
  JLBar_standard : CFSG.IsStandardSubgroup (layJLBar C (leviHom φ he))
  catalog : CFSG.Blueprint.Catalog (layDstar C (leviHom φ he))
  card_dvd : Nat.card (layDstar C (leviHom φ he)) ∣ Nat.card (GL (Fin 9) (ZMod 2))

theorem alt8_layer_facts
    (hD : CFSG.LocalAnalysis.SteinbergBV.DirectSimpleInvolutionCentralizerLayerStmt)
    [Finite G] {T : Sylow 2 (centralizer (L : Set G))} (hS : Setting L T z)
    [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (halt : conjClass (sp6N₂ φ e z) z = z • tauSet φ e (fun B => ∀ i, B i i = 0))
    (hsimple : LayerSimple (alt8C₂ φ e z) z (leviHom φ he)) :
    Alt8LayerFacts φ he z (alt8C₂ φ e z) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hzC, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{0} hS.oddCore_eq hS.standard
      hS.not_normal hS.center_eq hS.model T hS.cyclic hS.mem hS.order hS.core_z
  obtain ⟨C₂, hC₂D, hC₂ab, hC₂c, hC₂u, hC₂e, hC₂N, hN₂u, -, -, ⟨hzX, -, hCaN, ⟨ψ, hψ⟩, hsyl, -⟩,
      -, hCK, hKodd, -, hKn, -, ⟨κ, hκ1, hκ2⟩, hfixz, hA₂c, hcomm, -,
      ⟨Ψc, -, hΨc2, -⟩, hXne⟩ :=
    AlternatingEight.standard_binary_symplectic_six_alternating_eight_next_normalizer
      hS.oddCore_eq hS.standard hS.not_normal hS.center_eq hS.model T hS.cyclic hS.mem hS.order
      hS.core_z hb hnd hV φ e he halt
  have hCeq : alt8C₂ φ e z = C₂ := AlternatingEight.alt8C₂_eq φ e z hC₂D hC₂ab hC₂c hC₂u
  rw [hCeq] at hsimple ⊢
  have hN₂X : sp6N₂ φ e z ≤ layX C₂ := AlternatingEight.le_layX_of_conj C₂ hC₂N
  have hLX : ∀ g, leviHom φ he g ∈ layX C₂ := fun g =>
    hN₂X (leviHom_mem_normalizer_radSub φ he hzC hS.order g)
  obtain ⟨ha2, hinj, hrange, hJC, hinfJ, hsupJ⟩ :=
    lay_centralizer_facts C₂ z (leviHom φ he) hS.order hLX hzX ψ hψ
  have hXne' : layX C₂ ≠ ⊤ := hXne hS.simple hS.nonab
  have hKX := CFSG.QuasithinUnique.isKGroupCat_of_kProper hS.kProper hXne'
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
  obtain ⟨⟨-, hR2, -⟩, ⟨-, hθ2, -⟩, ⟨hYK, -, -⟩, ⟨hc1, hc2, hc3⟩, -, ⟨hstd, -, -, -⟩,
      ⟨-, -, -, -, hl5, -, -⟩, -, ⟨-, -, hQ3, hQ4, hQ5, -, -⟩, -, -, -⟩ :=
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
  obtain ⟨hKBR, κF, -, hκFker⟩ := lay_kernel_facts C₂ hKodd hKn κ hκ1 hκ2
  have hA₂C : sp6A₂ φ e ≤ C₂ := AlternatingEight.sp6A₂_le_of_coords φ e Ψc hΨc2 hA₂c
  have hC₂N₂ : C₂ ≤ sp6N₂ φ e z := hC₂D.trans (Subgroup.map_subtype_le _)
  have : IsSimpleGroup (layDstar C₂ (leviHom φ he)) := hsimple.1
  have hcat : CFSG.Blueprint.Catalog (layDstar C₂ (leviHom φ he)) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hYK (layDstar C₂ (leviHom φ he))
      (MonoidHom.id (layDstar C₂ (leviHom φ he))) Function.surjective_id
  have hord : Nat.card (layDstar C₂ (leviHom φ he)) ∣ Nat.card (GL (Fin 9) (ZMod 2)) := by
    have h1 : Nat.card (layDstar C₂ (leviHom φ he)) ∣ Nat.card (LayY C₂) :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (LayY C₂) ∣ Nat.card κF.range := by
      rw [← Subgroup.index_ker κF, hκFker]
      exact Subgroup.index_dvd_of_le hKBR
    have h3 : Nat.card κF.range ∣ Nat.card (MulAut C₂) := Subgroup.card_subgroup_dvd_card _
    have h4 : Nat.card (MulAut C₂) = Nat.card (GL (Fin 9) (ZMod 2)) :=
      AltEight.card_mulAut_eq_card_GL (by rw [hC₂c]; norm_num)
    exact h1.trans (h2.trans (h4 ▸ h3))
  exact
    { simple := hS.simple
      nonab := hS.nonab
      mem_centralizer := hzC
      sup_zpowers := hsup
      inf_zpowers := hinf
      orderOf_z := hS.order
      el := hC₂e
      card := hC₂c
      A₂_le := hA₂C
      fix_z := hfixz
      card_A₂ := hA₂c
      comm_z := hcomm
      le_N₂ := hC₂N₂
      uniq_N₂ := hN₂u
      z_mem := hzX
      levi_mem := hLX
      centralizer_a := by rw [ha]; exact hCaN
      levi_injective := hinj
      levi_range := hrange
      orderOf_a := ha2
      JL_le := hJC
      Ro_inv := hR2
      injOn_θ := hθ2
      orderOf_aBar := haBar
      JLBar_le := hc1
      JLBar_inf := hc2
      JLBar_sup := hc3
      Dstar_centralizer := hl5
      Q_map := hQ3
      Q_comap := hQ4
      Q_center := hQ5
      JLBar_standard := hstd
      catalog := hcat
      card_dvd := hord }

namespace Alt8LayerFacts

variable {φ he z} {C : Subgroup G}

theorem nonempty_JLBar_equiv (h : Alt8LayerFacts φ he z C) :
    Nonempty (layJLBar C (leviHom φ he) ≃* GL (Fin 3) (ZMod 2)) := by
  set ι := layLeviHom C (leviHom φ he) h.levi_mem
  have hιJL : ∀ g, ι g ∈ centralizer {laya C z} := fun g => h.JL_le (by
    rw [← h.levi_range]
    exact ⟨g, rfl⟩)
  have hψinj : Function.Injective ((layθ C).comp ι) := fun g g' hgg =>
    h.levi_injective (h.injOn_θ (hιJL g) (hιJL g') hgg)
  have hψrange : ((layθ C).comp ι).range = layJLBar C (leviHom φ he) := by
    rw [MonoidHom.range_comp, h.levi_range]
    rfl
  exact ⟨((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)).symm⟩

theorem source (h : Alt8LayerFacts φ he z C) (hsimple : LayerSimple C z (leviHom φ he)) :
    GL3Source (layDstar C (leviHom φ he)) (layaBar C z) (layJLBar C (leviHom φ he)) where
  normal := Subgroup.normalClosure_normal
  simple := hsimple.1
  nonab := hsimple.2.1
  centralizer_eq := h.Dstar_centralizer
  orderOf_eq := h.orderOf_aBar
  le := hsimple.2.2.1.le
  le_centralizer := h.JLBar_le
  sup_eq := h.JLBar_sup
  inf_eq := h.JLBar_inf
  gl3 := h.nonempty_JLBar_equiv

theorem false_of_evenLinear [Finite G] [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (hV : finrank (ZMod 2) V = 6) (h : Alt8LayerFacts φ he z C)
    (hsimple : LayerSimple C z (leviHom φ he)) {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = 2 ^ f)
    (η : layDstar C (leviHom φ he) ≃* LinearFlag.projectiveSL n k) : False :=
  alt8_even_linear_false φ he z h.simple h.nonab h.mem_centralizer h.sup_zpowers h.inf_zpowers
    h.orderOf_z hb hnd hV h.el h.card h.A₂_le h.fix_z h.card_A₂ h.comm_z h.le_N₂ h.uniq_N₂ h.z_mem
    h.levi_mem h.centralizer_a h.levi_injective h.levi_range h.orderOf_a h.JL_le h.Ro_inv
    h.injOn_θ h.orderOf_aBar h.JLBar_le h.JLBar_sup h.Dstar_centralizer h.Q_map h.Q_comap
    h.Q_center hsimple hn hf hk η

end Alt8LayerFacts

end CFSG.EvenSmallLie.Child3
