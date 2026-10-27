module

public import CFSG.Quasithin.Background.C1GNDefs
import CFSG.GroupTheory.NatL2SectionIrreducible
public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.Quasithin

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem commutatorElement_mul_right_of_mem_centralizer_nc {W : Subgroup G} {a x c : G}
    (ha : a ∈ W) (hxW : x ∈ Subgroup.normalizer (W : Set G))
    (hc : c ∈ Subgroup.centralizer (W : Set G)) : ⁅a, c * x⁆ = ⁅a, x⁆ := by
  have hxax : x * a⁻¹ * x⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp hxW a⁻¹).mp (W.inv_mem ha)
  have hcd : c * (x * a⁻¹ * x⁻¹) = (x * a⁻¹ * x⁻¹) * c :=
    (Subgroup.mem_centralizer_iff.mp hc _ hxax).symm
  rw [commutatorElement_def]
  rw [show a * (c * x) * a⁻¹ * (c * x)⁻¹
      = a * (c * (x * a⁻¹ * x⁻¹)) * c⁻¹ from by group]
  rw [hcd]
  group

private theorem normalizer_inf_centralizer_nc {W X : Subgroup G} {b : G}
    (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hbX : ∀ x ∈ X, ⁅x, b⁆ ∈ Subgroup.centralizer (W : Set G)) :
    X ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx c hc
  obtain ⟨hcW, hcC⟩ := hc
  have hxN : x ∈ Subgroup.normalizer (W : Set G) := hXW hx
  have hxcW : x * c * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxN c).mp hcW
  refine ⟨hxcW, ?_⟩
  change x * c * x⁻¹ ∈ Subgroup.centralizer ({b} : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.mp hcC b (Set.mem_singleton b)
  have hbxb : b * x * b⁻¹ = ⁅x, b⁆⁻¹ * x := by
    rw [commutatorElement_def]
    group
  have hdC : ⁅x, b⁆ ∈ Subgroup.centralizer (W : Set G) := hbX x hx
  have hcomm : ⁅x, b⁆ * (x * c * x⁻¹) = (x * c * x⁻¹) * ⁅x, b⁆ :=
    (Subgroup.mem_centralizer_iff.mp hdC (x * c * x⁻¹) hxcW).symm
  have hbc' : b * c * b⁻¹ = c := by
    calc b * c * b⁻¹ = c * b * b⁻¹ := by rw [hbc]
      _ = c := by group
  have hy : ⁅x, b⁆⁻¹ * (x * c * x⁻¹) * ⁅x, b⁆ = x * c * x⁻¹ := by
    calc ⁅x, b⁆⁻¹ * (x * c * x⁻¹) * ⁅x, b⁆
        = ⁅x, b⁆⁻¹ * ((x * c * x⁻¹) * ⁅x, b⁆) := by group
      _ = ⁅x, b⁆⁻¹ * (⁅x, b⁆ * (x * c * x⁻¹)) := by rw [hcomm.symm]
      _ = x * c * x⁻¹ := by group
  calc b * (x * c * x⁻¹)
      = (b * x * b⁻¹) * (b * c * b⁻¹) * (b * x * b⁻¹)⁻¹ * b := by group
    _ = (⁅x, b⁆⁻¹ * x) * c * (⁅x, b⁆⁻¹ * x)⁻¹ * b := by rw [hbxb, hbc']
    _ = (x * c * x⁻¹) * b := by
        rw [show (⁅x, b⁆⁻¹ * x) * c * (⁅x, b⁆⁻¹ * x)⁻¹
            = ⁅x, b⁆⁻¹ * (x * c * x⁻¹) * ⁅x, b⁆ from by group, hy]

private theorem conj_mul_inv_mul_eq_self_nc {W : Subgroup G} {b w : G}
    (hW : CFSG.Open.IsElemAbelian 2 W)
    (hbW : b ∈ Subgroup.normalizer (W : Set G))
    (hb2 : b ^ 2 ∈ Subgroup.centralizer (W : Set G)) (hw : w ∈ W) :
    b * (b * w * b⁻¹ * w⁻¹) * b⁻¹ = b * w * b⁻¹ * w⁻¹ := by
  let u : G := b * w * b⁻¹ * w⁻¹
  have hbwW : b * w * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hbW w).mp hw
  have huW : u ∈ W := W.mul_mem hbwW (W.inv_mem hw)
  have hb2w : b * b * w * (b * b)⁻¹ = w := by
    have h := Subgroup.mem_centralizer_iff.mp hb2 w hw
    rw [pow_two] at h
    rw [← h]
    group
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by
    have h2 : u * u = 1 := by simpa [pow_two] using hW.2 u huW
    exact h2)
  have e1 : b * u * b⁻¹ = (b * b * w * (b * b)⁻¹) * (b * w * b⁻¹)⁻¹ := by
    dsimp only [u]
    group
  have e2 : w * (b * w * b⁻¹)⁻¹ = u⁻¹ := by
    dsimp only [u]
    group
  show b * u * b⁻¹ = u
  rw [e1, hb2w, e2, hu_inv]

private theorem conj_commutatorElement_eq_self_nc {W X : Subgroup G} {b w x : G}
    (hW : CFSG.Open.IsElemAbelian 2 W)
    (hbW : b ∈ Subgroup.normalizer (W : Set G))
    (hb2 : b ^ 2 ∈ Subgroup.centralizer (W : Set G))
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hw : w ∈ W)
    (hbX : ⁅x, b⁆ ∈ Subgroup.centralizer (W : Set G))
    (hcase : X ≤ Subgroup.centralizer
      ((W ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G))
    (hx : x ∈ X) : b * ⁅w, x⁆ = ⁅w, x⁆ * b := by
  let u : G := b * w * b⁻¹ * w⁻¹
  have hbwW : b * w * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hbW w).mp hw
  have huW : u ∈ W := W.mul_mem hbwW (W.inv_mem hw)
  have hub : b * u * b⁻¹ = u := conj_mul_inv_mul_eq_self_nc hW hbW hb2 hw
  have huW' : u ∈ W ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine ⟨huW, ?_⟩
    change u ∈ Subgroup.centralizer ({b} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    calc b * u = (b * u * b⁻¹) * b := by group
      _ = u * b := by rw [hub]
  have hux : u * x = x * u := Subgroup.mem_centralizer_iff.mp (hcase hx) u huW'
  have hdC : ⁅x, b⁆⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
    (Subgroup.centralizer (W : Set G)).inv_mem hbX
  have hbxb : b * x * b⁻¹ = ⁅x, b⁆⁻¹ * x := by
    rw [commutatorElement_def]
    group
  have hstep : ⁅u * w, ⁅x, b⁆⁻¹ * x⁆ = ⁅u * w, x⁆ :=
    commutatorElement_mul_right_of_mem_centralizer_nc (W.mul_mem huW hw) hxW hdC
  have hux1 : ⁅u, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hux
  have hcalc : b * ⁅w, x⁆ * b⁻¹ = ⁅w, x⁆ := by
    calc b * ⁅w, x⁆ * b⁻¹ = ⁅b * w * b⁻¹, b * x * b⁻¹⁆ :=
          conjugate_commutatorElement w x b
      _ = ⁅u * w, ⁅x, b⁆⁻¹ * x⁆ := by
          rw [show b * w * b⁻¹ = u * w by dsimp only [u]; group, hbxb]
      _ = ⁅u * w, x⁆ := hstep
      _ = ⁅w * u, x⁆ := by rw [isMulCommutative_iff_of_setLike.mp hW.1 u huW w hw]
      _ = ⁅w, x⁆ := by
          rw [commutatorElement_mul_left_eq_conj_mul, hux1, mul_one]
          group
  calc b * ⁅w, x⁆ = (b * ⁅w, x⁆ * b⁻¹) * b := by group
    _ = ⁅w, x⁆ * b := by rw [hcalc]

theorem IsNatL2Section.not_le {K C W₁ W₀ : Subgroup G} {n : ℕ}
    (h : IsNatL2Section K C W₁ W₀ n) : ¬ W₁ ≤ W₀ := by
  intro hle
  obtain ⟨F, hF, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have htop : W₀.subgroupOf W₁ = ⊤ := Subgroup.subgroupOf_eq_top.mpr hle
  have hβ1 := MonoidHom.ker_eq_top_iff.mp (hβk.trans htop)
  have hsub : Subsingleton (Multiplicative (Fin 2 → F)) := ⟨fun a c => by
    obtain ⟨x, rfl⟩ := hβs a
    obtain ⟨y, rfl⟩ := hβs c
    rw [hβ1]
    rfl⟩
  have : Field F := hF
  have hnt : Nontrivial (Multiplicative (Fin 2 → F)) := by
    refine ⟨Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : F)), 1, ?_⟩
    intro hEq
    have hfun : (Pi.single (0 : Fin 2) (1 : F) : Fin 2 → F) = 0 := by
      exact congrArg Multiplicative.toAdd hEq
    have h10 : (1 : F) = 0 := by simpa using congrFun hfun 0
    exact one_ne_zero h10
  obtain ⟨a, c, hac⟩ := hnt
  exact hac (hsub.elim a c)

theorem not_le_centralizer_commutator_of_isNatL2Section {W X C : Subgroup G} {n : ℕ}
    (hnat : IsNatL2Section X C ⁅W, X⁆ (⁅W, X⁆ ⊓ centralizer (X : Set G)) n) :
    ¬ X ≤ centralizer ((⁅W, X⁆ : Subgroup G) : Set G) := by
  intro h
  apply hnat.not_le
  intro v hv
  refine ⟨hv, ?_⟩
  change v ∈ Subgroup.centralizer (X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (h hx) v hv).symm

theorem mem_centralizer_commutator_of_isNatL2Section [Finite G] {W X C : Subgroup G} {n : ℕ}
    {b : G} (hW : CFSG.Open.IsElemAbelian 2 W) (hX : twoResidual X = X)
    (hXW : X ≤ normalizer (W : Set G))
    (hnat : IsNatL2Section X C ⁅W, X⁆ (⁅W, X⁆ ⊓ centralizer (X : Set G)) n)
    (hbW : b ∈ normalizer (W : Set G)) (hb2 : b ^ 2 ∈ centralizer (W : Set G))
    (hbX : ∀ x ∈ X, ⁅x, b⁆ ∈ centralizer (W : Set G)) :
    b ∈ centralizer ((⁅W, X⁆ : Subgroup G) : Set G) := by
  let W' : Subgroup G := W ⊓ centralizer ({b} : Set G)
  have hXW' : X ≤ normalizer (W' : Set G) :=
    normalizer_inf_centralizer_nc hXW hbX
  by_cases hcase : X ≤ centralizer (W' : Set G)
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.commutator_def] at hy
    have hle : Subgroup.closure {g : G | ∃ w ∈ W, ∃ x ∈ X, ⁅w, x⁆ = g} ≤
        centralizer ({b} : Set G) := by
      rw [Subgroup.closure_le]
      rintro g ⟨w, hw, x, hx, rfl⟩
      change ⁅w, x⁆ ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact conj_commutatorElement_eq_self_nc hW hbW hb2 (hXW hx) hw (hbX x hx) hcase hx
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) b (Set.mem_singleton b)).symm
  · have hW2 : IsPGroup 2 W := fun x => ⟨1, Subtype.ext (by
        simpa using hW.2 (x : G) x.2)⟩
    have hle : ⁅W, X⁆ ≤ W' :=
      commutator_le_of_isNatL2Section hW2 hX hXW inf_le_left hXW' hnat hcase
    have hleC : ⁅W, X⁆ ≤ centralizer ({b} : Set G) := hle.trans inf_le_right
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hleC hy) b (Set.mem_singleton b)).symm

private theorem sSup_le_fixingSubgroup_of_isNatL2Section_nc [Finite G] {M X W C : Subgroup G}
    {n : ℕ} (hW : CFSG.Open.IsElemAbelian 2 W) (hMW : M ≤ normalizer (W : Set G))
    (hXM : X ≤ M) (hX : twoResidual X = X)
    (hnat : IsNatL2Section X C ⁅W, X⁆ (⁅W, X⁆ ⊓ centralizer (X : Set G)) n)
    {𝒮 : Set (Subgroup (MulAut ↥W))} (h𝒮M : ∀ B ∈ 𝒮, B ≤ autOn M W)
    (h𝒮2 : ∀ B ∈ 𝒮, ∀ b ∈ B, b ^ 2 = 1)
    (h𝒮X : ∀ B ∈ 𝒮, ∀ b ∈ B, ∀ x ∈ autOn X W, b * x = x * b) :
    sSup 𝒮 ≤ fixingSubgroup (MulAut ↥W) ((⁅W, X⁆).subgroupOf W : Set ↥W) := by
  have hXW : X ≤ normalizer (W : Set G) := hXM.trans hMW
  refine sSup_le ?_
  intro B hB b hb
  rw [mem_fixingSubgroup_iff (MulAut ↥W)]
  intro v hv
  obtain ⟨m, hmN, -, hmb⟩ := AutOn.mem_autOn_iff_exists.mp (h𝒮M B hB hb)
  have hm2 : m ^ 2 ∈ centralizer (W : Set G) := by
    have hpow : conjAct W (⟨m, hmN⟩ ^ 2) = 1 := by
      rw [map_pow, hmb]
      exact h𝒮2 B hB b hb
    have := (AutOn.conjAct_eq_one_iff (V := W) (⟨m, hmN⟩ ^ 2)).mp hpow
    simpa using this
  have hmX : ∀ x ∈ X, ⁅x, m⁆ ∈ centralizer (W : Set G) := by
    intro x hx
    have hxN : x ∈ normalizer (W : Set G) := hXW hx
    let xN : Subgroup.normalizer (W : Set G) := ⟨x, hxN⟩
    let mN : Subgroup.normalizer (W : Set G) := ⟨m, hmN⟩
    have hax : conjAct W xN ∈ autOn X W := AutOn.conjAct_mem_autOn_of_mem hxN hx
    have hcomm := h𝒮X B hB b hb (conjAct W xN) hax
    have hcomm' : conjAct W mN * conjAct W xN = conjAct W xN * conjAct W mN := by
      simpa only [mN, hmb] using hcomm
    have hmap : conjAct W ⁅xN, mN⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm'.symm
    have := (AutOn.conjAct_eq_one_iff (V := W) ⁅xN, mN⁆).mp hmap
    have hcoe : ((⁅xN, mN⁆ : Subgroup.normalizer (W : Set G)) : G) = ⁅x, m⁆ := by
      dsimp only [xN, mN]
      exact map_commutatorElement (Subgroup.subtype (Subgroup.normalizer (W : Set G))) _ _
    simpa [hcoe] using this
  have hmC : m ∈ centralizer ((⁅W, X⁆ : Subgroup G) : Set G) :=
    mem_centralizer_commutator_of_isNatL2Section hW hX hXW hnat hmN hm2 hmX
  rw [← hmb, MulAut.smul_def]
  apply Subtype.ext
  rw [AutOn.coe_conjAct_apply]
  have hvc : (v : G) ∈ ⁅W, X⁆ := Subgroup.mem_subgroupOf.mp hv
  have hc := Subgroup.mem_centralizer_iff.mp hmC (v : G) hvc
  calc m * (v : G) * m⁻¹ = (v : G) * m * m⁻¹ := by rw [← hc]
    _ = (v : G) := by group

theorem not_autOn_le_sSup_of_isNatL2Section [Finite G] {M X W C : Subgroup G} {n : ℕ}
    (hW : CFSG.Open.IsElemAbelian 2 W) (hMW : M ≤ normalizer (W : Set G)) (hXM : X ≤ M)
    (hX : twoResidual X = X)
    (hnat : IsNatL2Section X C ⁅W, X⁆ (⁅W, X⁆ ⊓ centralizer (X : Set G)) n)
    {𝒮 : Set (Subgroup (MulAut ↥W))} (h𝒮M : ∀ B ∈ 𝒮, B ≤ autOn M W)
    (h𝒮2 : ∀ B ∈ 𝒮, ∀ b ∈ B, b ^ 2 = 1)
    (h𝒮X : ∀ B ∈ 𝒮, ∀ b ∈ B, ∀ x ∈ autOn X W, b * x = x * b) :
    ¬ autOn X W ≤ sSup 𝒮 := by
  have hXW : X ≤ normalizer (W : Set G) := hXM.trans hMW
  intro hle
  have hST := sSup_le_fixingSubgroup_of_isNatL2Section_nc hW hMW hXM hX hnat h𝒮M h𝒮2 h𝒮X
  have hT : autOn X W ≤ fixingSubgroup (MulAut ↥W) ((⁅W, X⁆).subgroupOf W : Set ↥W) :=
    hle.trans hST
  apply not_le_centralizer_commutator_of_isNatL2Section hnat
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hxN : x ∈ normalizer (W : Set G) := hXW hx
  have hax : conjAct W ⟨x, hxN⟩ ∈ autOn X W := AutOn.conjAct_mem_autOn_of_mem hxN hx
  have hfix := (mem_fixingSubgroup_iff (MulAut ↥W)).mp (hT hax)
  have hcommW : ⁅W, X⁆ ≤ W := (Subgroup.le_normalizer_iff_commutator_le_left).mp hXW
  have hvW : v ∈ W := hcommW hv
  have hvsub : (⟨v, hvW⟩ : ↥W) ∈ (⁅W, X⁆).subgroupOf W := by
    rw [Subgroup.mem_subgroupOf]
    exact hv
  have h := hfix ⟨v, hvW⟩ hvsub
  have hcoe : x * v * x⁻¹ = v := by
    have := congrArg Subtype.val h
    simpa [MulAut.smul_def, AutOn.coe_conjAct_apply] using this
  calc v * x = (x * v * x⁻¹) * x := by rw [hcoe]
    _ = x * v := by group

end CFSG.Quasithin
