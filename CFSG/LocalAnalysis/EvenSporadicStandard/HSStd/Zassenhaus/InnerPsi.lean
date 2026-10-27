module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerThreePart
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Sporadic.ThSchreier.GlobalData
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Ind
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.OddStandard.ChildHe
public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath

section General

abbrev innR : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
  (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range

theorem ker_eq_top_of_index_four {A : Type*} [Group A] {H : Subgroup A} (hH : H.index = 4)
    (χ : A →* Multiplicative (ZMod 2)) (hHk : H ≤ χ.ker) {s p : A} (hs : s ∈ χ.ker)
    (hp : p ∈ χ.ker) (hsH : s ∉ H) (hpH : p ∉ H) (hspH : s * p ∉ H) : χ.ker = ⊤ := by
  have hi : χ.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card χ.range ≤ Nat.card (Multiplicative (ZMod 2)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 2 := card_multiplicative_zmod_two
  have h1 := Subgroup.relIndex_mul_index hHk
  rw [hH] at h1
  have h0 : χ.ker.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    omega
  by_cases h2 : χ.ker.index = 1
  · exact Subgroup.index_eq_one.1 h2
  · exfalso
    have h3 : χ.ker.index = 2 := by omega
    rw [h3] at h1
    have h4 : (H.subgroupOf χ.ker).index = 2 := by
      have : H.relIndex χ.ker = 2 := by omega
      exact this
    have h5 := (Subgroup.mul_mem_iff_of_index_two h4 (a := ⟨s, hs⟩) (b := ⟨p, hp⟩))
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h5
    apply hspH
    exact h5.2 (iff_of_false hsH hpH)

theorem zmod_two_eq_one_iff : ∀ x y : Multiplicative (ZMod 2), x * y = 1 → (x = 1 ↔ y = 1) := by
  decide

theorem zmod_two_mul_self : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by
  decide

theorem sq_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {x : G} (hx : orderOf x = 2) :
    x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx, pow_two] at this

theorem commute_conj_of {G : Type*} [Group G] (q k v : G)
    (h : (q⁻¹ * k * q) * v = v * (q⁻¹ * k * q)) : k * (q * v * q⁻¹) = (q * v * q⁻¹) * k := by
  calc k * (q * v * q⁻¹) = q * ((q⁻¹ * k * q) * v) * q⁻¹ := by group
    _ = q * (v * (q⁻¹ * k * q)) * q⁻¹ := by rw [h]
    _ = (q * v * q⁻¹) * k := by group

theorem centralizer_sup_zpowers {G : Type*} [Group G] (X : Subgroup G) (v : G) :
    centralizer ((X ⊔ zpowers v : Subgroup G) : Set G) =
      centralizer (X : Set G) ⊓ centralizer ({v} : Set G) := by
  ext g
  simp only [mem_inf, mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · intro h
    exact ⟨fun k hk => h k (mem_sup_left hk), h v (mem_sup_right (mem_zpowers v))⟩
  · rintro ⟨h1, h2⟩ k hk
    have hle : X ⊔ zpowers v ≤ centralizer ({g} : Set G) :=
      sup_le (fun a ha => mem_centralizer_singleton_iff.2 (h1 a ha))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 h2))
    exact mem_centralizer_singleton_iff.1 (hle hk)

end General

namespace InnerD8Config

variable {G : Type*} [Group G] {L : Subgroup G} {t : G} (c : InnerD8Config L t)

theorem u_mem_P : c.u ∈ c.P := mem_centralizer_singleton_iff.2 rfl

theorem u_sq : c.u * c.u = 1 := sq_eq_one_of_orderOf_eq_two c.u_ord

theorem u₁_sq : c.u₁ * c.u₁ = 1 := sq_eq_one_of_orderOf_eq_two c.u₁_ord

theorem u_ne_one : c.u ≠ 1 := by
  intro h
  have := c.u_ord
  rw [h, orderOf_one] at this
  omega

theorem u₁_ne_one : c.u₁ ≠ 1 := by
  intro h
  have := c.u₁_ord
  rw [h, orderOf_one] at this
  omega

theorem u₁_inv : c.u₁⁻¹ = c.u₁ := inv_eq_of_mul_eq_one_right c.u₁_sq

theorem t_mul_u : t * c.u = c.u * t := mem_centralizer_singleton_iff.1 c.t_mem_P

theorem mem_P_iff {g : G} : g ∈ c.P ↔ g * c.u = c.u * g := mem_centralizer_singleton_iff

theorem u₁_mul_u : c.u₁ * c.u = c.u * c.u₁ := c.mem_P_iff.1 c.u₁_mem.1.1

theorem u₁_comm_L₁ {k : G} (hk : k ∈ c.L₁) : k * c.u₁ = c.u₁ * k :=
  mem_centralizer_iff.1 c.u₁_mem.1.2 k hk

theorem u₁_comm_L₁t {k : G} (hk : k ∈ conjSub t c.L₁) : k * c.u₁ = c.u₁ * k :=
  mem_centralizer_iff.1 c.u₁_mem.2 k hk

theorem u_ne_u₁ : c.u ≠ c.u₁ := by
  intro h
  have h1 := c.u₁_conj
  have h2 : t * c.u₁ * t⁻¹ = c.u₁ := by
    rw [← h]
    calc t * c.u * t⁻¹ = c.u * t * t⁻¹ := by rw [c.t_mul_u]
      _ = c.u := by group
  rw [h2, ← h] at h1
  have h3 : c.u = c.u * c.u := h1
  exact c.u_ne_one (by simpa using h3)

theorem u_mul_u₁_ne_one : c.u * c.u₁ ≠ 1 := by
  intro h
  apply c.u_ne_u₁
  rw [← c.u₁_inv]
  exact eq_inv_of_mul_eq_one_left h

theorem u_mul_u₁_ne_u : c.u * c.u₁ ≠ c.u := by
  intro h
  exact c.u₁_ne_one (by simpa using h)

theorem u_mul_u₁_ne_u₁ : c.u * c.u₁ ≠ c.u₁ := by
  intro h
  exact c.u_ne_one (by simpa using h)

theorem u₁_mem_F : c.u₁ ∈ c.F := c.u₁_mem

theorem comm_P_conjSub {k : G} (hk : k ∈ conjSub t c.L₁) : k ∈ c.P := by
  obtain ⟨b, hb, rfl⟩ := hk
  exact mul_mem (mul_mem c.t_mem_P (c.pair.K_le hb)) (inv_mem c.t_mem_P)

theorem u_mem_F : c.u ∈ c.F := by
  refine ⟨⟨c.u_mem_P, ?_⟩, ?_⟩
  · refine mem_centralizer_iff.2 fun k hk => ?_
    exact c.mem_P_iff.1 (c.pair.K_le hk)
  · refine mem_centralizer_iff.2 fun k hk => ?_
    exact c.mem_P_iff.1 (c.comm_P_conjSub hk)

theorem mem_F_cases {v : G} (hv : v ∈ c.F) : v = 1 ∨ v = c.u ∨ v = c.u₁ ∨ v = c.u * c.u₁ := by
  have hfin : Finite ↥c.F := Nat.finite_of_card_ne_zero (by rw [c.card_F]; norm_num)
  let f : Fin 4 → ↥c.F := ![1, ⟨c.u, c.u_mem_F⟩, ⟨c.u₁, c.u₁_mem_F⟩,
    ⟨c.u * c.u₁, mul_mem c.u_mem_F c.u₁_mem_F⟩]
  have h1 := c.u_ne_one
  have h2 := c.u₁_ne_one
  have h3 := c.u_ne_u₁
  have h4 := c.u_mul_u₁_ne_one
  have h5 := c.u_mul_u₁_ne_u
  have h6 := c.u_mul_u₁_ne_u₁
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [f, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Subtype.ext_iff] at hij ⊢ <;>
      first
      | rfl
      | exact absurd hij h1
      | exact absurd hij.symm h1
      | exact absurd hij h2
      | exact absurd hij.symm h2
      | exact absurd hij h3
      | exact absurd hij.symm h3
      | exact absurd hij h4
      | exact absurd hij.symm h4
      | exact absurd hij h5
      | exact absurd hij.symm h5
      | exact absurd hij h6
      | exact absurd hij.symm h6
  have hb := hf.bijective_of_nat_card_le (by rw [c.card_F]; simp)
  obtain ⟨i, hi⟩ := hb.2 ⟨v, hv⟩
  have hi' : (f i : G) = v := congrArg Subtype.val hi
  fin_cases i
  · left; exact hi'.symm
  · right; left; exact hi'.symm
  · right; right; left; exact hi'.symm
  · right; right; right; exact hi'.symm

theorem comm_F {v : G} (hv : v ∈ c.F) : v * c.u₁ = c.u₁ * v := by
  rcases c.mem_F_cases hv with rfl | rfl | rfl | rfl
  · simp
  · exact c.u₁_mul_u.symm
  · rfl
  · rw [mul_assoc, c.u₁_sq, mul_one, ← mul_assoc, c.u₁_mul_u, mul_assoc, c.u₁_sq, mul_one]

theorem conj_mem_or {p : G} (hp : p ∈ c.P) {k : G} (hk : k ∈ c.L₁) :
    p * k * p⁻¹ ∈ c.L₁ ∨ p * k * p⁻¹ ∈ conjSub t c.L₁ := by
  have hmem : p * k * p⁻¹ ∈ c.L₁.map (MulAut.conj p).toMonoidHom :=
    ⟨k, hk, by simp [MulAut.conj_apply]⟩
  rcases c.pair.perm p hp with h | h
  · left
    rwa [h] at hmem
  · right
    rwa [h] at hmem

theorem conj_mem_or' {p : G} (hp : p ∈ c.P) {k : G} (hk : k ∈ conjSub t c.L₁) :
    p * k * p⁻¹ ∈ c.L₁ ∨ p * k * p⁻¹ ∈ conjSub t c.L₁ := by
  obtain ⟨b, hb, rfl⟩ := hk
  have e : p * ((MulAut.conj t).toMonoidHom b) * p⁻¹ = (p * t) * b * (p * t)⁻¹ := by
    simp [MulAut.conj_apply]
    group
  rw [e]
  exact c.conj_mem_or (mul_mem hp c.t_mem_P) hb

theorem conj_u₁_mem_F {q : G} (hq : q ∈ c.P) : q * c.u₁ * q⁻¹ ∈ c.F := by
  have hq' : q⁻¹ ∈ c.P := inv_mem hq
  refine ⟨⟨mul_mem (mul_mem hq c.u₁_mem.1.1) hq', ?_⟩, ?_⟩
  · refine mem_centralizer_iff.2 fun k hk => ?_
    apply commute_conj_of
    rcases c.conj_mem_or hq' hk with h | h <;> rw [inv_inv] at h
    · exact c.u₁_comm_L₁ h
    · exact c.u₁_comm_L₁t h
  · refine mem_centralizer_iff.2 fun k hk => ?_
    apply commute_conj_of
    rcases c.conj_mem_or' hq' hk with h | h <;> rw [inv_inv] at h
    · exact c.u₁_comm_L₁ h
    · exact c.u₁_comm_L₁t h

theorem conj_u_eq {q : G} (hq : q ∈ c.P) : q * c.u * q⁻¹ = c.u := by
  rw [c.mem_P_iff.1 hq]
  group

theorem conj_u₁_cases {q : G} (hq : q ∈ c.P) :
    q * c.u₁ * q⁻¹ = c.u₁ ∨ q * c.u₁ * q⁻¹ = c.u * c.u₁ := by
  rcases c.mem_F_cases (c.conj_u₁_mem_F hq) with h | h | h | h
  · exfalso
    apply c.u₁_ne_one
    simpa using h
  · exfalso
    apply c.u_ne_u₁
    have : q * c.u₁ * q⁻¹ = q * c.u * q⁻¹ := by rw [h, c.conj_u_eq hq]
    simpa using this.symm
  · exact Or.inl h
  · exact Or.inr h

theorem conj_mul_u₁ {q : G} (hq : q ∈ c.P) :
    q * (c.u * c.u₁) * q⁻¹ = c.u * (q * c.u₁ * q⁻¹) := by
  calc q * (c.u * c.u₁) * q⁻¹ = (q * c.u * q⁻¹) * (q * c.u₁ * q⁻¹) := by group
    _ = c.u * (q * c.u₁ * q⁻¹) := by rw [c.conj_u_eq hq]

open Classical in
@[expose] noncomputable def psi : ↥c.P →* Multiplicative (ZMod 2) where
  toFun q := if (q : G) * c.u₁ * (q : G)⁻¹ = c.u₁ then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' q q' := by
    have hmul : ((q * q' : ↥c.P) : G) * c.u₁ * ((q * q' : ↥c.P) : G)⁻¹ =
        (q : G) * ((q' : G) * c.u₁ * (q' : G)⁻¹) * (q : G)⁻¹ := by
      simp [mul_assoc]
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hsq := zmod_two_mul_self (Multiplicative.ofAdd (1 : ZMod 2))
    rcases c.conj_u₁_cases q.2 with ha | ha <;> rcases c.conj_u₁_cases q'.2 with hb | hb
    · rw [hmul, hb, ha]
      simp
    · rw [hmul, hb, c.conj_mul_u₁ q.2, ha]
      simp [c.u_mul_u₁_ne_u₁]
    · rw [hmul, hb, ha]
      simp [c.u_mul_u₁_ne_u₁]
    · rw [hmul, hb, c.conj_mul_u₁ q.2, ha]
      have : c.u * (c.u * c.u₁) = c.u₁ := by rw [← mul_assoc, c.u_sq, one_mul]
      rw [this]
      simp [c.u_mul_u₁_ne_u₁, hsq]

open Classical in
theorem psi_apply (q : ↥c.P) : c.psi q =
    if (q : G) * c.u₁ * (q : G)⁻¹ = c.u₁ then 1 else Multiplicative.ofAdd 1 := by
  classical
  simp [psi]

theorem commute_iff_conj (q : G) : Commute q c.u₁ ↔ q * c.u₁ * q⁻¹ = c.u₁ := by
  constructor
  · intro h
    rw [h.eq]
    group
  · intro h
    show q * c.u₁ = c.u₁ * q
    calc q * c.u₁ = q * c.u₁ * q⁻¹ * q := by group
      _ = c.u₁ * q := by rw [h]

theorem psi_eq_one_iff (q : ↥c.P) : c.psi q = 1 ↔ Commute (q : G) c.u₁ := by
  classical
  rw [c.commute_iff_conj, c.psi_apply]
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false hne h

theorem psi_ker : c.rho.ker ≤ c.psi.ker := by
  intro q hq
  have h1 := hq
  rw [ker_rho, c.pair.ker_rho, mem_subgroupOf, mem_inf] at h1
  have hF : (q : G) ∈ c.F := ⟨⟨q.2, h1.1⟩, h1.2⟩
  rw [MonoidHom.mem_ker, c.psi_eq_one_iff]
  exact c.comm_F hF

theorem psi_t : c.psi ⟨t, c.t_mem_P⟩ = Multiplicative.ofAdd 1 := by
  rw [psi_apply]
  have : t * c.u₁ * t⁻¹ = c.u * c.u₁ := c.u₁_conj
  simp [this, c.u_mul_u₁_ne_u₁]

theorem rho_of_mem_L₁ (k : ↥c.L₁) :
    c.rho ⟨k, c.pair.K_le k.2⟩ = base (MulAut.conj (c.eL₁ k)) 1 := by
  rw [rho_apply, c.pair.rho_of_mem k k.2, mapEquiv_base, map_one, congr_conj]

@[expose] noncomputable def phi : ↥c.P →* Multiplicative (ZMod 2) :=
  c.psi * swapChar.comp c.rho

theorem phi_apply (q : ↥c.P) : c.phi q = c.psi q * swapChar (c.rho q) := rfl

theorem phi_ker : c.rho.ker ≤ c.phi.ker := by
  intro q hq
  rw [MonoidHom.mem_ker, phi_apply, (MonoidHom.mem_ker).1 (c.psi_ker hq),
    (MonoidHom.mem_ker).1 hq, map_one, one_mul]

theorem phi_t : c.phi ⟨t, c.t_mem_P⟩ = 1 := by
  rw [phi_apply, c.psi_t, c.rho_t, swapChar_tau]
  exact zmod_two_mul_self _

theorem phi_of_commute (q : ↥c.P) (hq : Commute (q : G) c.u₁) {A B : MulAut (alternatingGroup (Fin 6))}
    (h : c.rho q = base A B) : c.phi q = 1 := by
  rw [phi_apply, (c.psi_eq_one_iff q).2 hq, h, swapChar_base, mul_one]

theorem commute_u₁_iff (c : InnerD8Config L t) (hρ : c.rho.range = ⊤)
    (j g : ↥c.P) (hj : Commute (j : G) c.u₁) (hg : Commute (g : G) c.u₁)
    {s p : MulAut (alternatingGroup (Fin 6))} (hjs : c.rho j = Wreath.base 1 s)
    (hgp : c.rho g = Wreath.base 1 p)
    (hs : s ∉ innR) (hp : p ∉ innR) (hsp : s * p ∉ innR) (q : ↥c.P) :
    Commute (q : G) c.u₁ ↔ c.rho q ∈ Wreath.baseSubgroup := by
  have hsurj : Function.Surjective c.rho := MonoidHom.range_eq_top.1 hρ
  let Φb : Wr2 (MulAut (alternatingGroup (Fin 6))) →* Multiplicative (ZMod 2) :=
    c.rho.liftOfSurjective hsurj ⟨c.phi, c.phi_ker⟩
  have hΦb : ∀ w : ↥c.P, Φb (c.rho w) = c.phi w := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨c.phi, c.phi_ker⟩ w
  have hsw : ∀ a b : MulAut (alternatingGroup (Fin 6)), Φb (base b a) = Φb (base a b) := by
    intro a b
    have : base b a = tau * base a b * tau⁻¹ := by
      rw [tau_mul_base, tau_inv, mul_assoc, tau_mul_tau, mul_one]
    rw [this, map_mul, map_mul, mul_comm (Φb tau), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
  have hΦtau : Φb tau = 1 := by
    rw [← c.rho_t, hΦb, c.phi_t]
  let χ : MulAut (alternatingGroup (Fin 6)) →* Multiplicative (ZMod 2) :=
    Φb.comp ((SemidirectProduct.inl : (MulAut (alternatingGroup (Fin 6)) ×
      MulAut (alternatingGroup (Fin 6))) →* Wr2 (MulAut (alternatingGroup (Fin 6)))).comp
      (MonoidHom.inl _ _))
  have hχ : ∀ a, χ a = Φb (base a 1) := fun a => rfl
  have hχs : s ∈ χ.ker := by
    rw [MonoidHom.mem_ker, hχ, ← hsw, ← hjs, hΦb]
    exact c.phi_of_commute j hj hjs
  have hχp : p ∈ χ.ker := by
    rw [MonoidHom.mem_ker, hχ, ← hsw, ← hgp, hΦb]
    exact c.phi_of_commute g hg hgp
  have hχH : innR ≤ χ.ker := by
    rintro _ ⟨m, rfl⟩
    rw [MonoidHom.mem_ker, hχ]
    have h1 := c.rho_of_mem_L₁ (c.eL₁.symm m)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1, hΦb]
    exact c.phi_of_commute _ (c.u₁_comm_L₁ (c.eL₁.symm m).2) h1
  have htop : χ.ker = ⊤ :=
    ker_eq_top_of_index_four CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6 χ hχH hχs hχp
      hs hp hsp
  have hall : ∀ w, Φb w = 1 := by
    intro w
    have hχ1 : ∀ a, Φb (base a 1) = 1 := fun a => by
      have : a ∈ χ.ker := by rw [htop]; exact mem_top a
      exact this
    have hb : ∀ a b, Φb (base a b) = 1 := by
      intro a b
      have : base a b = base a 1 * base 1 b := by rw [base_mul_base, mul_one, one_mul]
      rw [this, map_mul, hsw b 1, hχ1, hχ1, mul_one]
    rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · exact hb a b
    · rw [map_mul, hb, hΦtau, mul_one]
  have hq : c.psi q * swapChar (c.rho q) = 1 := by
    rw [← phi_apply, ← hΦb, hall]
  rw [← c.psi_eq_one_iff, mem_baseSubgroup_iff]
  exact zmod_two_eq_one_iff _ _ hq

theorem rho_base_apply (q : ↥c.P) {A B : MulAut (alternatingGroup (Fin 6))}
    (h : c.rho q = base A B) (k : ↥c.L₁) :
    ((c.eL₁.symm (A (c.eL₁ k)) : ↥c.L₁) : G) = (q : G) * k * (q : G)⁻¹ := by
  have hbase : c.pair.rho q ∈ (baseSubgroup : Subgroup (Wr2 (MulAut ↥c.L₁))) := by
    rw [mem_baseSubgroup_iff, ← swapChar_mapEquiv (MulAut.congr c.eL₁), ← c.rho_apply, h,
      swapChar_base]
  have hn : (q : G) ∈ normalizer (c.L₁ : Set G) := by
    rw [mem_normalizer_iff_map_eq]
    exact (c.pair.rho_mem_baseSubgroup_iff q).1 hbase
  have hr := c.pair.rho_of_normalizes q hn
  have h2 : c.rho q = base (MulAut.congr c.eL₁ (conjAutOf c.L₁ hn))
      (MulAut.congr c.eL₁ (conjAutOf c.L₁ (c.pair.tpt_mem_normalizer hn))) := by
    rw [c.rho_apply, hr, mapEquiv_base]
  rw [h2, base_injective] at h
  rw [← h.1]
  simp [MulAut.congr_apply, conjAutOf_apply]

theorem conj_injective_alt6 {m n : alternatingGroup (Fin 6)} (h : MulAut.conj m = MulAut.conj n) :
    m = n := by
  have hz : n⁻¹ * m ∈ center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff]
    intro g
    have h1 : m * g * m⁻¹ = n * g * n⁻¹ := by
      have := congrArg (fun f : MulAut (alternatingGroup (Fin 6)) => f g) h
      simpa [MulAut.conj_apply] using this
    calc g * (n⁻¹ * m) = n⁻¹ * (n * g * n⁻¹) * m := by group
      _ = n⁻¹ * (m * g * m⁻¹) * m := by rw [h1]
      _ = n⁻¹ * m * g := by group
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
  exact (inv_mul_eq_one.1 hz).symm

theorem card_centralizer_Z [Finite G] (c : InnerD8Config L t) (hρ : c.rho.range = ⊤)
    (hψ : ∀ q : ↥c.P, Commute (q : G) c.u₁ ↔ c.rho q ∈ Wreath.baseSubgroup)
    (hX : ∀ α : MulAut (alternatingGroup (Fin 6)),
      (∀ a ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set _), α a = a) →
      ∃ b ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set _), α = MulAut.conj b) :
    Nat.card ↥(c.P ⊓ centralizer ((c.L₁ ⊓ centralizer ({c.x} : Set G) : Subgroup G) : Set G) ⊓
      centralizer ({c.u₁} : Set G)) = 51840 := by
  classical
  have hsurj : Function.Surjective c.rho := MonoidHom.range_eq_top.1 hρ
  obtain ⟨xb, hxb⟩ : ∃ xb : alternatingGroup (Fin 6), xb = c.eL₁ ⟨c.x, c.x_mem⟩ := ⟨_, rfl⟩
  rw [← hxb] at hX
  have hx3 : orderOf xb = 3 := by
    rw [hxb, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact c.x_ord
  have h9 := card_centralizer_of_orderOf_eq_three hx3
  have hcomm := centralizer_commute_of_orderOf_eq_three hx3
  have key : ∀ k : ↥c.L₁, (k : G) ∈ centralizer ({c.x} : Set G) ↔
      c.eL₁ k ∈ centralizer ({xb} : Set (alternatingGroup (Fin 6))) := by
    intro k
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, hxb, ← map_mul, ← map_mul,
      c.eL₁.injective.eq_iff]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  let Φ₀ : ↥(centralizer ({xb} : Set (alternatingGroup (Fin 6)))) ×
      MulAut (alternatingGroup (Fin 6)) →* Wr2 (MulAut (alternatingGroup (Fin 6))) :=
    (SemidirectProduct.inl : (MulAut (alternatingGroup (Fin 6)) × MulAut (alternatingGroup (Fin 6)))
      →* Wr2 (MulAut (alternatingGroup (Fin 6)))).comp
      (((MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).comp
        (centralizer ({xb} : Set (alternatingGroup (Fin 6)))).subtype).prodMap (MonoidHom.id _))
  have hΦ₀ : ∀ b B, Φ₀ (b, B) = base (MulAut.conj (b : alternatingGroup (Fin 6))) B :=
    fun _ _ => rfl
  have hinj : Function.Injective Φ₀ := by
    rintro ⟨b, B⟩ ⟨b', B'⟩ h
    rw [hΦ₀, hΦ₀, base_injective] at h
    exact Prod.ext (Subtype.ext (conj_injective_alt6 h.1)) h.2
  have hD : Nat.card Φ₀.range = 9 * 1440 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, h9,
      CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
  have hcomap : (c.P ⊓ centralizer ((c.L₁ ⊓ centralizer ({c.x} : Set G) : Subgroup G) : Set G) ⊓
      centralizer ({c.u₁} : Set G)).subgroupOf c.P = Φ₀.range.comap c.rho := by
    ext q
    simp only [mem_subgroupOf, mem_comap, mem_inf]
    constructor
    · rintro ⟨⟨-, hXq⟩, hu⟩
      have hc : Commute (q : G) c.u₁ := mem_centralizer_singleton_iff.1 hu
      obtain ⟨⟨a, B⟩, hab⟩ := (hψ q).1 hc
      have hq : c.rho q = base a B := hab.symm
      have hfix : ∀ b ∈ centralizer ({xb} : Set (alternatingGroup (Fin 6))), a b = b := by
        intro b hb
        obtain ⟨k, rfl⟩ := c.eL₁.surjective b
        have hk : (k : G) ∈ c.L₁ ⊓ centralizer ({c.x} : Set G) := ⟨k.2, (key k).2 hb⟩
        have hcq : (k : G) * q = q * k := mem_centralizer_iff.1 hXq k hk
        have h1 := c.rho_base_apply q hq k
        have h2 : ((c.eL₁.symm (a (c.eL₁ k)) : ↥c.L₁) : G) = k := by
          rw [h1]
          calc (q : G) * k * (q : G)⁻¹ = (k * q) * (q : G)⁻¹ := by rw [hcq]
            _ = k := by group
        have h3 : c.eL₁.symm (a (c.eL₁ k)) = k := Subtype.ext h2
        rw [MulEquiv.symm_apply_eq] at h3
        exact h3
      obtain ⟨b', hb', hab'⟩ := hX a hfix
      exact ⟨(⟨b', hb'⟩, B), by rw [hΦ₀, ← hab', hq]⟩
    · rintro ⟨⟨b', B⟩, hq⟩
      have hq' : c.rho q = base (MulAut.conj (b' : alternatingGroup (Fin 6))) B := hq.symm
      have hbase : c.rho q ∈ (baseSubgroup : Subgroup (Wr2 (MulAut (alternatingGroup (Fin 6))))) :=
        ⟨(MulAut.conj (b' : alternatingGroup (Fin 6)), B), hq⟩
      refine ⟨⟨q.2, ?_⟩, mem_centralizer_singleton_iff.2 ((hψ q).2 hbase)⟩
      refine mem_centralizer_iff.2 fun k hk => ?_
      have hkL : k ∈ c.L₁ := hk.1
      have h1 := c.rho_base_apply q hq' ⟨k, hkL⟩
      have hkc : c.eL₁ ⟨k, hkL⟩ ∈ centralizer ({xb} : Set (alternatingGroup (Fin 6))) :=
        (key ⟨k, hkL⟩).1 hk.2
      have hcb : (b' : alternatingGroup (Fin 6)) * c.eL₁ ⟨k, hkL⟩ =
          c.eL₁ ⟨k, hkL⟩ * (b' : alternatingGroup (Fin 6)) := hcomm _ b'.2 _ hkc
      have hcj : MulAut.conj (b' : alternatingGroup (Fin 6)) (c.eL₁ ⟨k, hkL⟩) =
          c.eL₁ ⟨k, hkL⟩ := by
        rw [MulAut.conj_apply, hcb]
        group
      rw [hcj, MulEquiv.symm_apply_apply] at h1
      have h1' : k = (q : G) * k * (q : G)⁻¹ := h1
      calc k * (q : G) = ((q : G) * k * (q : G)⁻¹) * q := by rw [← h1']
        _ = q * k := by group
  have hle : c.P ⊓ centralizer ((c.L₁ ⊓ centralizer ({c.x} : Set G) : Subgroup G) : Set G) ⊓
      centralizer ({c.u₁} : Set G) ≤ c.P := inf_le_left.trans inf_le_left
  rw [← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hcomap,
    card_comap_of_surj c.rho hsurj, c.card_ker_rho, hD]

theorem card_centralizer_X_sup_u₁ [Finite G] (c : InnerD8Config L t) (hρ : c.rho.range = ⊤)
    (hψ : ∀ q : ↥c.P, Commute (q : G) c.u₁ ↔ c.rho q ∈ Wreath.baseSubgroup)
    (hX : ∀ α : MulAut (alternatingGroup (Fin 6)),
      (∀ a ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set _), α a = a) →
      ∃ b ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set _), α = MulAut.conj b) :
    Nat.card ↥(c.P ⊓ centralizer (((c.L₁ ⊓ centralizer ({c.x} : Set G) : Subgroup G) ⊔
      zpowers c.u₁ : Subgroup G) : Set G)) = 51840 := by
  rw [centralizer_sup_zpowers, ← inf_assoc]
  exact c.card_centralizer_Z hρ hψ hX

end InnerD8Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
