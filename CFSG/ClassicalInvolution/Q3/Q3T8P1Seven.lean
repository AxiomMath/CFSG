module

import CFSG.ClassicalInvolution.Asc77.AscT8BasicEng
public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def L7_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp Ω →
    ∀ W ∈ WSet Ω, ¬ DbarConnected Ω W → MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G]
section Members
variable {Ω : Set (Subgroup G)}
end Members
section Mu
variable {Ω : Set (Subgroup G)}
section DMembers
variable [Finite G]
end DMembers
section DeltaTT

theorem muDelta_mul_self [Finite G] (hΩ : HypOmegaMod Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {a : ↥(muGroup Ω W)} (ha : a ∈ muDelta Ω W) :
    a * a = 1 := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  apply Subtype.ext
  show (a : NQuot (W ⊔ OCW W)) * a = 1
  rw [hra, ← piG_mul (hR.2 hr) (hR.2 hr)]
  exact piG_of_mem_sup (Subgroup.mem_sup_left (Q3CL.Thompson.D_sq_mem hΩ hW hR hr))

theorem muDelta_conj_mem [Finite G] (hΩ : HypOmegaMod Ω) {W : Subgroup G} {a : ↥(muGroup Ω W)}
    (ha : a ∈ muDelta Ω W) (g : ↥(muGroup Ω W)) : g * a * g⁻¹ ∈ muDelta Ω W := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  obtain ⟨m, hm, hgm⟩ := mem_muGroup_iff.mp g.2
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
  refine ⟨conjSub m R, Q3CL.Thompson.conjSub_mem_D hΩ hR hmN, m * r * m⁻¹, conj_mem_conjSub hr, ?_,
      ?_⟩
  · rw [mem_normalizer_iff_of_mem hmN]
    exact hrW
  · show (g : NQuot (W ⊔ OCW W)) * a * (g : NQuot (W ⊔ OCW W))⁻¹ = piG W (m * r * m⁻¹)
    rw [hra, hgm, piG_mul (Subgroup.mul_mem _ hmN (hR.2 hr)) (Subgroup.inv_mem _ hmN),
      piG_mul hmN (hR.2 hr), piG_inv hmN]
end DeltaTT
section Translate
section
variable [Finite G]

theorem exists_not_conn_of_not_connected (hΩ : HypOmegaMod Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ d ∈ muDelta Ω W, ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
  by_contra hcon
  push Not at hcon
  apply hnc
  intro R hR T hT
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR
  obtain ⟨t, ht, htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hT
  have hd : (⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩ :
      ↥(muGroup Ω W)) ∈ muDelta Ω W := ⟨R, hR, r, hr, hrW, rfl⟩
  have ha : (⟨piG W t, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hT ht))⟩ :
      ↥(muGroup Ω W)) ∈ muDelta Ω W := ⟨T, hT, t, ht, htW, rfl⟩
  have hconn := hcon _ hd _ ha
  have key : ∀ x : ↥(muGroup Ω W), Star3T.Conn (muDelta Ω W)
      ⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩ x →
      ∃ R' ∈ DSet Ω W, ∃ r' ∈ R', r' ∉ W ∧ (x : NQuot (W ⊔ OCW W)) = piG W r' ∧
        Relation.ReflTransGen (DbarAdj Ω W) R R' := by
    intro x hx
    induction hx with
    | refl => exact ⟨R, hR, r, hr, hrW, rfl, Relation.ReflTransGen.refl⟩
    | @tail y z _ hyz ih =>
      obtain ⟨Ry, hRy, ry, hry, hryW, hyr, hpath⟩ := ih
      obtain ⟨Rz, hRz, rz, hrz, hrzW, hzr⟩ := hyz.2.1
      refine ⟨Rz, hRz, rz, hrz, hrzW, hzr, hpath.tail ⟨hRz, ?_⟩⟩
      have hryN := hRy.2 hry
      have hrzN := hRz.2 hrz
      by_cases hyz' : y = z
      · right
        have e : piG W rz = piG W ry := by rw [← hzr, ← hyr, hyz']
        exact ⟨le_sup_of_piG_eq hry hRy.2 hRz.2 (fun x hx hxW =>
            (Q3CL.Thompson.D_piG_eq hΩ hW hRz hx hrz hxW hrzW).trans e),
          le_sup_of_piG_eq hrz hRz.2 hRy.2 (fun x hx hxW =>
            (Q3CL.Thompson.D_piG_eq hΩ hW hRy hx hry hxW hryW).trans e.symm)⟩
      · left
        refine ⟨fun hle => hyz' ?_, fun x hx x' hx' => ?_⟩
        · apply Subtype.ext
          rw [hyr, hzr]
          exact (Q3CL.Thompson.piG_eq_of_le_sup hΩ hW hRy hRz hle hry hrz hryW hrzW).symm
        · by_cases hxW : x ∈ W
          · exact Subgroup.mem_sup_left (comm_mem_of_mem hxW (hRz.2 hx'))
          · by_cases hx'W : x' ∈ W
            · have h1 : x * x' * x⁻¹ * x'⁻¹ = (x * x' * x⁻¹) * x'⁻¹ := rfl
              have h2 : x * x' * x⁻¹ ∈ W := by
                have := (Subgroup.mem_normalizer_iff.mp (hRy.2 hx) x').mp hx'W
                exact this
              exact Subgroup.mem_sup_left (W.mul_mem h2 (W.inv_mem hx'W))
            · have hc : y * z = z * y := hyz.2.2
              have hc' : piG W x * piG W x' = piG W x' * piG W x := by
                rw [Q3CL.Thompson.D_piG_eq hΩ hW hRy hx hry hxW hryW,
                  Q3CL.Thompson.D_piG_eq hΩ hW hRz hx' hrz hx'W hrzW, ← hyr, ← hzr]
                exact congrArg Subtype.val hc
              exact (piG_comm_iff (hRy.2 hx) (hRz.2 hx')).mp hc'
  obtain ⟨R', hR', r', hr', hr'W, hr'eq, hpath⟩ := key _ hconn
  have hr'eq' : piG W t = piG W r' := hr'eq
  refine hpath.tail ⟨hT, Or.inr ⟨?_, ?_⟩⟩
  · exact le_sup_of_piG_eq hr' hR'.2 hT.2 (fun x hx hxW =>
      (Q3CL.Thompson.D_piG_eq hΩ hW hT hx ht hxW htW).trans hr'eq')
  · exact le_sup_of_piG_eq ht hT.2 hR'.2 (fun x hx hxW =>
      (Q3CL.Thompson.D_piG_eq hΩ hW hR' hx hr' hxW hr'W).trans hr'eq'.symm)
end
end Translate
end Mu
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
    CFSG.ClassicalInvolution.Asc77.Thompson

@[expose] def ThompsonCube : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, r ∉ W → t ∉ W →
      r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨ (r * t) ^ 3 ∈ W ⊔ OCW W

@[expose] def ThompsonStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ S ∈ DSet Ω W,
      ∀ r ∈ R, ∀ t ∈ T, ∀ s ∈ S, r ∉ W → t ∉ W → s ∉ W →
        r * t * r⁻¹ * t⁻¹ ∉ W ⊔ OCW W →
          s * r * s⁻¹ * r⁻¹ ∈ W ⊔ OCW W ∨ s * t * s⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨
            s * (r * t * r⁻¹) * s⁻¹ * (r * t * r⁻¹)⁻¹ ∈ W ⊔ OCW W

@[expose] def ThompsonClique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp Ω →
    ∀ W ∈ WSet Ω, ¬ DbarConnected Ω W → ∀ d ∈ muDelta Ω W,
      (Star3T.cent (muDelta Ω W) d).ncard = 1 ∨ (Star3T.cent (muDelta Ω W) d).ncard = 2 ∨
        ((Star3T.cent (muDelta Ω W) d).ncard = 4 ∧
          16 ≤ Nat.card ↥(Subgroup.closure (Star3T.cent (muDelta Ω W) d)))
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem isStar_muDelta (hΩ : HypOmegaMod Ω) [Finite G]
    (hW : W ∈ WSet Ω)
    (hstar : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ S ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, ∀ s ∈ S,
      r ∉ W → t ∉ W → s ∉ W → r * t * r⁻¹ * t⁻¹ ∉ W ⊔ OCW W →
        s * r * s⁻¹ * r⁻¹ ∈ W ⊔ OCW W ∨ s * t * s⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨
          s * (r * t * r⁻¹) * s⁻¹ * (r * t * r⁻¹)⁻¹ ∈ W ⊔ OCW W) :
    Star3T.IsStar (muDelta Ω W) := by
  rintro a ha b hb hab c hc
  have haa := muDelta_mul_self hΩ hW ha
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  obtain ⟨T, hT, t, ht, htW, htb⟩ := hb
  obtain ⟨S, hS, s, hs, hsW, hsc⟩ := hc
  have hrN := hR.2 hr
  have htN := hT.2 ht
  have hsN := hS.2 hs
  have hnc : r * t * r⁻¹ * t⁻¹ ∉ W ⊔ OCW W := fun h => hab (by
    apply Subtype.ext
    show (a : NQuot (W ⊔ OCW W)) * b = b * a
    rw [hra, htb]
    exact (piG_comm_iff hrN htN).mpr h)
  rcases hstar R hR T hT S hS r hr t ht s hs hrW htW hsW hnc with h | h | h
  · left
    apply Subtype.ext
    show (c : NQuot (W ⊔ OCW W)) * a = a * c
    rw [hra, hsc]
    exact (piG_comm_iff hsN hrN).mpr h
  · right
    left
    apply Subtype.ext
    show (c : NQuot (W ⊔ OCW W)) * b = b * c
    rw [htb, hsc]
    exact (piG_comm_iff hsN htN).mpr h
  · right
    right
    apply Subtype.ext
    have hrtr : r * t * r⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN)
    have hinv : (piG W r)⁻¹ = piG W r := by
      have : (a : NQuot (W ⊔ OCW W)) * a = 1 := congrArg Subtype.val haa
      rw [hra] at this
      exact inv_eq_of_mul_eq_one_left this
    have e : (a : NQuot (W ⊔ OCW W)) * b * a = piG W (r * t * r⁻¹) := by
      rw [hra, htb, piG_mul (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN),
        piG_mul hrN htN, piG_inv hrN, hinv]
    show (c : NQuot (W ⊔ OCW W)) * ((a : NQuot (W ⊔ OCW W)) * b * a) =
      ((a : NQuot (W ⊔ OCW W)) * b * a) * c
    rw [e, hsc]
    exact (piG_comm_iff hsN hrtr).mpr h
section Generators
variable [Finite G]

theorem exists_zpowers_eq_inf_W {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod Ω) {W : Subgroup G} (hW :
    W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) : ∃ u : G, Subgroup.zpowers u = R ⊓ W := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hcyc := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW hR hK hRK).2.2.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(R ⊓ W))
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact ⟨k, congrArg Subtype.val hk⟩
end Generators

theorem isTT_muDelta (hΩ : HypOmegaMod Ω) [Finite G]
    (hW : W ∈ WSet Ω)
    (hcube : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, r ∉ W → t ∉ W →
      r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨ (r * t) ^ 3 ∈ W ⊔ OCW W) :
    Star3T.IsTT (muDelta Ω W) where
  mul_self _ ha := muDelta_mul_self hΩ hW ha
  ne_one _ ha := muDelta_ne_one hW ha
  conj_mem _ ha g := muDelta_conj_mem hΩ ha g
  closure_eq_top := closure_muDelta_eq_top Ω W
  comm_or_cube := muDelta_comm_or_cube hcube

theorem muDelta_classification (h1 : ThompsonCube) (h2 : ThompsonStar)
    (h3 : ThompsonClique) [Finite G] (hP : PartIHyp Ω) (hW : W ∈ WSet Ω)
    (hnc : ¬ DbarConnected Ω W) :
    (∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 3), ∀ x, x ∈ muDelta Ω W ↔ (e x).IsSwap) ∨
    (∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4), ∀ x, x ∈ muDelta Ω W ↔ (e x).IsSwap) ∨
    MuIsoWylD4 Ω W := by
  obtain ⟨hΩ, hcls, hA⟩ := hP
  have hTT := isTT_muDelta hΩ hW (h1 G Ω ⟨hΩ, hcls, hA⟩ W hW)
  have hS := isStar_muDelta hΩ hW (h2 G Ω ⟨hΩ, hcls, hA⟩ W hW)
  obtain ⟨d, hd, a, ha, hconn⟩ := exists_not_conn_of_not_connected hΩ hW hnc
  rcases h3 G Ω ⟨hΩ, hcls, hA⟩ W hW hnc d hd with hk | hk | ⟨hk, hcard⟩
  · exact Or.inl (Star3T.exists_mulEquiv_perm_three hTT hS hd ha hconn hk)
  · exact Or.inr (Or.inl (Star3T.exists_mulEquiv_perm_four hTT hS hd ha hconn hk))
  · refine Or.inr (Or.inr ?_)
    exact Star3T.nonempty_mulEquiv_of_card_four hTT hS hd ha hconn hk hcard
      (M := coxeterD4) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
      coxeterD4.toCoxeterSystem
end Thompson

theorem l7_10_of_inputs (h1 : ThompsonCube) (h2 : ThompsonStar)
    (h3 : ThompsonClique) : L7_10 := by
  intro G _ _ Ω hP W hW hnc
  rcases Thompson.muDelta_classification h1 h2 h3 hP hW hnc with ⟨e, -⟩ | ⟨e, -⟩ | h
  · exact Or.inl ⟨e⟩
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact Or.inr (Or.inr h)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

@[expose] def ThompsonKey : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J →
      T ≤ R ⊔ W ⊔ OCW W
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}
section Fixed
variable [Finite G]

theorem exists_orderOf_four (hΩ : HypOmegaMod Ω)
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    ∃ w ∈ R ⊓ W, orderOf w = 4 := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hinfo := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hR hK hRK
  obtain ⟨g, hg⟩ := exists_zpowers_eq_inf_W hΩ hW hR
  have hgm : g ∈ R ⊓ W := hg ▸ Subgroup.mem_zpowers g
  obtain ⟨j, hj⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup hRK.2.1 hgm.1
  have hcard : orderOf g = Nat.card ↥(R ⊓ W) := by rw [← hg, Nat.card_zpowers]
  have h4 : 4 ≤ orderOf g := by rw [hcard]; exact hinfo.2.2.2.1
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 4 ∣ orderOf g := by
    rw [hj]
    exact ⟨2 ^ (j - 2), by rw [show j = (j - 2) + 2 by omega, pow_add]; ring_nf; simp⟩
  refine ⟨g ^ (orderOf g / 4), Subgroup.pow_mem _ hgm _, ?_⟩
  exact orderOf_pow_orderOf_div (by omega) hdvd
end Fixed
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.img_eq_of_K_eq (ρ σ : Rep Ω W) (h :
    ρ.K = σ.K) : ρ.img = σ.img := by
  have hle : σ.R ≤ ρ.R ⊔ W ⊔ OCW W :=
    c.hkey ρ.R ρ.hR σ.R σ.hR ρ.K ρ.hK ρ.hRK.1 (h ▸ σ.hRK.1)
  exact (Q3CL.Thompson.piG_eq_of_le_sup c.hΩ c.hW ρ.hR σ.hR hle ρ.hr σ.hr ρ.hrW σ.hrW).symm

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.omega_of_comm (ρ σ : Rep Ω W) (hne :
    ρ.K ≠ σ.K)
    (hcomm : ρ.img * σ.img = σ.img * ρ.img) : σ.K ∈ omegaNbr Ω ρ.K := by
  by_contra hnot
  exact c.noncomm ρ σ hne hnot hcomm

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.comm_of_omega (ρ σ : Rep Ω W) (hnbr :
    σ.K ∈ omegaNbr Ω ρ.K) :
    ρ.img * σ.img = σ.img * ρ.img :=
  Q3CL.Thompson.piG_comm_of_mem_omegaNbr (l6_2) c.hΩ c.hW c.hkey ρ.hK σ.hK hnbr.2.1.symm ρ.hR σ.hR
    ρ.hRK σ.hRK hnbr ρ.hr σ.hr ρ.hrW

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.centralizes (ρ σ : Rep Ω W) (hnbr :
    σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : v ∈ σ.K ⊓ W) :
    ρ.r * v = v * ρ.r :=
  Q3CL.Thompson.centralizes_inf_W_of_mem_omegaNbr (l6_2) c.hΩ c.hW ρ.hK σ.hK hnbr.2.1.symm ρ.hR
    σ.hR ρ.hRK σ.hRK hnbr ρ.hr hv

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conj_inv (ρ : Rep Ω W) {u : G} (hu : u
    ∈ ρ.K ⊓ W) : ρ.r * u * ρ.r⁻¹ = u⁻¹ :=
  Q3CL.Thompson.conj_eq_inv_of_mem_inf_W c.hΩ c.hW ρ.hK ρ.hR ρ.hRK ρ.hr ρ.hrW hu

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.comm_mem (ρ σ : Rep Ω W) (hne : ρ.K ≠
    σ.K) {v : G} (hv : v ∈ σ.K ⊓ W) :
    ρ.r * v * ρ.r⁻¹ * v⁻¹ ∈ ρ.K ⊓ W :=
  Q3CL.Thompson.comm_mem_inf_W c.hΩ c.hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK ρ.hr hv

@[expose] def _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.W4 : Subgroup G where
  carrier := {x | x ∈ W ∧ x ^ 4 = 1}
  one_mem' := ⟨W.one_mem, one_pow 4⟩
  mul_mem' := by
    rintro x y ⟨hxW, hx⟩ ⟨hyW, hy⟩
    refine ⟨W.mul_mem hxW hyW, ?_⟩
    rw [(show Commute x y from c.comm_W x hxW y hyW).mul_pow, hx, hy, one_mul]
  inv_mem' := by
    rintro x ⟨hxW, hx⟩
    refine ⟨W.inv_mem hxW, ?_⟩
    rw [inv_pow, hx, inv_one]

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.W4_le : c.W4 ≤ W := fun _ hx => hx.1

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conj_mem_W4 {r : G} (hr : r ∈
    Subgroup.normalizer (W : Set G)) {x : G} (hx : x ∈ c.W4) :
    r * x * r⁻¹ ∈ c.W4 := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hr x).mp hx.1, ?_⟩
  rw [conj_pow, hx.2]
  group
end Ctx
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem ne_and_not_omegaNbr_of_noncomm (h62 : L6_2) (hΩ : HypOmegaMod Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) {r t : G} (hr : r ∈ R) (ht : t ∈ T)
    (hrW : r ∉ W) (htW : t ∉ W)
    (hnc : piG W r * piG W t ≠ piG W t * piG W r) : K ≠ J ∧ J ∉ omegaNbr Ω K := by
  have hKJ : K ≠ J := by
    intro h
    subst h
    exact hnc (Q3CL.Thompson.piG_comm_of_le hΩ hW hR hT (hkey R hR T hT K hK hRK.1 hTJ.1) hr ht hrW
        htW)
  exact ⟨hKJ, fun hnbr => hnc (Q3CL.Thompson.piG_comm_of_mem_omegaNbr h62 hΩ hW hkey hK hJ hKJ hR
      hT hRK
    hTJ hnbr hr ht hrW)⟩

theorem piG_comm_third (h62 : L6_2) (hΩ : HypOmegaMod Ω)
    (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J L R T S : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hL : L ∈ Ω) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hS : S ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hSL : IsSylow2In S L) {r t s : G} (hr : r ∈ R) (ht : t ∈ T) (hs : s ∈ S) (hrW : r ∉ W)
    (htW : t ∉ W) (hsW : s ∉ W)
    (hrt : piG W r * piG W t ≠ piG W t * piG W r)
    (hsr : piG W s * piG W r ≠ piG W r * piG W s)
    (hst : piG W s * piG W t ≠ piG W t * piG W s) :
    piG W s * piG W (r * t * r⁻¹) = piG W (r * t * r⁻¹) * piG W s := by
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  obtain ⟨hKJ, hnotJK⟩ := ne_and_not_omegaNbr_of_noncomm h62 hΩ hW hkey hK hJ hR hT hRK hTJ
    hr ht hrW htW hrt
  obtain ⟨hLK, hnotKL⟩ := ne_and_not_omegaNbr_of_noncomm h62 hΩ hW hkey hL hK hS hR hSL hRK
    hs hr hsW hrW hsr
  obtain ⟨hLJ, hnotJL⟩ := ne_and_not_omegaNbr_of_noncomm h62 hΩ hW hkey hL hJ hS hT hSL hTJ
    hs ht hsW htW hst
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hJ
  obtain ⟨ℓ, hℓ⟩ := hΩ.exists_uniqueInvolution hL
  have hzW : z ∈ K ⊓ W := Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hK hR hRK hz
  have hjW : j ∈ J ⊓ W := Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJ hT hTJ hj
  have hℓW : ℓ ∈ L ⊓ W := Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hL hS hSL hℓ
  have hrj := Q3CL.Thompson.conj_involution_eq_mul h62 hΩ hW hK hJ hKJ hR hT hRK hTJ hnotJK hz hj
      hr hrW
  have hsz := Q3CL.Thompson.conj_involution_eq_mul h62 hΩ hW hL hK hLK hS hR hSL hRK hnotKL hℓ hz
      hs hsW
  have hsj := Q3CL.Thompson.conj_involution_eq_mul h62 hΩ hW hL hJ hLJ hS hT hSL hTJ hnotJL hℓ hj
      hs hsW
  have hszj : s * (z * j) = (z * j) * s := by
    have h1 : s * (z * j) * s⁻¹ = z * j := by
      calc s * (z * j) * s⁻¹ = (s * z * s⁻¹) * (s * j * s⁻¹) := by group
        _ = (ℓ * z) * (ℓ * j) := by rw [hsz, hsj]
        _ = ℓ * (z * ℓ) * j := by group
        _ = ℓ * (ℓ * z) * j := by rw [hWab z hzW.2 ℓ hℓW.2]
        _ = (ℓ * ℓ) * (z * j) := by group
        _ = z * j := by rw [hℓ.sq, one_mul]
    calc s * (z * j) = (s * (z * j) * s⁻¹) * s := by group
      _ = (z * j) * s := by rw [h1]
  have hzjW : z * j ∈ W := W.mul_mem hzW.2 hjW.2
  have hSc := Q3CL.Thompson.le_centralizer_of_mem hΩ hW hS hs hsW hzjW hszj
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have hsN : s ∈ Subgroup.normalizer (W : Set G) := hS.2 hs
  have hP : conjSub r T ∈ DSet Ω W := Q3CL.Thompson.conjSub_mem_D hΩ hT hrN
  have hKP : conjSub r J ∈ Ω := hΩ.conjInvariant r J hJ
  have hPKP : IsSylow2In (conjSub r T) (conjSub r J) := hTJ.conj r
  have hzP : IsUniqueInvolution (conjSub r J) (z * j) := hrj ▸ hj.conj r
  have hrtP : r * t * r⁻¹ ∈ conjSub r T := conj_mem_conjSub ht
  have hrtW : r * t * r⁻¹ ∉ W := fun h => htW ((mem_normalizer_iff_of_mem hrN t).mp h)
  by_cases hLP : L = conjSub r J
  · subst hLP
    have hle := hkey (conjSub r T) hP S hS (conjSub r J) hKP hPKP.1 hSL.1
    exact (Q3CL.Thompson.piG_comm_of_le hΩ hW hP hS hle hrtP hs hrtW hsW).symm
  · have hSN : S ≤ Subgroup.normalizer ((conjSub r J : Subgroup G) : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hKP hL (Ne.symm hLP) hzP hSL.1 hSL.2.1
        (by have := hΩ.eight_le_of_mem_RSet hS.1; omega) hSc
    have hnbr : L ∈ omegaNbr Ω (conjSub r J) := ⟨hL, hLP, S, hS.1, hSL.1, hSN⟩
    exact (Q3CL.Thompson.piG_comm_of_mem_omegaNbr h62 hΩ hW hkey hKP hL (Ne.symm hLP) hP hS hPKP
        hSL hnbr
      hrtP hs hrtW).symm
end Thompson

theorem thompsonStar_of_key (hkey : ThompsonKey) : ThompsonStar := by
  intro G _ _ Ω hP W hW R hR T hT S hS r hr t ht s hs hrW htW hsW hnc
  have hΩ : HypOmegaMod Ω := hP.hyp
  have h62 := l6_2
  have hkey' := hkey G Ω hP W hW
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  obtain ⟨L, hL, hSL⟩ := exists_isSylow2In_of_mem_RSet hS.1
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  have hsN : s ∈ Subgroup.normalizer (W : Set G) := hS.2 hs
  have hrtrN : r * t * r⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN)
  by_cases h1 : s * r * s⁻¹ * r⁻¹ ∈ W ⊔ OCW W
  · exact Or.inl h1
  by_cases h2 : s * t * s⁻¹ * t⁻¹ ∈ W ⊔ OCW W
  · exact Or.inr (Or.inl h2)
  right
  right
  refine (Thompson.piG_comm_iff hsN hrtrN).mp ?_
  refine Thompson.piG_comm_third h62 hΩ hW
    (fun R hR T hT J hJ hRJ hTJ' => hkey' R hR T hT J hJ hRJ hTJ') hK hJ hL hR hT hS hRK hTJ hSL
    hr ht hs hrW htW hsW ?_ ?_ ?_
  · exact fun h => hnc ((Thompson.piG_comm_iff hrN htN).mp h)
  · exact fun h => h1 ((Thompson.piG_comm_iff hsN hrN).mp h)
  · exact fun h => h2 ((Thompson.piG_comm_iff hsN htN).mp h)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77

theorem thompsonStar : ThompsonStar := thompsonStar_of_key (fun _ _ _ _ hP => Q3CL.thompsonKey hP)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Component
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Component
section Sylow
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_mem_omegaNbr (hΩ : HypOmegaMod Ω)
    {K R : Subgroup G} {S : Sylow 2 G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K)
    (hRS : R ≤ (S : Subgroup G)) {z : G} (hz : IsUniqueInvolution K z) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hfix : conjSub s R ≠ R) : conjSub s K ∈ omegaNbr Ω K := by
  exact CFSG.ClassicalInvolution.Asc77.T8.conjSub_mem_omegaNbrE hΩ.conjInvariant
    (fun hM hR hRM => Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hM hR hRM)
    (fun hR => hΩ.eight_le_of_mem_RSet hR) (l6_7_proved G Ω hΩ S)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      hΩ.le_normalizer_of_le_centralizer hK hJ hKJ hz hAJ hA2 hA3 hAc)
    hK hR hRK hRS hz hs hfix

theorem sylow_le_sigmaNorm (hΩ : HypOmegaMod Ω)
    {K R : Subgroup G} {S : Sylow 2 G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K)
    (hRS : R ≤ (S : Subgroup G)) {z : G} (hz : IsUniqueInvolution K z) :
    (S : Subgroup G) ≤ sigmaNorm Ω K := by
  intro s hs
  rw [mem_sigmaNorm_iff hΩ.conjInvariant hK]
  by_cases hfix : conjSub s R = R
  · rw [Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK hR hRK hfix]
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨hΩ.conjInvariant s K hK, Or.inl (conjSub_mem_omegaNbr hΩ hK hR hRK hRS hz hs hfix)⟩
end Sylow
section Group274
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Group274
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

@[expose] def _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.U4 (c : Q3CL.Thompson.Ctx Ω W)
    (ρ : Rep Ω W) : Subgroup G := ρ.K ⊓ c.W4

@[expose] def _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.UU (c : Q3CL.Thompson.Ctx Ω W)
    {ι : Type*} (ρ : ι → Rep Ω W) (S : Set ι) : Subgroup G :=
  Subgroup.closure {x | ∃ s ∈ S, x ∈ c.U4 (ρ s)}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.U4_le_W (ρ : Rep Ω W) : c.U4 ρ ≤ W :=
    fun _ hx => hx.2.1

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.mem_inf_of_mem_U4 {ρ : Rep Ω W} {x :
    G} (hx : x ∈ c.U4 ρ) : x ∈ ρ.K ⊓ W :=
  ⟨hx.1, hx.2.1⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.U4_le_UU {ι : Type*} (ρ : ι → Rep Ω W)
    {S : Set ι} {s : ι} (hs : s ∈ S) :
    c.U4 (ρ s) ≤ c.UU ρ S := fun _ hx => Subgroup.subset_closure ⟨s, hs, hx⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.UU_le_W4 {ι : Type*} (ρ : ι → Rep Ω W)
    (S : Set ι) : c.UU ρ S ≤ c.W4 := by
  rw [CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.UU, Subgroup.closure_le]
  rintro x ⟨s, -, hx⟩
  exact hx.2

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conj_mem_U4 (ρ σ : Rep Ω W) {x : G}
    (hx : x ∈ c.U4 σ) :
    ρ.r * x * ρ.r⁻¹ ∈ c.U4 ρ ⊔ c.U4 σ := by
  have hrN := ρ.r_mem_normalizer
  have hxW : x ∈ σ.K ⊓ W := c.mem_inf_of_mem_U4 hx
  by_cases hK : ρ.K = σ.K
  · have hxρ : x ∈ ρ.K ⊓ W := by rw [hK]; exact hxW
    rw [c.conj_inv ρ hxρ]
    exact Subgroup.mem_sup_right ((c.U4 σ).inv_mem hx)
  · have hcomm := c.comm_mem ρ σ hK hxW
    have e1 : ρ.r * x * ρ.r⁻¹ * x⁻¹ ∈ c.U4 ρ :=
      ⟨hcomm.1, c.W4.mul_mem (c.conj_mem_W4 hrN ⟨hx.2.1, hx.2.2⟩) (c.W4.inv_mem ⟨hx.2.1, hx.2.2⟩)⟩
    have e2 : ρ.r * x * ρ.r⁻¹ = (ρ.r * x * ρ.r⁻¹ * x⁻¹) * x := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left e1) (Subgroup.mem_sup_right hx)

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.normalizes_UU {ι : Type*} (ρ : ι → Rep
    Ω W) {S : Set ι} {s : ι} (hs : s ∈ S) :
    (ρ s).r ∈ Subgroup.normalizer ((c.UU ρ S : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_le
  have key : ∀ x ∈ c.UU ρ S, (ρ s).r * x * (ρ s).r⁻¹ ∈ c.UU ρ S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, hyt⟩ := hy
      have := c.conj_mem_U4 (ρ s) (ρ t) hyt
      exact (sup_le (c.U4_le_UU ρ hs) (c.U4_le_UU ρ ht)) this
    | one => simp
    | mul y z _ _ hy hz =>
      have e : (ρ s).r * (y * z) * (ρ s).r⁻¹ =
          ((ρ s).r * y * (ρ s).r⁻¹) * ((ρ s).r * z * (ρ s).r⁻¹) := by group
      rw [e]
      exact (c.UU ρ S).mul_mem hy hz
    | inv y _ hy =>
      have e : (ρ s).r * y⁻¹ * (ρ s).r⁻¹ = ((ρ s).r * y * (ρ s).r⁻¹)⁻¹ := by group
      rw [e]
      exact (c.UU ρ S).inv_mem hy
  rintro _ ⟨x, hx, rfl⟩
  exact key x hx

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_mul_of_mem_UU_insert {ι :
    Type*} (ρ : ι → Rep Ω W) {B : Set ι} {a : ι} {g : G}
    (hg : g ∈ c.UU ρ (insert a B)) :
    ∃ x ∈ c.U4 (ρ a), ∃ a₁ ∈ c.UU ρ B, g = x * a₁ := by
  have hcomm : ∀ x ∈ c.U4 (ρ a), ∀ y ∈ c.UU ρ B, x * y = y * x := fun x hx y hy =>
    c.comm_W x (c.U4_le_W _ hx) y (c.W4_le (c.UU_le_W4 ρ B hy))
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨t, ht, hyt⟩ := hy
    rcases ht with rfl | ht
    · exact ⟨y, hyt, 1, Subgroup.one_mem _, by simp⟩
    · exact ⟨1, Subgroup.one_mem _, y, c.U4_le_UU ρ ht hyt, by simp⟩
  | one => exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨x, hx, a₁, ha₁, rfl⟩ := hy
    obtain ⟨x', hx', a₁', ha₁', rfl⟩ := hz
    refine ⟨x * x', (c.U4 (ρ a)).mul_mem hx hx', a₁ * a₁', (c.UU ρ B).mul_mem ha₁ ha₁', ?_⟩
    calc x * a₁ * (x' * a₁') = x * (a₁ * x') * a₁' := by simp only [mul_assoc]
      _ = x * (x' * a₁) * a₁' := by rw [← hcomm x' hx' a₁ ha₁]
      _ = x * x' * (a₁ * a₁') := by simp only [mul_assoc]
  | inv y _ hy =>
    obtain ⟨x, hx, a₁, ha₁, rfl⟩ := hy
    refine ⟨x⁻¹, (c.U4 (ρ a)).inv_mem hx, a₁⁻¹, (c.UU ρ B).inv_mem ha₁, ?_⟩
    rw [mul_inv_rev]
    exact (Commute.inv_inv (show Commute x a₁ from hcomm x hx a₁ ha₁)).eq.symm
section Frame
variable (rep : ↥(muGroup Ω W) → Rep Ω W)
  (hrep : ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)))
include c hrep

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.rep_K_ne {x y : ↥(muGroup Ω W)} (hx :
    x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) : (rep x).K ≠ (rep y).K := by
  intro h
  apply hne
  have := c.img_eq_of_K_eq (rep x) (rep y) h
  rw [hrep x hx, hrep y hy] at this
  exact Subtype.ext this

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.rep_omega {x y : ↥(muGroup Ω W)} (hx :
    x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hne : x ≠ y) (hcomm : x * y = y * x) : (rep y).K ∈ omegaNbr Ω (rep x).K := by
  refine c.omega_of_comm (rep x) (rep y) (c.rep_K_ne rep hrep hx hy hne) ?_
  rw [hrep x hx, hrep y hy]
  exact congrArg Subtype.val hcomm

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.rep_noncomm {x y : ↥(muGroup Ω W)} (hx
    : x ∈ muDelta Ω W) (hy : y ∈ muDelta Ω W)
    (hnc : x * y ≠ y * x) : (rep x).K ≠ (rep y).K ∧ (rep y).K ∉ omegaNbr Ω (rep x).K := by
  refine ⟨fun h => hnc ?_, fun hnbr => hnc ?_⟩
  · have := c.img_eq_of_K_eq (rep x) (rep y) h
    rw [hrep x hx, hrep y hy] at this
    rw [Subtype.ext this]
  · have := c.comm_of_omega (rep x) (rep y) hnbr
    rw [hrep x hx, hrep y hy] at this
    exact Subtype.ext this

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.centralizes_UU {x : ↥(muGroup Ω W)}
    (hx : x ∈ muDelta Ω W) {S : Set ↥(muGroup Ω W)}
    (hS : ∀ s ∈ S, s ∈ muDelta Ω W ∧ x ≠ s ∧ x * s = s * x) :
    ∀ g ∈ c.UU rep S, (rep x).r * g * (rep x).r⁻¹ = g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, hys⟩ := hy
    obtain ⟨hsΔ, hxs, hcomm⟩ := hS s hs
    have hnbr := c.rep_omega rep hrep hx hsΔ hxs hcomm
    have := c.centralizes (rep x) (rep s) hnbr (c.mem_inf_of_mem_U4 hys)
    rw [this]
    group
  | one => simp
  | mul y z _ _ hy hz =>
    have e : (rep x).r * (y * z) * (rep x).r⁻¹ =
        ((rep x).r * y * (rep x).r⁻¹) * ((rep x).r * z * (rep x).r⁻¹) := by group
    rw [e, hy, hz]
  | inv y _ hy =>
    have e : (rep x).r * y⁻¹ * (rep x).r⁻¹ = ((rep x).r * y * (rep x).r⁻¹)⁻¹ := by group
    rw [e, hy]

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.U4_le_UU_of_generates {a d : ↥(muGroup
    Ω W)} {B : Finset ↥(muGroup Ω W)}
    (hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W) (haΔ : a ∈ muDelta Ω W) (hdB : d ∈ B)
    (hgen : Subgroup.closure (insert a (↑B : Set ↥(muGroup Ω W))) = ⊤)
    (hconj : ∀ y ∈ muDelta Ω W, ∃ q : ↥(muGroup Ω W), y = q * d * q⁻¹)
    {y : ↥(muGroup Ω W)} (hy : y ∈ muDelta Ω W) :
    c.U4 (rep y) ≤ c.UU rep (insert a (↑B : Set ↥(muGroup Ω W))) := by
  set S : Set ↥(muGroup Ω W) := insert a ↑B with hS
  have hSΔ : S ⊆ muDelta Ω W := Set.insert_subset haΔ hBΔ
  set W₀ := c.UU rep S with hW₀
  obtain ⟨q, hq⟩ := hconj y hy
  set L : Set G := {g | ∃ s ∈ S, g = (rep s).r} with hL
  have hLN : L ⊆ Subgroup.normalizer (W : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact (rep s).r_mem_normalizer
  have hLW₀ : Subgroup.closure L ≤ Subgroup.normalizer (W₀ : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact c.normalizes_UU rep hs
  have hq' : (q : NQuot (W ⊔ OCW W)) ∈ Subgroup.closure (piG W '' L) := by
    have hmem : q ∈ Subgroup.closure S := by rw [hgen]; trivial
    have h1 := Subgroup.mem_map_of_mem (muGroup Ω W).subtype hmem
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨(rep s).r, ⟨s, hs, rfl⟩, hrep s (hSΔ hs)⟩
  obtain ⟨g, hg, hgq⟩ := exists_mem_closure_of_mem_closure_piG hLN hq'
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := ((Subgroup.closure_le _).mpr hLN) hg
  have hgW₀ : g ∈ Subgroup.normalizer (W₀ : Set G) := hLW₀ hg
  have hdΔ : d ∈ muDelta Ω W := hBΔ (Finset.mem_coe.mpr hdB)
  let σ : Rep Ω W :=
    { K := conjSub g (rep d).K
      R := conjSub g (rep d).R
      r := g * (rep d).r * g⁻¹
      hK := c.hΩ.conjInvariant g _ (rep d).hK
      hR := Q3CL.Thompson.conjSub_mem_D c.hΩ (rep d).hR hgN
      hRK := (rep d).hRK.conj g
      hr := conj_mem_conjSub (rep d).hr
      hrW := fun h => (rep d).hrW ((mem_normalizer_iff_of_mem hgN _).mp h) }
  have himg : σ.img = (rep y).img := by
    show piG W (g * (rep d).r * g⁻¹) = (rep y).img
    rw [piG_mul (Subgroup.mul_mem _ hgN (rep d).r_mem_normalizer) (Subgroup.inv_mem _ hgN),
      piG_mul hgN (rep d).r_mem_normalizer, piG_inv hgN, hgq]
    have h1 : piG W (rep d).r = (d : NQuot (W ⊔ OCW W)) := hrep d hdΔ
    have h2 : (y : NQuot (W ⊔ OCW W)) =
        (q : NQuot (W ⊔ OCW W)) * d * (q : NQuot (W ⊔ OCW W))⁻¹ := by
      rw [hq]
      rfl
    rw [h1, hrep y hy, h2]
  have hKσ : σ.K = (rep y).K := c.K_eq_of_img_eq σ (rep y) himg
  intro x hx
  have hxσ' : x ∈ σ.K := by rw [hKσ]; exact hx.1
  have hxσ : x ∈ conjSub g (rep d).K := hxσ'
  rw [mem_conjSub_iff] at hxσ
  have hx4 : g⁻¹ * x * g ∈ c.W4 := by
    have := c.conj_mem_W4 (Subgroup.inv_mem _ hgN) (show x ∈ c.W4 from ⟨hx.2.1, hx.2.2⟩)
    simpa using this
  have hmem : g⁻¹ * x * g ∈ W₀ :=
    c.U4_le_UU rep (Set.mem_insert_of_mem a (Finset.mem_coe.mpr hdB))
      ⟨hxσ, hx4.1, hx4.2⟩
  have := (Subgroup.mem_normalizer_iff.mp hgW₀ _).mp hmem
  simpa [mul_assoc] using this

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.clique_subset {a d P : ↥(muGroup Ω W)}
    {B : Finset ↥(muGroup Ω W)}
    (hcfg : Star3T.Cfg (muDelta Ω W) d a)
    (hBC : (↑B : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) d) (hdB : d ∈ B)
    (hgen : Subgroup.closure (insert a (↑B : Set ↥(muGroup Ω W))) = ⊤)
    (hP : P ∈ Star3T.cent (muDelta Ω W) d) (hPB : P ∉ B) :
    ∀ P' ∈ Star3T.cent (muDelta Ω W) d, P' ≠ P → P' ∈ B := by
  intro P' hP' hne
  by_contra hP'B
  have hBΔ : (↑B : Set ↥(muGroup Ω W)) ⊆ muDelta Ω W := fun x hx => (hBC hx).1
  have haΔ := hcfg.mem_a
  have hconj := hcfg.tt.exists_conj_of_not_conn hcfg.mem_d hcfg.mem_a hcfg.not_conn
  have hPΔ : P ∈ muDelta Ω W := hP.1
  have hP'Δ : P' ∈ muDelta Ω W := hP'.1
  obtain ⟨u, huRW, hu4⟩ := exists_orderOf_four c.hΩ c.hW (rep P).hR
  obtain ⟨hRW, -, -, -, -⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW (rep P).hR (rep P).hK (rep
      P).hRK
  have huKW : u ∈ (rep P).K ⊓ W := by rw [← hRW]; exact huRW
  have hu_pow : u ^ 4 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu4] at this
  have hu2 : u * u ≠ 1 := fun h => by
    have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hu4] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have huW : u ∈ W := huKW.2
  obtain ⟨z, hz⟩ := c.hΩ.exists_uniqueInvolution (rep P).hK
  have h4' : (u * u) * (u * u) = 1 := by
    calc (u * u) * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hu_pow
  have hzu : u * u = z :=
    (hz.unique (u * u) ((rep P).K.mul_mem huKW.1 huKW.1) h4').resolve_left hu2
  have huW₀ : u ∈ c.UU rep (insert a (↑B : Set ↥(muGroup Ω W))) :=
    c.U4_le_UU_of_generates rep hrep hBΔ haΔ hdB hgen hconj hPΔ ⟨huKW.1, huW, hu_pow⟩
  obtain ⟨x, hx, a₁, ha₁, hu_eq⟩ := c.exists_mul_of_mem_UU_insert rep huW₀
  have hxW : x ∈ W := c.U4_le_W _ hx
  have ha₁W : a₁ ∈ W := c.W4_le (c.UU_le_W4 rep _ ha₁)
  have hpA : ∀ g ∈ c.UU rep (↑B : Set ↥(muGroup Ω W)),
      (rep P).r * g * (rep P).r⁻¹ = g :=
    c.centralizes_UU rep hrep hPΔ (fun s hs => ⟨hBΔ hs, fun e => hPB (e ▸ hs),
      hcfg.comm_cent hP (hBC hs)⟩)
  have h1 : (rep P).r * u * (rep P).r⁻¹ = u⁻¹ := c.conj_inv (rep P) huKW
  have h2 : (rep P).r * a₁ * (rep P).r⁻¹ = a₁ := hpA a₁ ha₁
  have hx_eq : x = u * a₁⁻¹ := by rw [hu_eq]; group
  have hpx : (rep P).r * x * (rep P).r⁻¹ = u⁻¹ * a₁⁻¹ := by
    calc (rep P).r * x * (rep P).r⁻¹ = (rep P).r * (u * a₁⁻¹) * (rep P).r⁻¹ := by rw [← hx_eq]
      _ = ((rep P).r * u * (rep P).r⁻¹) * ((rep P).r * a₁ * (rep P).r⁻¹)⁻¹ := by group
      _ = u⁻¹ * a₁⁻¹ := by rw [h1, h2]
  obtain ⟨za, hza⟩ := c.hΩ.exists_uniqueInvolution (rep a).hK
  have hPa : P * a ≠ a * P := hcfg.noncomm_a hP
  obtain ⟨hKPa, hnotPa⟩ := c.rep_noncomm rep hrep hPΔ haΔ hPa
  have hx2 : x * x = 1 := by
    by_contra hx2
    have hxx4 : (x * x) * (x * x) = 1 := by
      calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hx.2.2
    have hxza : x * x = za :=
      (hza.unique (x * x) ((rep a).K.mul_mem hx.1 hx.1) hxx4).resolve_left hx2
    have hc : Commute u a₁⁻¹ := c.comm_W u huW a₁⁻¹ (W.inv_mem ha₁W)
    have hu2inv : (u ^ 2)⁻¹ = u ^ 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add]
      exact hu_pow
    have hpxx : (rep P).r * (x * x) * (rep P).r⁻¹ = x * x := by
      calc (rep P).r * (x * x) * (rep P).r⁻¹
          = ((rep P).r * x * (rep P).r⁻¹) * ((rep P).r * x * (rep P).r⁻¹) := by group
        _ = (u⁻¹ * a₁⁻¹) * (u⁻¹ * a₁⁻¹) := by rw [hpx]
        _ = (u⁻¹) ^ 2 * (a₁⁻¹) ^ 2 := by rw [← pow_two, hc.inv_left.mul_pow]
        _ = u ^ 2 * (a₁⁻¹) ^ 2 := by rw [inv_pow, hu2inv]
        _ = (u * a₁⁻¹) * (u * a₁⁻¹) := by rw [← pow_two, hc.mul_pow]
        _ = x * x := by rw [← hx_eq]
    have hconj_za := c.conj_involution (rep P) (rep a) hKPa hnotPa hz hza
    rw [← hxza, hpxx, hxza] at hconj_za
    have : z = 1 := by
      have h3 : z * za = 1 * za := by rw [← hconj_za, one_mul]
      exact mul_right_cancel h3
    exact hz.ne_one this
  have hx1 : x ≠ 1 := by
    intro hx1
    have hu_a : u = a₁ := by rw [hu_eq, hx1, one_mul]
    have h3 : (rep P).r * u * (rep P).r⁻¹ = u := by rw [hu_a]; exact hpA a₁ ha₁
    rw [h3] at h1
    apply hu2
    calc u * u = u⁻¹ * u := congrArg (· * u) h1
      _ = 1 := inv_mul_cancel u
  have hxza : x = za := (hza.unique x hx.1 hx2).resolve_left hx1
  obtain ⟨z', hz'⟩ := c.hΩ.exists_uniqueInvolution (rep P').hK
  have hP'a : P' * a ≠ a * P' := hcfg.noncomm_a hP'
  obtain ⟨hKP'a, hnotP'a⟩ := c.rep_noncomm rep hrep hP'Δ haΔ hP'a
  have hnbr : (rep P).K ∈ omegaNbr Ω (rep P').K :=
    c.rep_omega rep hrep hP'Δ hPΔ hne (hcfg.comm_cent hP' hP)
  have hy_u : (rep P').r * u * (rep P').r⁻¹ = u := by
    have := c.centralizes (rep P') (rep P) hnbr huKW
    rw [this]
    group
  have hy_a : (rep P').r * a₁ * (rep P').r⁻¹ = a₁ :=
    c.centralizes_UU rep hrep hP'Δ (fun s hs => ⟨hBΔ hs, fun e => hP'B (e ▸ hs),
      hcfg.comm_cent hP' (hBC hs)⟩) a₁ ha₁
  have hy_za := c.conj_involution (rep P') (rep a) hKP'a hnotP'a hz' hza
  have hu_za : u = za * a₁ := by rw [hu_eq, hxza]
  have h5 : (rep P').r * u * (rep P').r⁻¹ = (z' * za) * a₁ := by
    calc (rep P').r * u * (rep P').r⁻¹
        = ((rep P').r * za * (rep P').r⁻¹) * ((rep P').r * a₁ * (rep P').r⁻¹) := by
          rw [hu_za]; group
      _ = (z' * za) * a₁ := by rw [hy_za, hy_a]
  rw [hy_u, hu_za] at h5
  have h6 : z' * za = za := mul_right_cancel h5.symm
  exact hz'.ne_one (mul_eq_right.mp h6)

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.not_mem_closure {x : ↥(muGroup Ω W)}
    (hx : x ∈ muDelta Ω W)
    {S : Set ↥(muGroup Ω W)} (hS : ∀ s ∈ S, s ∈ muDelta Ω W ∧ x ≠ s ∧ x * s = s * x) :
    x ∉ Subgroup.closure S := by
  intro hxS
  set L : Set G := {g | ∃ s ∈ S, g = (rep s).r} with hL
  have hLN : L ⊆ Subgroup.normalizer (W : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact (rep s).r_mem_normalizer
  have hq' : (x : NQuot (W ⊔ OCW W)) ∈ Subgroup.closure (piG W '' L) := by
    have h1 := Subgroup.mem_map_of_mem (muGroup Ω W).subtype hxS
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨(rep s).r, ⟨s, hs, rfl⟩, hrep s (hS s hs).1⟩
  obtain ⟨g, hg, hgx⟩ := exists_mem_closure_of_mem_closure_piG hLN hq'
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := ((Subgroup.closure_le _).mpr hLN) hg
  obtain ⟨hRW, -, hcyc, h4, -⟩ :=
    Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW (rep x).hR (rep x).hK (rep x).hRK
  obtain ⟨v, hvU, hv2⟩ := exists_sq_ne_one hcyc (by omega)
  have hvKW : v ∈ (rep x).K ⊓ W := by rw [← hRW]; exact hvU
  have hgv : g * v * g⁻¹ = v := by
    have hcl : Subgroup.closure L ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨hsΔ, hxs, hcomm⟩ := hS s hs
      have hnbr := c.rep_omega rep hrep hsΔ hx hxs.symm hcomm.symm
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact c.centralizes (rep s) (rep x) hnbr hvKW
    have := Subgroup.mem_centralizer_singleton_iff.mp (hcl hg)
    rw [this]
    group
  have h1 : (rep x).r * v * (rep x).r⁻¹ = v⁻¹ := c.conj_inv (rep x) hvKW
  have h2 : (rep x).r * v * (rep x).r⁻¹ = g * v * g⁻¹ := by
    refine Q3CL.Thompson.conj_eq_of_piG_eq c.hΩ c.hW hgN (rep x).r_mem_normalizer ?_ hvKW.2
    rw [hgx]
    exact (hrep x hx).symm
  rw [h1, hgv] at h2
  apply hv2
  calc v * v = v⁻¹ * v := congrArg (· * v) h2.symm
    _ = 1 := inv_mul_cancel v

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.two_pow_card_le_closure (S : Finset
    ↥(muGroup Ω W))
    (hS : ∀ x ∈ S, x ∈ muDelta Ω W)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    2 ^ S.card ≤ Nat.card ↥(Subgroup.closure (↑S : Set ↥(muGroup Ω W))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, pow_zero, Finset.coe_empty]
    exact Nat.card_pos
  | insert x S₀ hx ih =>
    have hS₀ : ∀ y ∈ S₀, y ∈ muDelta Ω W := fun y hy => hS y (Finset.mem_insert_of_mem hy)
    have hcomm₀ : ∀ y ∈ S₀, ∀ z ∈ S₀, y * z = z * y := fun y hy z hz =>
      hcomm y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    have ih' := ih hS₀ hcomm₀
    have hxΔ : x ∈ muDelta Ω W := hS x (Finset.mem_insert_self x S₀)
    have hnot : x ∉ Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) :=
      c.not_mem_closure rep hrep hxΔ fun s hs =>
        ⟨hS₀ s hs, fun e => hx (e ▸ hs), hcomm x (Finset.mem_insert_self x S₀) s
          (Finset.mem_insert_of_mem hs)⟩
    have hle : Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) ≤
        Subgroup.closure (↑(insert x S₀) : Set ↥(muGroup Ω W)) :=
      Subgroup.closure_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hne : Subgroup.closure (↑S₀ : Set ↥(muGroup Ω W)) ≠
        Subgroup.closure (↑(insert x S₀) : Set ↥(muGroup Ω W)) := fun e =>
      hnot (e ▸ Subgroup.subset_closure (by rw [Finset.coe_insert]; exact Set.mem_insert _ _))
    have := two_mul_card_le_of_le_of_ne hle hne
    rw [Finset.card_insert_of_notMem hx, pow_succ]
    omega
end Frame
end Ctx
end Thompson

theorem thompsonClique : ThompsonClique := by
  classical
  intro G _ _ Ω hP W hW hnc d hd
  have hΩ : HypOmegaMod Ω := hP.hyp
  let c : Q3CL.Thompson.Ctx Ω W := ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hP.aEmpty⟩
  have hTT := Thompson.isTT_muDelta hΩ hW (Q3CL.thompsonCube hP W hW)
  have hS := Thompson.isStar_muDelta hΩ hW (thompsonStar G Ω hP W hW)
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ := Thompson.exists_not_conn_of_not_connected hΩ hW hnc
  obtain ⟨a, haΔ, hna⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
    by_cases h : Star3T.Conn (muDelta Ω W) d d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hcfg : Star3T.Cfg (muDelta Ω W) d a := ⟨hTT, hS, hd, haΔ, hna⟩
  obtain ⟨n, B, hcard, hBC, hdB, hBn, hgen⟩ := hcfg.exists_generating_family
  obtain ⟨rep, hrep⟩ : ∃ rep : ↥(muGroup Ω W) → Thompson.Rep Ω W,
      ∀ x ∈ muDelta Ω W, (rep x).img = (x : NQuot (W ⊔ OCW W)) := by
    have hex : ∀ x ∈ muDelta Ω W, ∃ ρ : Thompson.Rep Ω W, ρ.img = (x : NQuot (W ⊔ OCW W)) := by
      rintro x ⟨R, hR, r, hr, hrW, hxr⟩
      obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
      exact ⟨⟨K, R, r, hK, hR, hRK, hr, hrW⟩, hxr.symm⟩
    have : Nonempty (Thompson.Rep Ω W) := by
      obtain ⟨ρ, -⟩ := hex d hd
      exact ⟨ρ⟩
    choose! rep hrep using hex
    exact ⟨rep, hrep⟩
  have hpow : ∀ k : ℕ, 2 * (k + 1) ≤ 2 ^ (k + 1) := fun k => by
    have := Nat.lt_two_pow_self (n := k)
    rw [pow_succ]
    omega
  have hn : n ≤ 2 := by
    by_contra hn3
    push Not at hn3
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h2k := hpow k
    by_cases hall : ∀ P ∈ Star3T.cent (muDelta Ω W) d, P ∈ B
    · have h1 : (Star3T.cent (muDelta Ω W) d).ncard ≤ B.card := by
        calc (Star3T.cent (muDelta Ω W) d).ncard ≤ (↑B : Set ↥(muGroup Ω W)).ncard :=
              Set.ncard_le_ncard (fun P hP => Finset.mem_coe.mpr (hall P hP)) (Set.toFinite _)
          _ = B.card := Set.ncard_coe_finset B
      rw [hcard, hBn] at h1
      omega
    · push Not at hall
      obtain ⟨P, hP, hPB⟩ := hall
      have hsub := c.clique_subset rep hrep hcfg hBC hdB hgen hP hPB
      have h1 : (Star3T.cent (muDelta Ω W) d).ncard ≤ B.card + 1 := by
        calc (Star3T.cent (muDelta Ω W) d).ncard
            ≤ (↑(insert P B) : Set ↥(muGroup Ω W)).ncard := by
              refine Set.ncard_le_ncard (fun P' hP' => ?_) (Set.toFinite _)
              by_cases h : P' = P
              · rw [h]
                exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
              · exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hsub P' hP' h))
          _ = (insert P B).card := Set.ncard_coe_finset _
          _ ≤ B.card + 1 := Finset.card_insert_le _ _
      rw [hcard, hBn] at h1
      omega
  interval_cases n
  · left
    rw [hcard]
    norm_num
  · right
    left
    rw [hcard]
    norm_num
  · right
    right
    refine ⟨by rw [hcard]; norm_num, ?_⟩
    have hfin : (Star3T.cent (muDelta Ω W) d).Finite := Set.toFinite _
    have hSc : hfin.toFinset.card = 4 := by
      rw [← Set.ncard_eq_toFinset_card _ hfin, hcard]
      norm_num
    have hΔ : ∀ x ∈ hfin.toFinset, x ∈ muDelta Ω W := fun x hx =>
      ((Set.Finite.mem_toFinset hfin).mp hx).1
    have hcomm : ∀ x ∈ hfin.toFinset, ∀ y ∈ hfin.toFinset, x * y = y * x := fun x hx y hy =>
      hcfg.comm_cent ((Set.Finite.mem_toFinset hfin).mp hx) ((Set.Finite.mem_toFinset hfin).mp hy)
    have h16 := c.two_pow_card_le_closure rep hrep hfin.toFinset hΔ hcomm
    rw [hSc, Set.Finite.coe_toFinset] at h16
    simpa using h16

theorem l7_10_proved : L7_10 := l7_10_of_inputs (fun _ _ _ _ hP => Q3CL.thompsonCube hP)
    thompsonStar thompsonClique
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
