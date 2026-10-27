module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz2
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open Matrix
open scoped MatrixGroups

@[expose] def Step49Goldschmidt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
    (∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ S₁ → h⁻¹ * x * h ∈ Q) →
      centralizer ({z} : Set G) ≤
        normalizer ((Q ⊔ AS76b.oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G)

theorem exists_mem_not_mem_zpowers {G : Type} [Group G] [Finite G] {V : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hV : Nat.card V = 16) : ∃ v ∈ V, v ∉ zpowers z := by
  by_contra h
  push Not at h
  have := Subgroup.card_le_of_le (show V ≤ zpowers z from h)
  rw [hV, Nat.card_zpowers, hz] at this
  omega

open scoped Pointwise in
theorem card_sup_zpowers_le {G : Type} [Group G] {z v : G} (hz : z ^ 2 = 1) (hv : v ^ 2 = 1)
    (hzv : v * z = z * v) : Nat.card (zpowers v ⊔ zpowers z : Subgroup G) ≤ 4 := by
  have hvc : v ∈ centralizer ((zpowers z : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (show Commute z v from hzv.symm) k).eq
  have hle : zpowers v ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ hvc)
  have hc := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers v) (zpowers z) hle
  have h1 : Nat.card (zpowers v ⊔ zpowers z : Subgroup G) =
      Nat.card ((zpowers v : Set G) * (zpowers z : Set G)) := by
    rw [← hc]
    rfl
  rw [h1]
  refine Set.natCard_mul_le.trans ?_
  have hv2 : Nat.card (zpowers v : Set G) ≤ 2 := by
    change Nat.card (zpowers v) ≤ 2
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hv
  have hz2 : Nat.card (zpowers z : Set G) ≤ 2 := by
    change Nat.card (zpowers z) ≤ 2
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hz
  calc Nat.card (zpowers v : Set G) * Nat.card (zpowers z : Set G) ≤ 2 * 2 :=
        Nat.mul_le_mul hv2 hz2
    _ = 4 := by norm_num

theorem exists_not_mem_zpowers_of_irreducible {G : Type} [Group G] [Finite G] {V Y : Subgroup G}
    {z : G} (hz : orderOf z = 2) (hzV : z ∈ V) (hVe : IsElemAbelian 2 V) (hVc : Nat.card V = 16)
    (hYz : Y ≤ centralizer ({z} : Set G))
    (hirr : ∀ W : Subgroup G, zpowers z ≤ W → W ≤ V → Y ≤ normalizer (W : Set G) →
      W = zpowers z ∨ W = V) :
    ∃ y ∈ Y, ∃ v ∈ V, y⁻¹ * v * y * v⁻¹ ∉ zpowers z := by
  by_contra h
  push Not at h
  obtain ⟨v, hvV, hvz⟩ := exists_mem_not_mem_zpowers hz hVc
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := isMulCommutative_iff_of_setLike.mp hVe.1
  set W : Subgroup G := zpowers v ⊔ zpowers z with hWdef
  have hWV : W ≤ V := sup_le (zpowers_le.mpr hvV) (zpowers_le.mpr hzV)
  have hzW : zpowers z ≤ W := le_sup_right
  have hYW : Y ≤ normalizer (W : Set G) := by
    intro y hy
    have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp (hYz hy)
    have hy' : y⁻¹ ∈ normalizer (W : Set G) := by
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · have e : (MulAut.conj y⁻¹).toMonoidHom v = (y⁻¹ * v * y * v⁻¹) * v := by
          simp [mul_assoc]
        rw [e]
        exact W.mul_mem (hzW (h y hy v hvV)) (le_sup_left (a := zpowers v) (mem_zpowers v))
      · have e : (MulAut.conj y⁻¹).toMonoidHom z = z := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          rw [mul_assoc, ← hyz, inv_mul_cancel_left]
        rw [e]
        exact hzW (mem_zpowers z)
    simpa using inv_mem hy'
  rcases hirr W hzW hWV hYW with hW | hW
  · exact hvz (hW ▸ (le_sup_left : zpowers v ≤ W) (mem_zpowers v))
  · have h4 := card_sup_zpowers_le hz2 (hVe.2 v hvV) (hcomm v hvV z hzV)
    rw [← hWdef, hW, hVc] at h4
    omega

theorem commutator_GL32 :
    ⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))), (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆ =
      (⊤ : Subgroup (GL (Fin 3) (ZMod 2))) := by
  have := isSimpleGroup_GL32
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))), (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆) with h | h
  · exfalso
    rw [commutator_eq_bot_iff_le_centralizer, coe_top, centralizer_univ, center_GL32] at h
    exact bot_ne_top (le_bot_iff.mp h).symm
  · exact h

theorem derivedSeries_sup_eq {G : Type} [Group G] {Y M : Subgroup G}
    (φ : ↥Y →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ) (hker : φ.ker = M.subgroupOf Y)
    (n : ℕ) : (derivedSeries ↥Y n).map Y.subtype ⊔ (M ⊓ Y) = Y := by
  have hperf : ∀ m, derivedSeries (GL (Fin 3) (ZMod 2)) m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero _
    | succ m ih => rw [derivedSeries_succ, ih, commutator_GL32]
  have hmap : (derivedSeries ↥Y n).map φ = ⊤ := by rw [map_derivedSeries_eq hφ, hperf]
  have hsup : derivedSeries ↥Y n ⊔ M.subgroupOf Y = ⊤ := by
    have := congrArg (Subgroup.comap φ) hmap
    rwa [comap_map_eq, comap_top, hker] at this
  have := congrArg (Subgroup.map Y.subtype) hsup
  rwa [Subgroup.map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] at this

namespace Sec4Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem derived_acts_nontrivially (h47 : Step47) (hQ : Sec4Q G A R g E F S₁ Q z) :
    ∀ B : Subgroup G, zpowers z ≤ B → B < Q → iX z E ⊔ iX z F ≤ normalizer (B : Set G) →
      ∀ n : ℕ, ∃ k ∈ (derivedSeries ↥(iX z E ⊔ iX z F) n).map (iX z E ⊔ iX z F).subtype,
        ∃ x ∈ Q, k⁻¹ * x * k * x⁻¹ ∉ B := by
  intro B hzB hBQ hYB n
  obtain ⟨⟨-, φ, hφs, hφk⟩, ⟨V₁, V₂, hV₁Q, hV₂Q, hV₁e, hV₂e, hV₁c, hV₂c, hV12, hV12', hYV₁,
    hYV₂, hirr⟩, -⟩ := h47 G A R g E F S₁ Q z hQ
  have hYz : (iX z E ⊔ iX z F) ≤ centralizer ({z} : Set G) :=
    sup_le ((iX_le z E).trans inf_le_left) ((iX_le z F).trans inf_le_left)
  have hYQ : (iX z E ⊔ iX z F) ≤ normalizer (Q : Set G) := by
    rw [← hV12']
    exact (le_inf hYV₁ hYV₂).trans (Subgroup.inf_normalizer_le_normalizer_sup V₁ V₂)
  by_contra hcon
  push Not at hcon
  let K : Subgroup G :=
    { carrier := {y | y ∈ normalizer (Q : Set G) ∧ y ∈ normalizer (B : Set G) ∧
        ∀ x ∈ Q, y⁻¹ * x * y * x⁻¹ ∈ B}
      mul_mem' := by
        rintro a b ⟨haQ, haB, ha⟩ ⟨hbQ, hbB, hb⟩
        refine ⟨mul_mem haQ hbQ, mul_mem haB hbB, fun x hx => ?_⟩
        have e : (a * b)⁻¹ * x * (a * b) * x⁻¹ =
            b⁻¹ * (a⁻¹ * x * a * x⁻¹) * b * (b⁻¹ * x * b * x⁻¹) := by group
        rw [e]
        refine B.mul_mem ?_ (hb x hx)
        have := (mem_normalizer_iff.mp (inv_mem hbB) _).mp (ha x hx)
        simpa [mul_assoc] using this
      one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp [one_mem]⟩
      inv_mem' := by
        rintro a ⟨haQ, haB, ha⟩
        refine ⟨inv_mem haQ, inv_mem haB, fun x hx => ?_⟩
        have hx' : a * x * a⁻¹ ∈ Q := (mem_normalizer_iff.mp haQ x).mp hx
        have h1 := ha _ hx'
        have e : a⁻¹ * (a * x * a⁻¹) * a * (a * x * a⁻¹)⁻¹ = (a⁻¹⁻¹ * x * a⁻¹ * x⁻¹)⁻¹ := by group
        rw [e] at h1
        exact inv_mem_iff.mp h1 }
  have hDK : (derivedSeries ↥(iX z E ⊔ iX z F) n).map (iX z E ⊔ iX z F).subtype ≤ K := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := hk
    exact ⟨hYQ y.2, hYB y.2, fun x hx => hcon _ ⟨y, hy, rfl⟩ x hx⟩
  have hQK : Q ≤ K := by
    intro q hq
    refine ⟨le_normalizer hq, mem_normalizer_iff.mpr fun b => ⟨fun hb => ?_, fun hb => ?_⟩,
      fun x hx => hzB (by simpa [mul_assoc] using hQ.commutator_mem (Q.inv_mem hq) hx)⟩
    · have hc := hzB (hQ.commutator_mem hq (hBQ.le hb))
      have e : q * b * q⁻¹ = q * b * q⁻¹ * b⁻¹ * b := by group
      rw [e]
      exact B.mul_mem hc hb
    · have hcQ : q * b * q⁻¹ ∈ Q := hBQ.le hb
      have hc := hzB (hQ.commutator_mem (Q.inv_mem hq) hcQ)
      have e : b = q⁻¹ * (q * b * q⁻¹) * q⁻¹⁻¹ * (q * b * q⁻¹)⁻¹ * (q * b * q⁻¹) := by group
      rw [e]
      exact B.mul_mem hc hb
  have hOK : AS76b.oddCoreIn (normalizer (Q : Set G)) ≤ K := by
    intro o ho
    have hoC := oddCoreIn_le_centralizer_of_isPGroup (IsPGroup.of_card hQ.card) ho
    refine ⟨AS76b.oddCoreIn_le _ ho,
      centralizer_le_normalizer _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBQ.le) hoC),
      fun x hx => ?_⟩
    have hxo := mem_centralizer_iff.mp hoC x hx
    rw [show o⁻¹ * x * o * x⁻¹ = o⁻¹ * (x * o) * x⁻¹ by group, hxo]
    simp only [inv_mul_cancel_left, mul_inv_cancel]
    exact one_mem _
  have hYK : (iX z E ⊔ iX z F) ≤ K := by
    rw [← derivedSeries_sup_eq φ hφs hφk n]
    exact sup_le hDK (inf_le_left.trans (sup_le hQK hOK))
  have hVB : ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)), Nat.card V = 16 → IsElemAbelian 2 V →
      (iX z E ⊔ iX z F) ≤ normalizer (V : Set G) → V ≤ Q → V ≤ B := by
    intro V hV hVc hVe hYV hVQ
    have hzV : z ∈ V := by
      have hz : z ∈ V₁ ⊓ V₂ := by rw [hV12]; exact mem_zpowers z
      rcases hV with rfl | rfl
      · exact hz.1
      · exact hz.2
    have hW := hirr V hV (B ⊓ V) (le_inf hzB (zpowers_le.mpr hzV)) inf_le_right
      ((le_inf hYB hYV).trans (Subgroup.inf_normalizer_le_normalizer_inf))
    rcases hW with hW | hW
    · exfalso
      obtain ⟨y, hy, v, hv, hyv⟩ := exists_not_mem_zpowers_of_irreducible hQ.order_z hzV hVe hVc
        hYz (hirr V hV)
      apply hyv
      rw [← hW]
      refine ⟨(hYK hy).2.2 v (hVQ hv), V.mul_mem ?_ (V.inv_mem hv)⟩
      have := (mem_normalizer_iff.mp (inv_mem (hYV hy)) v).mp hv
      simpa [mul_assoc] using this
    · exact hW ▸ inf_le_left
  have h1 := hVB V₁ (Set.mem_insert _ _) hV₁c hV₁e hYV₁ hV₁Q
  have h2 := hVB V₂ (Set.mem_insert_of_mem _ rfl) hV₂c hV₂e hYV₂ hV₂Q
  exact (lt_irrefl Q) (lt_of_le_of_lt (hV12' ▸ sup_le h1 h2) hBQ)

end Sec4Q

theorem step49Goldschmidt_of (hQO : GoldschmidtQO) (h47 : Step47) : Step49Goldschmidt := by
  intro G _ _ A R g E F S₁ Q z hQ hcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowOf 2 S₁ (centralizer ({z} : Set G)) :=
    hQ.sylow.of_le hQ.le_centralizer le_top
  obtain ⟨-, ⟨V₁, V₂, -, -, -, -, -, -, -, hV12', hYV₁, hYV₂, -⟩, -⟩ := h47 G A R g E F S₁ Q z hQ
  have hYQ : iX z E ⊔ iX z F ≤ normalizer (Q : Set G) := by
    rw [← hV12']
    exact (le_inf hYV₁ hYV₂).trans (Subgroup.inf_normalizer_le_normalizer_sup V₁ V₂)
  exact hQO G z Q S₁ (iX z E ⊔ iX z F) hQ.order_z hS hQ.le hQ.z_mem_Q (Or.inl hQ.card)
    (fun x hx y hy => hQ.commutator_mem hx hy) hcl
    (sup_le ((iX_le z E).trans inf_le_left) ((iX_le z F).trans inf_le_left)) hYQ
    (hQ.derived_acts_nontrivially h47)

end CFSG.ComponentClassification.AS81
