module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Milestones.CLS_component_free_involution_odd_cores_trivial
import CFSG.Milestones.QT_unique_Shult_simple_strongly_closed_TI_models
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace NonComp

variable {G : Type} [Group G]

def seriesStabIn (X Q V : Subgroup G) (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup G where
  carrier := {g | g ∈ X ∧ (∀ q ∈ Q, q⁻¹ * (g⁻¹ * q * g) ∈ V) ∧ ∀ z ∈ V, g⁻¹ * z * g = z}
  mul_mem' := by
    rintro g h ⟨hgX, hgQ, hgV⟩ ⟨hhX, hhQ, hhV⟩
    refine ⟨X.mul_mem hgX hhX, fun q hq => ?_, fun z hz => ?_⟩
    · have he : q⁻¹ * ((g * h)⁻¹ * q * (g * h)) =
          (q⁻¹ * (h⁻¹ * q * h)) * (h⁻¹ * (q⁻¹ * (g⁻¹ * q * g)) * h) := by group
      rw [he, hhV _ (hgQ q hq)]
      exact V.mul_mem (hhQ q hq) (hgQ q hq)
    · rw [show (g * h)⁻¹ * z * (g * h) = h⁻¹ * (g⁻¹ * z * g) * h by group, hgV z hz, hhV z hz]
  one_mem' := ⟨X.one_mem, fun q _ => by simp, fun z _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgX, hgQ, hgV⟩
    refine ⟨X.inv_mem hgX, fun q hq => ?_, fun z hz => ?_⟩
    · have hq' : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hXQ hgX) q).1 hq
      have he : q⁻¹ * (g⁻¹⁻¹ * q * g⁻¹) =
          ((g * q * g⁻¹)⁻¹ * (g⁻¹ * (g * q * g⁻¹) * g))⁻¹ := by group
      rw [he]
      exact V.inv_mem (hgQ _ hq')
    · calc g⁻¹⁻¹ * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgV z hz, inv_inv]
        _ = z := by group

theorem le_normalizer_of_charTwo [Finite G] (S : Sylow 2 G) {U X : Subgroup G}
    (hUS : U ≤ S) (hUab : IsMulCommutative U) (hcl : fusionStronglyClosed (U : Set G) S)
    (hUX : U ≤ X) (hchar : CFSG.Assembly.Dichotomy.dichotomyCharP 2 X) :
    X ≤ Subgroup.normalizer (U : Set G) := by
  set Q : Subgroup G := (CFSG.Assembly.pCore 2 X).map X.subtype with hQdef
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hcent : ∀ x ∈ X, x ∈ Subgroup.centralizer (Q : Set G) → x ∈ Q := by
    intro x hx hxc
    have hmem : (⟨x, hx⟩ : X) ∈ Subgroup.centralizer (CFSG.Assembly.pCore 2 X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc y ⟨y, hy, rfl⟩)
    exact ⟨⟨x, hx⟩, hchar hmem, rfl⟩
  have hUp : IsPGroup 2 U := (S.isPGroup').to_le hUS
  have hP : IsPGroup 2 (Q ⊔ U : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hQp hUp (hUX.trans hXQ)
  obtain ⟨S', hPS', hcl'⟩ := stronglyClosed_of_le_pGroup S hcl hP le_sup_right
  have hQS' : Q ≤ S' := le_sup_left.trans hPS'
  have hUS' : U ≤ S' := le_sup_right.trans hPS'
  have hconjQ : ∀ x ∈ X, ∀ q ∈ Q, x⁻¹ * q * x ∈ Q := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff''.1 (hXQ hx) q).1 hq
  have hconjV : ∀ x ∈ X, ∀ z ∈ U ⊓ Q, x⁻¹ * z * x ∈ U ⊓ Q := fun x hx z hz =>
    ⟨hcl' z hz.1 x (hQS' (hconjQ x hx z hz.2)), hconjQ x hx z hz.2⟩
  have hXV : X ≤ Subgroup.normalizer ((U ⊓ Q : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff'']
    intro z
    refine ⟨hconjV x hx z, fun hz => ?_⟩
    have := hconjV x⁻¹ (X.inv_mem hx) _ hz
    rwa [show x⁻¹⁻¹ * (x⁻¹ * z * x) * x⁻¹ = z by group] at this
  set K := seriesStabIn X Q (U ⊓ Q) hXQ with hKdef
  have hKX : K ≤ X := fun g hg => hg.1
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := by
    have key : ∀ n ∈ X, ∀ g ∈ K, n * g * n⁻¹ ∈ K := by
      rintro n hn g ⟨hgX, hgQ, hgV⟩
      refine ⟨X.mul_mem (X.mul_mem hn hgX) (X.inv_mem hn), fun q hq => ?_, fun z hz => ?_⟩
      · have hq0 : n⁻¹ * q * n ∈ Q := hconjQ n hn q hq
        have he : q⁻¹ * ((n * g * n⁻¹)⁻¹ * q * (n * g * n⁻¹)) =
            n * ((n⁻¹ * q * n)⁻¹ * (g⁻¹ * (n⁻¹ * q * n) * g)) * n⁻¹ := by group
        rw [he]
        have := hconjV n⁻¹ (X.inv_mem hn) _ (hgQ _ hq0)
        rwa [inv_inv] at this
      · have hz0 : n⁻¹ * z * n ∈ U ⊓ Q := hconjV n hn z hz
        calc (n * g * n⁻¹)⁻¹ * z * (n * g * n⁻¹) = n * (g⁻¹ * (n⁻¹ * z * n) * g) * n⁻¹ := by
              group
          _ = z := by rw [hgV _ hz0]; group
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key n hn g, fun hg => ?_⟩
    have := key n⁻¹ (X.inv_mem hn) _ hg
    rwa [show n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g by group] at this
  have hKp : IsPGroup 2 K := by
    rintro ⟨g, hgX, hgQ, hgV⟩
    obtain ⟨k, hk⟩ := N2 G Q (U ⊓ Q) hQp inf_le_right g hgQ hgV
    have hkQ : g ^ (2 ^ k) ∈ Q := hcent _ (X.pow_mem hgX _) hk
    obtain ⟨j, hj⟩ := hQp ⟨_, hkQ⟩
    have hj' : (g ^ (2 ^ k)) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    refine ⟨k + j, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hj']
  have hKQ : K ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKX hXK hKp
  have hUK : U ≤ K := by
    intro b hb
    refine ⟨hUX hb, fun q hq => ⟨?_, ?_⟩, fun z hz => ?_⟩
    · have h1 : q⁻¹ * b⁻¹ * q ∈ U :=
        conj_mem_of_stronglyClosed hUS' hcl' (hQS' hq) (U.inv_mem hb)
      rw [show q⁻¹ * (b⁻¹ * q * b) = (q⁻¹ * b⁻¹ * q) * b by group]
      exact U.mul_mem h1 hb
    · exact Q.mul_mem (Q.inv_mem hq) (hconjQ b (hUX hb) q hq)
    · have hbz : b * z = z * b := congrArg Subtype.val (hUab.is_comm.comm ⟨b, hb⟩ ⟨z, hz.1⟩)
      rw [mul_assoc, ← hbz, ← mul_assoc, inv_mul_cancel, one_mul]
  have hUV : (U ⊓ Q : Subgroup G) = U := inf_eq_left.2 (hUK.trans hKQ)
  intro x hx
  have h := hXV hx
  rwa [hUV] at h

end NonComp

open NonComp in
theorem N39 :
    S_N39 := by
  intro G _ _ _ hnab _ hrank hcomp hse S U hUS hU1 hUel hcl
  have hse' : ∀ M : Subgroup G, ¬ CFSG.Assembly.Dichotomy.dichotomyStronglyEmbedded M := by
    rintro M ⟨h1, h2, h3⟩
    refine hse M ⟨h1, h2, fun g hg => ?_⟩
    have := h3 g⁻¹ (fun h => hg (by simpa using M.inv_mem h))
    simpa using this
  have hC : ∀ v ∈ U, v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (U : Set G) := by
    intro v hv hv1
    have hvo : orderOf v = 2 := orderOf_eq_prime (hUel.2 v hv) hv1
    have hcore := CFSG.Milestones.cls_component_free_involution_odd_cores_trivial G hnab hrank
      hcomp hse' v hvo
    have hchar :=
      (CFSG.Milestones.cls_component_free_centralizer_quotient_characteristic_two G hcomp v
        hvo).2 hcore
    refine le_normalizer_of_charTwo S hUS hUel.1 hcl (fun w hw => ?_) hchar
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact congrArg Subtype.val (hUel.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hTI : fusionIsTI U := (isTI_iff_centralizer_le_normalizer S hUS hcl hUel.1).2 hC
  have hB := CFSG.Milestones.qt_unique_shult_simple_strongly_closed_ti_models G hnab S U hUS hU1
    hUel hcl hTI
  obtain ⟨q, k, -, hborel⟩ :=
    (CFSG.ComponentClassification.AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hB).borel
  obtain ⟨h1, h2, h3⟩ := (hborel S).1
  refine hse _ ⟨h1, h2, fun g hg => ?_⟩
  have := h3 g⁻¹ (fun h => hg (by simpa using Subgroup.inv_mem _ h))
  simpa using this

end CFSG.Goldschmidt
