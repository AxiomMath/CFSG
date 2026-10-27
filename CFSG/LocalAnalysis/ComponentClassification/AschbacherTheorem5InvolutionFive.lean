module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFactors

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem hyp71_of_field_hyps (hC : Counterexample G D r Abar) {t g : G}
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (ht2 : orderOf t = 2)
    (hg : g ∉ Subgroup.normalizer (D : Set G))
    (hj : ∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar j)) (g * t * g⁻¹)) : Hyp71 D t g where
  mem := ht
  orderOf_eq := ht2
  centralizer_le := by
    obtain ⟨j, hj⟩ := hj
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have hu1 : g * t * g⁻¹ ≠ 1 := by
      intro h1
      have : t = 1 := by
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at ht2
      omega
    have hsq : (g * t * g⁻¹) ^ 2 = 1 := by
      rw [pow_two]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    have hle := centralizer_le_of_centralizes hC j (two_power_of_sq hsq) hu1 hj
    intro x hx
    rw [mem_rightConjugate_iff]
    apply hle
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hx]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  ne := fun h => hg ((rightConjugate_normalizer_eq_iff hC.hyp g).mp h)

omit [Finite G] in
theorem onQuotient_of_mem (d : D) (hd : (d : G) ∈ Subgroup.normalizer (D : Set G))
    (q : D ⧸ aschbacherThm5OddCore D) :
    onQuotient D ⟨d, hd⟩ q = QuotientGroup.mk' (aschbacherThm5OddCore D) d * q *
      (QuotientGroup.mk' (aschbacherThm5OddCore D) d)⁻¹ := by
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) q
  rw [onQuotient_mk, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem false_of_product_centralizes (hin : SectionSevenBase)
    (hC : Counterexample G D r Abar) {k l : Fin r} (hkl : k ≠ l) {a b : G}
    (ha : a ∈ aschbacherThm5Preimage D (Abar k)) (hb : b ∈ aschbacherThm5Preimage D (Abar l))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b)
    (hdih : AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G))
    (hcent : ∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar j)) (g * (a * b) * g⁻¹)) : False := by
  have hyp := hC.hyp
  have haD : a ∈ D := preimage_le D _ ha
  have hbD : b ∈ D := preimage_le D _ hb
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have habD : a * b ∈ D := D.mul_mem haD hbD
  have habH : a * b ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer habD
  have hab2 : orderOf (a * b) = 2 := by
    apply orderOf_eq_prime
    · calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    · intro h1
      apply hne
      calc a = a * (b * b) := by rw [hbb, mul_one]
        _ = (a * b) * b := by group
        _ = b := by rw [h1, one_mul]
  have h' : Hyp71 D (a * b) g := hyp71_of_field_hyps hC habH hab2 hg hcent
  set π := QuotientGroup.mk' (aschbacherThm5OddCore D)
  set aq : D ⧸ aschbacherThm5OddCore D := π ⟨a, haD⟩
  set bq : D ⧸ aschbacherThm5OddCore D := π ⟨b, hbD⟩
  have haqk : aq ∈ Abar k := (mem_preimage_iff D _ ⟨a, haD⟩).mp ha
  have hbql : bq ∈ Abar l := (mem_preimage_iff D _ ⟨b, hbD⟩).mp hb
  have haq2 : aq ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a, haD⟩ : D) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact haa)
    rw [this, map_one]
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hdih
  have hNe : Even (2 ^ (n - 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  obtain ⟨u, w, hu, hw, hu1, hw1, huw, hcuw, hul, hwl⟩ :=
    AschbacherKnownGroup.FactsL2.exists_commuting_involutions_of_dihedral hNe
      (by positivity) S e (l := (⟨aq, haqk⟩ : Abar k)) (Subtype.ext (by simpa using haq2))
  have hσ : ∀ x : Abar k, x * ⟨aq, haqk⟩ = ⟨aq, haqk⟩ * x →
      onQuotient D ⟨a * b, habH⟩ (x : D ⧸ aschbacherThm5OddCore D) = x := by
    intro x hx
    have hxa : (x : D ⧸ aschbacherThm5OddCore D) * aq = aq * x := congrArg Subtype.val hx
    have hxb : (x : D ⧸ aschbacherThm5OddCore D) * bq = bq * x :=
      (hyp.hcomm k l hkl x x.2 bq hbql)
    have hd := onQuotient_of_mem (D := D) ⟨a * b, habD⟩ habH (x : D ⧸ aschbacherThm5OddCore D)
    have hπ : π ⟨a * b, habD⟩ = aq * bq := by
      rw [← map_mul]
      rfl
    rw [hπ] at hd
    rw [hd]
    calc aq * bq * (x : D ⧸ aschbacherThm5OddCore D) * (aq * bq)⁻¹
        = aq * (bq * x) * bq⁻¹ * aq⁻¹ := by group
      _ = aq * (x * bq) * bq⁻¹ * aq⁻¹ := by rw [hxb]
      _ = (aq * x) * aq⁻¹ := by group
      _ = (x * aq) * aq⁻¹ := by rw [hxa]
      _ = x := by group
  have horder : ∀ y : Abar k, y ^ 2 = 1 → y ≠ 1 → orderOf (y : D ⧸ aschbacherThm5OddCore D) = 2 :=
    fun y hy hy1 => by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hy hy1
  exact no_commuting_pair hin hC h' (horder u hu hu1) (horder w hw hw1)
    (congrArg Subtype.val hcuw) (fun h => huw (Subtype.ext h)) (hσ u hul) (hσ w hwl) l
    (mem_centralizer_factor hyp hkl.symm u.2) (mem_centralizer_factor hyp hkl.symm w.2)

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
