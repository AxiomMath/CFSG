module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Conj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem coprime_ker_subtype {p : ℕ} (L : Subgroup G) (A : Subgroup ↥L) :
    Nat.Coprime p (Nat.card ↥(A ⊓ (L.subtype : ↥L →* G).ker)) := by
  have hk : (L.subtype : ↥L →* G).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 L.subtype_injective
  rw [hk, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right p

theorem centMod_to_alpha {p : ℕ} (hp : p.Prime) {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) {K : Subgroup ↥L}
    (hCM : CentMod p (K.map L.subtype) b) :
    ∀ h ∈ K.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)),
      alphaPQ p L b hb h * h⁻¹ ∈ GLAPPrimeCoreOf p (K.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L))) := by
  intro h hh
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hh
  have hkG : ((k : ↥L) : G) ∈ K.map L.subtype := Subgroup.mem_map.2 ⟨k, hk, rfl⟩
  have hcm := (mem_centModSubgroup.1 (centMod_iff.1 hCM)).2 _ hkG
  obtain ⟨o, ho, hoeq⟩ := mem_glaPPrimeCoreOf_iff'.1 hcm
  have hmap := glaPPrimeCore_map_subgroupMap hp L.subtype K (coprime_ker_subtype L K)
  have ho2 : o ∈ (GLAPPrimeCore p ↥K).map (L.subtype.subgroupMap K) := by
    rw [hmap]
    exact ho
  obtain ⟨o', ho', ho'eq⟩ := Subgroup.mem_map.1 ho2
  set t : ↥L := conjLE L b hb k * k⁻¹ with ht
  have htinv : ((t⁻¹ : ↥L) : G) = ⁅((k : ↥L) : G), b⁆ := by
    rw [ht, mul_inv_rev, inv_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjLE_coe, commutatorElement_def]
    group
  have hot : ((o' : ↥K) : ↥L) = t⁻¹ := by
    apply Subtype.ext
    have h3 : (((o' : ↥K) : ↥L) : G) = ((o : ↥(K.map L.subtype)) : G) := by
      rw [← ho'eq]
      rfl
    rw [h3, hoeq, htinv]
  have ht'' : (o'⁻¹ : ↥K) ∈ GLAPPrimeCore p ↥K := (GLAPPrimeCore p ↥K).inv_mem ho'
  have ht''t : (((o'⁻¹ : ↥K) : ↥L)) = t := by
    rw [Subgroup.coe_inv, hot, inv_inv]
  have htK : t ∈ K := by
    rw [← ht''t]
    exact (o'⁻¹ : ↥K).2
  have hmapψ := glaPPrimeCore_map_subgroupMap hp (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) K
    (coprime_inf_quot hp L K)
  have hmemψ : QuotientGroup.mk' (GLAPPrimeCore p ↥L) t ∈ K.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) :=
    Subgroup.mem_map.2 ⟨t, htK, rfl⟩
  have hmemO : (⟨_, hmemψ⟩ : ↥(K.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)))) ∈
      GLAPPrimeCore p ↥(K.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L))) := by
    rw [← hmapψ]
    refine Subgroup.mem_map.2 ⟨o'⁻¹, ht'', Subtype.ext ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥L) ((o'⁻¹ : ↥K) : ↥L) = QuotientGroup.mk' (GLAPPrimeCore p ↥L) t
    rw [ht''t]
  have eL : alphaPQ p L b hb (QuotientGroup.mk' (GLAPPrimeCore p ↥L) k) *
      (QuotientGroup.mk' (GLAPPrimeCore p ↥L) k)⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥L) t := by
    rw [show alphaPQ p L b hb (QuotientGroup.mk' (GLAPPrimeCore p ↥L) k) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥L) (conjLE L b hb k) from alphaPQ_mk p L b hb k,
      ← map_inv, ← map_mul]
  rw [eL]
  exact mem_glaPPrimeCoreOf_iff'.2 ⟨_, hmemO, rfl⟩

theorem centMod_of_alpha_conj {p : ℕ} {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (w : ↥L)
    (hα : alphaPQ p L b hb = MulAut.conj (QuotientGroup.mk w : PQuot p L)) :
    CentMod p L ((w : G)⁻¹ * b) := by
  have hw : ((w : G)⁻¹ * b) ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer w.2)) hb
  refine centMod_iff.2 (mem_centModSubgroup.2 ⟨hw, fun l hl => ?_⟩)
  set l' : ↥L := ⟨l, hl⟩ with hl'
  have hk : alphaPQ p L b hb (QuotientGroup.mk l') = QuotientGroup.mk (w * l' * w⁻¹) := by
    rw [hα, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hk2 : QuotientGroup.mk (conjLE L b hb l') = (QuotientGroup.mk (w * l' * w⁻¹) : PQuot p L) := by
    rw [← alphaPQ_mk]
    exact hk
  have hn := QuotientGroup.eq.1 hk2
  have hcomm : ⁅l, (w : G)⁻¹ * b⁆ =
      ((((l' * w⁻¹) * ((conjLE L b hb l')⁻¹ * (w * l' * w⁻¹)) * (l' * w⁻¹)⁻¹ : ↥L)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjLE_coe, commutatorElement_def, hl']
    group
  refine mem_glaPPrimeCoreOf_iff'.2 ⟨_, Subgroup.Normal.conj_mem inferInstance _ hn _, hcomm.symm⟩


end CFSG.LocalAnalysis.GLTheoremA.H81
