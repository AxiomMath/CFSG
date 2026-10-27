module

public import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.FixedFreeQuotientUniformCoreDegrees
import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
import CFSG.FeitThompson.Representations.EqualDegreeSubcoherenceExtendsToFamily
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FieldActionCoreCoherence

open Subgroup

variable {L : Type*} [Group L]

def quotImage (H0 A K : Subgroup L) [H0.Normal] : Subgroup (↥K ⧸ H0.subgroupOf K) :=
  Subgroup.map (QuotientGroup.mk' (H0.subgroupOf K)) (A.subgroupOf K)

section QuotImage

variable {H0 A K : Subgroup L} [hH0n : H0.Normal]

theorem quotImage_eq_map :
    quotImage H0 A K
      = Subgroup.map (QuotientGroup.mk' (H0.subgroupOf K)) (A.subgroupOf K) := (rfl)

theorem mk_mem_quotImage {a : L} (ha : a ∈ A) (haK : a ∈ K) :
    (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : ↥K ⧸ H0.subgroupOf K) ∈ quotImage H0 A K :=
  ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem exists_of_mem_quotImage {z : ↥K ⧸ H0.subgroupOf K} (hz : z ∈ quotImage H0 A K) :
    ∃ a : L, ∃ haK : a ∈ K, a ∈ A ∧ QuotientGroup.mk (⟨a, haK⟩ : ↥K) = z := by
  obtain ⟨a, ha, haz⟩ := hz
  exact ⟨(a : L), a.2, Subgroup.mem_subgroupOf.mp ha, haz⟩

omit hH0n in
theorem mk_eq_mk_iff {a b : L} (haK : a ∈ K) (hbK : b ∈ K) :
    (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : ↥K ⧸ H0.subgroupOf K)
      = QuotientGroup.mk (⟨b, hbK⟩ : ↥K) ↔ a⁻¹ * b ∈ H0 := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact Iff.rfl

theorem mk_mul_mk {a b : L} (haK : a ∈ K) (hbK : b ∈ K) :
    (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : ↥K ⧸ H0.subgroupOf K)
        * QuotientGroup.mk (⟨b, hbK⟩ : ↥K)
      = QuotientGroup.mk (⟨a * b, mul_mem haK hbK⟩ : ↥K) := (rfl)

theorem mk_eq_one_of_mem_H0 {a : L} (haK : a ∈ K) (ha : a ∈ H0) :
    (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : ↥K ⧸ H0.subgroupOf K) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.mpr ha)

theorem quotImage_normal [A.Normal] : (quotImage H0 A K).Normal :=
  (Subgroup.normal_subgroupOf (N := A) (H := K)).map _ (QuotientGroup.mk'_surjective _)

theorem quotImage_mono {B : Subgroup L} (h : A ≤ B) : quotImage H0 A K ≤ quotImage H0 B K :=
  Subgroup.map_mono fun _ hx => h hx

theorem isMulCommutative_quotImage (h : ⁅A, A⁆ ≤ H0) : IsMulCommutative (quotImage H0 A K) :=
  isMulCommutative_map_mk'_of_commutator_le K h

theorem commutator_quotImage_le {B : Subgroup L} :
    ⁅quotImage H0 A K, quotImage H0 B K⁆ ≤ quotImage H0 ⁅A, B⁆ K := by
  rw [quotImage, quotImage, quotImage, ← Subgroup.map_commutator]
  refine Subgroup.map_mono (Subgroup.commutator_le.2 fun a ha b hb => ?_)
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
    (Subgroup.mem_subgroupOf.mp hb)

def quotIncl (H0 : Subgroup L) [H0.Normal] {A K : Subgroup L} (hAK : A ≤ K) :
    ↥A →* ↥K ⧸ H0.subgroupOf K :=
  (QuotientGroup.mk' (H0.subgroupOf K)).comp (Subgroup.inclusion hAK)

@[simp] theorem quotIncl_apply (hAK : A ≤ K) (a : ↥A) :
    quotIncl H0 hAK a = QuotientGroup.mk (⟨(a : L), hAK a.2⟩ : ↥K) := (rfl)

theorem range_quotIncl (hAK : A ≤ K) : (quotIncl H0 hAK).range = quotImage H0 A K := by
  ext z
  simp only [MonoidHom.mem_range, quotIncl_apply]
  refine ⟨fun h => ?_, fun hz => ?_⟩
  · obtain ⟨a, ha⟩ := h
    exact ha ▸ mk_mem_quotImage a.2 (hAK a.2)
  · obtain ⟨a, haK, haA, haz⟩ := exists_of_mem_quotImage hz
    exact ⟨⟨a, haA⟩, haz⟩

theorem natCard_quotImage (hAK : A ≤ K) (hbot : ∀ a ∈ A, a ∈ H0 → a = 1) :
    Nat.card (quotImage H0 A K) = Nat.card A := by
  have hinj : Function.Injective (quotIncl H0 hAK) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [quotIncl_apply, QuotientGroup.eq_one_iff] at ha
    exact Subtype.ext (hbot (a : L) a.2 (Subgroup.mem_subgroupOf.mp ha))
  rw [← range_quotIncl (H0 := H0) hAK, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem natCard_quotImage_dvd (hAK : A ≤ K) : Nat.card (quotImage H0 A K) ∣ Nat.card A :=
  dvd_trans (Subgroup.card_map_dvd _ _)
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv).dvd

end QuotImage

theorem relIndex_mul_natCard {A B : Subgroup L} (h : A ≤ B) :
    A.relIndex B * Nat.card A = Nat.card B := by
  rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.index_mul_card _

section Configuration

variable {H H0 U K : Subgroup L} [hHn : H.Normal] [H0.Normal]

omit hHn in
theorem disjoint_quotImage (hH0H : H0 ≤ H) (hdisj : Disjoint H U) :
    Disjoint (quotImage H0 H K) (quotImage H0 U K) := by
  rw [Subgroup.disjoint_def]
  intro z hz1 hz2
  obtain ⟨a, haK, haH, haz⟩ := exists_of_mem_quotImage hz1
  obtain ⟨b, hbK, hbU, hbz⟩ := exists_of_mem_quotImage hz2
  have hba : b⁻¹ * a ∈ H0 := (mk_eq_mk_iff hbK haK).1 (hbz.trans haz.symm)
  have hbH : b ∈ H := by
    have h2 : b = a * (b⁻¹ * a)⁻¹ := by group
    rw [h2]
    exact mul_mem haH (H.inv_mem (hH0H hba))
  have hb1 : b = 1 := Subgroup.disjoint_def.mp hdisj hbH hbU
  rw [← hbz]
  exact mk_eq_one_of_mem_H0 hbK (hb1 ▸ H0.one_mem)

theorem sup_quotImage_eq_top (hsup : H ⊔ U = K) :
    quotImage H0 H K ⊔ quotImage H0 U K = ⊤ := by
  rw [eq_top_iff]
  intro z _
  induction z using QuotientGroup.induction_on with
  | _ k =>
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_normal (hsup ▸ k.2 : (k : L) ∈ H ⊔ U)
    have haK : a ∈ K := hsup ▸ (le_sup_left (α := Subgroup L) ha)
    have hbK : b ∈ K := hsup ▸ (le_sup_right (α := Subgroup L) hb)
    have hkeq : k = (⟨a, haK⟩ : ↥K) * ⟨b, hbK⟩ := Subtype.ext (by simpa using hab.symm)
    rw [show (QuotientGroup.mk k : ↥K ⧸ H0.subgroupOf K)
        = QuotientGroup.mk (⟨a, haK⟩ : ↥K) * QuotientGroup.mk (⟨b, hbK⟩ : ↥K) by
      rw [← QuotientGroup.mk_mul, ← hkeq]]
    exact mul_mem (le_sup_left (α := Subgroup (↥K ⧸ H0.subgroupOf K)) (mk_mem_quotImage ha haK))
      (le_sup_right (α := Subgroup (↥K ⧸ H0.subgroupOf K)) (mk_mem_quotImage hb hbK))

theorem isComplement'_quotImage (hH0H : H0 ≤ H) (hdisj : Disjoint H U) (hsup : H ⊔ U = K) :
    (quotImage H0 H K).IsComplement' (quotImage H0 U K) := by
  have : (quotImage H0 H K).Normal := quotImage_normal
  rw [Subgroup.isComplement'_comm]
  exact isComplement'_of_sup_eq_top_of_inf_eq_bot (sup_quotImage_eq_top (H0 := H0) hsup)
    (disjoint_iff.1 (disjoint_quotImage hH0H hdisj))

theorem natCard_quotImage_of_le_U {A : Subgroup L} (hH0H : H0 ≤ H) (hdisj : Disjoint H U)
    (hAU : A ≤ U) (hAK : A ≤ K) : Nat.card (quotImage H0 A K) = Nat.card A :=
  natCard_quotImage hAK fun a ha ha0 =>
    Subgroup.disjoint_def.mp hdisj (hH0H ha0) (hAU ha)

theorem quotImage_chiefActionKer_eq (hHK : H ≤ K) :
    quotImage H0 (chiefActionKer H H0 U) K
      = quotImage H0 U K ⊓ centralizer ((quotImage H0 H K : Subgroup (↥K ⧸ H0.subgroupOf K)) :
          Set (↥K ⧸ H0.subgroupOf K)) := by
  refine le_antisymm (le_inf (quotImage_mono (chiefActionKer_le H H0 U)) ?_) ?_
  · intro z hz
    obtain ⟨c, hcK, hcC, hcz⟩ := exists_of_mem_quotImage hz
    obtain ⟨hcU, hkey⟩ := (mem_chiefActionKer_iff H H0 U).1 hcC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨h, hhK, hhH, hhx⟩ := exists_of_mem_quotImage hx
    have hmem : (c⁻¹ * h * c)⁻¹ * h ∈ H0 := QuotientGroup.eq.1 (hkey h hhH)
    rw [← hcz, ← hhx, mk_mul_mk, mk_mul_mk]
    refine (mk_eq_mk_iff (mul_mem hhK hcK) (mul_mem hcK hhK)).2 ?_
    have heq : (h * c)⁻¹ * (c * h) = (c⁻¹ * h * c)⁻¹ * h := by group
    rw [heq]
    exact hmem
  · rintro z ⟨hz1, hz2⟩
    obtain ⟨u, huK, huU, huz⟩ := exists_of_mem_quotImage hz1
    have huC : u ∈ chiefActionKer H H0 U := by
      refine (mem_chiefActionKer_iff H H0 U).2 ⟨huU, fun h hh => ?_⟩
      have hhK : h ∈ K := hHK hh
      have hcomm := Subgroup.mem_centralizer_iff.1 hz2 _ (mk_mem_quotImage hh hhK)
      rw [← huz, mk_mul_mk, mk_mul_mk] at hcomm
      have hmem : (h * u)⁻¹ * (u * h) ∈ H0 :=
        (mk_eq_mk_iff (mul_mem hhK huK) (mul_mem huK hhK)).1 hcomm
      refine QuotientGroup.eq.2 ?_
      have heq : (u⁻¹ * h * u)⁻¹ * h = (h * u)⁻¹ * (u * h) := by group
      rw [heq]
      exact hmem
    rw [← huz]
    exact mk_mem_quotImage huC huK

theorem inf_centralizer_quotImage_eq_bot (hH0H : H0 ≤ H) (hdisj : Disjoint H U) (hHK : H ≤ K)
    (hfree : ∀ u ∈ U, u ∉ chiefActionKer H H0 U → ∀ h ∈ H,
      ((u⁻¹ * h * u : L) : L ⧸ H0) = (h : L ⧸ H0) → h ∈ H0)
    {z : ↥K ⧸ H0.subgroupOf K} (hz : z ∈ quotImage H0 U K)
    (hzC : z ∉ quotImage H0 (chiefActionKer H H0 U) K) :
    quotImage H0 H K ⊓ centralizer {z} = ⊥ := by
  obtain ⟨u, huK, huU, huz⟩ := exists_of_mem_quotImage hz
  have huC : u ∉ chiefActionKer H H0 U := fun hc => hzC (huz ▸ mk_mem_quotImage hc huK)
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨h, hhK, hhH, hhx⟩ := exists_of_mem_quotImage hx1
  have hcomm : z * x = x * z :=
    Subgroup.mem_centralizer_iff.1 hx2 z (Set.mem_singleton z)
  rw [← huz, ← hhx, mk_mul_mk, mk_mul_mk] at hcomm
  have hmem : (h * u)⁻¹ * (u * h) ∈ H0 :=
    (mk_eq_mk_iff (mul_mem hhK huK) (mul_mem huK hhK)).1 hcomm.symm
  have hcoset : ((u⁻¹ * h * u : L) : L ⧸ H0) = (h : L ⧸ H0) := by
    refine QuotientGroup.eq.2 ?_
    have heq : (u⁻¹ * h * u)⁻¹ * h = (h * u)⁻¹ * (u * h) := by group
    rw [heq]
    exact hmem
  rw [← hhx]
  exact mk_eq_one_of_mem_H0 hhK (hfree u huU huC h hhH hcoset)

theorem relIndex_quotImage_chiefActionKer [Finite L] (hH0H : H0 ≤ H) (hdisj : Disjoint H U)
    (hUK : U ≤ K) :
    (quotImage H0 (chiefActionKer H H0 U) K).relIndex (quotImage H0 U K)
      = (chiefActionKer H H0 U).relIndex U := by
  have hCU : chiefActionKer H H0 U ≤ U := chiefActionKer_le H H0 U
  have hle : quotImage H0 (chiefActionKer H H0 U) K ≤ quotImage H0 U K := quotImage_mono hCU
  have hC : Nat.card (quotImage H0 (chiefActionKer H H0 U) K)
      = Nat.card (chiefActionKer H H0 U) :=
    natCard_quotImage_of_le_U (H := H) hH0H hdisj hCU (hCU.trans hUK)
  have hU : Nat.card (quotImage H0 U K) = Nat.card U :=
    natCard_quotImage_of_le_U (H := H) hH0H hdisj le_rfl hUK
  have h1 := relIndex_mul_natCard hle
  have h2 := relIndex_mul_natCard hCU
  rw [hC, hU] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

end Configuration

section Degree

variable {H H0 U K : Subgroup L} [H.Normal] [H0.Normal]

theorem apply_one_eq_relIndex_of_mem_irrKer [Finite L]
    (hH0H : H0 ≤ H) (hdisj : Disjoint H U) (hsup : H ⊔ U = K)
    (hcop : (Nat.card H).Coprime (Nat.card U)) (habel : ⁅H, H⁆ ≤ H0)
    (hfree : ∀ u ∈ U, u ∉ chiefActionKer H H0 U → ∀ h ∈ H,
      ((u⁻¹ * h * u : L) : L ⧸ H0) = (h : L ⧸ H0) → h ∈ H0)
    {θ : ↥K → ℂ}
    (hθ : θ ∈ irrKer ℂ (H.subgroupOf K)
      ((H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf K)) :
    θ 1 = ((chiefActionKer H H0 U).relIndex U : ℂ) := by
  set C := chiefActionKer H H0 U with hCdef
  have hHK : H ≤ K := hsup ▸ le_sup_left
  have hUK : U ≤ K := hsup ▸ le_sup_right
  have hCU : C ≤ U := chiefActionKer_le H H0 U
  obtain ⟨hθchar, hθker, hθdet⟩ := mem_irrKer.1 hθ
  have hθIrr : θ ∈ Irr ↥K := by rwa [← irrChar_eq_Irr]
  have hH0ker : ∀ x ∈ H0.subgroupOf K, θ x = θ 1 := fun x hx =>
    mem_charValueKernel.1 (hθker (SetLike.mem_coe.2 (Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : H0 ≤ H0 ⊔ ⁅C, C⁆) (Subgroup.mem_subgroupOf.mp hx)))))
  obtain ⟨ψ, hψIrr, hψθ⟩ :=
    exists_comp_mk_eq_of_mem_irrTrivialOn (N := H0.subgroupOf K)
      (mem_irrTrivialOn.2 ⟨hθIrr, hH0ker⟩)
  have hψval : ∀ x : ↥K, ψ (QuotientGroup.mk x) = θ x := fun x => congrFun hψθ x
  have hψ1 : ψ 1 = θ 1 := hψval 1
  have hEnormal : (quotImage H0 H K).Normal := quotImage_normal
  have hEabel : IsMulCommutative (quotImage H0 H K) := isMulCommutative_quotImage habel
  have hEU : (quotImage H0 H K).IsComplement' (quotImage H0 U K) :=
    isComplement'_quotImage hH0H hdisj hsup
  have hcop' : (Nat.card (quotImage H0 H K)).Coprime (Nat.card (quotImage H0 U K)) := by
    rw [natCard_quotImage_of_le_U (H := H) (U := U) hH0H hdisj le_rfl hUK]
    exact Nat.Coprime.coprime_dvd_left (natCard_quotImage_dvd hHK) hcop
  have hCeq : quotImage H0 C K
      = quotImage H0 U K ⊓ centralizer ((quotImage H0 H K :
          Subgroup (↥K ⧸ H0.subgroupOf K)) : Set (↥K ⧸ H0.subgroupOf K)) :=
    quotImage_chiefActionKer_eq hHK
  have hfree' : ∀ z ∈ quotImage H0 U K, z ∉ quotImage H0 C K →
      quotImage H0 H K ⊓ centralizer {z} = ⊥ := fun z hz hzC =>
    inf_centralizer_quotImage_eq_bot hH0H hdisj hHK hfree hz hzC
  have hψCker : ((⁅quotImage H0 C K, quotImage H0 C K⁆ : Subgroup (↥K ⧸ H0.subgroupOf K)) :
      Set (↥K ⧸ H0.subgroupOf K)) ⊆ charValueKernel ψ := by
    intro z hz
    obtain ⟨a, haK, haC, haz⟩ := exists_of_mem_quotImage (commutator_quotImage_le hz)
    rw [mem_charValueKernel, hψ1, ← haz, hψval]
    exact mem_charValueKernel.1 (hθker (SetLike.mem_coe.2 (Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : (⁅C, C⁆ : Subgroup L) ≤ H0 ⊔ ⁅C, C⁆) haC))))
  have hψEdet : ¬ ((quotImage H0 H K : Subgroup (↥K ⧸ H0.subgroupOf K)) :
      Set (↥K ⧸ H0.subgroupOf K)) ⊆ charValueKernel ψ := by
    intro hsubset
    refine hθdet fun x hx => ?_
    have hxH : (x : L) ∈ H := Subgroup.mem_subgroupOf.mp hx
    have hmem := hsubset (mk_mem_quotImage (H0 := H0) hxH x.2)
    rw [mem_charValueKernel, hψ1] at hmem
    have hxeq : (⟨(x : L), x.2⟩ : ↥K) = x := Subtype.ext rfl
    rw [mem_charValueKernel, ← hψval x, ← hxeq]
    exact hmem
  have hdeg := FixedFreeCoreDegree.apply_one_eq_relIndex (E := quotImage H0 H K)
    (U := quotImage H0 U K) (C := quotImage H0 C K) hEU hcop' hCeq hfree' hψIrr hψCker hψEdet
  rw [← hψ1, hdeg, relIndex_quotImage_chiefActionKer (H := H) hH0H hdisj hUK]

theorem apply_one_eq_index_mul_relIndex [Fintype L]
    (hH0H : H0 ≤ H) (hdisj : Disjoint H U) (hsup : H ⊔ U = K)
    (hcop : (Nat.card H).Coprime (Nat.card U)) (habel : ⁅H, H⁆ ≤ H0)
    (hfree : ∀ u ∈ U, u ∉ chiefActionKer H H0 U → ∀ h ∈ H,
      ((u⁻¹ * h * u : L) : L ⧸ H0) = (h : L ⧸ H0) → h ∈ H0)
    {f : L → ℂ}
    (hf : f ∈ indFam K (irrKer ℂ (H.subgroupOf K)
      ((H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf K))) :
    f 1 = (K.index : ℂ) * ((chiefActionKer H H0 U).relIndex U : ℂ) := by
  obtain ⟨θ, hθ, rfl⟩ := (CFSG.FeitThompson.mem_indFam K).1 hf
  have hKcard : ((Nat.card K : ℂ)) ≠ 0 := by simpa using (Nat.card_pos (α := ↥K)).ne'
  have hindex : (Nat.card L : ℂ) / (Nat.card K : ℂ) = (K.index : ℂ) := by
    rw [div_eq_iff hKcard, ← Nat.cast_mul, Subgroup.index_mul_card]
  rw [indClassFun_one, hindex,
    apply_one_eq_relIndex_of_mem_irrKer hH0H hdisj hsup hcop habel hfree hθ]

end Degree

section Coherence

variable {H H0 U K : Subgroup L} [H.Normal] [H0.Normal] {G : Type*} [Group G] [Fintype G]

theorem isCoherent_fieldActionDetectFam [Fintype L]
    {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
    (hc : IsSubcoherent S tau R)
    (τS : charSpanZero (S : Set (L → ℂ)) →+ virtualChars G)
    (hτS : ∀ f : charSpanZero (S : Set (L → ℂ)), (τS f : G → ℂ) = tau (f : L → ℂ))
    (hH0H : H0 ≤ H) (hdisj : Disjoint H U) (hsup : H ⊔ U = K)
    (hcop : (Nat.card H).Coprime (Nat.card U)) (habel : ⁅H, H⁆ ≤ H0)
    (hfree : ∀ u ∈ U, u ∉ chiefActionKer H H0 U → ∀ h ∈ H,
      ((u⁻¹ * h * u : L) : L ⧸ H0) = (h : L ⧸ H0) → h ∈ H0)
    (hS : (S : Set (L → ℂ)) = indFam K (irrKer ℂ (H.subgroupOf K)
      ((H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf K))) :
    IsCoherent (S : Set (L → ℂ)) τS := by
  refine hc.isCoherent_of_uniform_degree τS hτS fun χ hχ ψ hψ => ?_
  have hχ' : χ ∈ indFam K _ := hS ▸ (Finset.mem_coe.2 hχ : χ ∈ (S : Set (L → ℂ)))
  have hψ' : ψ ∈ indFam K _ := hS ▸ (Finset.mem_coe.2 hψ : ψ ∈ (S : Set (L → ℂ)))
  rw [apply_one_eq_index_mul_relIndex hH0H hdisj hsup hcop habel hfree hχ',
    apply_one_eq_index_mul_relIndex hH0H hdisj hsup hcop habel hfree hψ']

end Coherence

end FieldActionCoreCoherence

end CFSG.FeitThompson
