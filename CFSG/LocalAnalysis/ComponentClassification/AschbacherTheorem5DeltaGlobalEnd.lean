module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndBar
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndAbstract
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveOverlap

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

theorem component_eq_of_le {X : Type} [Group X] [Finite X] {m : ℕ} {K : Fin m → Subgroup X}
    (hK : ∀ l, IsComponentOf (K l) ⊤) {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (hLK : L ≤ ⨆ l, K l) : ∃ l, L = K l := by
  by_contra hne
  push Not at hne
  have hLC : (⨆ l, K l) ≤ Subgroup.centralizer (L : Set X) := by
    refine iSup_le fun l y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact components_commute hL (hK l) (hne l) x hx y hy
  have hab : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hLC (hLK hy)) x hx
  have hperf : Group.IsPerfect L := component_perfect hL
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (component_ne_bot hL)
  apply hx1
  have hcomm : commutator L = ⊥ := by
    rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact Subtype.ext (hab b.1 b.2 a.1 a.2)
  have hmem : (⟨x, hx⟩ : L) ∈ commutator L := by
    rw [hperf.commutator_eq_top]
    exact Subgroup.mem_top _
  rw [hcomm, Subgroup.mem_bot] at hmem
  exact hmem


theorem isSubnormal_map_equiv {X : Type*} [Group X] (φ : X ≃* X) {H K : Subgroup X}
    (h : IsSubnormal H K) : IsSubnormal (H.map φ.toMonoidHom) (K.map φ.toMonoidHom) :=
  h.map φ.toMonoidHom

theorem isComponentOf_rightConjugate {X : Type} [Group X] {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (c : X) : IsComponentOf (rightConjugate L c) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have h := isSubnormal_map_equiv (MulAut.conj c⁻¹) hL.2.1
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective] at h
  · exact Components.quasisimple_of_equiv
      (L.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).symm hL.2.2

theorem mem_of_twoElt_of_comm {X : Type} [Group X] [Finite X] {Z P : Subgroup X}
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hP : IsSylowOf 2 P Z) {z : X} (hz : z ∈ Z)
    (hz2 : ∃ k : ℕ, z ^ (2 ^ k) = 1) : z ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    obtain ⟨k, hk⟩ := hz2
    refine ⟨k, Subtype.ext ?_⟩
    change (z ^ n) ^ (2 ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨P', hP', hle⟩ := AschbacherTheorem3.exists_isSylowOf_le hzp
    ((Subgroup.zpowers_le).mpr hz)
  obtain ⟨c, hc, hcP⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hP hP'
  have hcN : c ∈ Subgroup.normalizer (P' : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : c * x * c⁻¹ = x := by rw [hZ c hc x (hP'.le hx)]; group
      rw [h1]
      exact hx
    · intro hx
      have hxZ : x ∈ Z := by
        have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
        rw [h2]
        exact Z.mul_mem (Z.mul_mem (Z.inv_mem hc) (hP'.le hx)) hc
      have h1 : c * x * c⁻¹ = x := by rw [hZ c hc x hxZ]; group
      rwa [h1] at hx
  rw [(rightConjugate_eq_self_iff P' c).mpr hcN] at hcP
  exact hcP ▸ hle (Subgroup.mem_zpowers z)

theorem isElemAbelian_map_subgroupOf {X Y : Type*} [Group X] [Group Y] {P K : Subgroup X}
    (h : IsElemAbelian 2 P) (f : K →* Y) : IsElemAbelian 2 ((P.subgroupOf K).map f) := by
  have h' : IsElemAbelian 2 (P.subgroupOf K) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have hc := congrArg Subtype.val (h.1.is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
      simpa using hc
    · simpa using h.2 _ hx
  exact isElemAbelian_map h' f

namespace SubQuot

variable {Q : Type} [Group Q] {Y₀ N : Subgroup Q} [(N.subgroupOf Y₀).Normal]

theorem isSylowOf_img [Finite Q] {P K : Subgroup Q} (hK : K ≤ Y₀) (h : IsSylowOf 2 P K) :
    IsSylowOf 2 (img Y₀ N P) (img Y₀ N K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK, hP2, hidx⟩ := isSylowOf_iff.mp h
  have h' : IsSylowOf 2 (P.subgroupOf Y₀) (K.subgroupOf Y₀) := by
    refine isSylowOf_iff.mpr ⟨fun x hx => Subgroup.mem_subgroupOf.mpr
      (hPK (Subgroup.mem_subgroupOf.mp hx)), hP2.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_subgroupOf hK]
    exact hidx
  exact AschbacherTheorem3.IsSylowOf.map h' (proj Y₀ N)

theorem isElemAbelian_img {P : Subgroup Q} (h : IsElemAbelian 2 P) :
    IsElemAbelian 2 (img Y₀ N P) :=
  isElemAbelian_map_subgroupOf h (proj Y₀ N)

theorem simple_img {K : Subgroup Q} (hK : K ≤ Y₀) (hq : CFSG.Open.IsQuasisimple K)
    (hker : ∀ k ∈ K, (k ∈ N ↔ ∀ x ∈ K, k * x = x * k)) :
    IsSimpleGroup (img Y₀ N K) ∧ ∃ x ∈ img Y₀ N K, ∃ y ∈ img Y₀ N K, x * y ≠ y * x := by
  have hmem : ∀ k : K, proj Y₀ N (Subgroup.inclusion hK k) ∈ img Y₀ N K := fun k =>
    proj_mem_img (x := Subgroup.inclusion hK k) k.2
  set f : K →* img Y₀ N K :=
    ((proj Y₀ N).comp (Subgroup.inclusion hK)).codRestrict _ hmem with hfdef
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := mem_img.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hkerf : f.ker = Subgroup.center K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    have h1 : f k = 1 ↔ (k : Q) ∈ N := by
      show f k = 1 ↔ ((Subgroup.inclusion hK k : Y₀) : Q) ∈ N
      rw [← proj_eq_one_iff (Subgroup.inclusion hK k)]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1, hker k k.2]
    constructor
    · intro h x
      exact Subtype.ext (h x x.2).symm
    · intro h x hx
      exact (congrArg Subtype.val (h ⟨x, hx⟩)).symm
  have e : K ⧸ Subgroup.center K ≃* img Y₀ N K :=
    (QuotientGroup.quotientMulEquivOfEq hkerf.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)
  have hs : IsSimpleGroup (img Y₀ N K) := by
    have := hq.2
    exact e.symm.isSimpleGroup
  refine ⟨hs, ?_⟩
  by_contra hab
  push Not at hab
  have : Group.IsPerfect K := ⟨hq.1⟩
  have hperf : Group.IsPerfect (img Y₀ N K) := Group.IsPerfect.ofSurjective hfsurj
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : img Y₀ N K)
  apply hy1
  have hcomm : commutator (img Y₀ N K) = ⊥ := by
    rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact Subtype.ext (hab b.1 b.2 a.1 a.2)
  have hmem' : (⟨y, hy⟩ : img Y₀ N K) ∈ commutator (img Y₀ N K) := by
    rw [hperf.commutator_eq_top]
    exact Subgroup.mem_top _
  rw [hcomm, Subgroup.mem_bot] at hmem'
  exact hmem'

end SubQuot

section Main

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem mem_barS_of_centerBar {a : Fin r} {d : DeltaDatum D Abar a} {z : Bar D}
    (hz : z ∈ centerBar D (aschbacherThm5Preimage D (Abar a)))
    (hz2 : ∃ k : ℕ, z ^ (2 ^ k) = 1) : z ∈ bar D d.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a)
  have hZab : ∀ x ∈ centerBar D A, ∀ y ∈ centerBar D A, x * y = y * x :=
    fun x hx y hy => centerBar_comm A hx y (centerBar_le A hy)
  have hAZ : bar D A ≤ Subgroup.normalizer (centerBar D A : Set (Bar D)) :=
    fun x hx => le_normalizer_centerBar (Subgroup.le_normalizer hx)
  have hsyl : IsSylowOf 2 (bar D d.S ⊓ centerBar D A) (centerBar D A) :=
    EndHyp.isSylowOf_barS.inf_of_le_normalizer (centerBar_le A) hAZ
  exact (mem_of_twoElt_of_comm hZab hsyl hz hz2).1

theorem end_of_6_4 (hin : SectionSixGlobalInputs) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hE : EndHyp d) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set V := AschbacherTheorem3.omegaOne d.S with hVdef
  set Ab := bar D A with hAbdef
  set Ub := bar D U with hUbdef
  set Sb := bar D d.S with hSbdef
  set Vb := bar D V with hVbdef
  set Zb := centerBar D A with hZbdef
  set Y₀ := Ab ⊔ Ub with hY₀def
  have hAbY : Ab ≤ Y₀ := le_sup_left
  have hUbY : Ub ≤ Y₀ := le_sup_right
  have hSbA : Sb ≤ Ab := EndHyp.isSylowOf_barS.le
  have hVbS : Vb ≤ Sb := bar_mono D EndHyp.V_le_S
  have hUbN : Ub ≤ Subgroup.normalizer (Ab : Set (Bar D)) := EndHyp.barU_le_normalizer
  have hY₀N : Y₀ ≤ Subgroup.normalizer (Ab : Set (Bar D)) := sup_le Subgroup.le_normalizer hUbN
  have hZbA : Zb ≤ Ab := centerBar_le A
  have hZbY : Zb ≤ Y₀ := hZbA.trans hAbY
  have hY₀Z : Y₀ ≤ Subgroup.normalizer (Zb : Set (Bar D)) := fun x hx =>
    le_normalizer_centerBar (hY₀N hx)
  have : (Zb.subgroupOf Y₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZbY).mpr hY₀Z
  have hUA : Ub ⊓ Ab = ⊥ := EndHyp.barU_inf_barA hC
  obtain ⟨m, K, -, hK, hKcomm, hKgen⟩ := bar_factor_components hC.hyp a
  replace hKgen : ⨆ l, K l = Ab := hKgen
  have hKA : ∀ l, K l ≤ Ab := fun l => (hK l).2
  have hKY : ∀ l, K l ≤ Y₀ := fun l => (hKA l).trans hAbY
  set Ah := SubQuot.img Y₀ Zb Ab with hAhdef
  set Eh := SubQuot.img Y₀ Zb Ub with hEhdef
  set Sh := SubQuot.img Y₀ Zb Sb with hShdef
  set Vh := SubQuot.img Y₀ Zb Vb with hVhdef
  set Xh : Fin m → Subgroup (Y₀ ⧸ Zb.subgroupOf Y₀) := fun l => SubQuot.img Y₀ Zb (K l)
    with hXhdef
  have hker : ∀ l, ∀ k ∈ K l, (k ∈ Zb ↔ ∀ x ∈ K l, k * x = x * k) := by
    intro l k hk
    constructor
    · intro hkZ x hx
      exact centerBar_comm A hkZ x (hKA l hx)
    · intro hkc
      refine ⟨hKA l hk, ?_⟩
      show k ∈ Subgroup.centralizer (Ab : Set (Bar D))
      rw [Subgroup.mem_centralizer_iff]
      have hle : Ab ≤ Subgroup.centralizer ({k} : Set (Bar D)) := by
        rw [← hKgen]
        refine iSup_le fun l' y hy => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        by_cases hll : l' = l
        · subst hll
          exact (hkc y hy).symm
        · exact hKcomm l' l hll y hy k hk
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hsimple := fun l => SubQuot.simple_img (hKY l) (hK l).1.2.2 (hker l)
  have f_normal : Ah.Normal := SubQuot.img_normal hAbY hY₀N
  have f_sup : Ah ⊔ Eh = ⊤ := by
    rw [hAhdef, hEhdef, ← SubQuot.img_sup hAbY hUbY]
    exact SubQuot.img_self
  have f_inf : Eh ⊓ Ah = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyA⟩
    obtain ⟨x, hxU, rfl⟩ := SubQuot.mem_img.mp hyE
    obtain ⟨x', hx'A, hxx'⟩ := SubQuot.mem_img.mp hyA
    have hmem := (SubQuot.proj_eq_proj_iff x' x).mp hxx'
    have hxA : (x : Bar D) ∈ Ab := by
      have : (x : Bar D) = (x' : Bar D) * ((x' : Bar D)⁻¹ * x) := by group
      rw [this]
      exact Ab.mul_mem hx'A (hZbA hmem)
    have h1 : (x : Bar D) ∈ Ub ⊓ Ab := ⟨hxU, hxA⟩
    rw [hUA, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, SubQuot.proj_eq_one_iff, h1]
    exact Zb.one_mem
  have f_elem : IsElemAbelian 2 Eh :=
    SubQuot.isElemAbelian_img (isElemAbelian_map_subgroupOf hE.U_elem (toBar D))
  have f_comm : ∀ l l', l ≠ l' → ∀ x ∈ Xh l, ∀ y ∈ Xh l', x * y = y * x := by
    intro l l' hll x hx y hy
    obtain ⟨x₁, hx₁, rfl⟩ := SubQuot.mem_img.mp hx
    obtain ⟨y₁, hy₁, rfl⟩ := SubQuot.mem_img.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKcomm l l' hll _ hx₁ _ hy₁)
  have f_gen : ⨆ l, Xh l = Ah := by
    rw [hAhdef, ← hKgen, SubQuot.img_iSup K hKY]
  have f_perm : ∀ e ∈ Eh, ∀ l, ∃ l', rightConjugate (Xh l) e = Xh l' := by
    intro e he l
    obtain ⟨u₁, hu₁, rfl⟩ := SubQuot.mem_img.mp he
    have hc := isComponentOf_rightConjugate (hK l).1 (u₁ : Bar D)
    have hcle : rightConjugate (K l) (u₁ : Bar D) ≤ ⨆ l, K l := by
      rw [hKgen]
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate (hKA l) (u₁ : Bar D)
      rwa [(rightConjugate_eq_self_iff Ab (u₁ : Bar D)).mpr (hUbN hu₁)] at h1
    obtain ⟨l', hl'⟩ := component_eq_of_le (fun l => (hK l).1) hc hcle
    exact ⟨l', by rw [← SubQuot.img_rightConjugate, hl']⟩
  have f_sylow : IsSylowOf 2 Sh Ah := SubQuot.isSylowOf_img hAbY EndHyp.isSylowOf_barS
  have f_sylowN : Eh ≤ Subgroup.normalizer (Sh : Set (Y₀ ⧸ Zb.subgroupOf Y₀)) :=
    SubQuot.img_le_normalizer fun x hx => EndHyp.barU_le_normalizer_S hx.1
  have f_Vle : Vh ≤ Sh := SubQuot.img_mono hVbS
  have f_Velem : IsElemAbelian 2 Vh :=
    SubQuot.isElemAbelian_img (isElemAbelian_map_subgroupOf hE.V_elem (toBar D))
  have f_Vcl : ∀ v ∈ Vh, ∀ x ∈ Ah, x⁻¹ * v * x ∈ Sh → x⁻¹ * v * x ∈ Vh := by
    intro v hv x hx hvx
    obtain ⟨v₁, hv₁, rfl⟩ := SubQuot.mem_img.mp hv
    obtain ⟨x₁, hx₁, rfl⟩ := SubQuot.mem_img.mp hx
    rw [← map_inv, ← map_mul, ← map_mul] at hvx ⊢
    obtain ⟨s₁, hs₁, hs₁w⟩ := SubQuot.mem_img.mp hvx
    have hz := (SubQuot.proj_eq_proj_iff s₁ (x₁⁻¹ * v₁ * x₁)).mp hs₁w
    set w : Bar D := ((x₁⁻¹ * v₁ * x₁ : Y₀) : Bar D) with hwdef
    set z : Bar D := (s₁ : Bar D)⁻¹ * w with hzdef
    have hw2 : w ^ 2 = 1 := by
      have hv2 : (v₁ : Bar D) ^ 2 = 1 :=
        (isElemAbelian_map_subgroupOf hE.V_elem (toBar D)).2 _ hv₁
      rw [hwdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((x₁ : Bar D)⁻¹ * v₁ * x₁) ^ 2 = (x₁ : Bar D)⁻¹ * (v₁ ^ 2) * x₁ by
        rw [sq, sq]; group, hv2]
      group
    have hzc : (s₁ : Bar D) * z = z * s₁ := (centerBar_comm A hz _ (hSbA hs₁)).symm
    have hz2 : z ^ 2 = ((s₁ : Bar D) ^ 2)⁻¹ := by
      have h1 : w = (s₁ : Bar D) * z := by rw [hzdef]; group
      have h2 : w ^ 2 = (s₁ : Bar D) ^ 2 * z ^ 2 := by
        rw [h1, (Commute.mul_pow hzc 2)]
      rw [hw2] at h2
      exact (eq_inv_of_mul_eq_one_right h2.symm).trans rfl
    have hztwo : ∃ k : ℕ, z ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := twoElt_of_mem EndHyp.isSylowOf_barS.isPGroup
        (Sb.inv_mem (Sb.pow_mem hs₁ 2))
      refine ⟨k + 1, ?_⟩
      rw [pow_succ', pow_mul, hz2]
      exact hk
    have hzS : z ∈ Sb := mem_barS_of_centerBar hz hztwo
    have hwS : w ∈ Sb := by
      have : w = (s₁ : Bar D) * z := by rw [hzdef]; group
      rw [this]
      exact Sb.mul_mem hs₁ hzS
    exact SubQuot.proj_mem_img (EndHyp.mem_barV hwS hw2)
  have f_Vcomm : ∀ e ∈ Eh, ∀ v ∈ Vh, e * v = v * e := by
    intro e he v hv
    obtain ⟨e₁, he₁, rfl⟩ := SubQuot.mem_img.mp he
    obtain ⟨v₁, hv₁, rfl⟩ := SubQuot.mem_img.mp hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE.barU_comm_barV hC _ he₁ _ hv₁)
  have f_comm_le : ∀ e ∈ Eh, ∀ x ∈ Sh, e⁻¹ * x⁻¹ * e * x ∈ Vh := by
    intro e he x hx
    obtain ⟨e₁, he₁, rfl⟩ := SubQuot.mem_img.mp he
    obtain ⟨x₁, hx₁, rfl⟩ := SubQuot.mem_img.mp hx
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact SubQuot.proj_mem_img (hE.barU_comm_mem hC _ he₁ _ hx₁)
  have f_wcl : ∀ x ∈ Ah, rightConjugate Eh x ≤ Sh ⊔ Eh → rightConjugate Eh x ≤ Eh ⊔ Vh := by
    intro x hx hle
    obtain ⟨x₁, hx₁, rfl⟩ := SubQuot.mem_img.mp hx
    obtain ⟨c, hc, hcx⟩ := (mem_bar_iff D A (x₁ : Bar D)).mp hx₁
    have hUx : rightConjugate Ub (x₁ : Bar D) ≤ Y₀ := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      have : y = (x₁ : Bar D)⁻¹ * ((x₁ : Bar D) * y * (x₁ : Bar D)⁻¹) * x₁ := by group
      rw [this]
      exact Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem x₁.2) (hUbY hy)) x₁.2
    rw [hEhdef, ← SubQuot.img_rightConjugate, hShdef, ← SubQuot.img_sup (hSbA.trans hAbY)
      hUbY] at hle
    have h1 := SubQuot.le_sup_of_img_le hUx hle
    rw [← hcx] at h1
    have h2 := hE.bar_conj_le hC c hc h1
    rw [hcx] at h2
    rw [hEhdef, ← SubQuot.img_rightConjugate, hVhdef, ← SubQuot.img_sup hUbY
      (hVbS.trans (hSbA.trans hAbY))]
    refine (SubQuot.img_mono h2).trans ?_
    rw [SubQuot.img_sup (sup_le hUbY (hVbS.trans (hSbA.trans hAbY))) hZbY,
      SubQuot.img_eq_bot le_rfl, sup_bot_eq]
  have f_card : Nat.card Vh < Nat.card Eh := by
    have hE1 := SubQuot.card_img_mul (N := Zb) hUbY
    have hUZ : Ub ⊓ Zb = ⊥ := le_bot_iff.mp (hUA ▸ inf_le_inf_left Ub hZbA)
    rw [hUZ, Subgroup.card_bot, mul_one, EndHyp.card_barU hC] at hE1
    have hV1 := SubQuot.card_img_mul (N := Zb) (hVbS.trans (hSbA.trans hAbY))
    rw [EndHyp.card_barV] at hV1
    have hle := EndHyp.card_inf_le (d := d)
    have hlt := hE.card_lt
    rw [← hEhdef] at hE1
    rw [← hVhdef] at hV1
    rw [hE1]
    have hpos : 0 < Nat.card (V ⊓ factorZStar D Abar a : Subgroup G) := Nat.card_pos
    have h3 : Nat.card Vh * Nat.card (V ⊓ factorZStar D Abar a : Subgroup G) <
        Nat.card U * Nat.card (V ⊓ factorZStar D Abar a : Subgroup G) :=
      calc Nat.card Vh * Nat.card (V ⊓ factorZStar D Abar a : Subgroup G)
          ≤ Nat.card Vh * Nat.card (Vb ⊓ Zb : Subgroup (Bar D)) := Nat.mul_le_mul_left _ hle
        _ = Nat.card V := hV1
        _ < _ := hlt
    exact Nat.lt_of_mul_lt_mul_right h3
  have hset : EndSetting Ah Eh Sh Vh Xh :=
    { normal := f_normal
      sup_eq := f_sup
      inf_eq := f_inf
      elem := f_elem
      simple := fun l => (hsimple l).1
      nonabelian := fun l => (hsimple l).2
      le := fun l => SubQuot.img_mono (hKA l)
      comm := f_comm
      gen := f_gen
      perm := f_perm
      sylow := f_sylow
      sylow_normalizer := f_sylowN
      V_le := f_Vle
      V_elem := f_Velem
      V_closed := f_Vcl
      V_comm := f_Vcomm
      comm_le := f_comm_le
      wcl := f_wcl
      card_lt := f_card }
  have hKle : ∀ l, K l ≤ bar D (A ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) := by
    intro l
    obtain ⟨e, he, he1, hecomm⟩ := hset.exists_centralizing hin l
    obtain ⟨u₁, hu₁, rfl⟩ := SubQuot.mem_img.mp he
    obtain ⟨u₂, hu₂U, hu₂⟩ := (mem_bar_iff D U (u₁ : Bar D)).mp hu₁
    have hu1 : (u₂ : G) ≠ 1 := by
      intro h1
      apply he1
      have h2 : u₂ = 1 := Subtype.ext h1
      have h3 : u₁ = 1 := by
        apply Subtype.ext
        rw [← hu₂, h2, map_one]
        rfl
      rw [h3, map_one]
    have : Group.IsPerfect (K l) := component_perfect (hK l).1
    set X := Subgroup.zpowers (u₁ : Bar D) with hXdef
    have hXK : ⁅X, K l⁆ ≤ Zb := by
      rw [Subgroup.commutator_le]
      intro x hx k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hcomm : SubQuot.proj Y₀ Zb (u₁ ^ n) * SubQuot.proj Y₀ Zb ⟨k, hKY l hk⟩ =
          SubQuot.proj Y₀ Zb ⟨k, hKY l hk⟩ * SubQuot.proj Y₀ Zb (u₁ ^ n) := by
        rw [map_zpow]
        exact ((Commute.zpow_left (hecomm _ (SubQuot.proj_mem_img (x := ⟨k, hKY l hk⟩) hk))
          n)).eq
      have hker1 : SubQuot.proj Y₀ Zb ⁅u₁ ^ n, ⟨k, hKY l hk⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm
      have h1 := (SubQuot.proj_eq_one_iff _).mp hker1
      have hcoe : ((⁅u₁ ^ n, ⟨k, hKY l hk⟩⁆ : Y₀) : Bar D) = ⁅(u₁ : Bar D) ^ n, k⁆ := by
        simp [commutatorElement_def]
      rwa [hcoe] at h1
    have hZK : ⁅Zb, K l⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (centerBar_comm A hz k (hKA l hk)).symm
    have h3 : ⁅⁅X, K l⁆, K l⁆ = ⊥ :=
      le_bot_iff.mp (hZK ▸ Subgroup.commutator_mono hXK le_rfl)
    have h4 := AschbacherComponentAction.perfect_three_subgroup_action (K l) X h3
    have hKC : K l ≤ bar D A ⊓ Subgroup.centralizer
        ({toBar D ⟨(u₂ : G), EndHyp.U_le_H hC hu₂U⟩} : Set (Bar D)) := by
      intro k hk
      refine ⟨hKA l hk, ?_⟩
      show k ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h5 := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers (u₁ : Bar D)) hk
      rw [h4, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5
      have h6 : toBar D ⟨(u₂ : G), EndHyp.U_le_H hC hu₂U⟩ = (u₁ : Bar D) := hu₂
      rw [h6]
      exact h5.symm
    exact hKC.trans (hE.barA_inf_centralizer_le hC hu₂U hu1)
  apply EndHyp.false_of_barA_le (d := d) hC
  show Ab ≤ _
  rw [← hKgen]
  exact iSup_le hKle

end Main

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
