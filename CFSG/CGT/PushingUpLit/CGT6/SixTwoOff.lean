module

public import CFSG.CGT.PushingUpLit.CGT6.SixTwoQ
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoType
public import CFSG.CGT.PushingUpLit.BHS6.NatBridge
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {V Y X : Subgroup G}

theorem isQuasisimple_autOn [V.Normal] (h : PerfCtx V Y X) (hX : InClassX ↥X)
    (hXC : ¬ X ≤ Subgroup.centralizer (V : Set G)) :
    CFSG.Open.IsQuasisimple ↥(autOn X V) := by
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  let f : ↥X →* ↥(autOn X V) := actOnRange V X hXV
  have hf : Function.Surjective f := actOnRange_surjective V X hXV
  have hker : f.ker = (X ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X :=
    ker_actOnRange V X hXV
  have hperfX : commutator ↥X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [map_commutator_subtype, h.hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hperfE : commutator ↥(autOn X V) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective f hf, ← Subgroup.map_commutator,
      ← commutator_def, hperfX]
  refine ⟨hperfE, ?_⟩
  have hEne : autOn X V ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hXV hXC
  have hZtop : Subgroup.center ↥(autOn X V) ≠ ⊤ := by
    intro hZ
    have hbot : (⊤ : Subgroup ↥(autOn X V)) ≤ ⊥ := by
      rw [← hperfE, commutator_def]
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top b)) a
    exact hEne (Subgroup.eq_bot_iff_forall _ |>.mpr fun x hx => by
      have := hbot (show (⟨x, hx⟩ : ↥(autOn X V)) ∈ ⊤ from trivial)
      exact congrArg Subtype.val (Subgroup.mem_bot.mp this))
  refine { toNontrivial := ?_, eq_bot_or_eq_top_of_normal := ?_ }
  · rw [QuotientGroup.nontrivial_iff]
    exact fun hc => hZtop hc
  · intro H hH
    have hH'n : (H.comap (QuotientGroup.mk' (Subgroup.center ↥(autOn X V)))).Normal :=
      hH.comap _
    have hKn : ((H.comap (QuotientGroup.mk' (Subgroup.center ↥(autOn X V)))).comap f).Normal :=
      hH'n.comap f
    by_cases hKtop : (H.comap (QuotientGroup.mk' (Subgroup.center ↥(autOn X V)))).comap f = ⊤
    · right
      rw [eq_top_iff]
      intro q _
      obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, rfl⟩ := hf e
      have : x ∈ (H.comap (QuotientGroup.mk' (Subgroup.center ↥(autOn X V)))).comap f := by
        rw [hKtop]
        trivial
      exact this
    · left
      set K : Subgroup ↥X :=
        (H.comap (QuotientGroup.mk' (Subgroup.center ↥(autOn X V)))).comap f with hK
      have hKX : K.map X.subtype ≤ X := Subgroup.map_subtype_le K
      have hKsub : (K.map X.subtype).subgroupOf X = K :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective K
      have hKle : K.map X.subtype ≤ oTwoIn X := by
        by_contra hnot
        have := inClassX_eq_of_normal_not_le hX hKX (by rw [hKsub]; exact hKn) hnot
        apply hKtop
        rw [eq_top_iff]
        intro x _
        have hx : (x : G) ∈ K.map X.subtype := by rw [this]; exact x.2
        obtain ⟨k, hk, hkx⟩ := hx
        have : k = x := Subtype.ext hkx
        rw [← this]
        exact hk
      have hZ : ∀ x : ↥X, x ∈ K → f x ∈ Subgroup.center ↥(autOn X V) := by
        intro x hxK
        have hxO : (x : G) ∈ oTwoIn X := hKle ⟨x, hxK, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro e'
        obtain ⟨x', rfl⟩ := hf e'
        have hc : ⁅(x : G), (x' : G)⁆ ∈ Subgroup.centralizer (V : Set G) :=
          h.hOX (Subgroup.commutator_mem_commutator hxO x'.2)
        have hc' : ⁅(x' : G), (x : G)⁆ ∈ Subgroup.centralizer (V : Set G) := by
          rw [← commutatorElement_inv]
          exact (Subgroup.centralizer (V : Set G)).inv_mem hc
        have hmem : (⁅x', x⁆ : ↥X) ∈ f.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          exact ⟨(⁅x', x⁆ : ↥X).2, hc'⟩
        have h1 : f ⁅x', x⁆ = 1 := hmem
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
      have he : e ∈ H.comap (QuotientGroup.mk' (Subgroup.center ↥(autOn X V))) := hq
      refine (QuotientGroup.eq_one_iff e).mpr ?_
      obtain ⟨x, rfl⟩ := hf e
      exact hZ x he

omit [Finite G] in
theorem autOn_isSubnormal [V.Normal] (hXs : X.IsSubnormal) :
    CFSG.Open.IsSubnormal (autOn X V) (autOn ⊤ V) := by
  have h0 : (X.subgroupOf (Subgroup.normalizer (V : Set G))).IsSubnormal :=
    isSubnormal_subgroupOf_of_isSubnormal hXs _
  have h1 := Quasithin.A3.subnormal_map (conjAct V) (open_isSubnormal_top_of_isSubnormal h0)
  have h2 : (⊤ : Subgroup ↥(Subgroup.normalizer (V : Set G))).map (conjAct V) = autOn ⊤ V := by
    unfold autOn
    congr 1
  rw [h2] at h1
  exact h1

omit [Finite G] in
theorem conj_mem_sup_centralizer_of_autOn [V.Normal] {A X : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hnorm : autOn A V ≤ Subgroup.normalizer (autOn X V : Set (MulAut ↥V))) :
    ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X ⊔ Subgroup.centralizer (V : Set G) := by
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top V]
    exact le_top
  intro a ha x hx
  have hab : conjAct V ⟨a, hAN ha⟩ ∈ autOn A V := mem_autOn_iff.mpr ⟨⟨a, hAN ha⟩, ha, rfl⟩
  have hxb : conjAct V ⟨x, hXV hx⟩ ∈ autOn X V := mem_autOn_iff.mpr ⟨⟨x, hXV hx⟩, hx, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm hab) (conjAct V ⟨x, hXV hx⟩)).mp hxb
  have e : conjAct V ⟨a, hAN ha⟩ * conjAct V ⟨x, hXV hx⟩ * (conjAct V ⟨a, hAN ha⟩)⁻¹ =
      conjAct V (⟨a, hAN ha⟩ * ⟨x, hXV hx⟩ * ⟨a, hAN ha⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [e] at h1
  obtain ⟨x', hx', hxx'⟩ := mem_autOn_iff.mp h1
  have h2 : conjAct V (x'⁻¹ * (⟨a, hAN ha⟩ * ⟨x, hXV hx⟩ * ⟨a, hAN ha⟩⁻¹)) = 1 := by
    rw [map_mul, map_inv, hxx', inv_mul_cancel]
  have h3 := (conjAct_eq_one_iff V _).mp h2
  have h4 : (x'⁻¹ : G) * (a * x * a⁻¹) ∈ Subgroup.centralizer (V : Set G) := by
    simpa using h3
  have h5 : a * x * a⁻¹ = (x' : G) * ((x' : G)⁻¹ * (a * x * a⁻¹)) := by group
  rw [h5]
  exact (X ⊔ Subgroup.centralizer (V : Set G)).mul_mem (Subgroup.mem_sup_left hx')
    (Subgroup.mem_sup_right h4)

theorem le_normalizer_of_autOn_le_normalizer [V.Normal] (h : PerfCtx V Y X) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hnorm : autOn A V ≤ Subgroup.normalizer (autOn X V : Set (MulAut ↥V))) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  have hmap := conj_mem_sup_centralizer_of_autOn hAN hnorm
  have hAXC : A ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have key : ∀ b ∈ A, ∀ z ∈ X ⊔ Subgroup.centralizer (V : Set G),
        b * z * b⁻¹ ∈ X ⊔ Subgroup.centralizer (V : Set G) := by
      intro b hb z hz
      have hmem : z ∈ (X : Set G) * (Subgroup.centralizer (V : Set G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left X _ h.hCX]
        exact hz
      obtain ⟨x, hx, c, hc, rfl⟩ := hmem
      have e : b * (x * c) * b⁻¹ = (b * x * b⁻¹) * (b * c * b⁻¹) := by group
      rw [e]
      have hCn : (Subgroup.centralizer (V : Set G)).Normal := inferInstance
      exact (X ⊔ Subgroup.centralizer (V : Set G)).mul_mem (hmap b hb x hx)
        (Subgroup.mem_sup_right (hCn.conj_mem c hc b))
    refine ⟨key a ha z, fun hz => ?_⟩
    have := key a⁻¹ (A.inv_mem ha) _ hz
    simpa [mul_assoc] using this
  exact fun a ha => h.normalizer_sup_le (hAXC ha)

theorem offender_le_normalizer [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : PerfCtx V Y X)
    (hX : InClassX ↥X) (hXC : ¬ X ≤ Subgroup.centralizer (V : Set G)) {A : Subgroup G}
    (hA : IsOffG V A) : A ≤ Subgroup.normalizer (X : Set G) := by
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hoff : IsOff (autOn A V) := (isOffG_iff_isOff_autOn hV hAN).mp hA
  have hAG : autOn A V ≤ autOn ⊤ V := autOn_le_autOn V le_top
  have hcomp : CFSG.Open.IsComponentOf (autOn X V) (autOn ⊤ V) :=
    ⟨autOn_le_autOn V le_top, autOn_isSubnormal h.hXs, isQuasisimple_autOn h hX hXC⟩
  have hnorm := offender_le_normalizer_of_isComponentOf hV2 hoff hAG hcomp
  exact le_normalizer_of_autOn_le_normalizer h hAN hnorm

end CFSG.CGT.PushingUpLit.CGT6
