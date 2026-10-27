module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.Proving

variable {G : Type} [Group G] [Finite G] {M S L Q : Subgroup G}

theorem pCoreOf_le_centralizer_blockV_of_le (hA : Asc81bHyp M S) (hLM : L ≤ M) :
    pCoreOf 2 M ≤ Subgroup.centralizer (blockV S L : Set G) := by
  have hX : L ⊔ S ≤ M := sup_le hLM hA.twoRadical.1
  have hQS : pCoreOf 2 M ≤ L ⊔ S := hA.twoCore_le.trans le_sup_right
  have h1 : pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ S) :=
    normal_pGroup_le_pCoreOf 2 _ _ hQS
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQS).mpr
        (hX.trans (localGroup_le_normalizer_pCoreOf 2 M)))
      (pCoreOf_isPGroup 2 M)
  exact h1.trans (AscTenThree.le_centralizer_omegaOneCenterOf_self _)

omit [Finite G] in
theorem le_normalizer_blockV_of (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hQS : Q ≤ Subgroup.normalizer (S : Set G)) : Q ≤ Subgroup.normalizer (blockV S L : Set G) :=
  le_normalizer_omegaOneCenterOf_of_le_normalizer
    (((le_inf hQL hQS).trans (Subgroup.inf_normalizer_le_normalizer_sup L S)).trans
      (normalizer_localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)))


omit [Finite G] in
theorem le_normalizer_blockV_of_sub (S L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockV S L : Set G) :=
  le_sup_left.trans (sup_le_normalizer_blockV S L)

omit [Finite G] in
theorem commutator_mem_pCoreOf (hQM : Q ≤ M) (hLM : L ≤ M)
    (hQC : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {q l : G} (hq : q ∈ Q) (hl : l ∈ L) : q⁻¹ * l⁻¹ * q * l ∈ pCoreOf 2 M := by
  set qm : ↥M := ⟨q, hQM hq⟩
  set lm : ↥M := ⟨l, hLM hl⟩
  have hqb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) qm ∈ barM M Q :=
    ⟨qm, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have hlb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) lm ∈ barM M L :=
    ⟨lm, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have h := Subgroup.mem_centralizer_iff.mp (hQC hqb) _ hlb
  have h' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (lm * qm) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (qm * lm) := by
    rw [map_mul, map_mul]
    exact h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
  refine CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mpr ⟨_, h', ?_⟩
  simp [qm, lm, mul_assoc]


theorem rho_mul_comm (hA : Asc81bHyp M S) (hQM : Q ≤ M) (hLM : L ≤ M)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hQS : Q ≤ Subgroup.normalizer (S : Set G))
    (hQC : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (q : ↥Q) (l : ↥L) :
    Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS) q *
        Setup.rho (blockV S L) L (le_normalizer_blockV_of_sub S L) l =
      Setup.rho (blockV S L) L (le_normalizer_blockV_of_sub S L) l *
        Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS) q := by
  have hu := pCoreOf_le_centralizer_blockV_of_le hA hLM
    (commutator_mem_pCoreOf hQM hLM hQC q.2 l.2)
  refine MulEquiv.ext fun w => Subtype.ext ?_
  have hw : (w : G) * ((q : G)⁻¹ * (l : G)⁻¹ * (q : G) * (l : G)) =
      ((q : G)⁻¹ * (l : G)⁻¹ * (q : G) * (l : G)) * (w : G) :=
    Subgroup.mem_centralizer_iff.mp hu w w.2
  change (q : G) * ((l : G) * (w : G) * (l : G)⁻¹) * (q : G)⁻¹ =
    (l : G) * ((q : G) * (w : G) * (q : G)⁻¹) * (l : G)⁻¹
  set a : G := (q : G)
  set b : G := (l : G)
  set x : G := (w : G)
  set u : G := a⁻¹ * b⁻¹ * a * b with hudef
  have hux : u * x * u⁻¹ = x := by
    rw [← hw]
    group
  have e1 : a * b = b * a * u := by rw [hudef]; group
  calc a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
    _ = (b * a * u) * x * (b * a * u)⁻¹ := by rw [e1]
    _ = b * a * (u * x * u⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = b * (a * x * a⁻¹) * b⁻¹ := by rw [hux]; group


theorem rho_eq_of_mk_eq (hA : Asc81bHyp M S) (hQM : Q ≤ M) (hLM : L ≤ M)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hQS : Q ≤ Subgroup.normalizer (S : Set G))
    (c : ↥Q) (l : ↥L)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨c, hQM c.2⟩ : ↥M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨l, hLM l.2⟩ : ↥M)) :
    Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS) c =
      Setup.rho (blockV S L) L (le_normalizer_blockV_of_sub S L) l := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  have ho : ((l : G)⁻¹ * (c : G)) ∈ pCoreOf 2 M :=
    CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mpr
      ⟨_, (CFSG.pCore 2 ↥M).inv_mem h, by simp⟩
  have hu := pCoreOf_le_centralizer_blockV_of_le hA hLM ho
  refine MulEquiv.ext fun w => Subtype.ext ?_
  have hw : (w : G) * ((l : G)⁻¹ * (c : G)) = ((l : G)⁻¹ * (c : G)) * (w : G) :=
    Subgroup.mem_centralizer_iff.mp hu w w.2
  change (c : G) * (w : G) * (c : G)⁻¹ = (l : G) * (w : G) * (l : G)⁻¹
  set a : G := (c : G)
  set b : G := (l : G)
  set x : G := (w : G)
  set u : G := b⁻¹ * a with hudef
  have hux : u * x * u⁻¹ = x := by
    rw [← hw]
    group
  have e1 : a = b * u := by rw [hudef]; group
  calc a * x * a⁻¹ = (b * u) * x * (b * u)⁻¹ := by rw [← e1]
    _ = b * (u * x * u⁻¹) * b⁻¹ := by group
    _ = b * x * b⁻¹ := by rw [hux]


@[expose] noncomputable def toBar (hLM : L ≤ M) : ↥L →* ↥(barM M L) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)).codRestrict (barM M L)
    fun l => ⟨Subgroup.inclusion hLM l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩

@[expose] noncomputable def toAut (S L : Subgroup G) : ↥L →* ↥(autOn L (blockV S L)) :=
  (Setup.rho (blockV S L) L (le_normalizer_blockV_of_sub S L)).codRestrict _ fun l =>
    (Setup.range_rho (le_normalizer_blockV_of_sub S L)).le ⟨l, rfl⟩

omit [Finite G] in
theorem coe_toBar (hLM : L ≤ M) (l : ↥L) :
    ((toBar hLM l : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(l : G), hLM l.2⟩ : ↥M) := rfl

omit [Finite G] in
theorem coe_toAut (l : ↥L) :
    ((toAut S L l : ↥(autOn L (blockV S L))) : MulAut ↥(blockV S L)) =
      Setup.rho (blockV S L) L (le_normalizer_blockV_of_sub S L) l := rfl

theorem exists_central_factor_blockV (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ h : ↥(barM M L) →* ↥(autOn L (blockV S L)), Function.Surjective h ∧
      h.ker ≤ Subgroup.center ↥(barM M L) ∧ ∀ l : ↥L, h (toBar hL.le l) = toAut S L l := by
  have hLV := le_normalizer_blockV_of_sub S L
  have hπ : Function.Surjective (toBar hL.le) := by
    rintro ⟨y, m, hm, rfl⟩
    exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  have hφ : Function.Surjective (toAut S L) := by
    rintro ⟨x, hx⟩
    rw [← Setup.range_rho hLV] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l, rfl⟩
  have hker1 : ∀ l : ↥L, toAut S L l = 1 ↔ (l : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
    intro l
    rw [← Setup.rho_eq_one_iff hLV l]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hk1 : (toBar hL.le).ker ≤ (toAut S L).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(x : G), hL.le x.2⟩ : ↥M) = 1 :=
      congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    have hxC := pCoreOf_le_centralizer_blockV_of_le hA hL.le
      (CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mpr ⟨_, hx', rfl⟩)
    exact (hker1 x).mpr hxC
  have hk2 : ∀ a ∈ (toAut S L).ker, toBar hL.le a ∈ Subgroup.center ↥(barM M L) := by
    intro a ha
    have haC := (hker1 a).mp ha
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(a : G), hL.le a.2⟩ : ↥M) ∈
        barM M (L ⊓ Subgroup.centralizer (blockV S L : Set G)) :=
      ⟨⟨(a : G), hL.le a.2⟩, Subgroup.mem_subgroupOf.mpr ⟨a.2, haC⟩, rfl⟩
    obtain ⟨z, hz, hza⟩ := barM_inf_centralizer_le_center hA hL hSL hmem
    have : z = toBar hL.le a := Subtype.ext hza
    rw [← this]
    exact hz
  exact StarAux.exists_central_factor (toBar hL.le) hπ (toAut S L) hφ hk1 hk2


omit [Finite G] in
theorem rho_conj_rho (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hQS : Q ≤ Subgroup.normalizer (S : Set G)) (q : ↥Q) (l : ↥L)
    (hql : (q : G) * (l : G) * (q : G)⁻¹ ∈ L) :
    Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS) q *
        Setup.rho (blockV S L) L (le_normalizer_blockV_of_sub S L) l *
        (Setup.rho (blockV S L) Q (le_normalizer_blockV_of hQL hQS) q)⁻¹ =
      Setup.rho (blockV S L) L (le_normalizer_blockV_of_sub S L) ⟨(q : G) * (l : G) * (q : G)⁻¹, hql⟩ := by
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [← map_inv]
  simp only [MulAut.mul_apply, Setup.rho_apply_coe, Subgroup.coe_inv]
  group

end CFSG.HardMathSupport.Curtis.Coordinator
