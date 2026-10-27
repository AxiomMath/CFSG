module

public import CFSG.Fischer.Classification.PartIII.R3.Chart
public import CFSG.Fischer.Classification.Uniqueness.Cover
public import CFSG.Fischer.Classification.Basic.Local

public section

namespace CFSG.Fischer.Classification.LocalU

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification LocalR3

variable {X Y : Type} [Group X] [Group Y]

@[expose] def IsTwin (A : Set X) (a b : X) : Prop :=
  a ∈ A ∧ b ∈ A ∧ a * b = b * a ∧ ∀ c ∈ A, (c * a = a * c ↔ c * b = b * c)

@[expose] def TwinFree (A S : Set X) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, IsTwin A a b → a = b

@[expose] def MeetsTwins (A S : Set X) : Prop :=
  ∀ a ∈ A, ∃ b ∈ S, IsTwin A a b

theorem isTwin_refl {A : Set X} {a : X} (ha : a ∈ A) : IsTwin A a a :=
  ⟨ha, ha, rfl, fun _ _ => Iff.rfl⟩

section ChartTwins

variable {c : X → Y} {A : Set X} {F : Set Y}

theorem isChart_isTwin_iff (h : IsChart c A F) {a b : X} (ha : a ∈ A) (hb : b ∈ A) :
    IsTwin F (c a) (c b) ↔ IsTwin A a b := by
  unfold IsTwin
  rw [← h.comm_iff a ha b hb]
  constructor
  · rintro ⟨-, -, hab, hall⟩
    refine ⟨ha, hb, hab, fun e he => ?_⟩
    have h1 := hall (c e) (h.mem he)
    rwa [← h.comm_iff e he a ha, ← h.comm_iff e he b hb] at h1
  · rintro ⟨-, -, hab, hall⟩
    refine ⟨h.mem ha, h.mem hb, hab, fun y hy => ?_⟩
    obtain ⟨e, he, rfl⟩ := h.exists_eq hy
    rw [← h.comm_iff e he a ha, ← h.comm_iff e he b hb]
    exact hall e he

theorem isChart_twinFree_image (h : IsChart c A F) {S : Set X} (hS : S ⊆ A) (hT : TwinFree A S) :
    TwinFree F (c '' S) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ htw
  rw [hT a ha b hb ((isChart_isTwin_iff h (hS ha) (hS hb)).1 htw)]

theorem isChart_twinFree_of_image (h : IsChart c A F) {S : Set X} (hS : S ⊆ A)
    (hT : TwinFree F (c '' S)) : TwinFree A S := fun a ha b hb htw =>
  h.injOn (hS ha) (hS hb)
    (hT _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ((isChart_isTwin_iff h (hS ha) (hS hb)).2 htw))

theorem isChart_meetsTwins_image (h : IsChart c A F) {S : Set X} (hS : S ⊆ A)
    (hM : MeetsTwins A S) :
    MeetsTwins F (c '' S) := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := h.exists_eq hy
  obtain ⟨b, hb, htw⟩ := hM a ha
  exact ⟨c b, ⟨b, hb, rfl⟩, (isChart_isTwin_iff h ha (hS hb)).2 htw⟩

theorem isChart_meetsTwins_of_image (h : IsChart c A F) {S : Set X} (hS : S ⊆ A)
    (hM : MeetsTwins F (c '' S)) : MeetsTwins A S := by
  intro a ha
  obtain ⟨_, ⟨b, hb, rfl⟩, htw⟩ := hM (c a) (h.mem ha)
  exact ⟨b, hb, (isChart_isTwin_iff h ha (hS hb)).1 htw⟩

end ChartTwins

theorem isTwin_conj {F : Set Y} (hP : Pair Y F) {p a b : Y} (h : Y)
    (htw : IsTwin (LocalClass F p) a b) :
    IsTwin (LocalClass F (h * p * h⁻¹)) (h * a * h⁻¹) (h * b * h⁻¹) := by
  have hc := isChart_mulEquiv (MulAut.conj h) (LocalClass F p)
  have hfun : (⇑(MulAut.conj h) : Y → Y) = fun x => h * x * h⁻¹ :=
    funext fun x => MulAut.conj_apply h x
  rw [hfun, Pair.image_conj_localClass hP] at hc
  exact (isChart_isTwin_iff hc htw.1 htw.2.1).2 htw

variable {E : Set X} {F : Set Y}

theorem lqMap_mul {d a b : X} (ha : a ∈ LocalGroup E d) (hb : b ∈ LocalGroup E d) :
    lqMap E d (a * b) = lqMap E d a * lqMap E d b := by
  simp only [lqMap, ha, hb, mul_mem ha hb, ↓reduceDIte]
  rfl

theorem lqMap_mul_mul {d a b : X} (ha : a ∈ LocalClass E d) (hb : b ∈ LocalClass E d) :
    lqMap E d (a * b * a) = lqMap E d a * lqMap E d b * lqMap E d a := by
  have ha' := mem_localGroup ha
  rw [lqMap_mul (mul_mem ha' (mem_localGroup hb)) ha', lqMap_mul ha' (mem_localGroup hb)]

theorem isChart_of_localQuotientEquiv (hP : Pair X E) {e : X}
    (hi : Function.Injective (starImage E e)) (φ : LocalQuotient E e ≃* Y)
    (hφ : φ '' LocalImages E e = F) : IsChart (φ ∘ lqMap E e) (LocalClass E e) F := by
  have h2 := isChart_mulEquiv φ (LocalImages E e)
  rw [hφ] at h2
  exact (Pair.isChart_lqMap hP hi).comp h2

theorem exists_localQuotientEquiv_of_mem (hP : Pair X E) {d e : X} (hd : d ∈ E) (he : e ∈ E)
    (φ : LocalQuotient E d ≃* Y) (hφ : φ '' LocalImages E d = F) :
    ∃ φ' : LocalQuotient E e ≃* Y, φ' '' LocalImages E e = F := by
  obtain ⟨ψ, hψE, hψe⟩ := Pair.exists_mulEquiv hP he hd
  refine ⟨(localQuotientCongr ψ hψE hψe).trans φ, ?_⟩
  rw [MulEquiv.coe_trans, Set.image_comp, localQuotientCongr_image, hφ]

theorem localClass_localClass_comm (d f : X) :
    LocalClass (LocalClass E d) f = LocalClass (LocalClass E f) d := by
  ext s
  simp only [mem_localClass]
  tauto

theorem mem_localClass_symm {d f : X} (hd : d ∈ E) (h : f ∈ LocalClass E d) :
    d ∈ LocalClass E f :=
  ⟨hd, h.2.1.symm, h.2.2.symm⟩

theorem image_muSet_inter {ι : X → Y} {d x f : X} (hι : IsChart ι (LocalClass E d) F)
    (hf : f ∈ muSet E d x) :
    ι '' muSet E d x ∩ LocalClass F (ι f) =
      ι '' (LocalClass (LocalClass E d) f ∩ LocalClass E x) := by
  rw [← hι.image_localClass hf.1,
    ← hι.image_inter (muSet_subset_localClass d x) (localClass_subset _ _)]
  congr 1
  ext s
  simp only [muSet, mem_localClass, Set.mem_inter_iff]
  tauto

structure MuSections (F : Set Y) : Prop where
  twinFree : ∀ p ∈ F, ∀ q ∈ F, q * p ≠ p * q → TwinFree (LocalClass F p) (muSet F p q)
  meets : ∀ p ∈ F, ∀ q ∈ F, q * p ≠ p * q → MeetsTwins (LocalClass F p) (muSet F p q)

section Local

variable {G : Type} [Group G] {D : Set G} (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
  (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D)
  (φ : LocalQuotient D d ≃* Y) (hφ : φ '' LocalImages D d = F)
include hP hZ hS hd hφ

theorem exists_chart_inter {x f : G} (hx : x ∈ D) (hxd : x * d ≠ d * x)
    (hf : f ∈ muSet D d x) :
    ∃ (c : G → Y) (p q : Y), p ∈ F ∧ q ∈ F ∧ q * p ≠ p * q ∧
      IsChart c (LocalClass (LocalClass D d) f) (LocalClass F p) ∧
      c '' (LocalClass (LocalClass D d) f ∩ LocalClass D x) = muSet F p q := by
  have hfd : f ∈ LocalClass D d := hf.1
  have hfD : f ∈ D := hfd.1
  have hdf : d ∈ LocalClass D f := mem_localClass_symm hd hfd
  have hxf : x ∈ LocalClass D f := mem_localClass_symm hx hf.2
  obtain ⟨φ₀, hφ₀⟩ := exists_localQuotientEquiv_of_mem hP hd hfD φ hφ
  have hι₀ := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hfD)
    φ₀ hφ₀
  refine ⟨φ₀ ∘ lqMap D f, _, _, hι₀.mem hdf, hι₀.mem hxf,
    fun h => hxd ((hι₀.comm_iff x hxf d hdf).2 h), ?_, ?_⟩
  · have h := hι₀.localClass hdf
    rwa [← localClass_localClass_comm] at h
  · rw [← hι₀.image_muSet hdf hxf]
    congr 1
    ext s
    simp only [muSet, mem_localClass, Set.mem_inter_iff]
    tauto

theorem twinFree_inter (hF : MuSections F) {x f : G} (hx : x ∈ D) (hxd : x * d ≠ d * x)
    (hf : f ∈ muSet D d x) :
    TwinFree (LocalClass F ((φ ∘ lqMap D d) f))
      ((φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass F ((φ ∘ lqMap D d) f)) := by
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  obtain ⟨c, p, q, hp, hq, hqp, hc, hcB⟩ := exists_chart_inter hP hZ hS hd φ hφ hx hxd hf
  have hB : LocalClass (LocalClass D d) f ∩ LocalClass D x ⊆ LocalClass (LocalClass D d) f :=
    Set.inter_subset_left
  rw [image_muSet_inter hι hf]
  refine isChart_twinFree_image (hι.localClass hf.1) hB (isChart_twinFree_of_image hc hB ?_)
  rw [hcB]
  exact hF.twinFree p hp q hq hqp

theorem meetsTwins_inter (hF : MuSections F) {x f : G} (hx : x ∈ D) (hxd : x * d ≠ d * x)
    (hf : f ∈ muSet D d x) :
    MeetsTwins (LocalClass F ((φ ∘ lqMap D d) f))
      ((φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass F ((φ ∘ lqMap D d) f)) := by
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  obtain ⟨c, p, q, hp, hq, hqp, hc, hcB⟩ := exists_chart_inter hP hZ hS hd φ hφ hx hxd hf
  have hB : LocalClass (LocalClass D d) f ∩ LocalClass D x ⊆ LocalClass (LocalClass D d) f :=
    Set.inter_subset_left
  rw [image_muSet_inter hι hf]
  refine isChart_meetsTwins_image (hι.localClass hf.1) hB
    (isChart_meetsTwins_of_image hc hB ?_)
  rw [hcB]
  exact hF.meets p hp q hq hqp

end Local

theorem mul_mul_mem_image_muSet {G : Type} [Group G] {D : Set G} (hP : Pair G D) {d : G}
    (φ : LocalQuotient D d ≃* Y) {x a b : G} (ha : a ∈ muSet D d x) (hb : b ∈ muSet D d x) :
    (φ ∘ lqMap D d) a * (φ ∘ lqMap D d) b * (φ ∘ lqMap D d) a ∈
      (φ ∘ lqMap D d) '' muSet D d x :=
  ⟨a * b * a, ⟨Pair.mul_mul_mem_localClass_of_mem hP ha.1 hb.1,
    Pair.mul_mul_mem_localClass_of_mem hP ha.2 hb.2⟩, by
      simp only [Function.comp_apply, lqMap_mul_mul ha.1 hb.1, map_mul]⟩

theorem lqMap_of_mem_localGroup {d g : X} (hg : g ∈ LocalGroup E d) :
    lqMap E d g = QuotientGroup.mk (⟨g, hg⟩ : LocalGroup E d) := by
  simp only [lqMap, hg, ↓reduceDIte]

theorem exists_image_conj {G : Type} [Group G] {D : Set G} (hP : Pair G D) {d : G}
    (φ : LocalQuotient D d ≃* Y) (h : Y) {x : G} (hx : x ∈ D) (hxd : x * d ≠ d * x) :
    ∃ x' ∈ D, x' * d ≠ d * x' ∧
      (fun s => h * s * h⁻¹) '' ((φ ∘ lqMap D d) '' muSet D d x) =
        (φ ∘ lqMap D d) '' muSet D d x' := by
  obtain ⟨⟨g, hg⟩, hgh⟩ := QuotientGroup.mk_surjective (φ.symm h)
  have hgd : g * d = d * g := commute_of_mem_localGroup' hg
  have hd' : g * d * g⁻¹ = d := by rw [hgd, mul_inv_cancel_right]
  have hφg : φ (lqMap D d g) = h := by
    rw [lqMap_of_mem_localGroup hg, hgh, MulEquiv.apply_symm_apply]
  have hφg' : φ (lqMap D d g⁻¹) = h⁻¹ := by
    rw [lqMap_of_mem_localGroup (inv_mem hg), ← hφg, lqMap_of_mem_localGroup hg, ← map_inv]
    rfl
  refine ⟨g * x * g⁻¹, Pair.conj_mem hP hx g, fun hc => hxd ?_, ?_⟩
  · have h1 : Commute (g * x * g⁻¹) (g * d * g⁻¹) := by rw [hd']; exact hc
    exact (Commute.conj_iff g).1 h1
  · have hmu : muSet D d (g * x * g⁻¹) = (fun s => g * s * g⁻¹) '' muSet D d x := by
      have h1 := Pair.image_conj_muSet hP g d x
      rw [hd'] at h1
      exact h1.symm
    rw [hmu, Set.image_image, Set.image_image]
    refine Set.image_congr fun s hs => ?_
    have hs' : s ∈ LocalGroup D d := mem_localGroup hs.1
    simp only [Function.comp_apply]
    rw [lqMap_mul (mul_mem hg hs') (inv_mem hg), lqMap_mul hg hs', map_mul, map_mul, hφg, hφg']

section Flag

variable {G : Type} [Group G] {D : Set G} (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
  (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D)
  (φ : LocalQuotient D d ≃* Y) (hφ : φ '' LocalImages D d = F) (hPF : Pair Y F)
  (hT : TripleProperty F) (hne : ∀ p ∈ F, (LocalClass F p).Nonempty)
include hP hZ hS hd hφ hPF hT hne

theorem muSet_eq_of_inter_eq {x x' f : G} (hx : x ∈ D) (hxd : x * d ≠ d * x) (hx' : x' ∈ D)
    (hx'd : x' * d ≠ d * x') (hf : f ∈ muSet D d x) (hf' : f ∈ muSet D d x')
    (h : (φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass F ((φ ∘ lqMap D d) f) =
      (φ ∘ lqMap D d) '' muSet D d x' ∩ LocalClass F ((φ ∘ lqMap D d) f)) :
    muSet D d x = muSet D d x' := by
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  have hfd : f ∈ LocalClass D d := hf.1
  have hfD : f ∈ D := hfd.1
  have hdf : d ∈ LocalClass D f := mem_localClass_symm hd hfd
  have hxf : x ∈ LocalClass D f := mem_localClass_symm hx hf.2
  have hx'f : x' ∈ LocalClass D f := mem_localClass_symm hx' hf'.2
  have hsub : ∀ y, LocalClass (LocalClass D d) f ∩ LocalClass D y ⊆ LocalClass D d :=
    fun y => Set.inter_subset_left.trans (localClass_subset _ _)
  rw [image_muSet_inter hι hf, image_muSet_inter hι hf'] at h
  have hB := (hι.image_eq_image_iff (hsub x) (hsub x')).1 h
  have hBf : ∀ y, LocalClass (LocalClass D d) f ∩ LocalClass D y =
      muSet (LocalClass D f) d y := fun y => by
    ext s
    simp only [muSet, mem_localClass, Set.mem_inter_iff]
    tauto
  rw [hBf, hBf] at hB
  obtain ⟨φ₀, hφ₀⟩ := exists_localQuotientEquiv_of_mem hP hd hfD φ hφ
  have hι₀ := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hfD)
    φ₀ hφ₀
  set ι₀ := φ₀ ∘ lqMap D f with hι₀def
  have hμ : muSet F (ι₀ d) (ι₀ x) = muSet F (ι₀ d) (ι₀ x') := by
    rw [← hι₀.image_muSet hdf hxf, ← hι₀.image_muSet hdf hx'f, hB]
  have hnc : ∀ y ∈ LocalClass D f, y * d ≠ d * y → ι₀ y * ι₀ d ≠ ι₀ d * ι₀ y :=
    fun y hy hyd e => hyd ((hι₀.comm_iff y hy d hdf).2 e)
  have hfar : ∀ y ∈ LocalClass D f, y * d ≠ d * y → ι₀ y ∈ farSet F (ι₀ d) := fun y hy hyd =>
    ⟨hι₀.mem hy, hnc y hy hyd,
      Pair.muSet_nonempty_of_triple hPF hT (hι₀.mem hdf) (hne _ (hι₀.mem hdf)) (hι₀.mem hy)
        (hnc y hy hyd)⟩
  have hdxd : d * x * d ∈ LocalClass D f := Pair.mul_mul_mem_localClass_of_mem hP hdf hxf
  rcases Pair.eq_or_eq_of_muSet_eq hT (hι₀.mem hdf) (hfar x hxf hxd) (hfar x' hx'f hx'd) hμ
    with h1 | h1
  · rw [hι₀.injOn hx'f hxf h1]
  · have h2 : ι₀ x' = ι₀ (d * x * d) := by
      rw [h1, hι₀def]
      simp only [Function.comp_apply, lqMap_mul_mul hdf hxf, map_mul]
    rw [hι₀.injOn hx'f hdxd h2, ← Pair.muSet_eq_muSet_mul_mul hP hd hx hxd]

theorem image_conj_eq_of_fix {x f : G} (hx : x ∈ D) (hxd : x * d ≠ d * x)
    (hf : f ∈ muSet D d x) (h : Y) (hhp : h * (φ ∘ lqMap D d) f * h⁻¹ = (φ ∘ lqMap D d) f)
    (hhS : (fun s => h * s * h⁻¹) ''
        ((φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass F ((φ ∘ lqMap D d) f)) =
      (φ ∘ lqMap D d) '' muSet D d x ∩ LocalClass F ((φ ∘ lqMap D d) f)) :
    (fun s => h * s * h⁻¹) '' ((φ ∘ lqMap D d) '' muSet D d x) =
      (φ ∘ lqMap D d) '' muSet D d x := by
  have hι := isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd)
    φ hφ
  set ι := φ ∘ lqMap D d with hιdef
  obtain ⟨x', hx', hx'd, heq⟩ := exists_image_conj hP φ h hx hxd
  have hfx' : f ∈ muSet D d x' := by
    have hmem : ι f ∈ ι '' muSet D d x' := by
      rw [← heq, ← hhp]
      exact ⟨ι f, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨f', hf', hff'⟩ := hmem
    rwa [hι.injOn hf'.1 hf.1 hff'] at hf'
  have hstar : (fun s => h * s * h⁻¹) '' LocalClass F (ι f) = LocalClass F (ι f) := by
    rw [Pair.image_conj_localClass hPF, hhp]
  have hinter : ι '' muSet D d x' ∩ LocalClass F (ι f) =
      ι '' muSet D d x ∩ LocalClass F (ι f) := by
    rw [← heq, ← hstar, ← Set.image_inter (conj_injective h), hstar, hhS]
  rw [heq, muSet_eq_of_inter_eq hP hZ hS hd φ hφ hPF hT hne hx hxd hx' hx'd hf hfx'
    hinter.symm]

end Flag

end CFSG.Fischer.Classification.LocalU
