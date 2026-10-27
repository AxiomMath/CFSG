module

public import CFSG.Fischer.Classification.PartII.O2Section
public import CFSG.Fischer.Classification.Unitary.Uniqueness
import CFSG.Fischer.Classification.SRG.Pair
public import CFSG.Fischer.Classification.Unitary.Basic

public section

namespace CFSG.Fischer.Classification.O2Bridge

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin LocalR3
  CFSG.Fischer.Classification.Unitary

section Fibres

variable {α β : Type*}

theorem ncard_eq_mul_of_fibres {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite)
    {f : α → β} (hf : Set.MapsTo f s t) {m : ℕ}
    (hfib : ∀ b ∈ t, {a | a ∈ s ∧ f a = b}.ncard = m) : s.ncard = m * t.ncard := by
  classical
  obtain ⟨S, rfl⟩ := hs.exists_finset_coe
  obtain ⟨T, rfl⟩ := ht.exists_finset_coe
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_eq_sum_card_fiberwise hf,
    Finset.sum_const_nat fun b hb => ?_, mul_comm]
  rw [← hfib b hb, ← Set.ncard_coe_finset, Finset.coe_filter]
  rfl

theorem two_mul_ncard_image_le {s : Set α} (hs : s.Finite) (f : α → β)
    (h : ∀ a ∈ s, ∃ b ∈ s, b ≠ a ∧ f b = f a) : 2 * (f '' s).ncard ≤ s.ncard := by
  classical
  obtain ⟨S, rfl⟩ := hs.exists_finset_coe
  rw [← Finset.coe_image, Set.ncard_coe_finset, Set.ncard_coe_finset]
  by_contra hlt
  obtain ⟨y, hy, hfib⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := f)
    (by omega : S.card < (S.image f).card * 2)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨b, hb, hba, hfb⟩ := h a ha
  have hsub : ({a, b} : Finset α) ⊆ S.filter fun x => f x = f a := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    rcases hx with rfl | rfl
    · exact ⟨ha, rfl⟩
    · exact ⟨hb, hfb⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hba.symm] at this
  omega

end Fibres

section Sections

variable {H : Type} [Group H] {E μ μ' : Set H}

theorem eq_of_subset_of_isTwinSection (hμ : O2Mod.IsTwinSection E μ)
    (hμ' : O2Mod.IsTwinSection E μ') (h : μ ⊆ μ') : μ = μ' := by
  refine h.antisymm fun t ht => ?_
  obtain ⟨s, hs, hts⟩ := hμ.exists_isTwin t (hμ'.subset ht)
  rwa [hμ'.eq_of_isTwin t ht s (h hs) hts]

theorem ncard_eq_four_mul [Finite H] (hμ : O2Mod.IsTwinSection E μ)
    (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4) {S : Set H} (hS : S ⊆ E)
    (hcl : ∀ a ∈ S, ∀ b, IsTwin E a b → b ∈ S) : S.ncard = 4 * (S ∩ μ).ncard := by
  refine ncard_eq_mul_of_fibres (f := O2Mod.sec E μ) (t := S ∩ μ) (Set.toFinite S)
    (Set.toFinite _) (fun a ha => ⟨hcl a ha _ (hμ.isTwin_sec (hS ha)), hμ.sec_mem (hS ha)⟩)
    fun s hs => ?_
  rw [← h4 s (hS hs.1)]
  congr 1
  ext a
  refine ⟨fun ⟨ha, has⟩ => ?_, fun has => ⟨hcl s hs.1 a has, ?_⟩⟩
  · rw [mem_twinClass, ← has]
    exact isTwin_symm (hμ.isTwin_sec (hS ha))
  · rw [← hμ.sec_eq_sec has, hμ.sec_eq_self hs.2]

end Sections

variable {G : Type} [Group G] {D : Set G}

theorem isTwinSection_image (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D) {c : G}
    (hTF : TwinFree (LocalClass D d) (muSet D d c))
    (hMT : MeetsTwins (LocalClass D d) (muSet D d c)) :
    O2Mod.IsTwinSection (LocalImages D d) (lqMap D d '' muSet D d c) := by
  have hι := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hd)
  have hsub : muSet D d c ⊆ LocalClass D d := muSet_subset_localClass d c
  refine ⟨hι.image_subset hsub, ?_, isChart_meetsTwins_image hι hsub hMT,
    isChart_twinFree_image hι hsub hTF⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact ⟨a * b * a, ⟨Pair.mul_mul_mem_localClass_of_mem hP ha.1 hb.1,
    Pair.mul_mul_mem_localClass_of_mem hP ha.2 hb.2⟩, lqMap_mul_mul ha.1 hb.1⟩

theorem twinClass_lqMap (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D) {a : G}
    (ha : a ∈ LocalClass D d) :
    twinClass (LocalImages D d) (lqMap D d a) = lqMap D d '' twinClass (LocalClass D d) a := by
  have hι := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hd)
  ext y
  constructor
  · intro hy
    obtain ⟨b, hb, rfl⟩ := hι.exists_eq hy.2.1
    exact ⟨b, (isChart_isTwin_iff hι ha hb).1 hy, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact (isChart_isTwin_iff hι ha hb.2.1).2 hb

theorem ncard_twinClass_image (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D)
    (h4 : ∀ a ∈ LocalClass D d, {b | IsTwin (LocalClass D d) a b}.ncard = 4) :
    ∀ a ∈ LocalImages D d, (twinClass (LocalImages D d) a).ncard = 4 := by
  have hι := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hd)
  intro a ha
  obtain ⟨f, hf, rfl⟩ := hι.exists_eq ha
  rw [twinClass_lqMap hP hZ hS hd hf, (hι.injOn.mono fun b hb => hb.2.1).ncard_image]
  exact h4 f hf

theorem exists_localGroup_conj_muSet (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) (hna : ∃ a b : commutator G, a * b ≠ b * a) {d : G}
    (hd : d ∈ D) {x : G} (hx : x ∈ D) (hxd : x * d ≠ d * x) :
    ∀ c ∈ D, c * d ≠ d * c →
      ∃ g ∈ LocalGroup D d, muSet D d c = (fun s => g * s * g⁻¹) '' muSet D d x :=
  Pair.exists_conj_of_transitive hP (Pair.exists_conj_far hP hZ hS hna hd hx hxd)

theorem ncard_eq_ncard_localClass_add (hP : Pair G D) {d : G} (hd : d ∈ D) :
    D.ncard = (LocalClass D d).ncard + 1 + {c | c ∈ D ∧ c * d ≠ d * c}.ncard := by
  have := Pair.finite hP
  have hD : D = insert d (LocalClass D d ∪ {c | c ∈ D ∧ c * d ≠ d * c}) := by
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · by_cases hyd : y = d
      · exact Or.inl hyd
      · by_cases hc : y * d = d * y
        · exact Or.inr (Or.inl ⟨hy, hyd, hc⟩)
        · exact Or.inr (Or.inr ⟨hy, hc⟩)
    · rintro (rfl | ⟨hy, -⟩ | ⟨hy, -⟩) <;> assumption
  conv_lhs => rw [hD]
  rw [Set.ncard_insert_of_notMem, Set.ncard_union_eq]
  · omega
  · exact Set.disjoint_left.2 fun y hy hy' => hy'.2 hy.2.2
  · rintro (h | h)
    · exact h.2.1 rfl
    · exact h.2 rfl

theorem ncard_localClass_eq_ncard_inter_add {d e : G} (hP : Pair G D)
    (he : e ∈ LocalClass D d) :
    (LocalClass D d).ncard = (LocalClass D d ∩ LocalClass D e).ncard + 1 +
      {f | f ∈ LocalClass D d ∧ f * e ≠ e * f}.ncard := by
  have := Pair.finite hP
  have hD : LocalClass D d = insert e ((LocalClass D d ∩ LocalClass D e) ∪
      {f | f ∈ LocalClass D d ∧ f * e ≠ e * f}) := by
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · by_cases hye : y = e
      · exact Or.inl hye
      · by_cases hc : y * e = e * y
        · exact Or.inr (Or.inl ⟨hy, hy.1, hye, hc⟩)
        · exact Or.inr (Or.inr ⟨hy, hc⟩)
    · rintro (rfl | ⟨hy, -⟩ | ⟨hy, -⟩) <;> assumption
  conv_lhs => rw [hD]
  rw [Set.ncard_insert_of_notMem, Set.ncard_union_eq]
  · omega
  · exact Set.disjoint_left.2 fun y hy hy' => hy'.2 hy.2.2.2
  · rintro (h | h)
    · exact h.2.2.1 rfl
    · exact h.2 rfl

theorem ncard_far_mul_ncard_muSet (hH : Hyp G D) (hna : NonabelianCommutator G) {d : G}
    (hd : d ∈ D) {e x : G} (he : e ∈ LocalClass D d) (hx : x ∈ D) (hxd : x * d ≠ d * x) :
    {c | c ∈ D ∧ c * d ≠ d * c}.ncard * (muSet D d x).ncard =
      (LocalClass D d).ncard * {f | f ∈ LocalClass D d ∧ f * e ≠ e * f}.ncard := by
  classical
  have := Pair.finite hH.pair
  have : Fintype D := Fintype.ofFinite D
  have hpe := SimpleGraph.IsSRGWith.param_eq _ (Pair.isSRGWith_commGraph hH hna hd he hx hxd)
    ((Set.ncard_pos (Set.toFinite D)).2 ⟨d, hd⟩)
  have h1 := ncard_eq_ncard_localClass_add hH.pair hd
  have h2 := ncard_localClass_eq_ncard_inter_add hH.pair he
  rw [show D.ncard - (LocalClass D d).ncard - 1 = {c | c ∈ D ∧ c * d ≠ d * c}.ncard by omega,
    show (LocalClass D d).ncard - (LocalClass D d ∩ LocalClass D e).ncard - 1 =
      {f | f ∈ LocalClass D d ∧ f * e ≠ e * f}.ncard by omega] at hpe
  exact hpe.symm

theorem mul_mul_mem_far (hP : Pair G D) {d : G} (hd : d ∈ D) {c : G} (hc : c ∈ D)
    (hcd : c * d ≠ d * c) :
    d * c * d ∈ {c | c ∈ D ∧ c * d ≠ d * c} ∧ d * c * d ≠ c ∧
      muSet D d (d * c * d) = muSet D d c := by
  have hdc : d * c ≠ c * d := fun e => hcd e.symm
  exact ⟨⟨Pair.mul_mul_mem hP hd hc, Pair.mul_mul_not_commute_left hP hd hdc⟩,
    Pair.mul_mul_ne_right hP hd hdc, (Pair.muSet_eq_muSet_mul_mul hP hd hc hcd).symm⟩

theorem exists_partner (hP : Pair G D) {d : G} (hd : d ∈ D) {c : G}
    (hc : c ∈ {c | c ∈ D ∧ c * d ≠ d * c}) :
    ∃ c' ∈ {c | c ∈ D ∧ c * d ≠ d * c}, c' ≠ c ∧ muSet D d c' = muSet D d c :=
  ⟨d * c * d, mul_mul_mem_far hP hd hc.1 hc.2⟩

theorem two_mul_ncard_image_muSet_le (hP : Pair G D) {d : G} (hd : d ∈ D) :
    2 * ((fun c => muSet D d c) '' {c | c ∈ D ∧ c * d ≠ d * c}).ncard ≤
      {c | c ∈ D ∧ c * d ≠ d * c}.ncard := by
  have := Pair.finite hP
  exact two_mul_ncard_image_le (Set.toFinite _) _ fun c hc => exists_partner hP hd hc

theorem ncard_far_eq_of_ncard_le (hP : Pair G D) {d : G} (hd : d ∈ D) {M : ℕ}
    (hM : M ≤ ((fun c => muSet D d c) '' {c | c ∈ D ∧ c * d ≠ d * c}).ncard)
    (hA : {c | c ∈ D ∧ c * d ≠ d * c}.ncard ≤ 2 * M) :
    {c | c ∈ D ∧ c * d ≠ d * c}.ncard = 2 * M := by
  have := two_mul_ncard_image_muSet_le hP hd
  omega

theorem muSet_fib_of_ncard_le (hP : Pair G D) {d : G} (hd : d ∈ D) {M : ℕ}
    (hM : M ≤ ((fun c => muSet D d c) '' {c | c ∈ D ∧ c * d ≠ d * c}).ncard)
    (hA : {c | c ∈ D ∧ c * d ≠ d * c}.ncard ≤ 2 * M) :
    ∀ c ∈ D, c * d ≠ d * c → ∀ c' ∈ D, c' * d ≠ d * c' → muSet D d c' = muSet D d c →
      c' = c ∨ c' = d * c * d := by
  intro c hc hcd c' hc' hc'd heq
  by_contra hne
  rw [not_or] at hne
  have := Pair.finite hP
  set A : Set G := {c | c ∈ D ∧ c * d ≠ d * c}
  have hcA : c ∈ A := ⟨hc, hcd⟩
  have himg : (fun c => muSet D d c) '' (A \ {c'}) = (fun c => muSet D d c) '' A := by
    refine (Set.image_mono Set.sdiff_subset).antisymm ?_
    rintro _ ⟨a, ha, rfl⟩
    by_cases hac : a = c'
    · exact ⟨c, ⟨hcA, fun h => hne.1 h.symm⟩, by simp only [hac, heq]⟩
    · exact ⟨a, ⟨ha, hac⟩, rfl⟩
  have hpart : ∀ a ∈ A \ {c'}, ∃ b ∈ A \ {c'}, b ≠ a ∧ muSet D d b = muSet D d a := by
    rintro a ⟨ha, hac⟩
    obtain ⟨b, hb, hba, hab⟩ := exists_partner hP hd ha
    by_cases hbc : b = c'
    ·
      have hμa : muSet D d c = muSet D d a := by rw [← hab, hbc, heq]
      obtain ⟨hA', hne', hμ'⟩ := mul_mul_mem_far hP hd hc hcd
      by_cases hca : c = a
      · refine ⟨d * c * d, ⟨hA', fun h => hne.2 h.symm⟩, ?_, hμ'.trans hμa⟩
        rw [← hca]
        exact hne'
      · exact ⟨c, ⟨hcA, fun h => hne.1 h.symm⟩, hca, hμa⟩
    · exact ⟨b, ⟨hb, hbc⟩, hba, hab⟩
  have h1 := two_mul_ncard_image_le (Set.toFinite (A \ {c'})) (fun c => muSet D d c) hpart
  rw [himg] at h1
  have hc'A : c' ∈ A := ⟨hc', hc'd⟩
  have h2 := Set.ncard_sdiff_singleton_add_one hc'A
  omega

theorem tripleAt_of_sections (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D)
    (hsec : ∀ c ∈ D, c * d ≠ d * c →
      O2Mod.IsTwinSection (LocalImages D d) (lqMap D d '' muSet D d c))
    (hfib : ∀ c ∈ D, c * d ≠ d * c → ∀ c' ∈ D, c' * d ≠ d * c' →
      muSet D d c' = muSet D d c → c' = c ∨ c' = d * c * d) :
    TripleAt D d := by
  have hι := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hd)
  intro c hc hdc y ⟨hyD, hsub⟩
  have hcd : c * d ≠ d * c := fun e => hdc e.symm
  by_cases hyd : y = d
  · exact Or.inl hyd
  by_cases hcomm : y * d = d * y
  ·
    exfalso
    have hyl : y ∈ LocalClass D d := ⟨hyD, hyd, hcomm⟩
    have key : ∀ a ∈ LocalImages D d, lqMap D d y * a = a * lqMap D d y := by
      intro a ha
      obtain ⟨_, ⟨t, ht, rfl⟩, htw⟩ := (hsec c hc hcd).exists_isTwin a ha
      exact (htw.2.2.2 _ (hι.mem hyl)).2
        ((hι.comm_iff y hyl t ht.1).1 (hsub ht).2.2.symm)
    apply Pair.starImage_ne_one hP hZ hS hd ⟨y, hyl⟩
    rw [starImage_eq_one_iff]
    exact fun g hg => (hι.comm_iff g hg y hyl).2 (key _ (hι.mem hg)).symm
  ·
    have himg : lqMap D d '' muSet D d c = lqMap D d '' muSet D d y :=
      eq_of_subset_of_isTwinSection (hsec c hc hcd) (hsec y hyD hcomm)
        (Set.image_mono fun s hs => ⟨hs.1, hsub hs⟩)
    have heq := (hι.image_eq_image_iff (muSet_subset_localClass d c)
      (muSet_subset_localClass d y)).1 himg
    exact Or.inr (hfib c hc hcd y hyD hcomm heq.symm)

end CFSG.Fischer.Classification.O2Bridge
