module

public import CFSG.CGT.Timmesfeld75.Sec5OutDefs
public import CFSG.CGT.Timmesfeld75.Sec3TwelveRho
public import CFSG.CGT.Timmesfeld75.Sec3Eleven
public import CFSG.CGT.Timmesfeld75.Sec4OneCommon
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G}

section Conj

theorem mem_classD_of_mem_conjSubgroup {k x : G} (hx : x ∈ conjSubgroup k T) (hx1 : x ≠ 1) :
    x ∈ classD T :=
  ⟨k⁻¹, k⁻¹ * x * k, mem_conjSubgroup.1 hx, fun h => hx1 (by
    have e : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [e, h]
    group), by group⟩

theorem mem_normD_of_mem_conjSubgroup {k x : G} (hx : x ∈ conjSubgroup k T) (hx1 : x ≠ 1)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) : x ∈ normD T :=
  ⟨mem_classD_of_mem_conjSubgroup hx hx1, hxN⟩

theorem MaxPair.conj_normalizer (hP : MaxPair T T₁) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) : MaxPair T (conjSubgroup g T₁) where
  wc := hP.wc
  conj := by
    obtain ⟨x, hx⟩ := hP.conj
    exact ⟨g * x, by rw [hx, conjSubgroup_conjSubgroup]⟩
  ne := hP.conjSubgroup_ne hg
  nontriv := by
    rw [normIn_conjSubgroup_of_mem_normalizer hg]
    exact fun h => hP.nontriv (conjSubgroup_eq_bot_iff.1 h)
  maximal := fun k hk => by
    rw [normIn_conjSubgroup_of_mem_normalizer hg, card_conjSubgroup]
    exact hP.maximal k hk

theorem StepHyp.conj_normalizer (hy : StepHyp T T₁) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) : StepHyp T (conjSubgroup g T₁) where
  finite := hy.finite
  simple := hy.simple
  nonab := hy.nonab
  pair := hy.pair.conj_normalizer hg
  card := hy.card
  ind := hy.ind

end Conj

section UIdx

variable [Finite G] {h : G}

omit [Finite G] in
theorem IsUIdx.normIn_conj_ne_bot (hu : IsUIdx T T₁ h) (hP : MaxPair T T₁) :
    normIn (conjSubgroup h T) T ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card (normIn T T₁) = 1 := by
    rw [← hu.2, hbot]
    simp
  exact hP.nontriv (Subgroup.card_eq_one.1 h1)

theorem IsUIdx.normIn_ne_bot (hu : IsUIdx T T₁ h) (hP : MaxPair T T₁) :
    normIn T (conjSubgroup h T) ≠ ⊥ :=
  normIn_ne_bot_of_conj hP.wc hu.1 (hu.normIn_conj_ne_bot hP)

theorem IsUIdx.sec3 (hu : IsUIdx T T₁ h) (hP : MaxPair T T₁) (hS : Sec3Global T) :
    Sec3 T (conjSubgroup h T) :=
  hS h hu.1 (hu.normIn_ne_bot hP)

theorem IsUIdx.card_normIn (hu : IsUIdx T T₁ h) (hP : MaxPair T T₁) (hS : Sec3Global T) :
    Nat.card (normIn T (conjSubgroup h T)) = Nat.card (normIn T T₁) :=
  ((hu.sec3 hP hS).card_normIn_swap).symm.trans hu.2

theorem IsUIdx.maxPair (hu : IsUIdx T T₁ h) (hP : MaxPair T T₁) (hS : Sec3Global T) :
    MaxPair T (conjSubgroup h T) where
  wc := hP.wc
  conj := ⟨h, rfl⟩
  ne := hu.1
  nontriv := hu.normIn_ne_bot hP
  maximal := fun k hk => (hP.maximal k hk).trans (hu.card_normIn hP hS).symm.le

theorem IsUIdx.stepHyp (hu : IsUIdx T T₁ h) (hy : StepHyp T T₁) (hS : Sec3Global T) :
    StepHyp T (conjSubgroup h T) :=
  { hy with pair := hu.maxPair hy.pair hS }

omit [Finite G] in
theorem IsUIdx.mul_normalizer (hu : IsUIdx T T₁ h) {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) : IsUIdx T T₁ (n * h) := by
  have hnT : conjSubgroup n T = T := mem_normalizer_iff_conjSubgroup_eq.1 hn
  have e : conjSubgroup (n * h) T = conjSubgroup n (conjSubgroup h T) :=
    (conjSubgroup_conjSubgroup n h T).symm
  refine ⟨fun h' => hu.1 ?_, ?_⟩
  · rw [e] at h'
    have hn' : conjSubgroup n⁻¹ T = T :=
      mem_normalizer_iff_conjSubgroup_eq.1 ((Subgroup.normalizer (T : Set G)).inv_mem hn)
    have h'' := congrArg (conjSubgroup n⁻¹) h'
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, hn'] at h''
    exact h''
  · have h2 := normIn_conj n (conjSubgroup h T) T
    rw [hnT] at h2
    rw [e, h2, card_conjSubgroup]
    exact hu.2

end UIdx

section Four

variable [Finite G]

omit [Finite G] in
theorem conjSubgroup_normIn_le_of_comm (h1 : Sec4NoA) (hy : StepHyp T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) {l : G}
    (hlL : l ∈ normIn T₁ T) (hl1 : l ≠ 1)
    (hcomm : ∀ u ∈ conjSubgroup g (normIn T₁ T), ⁅l, u⁆ ∈ T) :
    conjSubgroup g (normIn T₁ T) ≤ normIn T₁ T ⊔ T := by
  have hP := hy.pair
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have hsec3 : Sec3 T T₁ := hP.sec3 hS
  have hgT : conjSubgroup g T = T := mem_normalizer_iff_conjSubgroup_eq.1 hg
  have hL₁' : normIn (conjSubgroup g T₁) T = conjSubgroup g (normIn T₁ T) := by
    have := normIn_conj g T₁ T
    rwa [hgT] at this
  have hL₁'N : conjSubgroup g (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) :=
    conjSubgroup_le_normalizer hg inf_le_right
  have hlT₁ : l ∈ T₁ := normIn_le _ _ hlL
  by_cases hlin : l ∈ conjSubgroup g (normIn T₁ T) ⊔ T
  · have hmul := Subgroup.coe_mul_of_left_le_normalizer_right
      (conjSubgroup g (normIn T₁ T)) T hL₁'N
    have hlin' : l ∈ ((conjSubgroup g (normIn T₁ T) : Set G) * (T : Set G)) := by
      rw [← hmul]
      exact hlin
    obtain ⟨u, hu, t, ht, hult0⟩ := hlin'
    have hult : u * t = l := hult0
    have hu1 : u ≠ 1 := by
      intro hu1
      rw [hu1, one_mul] at hult
      have hlT : l ∈ T ⊓ T₁ := ⟨hult ▸ ht, hlT₁⟩
      rw [hsec3.cfg.inf, Subgroup.mem_bot] at hlT
      exact hl1 hlT
    have hne : conjSubgroup g (normIn T₁ T) ⊓ (normIn T₁ T ⊔ T) ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.2
        ⟨⟨u, hu, ?_⟩, fun h' => hu1 (congrArg Subtype.val h')⟩
      have hu' : u = l * t⁻¹ := by rw [← hult]; group
      rw [hu']
      exact (normIn T₁ T ⊔ T).mul_mem (Subgroup.mem_sup_left hlL)
        ((normIn T₁ T ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
    obtain ⟨hc1, -⟩ := hsec3.cfg.commute_conj_L₁ hg hne
    intro a ha
    by_contra haL
    have haT₁ : a ∈ conjSubgroup g T₁ := conjSubgroup_mono (normIn_le _ _) ha
    have ha1 : a ≠ 1 := fun h' => haL (h' ▸ (normIn T₁ T ⊔ T).one_mem)
    have haD : a ∈ normD T := by
      rw [hx₀, conjSubgroup_conjSubgroup] at haT₁
      exact mem_normD_of_mem_conjSubgroup haT₁ ha1 (hL₁'N ha)
    refine h1 G T T₁ hy hS hI a haD (fun h' => haL ?_) (fun l' hl' => ?_)
    · rw [sup_comm]
      exact h'
    · have hcm := hc1 a ha l' hl'
      rw [commutatorElement_eq_one_iff_mul_comm.2 hcm]
      exact T.one_mem
  · exfalso
    have hy' := hy.conj_normalizer hg
    have hlD : l ∈ normD T := by
      have hlT₁' : l ∈ conjSubgroup x₀ T := hx₀ ▸ hlT₁
      exact mem_normD_of_mem_conjSubgroup hlT₁' hl1 (mem_normIn.1 hlL).2
    refine h1 G T (conjSubgroup g T₁) hy' hS hI l hlD ?_ fun l' hl' => ?_
    · rw [hL₁', sup_comm]
      exact hlin
    · rw [hL₁'] at hl'
      exact hcomm l' hl'

theorem sec48_of_noA (h1 : Sec4NoA) : Sec48 := by
  intro G _ T T₁ hy hS hI
  have : Finite G := hy.finite
  have hP := hy.pair
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have hT₁ab : IsElemAbelian 2 T₁ := by
    rw [hx₀]
    exact isElemAbelian_conjSubgroup hP.wc.1 x₀
  have hL₁le : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := inf_le_right
  have hVab : IsElemAbelian 2 (barSub T (normIn T₁ T)) :=
    isElemAbelian_barSub (isElemAbelian_subgroup_of_le hT₁ab (normIn_le _ _))
  refine ⟨hVab, fun tb htb htb1 => ⟨fun z hz => ?_, fun γ hγ => ?_⟩⟩
  · refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact elemAbelian_mul_comm hVab htb hz
  · obtain ⟨xγ, rfl⟩ := QuotientGroup.mk_surjective γ
    have hg : (xγ : G) ∈ Subgroup.normalizer (T : Set G) := xγ.2
    have hγe : (QuotientGroup.mk xγ : NQuot T) = barElt T hg := rfl
    rw [hγe] at hγ ⊢
    obtain ⟨l, hl, hlL, rfl⟩ := exists_eq_barElt_of_mem_barSub htb
    have hl1 : l ≠ 1 := fun h => htb1 (by subst h; exact barElt_one)
    have hL₁'N : conjSubgroup (xγ : G) (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) :=
      conjSubgroup_le_normalizer hg hL₁le
    rw [conjSubgroup_barSub hg] at hγ
    have hcomm : ∀ u ∈ conjSubgroup (xγ : G) (normIn T₁ T), ⁅l, u⁆ ∈ T := by
      intro u hu
      have huN := hL₁'N hu
      have hmem : barElt T huN ∈ barSub T (conjSubgroup (xγ : G) (normIn T₁ T)) :=
        barElt_mem_barSub huN hu
      exact commutator_mem_of_bar_comm hl huN
        (Subgroup.mem_centralizer_iff.1 (hγ hmem) (barElt T hl) (Set.mem_singleton _))
    have hle := conjSubgroup_normIn_le_of_comm h1 hy hS hI hg hlL hl1 hcomm
    refine conjSubgroup_eq_of_le ?_
    rw [conjSubgroup_barSub hg]
    exact barSub_le_of_le_sup hL₁le (fun u hu _ => hle hu)

end Four

section SecA

variable [Finite G]

theorem secA_le_normIn_conj (hP : MaxPair T T₁) (hS : Sec3Global T) {k : G}
    (hne : conjSubgroup k T ≠ T) (hL : normIn T (conjSubgroup k T) ≠ ⊥) :
    secA T T₁ ≤ normIn T (conjSubgroup k T) := by
  have c : Cfg T (conjSubgroup k T) := Cfg.of_conj hP.wc hne hL
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.ne₁
  have hl1' : l ≠ 1 := fun h => hl1 (Subtype.ext h)
  have hlD : l ∈ normD T :=
    mem_normD_of_mem_conjSubgroup (normIn_le _ _ hl) hl1' (mem_normIn.1 hl).2
  rw [← c.inf_centralizer_eq_normIn hl hl1']
  exact le_inf secA_le_left ((secA_le_centralizer_normD hP hS).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hlD)))

theorem conjSubgroup_secA_le_normIn (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G}
    (hne : conjSubgroup h T ≠ T) (hL : normIn (conjSubgroup h T) T ≠ ⊥) :
    conjSubgroup h (secA T T₁) ≤ normIn (conjSubgroup h T) T := by
  have hne' : conjSubgroup h⁻¹ T ≠ T := fun h' => hne (by
    have := congrArg (conjSubgroup h) h'
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at this
    exact this.symm)
  have h2 := normIn_conj h T (conjSubgroup h⁻¹ T)
  rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
  have hL' : normIn T (conjSubgroup h⁻¹ T) ≠ ⊥ := fun hbot => hL (by
    rw [h2, hbot]
    exact Subgroup.map_bot _)
  rw [h2]
  exact conjSubgroup_mono (secA_le_normIn_conj hP hS hne' hL')

theorem secA_comm_conjSubgroup_secA (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G}
    (hne : conjSubgroup h T ≠ T) (hL : normIn (conjSubgroup h T) T ≠ ⊥) :
    ∀ a ∈ secA T T₁, ∀ x ∈ conjSubgroup h (secA T T₁), a * x = x * a := by
  intro a ha x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    simp
  have hxL := conjSubgroup_secA_le_normIn hP hS hne hL hx
  have hxD : x ∈ normD T :=
    mem_normD_of_mem_conjSubgroup (normIn_le _ _ hxL) hx1 (mem_normIn.1 hxL).2
  exact (Subgroup.mem_centralizer_iff.1 (secA_le_centralizer_normD hP hS ha) x hxD).symm

theorem commutator_conj_secA_le_of_ne (hP : MaxPair T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) {h : G} (hne : conjSubgroup h T ≠ T)
    (hL : normIn (conjSubgroup h T) T ≠ ⊥) :
    ∀ x ∈ conjSubgroup h (secA T T₁), ∀ t ∈ T, ⁅x, t⁆ ∈ secA T T₁ := by
  intro x hx t ht
  have hLT : normIn T (conjSubgroup h T) ≠ ⊥ := normIn_ne_bot_of_conj hP.wc hne hL
  have hs : Sec3 T (conjSubgroup h T) := hS h hne hLT
  have hA : secA T T₁ ≤ normIn T (conjSubgroup h T) := secA_le_normIn_conj hP hS hne hLT
  obtain ⟨hN, f, hf, hpsl⟩ := hI h hne hLT
  have hV := hs.conjSubgroup_sup_conj_eq hf hpsl (g := h) rfl hA
    (fun n hn => mem_normalizer_of_conjSubgroup_eq (conjSubgroup_secA hn))
  have hxL := conjSubgroup_secA_le_normIn hP hS hne hL hx
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hxL).2
  have hxT' : x ∈ conjSubgroup h T := normIn_le _ _ hxL
  have h1 : t * x * t⁻¹ ∈ secA T T₁ ⊔ conjSubgroup h (secA T T₁) := by
    have hxV : x ∈ secA T T₁ ⊔ conjSubgroup h (secA T T₁) := Subgroup.mem_sup_right hx
    have := conj_mem_conjSubgroup t hxV
    rwa [hV t (Subgroup.mem_sup_left ht)] at this
  have h2 : ⁅t, x⁆ ∈ secA T T₁ ⊔ conjSubgroup h (secA T T₁) := by
    have hxinv : x⁻¹ ∈ secA T T₁ ⊔ conjSubgroup h (secA T T₁) :=
      (secA T T₁ ⊔ conjSubgroup h (secA T T₁)).inv_mem (Subgroup.mem_sup_right hx)
    simpa [commutatorElement_def] using
      (secA T T₁ ⊔ conjSubgroup h (secA T T₁)).mul_mem h1 hxinv
  have h3 : ⁅t, x⁆ ∈ T := by
    have hxt : x * t⁻¹ * x⁻¹ ∈ T := conj_mem_of_mem_normalizer hxN (T.inv_mem ht)
    simpa [commutatorElement_def, mul_assoc] using T.mul_mem ht hxt
  have hcomm := secA_comm_conjSubgroup_secA hP hS hne hL
  have hay : ∀ a ∈ secA T T₁, ∀ y' ∈ conjSubgroup h (secA T T₁), a * y' * a⁻¹ = y' :=
    fun a ha y' hy' => by rw [hcomm a ha y' hy', mul_inv_cancel_right]
  have hAn : secA T T₁ ≤ Subgroup.normalizer (conjSubgroup h (secA T T₁) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy'
      rw [hay a ha y hy']
      exact hy'
    · intro hy'
      have h' := hay a⁻¹ ((secA T T₁).inv_mem ha) _ hy'
      have e : y = a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ := by group
      rw [e, h']
      exact hy'
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (secA T T₁)
    (conjSubgroup h (secA T T₁)) hAn
  have h2' : ⁅t, x⁆ ∈ ((secA T T₁ : Set G) * (conjSubgroup h (secA T T₁) : Set G)) := by
    rw [← hmul]
    exact h2
  obtain ⟨a, ha, y, hy, hay0⟩ := h2'
  have hay : a * y = ⁅t, x⁆ := hay0
  have hT_inf : T ⊓ conjSubgroup h T = ⊥ := hP.wc.inf_conj_eq_bot hne
  have hyT : y ∈ T ⊓ conjSubgroup h T := by
    refine ⟨?_, normIn_le _ _ (conjSubgroup_secA_le_normIn hP hS hne hL hy)⟩
    have : y = a⁻¹ * ⁅t, x⁆ := by rw [← hay]; group
    rw [this]
    exact T.mul_mem (T.inv_mem (secA_le_left ha)) h3
  rw [hT_inf, Subgroup.mem_bot] at hyT
  have hmem : ⁅t, x⁆ ∈ secA T T₁ := by
    rw [← hay, hyT, mul_one]
    exact ha
  have := (secA T T₁).inv_mem hmem
  rwa [commutatorElement_inv] at this

theorem commutator_conj_secA_le_centralizer_of_ne (hP : MaxPair T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) {g h : G} (hgne : conjSubgroup g T ≠ T)
    (hgL : normIn (conjSubgroup g T) T ≠ ⊥) (hhne : conjSubgroup h T ≠ T)
    (hhL : normIn (conjSubgroup h T) T ≠ ⊥) :
    ⁅conjSubgroup g (secA T T₁), conjSubgroup h (secA T T₁)⁆ ≤
      Subgroup.centralizer (T : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hAg : ⁅conjSubgroup g (secA T T₁), T⁆ ≤ secA T T₁ :=
    Subgroup.commutator_le.2 (commutator_conj_secA_le_of_ne hP hS hI hgne hgL)
  have hAh : ⁅conjSubgroup h (secA T T₁), T⁆ ≤ secA T T₁ :=
    Subgroup.commutator_le.2 (commutator_conj_secA_le_of_ne hP hS hI hhne hhL)
  have h1 : ⁅⁅conjSubgroup h (secA T T₁), T⁆, conjSubgroup g (secA T T₁)⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.commutator_mono_left hAh).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact secA_comm_conjSubgroup_secA hP hS hgne hgL a ha x hx
  have h2 : ⁅⁅T, conjSubgroup g (secA T T₁)⁆, conjSubgroup h (secA T T₁)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_comm T]
    refine (Subgroup.commutator_mono_left hAg).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact secA_comm_conjSubgroup_secA hP hS hhne hhL a ha x hx
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem commutator_conj_secA_le_centralizer (hP : MaxPair T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) {g h : G} (hg : IsUIdx T T₁ g) (hh : IsUIdx T T₁ h) :
    ⁅conjSubgroup g (secA T T₁), conjSubgroup h (secA T T₁)⁆ ≤
      Subgroup.centralizer (T : Set G) :=
  commutator_conj_secA_le_centralizer_of_ne hP hS hI hg.1 (hg.normIn_conj_ne_bot hP) hh.1
    (hh.normIn_conj_ne_bot hP)

end SecA

end CFSG.CGT.Timmesfeld75
