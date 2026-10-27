module

public import CFSG.CGT.Timmesfeld75.Sec4NineAbs
public import CFSG.CGT.Timmesfeld75.Sec5FiveBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIFinal

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] {T : Subgroup G}

theorem conjSubgroup_centralizer_of_mem_normalizer {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup n (Subgroup.centralizer (T : Set G)) = Subgroup.centralizer (T : Set G) := by
  have hn' : n⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer (T : Set G)).inv_mem hn
  have key : ∀ m ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ Subgroup.centralizer (T : Set G),
      m * x * m⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    intro m hm x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro t ht
    have h1 : m⁻¹ * t * m ∈ T := by
      simpa using conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hm) ht
    calc t * (m * x * m⁻¹) = m * ((m⁻¹ * t * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * t * m)) * m⁻¹ := by rw [hx _ h1]
      _ = (m * x * m⁻¹) * t := by group
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro h
    simpa [mul_assoc] using key n hn _ h
  · intro h
    simpa using key n⁻¹ hn' x h

theorem barSub_centralizer_normal :
    (barSub T (Subgroup.centralizer (T : Set G))).Normal :=
  barSub_normal fun _ hn => conjSubgroup_centralizer_of_mem_normalizer hn

end Gen

section Nine

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {h : G}

theorem IsUIdx.inf_barSub_centralizer_eq_bot (hu : IsUIdx T T₁ h) (hP : MaxPair T T₁)
    (hS : Sec3Global T) :
    barSub T (Subgroup.centralizer (T : Set G)) ⊓ barSub T (normIn (conjSubgroup h T) T) = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨hyA, hyL⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨u, huN, huC, rfl⟩ := exists_eq_barElt_of_mem_barSub hyA
  obtain ⟨v, hvN, hvL, hvu⟩ := exists_eq_barElt_of_mem_barSub hyL
  have huc : ∀ t ∈ T, u * t = t * u := fun t ht => (Subgroup.mem_centralizer_iff.1 huC t ht).symm
  have hvT : v⁻¹ * u ∈ T := (barElt_eq_iff hvN huN).1 hvu
  have hvc : ∀ t ∈ T, v * t = t * v := by
    intro t ht
    obtain ⟨s, hs⟩ : ∃ s, s = v⁻¹ * u := ⟨_, rfl⟩
    have hsT : s ∈ T := hs ▸ hvT
    have hv : v = u * s⁻¹ := by rw [hs]; group
    calc v * t = (u * s⁻¹) * t := by rw [← hv]
      _ = u * (s⁻¹ * t) := mul_assoc _ _ _
      _ = u * (t * s⁻¹) := by rw [elemAbelian_mul_comm hP.wc.1 (T.inv_mem hsT) ht]
      _ = (u * t) * s⁻¹ := (mul_assoc _ _ _).symm
      _ = (t * u) * s⁻¹ := by rw [huc t ht]
      _ = t * (u * s⁻¹) := mul_assoc _ _ _
      _ = t * v := by rw [← hv]
  have hv1 : v = 1 := by
    by_contra hv1
    have hcfg := (hu.sec3 hP hS).cfg
    have hTC : T ≤ Subgroup.centralizer ({v} : Set G) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (hvc t ht).symm
    have heq := hcfg.inf_centralizer_eq_normIn hvL hv1
    rw [inf_eq_left.2 hTC] at heq
    have hlt := hcfg.normIn_lt (⟨h, rfl⟩ : ∃ x : G, conjSubgroup h T = conjSubgroup x T)
    rw [← heq] at hlt
    exact lt_irrefl _ hlt
  rw [← hvu]
  exact Subgroup.mem_bot.2 ((barElt_eq_one_iff hvN).2 (by rw [hv1]; exact T.one_mem))

theorem IsUIdx.four_le_card_barSub (hu : IsUIdx T T₁ h) (hP : MaxPair T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) (h4 : 4 < Nat.card T) :
    4 ≤ Nat.card (barSub T (normIn (conjSubgroup h T) T)) := by
  have hS' := hu.sec3 hP hS
  have hI' : Sec3Iso T (conjSubgroup h T) := hI h hu.1 (hu.normIn_ne_bot hP)
  have hsq := hS'.card_le_sq_card_normIn hI'
  obtain ⟨n, -, hLn, hL1n, -⟩ := hS'.card_normIn_eq_two_pow
  have hUN : normIn (conjSubgroup h T) T ≤ Subgroup.normalizer (T : Set G) := inf_le_right
  have hUT : normIn (conjSubgroup h T) T ⊓ T = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ T ⊓ conjSubgroup h T := ⟨hx.2, (mem_normIn.1 hx.1).1⟩
    rwa [hP.wc.inf_conj_eq_bot hu.1] at hx'
  rw [card_barSub hUN hUT, hL1n]
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n ≤ 1 := by omega
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    rw [hLn] at hsq
    have h2 : (2 ^ n) ^ 2 ≤ 4 := calc
      (2 ^ n) ^ 2 ≤ (2 ^ 1) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 4 := by norm_num
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

end Nine

theorem sec4Nine_of_noA (h1 : Sec4NoA) : Sec4Nine := by
  intro G _ T T₁ hy hS hI h4 c hcP hcT x hxP
  have : Finite G := hy.finite
  have hP := hy.pair
  have hPN : hSubU T T₁ ≤ Subgroup.normalizer (T : Set G) :=
    sup_le Subgroup.le_normalizer (iSup₂_le fun _ _ => inf_le_right)
  have hcN := hPN hcP
  have hcC : c ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun t ht => (hcT t ht).symm
  have : (barSub T (Subgroup.centralizer (T : Set G))).Normal := barSub_centralizer_normal
  have hcA : barElt T hcN ∈ barSub T (Subgroup.centralizer (T : Set G)) :=
    barElt_mem_barSub hcN hcC
  let N' := Subgroup.normalizer (T : Set G)
  let φ : ↥N' →* NQuot T := QuotientGroup.mk' (T.subgroupOf N')
  let S : Subgroup G :=
    ((Subgroup.centralizer ({barElt T hcN} : Set (NQuot T))).comap φ).map N'.subtype
  have hmemS : ∀ z (hz : z ∈ N'),
      barElt T hz ∈ Subgroup.centralizer ({barElt T hcN} : Set (NQuot T)) → z ∈ S :=
    fun z hz hzc => ⟨⟨z, hz⟩, hzc, rfl⟩
  have hTS : T ≤ S := fun t ht => hmemS t (Subgroup.le_normalizer ht) (by
    rw [(barElt_eq_one_iff _).2 ht]
    exact Subgroup.one_mem _)
  have hLS : ∀ g : G, IsUIdx T T₁ g → normIn (conjSubgroup g T) T ≤ S := by
    intro g hg v hv
    have hvN : v ∈ N' := (mem_normIn.1 hv).2
    have hWC : IsWC (barSub T (normIn (conjSubgroup g T) T)) :=
      sec48_of_noA h1 G T (conjSubgroup g T) (hg.stepHyp hy hS) hS hI
    have hcomm := hWC.comm_of_inf_eq_bot (hg.four_le_card_barSub hP hS hI h4)
      (hg.inf_barSub_centralizer_eq_bot hP hS) _ hcA _ (barElt_mem_barSub hvN hv)
    refine hmemS v hvN (Subgroup.mem_centralizer_iff.2 fun w hw => ?_)
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hcomm
  have hPS : hSubU T T₁ ≤ S := sup_le hTS (iSup₂_le fun g hg => hLS g hg)
  obtain ⟨w, hw, hwx⟩ := hPS hxP
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := hPN hxP
  have hcx : barElt T hcN * barElt T hxN = barElt T hxN * barElt T hcN := by
    have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hw) (barElt T hcN) rfl
    have hwx' : w = ⟨x, hxN⟩ := Subtype.ext hwx
    rw [hwx'] at this
    exact this
  exact commutator_mem_of_bar_comm hcN hxN hcx

end CFSG.CGT.Timmesfeld75
