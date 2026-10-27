module

public import CFSG.CGT.Timmesfeld75.Sec4TwoQuot
public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Sec3L2
public import CFSG.CGT.Timmesfeld75.Lemma25
public import CFSG.CGT.Timmesfeld75.Sec4TwoBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Struct

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem Sec4Hyp.sec3Iso (h : Sec4Hyp T T₁ a T₂) : Sec3Iso T T₁ :=
  sec3Iso_of_conj_conj h.iso ⟨1, (conjSubgroup_one T).symm⟩ h.pair.conj h.pair.ne
    h.pair.nontriv

theorem Sec4Hyp.exists_mem_mid_not_mem_sec4N (h : Sec4Hyp T T₁ a T₂) :
    ∃ c ∈ T₁, ∀ t ∈ T, t⁻¹ * c ∉ sec4N T T₁ T₂ := by
  by_contra hcon'
  have hcon : ∀ c ∈ T₁, ∃ t ∈ T, t⁻¹ * c ∈ sec4N T T₁ T₂ := by
    intro c hc
    by_contra hnot
    exact hcon' ⟨c, hc, fun t ht hmem => hnot ⟨t, ht, hmem⟩⟩
  have hT₁N : T₁ ≤ Subgroup.normalizer (T : Set G) := by
    intro c hc
    obtain ⟨t, ht, htc⟩ := hcon c hc
    have e : c = t * (t⁻¹ * c) := by group
    rw [e]
    exact (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer ht)
      (sec4N_le_normalizer_left htc)
  obtain ⟨s, -, -, -, hsT₁⟩ := h.sec3.exists_swap
  have hlt : normIn T₁ T < T₁ := h.sec3.cfg.symm.normIn_lt ⟨s, hsT₁.symm⟩
  exact hlt.ne (le_antisymm (normIn_le _ _) fun x hx => mem_normIn.2 ⟨hx, hT₁N hx⟩)

theorem Sec4Hyp.normalClosure_sec4Y (h : Sec4Hyp T T₁ a T₂) :
    Subgroup.normalClosure
      ((T.subgroupOf (sec4Y T T₁ T₂) : Subgroup ↥(sec4Y T T₁ T₂)) : Set ↥(sec4Y T T₁ T₂)) =
        ⊤ := by
  set NC := Subgroup.normalClosure
    ((T.subgroupOf (sec4Y T T₁ T₂) : Subgroup ↥(sec4Y T T₁ T₂)) : Set ↥(sec4Y T T₁ T₂)) with hNC
  have hT : T.subgroupOf (sec4Y T T₁ T₂) ≤ NC := Subgroup.le_normalClosure
  have hconj : ∀ x ∈ sec4Y T T₁ T₂, (conjSubgroup x T).subgroupOf (sec4Y T T₁ T₂) ≤ NC := by
    intro x hx
    rw [← conjSubgroup_subgroupOf (sec4Y T T₁ T₂) T ⟨x, hx⟩]
    rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.normalClosure_normal (s := ((T.subgroupOf (sec4Y T T₁ T₂) :
      Subgroup ↥(sec4Y T T₁ T₂)) : Set ↥(sec4Y T T₁ T₂)))).conj_mem u (hT hu) ⟨x, hx⟩
  have hT₁ : T₁.subgroupOf (sec4Y T T₁ T₂) ≤ NC := by
    obtain ⟨x, hx, hx'⟩ := h.exists_mem_sec4Y_conj₁
    have e : T₁.subgroupOf (sec4Y T T₁ T₂) = (conjSubgroup x T).subgroupOf (sec4Y T T₁ T₂) := by
      rw [← hx']
    rw [e]
    exact hconj x hx
  have hT₂ : T₂.subgroupOf (sec4Y T T₁ T₂) ≤ NC := by
    obtain ⟨x, hx, hx'⟩ := h.exists_mem_sec4Y_conj₂
    have e : T₂.subgroupOf (sec4Y T T₁ T₂) = (conjSubgroup x T).subgroupOf (sec4Y T T₁ T₂) := by
      rw [← hx']
    rw [e]
    exact hconj x hx
  have hY : sec4Y T T₁ T₂ = (T ⊔ T₁) ⊔ T₂ := rfl
  have htop : (⊤ : Subgroup ↥(sec4Y T T₁ T₂)) =
      T.subgroupOf (sec4Y T T₁ T₂) ⊔ T₁.subgroupOf (sec4Y T T₁ T₂) ⊔
        T₂.subgroupOf (sec4Y T T₁ T₂) := by
    rw [← Subgroup.subgroupOf_sup left_le_sec4Y mid_le_sec4Y,
      ← Subgroup.subgroupOf_sup (sup_le left_le_sec4Y mid_le_sec4Y) right_le_sec4Y,
      ← hY, Subgroup.subgroupOf_self]
  exact top_le_iff.1 (htop ▸ sup_le (sup_le hT hT₁) hT₂)

theorem Sec4Hyp.strongWC_img_of_le (h : Sec4Hyp T T₁ a T₂) {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hTK : T ≤ K)
    [((sec4N T T₁ T₂).subgroupOf K).Normal] :
    StrongWC ((T.subgroupOf K).map (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf K))) :=
  strongWC_img h.pair.wc hTK fun _ hg hne _ ht htN _ hc hcN =>
    h.not_comm_mod_sec4N (hK hg) hne ht htN hc hcN

theorem Sec4Hyp.img_inf_center_eq_bot_of_le (h : Sec4Hyp T T₁ a T₂) {K : Subgroup G}
    (hKY : sec4Y T T₁ T₂ ≤ K) (hK : K ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G))
    (hTK : T ≤ K) [((sec4N T T₁ T₂).subgroupOf K).Normal] :
    (T.subgroupOf K).map (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf K)) ⊓
      Subgroup.center (↥K ⧸ (sec4N T T₁ T₂).subgroupOf K) = ⊥ := by
  obtain ⟨c, hcT₁, hct⟩ := h.exists_mem_mid_not_mem_sec4N
  obtain ⟨x, hx, hx'⟩ := h.exists_mem_sec4Y_conj₁
  have hne : conjSubgroup x T ≠ T := hx' ▸ h.pair.ne
  have hcN : c ∉ sec4N T T₁ T₂ := by
    have := hct 1 (Subgroup.one_mem _)
    simpa using this
  exact img_inf_center_eq_bot hTK
    (fun _ hg hne' _ ht htN _ hc hcN' => h.not_comm_mod_sec4N (hK hg) hne' ht htN hc hcN')
    (hKY hx) hne (by rw [← hx']; exact hcT₁) hcN

omit [Finite G] in
theorem cfgM_le_sec4N : cfgM T T₁ ≤ sec4N T T₁ T₂ :=
  sup_le normIn_le_sec4N_left normIn_le_sec4N_mid

omit [Finite G] in
theorem exists_iota {K N : Subgroup G} (hXK : T ⊔ T₁ ≤ K) (hMN : cfgM T T₁ ≤ N)
    [((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] [(N.subgroupOf K).Normal] :
    ∃ ι : (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) →* (↥K ⧸ N.subgroupOf K),
      ∀ x : ↥(T ⊔ T₁), ι (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inclusion hXK x) := by
  let ι₀ : ↥(T ⊔ T₁) →* ↥K ⧸ N.subgroupOf K :=
    (QuotientGroup.mk' (N.subgroupOf K)).comp (Subgroup.inclusion hXK)
  have hker : (cfgM T T₁).subgroupOf (T ⊔ T₁) ≤ ι₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (mk_eq_one_iff_mem (Subgroup.inclusion hXK x)).2
      (hMN (Subgroup.mem_subgroupOf.1 hx))
  exact ⟨QuotientGroup.lift _ ι₀ hker, fun x => rfl⟩

theorem Sec4Hyp.exists_mem_sup_conj_of_forall (h : Sec4Hyp T T₁ a T₂)
    (hY : ∀ y ∈ sec4Y T T₁ T₂, ∃ x ∈ T ⊔ T₁, x⁻¹ * y ∈ sec4N T T₁ T₂) :
    ∃ x ∈ T ⊔ T₁, T₂ = conjSubgroup x T := by
  obtain ⟨y, hy, hy'⟩ := h.exists_mem_sec4Y_conj₂
  obtain ⟨x, hx, hn⟩ := hY y hy
  refine ⟨x, hx, ?_⟩
  have hnT : conjSubgroup (x⁻¹ * y) T = T :=
    mem_normalizer_iff_conjSubgroup_eq.1 (sec4N_le_normalizer_left hn)
  calc T₂ = conjSubgroup y T := hy'
    _ = conjSubgroup (x * (x⁻¹ * y)) T := by rw [mul_inv_cancel_left]
    _ = conjSubgroup x (conjSubgroup (x⁻¹ * y) T) := (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup x T := by rw [hnT]

end Struct

end CFSG.CGT.Timmesfeld75
