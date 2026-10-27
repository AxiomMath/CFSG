module

public import CFSG.CGT.Timmesfeld75.Sec5FiveComm

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem mem_classD_conjSubgroup {x : G} (hx : x ∈ classD T) (x₀ : G) :
    x ∈ classD (conjSubgroup x₀ T) := by
  obtain ⟨k, t, ht, ht1, hxk⟩ := hx
  refine ⟨x₀ * k, x₀ * t * x₀⁻¹, conj_mem_conjSubgroup x₀ ht, fun h' => ht1 ?_, ?_⟩
  · calc t = x₀⁻¹ * (x₀ * t * x₀⁻¹) * x₀ := by group
      _ = 1 := by rw [h']; group
  · rw [hxk]
    group

section Five

variable [Finite G]

theorem conjSubgroup_secA_comm_of_mem_normalizer (hP : MaxPair T T₁) (hS : Sec3Global T) {k y : G}
    (hyD : y ∈ classD T) (hyN : y ∈ Subgroup.normalizer ((conjSubgroup k T : Subgroup G) : Set G)) :
    ∀ a ∈ conjSubgroup k (secA T T₁), a * y = y * a := by
  intro a ha
  have ha' : k⁻¹ * a * k ∈ secA T T₁ := mem_conjSubgroup.1 ha
  have hyD' : k⁻¹ * y * k ∈ classD T := classD_conj hyD k
  have hyN' : k⁻¹ * y * k ∈ Subgroup.normalizer (T : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have h1 := mem_normalizer_iff_conjSubgroup_eq.1 hyN
    calc conjSubgroup (k⁻¹ * y * k) T = conjSubgroup k⁻¹ (conjSubgroup y (conjSubgroup k T)) := by
          rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      _ = T := by rw [h1, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hc := Subgroup.mem_centralizer_iff.1 (secA_le_centralizer_normD hP hS ha') _
    (⟨hyD', hyN'⟩ : k⁻¹ * y * k ∈ normD T)
  calc a * y = k * ((k⁻¹ * a * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * y * k) * (k⁻¹ * a * k)) * k⁻¹ := by rw [← hc]
    _ = y * a := by group

omit [Finite G] in
theorem conjSubgroup_secA_conj_of_mem_normalizer {k n : G}
    (hn : n ∈ Subgroup.normalizer ((conjSubgroup k T : Subgroup G) : Set G)) :
    conjSubgroup n (conjSubgroup k (secA T T₁)) = conjSubgroup k (secA T T₁) := by
  have h1 : k⁻¹ * n * k ∈ Subgroup.normalizer (T : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have h2 := mem_normalizer_iff_conjSubgroup_eq.1 hn
    calc conjSubgroup (k⁻¹ * n * k) T = conjSubgroup k⁻¹ (conjSubgroup n (conjSubgroup k T)) := by
          rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      _ = T := by rw [h2, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  calc conjSubgroup n (conjSubgroup k (secA T T₁)) =
        conjSubgroup k (conjSubgroup (k⁻¹ * n * k) (secA T T₁)) := by
        rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
        congr 1
        group
    _ = conjSubgroup k (secA T T₁) := by rw [conjSubgroup_secA h1]

omit [Finite G] in
theorem card_normIn_conj_le (hP : MaxPair T T₁) {x₀ : G} (hx₀ : T₁ = conjSubgroup x₀ T) {g : G}
    (hg : conjSubgroup g T₁ ≠ T₁) :
    Nat.card (normIn T₁ (conjSubgroup g T₁)) ≤ Nat.card (normIn T T₁) := by
  have e : conjSubgroup g T₁ = conjSubgroup x₀ (conjSubgroup (x₀⁻¹ * g * x₀) T) := by
    rw [hx₀, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  have hne : conjSubgroup (x₀⁻¹ * g * x₀) T ≠ T := fun h' => hg (by rw [e, h', ← hx₀])
  have h1 : normIn T₁ (conjSubgroup g T₁) =
      conjSubgroup x₀ (normIn T (conjSubgroup (x₀⁻¹ * g * x₀) T)) := by
    rw [← normIn_conj, ← e, ← hx₀]
  rw [h1, card_conjSubgroup]
  exact hP.maximal _ hne

theorem isUIdx_of_conj (hP : MaxPair T T₁) (hS : Sec3Global T) {x₀ : G}
    (hx₀ : T₁ = conjSubgroup x₀ T) : IsUIdx T T₁ x₀ := by
  have hne : conjSubgroup x₀ T ≠ T := by rw [← hx₀]; exact hP.ne
  refine ⟨hne, ?_⟩
  rw [← hx₀]
  exact (hP.sec3 hS).card_normIn_swap

theorem isUIdx_conj_iff (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G} (hu : IsUIdx T T₁ h)
    {k : G} : IsUIdx T (conjSubgroup h T) k ↔ IsUIdx T T₁ k := by
  have hc := hu.card_normIn hP hS
  unfold IsUIdx
  rw [hc]

theorem secA_eq_of_isUIdx (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G}
    (hu : IsUIdx T T₁ h) : secA T (conjSubgroup h T) = secA T T₁ := by
  rw [secA_eq_centralizer_normD (hu.maxPair hP hS) hS, secA_eq_centralizer_normD hP hS]

theorem secR₁_eq_of_isUIdx (hP : MaxPair T T₁) (hS : Sec3Global T) {h : G}
    (hu : IsUIdx T T₁ h) : secR₁ T (conjSubgroup h T) = secR₁ T T₁ := by
  unfold secR₁
  rw [secA_eq_of_isUIdx hP hS hu]
  refine le_antisymm (iSup₂_le fun k hk => ?_) (iSup₂_le fun k hk => ?_)
  · exact le_iSup₂ (f := fun (k : G) (_ : IsUIdx T T₁ k) => conjSubgroup k (secA T T₁)) k
      ((isUIdx_conj_iff hP hS hu).1 hk)
  · exact le_iSup₂ (f := fun (k : G) (_ : IsUIdx T (conjSubgroup h T) k) =>
      conjSubgroup k (secA T T₁)) k ((isUIdx_conj_iff hP hS hu).2 hk)

theorem conj_normIn_le_of_mem_secR₁ (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T) (hA4 : secA T T₁ ≠ normIn T T₁) {x : G}
    (hx : x ∈ secR₁ T T₁) : ∀ l ∈ normIn T₁ T, x * l * x⁻¹ ∈ normIn T₁ T ⊔ T := by
  have hP := hy.pair
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := secR₁_le_normalizer hP hS hx
  have hV : IsWC (barSub T (normIn T₁ T)) := sec48_of_noA h1 G T T₁ hy hS hI
  have hRn : (barSub T (secR₁ T T₁)).Normal :=
    barSub_normal (fun n hn => conjSubgroup_secR₁ hn)
  have hR2 : IsPGroup 2 (barSub T (secR₁ T T₁)) :=
    isPGroup_barSub (isPGroup_secR₁ h1 h3 hy hS hI hA4)
  have hL₁2 : IsPGroup 2 (normIn T₁ T) :=
    (isPGroup_two_of_isElemAbelian (hP.sec3 hS).cfg.wc₁.1).to_le (normIn_le _ _)
  have hV2 : IsPGroup 2 (barSub T (normIn T₁ T)) := isPGroup_barSub hL₁2
  obtain ⟨P, hVP⟩ := hV2.exists_le_sylow
  have hRP : barSub T (secR₁ T T₁) ≤ (P : Subgroup (NQuot T)) :=
    le_sylow_of_normal_pGroup hRn hR2 P
  have hxbar : barElt T hxN ∈ (P : Subgroup (NQuot T)) := hRP (barElt_mem_barSub hxN hx)
  have hconj : conjSubgroup (barElt T hxN) (barSub T (normIn T₁ T)) ≤ (P : Subgroup (NQuot T)) :=
    conjSubgroup_le_of_le_of_mem hVP hxbar
  have heq := eq_of_conj_le_pGroup hV P.isPGroup' hVP hconj
  rw [conjSubgroup_barSub hxN] at heq
  intro l hl
  have hlN : l ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 (hl)).2
  have hyN : x * l * x⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
    have := (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hxN hlN)
      ((Subgroup.normalizer (T : Set G)).inv_mem hxN)
    exact this
  have hmem : barElt T hyN ∈ barSub T (conjSubgroup x (normIn T₁ T)) :=
    barElt_mem_barSub hyN (conj_mem_conjSubgroup x hl)
  rw [heq] at hmem
  obtain ⟨u, huN, huL, hu⟩ := (barElt_mem_barSub_iff hyN).1 hmem
  have e : x * l * x⁻¹ = u * (u⁻¹ * (x * l * x⁻¹)) := by group
  rw [e]
  exact (normIn T₁ T ⊔ T).mul_mem (Subgroup.mem_sup_left huL) (Subgroup.mem_sup_right hu)

end Five

end CFSG.CGT.Timmesfeld75
