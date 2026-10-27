module

public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycles
public import CFSG.ClassicalInvolution.Phan.Geometry.Collinear

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan Module

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

section Aniso

theorem exists_aniso_orth (hσ : IsUnitaryInvolution σ) {P : Submodule K (Fin m → K)}
    (hP : Nondeg σ P) (h3 : 3 ≤ finrank K P) {u : Fin m → K} (hu : u ∈ P) :
    ∃ v ∈ P, herm σ v v ≠ 0 ∧ herm σ u v = 0 := by
  have hbot : P ≠ ⊥ := fun h => by rw [h, finrank_bot] at h3; omega
  by_cases hu0 : herm σ u u = 0
  · by_cases hz : u = 0
    · obtain ⟨v, hvP, hv⟩ := exists_aniso_of_nondeg hσ hP hbot
      exact ⟨v, hvP, hv, by rw [hz, herm_zero_left]⟩
    ·
      obtain ⟨y, hyP, hy⟩ : ∃ y ∈ P, herm σ u y ≠ 0 := by
        by_contra! hcon
        exact hz (hP u hu hcon)
      have hy₁P : (herm σ u y)⁻¹ • y ∈ P := P.smul_mem _ hyP
      have huy₁ : herm σ u ((herm σ u y)⁻¹ • y) = 1 := by
        rw [herm_smul_right, inv_mul_cancel₀ hy]
      obtain ⟨t, ht⟩ := exists_isotropize hσ hu0 huy₁
      have hfP : (herm σ u y)⁻¹ • y + t • u ∈ P := P.add_mem hy₁P (P.smul_mem _ hu)
      generalize hf : (herm σ u y)⁻¹ • y + t • u = f at ht hfP
      have huf : herm σ u f = 1 := by
        rw [← hf, herm_add_right, huy₁, herm_smul_right, hu0, mul_zero, add_zero]
      have hfu : herm σ f u = 1 := by rw [herm_conj σ hσ.invol u f, huf, map_one]
      have hHnd : Nondeg σ (K ∙ u ⊔ K ∙ f) := by
        intro s hs hs'
        obtain ⟨u', hu', w, hw, rfl⟩ := Submodule.mem_sup.mp hs
        obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hu'
        obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hw
        have h1 := hs' f (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f))
        have h2 := hs' u (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
        simp only [herm_add_left, herm_smul_left, huf, ht, hu0, hfu, mul_one, mul_zero, add_zero,
          zero_add] at h1 h2
        rw [(map_eq_zero_iff σ σ.injective).mp h1, (map_eq_zero_iff σ σ.injective).mp h2,
          zero_smul, zero_smul, add_zero]
      have hHP : K ∙ u ⊔ K ∙ f ≤ P :=
        sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)
          ((Submodule.span_singleton_le_iff_mem _ _).mpr hfP)
      have hPH : Nondeg σ (P ⊓ perp σ (K ∙ u ⊔ K ∙ f)) := Nondeg.inf_perp hσ hP hHnd hHP
      have hdim := finrank_eq_add_finrank_inf_perp hσ hHnd hHP
      have hH2 : finrank K ↥(K ∙ u ⊔ K ∙ f) ≤ 2 := by
        have h1 : finrank K ↥(K ∙ u ⊔ K ∙ f) ≤ finrank K ↥(K ∙ u) + finrank K ↥(K ∙ f) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
        have h3 := finrank_span_singleton_le_one (K := K) u
        have h4 := finrank_span_singleton_le_one (K := K) f
        omega
      obtain ⟨v, hv, hvv⟩ := exists_aniso_of_nondeg hσ hPH (fun h => by
        rw [h, finrank_bot] at hdim
        omega)
      refine ⟨v, hv.1, hvv, ?_⟩
      have hvu : herm σ v u = 0 :=
        hv.2 u (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
      exact (herm_eq_zero_iff hσ v u).mp hvu
  ·
    have hS := Nondeg.inf_perp_span_singleton hσ hu hu0 hP
    have hdim := finrank_eq_inf_perp_add_one hσ hu hu0
    obtain ⟨v, hv, hvv⟩ := exists_aniso_of_nondeg hσ hS (fun h => by
      rw [h, finrank_bot] at hdim
      omega)
    refine ⟨v, hv.1, hvv, ?_⟩
    have hvu : herm σ v u = 0 := mem_perp_span_singleton.mp hv.2
    exact (herm_eq_zero_iff hσ v u).mp hvu

end Aniso

section Indep

@[expose] def gramMap (σ : K ≃+* K) (x : Fin 4 → Fin m → K) : (Fin m → K) →ₗ[K] (Fin 4 → K) where
  toFun e i := herm σ (x i) e
  map_add' e e' := by ext i; simp [herm_add_right]
  map_smul' c e := by ext i; simp [herm_smul_right]

theorem gramMap_apply (x : Fin 4 → Fin m → K) (e : Fin m → K) (i : Fin 4) :
    gramMap σ x e i = herm σ (x i) e := rfl

theorem herm_sum_left (c : Fin 4 → K) (x : Fin 4 → Fin m → K) (e : Fin m → K) :
    herm σ (∑ i, c i • x i) e = ∑ i, σ (c i) * herm σ (x i) e := by
  simp [Fin.sum_univ_four, herm_add_left, herm_smul_left]

theorem gramMap_surj {W : Submodule K (Fin m → K)}
    (hW : Nondeg σ W) {x : Fin 4 → Fin m → K} (hxW : ∀ i, x i ∈ W)
    (hli : LinearIndependent K x) (z : Fin 4 → K) : ∃ e ∈ W, gramMap σ x e = z := by
  have hrange : LinearMap.range ((gramMap σ x).domRestrict W) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set lam : Fin 4 → K := fun i => f (fun j => if i = j then 1 else 0) with hlam
    have hfz : ∀ w : Fin 4 → K, f w = ∑ i, w i * lam i := by
      intro w
      have := LinearMap.pi_apply_eq_sum_univ f w
      simpa [hlam, smul_eq_mul] using this
    set y : Fin m → K := ∑ i, σ.symm (lam i) • x i with hy
    have hyW : y ∈ W := Submodule.sum_mem _ fun i _ => W.smul_mem _ (hxW i)
    have hy0 : ∀ e ∈ W, herm σ y e = 0 := by
      intro e he
      have h1 : f (gramMap σ x e) = 0 := hfle ⟨⟨e, he⟩, rfl⟩
      rw [hfz] at h1
      rw [hy, herm_sum_left]
      simpa [gramMap_apply, mul_comm] using h1
    have hyz : y = 0 := hW y hyW hy0
    have hco : ∀ i, σ.symm (lam i) = 0 := Fintype.linearIndependent_iff.1 hli _ hyz
    apply hf0
    refine LinearMap.ext fun w => ?_
    rw [hfz]
    have : ∀ i, lam i = 0 := fun i => (map_eq_zero_iff σ.symm σ.symm.injective).1 (hco i)
    simp [this]
  obtain ⟨⟨e, he⟩, hez⟩ : z ∈ LinearMap.range ((gramMap σ x).domRestrict W) :=
    hrange ▸ Submodule.mem_top
  exact ⟨e, he, hez⟩

theorem exists_common_of_linearIndependent (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0)
    {W : Submodule K (Fin m → K)} (hW : Nondeg σ W) (h5 : 5 ≤ finrank K W)
    {x : Fin 4 → Fin m → K} (hxW : ∀ i, x i ∈ W) (hxn : ∀ i, herm σ (x i) (x i) ≠ 0)
    (hli : LinearIndependent K x) :
    ∃ e ∈ W, herm σ e e ≠ 0 ∧ ∀ i, herm σ (x i) (x i) * herm σ e e -
      herm σ (x i) e * herm σ e (x i) ≠ 0 := by
  classical
  set Φ := gramMap σ x with hΦ
  set T : Submodule K (Fin m → K) := W ⊓ LinearMap.ker Φ with hT
  have hker : ∀ {v : Fin m → K}, v ∈ T → ∀ i, herm σ (x i) v = 0 := fun {v} hv i =>
    congrFun (LinearMap.mem_ker.1 hv.2) i
  by_cases hT1 : ∃ v ∈ T, herm σ v v ≠ 0
  · obtain ⟨v, hvT, hv⟩ := hT1
    refine ⟨v, hvT.1, hv, fun i => ?_⟩
    rw [hker hvT i, zero_mul, sub_zero]
    exact mul_ne_zero (hxn i) hv
  have hT1' : ∀ v ∈ T, herm σ v v = 0 := fun v hv => by
    by_contra h
    exact hT1 ⟨v, hv, h⟩
  have hTT : ∀ s ∈ T, ∀ t ∈ T, herm σ s t = 0 := fun s hs t ht =>
    herm_eq_zero_of_forall_isotropic hσ hT1' hs ht
  obtain ⟨k₁, hk₁T, hk₁0⟩ : ∃ k ∈ T, k ≠ 0 := by
    have hrange : LinearMap.range (Φ.domRestrict W) = ⊤ := by
      refine LinearMap.range_eq_top.2 fun z => ?_
      obtain ⟨e, he, hz⟩ := gramMap_surj hW hxW hli z
      exact ⟨⟨e, he⟩, hz⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker (Φ.domRestrict W)
    rw [hrange, finrank_top] at hrn
    simp only [Module.finrank_fin_fun] at hrn
    have hk : 0 < finrank K ↥(LinearMap.ker (Φ.domRestrict W)) := by omega
    obtain ⟨⟨⟨k, hkW⟩, hkker⟩, hk0⟩ :=
      (Module.finrank_pos_iff_exists_ne_zero (R := K)
        (M := ↥(LinearMap.ker (Φ.domRestrict W)))).1 hk
    refine ⟨k, ⟨hkW, ?_⟩, fun h => hk0 ?_⟩
    · exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 hkker)
    · exact Subtype.ext (Subtype.ext h)
  set U : Submodule K (Fin m → K) := W ⊓ perp σ T with hU
  have hTU : ∀ s ∈ T, s ∈ perp σ T := fun s hs t ht => hTT s hs t ht
  have hex : ∃ i₀ : Fin 4, (fun j => if i₀ = j then (1 : K) else 0) ∉ U.map Φ := by
    by_contra! hall
    have htop : U.map Φ = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [pi_eq_sum_univ z]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hall i)
    have hWU : ∀ w ∈ W, w ∈ perp σ T := by
      intro w hw
      obtain ⟨u, hu, hΦu⟩ : Φ w ∈ U.map Φ := htop ▸ Submodule.mem_top
      have hwu : w - u ∈ T := ⟨W.sub_mem hw hu.1, LinearMap.mem_ker.2 (by
        rw [map_sub, hΦu, sub_self])⟩
      have := (perp σ T).add_mem hu.2 (hTU _ hwu)
      simpa using this
    refine hk₁0 (hW k₁ hk₁T.1 fun w hw => ?_)
    exact (herm_eq_zero_iff hσ _ _).2 (hWU w hw k₁ hk₁T)
  obtain ⟨i₀, hi₀⟩ := hex
  set ei₀ : Fin 4 → K := fun j => if i₀ = j then 1 else 0 with hei₀
  obtain ⟨e₀, he₀W, he₀Φ⟩ := gramMap_surj hW hxW hli ei₀
  obtain ⟨k₀, hk₀T, hk₀⟩ : ∃ k₀ ∈ T, herm σ e₀ k₀ ≠ 0 := by
    by_contra! hcon
    exact hi₀ ⟨e₀, ⟨he₀W, hcon⟩, he₀Φ⟩
  set n₁ := herm σ (x i₀) (x i₀) with hn₁
  set t : K := -n₁⁻¹ with ht
  have hσn₁ : σ n₁ = n₁ := herm_self_fixed σ hσ.invol _
  have hσt : σ t = t := by rw [ht, map_neg, map_inv₀, hσn₁]
  have ht0 : t ≠ 0 := neg_ne_zero.2 (inv_ne_zero (hxn i₀))
  set n₀ := herm σ e₀ e₀ with hn₀
  have hσn₀ : σ n₀ = n₀ := herm_self_fixed σ hσ.invol _
  obtain ⟨c, hc⟩ := hσ.trace_surj (t - n₀) (by rw [map_sub, hσt, hσn₀])
  set k : Fin m → K := (c / herm σ e₀ k₀) • k₀ with hk
  have hkT : k ∈ T := T.smul_mem _ hk₀T
  have hek : herm σ e₀ k = c := by
    rw [hk, herm_smul_right]
    field_simp
  have hee : herm σ (e₀ + k) (e₀ + k) = t := by
    simp only [herm_add_left, herm_add_right]
    rw [hek, herm_conj σ hσ.invol e₀ k, hek, hT1' k hkT]
    linear_combination hc
  have hΦe : ∀ i, herm σ (x i) (e₀ + k) = if i₀ = i then 1 else 0 := by
    intro i
    rw [herm_add_right, hker hkT i, add_zero]
    exact congrFun he₀Φ i
  refine ⟨e₀ + k, W.add_mem he₀W hkT.1, by rw [hee]; exact ht0, fun i => ?_⟩
  rw [hee, herm_conj σ hσ.invol (x i) (e₀ + k), hΦe i]
  by_cases hi : i₀ = i
  · subst hi
    simp only [↓reduceIte, map_one, mul_one]
    rw [ht, ← hn₁, mul_neg, mul_inv_cancel₀ (hxn i₀)]
    intro h
    apply h2
    linear_combination -h
  · simp only [hi, ↓reduceIte, map_zero, mul_zero, sub_zero]
    exact mul_ne_zero (hxn i) ht0

end Indep

section Dependent

theorem exists_orth_of_dependent (hσ : IsUnitaryInvolution σ) {W : Submodule K (Fin m → K)}
    (hW : Nondeg σ W) (h5 : 5 ≤ finrank K W) {x : Fin 4 → Fin m → K}
    (hxW : ∀ i, x i ∈ W) (hL : Nondeg σ (K ∙ x 0 ⊔ K ∙ x 1))
    (hL2 : finrank K ↥(K ∙ x 0 ⊔ K ∙ x 1) = 2) (hdep : ¬ LinearIndependent K x) :
    ∃ v ∈ W, herm σ v v ≠ 0 ∧ ∀ i, herm σ (x i) v = 0 := by
  classical
  set L : Submodule K (Fin m → K) := K ∙ x 0 ⊔ K ∙ x 1 with hLdef
  set S : Submodule K (Fin m → K) := Submodule.span K (Set.range x) with hSdef
  have hxS : ∀ i, x i ∈ S := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hSW : S ≤ W := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hxW i)
  have hLS : L ≤ S := sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (hxS 0))
    ((Submodule.span_singleton_le_iff_mem _ _).2 (hxS 1))
  have hLW : L ≤ W := hLS.trans hSW
  have hS3 : finrank K S ≤ 3 := by
    have hle : finrank K S ≤ 4 := by
      have h := finrank_range_le_card (R := K) x
      rwa [Fintype.card_fin] at h
    by_contra h4
    refine hdep (linearIndependent_iff_card_eq_finrank_span.2 ?_)
    have : finrank K S = 4 := by omega
    simpa [Set.finrank] using this.symm
  have hP : Nondeg σ (W ⊓ perp σ L) := Nondeg.inf_perp hσ hW hL hLW
  have hPdim := finrank_eq_add_finrank_inf_perp hσ hL hLW
  have hSdim := finrank_eq_add_finrank_inf_perp hσ hL hLS
  obtain ⟨u, hu⟩ := finrank_le_one_iff.1 (show finrank K ↥(S ⊓ perp σ L) ≤ 1 by omega)
  have huP : u.1 ∈ W ⊓ perp σ L := ⟨hSW u.2.1, u.2.2⟩
  obtain ⟨v, hvP, hv, huv⟩ := exists_aniso_orth hσ hP (by omega) huP
  refine ⟨v, hvP.1, hv, fun i => ?_⟩
  have hxi : x i ∈ L ⊔ (S ⊓ perp σ L) := by
    rw [sup_inf_perp_of_nondeg hσ 2 hL2 hL hLS]
    exact hxS i
  obtain ⟨l, hl, s, hs, hls⟩ := Submodule.mem_sup.1 hxi
  obtain ⟨c, hc⟩ := hu ⟨s, hs⟩
  have hsu : s = c • u.1 := by simpa using (congrArg Subtype.val hc).symm
  rw [← hls, herm_add_left, hsu, herm_smul_left, huv, mul_zero, add_zero]
  exact (herm_eq_zero_iff hσ _ _).2 (hvP.2 l hl)

end Dependent

section Main

variable {W : Submodule K (Fin m → K)}

theorem commonNeighbour4_collGraph3 (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0)
    (hW : Nondeg σ W) (h5 : 5 ≤ finrank K W) : CommonNeighbour4 (G := collGraph σ W) := by
  classical
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hab hbc hcd hda
  obtain ⟨xa, hxa, hxaW, rfl⟩ := mem_nsPts_iff.1 ha
  obtain ⟨xb, hxb, hxbW, rfl⟩ := mem_nsPts_iff.1 hb
  obtain ⟨xc, hxc, hxcW, rfl⟩ := mem_nsPts_iff.1 hc
  obtain ⟨xd, hxd, hxdW, rfl⟩ := mem_nsPts_iff.1 hd
  set x : Fin 4 → Fin m → K := ![xa, xb, xc, xd] with hx
  have hxW : ∀ i, x i ∈ W := by
    intro i
    fin_cases i <;> assumption
  have hxn : ∀ i, herm σ (x i) (x i) ≠ 0 := by
    intro i
    fin_cases i <;> assumption
  suffices H : ∃ e ∈ W, herm σ e e ≠ 0 ∧ ∀ i, IsCollinear σ (K ∙ x i) (K ∙ e) by
    obtain ⟨e, heW, he, hcol⟩ := H
    exact ⟨⟨K ∙ e, span_singleton_mem_nsPts he heW⟩, hcol 0, hcol 1, hcol 2, hcol 3⟩
  by_cases hli : LinearIndependent K x
  · obtain ⟨e, heW, he, hΔ⟩ := exists_common_of_linearIndependent hσ h2 hW h5 hxW hxn hli
    exact ⟨e, heW, he, fun i => (isCollinear_span_iff hσ (hxn i) he).2 (hΔ i)⟩
  · have hL2 : finrank K ↥(K ∙ x 0 ⊔ K ∙ x 1) = 2 :=
      finrank_sup_of_ne_pts (span_singleton_mem_nsPts hxa hxaW).2.1
        (span_singleton_mem_nsPts hxb hxbW).2.1 hab.1
    obtain ⟨v, hvW, hv, hvx⟩ := exists_orth_of_dependent hσ hW h5 hxW hab.2 hL2 hli
    exact ⟨v, hvW, hv, fun i => IsCollinear.of_orth hσ
      (span_singleton_mem_nsPts (hxn i) (hxW i)) (span_singleton_mem_nsPts hv hvW)
      (orth_span_singleton_iff.2 (hvx i))⟩

end Main

end CFSG.ClassicalInvolution.Phan.Q3G
