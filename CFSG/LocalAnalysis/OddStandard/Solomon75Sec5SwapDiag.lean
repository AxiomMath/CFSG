module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix

public section

namespace CFSG.OddStandard.Solomon75

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.Sol76

open scoped commutatorElement

section Perfect

variable {W : Type*} [Group W]

omit [Group W] in
theorem commutator_eq_self_of_quasisimple {W : Type*} [Group W] {K : Subgroup W}
    (hq : IsQuasisimple ↥K) : ⁅K, K⁆ = K := by
  have h1 : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h2 : commutator ↥K = ⊤ := hq.1.commutator_eq_top
  rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1.symm

theorem commute_of_central_comm {K : Subgroup W} {g : W} (hK : ⁅K, K⁆ = K)
    (hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (he : ∀ k ∈ K, ∀ x ∈ K, Commute x (k⁻¹ * (g * k * g⁻¹))) : ∀ k ∈ K, Commute g k := by
  have hcomm : ⁅K, K⁆ ≤ K ⊓ centralizer ({g} : Set W) := by
    refine commutator_le.mpr fun a ha b hb => mem_inf.mpr ⟨?_, ?_⟩
    · exact commutator_mem_commutator ha hb |> fun h => (commutator_le_self K h : _)
    rw [mem_centralizer_singleton_iff]
    set ea := a⁻¹ * (g * a * g⁻¹) with hea
    set eb := b⁻¹ * (g * b * g⁻¹) with heb
    have hga : g * a * g⁻¹ = a * ea := by rw [hea]; group
    have hgb : g * b * g⁻¹ = b * eb := by rw [heb]; group
    have h1 : b * ea = ea * b := (he a ha b hb).eq
    have hebK : eb ∈ K := mul_mem (inv_mem hb) (hgK b hb)
    have h2 : eb * ea = ea * eb := (he a ha eb hebK).eq
    have h3 : a⁻¹ * eb = eb * a⁻¹ := (he b hb a⁻¹ (inv_mem ha)).eq
    have key : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
      rw [commutatorElement_def]
      calc g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ =
          (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
        _ = a * ea * (b * eb) * (a * ea)⁻¹ * (b * eb)⁻¹ := by rw [hga, hgb]
        _ = a * (ea * b) * eb * ea⁻¹ * a⁻¹ * eb⁻¹ * b⁻¹ := by group
        _ = a * (b * ea) * eb * ea⁻¹ * a⁻¹ * eb⁻¹ * b⁻¹ := by rw [h1]
        _ = a * b * (ea * eb) * ea⁻¹ * a⁻¹ * eb⁻¹ * b⁻¹ := by group
        _ = a * b * (eb * ea) * ea⁻¹ * a⁻¹ * eb⁻¹ * b⁻¹ := by rw [h2]
        _ = a * b * (eb * a⁻¹) * eb⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * eb) * eb⁻¹ * b⁻¹ := by rw [h3]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    calc ⁅a, b⁆ * g = (g * ⁅a, b⁆ * g⁻¹) * g := by rw [key]
      _ = g * ⁅a, b⁆ := by group
  intro k hk
  rw [← hK] at hk
  exact (mem_centralizer_singleton_iff.mp (mem_inf.mp (hcomm hk)).2).symm

end Perfect

section Diag

variable {W : Type*} [Group W] [Finite W]

theorem centralizes_of_comm_diag {K : Subgroup W} (hK : IsComponent K) {g j : W}
    (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) (hjK : ∀ k ∈ K, j * k * j⁻¹ ∈ K)
    (hjg : Commute j g) (hjD : ∀ v ∈ K, Commute j (v * (g * v * g⁻¹))) :
    ∀ k ∈ K, Commute j k := by
  set K' : Subgroup W := K.map (MulAut.conj g).toMonoidHom with hK'
  have hK'c : IsComponent K' := isComponent_map_mulEquiv (MulAut.conj g) hK
  have hKK' : K ≠ K' := fun h => hne h.symm
  have he : ∀ k ∈ K, ∀ x ∈ K, Commute x (k⁻¹ * (j * k * j⁻¹)) := by
    intro v hv x hx
    set v' : W := j * v * j⁻¹ with hv'
    have hv'K : v' ∈ K := hjK v hv
    have e1 : g * j = j * g := hjg.eq.symm
    have h1 : g * v' * g⁻¹ = j * (g * v * g⁻¹) * j⁻¹ := by
      rw [hv']
      calc g * (j * v * j⁻¹) * g⁻¹ = (g * j) * v * (g * j)⁻¹ := by group
        _ = (j * g) * v * (j * g)⁻¹ := by rw [e1]
        _ = j * (g * v * g⁻¹) * j⁻¹ := by group
    have h2 : v' * (g * v' * g⁻¹) = v * (g * v * g⁻¹) := by
      have h3 : j * (v * (g * v * g⁻¹)) * j⁻¹ = v * (g * v * g⁻¹) := by
        have := (hjD v hv).eq
        calc j * (v * (g * v * g⁻¹)) * j⁻¹ = (v * (g * v * g⁻¹)) * j * j⁻¹ := by rw [this]
          _ = v * (g * v * g⁻¹) := by group
      calc v' * (g * v' * g⁻¹) = j * v * j⁻¹ * (j * (g * v * g⁻¹) * j⁻¹) := by rw [hv', h1]
        _ = j * (v * (g * v * g⁻¹)) * j⁻¹ := by group
        _ = v * (g * v * g⁻¹) := h3
    have h4 : v⁻¹ * v' = (g * v * g⁻¹) * (g * v' * g⁻¹)⁻¹ := by
      have : v⁻¹ * v' * (g * v' * g⁻¹) = g * v * g⁻¹ := by
        calc v⁻¹ * v' * (g * v' * g⁻¹) = v⁻¹ * (v' * (g * v' * g⁻¹)) := by group
          _ = v⁻¹ * (v * (g * v * g⁻¹)) := by rw [h2]
          _ = g * v * g⁻¹ := by group
      calc v⁻¹ * v' = v⁻¹ * v' * (g * v' * g⁻¹) * (g * v' * g⁻¹)⁻¹ := by group
        _ = (g * v * g⁻¹) * (g * v' * g⁻¹)⁻¹ := by rw [this]
    have heK' : v⁻¹ * v' ∈ K' := by
      rw [h4]
      exact mul_mem (conj_mem_map_conj hv) (inv_mem (conj_mem_map_conj hv'K))
    exact commute_of_ne hK hK'c hKK' hx heK'
  exact commute_of_central_comm (commutator_eq_self_of_quasisimple hK.1) hjK he

theorem diag_isComponent {K : Subgroup W} (hK : IsComponent K) {g : W} (hg2 : g * g = 1)
    (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) :
    ∃ (D : Subgroup W) (δ : ↥K →* ↥D), IsQuasisimple ↥D ∧ D ≤ centralizer ({g} : Set W) ∧
      (D.subgroupOf (centralizer ({g} : Set W))).IsSubnormal ∧ D ≤ layer W ∧
      Function.Surjective δ ∧ ∀ v : ↥K, ((δ v : ↥D) : W) = (v : W) * (g * v * g⁻¹) := by
  set C := centralizer ({g} : Set W) with hC
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  have hK'c : IsComponent K' := isComponent_map_mulEquiv (MulAut.conj g) hK
  have hne' : K ≠ K' := fun h => hne h.symm
  have hcK : ∀ v ∈ K, ∀ w ∈ K, Commute w (g * v * g⁻¹) := fun v hv w hw =>
    commute_of_ne hK hK'c hne' hw (conj_mem_map_conj hv)
  let δ : ↥K →* W :=
    { toFun := fun v => (v : W) * (g * v * g⁻¹)
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [coe_mul]
        have h := (hcK v v.2 w w.2).eq
        calc (v : W) * w * (g * (v * w) * g⁻¹) = v * (w * (g * v * g⁻¹)) * (g * w * g⁻¹) := by
              group
          _ = v * ((g * v * g⁻¹) * w) * (g * w * g⁻¹) := by rw [h]
          _ = v * (g * v * g⁻¹) * (w * (g * w * g⁻¹)) := by group }
  have hδ : ∀ v : ↥K, δ v = (v : W) * (g * v * g⁻¹) := fun _ => rfl
  have hKE : K ≤ layer W := component_le_layer hK
  have hK'E : K' ≤ layer W := component_le_layer hK'c
  have hq : IsQuasisimple δ.range := by
    have htop : IsQuasisimple ↥(⊤ : Subgroup ↥K) :=
      isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hK.1
    have hker : ¬ (⊤ : Subgroup ↥K) ≤ δ.ker := by
      intro h
      have hKK' : ∀ v ∈ K, v ∈ K' := by
        intro v hv
        have h1 : δ ⟨v, hv⟩ = 1 := h (mem_top _)
        rw [hδ] at h1
        have e : v = (g * v * g⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [e]
        exact inv_mem (conj_mem_map_conj hv)
      obtain ⟨a, b, hab⟩ := hK.1.2.2
      induction a using QuotientGroup.induction_on with
      | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (commute_of_ne hK hK'c hne' a.2 (hKK' b b.2)).eq
    have := isQuasisimple_map htop δ hker
    rwa [← MonoidHom.range_eq_map] at this
  have hδC : δ.range ≤ C := by
    rintro _ ⟨v, rfl⟩
    rw [hδ, hC, mem_centralizer_singleton_iff]
    have h3 := (hcK v v.2 v v.2).eq
    have key : g * ((v : W) * (g * v * g⁻¹)) * g⁻¹ = (v : W) * (g * v * g⁻¹) := by
      calc g * ((v : W) * (g * v * g⁻¹)) * g⁻¹ =
          (g * v * g⁻¹) * (g * g * v * (g * g)⁻¹) := by group
        _ = (g * v * g⁻¹) * (v * (g * g) * (g * g)⁻¹) := by
          rw [hg2]; simp
        _ = (g * v * g⁻¹) * v := by group
        _ = (v : W) * (g * v * g⁻¹) := h3.symm
    calc (v : W) * (g * v * g⁻¹) * g = g * ((v : W) * (g * v * g⁻¹)) * g⁻¹ * g := by
          rw [key]
      _ = g * ((v : W) * (g * v * g⁻¹)) := by group
  have hδE : δ.range ≤ layer W := by
    rintro _ ⟨v, rfl⟩
    exact mul_mem (hKE v.2) (hK'E (conj_mem_map_conj v.2))
  have : (layer W).Characteristic := layer_characteristic
  have : (layer W).Normal := inferInstance
  have hDn : layer W ⊓ C ≤ normalizer (δ.range : Set W) := by
    refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
    obtain ⟨hcE, hcC⟩ := mem_inf.mp hc
    have hcg : c * g = g * c := mem_centralizer_singleton_iff.mp hcC
    obtain ⟨v, rfl⟩ := hx
    have hcv : c * v * c⁻¹ ∈ K := (mem_normalizer_iff.mp (layer_le_normalizer hK hcE) v).mp v.2
    refine ⟨⟨c * v * c⁻¹, hcv⟩, ?_⟩
    rw [hδ, hδ]
    have e : c * g = g * c := hcg
    calc c * v * c⁻¹ * (g * (c * v * c⁻¹) * g⁻¹) =
        c * v * c⁻¹ * (g * c) * v * (g * c)⁻¹ := by group
      _ = c * v * c⁻¹ * (c * g) * v * (c * g)⁻¹ := by rw [e]
      _ = c * ((v : W) * (g * v * g⁻¹)) * c⁻¹ := by group
  have hCn : C ≤ normalizer ((layer W ⊓ C : Subgroup W) : Set W) := by
    refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
    obtain ⟨hxE, hxC⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨Normal.conj_mem inferInstance x hxE c,
      mul_mem (mul_mem hc hxC) (inv_mem hc)⟩
  exact ⟨δ.range, δ.rangeRestrict, hq, hδC,
    isSubnormal_subgroupOf_of_le_normalizer (le_inf hδE hδC) inf_le_right hDn hCn, hδE,
    δ.rangeRestrict_surjective, fun v => rfl⟩

omit [Finite W] in
theorem not_commutative_of_quasisimple {K : Subgroup W} (hq : IsQuasisimple ↥K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : False := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hcomm a a.2 b b.2)

omit [Finite W] in
theorem map_conj_mul_eq_of_eq {K : Subgroup W} {g j : W} (hg2 : g * g = 1) (hjg : Commute j g)
    (h : K.map (MulAut.conj j).toMonoidHom = K.map (MulAut.conj g).toMonoidHom) :
    K.map (MulAut.conj (j * g)).toMonoidHom = K := by
  ext x
  rw [mem_map_conj_iff]
  have e1 : (j * g)⁻¹ * x * (j * g) = j⁻¹ * (g⁻¹ * x * g) * j := by
    have e : g * j = j * g := hjg.eq.symm
    calc (j * g)⁻¹ * x * (j * g) = g⁻¹ * j⁻¹ * x * (j * g) := by group
      _ = g⁻¹ * j⁻¹ * x * (g * j) := by rw [e]
      _ = j⁻¹ * (g⁻¹ * x * g) * j := by
        have e' : g⁻¹ * j⁻¹ = j⁻¹ * g⁻¹ := by
          have := congrArg (fun t => t⁻¹) e
          simpa using this.symm
        calc g⁻¹ * j⁻¹ * x * (g * j) = (g⁻¹ * j⁻¹) * x * (g * j) := by group
          _ = (j⁻¹ * g⁻¹) * x * (g * j) := by rw [e']
          _ = j⁻¹ * (g⁻¹ * x * g) * j := by group
  rw [e1]
  have hy : ∀ y : W, j⁻¹ * y * j ∈ K ↔ g⁻¹ * y * g ∈ K := fun y => by
    have h' : y ∈ K.map (MulAut.conj j).toMonoidHom ↔ y ∈ K.map (MulAut.conj g).toMonoidHom := by
      rw [h]
    rwa [mem_map_conj_iff, mem_map_conj_iff] at h'
  rw [hy (g⁻¹ * x * g)]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  rw [hginv]
  have : g * (g * x * g) * g = x := by
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg2]; simp
  rw [this]

end Diag

end CFSG.OddStandard.Solomon75
