module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem sup_fix_pointwise {H K : Subgroup (V ≃ₗ[k] V)} {U : Submodule k V}
    (hH : ∀ x ∈ H, ∀ u ∈ U, x u = u) (hK : ∀ x ∈ K, ∀ u ∈ U, x u = u) :
    ∀ x ∈ H ⊔ K, ∀ u ∈ U, x u = u := by
  have : H ⊔ K ≤ centSub (MonoidHom.id (V ≃ₗ[k] V)) U :=
    sup_le (fun x hx u hu => hH x hx u hu) (fun x hx u hu => hK x hx u hu)
  exact fun x hx u hu => this hx u hu

theorem fix_iSup_of_fix {ι : Type*} {x : V ≃ₗ[k] V} {U : ι → Submodule k V}
    (h : ∀ i, ∀ w ∈ U i, x w = w) : ∀ w ∈ ⨆ i, U i, x w = w := by
  have h1 : (⨆ i, U i) ≤ LinearMap.eqLocus (x : V →ₗ[k] V) LinearMap.id :=
    iSup_le fun i w hw => h i w hw
  exact fun w hw => h1 hw

theorem commutator_mem_of_sup {X : Type*} [Group X] {L A : Subgroup X}
    (hAL : A ≤ Subgroup.normalizer (L : Set X)) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {x y : X} (hx : x ∈ L ⊔ A) (hy : y ∈ L ⊔ A) : ⁅x, y⁆ ∈ L := by
  obtain ⟨l, hl, a, ha, rfl⟩ := mem_sup_mul hAL hx
  obtain ⟨l', hl', a', ha', rfl⟩ := mem_sup_mul hAL hy
  have hc : a * a' = a' * a := hA a ha a' ha'
  have hc' : a' * a⁻¹ = a⁻¹ * a' := (Commute.inv_right (show Commute a' a from hc.symm)).eq
  have key : ⁅l * a, l' * a'⁆ = l * (a * l' * a⁻¹) * (a' * l⁻¹ * a'⁻¹) * l'⁻¹ := by
    rw [commutatorElement_def]
    calc l * a * (l' * a') * (l * a)⁻¹ * (l' * a')⁻¹
        = l * a * l' * (a' * a⁻¹) * l⁻¹ * a'⁻¹ * l'⁻¹ := by group
      _ = l * a * l' * (a⁻¹ * a') * l⁻¹ * a'⁻¹ * l'⁻¹ := by rw [hc']
      _ = l * (a * l' * a⁻¹) * (a' * l⁻¹ * a'⁻¹) * l'⁻¹ := by group
  rw [key]
  have h1 : a * l' * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hAL ha) l').1 hl'
  have h2 : a' * l⁻¹ * a'⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hAL ha') l⁻¹).1 (L.inv_mem hl)
  exact L.mul_mem (L.mul_mem (L.mul_mem hl h1) h2) (L.inv_mem hl')

namespace FamData

variable {N : Subgroup (V ≃ₗ[k] V)} {ι : Type*} {L : ι → Subgroup (V ≃ₗ[k] V)}
  (fd : FamData N L)

include fd

theorem ext_of_agree (f g : V →ₗ[k] V) (hI : ∀ i, ∀ w ∈ commGL (L i) ⊤, f w = g w)
    (hC : ∀ c ∈ fixGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)), f c = g c) : f = g := by
  have h1 : (⨆ i, commGL (L i) ⊤) ≤ LinearMap.eqLocus f g := iSup_le fun i w hw => hI i w hw
  have h2 : fixGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)) ≤ LinearMap.eqLocus f g :=
    fun c hc => hC c hc
  have h4 : commGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)) ⊤ ⊔
      fixGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)) = ⊤ := fd.compl.sup_eq_top
  rw [fd.W_eq] at h4
  have h3 : (⊤ : Submodule k V) ≤ LinearMap.eqLocus f g := by
    rw [← h4]
    exact sup_le h1 h2
  exact LinearMap.ext fun v => h3 Submodule.mem_top

theorem ext_of_agree' (x y : V ≃ₗ[k] V) (hI : ∀ i, ∀ w ∈ commGL (L i) ⊤, x w = y w)
    (hC : ∀ c ∈ fixGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)), x c = y c) : x = y :=
  LinearEquiv.ext fun v =>
    LinearMap.congr_fun (fd.ext_of_agree (x : V →ₗ[k] V) (y : V →ₗ[k] V) hI hC) v

variable {G A' : Subgroup (V ≃ₗ[k] V)} {i : ι}

theorem centralizes_of_planeData (pd : PlaneData G N A' (L i) (commGL (L i) ⊤)) {j : ι}
    (hji : j ≠ i) : ∀ a ∈ A', ∀ x ∈ L j, a * x = x * a := by
  intro a ha x hx
  have hx1 : x ∈ N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (commGL (L i) ⊤) :=
    ⟨fd.L_le j hx, fun v hv => fd.L_fix_I j i hji x hx v hv⟩
  rw [← pd.cent_eq] at hx1
  exact Subgroup.mem_centralizer_iff.1 hx1.2 a ha

theorem fix_of_planeData (pd : PlaneData G N A' (L i) (commGL (L i) ⊤)) :
    (∀ j, j ≠ i → ∀ w ∈ commGL (L j) ⊤, ∀ a ∈ A', a w = w) ∧
    (∀ c ∈ fixGL (⨆ j, L j : Subgroup (V ≃ₗ[k] V)), ∀ a ∈ A', a c = c) := by
  have hdisp : ∀ a ∈ A', ∀ v, a v - v ∈ commGL (L i) ⊤ := by
    intro a ha v
    have hv : v ∈ commGL (L i) ⊤ ⊔ fixGL A' := by
      rw [pd.V_eq]
      exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    have hac : a c = c := hc a ha
    have e : a (u + c) - (u + c) = a u - u := by
      rw [map_add, hac]
      abel
    rw [e]
    exact Submodule.sub_mem _ (pd.inv_A a ha u hu) hu
  have hfixI : ∀ j, j ≠ i → ∀ w ∈ commGL (L j) ⊤, ∀ a ∈ A', a w = w := by
    intro j hji w hw a ha
    have h1 : a w ∈ commGL (L j) ⊤ :=
      map_mem_commSub_top_of_commute (MonoidHom.id (V ≃ₗ[k] V)) (L j)
        (fun l hl => fd.centralizes_of_planeData pd hji a ha l hl) hw
    have h2 : a w - w ∈ commGL (L j) ⊤ := Submodule.sub_mem _ h1 hw
    have h3 := hdisp a ha w
    have hdis : Disjoint (commGL (L i) ⊤) (commGL (L j) ⊤) :=
      fd.I_indep.pairwiseDisjoint (Ne.symm hji)
    have h4 : a w - w = 0 := Submodule.disjoint_def.1 hdis _ h3 h2
    exact sub_eq_zero.1 h4
  refine ⟨hfixI, ?_⟩
  have hnorm : ∀ a ∈ A', ∀ d ∈ (⨆ j, L j : Subgroup (V ≃ₗ[k] V)),
      a * d * a⁻¹ ∈ (⨆ j, L j : Subgroup (V ≃ₗ[k] V)) := by
    intro a ha d hd
    refine Subgroup.iSup_induction L hd
      (C := fun d => a * d * a⁻¹ ∈ (⨆ j, L j : Subgroup (V ≃ₗ[k] V))) ?_ ?_ ?_
    · intro j x hx
      by_cases hji : j = i
      · subst hji
        have := (Subgroup.mem_normalizer_iff.1 (pd.A_norm ha) x).1 hx
        exact le_iSup L j this
      · have e : a * x * a⁻¹ = x := by
          rw [fd.centralizes_of_planeData pd hji a ha x hx]
          group
        rw [e]
        exact le_iSup L j hx
    · simp
    · intro x y hx hy
      have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
  have hfixc : ∀ a ∈ A', ∀ c ∈ fixGL (⨆ j, L j : Subgroup (V ≃ₗ[k] V)),
      a c ∈ fixGL (⨆ j, L j : Subgroup (V ≃ₗ[k] V)) := by
    intro a ha c hc d hd
    have h1 := hnorm a⁻¹ (A'.inv_mem ha) d hd
    rw [inv_inv] at h1
    have h2 : (a⁻¹ * d * a) c = c := hc _ h1
    have h3 : a⁻¹ (d (a c)) = c := h2
    calc d (a c) = a (a⁻¹ (d (a c))) := (gl_apply_inv a _).symm
      _ = a c := by rw [h3]
  intro c hc a ha
  have h1 : a c - c ∈ commGL (L i) ⊤ := hdisp a ha c
  have h2 : a c - c ∈ fixGL (⨆ j, L j : Subgroup (V ≃ₗ[k] V)) :=
    Submodule.sub_mem _ (hfixc a ha c hc) hc
  have h3 : commGL (L i) ⊤ ≤ commGL (⨆ j, L j : Subgroup (V ≃ₗ[k] V)) ⊤ := by
    rw [fd.W_eq]
    exact le_iSup (fun j => commGL (L j) ⊤) i
  have h4 : a c - c = 0 := Submodule.disjoint_def.1 fd.compl.disjoint _ (h3 h1) h2
  exact sub_eq_zero.1 h4

theorem fix_sup_I (pd : PlaneData G N A' (L i) (commGL (L i) ⊤)) {j : ι} (hji : j ≠ i) :
    ∀ x ∈ L i ⊔ A', ∀ w ∈ commGL (L j) ⊤, x w = w :=
  sup_fix_pointwise (fun x hx w hw => fd.L_fix_I i j (Ne.symm hji) x hx w hw)
    (fun a ha w hw => (fd.fix_of_planeData pd).1 j hji w hw a ha)

theorem fix_sup_C (pd : PlaneData G N A' (L i) (commGL (L i) ⊤)) :
    ∀ x ∈ L i ⊔ A', ∀ c ∈ fixGL (⨆ j, L j : Subgroup (V ≃ₗ[k] V)), x c = c :=
  sup_fix_pointwise (fun x hx c hc => fd.L_fix_C i x hx c hc)
    (fun a ha c hc => (fd.fix_of_planeData pd).2 c hc a ha)

theorem sup_le_of_planeData {A₁ A₂ : Subgroup (V ≃ₗ[k] V)}
    (pd₁ : PlaneData G N A₁ (L i) (commGL (L i) ⊤))
    (pd₂ : PlaneData G N A₂ (L i) (commGL (L i) ⊤)) : L i ⊔ A₁ ≤ L i ⊔ A₂ := by
  refine sup_le le_sup_left ?_
  intro a ha
  obtain ⟨hW₁, hb₁⟩ := pd₁.action
  obtain ⟨hW₂, hb₂⟩ := pd₂.action
  obtain ⟨s, hs⟩ := hb₂.2
    (resSub (MonoidHom.id (V ≃ₗ[k] V)) (L i ⊔ A₁) (commGL (L i) ⊤) hW₁ ⟨a, (le_sup_right : A₁ ≤ L i ⊔ A₁) ha⟩)
  have hsa : ∀ w ∈ commGL (L i) ⊤, (s : V ≃ₗ[k] V) w = a w := by
    intro w hw
    have e1 := resSub_apply (MonoidHom.id (V ≃ₗ[k] V)) (L i ⊔ A₂) (commGL (L i) ⊤) hW₂ s ⟨w, hw⟩
    rw [hs] at e1
    rw [resSub_apply] at e1
    exact e1.symm
  have hsub : (s : V ≃ₗ[k] V) = a := by
    refine fd.ext_of_agree' _ _ ?_ ?_
    · intro j w hw
      by_cases hji : j = i
      · subst hji
        exact hsa w hw
      · have e1 := fd.fix_sup_I pd₂ hji s s.2 w hw
        have e2 := (fd.fix_of_planeData pd₁).1 j hji w hw a ha
        rw [e1, e2]
    · intro c hc
      have e1 := fd.fix_sup_C pd₂ s s.2 c hc
      have e2 := (fd.fix_of_planeData pd₁).2 c hc a ha
      rw [e1, e2]
  rw [← hsub]
  exact s.2

theorem sup_eq_of_planeData {A₁ A₂ : Subgroup (V ≃ₗ[k] V)}
    (pd₁ : PlaneData G N A₁ (L i) (commGL (L i) ⊤))
    (pd₂ : PlaneData G N A₂ (L i) (commGL (L i) ⊤)) : L i ⊔ A₁ = L i ⊔ A₂ :=
  le_antisymm (fd.sup_le_of_planeData pd₁ pd₂) (fd.sup_le_of_planeData pd₂ pd₁)

theorem mul_comm_of_supports {i j : ι} (hij : i ≠ j) {x y : V ≃ₗ[k] V}
    (hxI : ∀ w ∈ commGL (L i) ⊤, x w ∈ commGL (L i) ⊤)
    (hyI : ∀ w ∈ commGL (L j) ⊤, y w ∈ commGL (L j) ⊤)
    (hxf : ∀ l, l ≠ i → ∀ w ∈ commGL (L l) ⊤, x w = w)
    (hyf : ∀ l, l ≠ j → ∀ w ∈ commGL (L l) ⊤, y w = w)
    (hxc : ∀ c ∈ fixGL (⨆ l, L l : Subgroup (V ≃ₗ[k] V)), x c = c)
    (hyc : ∀ c ∈ fixGL (⨆ l, L l : Subgroup (V ≃ₗ[k] V)), y c = c) : x * y = y * x := by
  refine fd.ext_of_agree' _ _ ?_ ?_
  · intro l w hw
    show x (y w) = y (x w)
    by_cases hli : l = i
    · subst hli
      rw [hyf l hij w hw, hyf l hij (x w) (hxI w hw)]
    · by_cases hlj : l = j
      · subst hlj
        rw [hxf l hli w hw, hxf l hli (y w) (hyI w hw)]
      · have e1 := hyf l hlj w hw
        have e2 := hxf l hli w hw
        rw [e1, e2, e1]
  · intro c hc
    show x (y c) = y (x c)
    rw [hyc c hc, hxc c hc, hyc c hc]

end FamData

end CFSG.QuasithinUnique.Setup.Layer
