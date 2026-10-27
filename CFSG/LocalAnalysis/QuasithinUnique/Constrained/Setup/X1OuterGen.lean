module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

section EvalG

theorem getD_map_one {G G' : Type*} [Group G] [Group G'] (f : G →* G') (S : List G) (i : ℕ) :
    (S.map f).getD i 1 = f (S.getD i 1) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases S[i]? <;> simp

theorem evalG_map {G G' : Type*} [Group G] [Group G'] (f : G →* G') (S : List G) :
    ∀ w : List ℤ, f (evalG S w) = evalG (S.map f) w
  | [] => by simp [evalG]
  | z :: w => by
    rw [evalG, evalG, map_mul, evalG_map f S w, getD_map_one, getD_map_one]
    split_ifs <;> simp

theorem evalG_mem {G : Type*} [Group G] (K : Subgroup G) {S : List G} (hS : ∀ g ∈ S, g ∈ K) :
    ∀ w : List ℤ, evalG S w ∈ K
  | [] => K.one_mem
  | z :: w => by
    have hget : ∀ k, S.getD k 1 ∈ K := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases h : S[k]? with
      | none => exact K.one_mem
      | some g => exact hS g (List.mem_of_getElem? h)
    rw [evalG]
    refine K.mul_mem ?_ (evalG_mem K hS w)
    split_ifs
    · exact hget _
    · exact K.inv_mem (hget _)

end EvalG

section OuterGen

variable {M : Type*} [Group M]

theorem exists_list_sub (N : Subgroup M) :
    ∀ ks : List M, (∀ x ∈ ks, x ∈ N) → ∃ ksN : List N, ksN.map Subtype.val = ks := by
  intro ks
  induction ks with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons x ks ih =>
    intro h
    obtain ⟨ksN, hks⟩ := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    exact ⟨⟨x, h x List.mem_cons_self⟩ :: ksN, by simp [hks]⟩

theorem hrepGen_of_cover (N : Subgroup M) {δ : M} {p k : ℕ} (reps : List M)
    (hcover : ∀ u : M, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ N, u = c * r * c⁻¹)
    (hreps : ∀ r ∈ reps, ∃ ks : List M, ks.length = k ∧ (∀ x ∈ ks, x ∈ N) ∧
      ∃ w : List ℤ, orderOf (evalG (ks.map fun x => r * (x * r * x⁻¹)) w) = p) :
    ∀ u : M, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ ks : List M, ks.length = k ∧ (∀ x ∈ ks, x ∈ N) ∧
      ∃ w : List ℤ, orderOf (evalG (ks.map fun x => u * (x * u * x⁻¹)) w) = p := by
  intro u hu hord
  obtain ⟨r, hr, c, hc, rfl⟩ := hcover u hu hord
  obtain ⟨ks, hlen, hkN, w, hp⟩ := hreps r hr
  refine ⟨ks.map fun x => c * x * c⁻¹, by simpa using hlen, ?_, w, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact N.mul_mem (N.mul_mem hc (hkN y hy)) (N.inv_mem hc)
  · have h1 := evalG_map (MulAut.conj c).toMonoidHom (ks.map fun x => r * (x * r * x⁻¹)) w
    have h2 : (ks.map fun x => r * (x * r * x⁻¹)).map (MulAut.conj c).toMonoidHom =
        (ks.map fun x => c * x * c⁻¹).map fun x => c * r * c⁻¹ * (x * (c * r * c⁻¹) * x⁻¹) := by
      simp only [List.map_map]
      refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h2] at h1
    rw [← h1]
    have := MulEquiv.orderOf_eq (MulAut.conj c) (evalG (ks.map fun x => r * (x * r * x⁻¹)) w)
    simp only [MulAut.conj_apply] at this
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this, hp]

theorem outer_gen_of_delta (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) {p k : ℕ}
    (hrep : ∀ u : M, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ ks : List M, ks.length = k ∧
      (∀ x ∈ ks, x ∈ N) ∧ ∃ w : List ℤ,
        orderOf (evalG (ks.map fun x => u * (x * u * x⁻¹)) w) = p) :
    ∀ α : MulAut N, α * α = 1 → α ∉ inner N → ∃ cs : List (MulAut N), cs.length = k + 1 ∧
      (∀ c ∈ cs, c ∈ inner N) ∧ ∃ y ∈ Subgroup.closure (conjSet cs {α}), orderOf y = p := by
  intro α hα2 hα
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ with hu
  have huN : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, ?_⟩
    ext h
    rw [MonoidHom.map_one, MulAut.one_apply, hαg]
    simp [h1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨ks, hlen, hkN, w, hp⟩ := hrep u huN hord
  obtain ⟨ksN, hksN⟩ := exists_list_sub N ks hkN
  have hP : ∀ x : N, u * ((x : M) * u * (x : M)⁻¹) ∈ N := fun x => by
    have : u * ((x : M) * u * (x : M)⁻¹) =
        g * (δ * ((x : M) * g) * δ⁻¹) * (δ * δ) * (x : M)⁻¹ := by
      simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem (N.mul_mem hg (hδ _ (N.mul_mem x.2 hg))) hδ2) (N.inv_mem x.2)
  have hconj : ∀ x : N, α * (MulAut.conj x * α * (MulAut.conj x)⁻¹) =
      MulAut.conj (⟨u * ((x : M) * u * (x : M)⁻¹), hP x⟩ : N) := fun x => by
    ext h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    simp only [hαg, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  set Pl : List (MulAut N) := ksN.map fun x : N => α * (MulAut.conj x * α * (MulAut.conj x)⁻¹) with hPl
  set zl : List N := ksN.map fun x : N => (⟨u * ((x : M) * u * (x : M)⁻¹), hP x⟩ : N) with hzl
  have hPl' : Pl = zl.map (MulAut.conj : N →* MulAut N) := by
    simp only [hPl, hzl, List.map_map]
    exact List.map_congr_left fun x _ => hconj x
  refine ⟨1 :: ksN.map (fun x => (MulAut.conj : N →* MulAut N) x), by simpa [← hksN] using hlen, ?_,
    evalG Pl w, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Subgroup.one_mem _
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
      exact ⟨x, rfl⟩
  ·
    refine evalG_mem _ (fun a ha => ?_) w
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨1, by simp, α, rfl, by simp⟩)
      (Subgroup.subset_closure ⟨MulAut.conj x, ?_, α, rfl, rfl⟩)
    exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩)
  · have h1 : evalG Pl w = MulAut.conj (evalG zl w) := by
      rw [hPl', ← evalG_map]
    rw [h1, orderOf_injective (MulAut.conj : N →* MulAut N) (conj_injective_of_center N hcenter),
      ← Subgroup.orderOf_coe]
    have h2 := evalG_map N.subtype zl w
    have h3 : zl.map N.subtype = ks.map fun x => u * (x * u * x⁻¹) := by
      rw [← hksN]
      simp only [hzl, List.map_map]
      rfl
    rw [h3] at h2
    simp only [Subgroup.coe_subtype] at h2
    rw [h2]
    exact hp

end OuterGen

end CFSG.QuasithinUnique.Setup.X1
