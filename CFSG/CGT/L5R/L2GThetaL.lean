module

public import CFSG.CGT.L5R.L2GSwapL
public import CFSG.CGT.M24S.Type4
public import CFSG.CGT.T75JM.L2GTheta

public section

namespace CFSG.CGT.L5R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM

variable {G : Type} {H : Type*} [Group G] [Group H]

theorem exists_thetaL {T T₁ : Subgroup G} (h : TCtxL T T₁) (hnt : ¬ CFSG.CGT.M24S.HasType4 T)
    [Finite H] (M : T1ModelL H) (E : OntoEmb H (Subgroup.normalizer (T : Set G)))
    (hT : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) (hB : ∀ x, x ∈ M.B0 ↔ E.Φ x ∈ T₁) {g₀ : G}
    (hg1 : conjSubgroup g₀ T = T₁) (hg2 : conjSubgroup g₀ T₁ = T) :
    ∃ g : G, conjSubgroup g T = T₁ ∧ g * g = 1 ∧
      ∀ i, g * E.Φ (M.d i) * g⁻¹ = E.Φ (M.theta i) := by
  classical
  obtain ⟨s, hs⟩ := h.conj
  have hB0 : M.B0 = T₁.comap E.Φ := by
    ext x
    rw [hB x]
    rfl
  have hD : ∀ x : H, x ∈ Subgroup.normalizer (M.B0 : Set H) ↔
      E.Φ x ∈ Subgroup.normalizer (T₁ : Set G) := by
    intro x
    rw [hB0]
    exact h.mem_normalizer_comap_iff E x
  have hex : ∀ x ∈ Subgroup.normalizer (M.B0 : Set H),
      ∃ y : H, E.Φ y = g₀ * E.Φ x * g₀⁻¹ := by
    intro x hx
    exact E.surj _ (swap_mem_D hg1 hg2 (E.mem x) ((hD x).1 hx)).1
  let f : H → H := fun x => if hx : ∃ y : H, E.Φ y = g₀ * E.Φ x * g₀⁻¹ then Classical.choose hx
    else 1
  have hf : ∀ x ∈ Subgroup.normalizer (M.B0 : Set H), E.Φ (f x) = g₀ * E.Φ x * g₀⁻¹ := by
    intro x hx
    have hx' := hex x hx
    have := Classical.choose_spec hx'
    simpa only [f, hx', ↓reduceDIte] using this
  have hfD : ∀ x ∈ Subgroup.normalizer (M.B0 : Set H),
      f x ∈ Subgroup.normalizer (M.B0 : Set H) := by
    intro x hx
    rw [hD, hf x hx]
    exact (swap_mem_D hg1 hg2 (E.mem x) ((hD x).1 hx)).2
  have hfmul : ∀ x ∈ Subgroup.normalizer (M.B0 : Set H), ∀ y ∈ Subgroup.normalizer (M.B0 : Set H),
      f (x * y) = f x * f y := by
    intro x hx y hy
    apply E.inj
    rw [map_mul, hf x hx, hf y hy, hf (x * y) (Subgroup.mul_mem _ hx hy), map_mul]
    group
  have hfinj : ∀ x ∈ Subgroup.normalizer (M.B0 : Set H), ∀ y ∈ Subgroup.normalizer (M.B0 : Set H),
      f x = f y → x = y := by
    intro x hx y hy hxy
    apply E.inj
    have h1 := congrArg E.Φ hxy
    rw [hf x hx, hf y hy] at h1
    have h2 := congrArg (fun z => g₀⁻¹ * z * g₀) h1
    simpa [mul_assoc] using h2
  have hfA : ∀ a ∈ Subgroup.normalizer (M.B0 : Set H), a ∈ M.T0 → f a ∈ M.B0 := by
    intro a ha haT
    rw [hB, hf a ha]
    have hmem : E.Φ a ∈ normIn T T₁ := mem_normIn.2 ⟨(hT a).1 haT, (hD a).1 ha⟩
    exact (mem_normIn.1 (swap_mem_B hg1 hg2 hmem)).1
  have hfB : ∀ b ∈ M.B0, f b ∈ M.T0 := by
    intro b hb
    have hbD : b ∈ Subgroup.normalizer (M.B0 : Set H) := Subgroup.le_normalizer hb
    rw [hT, hf b hbD]
    have hmem : E.Φ b ∈ normIn T₁ T := mem_normIn.2 ⟨(hB b).1 hb, E.mem b⟩
    exact (mem_normIn.1 (swap_mem_A hg1 hg2 hmem)).1
  have hz1T : ∃ c : G, E.Φ M.z1 ∈ conjSubgroup c T := by
    obtain ⟨n, hn⟩ := M.z1_conj
    have h1 : E.Φ (n * M.z1 * n⁻¹) ∈ conjSubgroup s T := by rw [← hs]; exact (hB _).1 hn
    rw [map_mul, map_mul, map_inv] at h1
    have h2 := conj_mem_conjSubgroup h1 (E.Φ n)⁻¹
    refine ⟨(E.Φ n)⁻¹ * s, ?_⟩
    simpa [mul_assoc] using h2
  have hz1 : ∀ m : H, m * f M.z1 * m⁻¹ ∈ M.T0 ∨
      Nat.card ↥(M.T0 ⊓ Subgroup.centralizer ({m * f M.z1 * m⁻¹} : Set H)) ≠ 4 := by
    intro m
    by_cases hx : m * f M.z1 * m⁻¹ ∈ M.T0
    · exact Or.inl hx
    · right
      intro hc
      apply hnt
      obtain ⟨c, hc'⟩ := hz1T
      have hmem : E.Φ (m * f M.z1 * m⁻¹) ∈ conjSubgroup (E.Φ m * g₀ * c) T := by
        rw [map_mul, map_mul, map_inv, hf _ M.z1_mem]
        have := conj_mem_conjSubgroup (conj_mem_conjSubgroup hc' g₀) (E.Φ m)
        simpa [mul_assoc] using this
      exact ⟨_, _, E.mem _, fun hxT => hx ((hT _).2 hxT), hmem,
        by rw [← card_inf_centralizer_comap E hT, hc]⟩
  have hz2 : ∀ m n : H, n * M.b0 * n⁻¹ ≠ m * f M.z2 * m⁻¹ := by
    intro m n hmn
    apply hnt
    have hb0 : E.Φ M.b0 ∈ conjSubgroup s T := by rw [← hs]; exact (hB _).1 M.b0_mem
    have hfz2 : f M.z2 = (m⁻¹ * n) * M.b0 * (m⁻¹ * n)⁻¹ := by
      have : f M.z2 = m⁻¹ * (m * f M.z2 * m⁻¹) * m := by group
      rw [this, ← hmn]
      group
    have h1 : E.Φ (f M.z2) ∈ conjSubgroup (E.Φ (m⁻¹ * n) * s) T := by
      have e : E.Φ (f M.z2) = E.Φ (m⁻¹ * n) * E.Φ M.b0 * (E.Φ (m⁻¹ * n))⁻¹ := by
        rw [hfz2]
        simp only [map_mul, map_inv]
      rw [e]
      exact conj_mem_conjSubgroup hb0 _
    rw [hf _ M.z2_mem] at h1
    have h2 := conj_mem_conjSubgroup h1 g₀⁻¹
    have e1 : g₀⁻¹ * (g₀ * E.Φ M.z2 * g₀⁻¹) * g₀⁻¹⁻¹ = E.Φ M.z2 := by group
    rw [e1] at h2
    exact ⟨_, _, E.mem _, fun hxT => M.z2_notMem ((hT _).2 hxT), h2,
      by rw [← card_inf_centralizer_comap E hT, M.z2_card]⟩
  obtain ⟨e, he, hθ⟩ := M.swap f hfD hfmul hfinj hfA hfB hz1 hz2
  have hsurj : ∃ d ∈ Subgroup.normalizer (M.B0 : Set H), f d = e := by
    let F : ↥(Subgroup.normalizer (M.B0 : Set H)) → ↥(Subgroup.normalizer (M.B0 : Set H)) :=
      fun x => ⟨f x, hfD x x.2⟩
    have hFinj : Function.Injective F := fun x y hxy =>
      Subtype.ext (hfinj x x.2 y y.2 (congrArg Subtype.val hxy))
    obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hFinj ⟨e, he⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  obtain ⟨d, hdD, hde⟩ := hsurj
  set g : G := g₀ * E.Φ d with hg
  have hdN : E.Φ d ∈ Subgroup.normalizer (T : Set G) := E.mem d
  have hdN₁ : E.Φ d ∈ Subgroup.normalizer (T₁ : Set G) := (hD d).1 hdD
  have hdT : conjSubgroup (E.Φ d) T = T := mem_normalizer_iff_conjSubgroup_eq.1 hdN
  have hdT₁ : conjSubgroup (E.Φ d) T₁ = T₁ := mem_normalizer_iff_conjSubgroup_eq.1 hdN₁
  have hgT : conjSubgroup g T = T₁ := by
    rw [hg, ← conjSubgroup_conjSubgroup, hdT, hg1]
  have hgT₁ : conjSubgroup g T₁ = T := by
    rw [hg, ← conjSubgroup_conjSubgroup, hdT₁, hg2]
  have hrel : ∀ i, g * E.Φ (M.d i) * g⁻¹ = E.Φ (M.theta i) := by
    intro i
    have h1 := hθ i
    have hdi : M.d i ∈ Subgroup.normalizer (M.B0 : Set H) := M.d_mem i
    have h2 : f (d * M.d i * d⁻¹) = e * f (M.d i) * e⁻¹ := by
      rw [hfmul _ (Subgroup.mul_mem _ hdD hdi) _ (Subgroup.inv_mem _ hdD),
        hfmul _ hdD _ hdi, ← hde]
      have h3 : f d⁻¹ = (f d)⁻¹ := by
        have := hfmul d hdD d⁻¹ (Subgroup.inv_mem _ hdD)
        rw [mul_inv_cancel] at this
        have h1' : f 1 = 1 := by
          have := hfmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
          simpa using this
        rw [h1'] at this
        exact (eq_inv_of_mul_eq_one_right this.symm)
      rw [h3]
    have h4 := hf (d * M.d i * d⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hdD hdi)
      (Subgroup.inv_mem _ hdD))
    rw [h2, h1] at h4
    rw [h4, hg]
    simp only [map_mul, map_inv]
    group
  have hg2N : g * g ∈ Subgroup.normalizer (T : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← conjSubgroup_conjSubgroup, hgT, hgT₁]
  have hg2N₁ : g * g ∈ Subgroup.normalizer (T₁ : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← conjSubgroup_conjSubgroup, hgT₁, hgT]
  obtain ⟨z, hz⟩ := E.surj (g * g) hg2N
  have hzD : z ∈ Subgroup.normalizer (M.B0 : Set H) := (hD z).2 (hz ▸ hg2N₁)
  obtain ⟨w, hw⟩ := M.theta_sq
  have hconj : ∀ i, g * E.Φ (M.theta i) * g⁻¹ = E.Φ (M.d i) := by
    intro i
    have e1 : E.Φ (M.theta i) = FreeGroup.lift (fun j => E.Φ (M.d j)) (FreeGroup.mk (w i)) := by
      rw [← map_lift_eq, (hw i).1]
    have e2 : g * E.Φ (M.theta i) * g⁻¹ =
        FreeGroup.lift (fun j => g * E.Φ (M.d j) * g⁻¹) (FreeGroup.mk (w i)) := by
      have := map_lift_eq (MulAut.conj g).toMonoidHom (fun j => E.Φ (M.d j)) (FreeGroup.mk (w i))
      rw [e1]
      simpa [MulAut.conj_apply] using this
    rw [e2]
    simp only [hrel]
    rw [← map_lift_eq, (hw i).2]
  have hyc : ∀ i, z * M.d i = M.d i * z := by
    intro i
    apply E.inj
    simp only [map_mul, hz]
    calc g * g * E.Φ (M.d i) = g * (g * E.Φ (M.d i) * g⁻¹) * g := by group
      _ = g * E.Φ (M.theta i) * g := by rw [hrel]
      _ = (g * E.Φ (M.theta i) * g⁻¹) * (g * g) := by group
      _ = E.Φ (M.d i) * (g * g) := by rw [hconj]
  have hz1' : z = 1 := M.center z hzD hyc
  refine ⟨g, hgT, ?_, hrel⟩
  rw [← hz, hz1', map_one]

theorem exists_configL {T T₁ : Subgroup G} (h : TCtxL T T₁) (hnt : ¬ CFSG.CGT.M24S.HasType4 T)
    [Finite H] (M : T1ModelL H) (E : OntoEmb H (Subgroup.normalizer (T : Set G)))
    (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) :
    ∃ (E' : OntoEmb H (Subgroup.normalizer (T : Set G))) (g : G),
      (∀ x, x ∈ M.T0 ↔ E'.Φ x ∈ T) ∧ conjSubgroup g T = T₁ ∧ g * g = 1 ∧
        ∀ i, g * E'.Φ (M.d i) * g⁻¹ = E'.Φ (M.theta i) := by
  obtain ⟨n, hn⟩ := exists_conjB h M hE
  set E' : OntoEmb H (Subgroup.normalizer (T : Set G)) := E.comp (MulAut.conj n) with hE'
  have hΦ : ∀ x, E'.Φ x = E.Φ (n * x * n⁻¹) := fun x => by
    simp [E', MulAut.conj_apply]
  have hT' : ∀ x, x ∈ M.T0 ↔ E'.Φ x ∈ T := by
    intro x
    rw [hΦ, map_mul, map_mul, map_inv, hE x]
    exact Subgroup.mem_normalizer_iff.1 (E.mem n) (E.Φ x)
  have hB' : ∀ x, x ∈ M.B0 ↔ E'.Φ x ∈ T₁ := fun x => by rw [hΦ]; exact hn x
  obtain ⟨g₀, hg1, hg2⟩ := exists_swapperL h M hE
  obtain ⟨g, hgT, hg, hrel⟩ := exists_thetaL h hnt M E' hT' hB' hg1 hg2
  exact ⟨E', g, hT', hgT, hg, hrel⟩

end CFSG.CGT.L5R
