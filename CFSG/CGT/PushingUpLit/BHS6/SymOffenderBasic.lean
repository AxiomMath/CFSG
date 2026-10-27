module

public import CFSG.CGT.PushingUpLit.BHS.AltCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6
open scoped commutatorElement

section Delta

variable {n : ℕ}

theorem vsum_pairVec_eq_self' (o : Fin n) (v : ↥(coreMod n)) :
    vsum (fun i => pairVec o i) v = v := by
  refine vcoord_ext fun q => ?_
  refine (vcoord_map_vsum (MonoidHom.id ↥(coreMod n)) (fun i => pairVec o i) v q).trans ?_
  show ∑ i, vcoord v i * vcoord (pairVec o i) q = vcoord v q
  simp only [vcoord_pairVec, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_vcoord, zero_mul, zero_add]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem mem_closure_pairVec' (hn : 0 < n) (v : ↥(coreMod n)) :
    v ∈ Subgroup.closure {x : ↥(coreMod n) | ∃ a b : Fin n, x = pairVec a b} := by
  rw [← vsum_pairVec_eq_self' ⟨0, hn⟩ v, vsum]
  refine Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _
  exact ⟨⟨0, hn⟩, i, rfl⟩

theorem eq_top_of_commutator_coreAct_alt (h3 : 3 ≤ n) (H : Subgroup ↥(coreMod n))
    (hH : ∀ σ ∈ alternatingGroup (Fin n), ∀ v : ↥(coreMod n), coreAct n σ v * v⁻¹ ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hpair : ∀ a b : Fin n, pairVec a b ∈ H := by
    intro a b
    by_cases hab : a = b
    · rw [hab, pairVec_self]
      exact H.one_mem
    · obtain ⟨k, hka, hkb⟩ := exists_ne_ne h3 a b
      have hσ : cyc a b k ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup]
        exact (cyc_isThreeCycle hab (Ne.symm hka) (Ne.symm hkb)).sign
      have h1 := hH _ hσ (pairVec a k)
      rwa [coreAct_cyc_pairVec (Ne.symm hka) (Ne.symm hkb)] at h1
  exact (Subgroup.closure_le H).2 (by rintro _ ⟨a, b, rfl⟩; exact hpair a b)
    (mem_closure_pairVec' (by omega) v)

end Delta

section Even

variable {Γ : Type} [Group Γ] {n : ℕ}

@[expose] def evenSub (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) : Subgroup Γ :=
  ((alternatingGroup (Fin n)).comap φ).map G.subtype

theorem mem_evenSub {G : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)} {g : Γ} :
    g ∈ evenSub G φ ↔ ∃ hg : g ∈ G, φ ⟨g, hg⟩ ∈ alternatingGroup (Fin n) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨g, h⟩, hx, rfl⟩

theorem evenSub_le (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) : evenSub G φ ≤ G := by
  intro x hx
  exact (mem_evenSub.1 hx).1

theorem le_normalizer_evenSub (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) :
    G ≤ Subgroup.normalizer (evenSub G φ : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨hhG, hha⟩ := mem_evenSub.1 hh
    refine mem_evenSub.2 ⟨G.mul_mem (G.mul_mem hg hhG) (G.inv_mem hg), ?_⟩
    have e : (⟨g * h * g⁻¹, G.mul_mem (G.mul_mem hg hhG) (G.inv_mem hg)⟩ : ↥G) =
        ⟨g, hg⟩ * ⟨h, hhG⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem _ hha (φ ⟨g, hg⟩)
  · intro hh
    obtain ⟨hhG, hha⟩ := mem_evenSub.1 hh
    have hhG' : h ∈ G := by
      have := G.mul_mem (G.mul_mem (G.inv_mem hg) hhG) hg
      simpa [mul_assoc] using this
    refine mem_evenSub.2 ⟨hhG', ?_⟩
    have e : (⟨h, hhG'⟩ : ↥G) = ⟨g, hg⟩⁻¹ * ⟨g * h * g⁻¹, hhG⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [e, map_mul, map_mul, map_inv]
    exact (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem _ hha
      ((φ ⟨g, hg⟩)⁻¹)

@[expose] def evenHom (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) :
    ↥(evenSub G φ) →* alternatingGroup (Fin n) where
  toFun x := ⟨φ ⟨x, (mem_evenSub.1 x.2).1⟩, (mem_evenSub.1 x.2).2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' x y := Subtype.ext (map_mul φ ⟨x, (mem_evenSub.1 x.2).1⟩ ⟨y, (mem_evenSub.1 y.2).1⟩)

theorem evenHom_coe (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) (x : ↥(evenSub G φ)) :
    ((evenHom G φ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
      φ ⟨x, (mem_evenSub.1 x.2).1⟩ := rfl

theorem evenHom_surjective (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n))
    (hφs : Function.Surjective φ) : Function.Surjective (evenHom G φ) := by
  intro σ
  obtain ⟨g, hg⟩ := hφs (σ : Equiv.Perm (Fin n))
  have hge : (g : Γ) ∈ evenSub G φ := mem_evenSub.2 ⟨g.2, by
    have : φ ⟨(g : Γ), g.2⟩ = σ := hg
    rw [this]
    exact σ.2⟩
  refine ⟨⟨g, hge⟩, Subtype.ext ?_⟩
  rw [evenHom_coe]
  exact hg

theorem conj_mem_commutator {H K : Subgroup Γ} {g : Γ}
    (hH : g ∈ Subgroup.normalizer (H : Set Γ)) (hK : g ∈ Subgroup.normalizer (K : Set Γ))
    {x : Γ} (hx : x ∈ ⁅H, K⁆) : g * x * g⁻¹ ∈ ⁅H, K⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure
    {z : Γ | ∃ h₁ ∈ H, ∃ h₂ ∈ K, ⁅h₁, h₂⁆ = z}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    refine Subgroup.subset_closure ⟨g * h₁ * g⁻¹, ?_, g * h₂ * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hH h₁).mp hh₁
    · exact (Subgroup.mem_normalizer_iff.mp hK h₂).mp hh₂
    · simp only [commutatorElement_def]
      group
  · simp
  · intro a b _ _ ha hb
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

end Even

section Core

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}

theorem exists_perfectCore {G V : Subgroup Γ} (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (h3 : 3 ≤ n) (φ : ↥G →* Equiv.Perm (Fin n)) (hφs : Function.Surjective φ)
    (ψ : ↥V →* ↥(coreMod n)) (hψs : Function.Surjective ψ)
    (hψe : ∀ (e : ↥G) (v : ↥V) (hv : (e : Γ) * v * (e : Γ)⁻¹ ∈ V),
      ψ ⟨(e : Γ) * v * (e : Γ)⁻¹, hv⟩ = coreAct n (φ e) (ψ v)) :
    ∃ W : Subgroup Γ, W ≤ V ∧ G ≤ Subgroup.normalizer (W : Set Γ) ∧
      (∀ u : ↥(coreMod n), ∃ w : ↥V, (w : Γ) ∈ W ∧ ψ w = u) ∧ ⁅evenSub G φ, W⁆ = W := by
  classical
  let S : Set (Subgroup Γ) := {W | W ≤ V ∧ G ≤ Subgroup.normalizer (W : Set Γ) ∧
    ∀ u : ↥(coreMod n), ∃ w : ↥V, (w : Γ) ∈ W ∧ ψ w = u}
  have hVS : V ∈ S := ⟨le_rfl, hVn, fun u => by
    obtain ⟨w, hw⟩ := hψs u
    exact ⟨w, w.2, hw⟩⟩
  obtain ⟨W, hW⟩ := (Set.toFinite S).exists_minimal ⟨V, hVS⟩
  obtain ⟨hWV, hWG, hWψ⟩ := hW.prop
  refine ⟨W, hWV, hWG, hWψ, ?_⟩
  have hE₀G : evenSub G φ ≤ G := evenSub_le G φ
  have hW'le : ⁅evenSub G φ, W⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro e he w hw
    have h1 : (e : Γ) * w * (e : Γ)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWG (hE₀G he)) w).mp hw
    have h2 := W.mul_mem h1 (W.inv_mem hw)
    simpa [commutatorElement_def, mul_assoc] using h2
  have hW'S : ⁅evenSub G φ, W⁆ ∈ S := by
    refine ⟨hW'le.trans hWV, fun g hg => ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact conj_mem_commutator (le_normalizer_evenSub G φ hg) (hWG hg)
      · intro hx
        have h1 := conj_mem_commutator (le_normalizer_evenSub G φ (G.inv_mem hg))
          (hWG (G.inv_mem hg)) hx
        simpa [mul_assoc] using h1
    · set H : Subgroup ↥(coreMod n) := ((⁅evenSub G φ, W⁆.subgroupOf V).map ψ) with hH
      have hHtop : H = ⊤ := by
        refine eq_top_of_commutator_coreAct_alt h3 H fun σ hσ v => ?_
        obtain ⟨g, hg⟩ := hφs σ
        obtain ⟨w, hwW, hwv⟩ := hWψ v
        have hgE : (g : Γ) ∈ evenSub G φ :=
          mem_evenSub.2 ⟨g.2, by rw [show φ ⟨(g : Γ), g.2⟩ = σ from hg]; exact hσ⟩
        have hq : (g : Γ) * w * (g : Γ)⁻¹ ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (hVn g.2) (w : Γ)).mp w.2
          exact this
        refine ⟨⟨(g : Γ) * w * (g : Γ)⁻¹, hq⟩ * w⁻¹, ?_, ?_⟩
        · show ((⟨(g : Γ) * w * (g : Γ)⁻¹, hq⟩ * w⁻¹ : ↥V) : Γ) ∈ ⁅evenSub G φ, W⁆
          have : ((⟨(g : Γ) * w * (g : Γ)⁻¹, hq⟩ * w⁻¹ : ↥V) : Γ) = ⁅(g : Γ), (w : Γ)⁆ := by
            simp [commutatorElement_def]
          rw [this]
          exact Subgroup.commutator_mem_commutator hgE hwW
        · rw [map_mul, map_inv, hψe g w hq, hwv]
          have : φ g = σ := hg
          rw [this]
          rfl
      intro u
      have hu : u ∈ H := hHtop ▸ Subgroup.mem_top u
      obtain ⟨w, hw, hwu⟩ := hu
      exact ⟨w, hw, hwu⟩
  exact le_antisymm hW'le (hW.2 hW'S hW'le)

omit [Finite Γ] in
theorem natAlt_data_core {G V W : Subgroup Γ} (hn : Odd n) (h3 : 3 ≤ n)
    (φ : ↥G →* Equiv.Perm (Fin n)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (G ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf G)
    (ψ : ↥V →* ↥(coreMod n))
    (hψk : ψ.ker = (V ⊓ Subgroup.centralizer (G : Set Γ)).subgroupOf V)
    (hψe : ∀ (e : ↥G) (v : ↥V) (hv : (e : Γ) * v * (e : Γ)⁻¹ ∈ V),
      ψ ⟨(e : Γ) * v * (e : Γ)⁻¹, hv⟩ = coreAct n (φ e) (ψ v))
    (hWV : W ≤ V) (hWψ : ∀ u : ↥(coreMod n), ∃ w : ↥V, (w : Γ) ∈ W ∧ ψ w = u) :
    Function.Surjective (evenHom G φ) ∧
      (evenHom G φ).ker =
        (evenSub G φ ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf (evenSub G φ) ∧
      Function.Surjective (ψ.comp (Subgroup.inclusion hWV)) ∧
      (ψ.comp (Subgroup.inclusion hWV)).ker =
        (W ⊓ Subgroup.centralizer ((evenSub G φ : Subgroup Γ) : Set Γ)).subgroupOf W ∧
      ∀ (e : ↥(evenSub G φ)) (w : ↥W) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ W),
        (ψ.comp (Subgroup.inclusion hWV)) ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ =
          coreAct n ((evenHom G φ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
            ((ψ.comp (Subgroup.inclusion hWV)) w) := by
  classical
  have hE₀G : evenSub G φ ≤ G := evenSub_le G φ
  refine ⟨evenHom_surjective G φ hφs, ?_, ?_, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have h1 : φ ⟨x, (mem_evenSub.1 x.2).1⟩ = 1 := by
        have := congrArg Subtype.val hx
        simpa [evenHom_coe] using this
      have h2 : (⟨x, (mem_evenSub.1 x.2).1⟩ : ↥G) ∈ φ.ker := h1
      rw [hφk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at h2 ⊢
      intro w hw
      exact h2.2 w (hWV hw)
    · rintro ⟨-, hxW⟩
      apply Subtype.ext
      have hco : coreAct n (φ ⟨x, (mem_evenSub.1 x.2).1⟩) = 1 := by
        refine MulEquiv.ext fun u => ?_
        obtain ⟨w, hwW, hwu⟩ := hWψ u
        have hxw : (x : Γ) * w * (x : Γ)⁻¹ = w := by
          have := Subgroup.mem_centralizer_iff.mp hxW w hwW
          calc (x : Γ) * w * (x : Γ)⁻¹ = ((x : Γ) * w) * (x : Γ)⁻¹ := rfl
            _ = (w * x) * (x : Γ)⁻¹ := by rw [this]
            _ = w := by group
        have hv : (x : Γ) * w * (x : Γ)⁻¹ ∈ V := by
          rw [hxw]
          exact w.2
        have h1 := hψe ⟨x, (mem_evenSub.1 x.2).1⟩ w hv
        have h2 : (⟨(x : Γ) * w * (x : Γ)⁻¹, hv⟩ : ↥V) = w := Subtype.ext hxw
        rw [h2, hwu] at h1
        have h3' : (coreAct n (φ ⟨x, (mem_evenSub.1 x.2).1⟩)) u = u := h1.symm
        exact h3'
      have := coreAct_injective h3 (hco.trans (map_one (coreAct n)).symm)
      simpa [evenHom_coe] using this
  · intro u
    obtain ⟨w, hwW, hwu⟩ := hWψ u
    exact ⟨⟨w, hwW⟩, hwu⟩
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hw
      have h1 : ψ ⟨w, hWV w.2⟩ = 1 := hw
      have h2 : (⟨w, hWV w.2⟩ : ↥V) ∈ ψ.ker := h1
      rw [hψk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
      refine ⟨w.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at h2 ⊢
      intro e he
      exact h2.2 e (hE₀G he)
    · rintro ⟨-, hwC⟩
      have hfix : ψ ⟨w, hWV w.2⟩ ∈ fixV ((alternatingGroup (Fin n)).map (coreAct n)) := by
        intro y hy
        obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hy
        obtain ⟨x, hx⟩ := evenHom_surjective G φ hφs ⟨σ, hσ⟩
        have hxσ : φ ⟨x, (mem_evenSub.1 x.2).1⟩ = σ := by
          have := congrArg Subtype.val hx
          simpa [evenHom_coe] using this
        have hxw : (x : Γ) * w * (x : Γ)⁻¹ = w := by
          have := Subgroup.mem_centralizer_iff.mp hwC x x.2
          calc (x : Γ) * w * (x : Γ)⁻¹ = ((x : Γ) * w) * (x : Γ)⁻¹ := rfl
            _ = (w * x) * (x : Γ)⁻¹ := by rw [← this]
            _ = w := by group
        have hv : (x : Γ) * w * (x : Γ)⁻¹ ∈ V := by
          rw [hxw]
          exact hWV w.2
        have h1 := hψe ⟨x, (mem_evenSub.1 x.2).1⟩ ⟨w, hWV w.2⟩ hv
        have h2 : (⟨(x : Γ) * w * (x : Γ)⁻¹, hv⟩ : ↥V) = ⟨w, hWV w.2⟩ := Subtype.ext hxw
        rw [h2, hxσ] at h1
        exact h1.symm
      rw [fixV_alt_map hn h3] at hfix
      exact Subgroup.mem_bot.mp hfix
  · intro e w hw
    have hv : (e : Γ) * w * (e : Γ)⁻¹ ∈ V := hWV hw
    have h1 := hψe ⟨e, hE₀G e.2⟩ ⟨w, hWV w.2⟩ hv
    exact h1

end Core

end CFSG.CGT.PushingUpLit.BHS6
