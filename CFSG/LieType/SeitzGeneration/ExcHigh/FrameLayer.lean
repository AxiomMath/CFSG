module

public import CFSG.LieType.SeitzGeneration.ExcHigh.CubePlanes

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open CFSG.HardMathSupport.Lang.AnisoE6 TauCeti

theorem card_sup_eq_mul_of_commute_disjoint {G : Type*} [Group G] {A F : Subgroup G}
    (hc : ∀ a ∈ A, ∀ f ∈ F, a * f = f * a) (hd : Disjoint A F) :
    Nat.card ↥(A ⊔ F) = Nat.card A * Nat.card F := by
  have comm : ∀ (a : A) (f : F), Commute (A.subtype a) (F.subtype f) :=
    fun a f => hc a a.2 f f.2
  have hinj : Function.Injective ((A.subtype).noncommCoprod (F.subtype) comm) := by
    refine (MonoidHom.noncommCoprod_injective A.subtype F.subtype comm).2
      ⟨Subgroup.subtype_injective A, Subgroup.subtype_injective F, ?_⟩
    simpa [Subgroup.range_subtype] using hd
  have hrange : ((A.subtype).noncommCoprod (F.subtype) comm).range = A ⊔ F := by
    rw [MonoidHom.noncommCoprod_range A.subtype F.subtype comm]
    simp [Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem cl_eq_top_of_closing {G : Type*} [Group G] {E X P : Subgroup G} (hX : X ≤ cl E)
    (hP : P ≤ cl E)
    (hclose : ∀ H : Subgroup G, X ≤ H → ¬ H ≤ Subgroup.normalizer (X : Set G) → H = ⊤)
    (hPX : ¬ P ≤ Subgroup.normalizer (X : Set G)) : cl E = ⊤ :=
  hclose _ hX fun hN => hPX (hP.trans hN)

theorem frame_factor_le_cl {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {V V₁ V₂ X E : Subgroup G} (hV : Nat.card V = p ^ 4) (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V)
    (hV₂c : Nat.card V₂ = p ^ 2) (hdisj : Disjoint V₁ V₂)
    (hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) (hXV₂ : ∀ g ∈ X, ∀ b ∈ V₂, g * b = b * g)
    (hpow : ∀ x ∈ V₁, x ^ p = 1)
    (hPG : X ≤ Subgroup.closure {g | g ∈ X ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g})
    (hEV : E ≤ V) (hEc : Nat.card E = p ^ 2) : X ≤ cl E := by
  haveI := Fact.mk hp
  refine hPG.trans ?_
  rw [Subgroup.closure_le]
  rintro g ⟨hgX, x, hxV, hx1, hgx⟩
  set D : Subgroup G := Subgroup.zpowers x ⊔ V₂ with hD
  have hzx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hpow x hxV) hx1]
  have hzV : Subgroup.zpowers x ≤ V₁ := (Subgroup.zpowers_le).2 hxV
  have hdz : Disjoint (Subgroup.zpowers x) V₂ := hdisj.mono_left hzV
  have hcD : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
    hcomm a (hzV ha) b hb
  have hDc : Nat.card D = p ^ 3 := by
    rw [hD, card_sup_eq_mul_of_commute_disjoint hcD hdz, hzx, hV₂c]
    ring
  have hDV : D ≤ V := sup_le (hzV.trans hV₁V) hV₂V
  have hDi : D.relIndex V = p := by
    have h2 := Subgroup.relIndex_mul_card D V
    rw [inf_of_le_left hDV, hDc, hV] at h2
    have hp0 : 0 < p ^ 3 := pow_pos hp.pos 3
    have : D.relIndex V * p ^ 3 = p * p ^ 3 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  obtain ⟨y, hyE, hy1⟩ := exists_ne_one_mem_plane_inf_hyperplane hp hEV hEc hDi
    (by rw [hV]; exact (pow_pos hp.pos 4).ne')
  have hcent : D ≤ Subgroup.centralizer ({g} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.zpow_left (show Commute x g from hgx.symm) n).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hXV₂ g hgX b hb).symm
  have hyg := Subgroup.mem_centralizer_singleton_iff.1 (hcent hyE.2)
  exact mem_cl_of_commute hyE.1 hy1 hyg.symm

theorem planeGen_of_oneV {d : ValidLieTypeIndex} {p m : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)))
    (hS : SylowTorus (Cat d) p m)
    (hV : ∃ V : Subgroup (Cat d), IsElemAbelian p V ∧ Nat.card V = p ^ m ∧
      ∀ E : Subgroup (Cat d), E ≤ V → IsElemAbelian p E → Nat.card E = p ^ 2 → cl E = ⊤)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hin : InnerPlane d p E) : PlaneGen E := by
  obtain ⟨E', hE'el, hE'c, hE'map⟩ := exists_map_conj_eq hinj hin hE hEc
  obtain ⟨V, hVel, hVc, hVall⟩ := hV
  obtain ⟨T, V0, -, hconj, hV0T, hV0tor, hV0el, hV0c⟩ := hS.exists_torus
  obtain ⟨g, hg⟩ := hconj E' (isPGroup_of_isElemAbelian hE'el)
  set V' : Subgroup (Cat d) := V0.map (MulAut.conj g).toMonoidHom with hV'def
  have hV'el : IsElemAbelian p V' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hV0el _
  have hV'c : Nat.card V' = p ^ m := by
    rw [hV'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hV0c]
  have hE'V' : E' ≤ V' := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hg hx
    have htp : t ^ p = 1 := by
      have h1 := hE'el.2 x hx
      rw [← hxt] at h1
      have : (MulAut.conj g) (t ^ p) = 1 := by
        rw [map_pow]
        exact h1
      exact (MulAut.conj g).injective (this.trans (map_one _).symm)
    exact ⟨t, hV0tor t ht htp, hxt⟩
  obtain ⟨x, hx⟩ := exists_conj_of_sylowTorus_cube hp hS hVel hVc hV'el hV'c
  set E'' : Subgroup (Cat d) := E'.map (MulAut.conj x⁻¹).toMonoidHom with hE''def
  have hE''V : E'' ≤ V := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ V.map (MulAut.conj x).toMonoidHom := hx ▸ hE'V' hy
    obtain ⟨v, hv, hvy⟩ := hy'
    have : (MulAut.conj x⁻¹).toMonoidHom y = v := by
      rw [← hvy]
      show x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v
      group
    rw [this]
    exact hv
  have hE''el : IsElemAbelian p E'' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'el _
  have hE''c : Nat.card E'' = p ^ 2 := by
    rw [hE''def, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hE'c]
  have htop : cl E'' = ⊤ := hVall E'' hE''V hE''el hE''c
  have hE'top : cl E' = ⊤ := cl_eq_top_of_map (MulAut.conj x⁻¹) E' (by simpa [hE''def] using htop)
  rw [PlaneGen, ← hE'map, planeClosure_map_conj hinj]
  exact hE'top

structure LeviLayer (G : Type*) [Group G] (p : ℕ) (V L : Subgroup G) : Prop where
  exists_split : ∃ A B : Subgroup G, A ≤ V ∧ B ≤ V ∧ Nat.card A = p ∧ Nat.card B = p ^ 3 ∧
    Disjoint A B ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ (∀ l ∈ L, ∀ a ∈ A, l * a = a * l) ∧
    HyperGen p L B

theorem le_hyperClosure_of_levi {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {V A B L : Subgroup G} (hV : Nat.card V = p ^ 4) (hAV : A ≤ V) (hBV : B ≤ V)
    (hAc : Nat.card A = p) (hBc : Nat.card B = p ^ 3) (hdisj : Disjoint A B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hLA : ∀ l ∈ L, ∀ a ∈ A, l * a = a * l)
    (hHG : HyperGen p L B) : L ≤ hyperClosure p ⊤ V := by
  refine hHG.trans ?_
  rw [Subgroup.closure_le]
  rintro k ⟨hkL, F, hFB, hFi, hFk⟩
  refine Subgroup.subset_closure ⟨trivial, A ⊔ F, sup_le hAV (hFB.trans hBV), ?_, ?_⟩
  ·
    have hFc : Nat.card F = p ^ 2 := by
      have h1 := Subgroup.relIndex_mul_card F B
      rw [inf_of_le_left hFB, hFi, hBc] at h1
      have hp0 : 0 < p := hp.pos
      have : p * Nat.card F = p * p ^ 2 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    have hdF : Disjoint A F := hdisj.mono_right hFB
    have hcard : Nat.card ↥(A ⊔ F) = p ^ 3 := by
      rw [card_sup_eq_mul_of_commute_disjoint (fun a ha f hf => hAB a ha f (hFB hf)) hdF,
        hAc, hFc]
      ring
    have h2 := Subgroup.relIndex_mul_card (A ⊔ F) V
    rw [inf_of_le_left (sup_le hAV (hFB.trans hBV)), hcard, hV] at h2
    have hp0 : 0 < p ^ 3 := pow_pos hp.pos 3
    have : (A ⊔ F).relIndex V * p ^ 3 = p * p ^ 3 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  · intro x hx
    have hcent : A ⊔ F ≤ Subgroup.centralizer ({k} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun f hf => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hLA k hkL a ha).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hFk f hf
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hx)

theorem LeviLayer.le_hyperClosure {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {V L : Subgroup G}
    (hV : Nat.card V = p ^ 4) (h : LeviLayer G p V L) : L ≤ hyperClosure p ⊤ V := by
  obtain ⟨A, B, hAV, hBV, hAc, hBc, hd, hAB, hLA, hHG⟩ := h.exists_split
  exact le_hyperClosure_of_levi hp hV hAV hBV hAc hBc hd hAB hLA hHG

theorem planes_of_frame_layer {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {V V₁ V₂ X₁ X₂ P : Subgroup G} (hV : Nat.card V = p ^ 4)
    (hV₁V : V₁ ≤ V) (hV₂V : V₂ ≤ V) (hV₁c : Nat.card V₁ = p ^ 2) (hV₂c : Nat.card V₂ = p ^ 2)
    (hdisj : Disjoint V₁ V₂) (hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a)
    (hpow : ∀ x ∈ V, x ^ p = 1) (hX₁V₂ : ∀ g ∈ X₁, ∀ b ∈ V₂, g * b = b * g)
    (hX₂V₁ : ∀ g ∈ X₂, ∀ b ∈ V₁, g * b = b * g)
    (hPG₁ : X₁ ≤ Subgroup.closure {g | g ∈ X₁ ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g})
    (hPG₂ : X₂ ≤ Subgroup.closure {g | g ∈ X₂ ∧ ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g})
    (hclose : ∀ H : Subgroup G, X₁ ⊔ X₂ ≤ H →
      ¬ H ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) → H = ⊤)
    (hlayer : LeviLayer G p V P)
    (hPX : ¬ P ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G)) :
    ∀ E : Subgroup G, E ≤ V → Nat.card E = p ^ 2 → cl E = ⊤ := by
  intro E hEV hEc
  have hVne : Nat.card V ≠ 0 := by rw [hV]; exact (pow_pos hp.pos 4).ne'
  have hX₁ : X₁ ≤ cl E :=
    frame_factor_le_cl hp hV hV₁V hV₂V hV₂c hdisj hcomm hX₁V₂ (fun x hx => hpow x (hV₁V hx)) hPG₁
      hEV hEc
  have hX₂ : X₂ ≤ cl E :=
    frame_factor_le_cl hp hV hV₂V hV₁V hV₁c hdisj.symm (fun a ha b hb => (hcomm b hb a ha).symm)
      hX₂V₁ (fun x hx => hpow x (hV₂V hx)) hPG₂ hEV hEc
  have hP : P ≤ cl E := (hlayer.le_hyperClosure hp hV).trans (hyperClosure_le_cl hp hEV hEc hVne)
  exact cl_eq_top_of_closing (sup_le hX₁ hX₂) hP hclose hPX

end CFSG.LieType.SeitzGeneration.ExcHigh
