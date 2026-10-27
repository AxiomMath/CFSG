module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModel

public section

namespace CFSG.ComponentClassification.FooteSmall

open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall

theorem exists_dihPair {K : Type} [Group K] [Finite K] {G : Type*} [Group G] (PM : Subgroup G)
    (e : K ≃* PM) (Q0 : Subgroup G) (hQ0 : IsPGroup 2 Q0) {a b : G} (haQ : a ∈ Q0) (hbQ : b ∈ Q0)
    (haP : a ∈ PM) (hbP : b ∈ PM) (hab : IsDihPair a b) {H : Type*} [Group H] (P : Sylow 2 K)
    (ψ : (P : Subgroup K) ≃* H) : ∃ u v : H, IsDihPair u v := by
  set D : Subgroup K := (Q0.comap PM.subtype).map e.symm.toMonoidHom
  have hDp : IsPGroup 2 D := (hQ0.comap_of_injective PM.subtype Subtype.val_injective).map _
  obtain ⟨Q, hDQ⟩ := hDp.exists_le_sylow
  have hx : e.symm ⟨a, haP⟩ ∈ D := ⟨⟨a, haP⟩, haQ, rfl⟩
  have hy : e.symm ⟨b, hbP⟩ ∈ D := ⟨⟨b, hbP⟩, hbQ, rfl⟩
  let φ : (Q : Subgroup K) ≃* (P : Subgroup K) := Sylow.equiv Q P
  refine ⟨ψ (φ ⟨_, hDQ hx⟩), ψ (φ ⟨_, hDQ hy⟩), ?_⟩
  have h1 : IsDihPair (⟨a, haP⟩ : PM) ⟨b, hbP⟩ :=
    IsDihPair.of_map PM.subtype Subtype.val_injective hab
  have h2 : IsDihPair (e.symm ⟨a, haP⟩) (e.symm ⟨b, hbP⟩) :=
    h1.map e.symm.toMonoidHom e.symm.injective
  have h3 : IsDihPair (⟨_, hDQ hx⟩ : (Q : Subgroup K)) ⟨_, hDQ hy⟩ :=
    IsDihPair.of_map (Q : Subgroup K).subtype Subtype.val_injective h2
  exact (h3.map φ.toMonoidHom φ.injective).map ψ.toMonoidHom ψ.injective

theorem conj_mem_P {K G : Type*} [Group K] [Group G] (M : AutModel K G) {g : G} (hg : g ∈ M.A)
    {c : G} (hc : c ∈ M.P) : g * c * g⁻¹ ∈ M.P := by
  have h := M.spec (M.Φ.symm ⟨g, hg⟩) (M.e.symm ⟨c, hc⟩)
  simp only [MulEquiv.apply_symm_apply] at h
  rw [← h]
  exact (M.e _).2

theorem comm_conj {G : Type*} [Group G] {a b g : G} (h : b * (g * a * g⁻¹) = g * a * g⁻¹ * b) :
    a * (g⁻¹ * b * g) = g⁻¹ * b * g * a :=
  calc a * (g⁻¹ * b * g) = g⁻¹ * (g * a * g⁻¹ * b) * g := by group
    _ = g⁻¹ * (b * (g * a * g⁻¹)) * g := by rw [h]
    _ = g⁻¹ * b * g * a := by group

theorem iSup_fix_eq_top {K : Type} [Group K] {n : ℕ} (M : AutModel K (Equiv.Perm (Fin n)))
    (Q0 : Subgroup (Equiv.Perm (Fin n))) (hQ0A : Q0 ≤ M.A)
    (hQ0 : Nat.card Q0 = 2 ^ (Nat.card M.A).factorization 2)
    (hgen : ∀ u ∈ Q0, ∀ v ∈ Q0, IsDihPair u v → ∀ X : Subgroup (Equiv.Perm (Fin n)),
      (∀ c ∈ M.P, ∀ t ∈ dihInvs u v, c * t = t * c → c ∈ X) → M.P ≤ X)
    (T : Subgroup (MulAut K)) (hT : IsPGroup 2 T) {u v : MulAut K} (hu : u ∈ T) (hv : v ∈ T)
    (huv : IsDihPair u v) :
    ⨆ (τ : MulAut K) (_ : τ ∈ T) (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id K) = ⊤ := by
  classical
  set H : Subgroup K := ⨆ (τ : MulAut K) (_ : τ ∈ T) (_ : orderOf τ = 2),
    MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id K)
  have hT' : IsPGroup 2 (T.map M.Φ.toMonoidHom) := hT.map _
  obtain ⟨Q, hTQ⟩ := hT'.exists_le_sylow
  let Q0S : Sylow 2 M.A := Sylow.ofCard (Q0.subgroupOf M.A) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0A).toEquiv]
    exact hQ0)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M.A Q Q0S
  let f : MulAut K →* Equiv.Perm (Fin n) :=
    (MulAut.conj (g : Equiv.Perm (Fin n))).toMonoidHom.comp (M.A.subtype.comp M.Φ.toMonoidHom)
  have hf : ∀ τ, f τ = (g : Equiv.Perm (Fin n)) * (M.Φ τ : Equiv.Perm (Fin n)) *
      (g : Equiv.Perm (Fin n))⁻¹ := fun τ => rfl
  have hfinj : Function.Injective f := by
    intro τ σ h
    rw [hf, hf, mul_left_inj, mul_right_inj] at h
    exact M.Φ.injective (Subtype.ext h)
  have hconj : ∀ τ ∈ T, f τ ∈ Q0 := by
    intro τ hτ
    have h1 : M.Φ τ ∈ (Q : Subgroup M.A) := hTQ ⟨τ, hτ, rfl⟩
    have h2 : MulAut.conj g (M.Φ τ) ∈ ((g • Q : Sylow 2 M.A) : Subgroup M.A) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hg] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  set X : Subgroup (Equiv.Perm (Fin n)) :=
    (H.map (modelEmb M)).map (MulAut.conj (g : Equiv.Perm (Fin n))).toMonoidHom
  have hcX : ∀ c ∈ M.P, ∀ t ∈ dihInvs (f u) (f v), c * t = t * c → c ∈ X := by
    intro c hc t ht hct
    rw [dihInvs_map] at ht
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 ht
    have hc' : (g : Equiv.Perm (Fin n))⁻¹ * c * g ∈ M.P := by
      have := conj_mem_P M (M.A.inv_mem g.2) hc
      rwa [inv_inv] at this
    rw [hf] at hct
    have hcomm := comm_conj hct
    set x := M.e.symm ⟨_, hc'⟩ with hxdef
    have hx : τ x = x := by
      rw [apply_eq_self_iff M τ x, hxdef, modelEmb_symm]
      exact hcomm
    have hxH : x ∈ H := by
      refine Subgroup.mem_iSup_of_mem τ (Subgroup.mem_iSup_of_mem (dihInvs_subset hu hv τ hτ)
        (Subgroup.mem_iSup_of_mem (huv.orderOf_eq_two τ hτ) ?_))
      exact hx
    refine ⟨modelEmb M x, ⟨x, hxH, rfl⟩, ?_⟩
    rw [hxdef, modelEmb_symm]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hPX : M.P ≤ X := hgen (f u) (hconj u hu) (f v) (hconj v hv) (huv.map f hfinj) X hcX
  rw [eq_top_iff]
  intro y _
  have hw := conj_mem_P M g.2 (modelEmb_mem M y)
  obtain ⟨z, ⟨y', hy'H, rfl⟩, hz⟩ := hPX hw
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hz
  rwa [← modelEmb_injective M hz]

theorem factorization_two_of_eq {N k r : ℕ} (hN : N = 2 ^ k * r) (hr : r % 2 = 1) :
    N.factorization 2 = k := by
  subst hN
  rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by omega), add_zero]

open CFSG.Certificates CFSG.Sporadic.Schreier in
theorem iSup_fix_eq_top_of_checks {K : Type} [Group K] [Finite K] {n k m : ℕ}
    (QP QA : RawSchreierDatum n) (hQP : ValidSchreier QP) (hQA : ValidSchreier QA)
    {pa pb : Equiv.Perm (Fin n)} (hP : QP.originalSubgroup = Subgroup.closure {pa, pb})
    (M : AutModel K (Equiv.Perm (Fin n))) (hMP : M.P = QP.originalSubgroup)
    (hMA : M.A = QA.originalSubgroup) (L : List (Equiv.Perm (Fin n)))
    (hL : closedCheck L = true) (hLnd : L.Nodup)
    (hLcard : L.length = 2 ^ QA.orderCertificate.factorization 2)
    (hLA : L.all (fun g => QA.sift g 0) = true)
    (hpair : pairCheck k m L (elemsT QP) [pa, pb] = true) {a b : Equiv.Perm (Fin n)}
    (haL : a ∈ L) (hbL : b ∈ L) (haP : QP.sift a 0 = true) (hbP : QP.sift b 0 = true)
    (hab : dihB a b = true) (T : Subgroup (MulAut K)) (hT : IsPGroup 2 T)
    (hTP : ∃ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* T)) :
    ⨆ (τ : MulAut K) (_ : τ ∈ T) (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id K) = ⊤ := by
  set Q0 := ofList L hL
  have hQ0A : Q0 ≤ M.A := by
    intro g hg
    rw [hMA, mem_iff_sift QA hQA]
    exact List.all_eq_true.1 hLA g ((mem_ofList L hL g).1 hg)
  have hcard : Nat.card Q0 = 2 ^ (Nat.card M.A).factorization 2 := by
    rw [card_ofList L hL hLnd, hLcard, hMA, card_group QA hQA]
  have hQ0p : IsPGroup 2 Q0 := IsPGroup.of_card hcard
  have hgen : ∀ u ∈ Q0, ∀ v ∈ Q0, IsDihPair u v → ∀ X : Subgroup (Equiv.Perm (Fin n)),
      (∀ c ∈ M.P, ∀ t ∈ dihInvs u v, c * t = t * c → c ∈ X) → M.P ≤ X := by
    intro u hu v hv huv X hX
    have h := pairCheck_sound hpair M.P (fun c hc => by
      rw [hMP, ← mem_elemsT QP hQP]; exact hc) hu hv huv X hX
    rw [hMP, hP, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact h _ List.mem_cons_self
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨P, ⟨ψ⟩⟩ := hTP
  have haP' : a ∈ M.P := by rw [hMP, mem_iff_sift QP hQP]; exact haP
  have hbP' : b ∈ M.P := by rw [hMP, mem_iff_sift QP hQP]; exact hbP
  obtain ⟨u, v, huv⟩ := exists_dihPair M.P M.e Q0 hQ0p haL hbL haP' hbP' ((dihB_iff a b).1 hab)
    P ψ
  exact iSup_fix_eq_top M Q0 hQ0A hcard hgen T hT u.2 v.2 (huv.map T.subtype Subtype.val_injective)

end CFSG.ComponentClassification.FooteSmall
