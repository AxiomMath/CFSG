module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.LocalCores
open scoped commutatorElement

variable {W : Type*} [Group W]

theorem mem_map_conj_iff {K : Subgroup W} {g x : W} :
    x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_map_conj {K : Subgroup W} {g k : W} (hk : k ∈ K) :
    g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by
  rw [mem_map_conj_iff]
  simpa [mul_assoc] using hk

theorem commute_conj {a b : W} (g : W) (h : Commute a b) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) := by
  change g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h.eq]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem map_conj_map_conj {K : Subgroup W} {g : W} (hg2 : ∀ x ∈ K, g ^ 2 * x = x * g ^ 2) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff]
  constructor
  · intro hx
    have h := hg2 _ hx
    rw [pow_two] at h
    have e : x = g * g * (g⁻¹ * (g⁻¹ * x * g) * g) * (g * g)⁻¹ := by group
    rw [e, h]
    simpa [mul_assoc] using hx
  · intro hx
    have h := hg2 _ hx
    rw [pow_two] at h
    have e : g⁻¹ * (g⁻¹ * x * g) * g = (g * g)⁻¹ * (x * (g * g)) := by group
    rw [e, ← h]
    simpa [mul_assoc] using hx

variable [Finite W]

theorem commute_of_ne {K L : Subgroup W} (hK : IsComponent K) (hL : IsComponent L) (hne : K ≠ L)
    {a b : W} (ha : a ∈ K) (hb : b ∈ L) : Commute a b := by
  rcases distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · exact ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h ha)) b hb).symm

theorem exists_mem_mul_centralizer {K : Subgroup W} (hK : IsComponent K) {y : W}
    (hy : y ∈ layer W) : ∃ u ∈ K, ∀ k ∈ K, Commute k (u⁻¹ * y) := by
  classical
  obtain ⟨x, rfl⟩ := exists_layerMul_eq hy
  set Ki : ComponentIndex W := ⟨K, hK⟩
  refine ⟨(x Ki : W), (x Ki).2, fun k hk => ?_⟩
  have h1 := layerMul_eq_mul_update x Ki
  have h2 : (x Ki : W)⁻¹ * layerMul W x = layerMul W (Function.update x Ki 1) := by
    rw [h1, inv_mul_cancel_left]
  rw [h2]
  exact commute_layerMul_update x Ki (k := k) hk

theorem le_of_pieces {J T : Subgroup W} (hJ : ⁅J, J⁆ = J) (hJE : J ≤ layer W) {g : W}
    (hJg : ∀ j ∈ J, Commute g j) (hg2 : ∀ x ∈ layer W, g ^ 2 * x = x * g ^ 2)
    (hTg : T ≤ centralizer ({g} : Set W))
    (hfix : ∀ K : Subgroup W, IsComponent K → ¬ J ≤ centralizer (K : Set W) →
      K.map (MulAut.conj g).toMonoidHom = K → K ≤ T)
    (hswap : ∀ K : Subgroup W, IsComponent K → ¬ J ≤ centralizer (K : Set W) →
      K.map (MulAut.conj g).toMonoidHom ≠ K → ∀ u ∈ K, u * (g * u * g⁻¹) ∈ T) :
    J ≤ T := by
  classical
  set E := layer W with hE
  have hTgc : ∀ t ∈ T, Commute g t := fun t ht =>
    (mem_centralizer_singleton_iff.mp (hTg ht)).symm
  let σ : ComponentIndex W → ComponentIndex W := fun K =>
    ⟨K.1.map (MulAut.conj g).toMonoidHom, isComponent_map_mulEquiv (MulAut.conj g) K.2⟩
  have hσσ : ∀ K, σ (σ K) = K := fun K =>
    Subtype.ext (map_conj_map_conj fun x hx => hg2 x (component_le_layer K.2 hx))
  have hσ1 : ∀ K, (σ K).1 = K.1.map (MulAut.conj g).toMonoidHom := fun _ => rfl
  have hJσ : ∀ K : ComponentIndex W, J ≤ centralizer (K.1 : Set W) →
      J ≤ centralizer ((σ K).1 : Set W) := by
    intro K hJK j hj
    rw [mem_centralizer_iff]
    intro x hx
    rw [hσ1, SetLike.mem_coe, mem_map_conj_iff] at hx
    have h1 : Commute (g⁻¹ * x * g) j := (mem_centralizer_iff.mp (hJK hj)) _ hx
    have h2 := commute_conj g h1
    have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have e2 : g * j * g⁻¹ = j := by rw [(hJg j hj).eq]; group
    rw [e1, e2] at h2
    exact h2.eq
  let cov : Finset (ComponentIndex W) → ComponentIndex W → Prop := fun S K => K ∈ S ∨ σ K ∈ S
  have hcovσ : ∀ S K, cov S K → cov S (σ K) := by
    rintro S K (h | h)
    · exact Or.inr (by rw [hσσ]; exact h)
    · exact Or.inl h
  have key : ∀ y ∈ J, ∀ S : Finset (ComponentIndex W), ∃ r ∈ T ⊓ E,
      ∀ K : ComponentIndex W, (cov S K → ∀ k ∈ K.1, Commute k (r⁻¹ * y)) ∧
        (¬ cov S K → ∀ k ∈ K.1, Commute k r) := by
    intro y hy S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨1, one_mem _, fun K => ⟨fun h => ?_, fun _ k _ => Commute.one_right k⟩⟩
      simp [cov] at h
    | @insert K₀ S hK₀S ih =>
      obtain ⟨r, hr, hrK⟩ := ih
      by_cases hc : cov S K₀
      ·
        refine ⟨r, hr, fun K => ⟨fun hK => (hrK K).1 ?_, fun hK => (hrK K).2 fun h => hK ?_⟩⟩
        · rcases hK with h | h
          · rcases Finset.mem_insert.mp h with h | h
            · rw [h]; exact hc
            · exact Or.inl h
          · rcases Finset.mem_insert.mp h with h | h
            · have hK : K = σ K₀ := by rw [← h, hσσ]
              rw [hK]; exact hcovσ _ _ hc
            · exact Or.inr h
        · rcases h with h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr (Finset.mem_insert_of_mem h)
      · have hcσ : ¬ cov S (σ K₀) := fun h => hc (by rw [← hσσ K₀]; exact hcovσ _ _ h)
        set y' := r⁻¹ * y with hy'
        have hrE : r ∈ E := (mem_inf.mp hr).2
        have hrT : r ∈ T := (mem_inf.mp hr).1
        have hy'E : y' ∈ E := mul_mem (inv_mem hrE) (hJE hy)
        have hy'g : Commute g y' := ((hTgc r hrT).inv_right).mul_right (hJg y hy)
        obtain ⟨r₀, hr₀, hr₀K₀, hr₀σ, hr₀o⟩ : ∃ r₀ ∈ T ⊓ E,
            (∀ k ∈ K₀.1, Commute k (r₀⁻¹ * y')) ∧
            (∀ k ∈ (σ K₀).1, Commute k (r₀⁻¹ * y')) ∧
            (∀ K : ComponentIndex W, K ≠ K₀ → K ≠ σ K₀ → ∀ k ∈ K.1, Commute k r₀) := by
          by_cases hJK : J ≤ centralizer (K₀.1 : Set W)
          ·
            have hJK' := hJσ K₀ hJK
            refine ⟨1, one_mem _, fun k hk => ?_, fun k hk => ?_,
              fun K _ _ k _ => Commute.one_right k⟩
            · rw [inv_one, one_mul]
              exact ((hrK K₀).2 hc k hk).inv_right.mul_right
                ((mem_centralizer_iff.mp (hJK hy)) k hk)
            · rw [inv_one, one_mul]
              exact ((hrK (σ K₀)).2 hcσ k hk).inv_right.mul_right
                ((mem_centralizer_iff.mp (hJK' hy)) k hk)
          obtain ⟨u, hu, huc⟩ := exists_mem_mul_centralizer K₀.2 hy'E
          by_cases hfx : K₀.1.map (MulAut.conj g).toMonoidHom = K₀.1
          ·
            have hσK₀ : σ K₀ = K₀ := Subtype.ext hfx
            refine ⟨u, ⟨hfix _ K₀.2 hJK hfx hu, component_le_layer K₀.2 hu⟩, huc, ?_, ?_⟩
            · rw [hσK₀]; exact huc
            · intro K hK _ k hk
              exact commute_of_ne K.2 K₀.2 (fun h => hK (Subtype.ext h)) hk hu
          ·
            have hne : K₀.1 ≠ (σ K₀).1 := fun h => hfx h.symm
            have hgu : g * u * g⁻¹ ∈ (σ K₀).1 := conj_mem_map_conj hu
            have hcomm : Commute u (g * u * g⁻¹) := commute_of_ne K₀.2 (σ K₀).2 hne hu hgu
            refine ⟨u * (g * u * g⁻¹), ⟨hswap _ K₀.2 hJK hfx u hu, mul_mem
              (component_le_layer K₀.2 hu) (component_le_layer (σ K₀).2 hgu)⟩, ?_, ?_, ?_⟩
            · intro k hk
              have h2 : Commute k (g * u * g⁻¹) := commute_of_ne K₀.2 (σ K₀).2 hne hk hgu
              have e : (u * (g * u * g⁻¹))⁻¹ * y' = (g * u * g⁻¹)⁻¹ * (u⁻¹ * y') := by group
              rw [e]
              exact h2.inv_right.mul_right (huc k hk)
            · intro k hk
              have hk' : g⁻¹ * k * g ∈ K₀.1 := mem_map_conj_iff.mp hk
              have h1 := commute_conj g (huc _ hk')
              have e1 : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
              have e2 : g * (u⁻¹ * y') * g⁻¹ = (g * u * g⁻¹)⁻¹ * y' := by
                have : g * y' * g⁻¹ = y' := by rw [hy'g.eq]; group
                calc g * (u⁻¹ * y') * g⁻¹ = (g * u * g⁻¹)⁻¹ * (g * y' * g⁻¹) := by group
                  _ = (g * u * g⁻¹)⁻¹ * y' := by rw [this]
              rw [e1, e2] at h1
              have h2 : Commute u k := commute_of_ne K₀.2 (σ K₀).2 hne hu hk
              have e : (u * (g * u * g⁻¹))⁻¹ * y' = u⁻¹ * ((g * u * g⁻¹)⁻¹ * y') := by
                rw [hcomm.eq]; group
              rw [e]
              exact h2.symm.inv_right.mul_right h1
            · intro K hK hKσ k hk
              exact (commute_of_ne K.2 K₀.2 (fun h => hK (Subtype.ext h)) hk hu).mul_right
                (commute_of_ne K.2 (σ K₀).2 (fun h => hKσ (Subtype.ext h)) hk hgu)
        refine ⟨r * r₀, mul_mem hr hr₀, fun K => ⟨fun hK k hk => ?_, fun hK k hk => ?_⟩⟩
        · have e : (r * r₀)⁻¹ * y = r₀⁻¹ * y' := by rw [hy']; group
          rw [e]
          by_cases h0 : K = K₀
          · rw [h0] at hk; exact hr₀K₀ k hk
          by_cases h1 : K = σ K₀
          · rw [h1] at hk; exact hr₀σ k hk
          have hKS : cov S K := by
            rcases hK with h | h
            · rcases Finset.mem_insert.mp h with h | h
              · exact absurd h h0
              · exact Or.inl h
            · rcases Finset.mem_insert.mp h with h | h
              · exact absurd (by rw [← h, hσσ]) h1
              · exact Or.inr h
          exact (hr₀o K h0 h1 k hk).inv_right.mul_right ((hrK K).1 hKS k hk)
        · have h0 : K ≠ K₀ := fun h => hK (Or.inl (Finset.mem_insert.mpr (Or.inl h)))
          have h1 : K ≠ σ K₀ := fun h => hK (Or.inr (Finset.mem_insert.mpr (Or.inl (by
            rw [h, hσσ]))))
          have hKS : ¬ cov S K := fun h => hK (by
            rcases h with h | h
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · exact Or.inr (Finset.mem_insert_of_mem h))
          exact ((hrK K).2 hKS k hk).mul_right (hr₀o K h0 h1 k hk)
  have hdec : ∀ y ∈ J, ∃ r ∈ T ⊓ E, r⁻¹ * y ∈ centralizer (E : Set W) := by
    intro y hy
    obtain ⟨r, hr, hrK⟩ := key y hy Finset.univ
    refine ⟨r, hr, ?_⟩
    have hle : E ≤ centralizer ({r⁻¹ * y} : Set W) := by
      rw [hE]
      refine sSup_le fun K hK => fun k hk => ?_
      rw [mem_centralizer_singleton_iff]
      exact ((hrK ⟨K, hK⟩).1 (Or.inl (Finset.mem_univ _)) k hk).eq
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hle hx)
  rw [← hJ]
  refine commutator_le.mpr fun a ha b hb => ?_
  obtain ⟨r, hr, hz⟩ := hdec a ha
  obtain ⟨r', hr', hz'⟩ := hdec b hb
  have hrE : r ∈ E := (mem_inf.mp hr).2
  have hr'E : r' ∈ E := (mem_inf.mp hr').2
  set z := r⁻¹ * a with hzdef
  set z' := r'⁻¹ * b with hz'def
  have ha' : a = r * z := by rw [hzdef]; group
  have hb' : b = r' * z' := by rw [hz'def]; group
  have hz'E : z' ∈ E := mul_mem (inv_mem hr'E) (hJE hb)
  have c1 : ∀ x ∈ E, Commute x z := fun x hx => (mem_centralizer_iff.mp hz) x hx
  have c2 : ∀ x ∈ E, Commute x z' := fun x hx => (mem_centralizer_iff.mp hz') x hx
  have e : ⁅a, b⁆ = ⁅r, r'⁆ := by
    rw [ha', hb', commutatorElement_def, commutatorElement_def]
    have h1 := (c1 r' hr'E).eq
    have h2 := (c1 z' hz'E).eq
    have h5 := (c2 r⁻¹ (inv_mem hrE)).eq
    calc r * z * (r' * z') * (r * z)⁻¹ * (r' * z')⁻¹
        = r * (z * r') * z' * z⁻¹ * r⁻¹ * z'⁻¹ * r'⁻¹ := by group
      _ = r * r' * (z * z') * z⁻¹ * r⁻¹ * z'⁻¹ * r'⁻¹ := by rw [← h1]; group
      _ = r * r' * (z' * z) * z⁻¹ * r⁻¹ * z'⁻¹ * r'⁻¹ := by rw [← h2]
      _ = r * r' * (z' * r⁻¹) * z'⁻¹ * r'⁻¹ := by group
      _ = r * r' * (r⁻¹ * z') * z'⁻¹ * r'⁻¹ := by rw [← h5]
      _ = r * r' * r⁻¹ * r'⁻¹ := by group
  rw [e, commutatorElement_def]
  have hrT := (mem_inf.mp hr).1
  have hr'T := (mem_inf.mp hr').1
  exact mul_mem (mul_mem (mul_mem hrT hr'T) (inv_mem hrT)) (inv_mem hr'T)

omit [Finite W] in
theorem le_normalizer_of_forall_conj_mem {H S : Subgroup W}
    (h : ∀ c ∈ H, ∀ x ∈ S, c * x * c⁻¹ ∈ S) : H ≤ normalizer (S : Set W) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h c hc x hx, fun hx => ?_⟩
  have := h c⁻¹ (inv_mem hc) _ hx
  simpa [mul_assoc] using this

theorem le_pLayer_of_isQuasisimple {C P : Subgroup W} (hPC : P ≤ C) (hq : IsQuasisimple P)
    (hs : (P.subgroupOf C).IsSubnormal) : P ≤ (pLayer ↥C 2).map C.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp : IsComponent (P.subgroupOf C) :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hPC).symm hq, hs⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have hP2 : IsPComponent 2 (P.subgroupOf C) :=
    LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
      (LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp
        (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd))
  have hle : P.subgroupOf C ≤ pLayer ↥C 2 := le_sSup hP2
  calc P = (P.subgroupOf C).map C.subtype := (map_subgroupOf_eq_of_le hPC).symm
    _ ≤ _ := map_mono hle

omit [Finite W] in
theorem isSubnormal_subgroupOf_of_le_normalizer {P D C : Subgroup W} (hPD : P ≤ D) (hDC : D ≤ C)
    (hDn : D ≤ normalizer (P : Set W)) (hCn : C ≤ normalizer (D : Set W)) :
    (P.subgroupOf C).IsSubnormal := by
  have hPD' : P.subgroupOf C ≤ D.subgroupOf C := fun x hx => hPD hx
  refine IsSubnormal.step _ (D.subgroupOf C) hPD' ?_ ?_
  · refine Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hDC).mpr hCn)
  · rw [normal_subgroupOf_iff_le_normalizer hPD']
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hDn (mem_subgroupOf.mp hc)) x

omit [Finite W] in
theorem commute_of_forall_mul {K J : Subgroup W} {g : W} (hK : ⁅K, K⁆ = K)
    (hgK : K.map (MulAut.conj g).toMonoidHom = K) (hJg : ∀ j ∈ J, Commute g j)
    (hcov : ∀ k ∈ K, ∃ j ∈ J, ∀ x ∈ K, Commute x (j⁻¹ * k)) : ∀ k ∈ K, Commute g k := by
  have hgk : ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun k hk => by
    rw [← hgK]; exact conj_mem_map_conj hk
  have hgk' : ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun k hk => by
    rw [← hgK] at hk; exact mem_map_conj_iff.mp hk
  have he : ∀ k ∈ K, ∀ x ∈ K, Commute x (k⁻¹ * (g * k * g⁻¹)) := by
    intro k hk x hx
    obtain ⟨j, hj, hjc⟩ := hcov k hk
    set c := j⁻¹ * k with hc
    have hkc : k = j * c := by rw [hc]; group
    have hgc : Commute x (g * c * g⁻¹) := by
      have h1 := commute_conj g (hjc _ (hgk' x hx))
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [e] at h1
    have e : k⁻¹ * (g * k * g⁻¹) = c⁻¹ * (g * c * g⁻¹) := by
      rw [hkc]
      have h2 := (hJg j hj).eq
      calc (j * c)⁻¹ * (g * (j * c) * g⁻¹) = c⁻¹ * j⁻¹ * (g * j) * c * g⁻¹ := by group
        _ = c⁻¹ * j⁻¹ * (j * g) * c * g⁻¹ := by rw [h2]
        _ = c⁻¹ * (g * c * g⁻¹) := by group
    rw [e]
    exact (hjc x hx).inv_right.mul_right hgc
  have hcomm : ⁅K, K⁆ ≤ K ⊓ centralizer ({g} : Set W) := by
    refine commutator_le.mpr fun a ha b hb => mem_inf.mpr ⟨commutator_mem_commutator ha hb |>
      fun h => (commutator_le_self K h : _), ?_⟩
    rw [mem_centralizer_singleton_iff]
    set ea := a⁻¹ * (g * a * g⁻¹) with hea
    set eb := b⁻¹ * (g * b * g⁻¹) with heb
    have hga : g * a * g⁻¹ = a * ea := by rw [hea]; group
    have hgb : g * b * g⁻¹ = b * eb := by rw [heb]; group
    have h1 : b * ea = ea * b := (he a ha b hb).eq
    have hebK : eb ∈ K := mul_mem (inv_mem hb) (hgk b hb)
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

theorem le_pLayer_centralizer {J : Subgroup W} (hJ : ⁅J, J⁆ = J) (hJE : J ≤ layer W) {g : W}
    (hJg : ∀ j ∈ J, Commute g j) (hg2 : ∀ x ∈ layer W, g ^ 2 * x = x * g ^ 2)
    (hfixc : ∀ K : Subgroup W, IsComponent K → ¬ J ≤ centralizer (K : Set W) →
      K.map (MulAut.conj g).toMonoidHom = K → ∀ k ∈ K, Commute g k) :
    J ≤ (pLayer ↥(centralizer ({g} : Set W)) 2).map (centralizer ({g} : Set W)).subtype := by
  set C := centralizer ({g} : Set W) with hC
  refine le_of_pieces hJ hJE hJg hg2 (map_subtype_le _) (fun K hK hJK hgK => ?_)
    (fun K hK hJK hgK u hu => ?_)
  · have hKC : K ≤ C := fun k hk => mem_centralizer_singleton_iff.mpr
      (hfixc K hK hJK hgK k hk).symm
    exact le_pLayer_of_isQuasisimple hKC hK.1 hK.2.subgroupOf
  ·
    set K' := K.map (MulAut.conj g).toMonoidHom with hK'
    have hK'c : IsComponent K' := isComponent_map_mulEquiv (MulAut.conj g) hK
    have hne : K ≠ K' := fun h => hgK h.symm
    have hcK : ∀ v ∈ K, ∀ w ∈ K, Commute w (g * v * g⁻¹) := fun v hv w hw =>
      commute_of_ne hK hK'c hne hw (conj_mem_map_conj hv)
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
        exact Subtype.ext (commute_of_ne hK hK'c hne a.2 (hKK' b b.2)).eq
      have := isQuasisimple_map htop δ hker
      rwa [← MonoidHom.range_eq_map] at this
    have hδC : δ.range ≤ C := by
      rintro _ ⟨v, rfl⟩
      rw [hδ, hC, mem_centralizer_singleton_iff]
      have h2 := hg2 v (hKE v.2)
      rw [pow_two] at h2
      have h3 := (hcK v v.2 v v.2).eq
      have key : g * ((v : W) * (g * v * g⁻¹)) * g⁻¹ = (v : W) * (g * v * g⁻¹) := by
        calc g * ((v : W) * (g * v * g⁻¹)) * g⁻¹ =
            (g * v * g⁻¹) * (g * g * v * (g * g)⁻¹) := by group
          _ = (g * v * g⁻¹) * (v * (g * g) * (g * g)⁻¹) := by rw [h2]
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
    have hT := le_pLayer_of_isQuasisimple hδC hq
      (isSubnormal_subgroupOf_of_le_normalizer (le_inf hδE hδC) inf_le_right hDn hCn)
    exact hT ⟨⟨u, hu⟩, rfl⟩

end CFSG.ComponentClassification.Sol76
