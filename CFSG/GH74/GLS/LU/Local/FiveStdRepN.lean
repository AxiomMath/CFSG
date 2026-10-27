module

public import CFSG.GH74.GLS.LU.Local.FiveStdBase
public import CFSG.GH74.GLS.LU.Local.FiveStdRepA2

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

namespace FiveStdRep

theorem checkN_spec {u a b : E} (h : checkN u a b = true) :
    noInvCheck (ppE a b 4 4) = true ∧ sylowTorusCheck (PlOf u) = true := by
  unfold checkN at h
  simpa only [Bool.and_eq_true] using h

theorem aux_mod (n : ℕ) (h : (n % 2 != 0 && n % 5 != 0) = false) : n % 2 = 0 ∨ n % 5 = 0 := by
  by_contra hc
  rw [not_or] at hc
  simp [hc.1, hc.2] at h

theorem noInvCheck_spec {H0 : List E} (h : noInvCheck H0 = true) :
    (∀ e ∈ Cs, ordE e % 2 = 0 ∨ ordE e % 5 = 0 ∨ ordE e = 1 ∨ ordE e = 3) ∧
    (∀ r ∈ Cs, ordE r = 3 → ∃ h1 ∈ H0, ∃ h2 ∈ H0,
      ordE (mulE (conjE h1 r) (conjE h2 r)) % 2 = 0 ∨ ordE (mulE (conjE h1 r) (conjE h2 r)) % 5 = 0) := by
  unfold noInvCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.any_eq_true, List.mem_map, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun e he => ?_, fun r hr hr3 => ?_⟩
  · rcases h1 e he with (h | h) | h
    · rcases aux_mod _ h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · obtain ⟨x1, ⟨a1, ha1, rfl⟩, x2, ⟨a2, ha2, rfl⟩, hord⟩ := h2 r ⟨hr, hr3⟩
    exact ⟨a1, ha1, a2, ha2, hord⟩

theorem mem_z4pairs_iff {els : List E} {a b : E} :
    (a, b) ∈ z4pairs els ↔ a ∈ els ∧ b ∈ els ∧ commE a b = true ∧ nodupL (ppE a b 4 4) = true := by
  unfold z4pairs
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨a', ha', b', hb', h⟩
    by_cases hT : (commE a' b' && nodupL (ppE a' b' 4 4)) = true
    · simp only [hT, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Bool.and_eq_true] at hT
      exact ⟨ha', hb', hT.1, hT.2⟩
    · simp [hT] at h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨a, h1, b, h2, ?_⟩
    have hT : (commE a b && nodupL (ppE a b 4 4)) = true := by rw [Bool.and_eq_true]; exact ⟨h3, h4⟩
    simp [hT]

theorem sylowTorusCheck_spec {Pl : List E} (h : sylowTorusCheck Pl = true) :
    ∀ q ∈ Syl36, ∀ p ∈ z4pairs (Pl.filter fun x => ordE x == 4),
      normAll [p.1, p.2] [q.1, q.2.1] q.2.2 = true → normK p.1 = true ∧ normK p.2 = true := by
  unfold sylowTorusCheck at h
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
  intro q hq p hp hn
  rcases h q hq p hp with h' | h'
  · rw [hn] at h'
    exact absurd h' (by simp)
  · exact h'

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

omit [Finite G] in
theorem orderOf_eq_ordE_of_ne {e : E} (he : validE e = true) (h : ordE e ≠ 301) :
    orderOf (st.ι e) = ordE e := by
  rcases st.model.ordE_spec he with ⟨h1, -⟩ | ⟨h1, -, -⟩
  · exact absurd h1 h
  · exact st.model.orderOf_of_ordE he rfl (by omega)

theorem noInv_part (hb : baseCheck = true) {t u a b : E} (hu : validE u = true) (hab : (a, b) ∈ tpOf u)
    (hP : checkP t u a b = true) (hN : noInvCheck (ppE a b 4 4) = true) :
    ∀ H' : Subgroup G, IsTorus st.z (st.ι u) st.K₁ st.K₂ H' → ∀ R : Subgroup G, R ≤ Cz st.z →
      (∀ h ∈ H', cjL h R = R) → (∀ r ∈ R, ¬ 2 ∣ orderOf r ∧ ¬ 5 ∣ orderOf r) → R = ⊥ := by
  obtain ⟨hn1, hn2⟩ := noInvCheck_spec hN
  have hord : ∀ e : E, validE e = true → ordE e ≠ 301 := by
    intro e he h301
    have := hn1 e ((mem_Cs_iff e).2 he)
    omega
  have hord' : ∀ e : E, validE e = true → orderOf (st.ι e) = ordE e :=
    fun e he => orderOf_eq_ordE_of_ne st he (hord e he)
  intro H' hH' R hRC hHR hR
  have hS := torus_set_eq st hb hu hab hP hH'
  obtain ⟨haP, hbP, -⟩ := mem_tpOf_iff.1 hab
  have hva : validE a = true := V_PlOf u a haP
  have hvb : validE b = true := V_PlOf u b hbP
  have hVH : V (ppE a b 4 4) := st.model.V_ppE hva hvb 4 4
  by_contra hne
  obtain ⟨⟨r, hrR⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨rE, hvr, rfl⟩ := st.mem_C_iff.1 (hRC hrR)
  have h2 := hR _ hrR
  rw [hord' rE hvr] at h2
  have hmem : rE ∈ Cs := (mem_Cs_iff rE).2 hvr
  have hr3 : ordE rE = 3 := by
    rcases hn1 rE hmem with h | h | h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) h2.1
    · exact absurd (Nat.dvd_of_mod_eq_zero h) h2.2
    · exact absurd (orderOf_eq_one_iff.1 ((hord' rE hvr).trans h)) hr1'
    · exact h
  obtain ⟨h1, hh1, h2', hh2, hmod⟩ := hn2 rE hmem hr3
  have hv1 := hVH h1 hh1
  have hv2 := hVH h2' hh2
  have hH1 : st.ι h1 ∈ H' := by
    rw [← SetLike.mem_coe, hS]
    exact mem_S.2 ⟨h1, hh1, rfl⟩
  have hH2 : st.ι h2' ∈ H' := by
    rw [← SetLike.mem_coe, hS]
    exact mem_S.2 ⟨h2', hh2, rfl⟩
  have hx1 : st.ι (conjE h1 rE) ∈ R := by
    rw [st.model.map_conjE hv1 hvr]
    have := repCj_mem_self (g := st.ι h1) hrR
    rwa [hHR _ hH1] at this
  have hx2 : st.ι (conjE h2' rE) ∈ R := by
    rw [st.model.map_conjE hv2 hvr]
    have := repCj_mem_self (g := st.ι h2') hrR
    rwa [hHR _ hH2] at this
  have hvx1 := st.model.valid_conjE hv1 hvr
  have hvx2 := st.model.valid_conjE hv2 hvr
  have hxy : st.ι (mulE (conjE h1 rE) (conjE h2' rE)) ∈ R := by
    rw [st.model.map_mul _ _ hvx1 hvx2]
    exact R.mul_mem hx1 hx2
  have hvxy := st.model.valid_mul _ _ hvx1 hvx2
  have h3 := hR _ hxy
  rw [hord' _ hvxy] at h3
  rcases hmod with h | h
  · exact h3.1 (Nat.dvd_of_mod_eq_zero h)
  · exact h3.2 (Nat.dvd_of_mod_eq_zero h)

theorem sylow_part (hb : baseCheck = true) (hs : sylCover = true) {u : E} (hu : validE u = true)
    (hS : sylowTorusCheck (PlOf u) = true) :
    ∀ A : Subgroup G, (∀ h ∈ A, h * st.z = st.z * h ∧ h * st.ι u = st.ι u * h) →
      Nonempty (↥A ≃* Z4Z4) → (∃ R : Subgroup G, IsSylowIn 5 R (Cz st.z) ∧ ∀ h ∈ A, cjL h R = R) →
      ∀ h ∈ A, cjL h st.K₁ = st.K₁ ∧ cjL h st.K₂ = st.K₂ := by
  intro A hA ⟨f⟩ ⟨R, hR, hRA⟩
  obtain ⟨a, b, hva, hvb, haP, hbP, h4a, h4b, hc, hn, haA, hbA, hAS⟩ := exists_pair_of_torus st hb hu hA f
  obtain ⟨q, hq, hRq⟩ := FiveStdSetting.sylow_cover st hb hs R hR
  obtain ⟨gx, hgx, gy, hgy, rfl⟩ := FiveStdBase.mem_Syl36.1 hq
  obtain ⟨hgxK, -⟩ := FiveStdBase.X1cands_spec hgx
  obtain ⟨hgyK, -⟩ := FiveStdBase.Y1cands_spec hgy
  obtain ⟨-, hK1, hK2, -⟩ := baseCheck_spec hb
  have hvgx : validE gx = true := hK1 gx hgxK
  have hvgy : validE gy = true := hK2 gy hgyK
  have hVq : V (ppE gx gy 5 5) := st.model.V_ppE hvgx hvgy 5 5
  have hRq' : (R : Set G) = S st.ι (ppE gx gy 5 5) := hRq
  have hgxS : st.ι gx ∈ S st.ι (ppE gx gy 5 5) := by
    rw [st.model.S_ppE hvgx hvgy]
    exact ⟨1, by norm_num, 0, by norm_num, by simp⟩
  have hgyS : st.ι gy ∈ S st.ι (ppE gx gy 5 5) := by
    rw [st.model.S_ppE hvgx hvgy]
    exact ⟨0, by norm_num, 1, by norm_num, by simp⟩
  have hnorm : normAll [a, b] [gx, gy] (ppE gx gy 5 5) = true := by
    rw [st.model.normAll_iff (V_cons hva (V_cons hvb V_nil)) (V_cons hvgx (V_cons hvgy V_nil)) hVq]
    intro h hh x hx
    have hhA : st.ι h ∈ A := by
      rcases List.mem_cons.1 hh with rfl | hh
      · exact haA
      · rcases List.mem_cons.1 hh with rfl | hh
        · exact hbA
        · simp at hh
    have hxS : st.ι x ∈ S st.ι (ppE gx gy 5 5) := by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hgxS
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hgyS
        · simp at hx
    have hxR : st.ι x ∈ R := by
      rw [← SetLike.mem_coe, hRq']
      exact hxS
    have h1 := repCj_mem_self (g := st.ι h) hxR
    rw [hRA _ hhA, ← SetLike.mem_coe, hRq'] at h1
    exact h1
  have hmem : (a, b) ∈ z4pairs ((PlOf u).filter fun x => ordE x == 4) :=
    mem_z4pairs_iff.2 ⟨List.mem_filter.2 ⟨haP, by simpa using h4a⟩, List.mem_filter.2 ⟨hbP, by simpa using h4b⟩,
      hc, hn⟩
  obtain ⟨hna, hnb⟩ := sylowTorusCheck_spec hS (gx, gy, ppE gx gy 5 5) hq (a, b) hmem hnorm
  have hNa := mem_inf_normalizer.2 ((normK_iff st hb hva).1 hna)
  have hNb := mem_inf_normalizer.2 ((normK_iff st hb hvb).1 hnb)
  have hle : A ≤ normalizer (st.K₁ : Set G) ⊓ normalizer (st.K₂ : Set G) := by
    intro x hx
    have hx' : x ∈ S st.ι (ppE a b 4 4) := by rw [← hAS]; exact hx
    rw [st.model.S_ppE hva hvb] at hx'
    obtain ⟨i, -, j, -, rfl⟩ := hx'
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hNa i) (Subgroup.pow_mem _ hNb j)
  intro h hh
  exact mem_inf_normalizer.1 (hle hh)

end FiveStdRep

namespace FiveStdSetting

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

open FiveStdRep

theorem rep_N (hb : baseCheck = true) (hs : sylCover = true) {tE uE : E} (hp : pairCond tE uE = true)
    (hr : checkRep tE uE = true) :
    (∀ H' : Subgroup G, IsTorus st.z (st.ι uE) st.K₁ st.K₂ H' → ∀ R : Subgroup G, R ≤ Cz st.z →
      (∀ h ∈ H', cjL h R = R) → (∀ r ∈ R, ¬ 2 ∣ orderOf r ∧ ¬ 5 ∣ orderOf r) → R = ⊥) ∧
    (∀ A : Subgroup G, (∀ h ∈ A, h * st.z = st.z * h ∧ h * st.ι uE = st.ι uE * h) →
      Nonempty (↥A ≃* Z4Z4) → (∃ R : Subgroup G, IsSylowIn 5 R (Cz st.z) ∧ ∀ h ∈ A, cjL h R = R) →
      ∀ h ∈ A, cjL h st.K₁ = st.K₁ ∧ cjL h st.K₂ = st.K₂) := by
  obtain ⟨-, hu⟩ := pairCond_valid hb hp
  obtain ⟨a, b, hab, hP, -, hN⟩ := checkRep_spec hr
  obtain ⟨hN1, hN2⟩ := checkN_spec hN
  exact ⟨noInv_part st hb hu hab hP hN1, sylow_part st hb hs hu hN2⟩

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five
