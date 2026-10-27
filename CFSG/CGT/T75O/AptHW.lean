module

public import CFSG.Timmesfeld.ARS.CaseHAdX

public section

namespace CFSG.CGT.T75O

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseH CFSG.Timmesfeld.ARS.Sec8Field

namespace Apt

theorem isPGroup_multiplicative {E : Type} [Field E] [CharP E 2] : IsPGroup 2 (Multiplicative E) :=
  fun s => ⟨1, by
    rw [pow_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    change 2 • Multiplicative.toAdd s = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _⟩

end Apt

variable {G : Type} [Group G] {R : Set (Subgroup G)}
  {A A₀ P P' : Subgroup G} {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E]

namespace Apt

theorem ad_congr {g g' : G} (h : g = g') (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hg' : g' ∈ Subgroup.normalizer (A : Set G)) (v : S.V) : S.ad hg v = S.ad hg' v := by
  subst h
  rfl

theorem ad_x1_zero (c : Coords S F E) (v : S.V) :
    S.ad (c.x1_mem_normalizer 0) v = v := by
  rw [S.ad_apply]
  have h : (⟨c.x1 0 * ↑(S.lift v) * (c.x1 0)⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root
      (c.x1_mem_normalizer 0) (S.lift v).2⟩ : ↥(M R A)) = S.lift v :=
    Subtype.ext (by simp [c.x1_zero])
  rw [h, S.proj_lift]

theorem ad_x1_add (c : Coords S F E) (s s' : E) (v : S.V) :
    S.ad (c.x1_mem_normalizer (s + s')) v =
      S.ad (c.x1_mem_normalizer s) (S.ad (c.x1_mem_normalizer s') v) := by
  rw [← S.ad_mul (c.x1_mem_normalizer s) (c.x1_mem_normalizer s') v]
  exact ad_congr (c.x1_add s s') _ _ v

@[instance_reducible] noncomputable def xAct (c : Coords S F E) (W : Subgroup S.V)
    (hW : ∀ s : E, ∀ w ∈ W, S.ad (c.x1_mem_normalizer s) w ∈ W) :
    MulAction (Multiplicative E) W where
  smul s w := ⟨S.ad (c.x1_mem_normalizer (Multiplicative.toAdd s)) w, hW _ w w.2⟩
  one_smul w := Subtype.ext (by
    change S.ad (c.x1_mem_normalizer (Multiplicative.toAdd 1)) w = w
    rw [toAdd_one]
    exact ad_x1_zero c w)
  mul_smul s s' w := Subtype.ext (by
    change S.ad (c.x1_mem_normalizer (Multiplicative.toAdd (s * s'))) w = S.ad _ (S.ad _ w)
    rw [toAdd_mul]
    exact ad_x1_add c _ _ w)

theorem exists_fixed [CharP E 2] (c : Coords S F E) (W : Subgroup S.V)
    (hW : ∀ s : E, ∀ w ∈ W, S.ad (c.x1_mem_normalizer s) w ∈ W) (hW2 : IsPGroup 2 W)
    [Finite W] (hnt : Nontrivial W) :
    ∃ w ∈ W, w ≠ 1 ∧ ∀ s : E, S.ad (c.x1_mem_normalizer s) w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let inst := xAct c W hW
  obtain ⟨n, hn, hcard⟩ := (hW2.nontrivial_iff_card).1 hnt
  have hdvd : 2 ∣ Nat.card W := hcard ▸ dvd_pow_self 2 hn.ne'
  have h1 : (1 : W) ∈ MulAction.fixedPoints (Multiplicative E) W := fun s =>
    Subtype.ext (map_one _)
  obtain ⟨b, hb, hne⟩ :=
    (isPGroup_multiplicative (E := E)).exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd
      h1
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), fun s => ?_⟩
  have := hb (Multiplicative.ofAdd s)
  exact congrArg Subtype.val this

theorem le_of_fixed [CharP E 2] [Finite G] (c : Coords S F E)
    (hfix : ∀ (u : F) (w r : E) (v : F),
      (∀ s : E, S.ad (c.x1_mem_normalizer s) (c.vc u w r v) = c.vc u w r v) →
        u = 0 ∧ w = 0 ∧ r = 0)
    {T : Subgroup G} (hAT : A ≤ T) (hTM : T ≤ M R A) (hT2 : IsPGroup 2 T)
    (hNT : ∀ s : E, ∀ t ∈ T, c.x1 s * t * (c.x1 s)⁻¹ ∈ T)
    (hTP' : ∀ v : F, c.x2 v ∈ T → v = 0) : T ≤ A := by
  by_contra hTA
  let W : Subgroup S.V := (T.subgroupOf (M R A)).map S.proj
  have hWmem : ∀ w ∈ W, ∃ t : G, ∃ ht : t ∈ T, w = S.proj ⟨t, hTM ht⟩ := fun w hw => by
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw
    exact ⟨x.1, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  have hW : ∀ s : E, ∀ w ∈ W, S.ad (c.x1_mem_normalizer s) w ∈ W := fun s w hw => by
    obtain ⟨t, ht, rfl⟩ := hWmem w hw
    rw [← S.proj_conj_eq_ad (c.x1_mem_normalizer s) ⟨t, hTM ht⟩
      (conj_mem_M_of_mem_normalizer S.hyp.root (c.x1_mem_normalizer s) (hTM ht))]
    exact Subgroup.mem_map.2 ⟨⟨_, conj_mem_M_of_mem_normalizer S.hyp.root (c.x1_mem_normalizer s)
      (hTM ht)⟩, Subgroup.mem_subgroupOf.2 (hNT s t ht), rfl⟩
  have hW2 : IsPGroup 2 W := (hT2.comap_subtype (K := M R A)).map S.proj
  obtain ⟨t₀, ht₀, ht₀A⟩ := Set.not_subset.1 hTA
  have hne : S.proj ⟨t₀, hTM ht₀⟩ ≠ 1 := fun h => by
    obtain ⟨a, ha, hdec⟩ := S.exists_eq_mul ⟨t₀, hTM ht₀⟩
    rw [h] at hdec
    apply ht₀A
    have : t₀ = a := by simpa using hdec
    rw [this]
    exact ha
  have hnt : Nontrivial W := ⟨⟨⟨S.proj ⟨t₀, hTM ht₀⟩, Subgroup.mem_map.2 ⟨⟨t₀, hTM ht₀⟩,
    Subgroup.mem_subgroupOf.2 ht₀, rfl⟩⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  have : Finite W := inferInstance
  obtain ⟨w, hwW, hw1, hwfix⟩ := exists_fixed c W hW hW2 hnt
  obtain ⟨u, w', r, v, rfl⟩ := c.vc_surjective w
  obtain ⟨rfl, rfl, rfl⟩ := hfix u w' r v hwfix
  obtain ⟨t, ht, hteq⟩ := hWmem _ hwW
  obtain ⟨a₀, ha₀, hdec⟩ := S.exists_eq_mul ⟨t, hTM ht⟩
  rw [← hteq] at hdec
  have hdec' : t = c.x2 v * a₀ := by
    simpa [Coords.vc, c.x6_zero, c.x5_zero, c.x3_zero] using hdec
  have hx2 : c.x2 v ∈ T := by
    have : c.x2 v = t * a₀⁻¹ := by rw [hdec']; group
    rw [this]
    exact T.mul_mem ht (T.inv_mem (hAT ha₀))
  have hv := hTP' v hx2
  rw [hv, c.vc_zero] at hw1
  exact hw1 rfl

end Apt

end CFSG.CGT.T75O
