module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2Fixed
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Glue

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6

section Fixed


@[reducible] noncomputable def f4Fixed (K : Type) [Field K] : Subgroup (adjointGroup .E6 K) :=
  (twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subgroupOf _

noncomputable def f4Iso (K : Type) [Field K] : adjointGroup .F4 K ≃* f4Fixed K :=
  (e6FixedF4EquivAll K).symm.trans
    (Subgroup.subgroupOfEquivOfLe (twistedFixedGroup_le_adjointGroup TwistTag.E6 K (RingHom.id K))).symm

noncomputable def f4Embed (K : Type) [Field K] : adjointGroup .F4 K →* adjointGroup .E6 K :=
  (f4Fixed K).subtype.comp (f4Iso K).toMonoidHom

theorem f4Embed_injective (K : Type) [Field K] : Function.Injective (f4Embed K) :=
  Subtype.val_injective.comp (f4Iso K).injective

theorem range_f4Embed (K : Type) [Field K] : (f4Embed K).range = f4Fixed K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (f4Iso K y).2
  · intro hx
    exact ⟨(f4Iso K).symm ⟨x, hx⟩, by simp [f4Embed]⟩

def xEl (K : Type) [Field K] (i : Fin Tag.E6.rank) (c : K) : adjointGroup .E6 K :=
  ⟨xUnit Tag.E6 K i c, xUnit_mem_adjointGroup i c⟩

def yEl (K : Type) [Field K] (i : Fin Tag.E6.rank) (c : K) : adjointGroup .E6 K :=
  ⟨yUnit Tag.E6 K i c, yUnit_mem_adjointGroup i c⟩

theorem xEl_node4_mem_f4Fixed (K : Type) [Field K] (c : K) :
    xEl K (e6Index 3) c ∈ f4Fixed K ∧ yEl K (e6Index 3) c ∈ f4Fixed K := by
  have h := xyUnit_mem_fixed_of_orbitWord_eq K ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c
  exact ⟨Subgroup.mem_subgroupOf.mpr h.1, Subgroup.mem_subgroupOf.mpr h.2⟩

end Fixed

section Closing


theorem eq_top_of_simpleRootOps (K : Type) [Field K] (M : Subgroup (adjointGroup .E6 K))
    (h : ∀ (i : Fin Tag.E6.rank) (c : K), xEl K i c ∈ M ∧ yEl K i c ∈ M) : M = ⊤ := by
  rw [eq_top_iff]
  set N : Subgroup (ModGL Tag.E6 K) := M.map (adjointGroup .E6 K).subtype with hN
  have hgen : adjointGroup .E6 K ≤ N := by
    unfold adjointGroup
    rw [Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have h1 : xEl K i c ∈ M := (h i c).1
      have hg' : g = xUnit Tag.E6 K i c := Units.ext hg
      refine ⟨xEl K i c, h1, ?_⟩
      simp only [Subgroup.coe_subtype, xEl]
      exact hg'.symm
    · have h1 : yEl K i c ∈ M := (h i c).2
      have hg' : g = yUnit Tag.E6 K i c := Units.ext hg
      refine ⟨yEl K i c, h1, ?_⟩
      simp only [Subgroup.coe_subtype, yEl]
      exact hg'.symm
  intro x _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hgen x.2)
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem closure_f4Fixed_union_centralizer_eq_top (K : Type) [Field K] (t : adjointGroup .E6 K)
    (ht : ∀ (i : Fin Tag.E6.rank), i ≠ e6Index 3 → ∀ c : K,
      Commute t (xEl K i c) ∧ Commute t (yEl K i c)) :
    Subgroup.closure ((f4Fixed K : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) = ⊤ := by
  classical
  apply eq_top_of_simpleRootOps K
  intro i c
  by_cases hi : i = e6Index 3
  · subst hi
    exact ⟨Subgroup.subset_closure (Or.inl (xEl_node4_mem_f4Fixed K c).1),
      Subgroup.subset_closure (Or.inl (xEl_node4_mem_f4Fixed K c).2)⟩
  · obtain ⟨hx, hy⟩ := ht i hi c
    refine ⟨Subgroup.subset_closure (Or.inr ?_), Subgroup.subset_closure (Or.inr ?_)⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hy.symm

theorem closure_conj_eq_top (K : Type) [Field K] (R : Subgroup (adjointGroup .E6 K))
    (k : adjointGroup .E6 K) (hk : k ∈ R) (z : adjointGroup .E6 K)
    (h : Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) = ⊤) :
    Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({k⁻¹ * z * k} : Set (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K))) = ⊤ := by
  classical
  set M := Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({k⁻¹ * z * k} : Set (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K))) with hM
  have hconj : ∀ x ∈ Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))),
      k⁻¹ * x * k ∈ M := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hxR | hxC
      · apply Subgroup.subset_closure
        left
        have : k⁻¹ * x * k ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hk) hxR) hk
        exact this
      · apply Subgroup.subset_closure
        right
        simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
          forall_eq] at hxC ⊢
        calc k⁻¹ * z * k * (k⁻¹ * x * k) = k⁻¹ * (z * x) * k := by group
          _ = k⁻¹ * (x * z) * k := by rw [hxC]
          _ = (k⁻¹ * x * k) * (k⁻¹ * z * k) := by group
    | one => simp
    | mul x y _ _ hx hy =>
      have : k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
      rw [this]
      exact M.mul_mem hx hy
    | inv x _ hx =>
      have : k⁻¹ * x⁻¹ * k = (k⁻¹ * x * k)⁻¹ := by group
      rw [this]
      exact M.inv_mem hx
  rw [eq_top_iff]
  intro y _
  have hy : k * y * k⁻¹ ∈ Subgroup.closure ((R : Set (adjointGroup .E6 K)) ∪
      (Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) : Set (adjointGroup .E6 K))) := by
    rw [h]
    exact Subgroup.mem_top _
  have := hconj _ hy
  have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  rwa [e] at this

section Glue

theorem e6HighInF4_of_closing {ε : ℕ}
    (hConj : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
      ∀ E₀ : Subgroup (adjointGroup .E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
        ¬ NormalizesRNative .E6 K E₀ →
        ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (f4Embed K).range)
    (hClose : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = ε →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((f4Embed K).range ∪
          (Subgroup.centralizer ({f4Embed K e} : Set (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = ⊤) :
    E6HighInF4 ε := by
  intro K _ _ hK E₀ hexp hcard hn
  obtain ⟨g, hg⟩ := hConj K hK E₀ hexp hcard hn
  set E₁ : Subgroup (adjointGroup .E6 K) := E₀.map (MulAut.conj g).toMonoidHom with hE₁def
  have hE₁le : E₁ ≤ (f4Embed K).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hι := f4Embed_injective K
  set E₃ : Subgroup (adjointGroup .F4 K) := E₁.comap (f4Embed K) with hE₃def
  have hE₃map : E₃.map (f4Embed K) = E₁ := Subgroup.map_comap_eq_self hE₁le
  have hcardE₁ : Nat.card E₁ = 3 ^ 2 := by
    rw [hE₁def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map (f4Embed K)) = Nat.card E₃ :=
      Subgroup.card_map_of_injective hι
    rw [← h1, hE₃map, hcardE₁]
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    have hmem : (f4Embed K) x ∈ E₀.map (MulAut.conj g).toMonoidHom := hx
    obtain ⟨y, hy, hyx⟩ := hmem
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hnF : ¬ NormalizesRNative .F4 K E₃ :=
    not_normalizesRIn_comap_of_map (f4Embed K) hι g hn E₃ hE₃map
  obtain ⟨e, he, he1, hcl⟩ := hClose K hK E₃ hexp₃ hcardE₃ hnF
  exact ⟨g, f4Embed K, E₃, hι, hE₃map, e, he, he1, hcl⟩

theorem exists_units_orderOf_three (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hdvd : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    have h1 : 1 ≤ Nat.card K := Nat.card_pos
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  exact ⟨ω, hω⟩

theorem hClose_one_of_purity
    (hReg : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ D : LangPlaneData .F4 K E₃, ∀ α, IsRoot .F4 α → ¬ D.Kills α)
    (hPure : F4PureSplit)
    (hCent : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 → ∀ ω : Kˣ, orderOf ω = 3 →
      ∀ (i : Fin Tag.E6.rank), i ≠ e6Index 3 → ∀ c : K,
        Commute (f4Embed K (zSplit K ω)) (xEl K i c) ∧ Commute (f4Embed K (zSplit K ω)) (yEl K i c)) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((f4Embed K).range ∪
          (Subgroup.centralizer ({f4Embed K e} : Set (adjointGroup .E6 K)) :
            Set (adjointGroup .E6 K))) = ⊤ := by
  intro K _ _ hK E₃ hexp hcard hnF
  obtain ⟨ω, hω⟩ := exists_units_orderOf_three K hK
  obtain ⟨D, hD⟩ := hReg K hK E₃ hexp hcard hnF
  have hnt : Nontrivial E₃ := by
    haveI : Fintype E₃ := Fintype.ofFinite E₃
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨x, hx⟩ := exists_ne (1 : E₃)
  have he1 : (x : adjointGroup .F4 K) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨g, hg⟩ := hPure K hK ω hω E₃ hexp hcard D hD x x.2 he1
  refine ⟨x, x.2, he1, ?_⟩
  have hez : f4Embed K x = (f4Embed K g)⁻¹ * f4Embed K (zSplit K ω) * f4Embed K g := by
    have hx' : (x : adjointGroup .F4 K) = g⁻¹ * zSplit K ω * g := by
      rw [← hg]
      group
    rw [hx', map_mul, map_mul, map_inv]
  rw [hez]
  have hk : f4Embed K g ∈ (f4Embed K).range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hfix := closure_f4Fixed_union_centralizer_eq_top K (f4Embed K (zSplit K ω))
    (fun i hi c => hCent K hK ω hω i hi c)
  rw [← range_f4Embed] at hfix
  exact closure_conj_eq_top K (f4Embed K).range (f4Embed K g) hk _ hfix

theorem e6HighInF4_one_of_purity
    (hConj : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
      ∀ E₀ : Subgroup (adjointGroup .E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
        ¬ NormalizesRNative .E6 K E₀ →
        ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (f4Embed K).range)
    (hReg : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
      ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
        ¬ NormalizesRNative .F4 K E₃ →
        ∃ D : LangPlaneData .F4 K E₃, ∀ α, IsRoot .F4 α → ¬ D.Kills α)
    (hPure : F4PureSplit)
    (hCent : ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 → ∀ ω : Kˣ, orderOf ω = 3 →
      ∀ (i : Fin Tag.E6.rank), i ≠ e6Index 3 → ∀ c : K,
        Commute (f4Embed K (zSplit K ω)) (xEl K i c) ∧ Commute (f4Embed K (zSplit K ω)) (yEl K i c)) :
    E6HighInF4 1 :=
  e6HighInF4_of_closing hConj (hClose_one_of_purity hReg hPure hCent)

end Glue

end Closing

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
