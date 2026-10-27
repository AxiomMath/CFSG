module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem case4_decomp {G : Type} [Group G] {C U Z : Subgroup G} (hCZ : C ≤ Z) (hUZ : U ≤ Z)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hsum : Z = C ⊔ U) :
    ∀ z : G, z ∈ Z → ∃ c u : G, c ∈ C ∧ u ∈ U ∧ z = c * u := by
  let S : Subgroup G :=
    { carrier := {z | ∃ c u : G, c ∈ C ∧ u ∈ U ∧ z = c * u}
      mul_mem' := by
        rintro _ _ ⟨c₁, u₁, hc₁, hu₁, rfl⟩ ⟨c₂, u₂, hc₂, hu₂, rfl⟩
        refine ⟨c₁ * c₂, u₁ * u₂, C.mul_mem hc₁ hc₂, U.mul_mem hu₁ hu₂, ?_⟩
        have h : u₁ * c₂ = c₂ * u₁ := hcomm _ (hUZ hu₁) _ (hCZ hc₂)
        calc c₁ * u₁ * (c₂ * u₂) = c₁ * (u₁ * c₂) * u₂ := by group
          _ = c₁ * (c₂ * u₁) * u₂ := by rw [h]
          _ = c₁ * c₂ * (u₁ * u₂) := by group
      one_mem' := ⟨1, 1, C.one_mem, U.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨c, u, hc, hu, rfl⟩
        refine ⟨c⁻¹, u⁻¹, C.inv_mem hc, U.inv_mem hu, ?_⟩
        have h : u * c = c * u := hcomm _ (hUZ hu) _ (hCZ hc)
        calc (c * u)⁻¹ = (u * c)⁻¹ := by rw [h]
          _ = c⁻¹ * u⁻¹ := by simp }
  have hZS : Z ≤ S := by
    rw [hsum]
    exact sup_le (fun c hc => ⟨c, 1, hc, U.one_mem, by simp⟩)
      (fun u hu => ⟨1, u, C.one_mem, hu, by simp⟩)
  exact fun z hz => hZS hz

theorem case4_uniq {G : Type} [Group G] {C U : Subgroup G} (hdisj : C ⊓ U = ⊥)
    {c c' u u' : G} (hc : c ∈ C) (hc' : c' ∈ C) (hu : u ∈ U) (hu' : u' ∈ U)
    (h : c * u = c' * u') : c = c' ∧ u = u' := by
  have h1 : c'⁻¹ * c = u' * u⁻¹ := by
    calc c'⁻¹ * c = c'⁻¹ * (c * u) * u⁻¹ := by group
      _ = c'⁻¹ * (c' * u') * u⁻¹ := by rw [h]
      _ = u' * u⁻¹ := by group
  have h2 : c'⁻¹ * c ∈ C ⊓ U :=
    ⟨C.mul_mem (C.inv_mem hc') hc, h1 ▸ U.mul_mem hu' (U.inv_mem hu)⟩
  rw [hdisj, Subgroup.mem_bot] at h2
  have hcc : c = c' := by
    have := congrArg (c' * ·) h2
    simpa using this
  refine ⟨hcc, ?_⟩
  subst hcc
  simpa using h

theorem case4_split_exists {G : Type} [Group G] {C U Z : Subgroup G} (hCZ : C ≤ Z) (hUZ : U ≤ Z)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hsum : Z = C ⊔ U) (hdisj : C ⊓ U = ⊥) :
    ∃ π : ↥Z →* ↥U, (∀ u : ↥U, π ⟨(u : G), hUZ u.2⟩ = u) ∧ π.ker = C.subgroupOf Z := by
  have hdec := case4_decomp hCZ hUZ hcomm hsum
  choose! cc uu hcc huu hzz using hdec
  refine ⟨MonoidHom.mk' (fun z => ⟨uu z, huu z z.2⟩) ?_, ?_, ?_⟩
  · intro a b
    have ha := hzz a a.2
    have hb := hzz b b.2
    have hab := hzz (a * b : ↥Z) (a * b).2
    have hcomm' : uu a * cc b = cc b * uu a := hcomm _ (hUZ (huu a a.2)) _ (hCZ (hcc b b.2))
    have key : cc (a * b : ↥Z) * uu (a * b : ↥Z) = (cc a * cc b) * (uu a * uu b) := by
      calc cc (a * b : ↥Z) * uu (a * b : ↥Z) = (a : G) * b := hab.symm
        _ = (cc a * uu a) * (cc b * uu b) := by rw [← ha, ← hb]
        _ = cc a * (uu a * cc b) * uu b := by group
        _ = cc a * (cc b * uu a) * uu b := by rw [hcomm']
        _ = (cc a * cc b) * (uu a * uu b) := by group
    exact Subtype.ext (case4_uniq hdisj (hcc _ (a * b).2) (C.mul_mem (hcc a a.2) (hcc b b.2))
      (huu _ (a * b).2) (U.mul_mem (huu a a.2) (huu b b.2)) key).2
  · intro u
    have h1 : (1 : G) * (u : G) = cc (u : G) * uu (u : G) := by
      rw [one_mul]; exact hzz _ (hUZ u.2)
    exact Subtype.ext (case4_uniq hdisj C.one_mem (hcc _ (hUZ u.2)) u.2 (huu _ (hUZ u.2)) h1).2.symm
  · ext z
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      have h1 : uu (z : G) = 1 := congrArg Subtype.val hz
      have := hzz z z.2
      rw [h1, mul_one] at this
      rw [this]
      exact hcc z z.2
    · intro hz
      have h1 : (z : G) * 1 = cc (z : G) * uu (z : G) := by
        rw [mul_one]; exact hzz _ z.2
      have := (case4_uniq hdisj hz (hcc _ z.2) U.one_mem (huu _ z.2) h1).2
      exact Subtype.ext this.symm

theorem case4_via_split {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {K Z C U : Subgroup G}
    {α : ↥K →* ↥Γ} (hZK : K ≤ normalizer (Z : Set G))
    (hCK : ∀ k ∈ K, ∀ c ∈ C, k * c * k⁻¹ = c)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hsum : Z = C ⊔ U) (hdisj : C ⊓ U = ⊥)
    (hU : CFSG.Quasithin.IsSumOfNaturalModulesVia K U ⊥ α false 1) :
    CFSG.Quasithin.IsSumOfNaturalModulesVia K Z C α false 1 := by
  have hCZ : C ≤ Z := hsum ▸ le_sup_left
  have hUZ : U ≤ Z := hsum ▸ le_sup_right
  obtain ⟨hKU, -, β, hβs, hβker, hβeq⟩ := hU
  obtain ⟨π, hπU, hπker⟩ := case4_split_exists hCZ hUZ hcomm hsum hdisj
  refine ⟨hZK, hCZ, β.comp π, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, rfl⟩ := hβs y
    exact ⟨⟨u, hUZ u.2⟩, by simp [hπU]⟩
  · have hβinj : Function.Injective β := by
      rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
    rw [MonoidHom.ker_comp_of_injective π β hβinj, hπker]
  · intro k u₁ v₁ hv i
    set u : ↥U := π u₁ with hu
    set c : ↥Z := u₁ * (⟨(u : G), hUZ u.2⟩ : ↥Z)⁻¹ with hc
    have hcker : c ∈ π.ker := by
      rw [MonoidHom.mem_ker, hc, map_mul, map_inv, hπU, hu, mul_inv_cancel]
    have hcC : (c : G) ∈ C := by
      rw [hπker] at hcker
      exact hcker
    have hu₁ : (u₁ : G) = (c : G) * (u : G) := by
      rw [hc]
      simp
    have hvmem : (k : G) * (u : G) * (k : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (hKU k.2) u).1 u.2
    set v : ↥U := ⟨(k : G) * (u : G) * (k : G)⁻¹, hvmem⟩ with hv'
    have hv₁ : (v₁ : G) = (c : G) * (v : G) := by
      rw [hv, hu₁, hv']
      have := hCK k k.2 c hcC
      calc (k : G) * ((c : G) * (u : G)) * (k : G)⁻¹
          = ((k : G) * (c : G) * (k : G)⁻¹) * ((k : G) * (u : G) * (k : G)⁻¹) := by group
        _ = (c : G) * ((k : G) * (u : G) * (k : G)⁻¹) := by rw [this]
    have hπv₁ : π v₁ = v := by
      have : v₁ = c * (⟨(v : G), hUZ v.2⟩ : ↥Z) := Subtype.ext hv₁
      rw [this, map_mul, (MonoidHom.mem_ker.1 hcker), hπU, one_mul]
    have hπu₁ : π u₁ = u := hu.symm
    simp only [MonoidHom.comp_apply, hπv₁, hπu₁]
    exact hβeq k u v rfl i

theorem case4_normalizer_centralizer {G : Type} [Group G] {K Q : Subgroup G}
    (hK : K ≤ normalizer (Q : Set G)) :
    K ≤ normalizer ((centralizer (Q : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro q hq
  have hq' : k⁻¹ * q * k ∈ Q := (Subgroup.mem_normalizer_iff''.1 (hK hk) q).1 hq
  have h := hc _ hq'
  calc q * (k * c * k⁻¹) = k * ((k⁻¹ * q * k) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * q * k)) * k⁻¹ := by rw [h]
    _ = k * c * k⁻¹ * q := by group

theorem case4_normalizer_inf {G : Type} [Group G] {K B C : Subgroup G}
    (hB : K ≤ normalizer (B : Set G)) (hC : K ≤ normalizer (C : Set G)) :
    K ≤ normalizer ((B ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at hB hC ⊢
  exact fun k hk x hx => ⟨hB k hk x hx.1, hC k hk x hx.2⟩

theorem CampbellHyp.hasNatSection_of_case4 (h : CampbellHyp X K R P) {F : Type} [Field F]
    [Fintype F] (hF : Fintype.card F = 2) {α : ↥K →* ↥(StatedSL 3 F)}
    (hα : CFSG.Quasithin.IsModO2Surj K α)
    (hsum : CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K) =
      CFSG.Quasithin.c134CQ X K ⊔
        ⁅CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K), K⁆)
    (hdisj : CFSG.Quasithin.c134CQ X K ⊓
      ⁅CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K), K⁆ = ⊥)
    (hU : CFSG.Quasithin.IsSumOfNaturalModulesVia K
      ⁅CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K), K⁆ ⊥ α false 1) :
    HasNatSection K (CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K))
      (CFSG.Quasithin.c134CQ X K) := by
  refine hasNatSection_of_via hF hα ?_
  have hKQ : K ≤ normalizer ((CFSG.Quasithin.c134Q X K : Subgroup A) : Set A) :=
    normalizer_commutator_of_normalizes (le_trans h.K_le (normalizer_pCoreOf X))
      Subgroup.le_normalizer
  refine case4_via_split ?_ ?_ ?_ hsum hdisj hU
  · exact case4_normalizer_inf hKQ (case4_normalizer_centralizer hKQ)
  · intro k hk c hc
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.1 hc.2 k hk
    rw [hkc]
    group
  · intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 ha.2 b hb.1).symm
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
