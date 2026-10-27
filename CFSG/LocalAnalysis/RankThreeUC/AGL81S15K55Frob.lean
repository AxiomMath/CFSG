module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Tools
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Module

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof

open CFSG.QuasithinUnique.Setup.Family

section Hall

theorem card_GL32 : Nat.card GL32 = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem exists_subgroup_card_21 : ∃ F : Subgroup GL32, Nat.card F = 21 := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isSimpleGroup_gl32
  obtain ⟨P⟩ : Nonempty (Sylow 7 GL32) := inferInstance
  have hP7 : Nat.card P = 7 := by
    rw [Sylow.card_eq_multiplicity P, card_GL32]
    have : (168 : ℕ).factorization 7 = 1 := by
      rw [Nat.factorization_def _ h7.out]
      decide +kernel
    rw [this]
    norm_num
  have hindex : (P : Subgroup GL32).index = 24 := by
    have h := Subgroup.card_mul_index (P : Subgroup GL32)
    rw [card_GL32] at h
    have : Nat.card (P : Subgroup GL32) = 7 := hP7
    rw [this] at h
    omega
  have hdvd : Nat.card (Sylow 7 GL32) ∣ 24 := hindex ▸ Sylow.card_dvd_index P
  have hmod : Nat.card (Sylow 7 GL32) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 GL32
  have hn : Nat.card (Sylow 7 GL32) = 1 ∨ Nat.card (Sylow 7 GL32) = 8 := by
    have hle : Nat.card (Sylow 7 GL32) ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 7 GL32) <;> simp_all <;> omega
  rcases hn with h1 | h8
  · exfalso
    haveI : Subsingleton (Sylow 7 GL32) := (Nat.card_eq_one_iff_unique.1 h1).1
    have hnorm : (P : Subgroup GL32).Normal := Sylow.normal_of_subsingleton P
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup GL32) with hb | ht
    · have : Nat.card (P : Subgroup GL32) = 1 := by rw [hb]; exact Subgroup.card_bot
      have h7' : Nat.card (P : Subgroup GL32) = 7 := hP7
      omega
    · have : Nat.card (P : Subgroup GL32) = 168 := by rw [ht, Subgroup.card_top, card_GL32]
      have h7' : Nat.card (P : Subgroup GL32) = 7 := hP7
      omega
  · refine ⟨Subgroup.normalizer (P : Set GL32), ?_⟩
    have h1 := Sylow.card_eq_index_normalizer P
    rw [h8] at h1
    have h2 := Subgroup.card_mul_index (Subgroup.normalizer (P : Set GL32))
    rw [card_GL32, ← h1] at h2
    omega

theorem exists_subgroup_card_21_of_equiv {G : Type*} [Group G] {L : Subgroup G} (eL : ↥L ≃* GL32) :
    ∃ F : Subgroup G, F ≤ L ∧ Nat.card F = 21 := by
  obtain ⟨F₀, hF₀⟩ := exists_subgroup_card_21
  refine ⟨(F₀.map eL.symm.toMonoidHom).map L.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.card_map_of_injective eL.symm.injective, hF₀]

theorem exists_mul_of_sylow {G : Type*} [Group G] [Finite G] {L F S₀ : Subgroup G} (hFL : F ≤ L)
    (hF : Nat.card F = 21) (hSL : S₀ ≤ L) (hS : Nat.card S₀ = 8) (hL : Nat.card L = 168) :
    ∀ l ∈ L, ∃ f ∈ F, ∃ s ∈ S₀, l = f * s := by
  have hcop : Nat.Coprime (Nat.card F) (Nat.card S₀) := by rw [hF, hS]; norm_num
  have hinf : F ⊓ S₀ = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  let φ : ↥F × ↥S₀ → ↥L := fun p => ⟨(p.1 : G) * p.2, L.mul_mem (hFL p.1.2) (hSL p.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨f, s⟩ ⟨f', s'⟩ h
    have h1 : (f : G) * s = f' * s' := congrArg Subtype.val h
    have h2 : (f' : G)⁻¹ * f = s' * (s : G)⁻¹ := by
      calc (f' : G)⁻¹ * f = (f' : G)⁻¹ * (f * s) * (s : G)⁻¹ := by group
        _ = (f' : G)⁻¹ * (f' * s') * (s : G)⁻¹ := by rw [h1]
        _ = s' * (s : G)⁻¹ := by group
    have hmem : (f' : G)⁻¹ * f ∈ F ⊓ S₀ :=
      ⟨F.mul_mem (F.inv_mem f'.2) f.2, h2 ▸ S₀.mul_mem s'.2 (S₀.inv_mem s.2)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hff : f = f' := by
      have : (f : G) = f' := by
        calc (f : G) = f' * ((f' : G)⁻¹ * f) := by group
          _ = f' := by rw [hmem, mul_one]
      exact Subtype.ext this
    have hss : s = s' := by
      subst hff
      exact Subtype.ext (mul_left_cancel h1)
    rw [hff, hss]
  have hcard : Nat.card (↥F × ↥S₀) = Nat.card L := by
    rw [Nat.card_prod, hF, hS, hL]
  have hsurj : Function.Surjective φ :=
    (hinj.bijective_of_nat_card_le (by rw [hcard])).2
  intro l hl
  obtain ⟨⟨f, s⟩, hfs⟩ := hsurj ⟨l, hl⟩
  exact ⟨f, f.2, s, s.2, (congrArg Subtype.val hfs).symm⟩

end Hall

section FixZero

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem odd_nsmul_eq_self {n : ℕ} (hn : Odd n) (x : W) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, zmod_two_add_self, nsmul_zero, zero_add]

theorem fixed_eq_zero_of_generation [Finite G] (ρ : Representation (ZMod 2) G W)
    {L F S₀ : Subgroup G} (hF : Odd (Nat.card F))
    (hLfs : ∀ l ∈ L, ∃ f ∈ F, ∃ s ∈ S₀, l = f * s)
    (hgen : ∀ w : W, w ∈ Submodule.span (ZMod 2)
      {v | ∃ l ∈ L, ∃ c : W, (∀ s ∈ S₀, ρ s c = c) ∧ v = ρ l c}) :
    ∀ u ∈ commOn ρ L ⊤, (∀ f ∈ F, ρ f u = u) → u = 0 := by
  classical
  haveI : Fintype ↥F := Fintype.ofFinite _
  set e : Module.End (ZMod 2) W := ∑ f : ↥F, ρ (f : G) with he
  have hmul : ∀ f' ∈ F, e * ρ f' = e := by
    intro f' hf'
    rw [he, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨f', hf'⟩ : ↥F)) _ _ (fun f => ?_)
    rw [← map_mul]
    rfl
  have hec : ∀ c : W, (∀ s ∈ S₀, ρ s c = c) → ∀ l ∈ L, e (ρ l c) = e c := by
    intro c hc l hl
    obtain ⟨f, hf, s, hs, rfl⟩ := hLfs l hl
    have h1 : ρ (f * s) c = ρ f c := by rw [map_mul, Module.End.mul_apply, hc s hs]
    rw [h1, ← Module.End.mul_apply, hmul f hf]
  have hkill : ∀ l ∈ L, ∀ v : W, e (ρ l v - v) = 0 := by
    intro l hl v
    induction hgen v using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l₂, hl₂, c, hc, rfl⟩ := hx
      rw [map_sub, ← Module.End.mul_apply (ρ l) (ρ l₂), ← map_mul,
        hec c hc (l * l₂) (L.mul_mem hl hl₂), hec c hc l₂ hl₂, sub_self]
    | zero => simp
    | add x y _ _ hx hy =>
      have h1 : ρ l (x + y) - (x + y) = (ρ l x - x) + (ρ l y - y) := by
        rw [map_add]
        abel
      rw [h1, map_add, hx, hy, add_zero]
    | smul a x _ hx =>
      rw [map_smul, ← smul_sub, map_smul, hx, smul_zero]
  have hkillU : ∀ u ∈ commOn ρ L ⊤, e u = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, v, -, rfl⟩ := hx
      exact hkill a ha v
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  intro u hu hfix
  have h1 : e u = u := by
    rw [he, LinearMap.sum_apply]
    have : ∀ f : ↥F, (ρ (f : G)) u = u := fun f => hfix f f.2
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
    have hc : Fintype.card ↥F = Nat.card ↥F := (Nat.card_eq_fintype_card).symm
    rw [hc]
    exact odd_nsmul_eq_self hF u
  rw [← h1]
  exact hkillU u hu

theorem not_secTrivial_of_fixed_zero [Finite G] (ρ : Representation (ZMod 2) G W)
    {L F : Subgroup G} (hFL : F ≤ L) (hF : Odd (Nat.card F)) {U Z₀ Z₁ : Submodule (ZMod 2) W}
    (hU : ∀ u ∈ U, (∀ f ∈ F, ρ f u = u) → u = 0) (hZ₁U : Z₁ ≤ U) (hlt : Z₀ < Z₁)
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z₁) : ¬ SecTrivial ρ L Z₀ Z₁ := by
  classical
  intro htriv
  haveI : Fintype ↥F := Fintype.ofFinite _
  obtain ⟨z, hz1, hz0⟩ := Set.exists_of_ssubset hlt
  set ez : W := ∑ f : ↥F, ρ (f : G) z with hez
  have hez1 : ez ∈ Z₁ := Submodule.sum_mem _ fun f _ => hinv f (hFL f.2) z hz1
  have hezfix : ∀ f' ∈ F, ρ f' ez = ez := by
    intro f' hf'
    rw [hez, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨f', hf'⟩ : ↥F)) _ _ (fun f => ?_)
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hez0 : ez = 0 := hU ez (hZ₁U hez1) hezfix
  have hdiff : ez - z ∈ Z₀ := by
    have h1 : ez - z = ∑ f : ↥F, (ρ (f : G) z - z) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
      have hc : Fintype.card ↥F = Nat.card ↥F := (Nat.card_eq_fintype_card).symm
      rw [hc, odd_nsmul_eq_self hF z]
    rw [h1]
    exact Submodule.sum_mem _ fun f _ => htriv f (hFL f.2) z hz1
  rw [hez0, zero_sub] at hdiff
  exact hz0 (by simpa using Z₀.neg_mem hdiff)

end FixZero

end CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof
