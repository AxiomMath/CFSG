module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.GSThmB.QPUAlt

open CFSG Subgroup Equiv Equiv.Perm MulAction
open scoped Pointwise

theorem eq_or_eq_of_isThreeCycle {α : Type*} [Fintype α] [DecidableEq α] {c : Perm α}
    (hc : c.IsThreeCycle) {x y : α} (hx : c x ≠ x) (hy : c y ≠ y) (hxy : x ≠ y) :
    y = c x ∨ x = c y := by
  obtain ⟨i, hi⟩ := hc.isCycle.exists_pow_eq hx hy
  have h3 : c ^ 3 = 1 := by rw [← hc.orderOf]; exact pow_orderOf_eq_one c
  have hi' : (c ^ (i % 3)) x = y := by
    rw [← hi]
    conv_rhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, h3, one_pow, mul_one]
  obtain h | h | h : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  · rw [h, pow_zero, Perm.one_apply] at hi'
    exact absurd hi' hxy
  · rw [h, pow_one] at hi'
    exact Or.inl hi'.symm
  · rw [h] at hi'
    right
    rw [← hi', ← Perm.mul_apply, ← pow_succ', h3, Perm.one_apply]

theorem exists_mem_ne_ne {α : Type*} {F : Set α} (hF : 3 ≤ Nat.card F) (a b : α) :
    ∃ c ∈ F, c ≠ a ∧ c ≠ b := by
  by_contra h
  push Not at h
  have hsub : F ⊆ {a, b} := fun c hc => by
    by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr (h c hc hca)
  have h1 : Nat.card F ≤ Nat.card ({a, b} : Set α) := Nat.card_mono (Set.toFinite _) hsub
  have h2 : Nat.card ({a, b} : Set α) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])
  omega

theorem two_dvd_card_alternatingGroup {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h4 : 4 ≤ Nat.card Ω) : 2 ∣ Nat.card (alternatingGroup Ω) := by
  have : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have h2 := two_mul_nat_card_alternatingGroup (α := Ω)
  rw [Nat.card_perm] at h2
  have h4' : 4 ∣ (Nat.card Ω).factorial := Nat.dvd_factorial (by norm_num) h4
  omega

theorem two_mul_card_eq_factorial {L : Type} [Group L] [Finite L] {α : Type} [Finite α]
    [DecidableEq α] (ψ : L →* Perm α) (hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L)) (F : Set α)
    (hF : 5 ≤ Nat.card F)
    (h3 : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, a ≠ b → a ≠ c → b ≠ c →
      ∃ l : L, ψ l = swap a b * swap a c) :
    ∃ m : ℕ, 5 ≤ m ∧ 2 * Nat.card (L ⧸ pPrimeCore 2 L) = m.factorial := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite α
  set S : Set L := {l | (ψ l).IsThreeCycle} with hS
  set N : Subgroup L := normalClosure S with hN
  set H : Subgroup (Perm α) := N.map ψ with hH
  set T : Set (Perm α) := ψ '' Group.conjugatesOfSet S with hT
  have hT3 : ∀ c ∈ T, c.IsThreeCycle := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨s, hs, hsl⟩ := Group.mem_conjugatesOfSet_iff.mp hl
    obtain ⟨g, rfl⟩ := isConj_iff.mp hsl
    show (ψ (g * s * g⁻¹)).cycleType = {3}
    rw [map_mul, map_mul, map_inv, cycleType_conj]
    exact hs
  have hHT : H = closure T := MonoidHom.map_closure ψ _
  have hTH : ∀ c ∈ T, c ∈ H := fun c hc => hHT ▸ subset_closure hc
  have hcyc : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, a ≠ b → a ≠ c → b ≠ c → swap a b * swap a c ∈ H := by
    intro a ha b hb c hc hab hac hbc
    obtain ⟨l, hl⟩ := h3 a ha b hb c hc hab hac hbc
    have hlS : l ∈ S := by
      show (ψ l).IsThreeCycle
      rw [hl]
      exact isThreeCycle_swap_mul_swap_same hab hac hbc
    exact ⟨l, subset_normalClosure hlS, hl⟩
  obtain ⟨⟨x₀, hx₀⟩⟩ : Nonempty F := (Nat.card_pos_iff.mp (by omega)).1
  set Ω : Set α := orbit H x₀ with hΩ
  have hFΩ : F ⊆ Ω := by
    intro y hy
    by_cases hyx : y = x₀
    · rw [hyx]
      exact mem_orbit_self x₀
    · obtain ⟨z, hzF, hzx, hzy⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card F) x₀ y
      have hmem := hcyc z hzF y hy x₀ hx₀ hzy hzx hyx
      refine ⟨⟨_, hmem⟩, ?_⟩
      change (swap z y * swap z x₀) x₀ = y
      rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  have hΩ5 : 5 ≤ Nat.card Ω := hF.trans (Nat.card_mono (Set.toFinite _) hFΩ)
  set τ : H →* Perm Ω := MulAction.toPermHom H Ω with hτ
  have hτapp : ∀ (h : H) (ω : Ω), ((τ h ω : Ω) : α) = (h : Perm α) ω := fun _ _ => rfl
  set G₀ : Subgroup (Perm Ω) := τ.range with hG₀
  have hgen : ∀ K : Subgroup (Perm Ω), (∀ c (hc : c ∈ T), τ ⟨c, hTH c hc⟩ ∈ K) → G₀ ≤ K := by
    intro K hK
    rintro _ ⟨h, rfl⟩
    have hle : closure T ≤ (K.comap τ).map H.subtype :=
      (closure_le _).mpr fun c hc => ⟨⟨c, hTH c hc⟩, hK c hc, rfl⟩
    obtain ⟨h', hh', hh'eq⟩ := hle (by rw [← hHT]; exact h.2)
    rwa [show h = h' from Subtype.ext hh'eq.symm]
  have hpre : IsPretransitive G₀ Ω := by
    refine ⟨fun ω₁ ω₂ => ?_⟩
    obtain ⟨h, hh⟩ := exists_smul_eq H ω₁ ω₂
    exact ⟨⟨τ h, h, rfl⟩, hh⟩
  have hprim : IsPreprimitive G₀ Ω := by
    refine { toIsPretransitive := hpre, isTrivialBlock_of_isBlock := fun {B} hB => ?_ }
    by_cases hBs : B.Subsingleton
    · exact Or.inl hBs
    · right
      obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := Set.not_subsingleton_iff.mp hBs
      have hstab : G₀ ≤ stabilizer (Perm Ω) B := by
        refine hgen _ fun c hc => ?_
        rw [mem_stabilizer_iff]
        by_contra hne
        have hdis : Disjoint ((⟨τ ⟨c, hTH c hc⟩, ⟨c, hTH c hc⟩, rfl⟩ : G₀) • B) B :=
          ((isBlock_iff_smul_eq_or_disjoint.mp hB) ⟨_, ⟨c, hTH c hc⟩, rfl⟩).resolve_left hne
        have hmove : ∀ {b}, b ∈ B → ∀ {b'}, b' ∈ B → c b = b' → False := by
          intro b hb b' hb' hcb
          refine Set.disjoint_left.mp hdis ?_ hb'
          refine ⟨b, hb, Subtype.ext ?_⟩
          exact hcb
        have hc3 := hT3 c hc
        have h1 : c b₁ ≠ b₁ := fun h => hmove hb₁ hb₁ h
        have h2 : c b₂ ≠ b₂ := fun h => hmove hb₂ hb₂ h
        rcases eq_or_eq_of_isThreeCycle hc3 h1 h2 (fun h => hb (Subtype.ext h)) with h | h
        · exact hmove hb₁ hb₂ h.symm
        · exact hmove hb₂ hb₁ h.symm
      ext ω
      simp only [Set.mem_univ, iff_true]
      obtain ⟨g, hg⟩ := exists_smul_eq G₀ b₁ ω
      have hgB := mem_stabilizer_iff.mp (hstab g.2)
      rw [← hg]
      have : (g : Perm Ω) • b₁ ∈ (g : Perm Ω) • B := Set.smul_mem_smul_set hb₁
      rwa [hgB] at this
  obtain ⟨y₁, hy₁, hy₁x, -⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card F) x₀ x₀
  obtain ⟨y₂, hy₂, hy₂x, hy₂y⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card F) x₀ y₁
  have hc₀ := hcyc x₀ hx₀ y₁ hy₁ y₂ hy₂ (Ne.symm hy₁x) (Ne.symm hy₂x) (Ne.symm hy₂y)
  set ω₀ : Ω := ⟨x₀, hFΩ hx₀⟩
  set ω₁ : Ω := ⟨y₁, hFΩ hy₁⟩
  set ω₂ : Ω := ⟨y₂, hFΩ hy₂⟩
  have hg₀ : τ ⟨_, hc₀⟩ = swap ω₀ ω₁ * swap ω₀ ω₂ := by
    ext ω
    rw [hτapp, Perm.mul_apply, Perm.mul_apply, ← Subtype.val_injective.swap_apply,
      ← Subtype.val_injective.swap_apply]
  have h3g₀ : (swap ω₀ ω₁ * swap ω₀ ω₂).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (fun h => hy₁x (congrArg Subtype.val h).symm)
      (fun h => hy₂x (congrArg Subtype.val h).symm) (fun h => hy₂y (congrArg Subtype.val h).symm)
  have hAG : alternatingGroup Ω ≤ G₀ :=
    alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3g₀ ⟨_, hg₀⟩
  have hGA : G₀ ≤ alternatingGroup Ω := by
    refine hgen _ fun c hc => ?_
    have hc3 := hT3 c hc
    have hcH := hTH c hc
    have hinv : ∀ y, c y ∈ Ω ↔ y ∈ Ω := by
      intro y
      have h1 : c y = (⟨c, hcH⟩ : H) • y := rfl
      rw [h1, hΩ, ← orbit_eq_iff, orbit_smul, orbit_eq_iff]
    by_cases hΩc : ∃ x ∈ Ω, c x ≠ x
    · obtain ⟨x, hxΩ, hcx⟩ := hΩc
      have hsupp : ∀ y, c y ≠ y → y ∈ Ω := by
        intro y hy
        obtain ⟨i, hi⟩ := hc3.isCycle.exists_pow_eq hcx hy
        rw [← hi]
        have h1 : (c ^ i) x = (⟨c, hcH⟩ ^ i : H) • x := by
          simp [Subgroup.smul_def, Perm.smul_def]
        rw [h1, hΩ, ← orbit_eq_iff, orbit_smul, orbit_eq_iff]
        exact hxΩ
      have h1 : τ ⟨c, hcH⟩ = c.subtypePerm (p := (· ∈ Ω)) hinv := by
        ext ω
        rfl
      rw [mem_alternatingGroup, h1]
      have h2 := sign_subtypePerm c hinv hsupp
      rw [hc3.sign] at h2
      convert h2
    · push Not at hΩc
      have h1 : τ ⟨c, hcH⟩ = 1 := by
        ext ω
        exact hΩc ω ω.2
      rw [h1]
      exact one_mem _
  have hsA : IsSimpleGroup (alternatingGroup Ω) := alternatingGroup.isSimpleGroup hΩ5
  have hAev : 2 ∣ Nat.card (alternatingGroup Ω) := two_dvd_card_alternatingGroup (by omega)
  let φ₀ : N →* Perm Ω := τ.comp (ψ.subgroupMap N)
  have hφ₀ : ∀ x : N, φ₀ x ∈ alternatingGroup Ω := fun x => hGA ⟨_, rfl⟩
  let φ : N →* alternatingGroup Ω := φ₀.codRestrict _ hφ₀
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨h, hh⟩ := hAG a.2
    obtain ⟨x, hx⟩ := ψ.subgroupMap_surjective N h
    refine ⟨x, Subtype.ext ?_⟩
    change τ (ψ.subgroupMap N x) = a
    rw [hx, hh]
  set O := pPrimeCore 2 L with hO
  have hOodd : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card (p := 2) (G := L)
  have hnot : ∀ {k : ℕ}, Nat.card (alternatingGroup Ω) ∣ k → k ∣ Nat.card O → False :=
    fun h1 h2 => (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (hOodd.coprime_dvd_right (h1.trans h2)) hAev
  have hK : O.subgroupOf N ≤ φ.ker := by
    have hn : ((O.subgroupOf N).map φ).Normal := Normal.map inferInstance φ hφ
    rcases hsA.eq_bot_or_eq_top_of_normal ((O.subgroupOf N).map φ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      have hdvd := card_map_dvd (O.subgroupOf N) φ
      rw [ht, card_top] at hdvd
      refine hnot hdvd ?_
      rw [← card_map_of_injective N.subtype_injective, subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
  let Θ : N →* L ⧸ O := (QuotientGroup.mk' O).comp N.subtype
  have hΘker : Θ.ker = O.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hΘ : Function.Surjective Θ := by
    have hn : (N.map (QuotientGroup.mk' O)).Normal :=
      Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
    rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' O)) with hb | ht
    · exfalso
      have hNO : N ≤ O := by
        intro x hx
        have h1 : QuotientGroup.mk' O x ∈ N.map (QuotientGroup.mk' O) := ⟨x, hx, rfl⟩
        rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      exact hnot (card_dvd_of_surjective hφ) (card_dvd_of_le hNO)
    · intro q
      have h1 : q ∈ N.map (QuotientGroup.mk' O) := ht ▸ mem_top q
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ.ker = Θ.ker := by
    refine le_antisymm ?_ (hΘker ▸ hK)
    have hn : (φ.ker.map Θ).Normal := Normal.map inferInstance Θ hΘ
    rcases hs.eq_bot_or_eq_top_of_normal (φ.ker.map Θ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      have hall : ∀ x : N, φ x = 1 := by
        intro x
        have h1 : Θ x ∈ φ.ker.map Θ := ht ▸ mem_top _
        obtain ⟨k, hk, hkx⟩ := h1
        have h2 : k⁻¹ * x ∈ Θ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
        rw [hΘker] at h2
        have h3 := hK h2
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one,
          one_mul] at h3
        exact h3
      obtain ⟨a, b, hab⟩ := exists_pair_ne (alternatingGroup Ω)
      obtain ⟨x, rfl⟩ := hφ a
      obtain ⟨y, rfl⟩ := hφ b
      exact hab ((hall x).trans (hall y).symm)
  refine ⟨Nat.card Ω, hΩ5, ?_⟩
  have : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Θ hΘ).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    two_mul_nat_card_alternatingGroup, Nat.card_perm]

end CFSG.ComponentClassification.GSThmB.QPUAlt
