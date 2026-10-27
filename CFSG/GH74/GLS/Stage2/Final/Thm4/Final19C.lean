module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19B

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section PMod

theorem exists_pow_mem_oResidual {Y : Type*} [Group Y] [Finite Y] (p : ℕ) [hp : Fact p.Prime] (y : Y) :
    ∃ a : ℕ, y ^ (p ^ a) ∈ oResidual p Y := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.out.one_lt.ne'
  refine ⟨a, Subgroup.subset_closure ?_⟩
  change Nat.Coprime (orderOf (y ^ p ^ a)) p
  rw [orderOf_pow_of_dvd (pow_ne_zero a hp.out.ne_zero) (Dvd.intro _ hord.symm), hord,
    Nat.mul_div_cancel_left m (pow_pos hp.out.pos a)]
  exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem core_lemma (p : ℕ) [Fact p.Prime] (K : Subgroup Γ) [K.Normal] {ι : Type*} (B : ι → Subgroup Γ)
    [∀ i, (B i).Normal] (hB : ∀ i, ∀ b ∈ B i, ∃ a : ℕ, b ^ (p ^ a) ∈ K) :
    ∀ x ∈ ⨆ i, B i, ∃ a : ℕ, x ^ (p ^ a) ∈ K := by
  intro x hx
  have hle : ∀ i, (B i).map (QuotientGroup.mk' K) ≤ pCore p (Γ ⧸ K) := by
    intro i
    have hn : ((B i).map (QuotientGroup.mk' K)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hpg : IsPGroup p ↥((B i).map (QuotientGroup.mk' K)) := by
      rintro ⟨_, b, hb, rfl⟩
      obtain ⟨a, ha⟩ := hB i b hb
      refine ⟨a, Subtype.ext ?_⟩
      change (QuotientGroup.mk' K b) ^ (p ^ a) = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ha
    exact le_sSup ⟨hn, hpg⟩
  have hx' : QuotientGroup.mk' K x ∈ pCore p (Γ ⧸ K) := by
    have : (⨆ i, B i).map (QuotientGroup.mk' K) ≤ pCore p (Γ ⧸ K) := by
      rw [Subgroup.map_iSup]
      exact iSup_le hle
    exact this ⟨x, hx, rfl⟩
  obtain ⟨a, ha⟩ := (pCore_isPGroup (G := Γ ⧸ K) (p := p)) ⟨_, hx'⟩
  refine ⟨a, ?_⟩
  have h1 : (QuotientGroup.mk' K x) ^ (p ^ a) = 1 := by simpa using congrArg Subtype.val ha
  rw [← map_pow] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem perfect_le_of_pmod (p : ℕ) [Fact p.Prime] (K : Subgroup Γ) [K.Normal] {Λ : Subgroup Γ}
    (hperf : Group.IsPerfect ↥Λ) (h : ∀ x ∈ Λ, ∃ a : ℕ, x ^ (p ^ a) ∈ K) : Λ ≤ K := by
  have hpg : IsPGroup p ↥(Λ.map (QuotientGroup.mk' K)) := by
    rintro ⟨_, b, hb, rfl⟩
    obtain ⟨a, ha⟩ := h b hb
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' K b) ^ (p ^ a) = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ha
  have hperf' : Group.IsPerfect ↥(Λ.map (QuotientGroup.mk' K)) := Group.IsPerfect.map _
  have hnil : Group.IsNilpotent ↥(Λ.map (QuotientGroup.mk' K)) := hpg.isNilpotent
  have hsolv : Group.IsSolvable ↥(Λ.map (QuotientGroup.mk' K)) := inferInstance
  have hbot : Λ.map (QuotientGroup.mk' K) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(Λ.map (QuotientGroup.mk' K)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hsolv
  intro x hx
  have : QuotientGroup.mk' K x ∈ (⊥ : Subgroup (Γ ⧸ K)) := hbot ▸ ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp this)

omit [Finite Γ] in
theorem two_elem_mem_of_pmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (K : Subgroup Γ) [K.Normal] {x : Γ}
    (hx2 : ∃ b : ℕ, x ^ (2 ^ b) = 1) (h : ∃ a : ℕ, x ^ (p ^ a) ∈ K) : x ∈ K := by
  obtain ⟨b, hb⟩ := hx2
  obtain ⟨a, ha⟩ := h
  have h1 : orderOf (QuotientGroup.mk' K x) ∣ 2 ^ b := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, hb, map_one]
  have h2 : orderOf (QuotientGroup.mk' K x) ∣ p ^ a := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ha
  have hcop : Nat.Coprime (2 ^ b) (p ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr (Ne.symm hp2))
  have h3 : orderOf (QuotientGroup.mk' K x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)

omit [Finite Γ] in
theorem commutator_top_normal (A : Subgroup Γ) : (⁅(⊤ : Subgroup Γ), A⁆).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hx' : x ∈ Subgroup.closure {y : Γ | ∃ g₁ ∈ (⊤ : Subgroup Γ), ∃ g₂ ∈ A, ⁅g₁, g₂⁆ = y} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨m, -, c, hc, rfl⟩ := hy
    have h1 : g * ⁅m, c⁆ * g⁻¹ = ⁅g * m, c⁆ * (⁅g, c⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator trivial hc)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator trivial hc))
  | one => simp
  | mul y₁ y₂ _ _ h₁ h₂ =>
    have : g * (y₁ * y₂) * g⁻¹ = (g * y₁ * g⁻¹) * (g * y₂ * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ h₁ h₂
  | inv y _ h₁ =>
    have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ h₁

end PMod

section GLevel

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

omit [Finite G] in
theorem commutator_Cen_zpowers_self (z : G) : ⁅Cen z, zpowers z⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h : Commute m z := Subgroup.mem_centralizer_singleton_iff.mp hm
  exact (Commute.zpow_left h.symm n)

theorem part_B (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) (h26 : Lemma26 z S)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (h195 : ∀ t ∈ S, IsConj z t → inSubgroup (oResidual p) ⁅Cen z, zpowers t⁆ ≤
      centralizer ((Bg.Fpi {r | r.Prime ∧ r ≠ 2} (Cen z) : Subgroup G) : Set G)) :
    (∀ x ∈ pLayerOf 2 (Cen z), ∀ f ∈ (fitOdd ↥(Cen z)).map (Cen z).subtype, x * f = f * x) ∧
    (∀ x ∈ S ⊓ WC z, ∀ f ∈ (fitOdd ↥(Cen z)).map (Cen z).subtype, x * f = f * x) := by
  have hSC : S ≤ Cen z := hS.le
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  let K : Subgroup ↥(Cen z) := Subgroup.centralizer (fitOdd ↥(Cen z) : Set ↥(Cen z))
  have hK : K.Normal := inferInstance
  let ι := {t : G // t ∈ S ∧ IsConj z t}
  let B : ι → Subgroup ↥(Cen z) := fun t =>
    ⁅(⊤ : Subgroup ↥(Cen z)), Subgroup.zpowers (⟨t.1, hSC t.2.1⟩ : ↥(Cen z))⁆
  have hBn : ∀ i, (B i).Normal := fun i => commutator_top_normal _
  have hBmap : ∀ i : ι, (B i).map (Cen z).subtype = ⁅Cen z, zpowers i.1⁆ := by
    intro i
    change (⁅(⊤ : Subgroup ↥(Cen z)), Subgroup.zpowers (⟨i.1, hSC i.2.1⟩ : ↥(Cen z))⁆).map (Cen z).subtype = _
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_zpowers]
    rfl
  have hBp : ∀ i : ι, ∀ b ∈ B i, ∃ a : ℕ, b ^ (p ^ a) ∈ K := by
    intro i b hb
    have hbG : (b : G) ∈ ⁅Cen z, zpowers i.1⁆ := by
      rw [← hBmap i]
      exact ⟨b, hb, rfl⟩
    obtain ⟨a, ha⟩ := exists_pow_mem_oResidual p (⟨b, hbG⟩ : ↥⁅Cen z, zpowers i.1⁆)
    refine ⟨a, ?_⟩
    have h1 : ((b : G) ^ (p ^ a)) ∈ inSubgroup (oResidual p) ⁅Cen z, zpowers i.1⁆ :=
      ⟨_, ha, rfl⟩
    have h2 := h195 i.1 i.2.1 i.2.2 h1
    have h3 : ∀ f ∈ (fitOdd ↥(Cen z)).map (Cen z).subtype, f ∈ (Bg.Fpi {r | r.Prime ∧ r ≠ 2} (Cen z) : Subgroup G) :=
      fun f hf => fitOdd_le_Fpi (Cen z) hf
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    refine Subtype.ext ?_
    have h4 := Subgroup.mem_centralizer_iff.mp h2 (f : G) (h3 _ ⟨f, hf, rfl⟩)
    simpa using h4
  have hjoin := core_lemma p K B hBp
  have hΛ : pLayerOf 2 (Cen z) ⊔ (S ⊓ WC z) ≤ (⨆ i, B i).map (Cen z).subtype := by
    refine h26.trans (iSup_le fun t => iSup_le fun ht => iSup_le fun hc => ?_)
    calc O2Of ⁅Cen z, zpowers t⁆ ≤ ⁅Cen z, zpowers t⁆ := Subgroup.map_subtype_le _
      _ = (B ⟨t, ht, hc⟩).map (Cen z).subtype := (hBmap ⟨t, ht, hc⟩).symm
      _ ≤ _ := Subgroup.map_mono (le_iSup B ⟨t, ht, hc⟩)
  have hmem : ∀ x : ↥(Cen z), (x : G) ∈ pLayerOf 2 (Cen z) ⊔ (S ⊓ WC z) → x ∈ ⨆ i, B i := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hΛ hx
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hcentK : ∀ y ∈ K, ∀ f ∈ (fitOdd ↥(Cen z)).map (Cen z).subtype, ((y : ↥(Cen z)) : G) * f = f * y := by
    rintro y hy _ ⟨f, hf, rfl⟩
    exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy f hf)).symm
  refine ⟨?_, ?_⟩
  · intro x hx f hf
    rw [pLayerOf_eq_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hperf : Group.IsPerfect ↥(pLayer ↥(Cen z) 2) :=
      Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect _)
    have hle : pLayer ↥(Cen z) 2 ≤ K := by
      refine perfect_le_of_pmod p K hperf fun y hy => hjoin y (hmem y ?_)
      rw [pLayerOf_eq_map] at *
      exact Subgroup.mem_sup_left ⟨y, hy, rfl⟩
    exact hcentK y (hle hy) f hf
  · rintro x ⟨hxS, hxW⟩ f hf
    have hxC : x ∈ Cen z := hSC hxS
    have hx2 : ∃ b : ℕ, (⟨x, hxC⟩ : ↥(Cen z)) ^ (2 ^ b) = 1 := by
      obtain ⟨b, hb⟩ := hS2 ⟨x, hxS⟩
      exact ⟨b, Subtype.ext (by simpa using congrArg Subtype.val hb)⟩
    have hmx := hmem ⟨x, hxC⟩ (Subgroup.mem_sup_right ⟨hxS, hxW⟩)
    have hxK := two_elem_mem_of_pmod p hp2 K hx2 (hjoin _ hmx)
    exact hcentK ⟨x, hxC⟩ hxK f hf

end GLevel

end CFSG.GH74.GLS.Stage2.Final.Thm4
