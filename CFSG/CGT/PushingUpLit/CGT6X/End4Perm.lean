module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open Equiv CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit.CGT6

section Simple60

variable {M : Type*} [Group M] [Finite M] [IsSimpleGroup M]

theorem pm4_index_cases (h60 : Nat.card M = 60) (S : Subgroup M) (hS : S.index ≤ 9) :
    S = ⊤ ∨ S.index = 5 ∨ S.index = 6 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.normalCore with h | h
  · right
    have hdvd := S.index_normalCore_dvd_factorial_index
    rw [h, Subgroup.index_bot, h60] at hdvd
    have hd60 : S.index ∣ 60 := h60 ▸ Subgroup.index_dvd_card S
    obtain ⟨d, hd⟩ : ∃ d, d = S.index := ⟨_, rfl⟩
    rw [← hd] at hdvd hd60 hS ⊢
    interval_cases d <;> simp [Nat.factorial] at hdvd hd60 ⊢
  · left
    exact top_le_iff.mp (h ▸ S.normalCore_le)

theorem pm4_normalizer_eq (h60 : Nat.card M = 60) {S : Subgroup M}
    (hS : S.index = 5 ∨ S.index = 6) : Subgroup.normalizer (S : Set M) = S := by
  have hle : S ≤ Subgroup.normalizer (S : Set M) := Subgroup.le_normalizer
  have hdvd : (Subgroup.normalizer (S : Set M)).index ∣ S.index := Subgroup.index_dvd_of_le hle
  have h9 : (Subgroup.normalizer (S : Set M)).index ≤ 9 := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rcases pm4_index_cases h60 _ h9 with h | h | h
  · exfalso
    have hN : S.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h1 | h1
    · rw [h1, Subgroup.index_bot, h60] at hS
      omega
    · rw [h1, Subgroup.index_top] at hS
      omega
  · have hfi : (Subgroup.normalizer (S : Set M)).FiniteIndex := ⟨by omega⟩
    rw [h] at hdvd
    have h5 : S.index = 5 := by omega
    exact (Subgroup.eq_of_index_dvd_index hle (by rw [h, h5])).symm
  · have hfi : (Subgroup.normalizer (S : Set M)).FiniteIndex := ⟨by omega⟩
    rw [h] at hdvd
    have h6 : S.index = 6 := by omega
    exact (Subgroup.eq_of_index_dvd_index hle (by rw [h, h6])).symm

omit [IsSimpleGroup M] in
theorem pm4_fixes_of_selfNormalizing {X : Type*} [MulAction M X] {q : X}
    (hN : Subgroup.normalizer (MulAction.stabilizer M q : Set M) = MulAction.stabilizer M q)
    {σ : X → X} (hσ : ∀ (m : M) (x : X), σ (m • x) = m • σ x)
    (hq : σ q ∈ MulAction.orbit M q) : σ q = q := by
  obtain ⟨g, hg'⟩ := hq
  have hg : g • q = σ q := hg'
  set S := MulAction.stabilizer M q
  have hle : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    have hs : s • q = q := hs
    rw [MulAction.mem_stabilizer_iff]
    show (g⁻¹ * s * g⁻¹⁻¹) • q = q
    rw [inv_inv, mul_smul, mul_smul, hg, ← hσ, hs, ← hg, ← mul_smul, inv_mul_cancel, one_smul]
  have heq : S.map (MulAut.conj g⁻¹).toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hmem : g⁻¹ ∈ Subgroup.normalizer (S : Set M) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  rw [hN] at hmem
  have : g ∈ S := by simpa using S.inv_mem hmem
  rw [← hg]
  exact MulAction.mem_stabilizer_iff.mp this

section Orbits

variable {n : ℕ} [MulAction M (Fin n)]

omit [Finite M] [IsSimpleGroup M] in
theorem pm4_orbit_ncard_le (x : Fin n) : (MulAction.orbit M x).ncard ≤ n := by
  have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit M x))
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem pm4_index_moved (hn : n ≤ 9) (h60 : Nat.card M = 60) {q : Fin n}
    (hq : ¬ ∀ m : M, m • q = q) :
    (MulAction.stabilizer M q).index = 5 ∨ (MulAction.stabilizer M q).index = 6 := by
  have h9 : (MulAction.stabilizer M q).index ≤ 9 := by
    rw [MulAction.index_stabilizer]
    exact (pm4_orbit_ncard_le q).trans hn
  rcases pm4_index_cases h60 _ h9 with h | h | h
  · exfalso
    apply hq
    intro m
    have : m ∈ MulAction.stabilizer M q := h ▸ Subgroup.mem_top m
    exact this
  · exact Or.inl h
  · exact Or.inr h

theorem pm4_five_le_ncard (hn : n ≤ 9) (h60 : Nat.card M = 60) {q : Fin n}
    (hq : ¬ ∀ m : M, m • q = q) : 5 ≤ (MulAction.orbit M q).ncard := by
  rw [← MulAction.index_stabilizer]
  rcases pm4_index_moved hn h60 hq with h | h <;> omega

theorem pm4_mem_orbit (hn : n ≤ 9) (h60 : Nat.card M = 60) {x q : Fin n}
    (hx : ¬ ∀ m : M, m • x = x) (hq : ¬ ∀ m : M, m • q = q) :
    x ∈ MulAction.orbit M q := by
  by_contra hxq
  have hdisj : Disjoint (MulAction.orbit M q) (MulAction.orbit M x) := by
    rw [Set.disjoint_left]
    intro y hyq hyx
    apply hxq
    have e0 : MulAction.orbit M y = MulAction.orbit M q := MulAction.orbit_eq_iff.mpr hyq
    have e1 : MulAction.orbit M y = MulAction.orbit M x := MulAction.orbit_eq_iff.mpr hyx
    rw [← e0, e1]
    exact MulAction.mem_orbit_self x
  have hU := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : (MulAction.orbit M q ∪ MulAction.orbit M x).ncard ≤ n := by
    have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit M q ∪ MulAction.orbit M x))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h1 := pm4_five_le_ncard hn h60 hq
  have h2 := pm4_five_le_ncard hn h60 hx
  omega

omit [Finite M] [IsSimpleGroup M] in
theorem pm4_moved_of_mem_orbit {x q : Fin n} (hq : ¬ ∀ m : M, m • q = q)
    (hx : x ∈ MulAction.orbit M q) : ¬ ∀ m : M, m • x = x := by
  intro h
  obtain ⟨g, hg⟩ := hx
  have hg' : g • q = x := hg
  apply hq
  have h1 : g • q = q := by
    have := h g⁻¹
    rw [← hg', inv_smul_smul] at this
    exact this.symm
  have hqx : q = x := h1.symm.trans hg'
  subst hqx
  exact h

theorem pm4_comm_trivial (hn : n ≤ 9) (h60 : Nat.card M = 60) {σ : Perm (Fin n)}
    (hσ : ∀ (m : M) (x : Fin n), σ (m • x) = m • σ x) {x : Fin n}
    (hx : ¬ ∀ m : M, m • x = x) : σ x = x := by
  have hσx : ¬ ∀ m : M, m • σ x = σ x := by
    intro h
    apply hx
    intro m
    apply σ.injective
    rw [hσ, h]
  exact pm4_fixes_of_selfNormalizing (pm4_normalizer_eq h60 (pm4_index_moved hn h60 hx))
    hσ (pm4_mem_orbit hn h60 hσx hx)

theorem pm4_fixed_card (hn : n ≤ 9) (h60 : Nat.card M = 60)
    (hfaith : ∀ m : M, (∀ x : Fin n, m • x = x) → m = 1) (F : Finset (Fin n))
    (hF : ∀ x, x ∈ F ↔ ∀ m : M, m • x = x) : F.card + 5 = n ∨ F.card + 6 = n := by
  obtain ⟨q, hq⟩ : ∃ q : Fin n, ¬ ∀ m : M, m • q = q := by
    by_contra hall
    push Not at hall
    have hsub : Subsingleton M := ⟨fun a b => by
      rw [hfaith a (fun x => hall x a), hfaith b (fun x => hall x b)]⟩
    have := Nat.card_of_subsingleton (1 : M)
    omega
  have hset : (↑Fᶜ : Set (Fin n)) = MulAction.orbit M q := by
    ext x
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe, hF]
    exact ⟨fun hx => pm4_mem_orbit hn h60 hx hq, fun hx => pm4_moved_of_mem_orbit hq hx⟩
  have hcard : Fᶜ.card = (MulAction.orbit M q).ncard := by
    rw [← hset, Set.ncard_coe_finset]
  have hc : Fᶜ.card = n - F.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hFn : F.card ≤ n := by simpa using Finset.card_le_univ F
  rw [← MulAction.index_stabilizer] at hcard
  rcases pm4_index_moved hn h60 hq with h | h
  · left
    omega
  · right
    omega

end Orbits

end Simple60

set_option linter.unusedVariables false in
theorem alt5_config {n : ℕ} (hn : n = 7 ∨ n = 9) (H : Subgroup (alternatingGroup (Fin n)))
    [IsSimpleGroup ↥H] (hH : Nat.card ↥H = 60) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1)
    (hcomm : ∀ h ∈ H, σ * (h : Equiv.Perm (Fin n)) = (h : Equiv.Perm (Fin n)) * σ) :
    ∃ F : Finset (Fin n), (∀ h ∈ H, ∀ i ∈ F, (h : Equiv.Perm (Fin n)) i = i) ∧
      (∀ i, i ∉ F → σ i = i) ∧ ((H = altStabilizer n F ∧ F.card + 5 = n) ∨ F.card + 6 = n) := by
  classical
  have hn9 : n ≤ 9 := by omega
  have hsmul : ∀ (m : ↥H) (x : Fin n),
      m • x = ((m : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) x := fun _ _ => rfl
  have hfaith : ∀ m : ↥H, (∀ x : Fin n, m • x = x) → m = 1 := by
    intro m hm
    apply Subtype.ext
    apply Subtype.ext
    exact Equiv.ext fun x => hm x
  have hσ' : ∀ (m : ↥H) (x : Fin n), σ (m • x) = m • σ x := by
    intro m x
    rw [hsmul, hsmul]
    exact congrArg (fun f : Equiv.Perm (Fin n) => f x) (hcomm m m.2)
  let F : Finset (Fin n) := Finset.univ.filter fun x => ∀ m : ↥H, m • x = x
  have hFmem : ∀ x, x ∈ F ↔ ∀ m : ↥H, m • x = x := fun x => by simp [F]
  refine ⟨F, ?_, ?_, ?_⟩
  · intro h hh i hi
    exact (hFmem i).mp hi ⟨h, hh⟩
  · intro i hi
    exact pm4_comm_trivial hn9 hH hσ' (fun hall => hi ((hFmem i).mpr hall))
  · rcases pm4_fixed_card hn9 hH hfaith F hFmem with h5 | h6
    · left
      refine ⟨?_, h5⟩
      have hle : H ≤ altStabilizer n F := by
        intro h hh
        rw [mem_altStabilizer_iff]
        intro i hi
        exact (hFmem i).mp hi ⟨h, hh⟩
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [card_altStabilizer F (by omega), hH]
      have : n - F.card = 5 := by omega
      rw [this]
      decide
    · right
      exact h6

theorem a7_config (H : Subgroup (alternatingGroup (Fin 7))) [IsSimpleGroup ↥H]
    (hH : Nat.card ↥H = 60) (σ : Equiv.Perm (Fin 7)) (hσ : σ ≠ 1)
    (hcomm : ∀ h ∈ H, σ * (h : Equiv.Perm (Fin 7)) = (h : Equiv.Perm (Fin 7)) * σ) :
    ∃ p q : Fin 7, p ≠ q ∧ H = altStabilizer 7 {p, q} ∧ σ = Equiv.swap p q := by
  obtain ⟨F, -, hσF, hF⟩ := alt5_config (Or.inl rfl) H hH σ hσ hcomm
  have hsupp : σ.support ⊆ F := by
    intro i hi
    by_contra hiF
    exact (Equiv.Perm.mem_support.mp hi) (hσF i hiF)
  have h2 := Equiv.Perm.two_le_card_support_of_ne_one hσ
  have hFc := Finset.card_le_card hsupp
  rcases hF with ⟨hHF, hc⟩ | hc
  · have hFeq : σ.support = F := Finset.eq_of_subset_of_card_le hsupp (by omega)
    have hsw : σ.support.card = 2 := by omega
    obtain ⟨a, b, hab, hσab⟩ := Equiv.Perm.card_support_eq_two.mp hsw
    refine ⟨a, b, hab, ?_, hσab⟩
    rw [hHF, ← hFeq, hσab, Equiv.Perm.support_swap hab]
  · omega

theorem a9_config (H : Subgroup (alternatingGroup (Fin 9))) [IsSimpleGroup ↥H]
    (hH : Nat.card ↥H = 60) (σ : Equiv.Perm (Fin 9)) (hσ : σ ≠ 1) (hσ2 : σ * σ = 1)
    (hcomm : ∀ h ∈ H, σ * (h : Equiv.Perm (Fin 9)) = (h : Equiv.Perm (Fin 9)) * σ) :
    (∃ F : Finset (Fin 9), F.card = 4 ∧ H = altStabilizer 9 F ∧ ∀ i, i ∉ F → σ i = i) ∨
    (∃ a b : Fin 9, a ≠ b ∧ σ = Equiv.swap a b ∧
      ∀ h ∈ H, (h : Equiv.Perm (Fin 9)) a = a ∧ (h : Equiv.Perm (Fin 9)) b = b) := by
  obtain ⟨F, hfix, hσF, hF⟩ := alt5_config (Or.inr rfl) H hH σ hσ hcomm
  rcases hF with ⟨hHF, hc⟩ | hc
  · exact Or.inl ⟨F, by omega, hHF, hσF⟩
  · right
    have hsupp : σ.support ⊆ F := by
      intro i hi
      by_contra hiF
      exact (Equiv.Perm.mem_support.mp hi) (hσF i hiF)
    have h2 : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support (by rw [pow_two]; exact hσ2)
    have h2le := Equiv.Perm.two_le_card_support_of_ne_one hσ
    have hle3 : σ.support.card ≤ 3 := (Finset.card_le_card hsupp).trans (by omega)
    have hcard : σ.support.card = 2 := by omega
    obtain ⟨a, b, hab, hσab⟩ := Equiv.Perm.card_support_eq_two.mp hcard
    refine ⟨a, b, hab, hσab, fun h hh => ?_⟩
    have hs : σ.support = {a, b} := by rw [hσab, Equiv.Perm.support_swap hab]
    have ha : a ∈ F := hsupp (by rw [hs]; simp)
    have hb : b ∈ F := hsupp (by rw [hs]; simp)
    exact ⟨hfix h hh a ha, hfix h hh b hb⟩

section Generation

theorem pm4_eq_top_of_prime {n : ℕ} (hp : n.Prime) (L : Subgroup (alternatingGroup (Fin n)))
    (x₀ : Fin n) (htrans : ∀ x : Fin n, ∃ a ∈ L, (a : Perm (Fin n)) x₀ = x)
    {w : alternatingGroup (Fin n)} (hw : w ∈ L) (h3 : (w : Perm (Fin n)).IsThreeCycle) :
    L = ⊤ := by
  classical
  let M : Subgroup (Perm (Fin n)) := L.map (alternatingGroup (Fin n)).subtype
  have : MulAction.IsPretransitive ↥M (Fin n) := by
    refine MulAction.IsPretransitive.of_orbit (x₀ := x₀) fun x => ?_
    obtain ⟨a, ha, hax⟩ := htrans x
    exact ⟨⟨a.1, ⟨a, ha, rfl⟩⟩, hax⟩
  have : MulAction.IsPreprimitive ↥M (Fin n) :=
    MulAction.IsPreprimitive.of_prime_card (by rwa [Nat.card_eq_fintype_card, Fintype.card_fin])
  have hle := Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (G := M) inferInstance h3 ⟨w, hw, rfl⟩
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, hb, hba⟩ := hle a.2
  have : b = a := Subtype.ext hba
  rwa [← this]

@[expose] def kA : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def kB : alternatingGroup (Fin 7) :=
  ⟨swap 0 2 * swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def c456 : alternatingGroup (Fin 7) :=
  ⟨swap 4 5 * swap 5 6, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private def kC : alternatingGroup (Fin 7) :=
  ⟨swap 0 4 * swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

private def gA7 : alternatingGroup (Fin 7) :=
  ⟨swap 0 6 * swap 1 5 * (swap 2 3 * swap 3 4), Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem isThreeCycle_c456 :
    ((c456 : alternatingGroup (Fin 7)) : Perm (Fin 7)).IsThreeCycle := by
  show (swap (4 : Fin 7) 5 * swap 5 6).IsThreeCycle
  rw [swap_comm 4 5]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem c456_conj_swap :
    (swap (5 : Fin 7) 6 * ((c456 : alternatingGroup (Fin 7)) : Perm (Fin 7)) * swap 5 6) =
      ((c456 : alternatingGroup (Fin 7)) : Perm (Fin 7))⁻¹ := by
  decide

@[expose] def kleinA7 : Subgroup (alternatingGroup (Fin 7)) := Subgroup.closure {kA, kB}

theorem coe_kleinA7 : (kleinA7 : Set (alternatingGroup (Fin 7))) =
    ↑({1, kA, kB, kA * kB} : Finset (alternatingGroup (Fin 7))) := by
  ext x
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    SetLike.mem_coe]
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = kA ∨ x = kB ∨ x = kA * kB)
      ?_ ?_ ?_ ?_ hx
    · rintro y (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · rintro y z - - (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide
    · rintro y - (rfl | rfl | rfl | rfl) <;> decide
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem card_kleinA7 : Nat.card ↥kleinA7 = 4 := by
  have h : Nat.card ↥kleinA7 = Set.ncard (kleinA7 : Set (alternatingGroup (Fin 7))) :=
    Nat.card_coe_set_eq _
  rw [h, coe_kleinA7, Set.ncard_coe_finset]
  decide

theorem kleinA7_le : kleinA7 ≤ altStabilizer 7 {4, 5, 6} := by
  rw [kleinA7, Subgroup.closure_le]
  rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, mem_altStabilizer_iff] <;> decide

theorem exists_gen_kleinA7 : ∃ g : alternatingGroup (Fin 7),
    Subgroup.closure ((kleinA7 : Set (alternatingGroup (Fin 7))) ∪
      ((kleinA7.map (MulAut.conj g).toMonoidHom : Subgroup (alternatingGroup (Fin 7))) :
        Set (alternatingGroup (Fin 7)))) = ⊤ := by
  refine ⟨gA7, ?_⟩
  set L := Subgroup.closure ((kleinA7 : Set (alternatingGroup (Fin 7))) ∪
      ((kleinA7.map (MulAut.conj gA7).toMonoidHom : Subgroup (alternatingGroup (Fin 7))) :
        Set (alternatingGroup (Fin 7)))) with hL
  have hkA₀ : kA ∈ kleinA7 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hkB₀ : kB ∈ kleinA7 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hkA : kA ∈ L := Subgroup.subset_closure (Or.inl hkA₀)
  have hkB : kB ∈ L := Subgroup.subset_closure (Or.inl hkB₀)
  have hc : gA7 * kA * gA7⁻¹ ∈ L := Subgroup.subset_closure (Or.inr ⟨kA, hkA₀, rfl⟩)
  have hd : gA7 * kB * gA7⁻¹ ∈ L := Subgroup.subset_closure (Or.inr ⟨kB, hkB₀, rfl⟩)
  have hw : (kA * (gA7 * kA * gA7⁻¹)) * (kA * (gA7 * kA * gA7⁻¹)) ∈ L :=
    mul_mem (mul_mem hkA hc) (mul_mem hkA hc)
  refine pm4_eq_top_of_prime (by norm_num) L 0 ?_ hw ?_
  · intro x
    fin_cases x
    · exact ⟨1, one_mem _, by decide⟩
    · exact ⟨kA, hkA, by decide⟩
    · exact ⟨kB, hkB, by decide⟩
    · exact ⟨kA * kB, mul_mem hkA hkB, by decide⟩
    · exact ⟨(gA7 * kA * gA7⁻¹) * (kA * kB), mul_mem hc (mul_mem hkA hkB), by decide⟩
    · exact ⟨(gA7 * kB * gA7⁻¹) * ((gA7 * kA * gA7⁻¹) * (kA * kB)),
        mul_mem hd (mul_mem hc (mul_mem hkA hkB)), by decide⟩
    · exact ⟨(gA7 * kB * gA7⁻¹) * (kA * kB), mul_mem hd (mul_mem hkA hkB), by decide⟩
  · have h : (((kA * (gA7 * kA * gA7⁻¹)) * (kA * (gA7 * kA * gA7⁻¹)) :
        alternatingGroup (Fin 7)) : Perm (Fin 7)) = swap 2 3 * swap 2 4 := by decide
    rw [h]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem gen_alt5_cycle :
    Subgroup.closure ((altStabilizer 7 {5, 6} : Set (alternatingGroup (Fin 7))) ∪ {c456}) = ⊤ := by
  set L := Subgroup.closure ((altStabilizer 7 {5, 6} : Set (alternatingGroup (Fin 7))) ∪ {c456})
    with hL
  have hS : ∀ x ∈ altStabilizer 7 {5, 6}, x ∈ L := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hc : c456 ∈ L := Subgroup.subset_closure (Or.inr rfl)
  have hkA : kA ∈ L := hS _ (by rw [mem_altStabilizer_iff]; decide)
  have hkB : kB ∈ L := hS _ (by rw [mem_altStabilizer_iff]; decide)
  have hkC : kC ∈ L := hS _ (by rw [mem_altStabilizer_iff]; decide)
  refine pm4_eq_top_of_prime (by norm_num) L 0 ?_ hc isThreeCycle_c456
  intro x
  fin_cases x
  · exact ⟨1, one_mem _, by decide⟩
  · exact ⟨kA, hkA, by decide⟩
  · exact ⟨kB, hkB, by decide⟩
  · exact ⟨kA * kB, mul_mem hkA hkB, by decide⟩
  · exact ⟨kC, hkC, by decide⟩
  · exact ⟨c456 * kC, mul_mem hc hkC, by decide⟩
  · exact ⟨c456 * (c456 * kC), mul_mem hc (mul_mem hc hkC), by decide⟩

end Generation

section Pairs

theorem pm4_exists_perm_pair {α : Type*} [DecidableEq α] {p q c d : α} (hpq : p ≠ q)
    (hcd : c ≠ d) : ∃ ρ : Perm α, ρ p = c ∧ ρ q = d := by
  refine ⟨swap (swap p c q) d * swap p c, ?_, ?_⟩
  · have h1 : c ≠ swap p c q := by
      intro h
      apply hpq
      have := congrArg (swap p c) h
      rwa [swap_apply_right, swap_apply_self] at this
    rw [Perm.mul_apply, swap_apply_left]
    exact swap_apply_of_ne_of_ne h1 hcd
  · rw [Perm.mul_apply, swap_apply_left]

theorem exists_perm_pair (p q : Fin 7) (hpq : p ≠ q) :
    ∃ ρ : Perm (Fin 7), ρ p = 5 ∧ ρ q = 6 :=
  pm4_exists_perm_pair hpq (by decide)

end Pairs

end CFSG.CGT.PushingUpLit.CGT6X.End4
