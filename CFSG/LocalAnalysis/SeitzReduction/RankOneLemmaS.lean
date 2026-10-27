module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.SeitzReduction.RankOne

open Equiv MulAction

section Group

variable {G : Type*} [Group G]

theorem commute_of_inf_eq_bot {M K L : Subgroup G} (hKM : K ≤ M) (hLM : L ≤ M)
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hKL : K ⊓ L = ⊥) {k l : G} (hk : k ∈ K) (hl : l ∈ L) : k * l = l * k := by
  have h1 : k * l * k⁻¹ * l⁻¹ ∈ L := L.mul_mem (hLn k (hKM hk) l hl) (L.inv_mem hl)
  have h2 : k * l * k⁻¹ * l⁻¹ ∈ K := by
    have := K.mul_mem hk (hKn l (hLM hl) k⁻¹ (K.inv_mem hk))
    simpa only [mul_assoc] using this
  have h3 : k * l * k⁻¹ * l⁻¹ = 1 := by
    have : k * l * k⁻¹ * l⁻¹ ∈ K ⊓ L := ⟨h2, h1⟩
    rwa [hKL, Subgroup.mem_bot] at this
  calc k * l = (k * l * k⁻¹ * l⁻¹) * (l * k) := by group
    _ = l * k := by rw [h3, one_mul]

theorem pow_eq_self_of_sq_eq_one {s : G} (hs : s ^ 2 = 1) {k : ℕ} (hk : Odd k) : s ^ k = s := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, hs, one_pow, one_mul]

theorem eq_inv_pow_of_commute {u s : G} (hus : Commute u s) (hs : s ^ 2 = 1) {k : ℕ}
    (hk : Odd k) (h : (u * s) ^ k = 1) : s = (u ^ k)⁻¹ := by
  rw [hus.mul_pow, pow_eq_self_of_sq_eq_one hs hk] at h
  exact eq_inv_of_mul_eq_one_right h

theorem conj_mem_inf_centralizer {A M : Subgroup G} {T : Set G}
    (hM : ∀ x ∈ A, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hT : ∀ x ∈ A, ∀ t ∈ T, x⁻¹ * t * x ∈ T)
    {x w : G} (hx : x ∈ A) (hw : w ∈ M ⊓ Subgroup.centralizer T) :
    x * w * x⁻¹ ∈ M ⊓ Subgroup.centralizer T := by
  refine ⟨hM x hx w hw.1, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
  have h := Subgroup.mem_centralizer_iff.1 hw.2 (x⁻¹ * t * x) (hT x hx t ht)
  calc t * (x * w * x⁻¹) = x * ((x⁻¹ * t * x) * w) * x⁻¹ := by group
    _ = x * (w * (x⁻¹ * t * x)) * x⁻¹ := by rw [h]
    _ = x * w * x⁻¹ * t := by group

end Group

section Perm

variable {Ω : Type*}

theorem exists_apply_eq_of_two_transitive {N : Subgroup (Perm Ω)}
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d) (β γ : Ω) :
    ∃ x ∈ N, x β = γ := by
  by_cases hβγ : β = γ
  · exact ⟨1, N.one_mem, by rw [hβγ, Perm.one_apply]⟩
  · obtain ⟨x, hx, hxβ, -⟩ := h2 β γ γ β hβγ (Ne.symm hβγ)
    exact ⟨x, hx, hxβ⟩

theorem exists_apply_eq_of_normal_of_two_transitive {N M : Subgroup (Perm Ω)}
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    (hMn : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hM : M ≠ ⊥) (β γ : Ω) :
    ∃ m ∈ M, m β = γ := by
  by_cases hβγ : β = γ
  · exact ⟨1, M.one_mem, by rw [hβγ, Perm.one_apply]⟩
  obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hM
  obtain ⟨δ, hδ⟩ : ∃ δ, m δ ≠ δ := by
    by_contra! h
    exact hm1 (Subtype.ext (Perm.ext h))
  obtain ⟨x, hx, hxδ, hxmδ⟩ := h2 δ (m δ) β γ (Ne.symm hδ) hβγ
  refine ⟨x * m * x⁻¹, hMn x hx m hm, ?_⟩
  subst hxδ
  simp [Perm.mul_apply, hxmδ]

theorem existsUnique_apply_eq_of_commute {A : Subgroup (Perm Ω)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htr : ∀ β γ : Ω, ∃ a ∈ A, a β = γ) (β γ : Ω) :
    ∃! a : A, (a : Perm Ω) β = γ := by
  obtain ⟨a, ha, haβ⟩ := htr β γ
  refine ⟨⟨a, ha⟩, haβ, ?_⟩
  rintro ⟨b, hb⟩ hbβ
  change b β = γ at hbβ
  refine Subtype.ext (Perm.ext fun δ => ?_)
  obtain ⟨c, hc, rfl⟩ := htr β δ
  have hbc : b (c β) = c (b β) := by
    rw [← Perm.mul_apply, hcomm b hb c hc, Perm.mul_apply]
  have hac : a (c β) = c (a β) := by
    rw [← Perm.mul_apply, hcomm a ha c hc, Perm.mul_apply]
  change b (c β) = a (c β)
  rw [hbc, hac, haβ, hbβ]

theorem inf_stabilizer_eq_bot_of_existsUnique {A : Subgroup (Perm Ω)}
    (hreg : ∀ β γ : Ω, ∃! a : A, (a : Perm Ω) β = γ) (α : Ω) :
    A ⊓ stabilizer (Perm Ω) α = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  have h1 : (⟨a, ha.1⟩ : A) = 1 := (hreg α α).unique (mem_stabilizer_iff.1 ha.2) rfl
  exact congrArg Subtype.val h1

theorem card_eq_card_mul_card_inf_stabilizer {M : Subgroup (Perm Ω)}
    (htr : ∀ β γ : Ω, ∃ m ∈ M, m β = γ) (α : Ω) :
    Nat.card M = Nat.card Ω * Nat.card ↥(M ⊓ stabilizer (Perm Ω) α) := by
  have : IsPretransitive M Ω := ⟨fun β γ => by
    obtain ⟨m, hm, h⟩ := htr β γ
    exact ⟨⟨m, hm⟩, h⟩⟩
  have h1 := (stabilizer M α).card_mul_index
  rw [index_stabilizer_of_transitive] at h1
  have hstab : stabilizer M α = (stabilizer (Perm Ω) α).subgroupOf M := by
    ext; rfl
  have h3 : Nat.card (stabilizer M α) = Nat.card ↥(M ⊓ stabilizer (Perm Ω) α) := by
    rw [hstab, ← Subgroup.card_subtype M, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← h1, h3, mul_comm]

theorem odd_orderOf_of_apply_eq {N : Subgroup (Perm Ω)} (htr : ∀ β γ : Ω, ∃ x ∈ N, x β = γ)
    {α : Ω} (hodd : Odd (Nat.card ↥(N ⊓ stabilizer (Perm Ω) α)))
    {g : Perm Ω} (hg : g ∈ N) {γ : Ω} (hγ : g γ = γ) : Odd (orderOf g) := by
  obtain ⟨x, hx, rfl⟩ := htr α γ
  have hmem : x⁻¹ * g * x ∈ N ⊓ stabilizer (Perm Ω) α := by
    refine Subgroup.mem_inf.2 ⟨N.mul_mem (N.mul_mem (N.inv_mem hx) hg) hx, ?_⟩
    rw [mem_stabilizer_iff, Perm.smul_def, Perm.mul_apply, Perm.mul_apply, hγ]
    simp
  have hconj : orderOf (x⁻¹ * g * x) = orderOf g :=
    SemiconjBy.orderOf_eq x (by rw [SemiconjBy]; group)
  have hdvd := orderOf_dvd_natCard (⟨x⁻¹ * g * x, hmem⟩ : ↥(N ⊓ stabilizer (Perm Ω) α))
  rw [Subgroup.orderOf_mk, hconj] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

theorem eq_bot_of_odd_card {M K : Subgroup (Perm Ω)} (hKM : K ≤ M)
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (htr : ∀ β γ : Ω, ∃ m ∈ M, m β = γ)
    {n : ℕ} (hΩ : Nat.card Ω = 2 ^ n) (hodd : Odd (Nat.card K)) : K = ⊥ := by
  have : IsPretransitive M Ω := ⟨fun β γ => by
    obtain ⟨m, hm, h⟩ := htr β γ
    exact ⟨⟨m, hm⟩, h⟩⟩
  have : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hKM).2 fun h k hh hk => hKn k hk h hh
  have hfix : ∀ α : Ω, ∀ k ∈ K, k α = α := by
    intro α k hk
    have hB1 : (orbit (K.subgroupOf M) α).ncard ∣ 2 ^ n :=
      hΩ ▸ (IsBlock.orbit_of_normal (G := M) (N := K.subgroupOf M) α).ncard_dvd_card
        (nonempty_orbit α)
    have hB2 : (orbit (K.subgroupOf M) α).ncard ∣ Nat.card K := by
      rw [← index_stabilizer]
      have := (stabilizer (K.subgroupOf M) α).index_dvd_card
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at this
    have hB3 : (orbit (K.subgroupOf M) α).ncard = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hB1
      have hodd' : Odd (orbit (K.subgroupOf M) α).ncard := Odd.of_dvd_nat hodd hB2
      rw [hj] at hodd' ⊢
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rfl
      · exact absurd (Nat.even_pow.2 ⟨even_two, hjpos.ne'⟩) (Nat.not_even_iff_odd.2 hodd')
    obtain ⟨b, hb⟩ := Set.ncard_eq_one.1 hB3
    have hα : α ∈ orbit (K.subgroupOf M) α := mem_orbit_self α
    have hkα : k α ∈ orbit (K.subgroupOf M) α :=
      ⟨⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.2 hk⟩, rfl⟩
    rw [hb] at hα hkα
    exact hkα.trans hα.symm
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  exact Perm.ext fun β => hfix β k hk

section Minimal

variable {N M K : Subgroup (Perm Ω)}

theorem exists_conj_not_mem
    (hMmin : ∀ M' : Subgroup (Perm Ω), M' ≠ ⊥ → M' ≤ M →
      (∀ x ∈ N, ∀ m ∈ M', x * m * x⁻¹ ∈ M') → M' = M)
    (hK1 : K ≠ ⊥) (hKM : K ≤ M) (hKne : K ≠ M) :
    ∃ g ∈ N, ∃ k ∈ K, g * k * g⁻¹ ∉ K := by
  by_contra! h
  exact hKne (hMmin K hK1 hKM h)

variable [Finite Ω]

theorem conj_mem_or_commute (hMn : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hKM : K ≤ M)
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hKmin : ∀ K' : Subgroup (Perm Ω), K' ≠ ⊥ → K' ≤ K →
      (∀ m ∈ M, ∀ k ∈ K', m * k * m⁻¹ ∈ K') → K' = K)
    {g : Perm Ω} (hg : g ∈ N) :
    (∀ k ∈ K, g * k * g⁻¹ ∈ K) ∨
      ∀ k ∈ K, ∀ k' ∈ K, g * k * g⁻¹ * k' = k' * (g * k * g⁻¹) := by
  set L := K.map (MulAut.conj g).toMonoidHom with hL
  have hmemL : ∀ x, x ∈ L ↔ ∃ k ∈ K, g * k * g⁻¹ = x := by
    intro x
    simp [hL, Subgroup.mem_map, MulAut.conj_apply]
  have hLM : L ≤ M := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (hmemL x).1 hx
    exact hMn g hg k (hKM hk)
  have hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    obtain ⟨k, hk, rfl⟩ := (hmemL l).1 hl
    have hm' : g⁻¹ * m * g ∈ M := by simpa using hMn g⁻¹ (N.inv_mem hg) m hm
    exact (hmemL _).2 ⟨(g⁻¹ * m * g) * k * (g⁻¹ * m * g)⁻¹, hKn _ hm' k hk, by group⟩
  by_cases hbot : L ⊓ K = ⊥
  · right
    intro k hk k' hk'
    exact commute_of_inf_eq_bot hLM hKM hLn hKn hbot ((hmemL _).2 ⟨k, hk, rfl⟩) hk'
  · left
    have hinf : L ⊓ K = K :=
      hKmin _ hbot inf_le_right fun m hm x hx => ⟨hLn m hm x hx.1, hKn m hm x hx.2⟩
    have hKL : K ≤ L := hinf ▸ inf_le_left
    have hcard : Nat.card L = Nat.card K :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hKeqL : K = L := Subgroup.eq_of_le_of_card_ge hKL hcard.le
    intro k hk
    have : g * k * g⁻¹ ∈ L := (hmemL _).2 ⟨k, hk, rfl⟩
    rwa [← hKeqL] at this

theorem exists_not_commute_of_minimal (hMn : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hMmin : ∀ M' : Subgroup (Perm Ω), M' ≠ ⊥ → M' ≤ M →
      (∀ x ∈ N, ∀ m ∈ M', x * m * x⁻¹ ∈ M') → M' = M)
    (hMnab : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a)
    (hK1 : K ≠ ⊥) (hKM : K ≤ M) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hKmin : ∀ K' : Subgroup (Perm Ω), K' ≠ ⊥ → K' ≤ K →
      (∀ m ∈ M, ∀ k ∈ K', m * k * m⁻¹ ∈ K') → K' = K) :
    ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
  by_contra! hab
  set T : Set (Perm Ω) := {x | ∃ g ∈ N, ∃ k ∈ K, g * k * g⁻¹ = x} with hT
  have hKW : K ≤ M ⊓ Subgroup.centralizer T := by
    intro k hk
    refine ⟨hKM hk, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨g, hg, k', hk', rfl⟩
    rcases conj_mem_or_commute hMn hKM hKn hKmin hg with h | h
    · exact hab _ (h k' hk') k hk
    · exact h k' hk' k hk
  have hWn : ∀ x ∈ N, ∀ w ∈ M ⊓ Subgroup.centralizer T, x * w * x⁻¹ ∈ M ⊓ Subgroup.centralizer T :=
    fun x hx w hw => conj_mem_inf_centralizer hMn (by
      rintro x hx _ ⟨g, hg, k, hk, rfl⟩
      exact ⟨x⁻¹ * g, N.mul_mem (N.inv_mem hx) hg, k, hk, by group⟩) hx hw
  have hW : M ⊓ Subgroup.centralizer T = M :=
    hMmin _ (fun h => hK1 (eq_bot_iff.2 (h ▸ hKW))) inf_le_left hWn
  have hKZ : K ≤ M ⊓ Subgroup.centralizer (M : Set (Perm Ω)) := by
    intro k hk
    refine ⟨hKM hk, Subgroup.mem_centralizer_iff.2 fun m hm => ?_⟩
    have hmW : m ∈ M ⊓ Subgroup.centralizer T := by rw [hW]; exact hm
    exact (Subgroup.mem_centralizer_iff.1 hmW.2 k ⟨1, N.one_mem, k, hk, by group⟩).symm
  have hZn : ∀ x ∈ N, ∀ z ∈ M ⊓ Subgroup.centralizer (M : Set (Perm Ω)),
      x * z * x⁻¹ ∈ M ⊓ Subgroup.centralizer (M : Set (Perm Ω)) :=
    fun x hx z hz => conj_mem_inf_centralizer hMn (fun x hx m hm => by
      simpa using hMn x⁻¹ (N.inv_mem hx) m hm) hx hz
  have hZ : M ⊓ Subgroup.centralizer (M : Set (Perm Ω)) = M :=
    hMmin _ (fun h => hK1 (eq_bot_iff.2 (h ▸ hKZ))) inf_le_left hZn
  obtain ⟨a, ha, b, hb, hne⟩ := hMnab
  have hbZ : b ∈ M ⊓ Subgroup.centralizer (M : Set (Perm Ω)) := by rw [hZ]; exact hb
  exact hne (Subgroup.mem_centralizer_iff.1 hbZ.2 a ha)

theorem false_of_minimal_normal_ne
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    (hfix : ∀ g ∈ N, ∀ γ : Ω, g γ = γ → Odd (orderOf g))
    {n : ℕ} (hΩ : Nat.card Ω = 2 ^ n)
    (hMN : M ≤ N) (hMn : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hMmin : ∀ M' : Subgroup (Perm Ω), M' ≠ ⊥ → M' ≤ M →
      (∀ x ∈ N, ∀ m ∈ M', x * m * x⁻¹ ∈ M') → M' = M)
    (hMtr : ∀ β γ : Ω, ∃ m ∈ M, m β = γ)
    (hMnab : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a)
    (hK1 : K ≠ ⊥) (hKM : K ≤ M) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hKmin : ∀ K' : Subgroup (Perm Ω), K' ≠ ⊥ → K' ≤ K →
      (∀ m ∈ M, ∀ k ∈ K', m * k * m⁻¹ ∈ K') → K' = K)
    (hKne : K ≠ M) : False := by
  have hKnab := exists_not_commute_of_minimal hMn hMmin hMnab hK1 hKM hKn hKmin
  set Z := M ⊓ Subgroup.centralizer (K : Set (Perm Ω)) with hZ
  have hZM : Z ≤ M := inf_le_left
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    conj_mem_inf_centralizer (A := M)
      (fun x hx m' hm' => M.mul_mem (M.mul_mem hx hm') (M.inv_mem hx))
      (fun x hx t ht => by simpa using hKn x⁻¹ (M.inv_mem hx) t ht) hm hz
  have hKZ : K ⊓ Z = ⊥ := by
    by_contra hne
    have hKZK := hKmin (K ⊓ Z) hne inf_le_left
      fun m hm x hx => ⟨hKn m hm x hx.1, hZn m hm x hx.2⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hKnab
    have hb' : b ∈ K ⊓ Z := by rw [hKZK]; exact hb
    exact hab (Subgroup.mem_centralizer_iff.1 hb'.2.2 a ha)
  have hZ1 : Z ≠ ⊥ := by
    obtain ⟨g, hg, k, hk, hgk⟩ := exists_conj_not_mem hMmin hK1 hKM hKne
    rcases conj_mem_or_commute hMn hKM hKn hKmin hg with h | h
    · exact absurd (h k hk) hgk
    · intro hbot
      have hmem : g * k * g⁻¹ ∈ Z :=
        ⟨hMn g hg k (hKM hk), Subgroup.mem_centralizer_iff.2 fun k' hk' => (h k hk k' hk').symm⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hgk (by rw [hmem]; exact K.one_mem)
  have hinv : ∀ H : Subgroup (Perm Ω), H ≠ ⊥ → H ≤ M → (∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H) →
      ∃ s ∈ H, orderOf s = 2 := by
    intro H hH1 hHM hHn
    have heven : 2 ∣ Nat.card H := by
      have : ¬ Odd (Nat.card H) := fun hodd => hH1 (eq_bot_of_odd_card hHM hHn hMtr hΩ hodd)
      exact even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 this)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨s, hs⟩, hord⟩ := exists_prime_orderOf_dvd_card' 2 heven
    exact ⟨s, hs, by rwa [Subgroup.orderOf_mk] at hord⟩
  obtain ⟨s₁, hs₁K, hs₁⟩ := hinv K hK1 hKM hKn
  obtain ⟨s₂, hs₂Z, hs₂⟩ := hinv Z hZ1 hZM hZn
  have hsq : ∀ s : Perm Ω, orderOf s = 2 → s ^ 2 = 1 := fun s hs => hs ▸ pow_orderOf_eq_one s
  have hnofix : ∀ s ∈ N, orderOf s = 2 → ∀ γ, s γ ≠ γ := by
    intro s hs hord γ hγ
    have := hfix s hs γ hγ
    rw [hord] at this
    exact Nat.not_odd_iff_even.2 even_two this
  have hcomm12 : Commute s₁ s₂ := Subgroup.mem_centralizer_iff.1 hs₂Z.2 s₁ hs₁K
  have hs₂ne : s₂ ∉ K := by
    intro h
    have : s₂ ∈ K ⊓ Z := ⟨h, hs₂Z⟩
    rw [hKZ, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hs₂
    exact absurd hs₂ (by norm_num)
  have hs₁ne : s₁ ∉ Z := by
    intro h
    have : s₁ ∈ K ⊓ Z := ⟨hs₁K, h⟩
    rw [hKZ, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hs₁
    exact absurd hs₁ (by norm_num)
  have hs₁₂ : orderOf (s₁ * s₂) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [hcomm12.mul_pow, hsq s₁ hs₁, hsq s₂ hs₂, one_mul]
    · intro h
      exact hs₂ne (eq_inv_of_mul_eq_one_right h ▸ K.inv_mem hs₁K)
  have hs₁N : s₁ ∈ N := hMN (hKM hs₁K)
  have hs₁₂N : s₁ * s₂ ∈ N := N.mul_mem hs₁N (hMN (hZM hs₂Z))
  obtain ⟨α⟩ : Nonempty Ω :=
    (Nat.card_pos_iff.1 (hΩ ▸ pow_pos two_pos n : 0 < Nat.card Ω)).1
  obtain ⟨g, hg, hgα, hgβ⟩ := h2 α (s₁ α) α ((s₁ * s₂) α) (Ne.symm (hnofix s₁ hs₁N hs₁ α))
    (Ne.symm (hnofix _ hs₁₂N hs₁₂ α))
  have hgα' : g⁻¹ α = α := by rw [Perm.inv_eq_iff_eq]; exact hgα.symm
  have hℓα : (g * s₁ * g⁻¹) α = (s₁ * s₂) α := by
    rw [Perm.mul_apply, Perm.mul_apply, hgα']
    exact hgβ
  have hyα : ((g * s₁ * g⁻¹)⁻¹ * (s₁ * s₂)) α = α := by
    rw [Perm.mul_apply, ← hℓα]
    simp
  have hyN : (g * s₁ * g⁻¹)⁻¹ * (s₁ * s₂) ∈ N :=
    N.mul_mem (N.inv_mem (N.mul_mem (N.mul_mem hg hs₁N) (N.inv_mem hg))) hs₁₂N
  have hyodd := hfix _ hyN α hyα
  have hy1 := pow_orderOf_eq_one ((g * s₁ * g⁻¹)⁻¹ * (s₁ * s₂))
  set k := orderOf ((g * s₁ * g⁻¹)⁻¹ * (s₁ * s₂)) with hk
  rcases conj_mem_or_commute hMn hKM hKn hKmin hg with h | h
  ·
    have huK : (g * s₁ * g⁻¹)⁻¹ * s₁ ∈ K := K.mul_mem (K.inv_mem (h s₁ hs₁K)) hs₁K
    have hus : Commute ((g * s₁ * g⁻¹)⁻¹ * s₁) s₂ :=
      Subgroup.mem_centralizer_iff.1 hs₂Z.2 _ huK
    rw [← mul_assoc] at hy1
    have := eq_inv_pow_of_commute hus (hsq s₂ hs₂) hyodd hy1
    exact hs₂ne (this ▸ K.inv_mem (K.pow_mem huK k))
  ·
    have hℓZ : g * s₁ * g⁻¹ ∈ Z :=
      ⟨hMn g hg s₁ (hKM hs₁K), Subgroup.mem_centralizer_iff.2 fun k' hk' => (h s₁ hs₁K k' hk').symm⟩
    have hvZ : (g * s₁ * g⁻¹)⁻¹ * s₂ ∈ Z := Z.mul_mem (Z.inv_mem hℓZ) hs₂Z
    have hvs : Commute ((g * s₁ * g⁻¹)⁻¹ * s₂) s₁ :=
      (Subgroup.mem_centralizer_iff.1 hvZ.2 s₁ hs₁K).symm
    rw [hcomm12.eq, ← mul_assoc] at hy1
    have := eq_inv_pow_of_commute hvs (hsq s₁ hs₁) hyodd hy1
    exact hs₁ne (this ▸ Z.inv_mem (Z.pow_mem hvZ k))

theorem eq_bot_or_eq_of_minimal_normal
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    (hfix : ∀ g ∈ N, ∀ γ : Ω, g γ = γ → Odd (orderOf g))
    {n : ℕ} (hΩ : Nat.card Ω = 2 ^ n)
    (hMN : M ≤ N) (hMn : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hMmin : ∀ M' : Subgroup (Perm Ω), M' ≠ ⊥ → M' ≤ M →
      (∀ x ∈ N, ∀ m ∈ M', x * m * x⁻¹ ∈ M') → M' = M)
    (hMtr : ∀ β γ : Ω, ∃ m ∈ M, m β = γ)
    (hMnab : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a)
    (hKM : K ≤ M) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) : K = ⊥ ∨ K = M := by
  by_contra! hne
  obtain ⟨hK1, hKne⟩ := hne
  have : Finite (Subgroup (Perm Ω)) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨K₁, hK₁K, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun K' : Subgroup (Perm Ω) => K' ≠ ⊥ ∧ K' ≤ M ∧ ∀ m ∈ M, ∀ k ∈ K', m * k * m⁻¹ ∈ K') K
    ⟨hK1, hKM, hKn⟩
  exact false_of_minimal_normal_ne h2 hfix hΩ hMN hMn hMmin hMtr hMnab hmin.1.1 hmin.1.2.1
    hmin.1.2.2 (fun K' h1 h2 h3 => le_antisymm h2 (hmin.2 ⟨h1, h2.trans hmin.1.2.1, h3⟩ h2))
    (fun h => hKne (le_antisymm hKM (h ▸ hK₁K)))

end Minimal

variable [Finite Ω]

theorem sq_eq_one_of_minimal_normal_of_commute {N M : Subgroup (Perm Ω)}
    (hMn : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hMmin : ∀ M' : Subgroup (Perm Ω), M' ≠ ⊥ → M' ≤ M →
      (∀ x ∈ N, ∀ m ∈ M', x * m * x⁻¹ ∈ M') → M' = M)
    (hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (heven : 2 ∣ Nat.card M) {a : Perm Ω}
    (ha : a ∈ M) : a ^ 2 = 1 := by
  let Q : Subgroup (Perm Ω) :=
    { carrier := {y | ∃ m ∈ M, m ^ 2 = y}
      one_mem' := ⟨1, M.one_mem, one_pow 2⟩
      mul_mem' := by
        rintro _ _ ⟨m₁, hm₁, rfl⟩ ⟨m₂, hm₂, rfl⟩
        exact ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, Commute.mul_pow (hcomm m₁ hm₁ m₂ hm₂) 2⟩
      inv_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨m⁻¹, M.inv_mem hm, inv_pow m 2⟩ }
  have hQM : Q ≤ M := by
    rintro _ ⟨m, hm, rfl⟩
    exact M.pow_mem hm 2
  have hQn : ∀ x ∈ N, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := by
    rintro x hx _ ⟨m, hm, rfl⟩
    exact ⟨x * m * x⁻¹, hMn x hx m hm, conj_pow⟩
  have hQne : Q ≠ M := by
    intro hQ
    have hsurj : Function.Surjective (fun m : M => m ^ 2) := by
      rintro ⟨y, hy⟩
      obtain ⟨m, hm, rfl⟩ : ∃ m ∈ M, m ^ 2 = y := by
        rw [← hQ] at hy
        exact hy
      exact ⟨⟨m, hm⟩, rfl⟩
    have hinj := Finite.injective_iff_surjective.2 hsurj
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 heven
    have h1 : s ^ 2 = (1 : M) ^ 2 := by rw [← hs, pow_orderOf_eq_one, one_pow]
    have h2 : s = 1 := hinj h1
    rw [h2, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hQ : Q = ⊥ := by
    by_contra h
    exact hQne (hMmin Q h hQM hQn)
  have : a ^ 2 ∈ Q := ⟨a, ha, rfl⟩
  rwa [hQ, Subgroup.mem_bot] at this

theorem minimal_normal_regular_or_simple {N : Subgroup (Perm Ω)}
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    {n : ℕ} (hΩ : Nat.card Ω = 2 ^ n) (α : Ω)
    (hodd : Odd (Nat.card ↥(N ⊓ stabilizer (Perm Ω) α)))
    {M : Subgroup (Perm Ω)} (hM1 : M ≠ ⊥) (hMN : M ≤ N) (hMn : (M.subgroupOf N).Normal)
    (hMmin : ∀ M' : Subgroup (Perm Ω), M' ≠ ⊥ → M' ≤ M → (M'.subgroupOf N).Normal → M' = M) :
    ((∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧ (∀ a ∈ M, a ^ 2 = 1) ∧ Nat.card M = 2 ^ n ∧
        ∀ β γ : Ω, ∃! a : M, (a : Perm Ω) β = γ) ∨
    (IsSimpleGroup M ∧ (∃ a b : M, a * b ≠ b * a) ∧ (∀ β γ : Ω, ∃ s ∈ M, s β = γ) ∧
      Nat.card M = 2 ^ n * Nat.card ↥(M ⊓ stabilizer (Perm Ω) α) ∧
      Odd (Nat.card ↥(M ⊓ stabilizer (Perm Ω) α))) := by
  have hMn' : ∀ x ∈ N, ∀ m ∈ M, x * m * x⁻¹ ∈ M := fun x hx m hm =>
    (Subgroup.normal_subgroupOf_iff hMN).1 hMn m x hm hx
  have hMmin' : ∀ M' : Subgroup (Perm Ω), M' ≠ ⊥ → M' ≤ M →
      (∀ x ∈ N, ∀ m ∈ M', x * m * x⁻¹ ∈ M') → M' = M := fun M' h1 h2 h3 =>
    hMmin M' h1 h2 ((Subgroup.normal_subgroupOf_iff (h2.trans hMN)).2 fun h k hh hk => h3 k hk h hh)
  have hfix : ∀ g ∈ N, ∀ γ : Ω, g γ = γ → Odd (orderOf g) := fun g hg γ hγ =>
    odd_orderOf_of_apply_eq (exists_apply_eq_of_two_transitive h2) hodd hg hγ
  have hMtr := exists_apply_eq_of_normal_of_two_transitive h2 hMn' hM1
  have hcard := card_eq_card_mul_card_inf_stabilizer hMtr α
  rw [hΩ] at hcard
  by_cases hab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a
  · have hreg := existsUnique_apply_eq_of_commute hab hMtr
    rw [inf_stabilizer_eq_bot_of_existsUnique hreg α, Subgroup.card_bot, mul_one] at hcard
    have hn : n ≠ 0 := by
      rintro rfl
      exact hM1 (Subgroup.card_eq_one.1 (by rw [hcard, pow_zero]))
    have heven : 2 ∣ Nat.card M := hcard ▸ dvd_pow_self 2 hn
    exact Or.inl ⟨hab, fun a ha => sq_eq_one_of_minimal_normal_of_commute hMn' hMmin' hab heven ha,
      hcard, hreg⟩
  push Not at hab
  right
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM1
  refine ⟨{ eq_bot_or_eq_top_of_normal := fun H hH => ?_ }, ?_, hMtr, hcard,
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le (inf_le_inf_right _ hMN))⟩
  · have hKM : H.map M.subtype ≤ M := Subgroup.map_subtype_le H
    have hKn : ∀ m ∈ M, ∀ k ∈ H.map M.subtype, m * k * m⁻¹ ∈ H.map M.subtype := by
      rintro m hm _ ⟨h, hh, rfl⟩
      exact ⟨⟨m, hm⟩ * h * ⟨m, hm⟩⁻¹, hH.conj_mem h hh ⟨m, hm⟩, rfl⟩
    rcases eq_bot_or_eq_of_minimal_normal h2 hfix hΩ hMN hMn' hMmin' hMtr hab hKM hKn with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective H M.subtype_injective).1 h)
    · refine Or.inr (Subgroup.map_injective M.subtype_injective ?_)
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · obtain ⟨a, ha, b, hb, hne⟩ := hab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hne (congrArg Subtype.val h)⟩

end Perm

theorem socle_elementary_abelian_or_simple_of_odd_stabilizer {Ω : Type*} [Finite Ω]
    (N : Subgroup (Equiv.Perm Ω))
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    {n : ℕ} (hn : 1 ≤ n) (hΩ : Nat.card Ω = 2 ^ n) (α : Ω)
    (hodd : Odd (Nat.card ↥(N ⊓ MulAction.stabilizer (Equiv.Perm Ω) α))) :
    (∃ A : Subgroup (Equiv.Perm Ω), A ≤ N ∧ (A.subgroupOf N).Normal ∧
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = 2 ^ n ∧
        ∀ β γ : Ω, ∃! a : A, (a : Equiv.Perm Ω) β = γ) ∨
    ∃ S : Subgroup (Equiv.Perm Ω), S ≤ N ∧ (S.subgroupOf N).Normal ∧ IsSimpleGroup S ∧
      (∃ a b : S, a * b ≠ b * a) ∧ (∀ β γ : Ω, ∃ s ∈ S, s β = γ) ∧
      Nat.card S = 2 ^ n * Nat.card ↥(S ⊓ MulAction.stabilizer (Equiv.Perm Ω) α) ∧
      Odd (Nat.card ↥(S ⊓ MulAction.stabilizer (Equiv.Perm Ω) α)) := by
  have hN1 : N ≠ ⊥ := by
    have hcard : 1 < Nat.card Ω := by
      rw [hΩ]
      exact Nat.one_lt_two_pow (by omega)
    obtain ⟨a, b, hab⟩ := (Finite.one_lt_card_iff_nontrivial.1 hcard).exists_pair_ne
    obtain ⟨x, hx, hxa, -⟩ := h2 a b b a hab hab.symm
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, Perm.one_apply] at hxa
    exact hab hxa
  have : Finite (Subgroup (Perm Ω)) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨M, -, ⟨hM1, hMN, hMn⟩, hMmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun M' : Subgroup (Perm Ω) => M' ≠ ⊥ ∧ M' ≤ N ∧ (M'.subgroupOf N).Normal) N
    ⟨hN1, le_rfl, (Subgroup.normal_subgroupOf_iff le_rfl).2 fun h k hh hk =>
      N.mul_mem (N.mul_mem hk hh) (N.inv_mem hk)⟩
  rcases minimal_normal_regular_or_simple h2 hΩ α hodd hM1 hMN hMn
      (fun M' h1 h2 h3 => le_antisymm h2 (hMmin ⟨h1, h2.trans hMN, h3⟩ h2)) with h | h
  · exact Or.inl ⟨M, hMN, hMn, h⟩
  · exact Or.inr ⟨M, hMN, hMn, h⟩

end CFSG.SeitzReduction.RankOne
