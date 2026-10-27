module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsAll
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding Equiv

namespace AltSurvivor

section Points

variable {Ω : Type*}

theorem exists_notMem_of_card_le {O S : Finset Ω} {k : ℕ} (hS : S.card ≤ k) (hk : k < O.card) :
    ∃ d ∈ O, d ∉ S :=
  Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hS hk)

theorem inv_iff {O O' : Finset Ω} {s : Perm Ω} (hs : ∀ x, x ∈ O ↔ s x ∈ O') :
    ∀ x, x ∈ O' ↔ s⁻¹ x ∈ O := by
  intro x
  rw [hs]
  simp

theorem apply_ne_of_commute {c v : Perm Ω} (h : v * c = c * v) {x : Ω} (hx : c x ≠ x) :
    c (v x) ≠ v x := by
  have h1 : c (v x) = v (c x) := by
    have := congrArg (fun f : Perm Ω => f x) h
    simpa using this.symm
  rw [h1]
  exact fun h2 => hx (v.injective h2)

theorem apply_mem_iff_of_commute {b g : Perm Ω} {O : Finset Ω} (hs : ∀ x, b x ≠ x ↔ x ∈ O)
    (h : g * b = b * g) (x : Ω) : g x ∈ O ↔ x ∈ O := by
  rw [← hs, ← hs]
  have h1 : b (g x) = g (b x) := by
    have := congrArg (fun f : Perm Ω => f x) h
    simpa using this.symm
  rw [h1]
  exact ⟨fun h2 h3 => h2 (by rw [h3]), fun h2 h3 => h2 (g.injective h3)⟩

end Points

section Swaps

variable {Ω : Type*} [DecidableEq Ω]

theorem swap_mul_swap_apply_left {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) :
    (swap a b * swap b c) a = b := by
  simp [swap_apply_of_ne_of_ne hab hac]

theorem swap_mul_swap_apply_of_ne {a b c z : Ω} (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    (swap a b * swap b c) z = z := by
  simp [swap_apply_of_ne_of_ne hzb hzc, swap_apply_of_ne_of_ne hza hzb]

theorem eq_or_eq_or_eq_of_swap_mul_swap_ne {a b c w : Ω}
    (h : (swap a b * swap b c) w ≠ w) : w = a ∨ w = b ∨ w = c := by
  by_contra hcon
  push Not at hcon
  exact h (swap_mul_swap_apply_of_ne hcon.1 hcon.2.1 hcon.2.2)

theorem mem_of_apply_mem_of_forall_mem {O₁ O : Finset Ω} {y : Perm Ω}
    (h : ∀ x ∈ O₁, y x ∈ O) (hc : O.card ≤ O₁.card) {x : Ω} (hx : y x ∈ O) : x ∈ O₁ := by
  have hsub : O₁.image y ⊆ O := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact h w hw
  have hcard : O.card ≤ (O₁.image y).card := by
    rw [Finset.card_image_of_injective _ y.injective]
    exact hc
  have heq : O₁.image y = O := Finset.eq_of_subset_of_card_le hsub hcard
  have : y x ∈ O₁.image y := heq ▸ hx
  obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp this
  exact y.injective hwx ▸ hw

theorem iff_of_forall_mem_or {O₁ O₂ : Finset Ω} (hc : O₁.card = O₂.card) {y : Perm Ω}
    (h : (∀ x ∈ O₁, y x ∈ O₁) ∨ (∀ x ∈ O₁, y x ∈ O₂)) :
    (∀ x, x ∈ O₁ ↔ y x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ y x ∈ O₂) := by
  rcases h with h | h
  · exact Or.inl fun x => ⟨h x, mem_of_apply_mem_of_forall_mem h le_rfl⟩
  · exact Or.inr fun x => ⟨h x, mem_of_apply_mem_of_forall_mem h hc.ge⟩

end Swaps

section AltOn

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def altOn (O : Finset Ω) : Subgroup (Perm Ω) :=
  (alternatingGroup O).map (Perm.ofSubtype : Perm O →* Perm Ω)

theorem mem_altOn {O : Finset Ω} {g : Perm Ω} :
    g ∈ altOn O ↔ Perm.sign g = 1 ∧ ∀ x, x ∉ O → g x = x := by
  rw [altOn, alternatingGroup.map_ofSubtype, Subgroup.mem_inf, Perm.mem_range_ofSubtype_iff,
    Perm.mem_alternatingGroup, and_comm]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    by_contra hne
    exact hx (h (Perm.mem_support.mpr hne))
  · intro h x hx
    by_contra hxO
    exact (Perm.mem_support.mp hx) (h x hxO)

theorem swap_mul_swap_mem_altOn {O : Finset Ω} {a b c : Ω} (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hab : a ≠ b) (hbc : b ≠ c) : swap a b * swap b c ∈ altOn O := by
  rw [mem_altOn]
  refine ⟨by simp [Perm.sign_swap hab, Perm.sign_swap hbc], fun x hx => ?_⟩
  have hxa : x ≠ a := fun h => hx (h ▸ ha)
  have hxb : x ≠ b := fun h => hx (h ▸ hb)
  have hxc : x ≠ c := fun h => hx (h ▸ hc)
  simp [swap_apply_of_ne_of_ne hxb hxc, swap_apply_of_ne_of_ne hxa hxb]

theorem conj_mem_altOn {O O' : Finset Ω} {s g : Perm Ω} (hs : ∀ x, x ∈ O ↔ s x ∈ O')
    (hg : g ∈ altOn O) : s * g * s⁻¹ ∈ altOn O' := by
  rw [mem_altOn] at hg ⊢
  refine ⟨by simp [hg.1], fun x hx => ?_⟩
  have h1 : s⁻¹ x ∉ O := by
    rw [hs]
    simpa using hx
  rw [Perm.mul_apply, Perm.mul_apply, hg.2 _ h1]
  simp

theorem mem_iff_apply_mem_of_mem_altOn {O : Finset Ω} {g : Perm Ω} (hg : g ∈ altOn O) (x : Ω) :
    x ∈ O ↔ g x ∈ O := by
  rw [mem_altOn] at hg
  by_cases hx : x ∈ O
  · simp only [hx, true_iff]
    by_contra hgx
    have h2 : g x = x := g.injective (hg.2 _ hgx)
    exact hgx (by rw [h2]; exact hx)
  · simp [hx, hg.2 x hx]

theorem eq_self_of_commute_altOn {O : Finset Ω} (hO : 5 ≤ O.card) {v : Perm Ω}
    (hv : ∀ l ∈ altOn O, v * l = l * v) {x : Ω} (hx : x ∈ O) : v x = x := by
  obtain ⟨y, hyO, hy⟩ :=
    exists_notMem_of_card_le (O := O) (S := {x}) (k := 1) (by simp) (by omega)
  obtain ⟨z, hzO, hz⟩ := exists_notMem_of_card_le (O := O) (S := {x, y}) (k := 2)
    Finset.card_le_two (by omega)
  obtain ⟨y', hy'O, hy'⟩ := exists_notMem_of_card_le (O := O) (S := {x, y, z}) (k := 3)
    Finset.card_le_three (by omega)
  obtain ⟨z', hz'O, hz'⟩ := exists_notMem_of_card_le (O := O) (S := {x, y, z, y'}) (k := 4)
    Finset.card_le_four (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy hz hy' hz'
  have h1 : swap x y * swap y z ∈ altOn O :=
    swap_mul_swap_mem_altOn hx hyO hzO (Ne.symm hy) (Ne.symm hz.2)
  have h2 : swap x y' * swap y' z' ∈ altOn O :=
    swap_mul_swap_mem_altOn hx hy'O hz'O (Ne.symm hy'.1) (Ne.symm hz'.2.2.2)
  have m1 := apply_ne_of_commute (hv _ h1) (x := x) (by
    rw [swap_mul_swap_apply_left (Ne.symm hy) (Ne.symm hz.1)]
    exact hy)
  have m2 := apply_ne_of_commute (hv _ h2) (x := x) (by
    rw [swap_mul_swap_apply_left (Ne.symm hy'.1) (Ne.symm hz'.1)]
    exact hy'.1)
  have e1 := eq_or_eq_or_eq_of_swap_mul_swap_ne m1
  have e2 := eq_or_eq_or_eq_of_swap_mul_swap_ne m2
  rcases e1 with e1 | e1 | e1
  · exact e1
  · exfalso
    rcases e2 with e2 | e2 | e2
    · exact hy (e1.symm.trans e2)
    · exact hy'.2.1 (e2.symm.trans e1)
    · exact hz'.2.1 (e2.symm.trans e1)
  · exfalso
    rcases e2 with e2 | e2 | e2
    · exact hz.1 (e1.symm.trans e2)
    · exact hy'.2.2 (e2.symm.trans e1)
    · exact hz'.2.2.1 (e2.symm.trans e1)

omit [Fintype Ω] in
theorem inf_altOn_eq_bot_or_le {O : Finset Ω} (hO : 5 ≤ O.card) {V : Subgroup (Perm Ω)}
    (hV : ∀ l ∈ altOn O, ∀ v ∈ V, l * v * l⁻¹ ∈ V) : V ⊓ altOn O = ⊥ ∨ altOn O ≤ V := by
  have hsimple : IsSimpleGroup (alternatingGroup O) :=
    alternatingGroup.isSimpleGroup (by simpa using hO)
  let f : alternatingGroup O →* Perm Ω :=
    (Perm.ofSubtype : Perm O →* Perm Ω).comp (alternatingGroup O).subtype
  have hmemf : ∀ s : alternatingGroup O, f s ∈ altOn O := fun s =>
    Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩
  have hnormal : (V.comap f).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact hV _ (hmemf g) _ hn⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal (V.comap f) with h | h
  · left
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxA⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hxA
    have hmem : (⟨s, hs⟩ : alternatingGroup O) ∈ V.comap f := hxV
    rw [h, Subgroup.mem_bot] at hmem
    have : s = 1 := congrArg Subtype.val hmem
    rw [this, map_one]
    exact Subgroup.one_mem _
  · right
    intro x hxA
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hxA
    have hmem : (⟨s, hs⟩ : alternatingGroup O) ∈ V.comap f := h ▸ Subgroup.mem_top _
    exact hmem

end AltOn

section Cycles

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem isCycle_of_pow_eq_one {b : Perm Ω} {O : Finset Ω} {p : ℕ} (hp : p.Prime) (hb : b ^ p = 1)
    (hs : ∀ x, b x ≠ x ↔ x ∈ O) (hO : O.card = p) : b.IsCycle := by
  have : Fact p.Prime := ⟨hp⟩
  have hsupp : b.support = O := by
    ext x
    rw [Perm.mem_support, hs]
  have hne : b ≠ 1 := by
    obtain ⟨x, hx⟩ : O.Nonempty := Finset.card_pos.mp (hO ▸ hp.pos)
    intro h
    exact (hs x).mpr hx (by rw [h]; rfl)
  have hord : orderOf b = p := orderOf_eq_prime hb hne
  refine Perm.isCycle_of_prime_order (by rw [hord]; exact hp) ?_
  rw [hord, hsupp, hO]
  have := hp.pos
  omega

omit [Fintype Ω] in
theorem exists_zpow_mul_zpow_eq {b₁ b₂ g : Perm Ω} {O₁ O₂ : Finset Ω} (hb₁ : b₁.IsCycle)
    (hb₂ : b₂.IsCycle) (hs₁ : ∀ x, b₁ x ≠ x ↔ x ∈ O₁) (hs₂ : ∀ x, b₂ x ≠ x ↔ x ∈ O₂)
    (hd : Disjoint O₁ O₂) (hcov : ∀ x, x ∈ O₁ ∨ x ∈ O₂) (hg₁ : g * b₁ = b₁ * g)
    (hg₂ : g * b₂ = b₂ * g) : ∃ i j : ℤ, g = b₁ ^ i * b₂ ^ j := by
  have hb₁₂ : Commute b₁ b₂ := by
    refine Perm.Disjoint.commute fun x => ?_
    by_cases hx : x ∈ O₁
    · right
      by_contra hne
      exact Finset.disjoint_left.mp hd hx ((hs₂ x).mp hne)
    · left
      by_contra hne
      exact hx ((hs₁ x).mp hne)
  obtain ⟨x₁, hx₁, hcyc₁⟩ := hb₁
  obtain ⟨x₂, hx₂, hcyc₂⟩ := hb₂
  have hgx₁ : b₁ (g x₁) ≠ g x₁ :=
    (hs₁ _).mpr ((apply_mem_iff_of_commute hs₁ hg₁ x₁).mpr ((hs₁ _).mp hx₁))
  obtain ⟨i, hi⟩ := hcyc₁ hgx₁
  have hb₁i : Commute (b₁ ^ (-i)) b₁ := (Commute.refl b₁).zpow_left _
  have hb₁i₂ : Commute (b₁ ^ (-i)) b₂ := hb₁₂.zpow_left _
  have hc₁ : (b₁ ^ (-i) * g) * b₁ = b₁ * (b₁ ^ (-i) * g) := Commute.mul_left hb₁i hg₁
  have hc₂ : (b₁ ^ (-i) * g) * b₂ = b₂ * (b₁ ^ (-i) * g) := Commute.mul_left hb₁i₂ hg₂
  have hfix₁ : (b₁ ^ (-i) * g) x₁ = x₁ := by
    rw [Perm.mul_apply, ← hi, ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
      Perm.one_apply]
  have hall₁ : ∀ y, y ∈ O₁ → (b₁ ^ (-i) * g) y = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := hcyc₁ ((hs₁ y).mpr hy)
    have hk : Commute (b₁ ^ (-i) * g) (b₁ ^ k) := Commute.zpow_right (hc₁ : Commute _ _) k
    have key : (b₁ ^ (-i) * g) ((b₁ ^ k) x₁) = (b₁ ^ k) ((b₁ ^ (-i) * g) x₁) :=
      congrArg (fun f : Perm Ω => f x₁) hk.eq
    rw [key, hfix₁]
  set g₁ : Perm Ω := b₁ ^ (-i) * g with hg₁def
  have hg₁x₂ : b₂ (g₁ x₂) ≠ g₁ x₂ :=
    (hs₂ _).mpr ((apply_mem_iff_of_commute hs₂ hc₂ x₂).mpr ((hs₂ _).mp hx₂))
  obtain ⟨j, hj⟩ := hcyc₂ hg₁x₂
  have hb₂j : Commute (b₂ ^ (-j)) b₂ := (Commute.refl b₂).zpow_left _
  have hc₂' : (b₂ ^ (-j) * g₁) * b₂ = b₂ * (b₂ ^ (-j) * g₁) := Commute.mul_left hb₂j hc₂
  have hfix₂ : (b₂ ^ (-j) * g₁) x₂ = x₂ := by
    rw [Perm.mul_apply, ← hj, ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
      Perm.one_apply]
  have hall₂ : ∀ y, y ∈ O₂ → (b₂ ^ (-j) * g₁) y = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := hcyc₂ ((hs₂ y).mpr hy)
    have hk : Commute (b₂ ^ (-j) * g₁) (b₂ ^ k) := Commute.zpow_right (hc₂' : Commute _ _) k
    have key : (b₂ ^ (-j) * g₁) ((b₂ ^ k) x₂) = (b₂ ^ k) ((b₂ ^ (-j) * g₁) x₂) :=
      congrArg (fun f : Perm Ω => f x₂) hk.eq
    rw [key, hfix₂]
  have hone : b₂ ^ (-j) * g₁ = 1 := by
    ext y
    rcases hcov y with hy | hy
    · have hy2 : b₂ y = y := by
        by_contra hne
        exact Finset.disjoint_left.mp hd hy ((hs₂ y).mp hne)
      rw [Perm.mul_apply, hall₁ y hy, Perm.zpow_apply_eq_self_of_apply_eq_self hy2,
        Perm.one_apply]
    · rw [hall₂ y hy, Perm.one_apply]
  refine ⟨i, j, ?_⟩
  calc g = b₁ ^ i * (b₂ ^ j * (b₂ ^ (-j) * (b₁ ^ (-i) * g))) := by group
    _ = b₁ ^ i * b₂ ^ j := by rw [← hg₁def, hone, mul_one]

end Cycles

section Partition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_bot_or_altOn_le {O₁ O₂ : Finset Ω} (hd : Disjoint O₁ O₂)
    (hcov : ∀ x, x ∈ O₁ ∨ x ∈ O₂) (h₁ : 5 ≤ O₁.card) (h₂ : 5 ≤ O₂.card)
    {Y V : Subgroup (Perm Ω)} (hY₁ : altOn O₁ ≤ Y) (hY₂ : altOn O₂ ≤ Y)
    (hpres : ∀ y ∈ Y, (∀ x, x ∈ O₁ ↔ y x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ y x ∈ O₂)) {s : Perm Ω}
    (hsY : s ∈ Y) (hs : ∀ x, x ∈ O₁ ↔ s x ∈ O₂) (hVY : V ≤ Y)
    (hVn : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V) : V = ⊥ ∨ (altOn O₁ ≤ V ∧ altOn O₂ ≤ V) := by
  have hs1 := inf_altOn_eq_bot_or_le h₁ (fun l hl v hv => hVn l (hY₁ hl) v hv)
  have hs2 := inf_altOn_eq_bot_or_le h₂ (fun l hl v hv => hVn l (hY₂ hl) v hv)
  have h12 : altOn O₁ ≤ V → altOn O₂ ≤ V := by
    intro h g hg
    have h1 : s⁻¹ * g * s ∈ altOn O₁ := by
      simpa using conj_mem_altOn (inv_iff hs) hg
    have h2 := hVn s hsY _ (h h1)
    rwa [show s * (s⁻¹ * g * s) * s⁻¹ = g by group] at h2
  have h21 : altOn O₂ ≤ V → altOn O₁ ≤ V := by
    intro h g hg
    have h1 : s * g * s⁻¹ ∈ altOn O₂ := conj_mem_altOn hs hg
    have h2 := hVn s⁻¹ (Y.inv_mem hsY) _ (h h1)
    rwa [show s⁻¹ * (s * g * s⁻¹) * s⁻¹⁻¹ = g by group] at h2
  by_cases hA : altOn O₁ ≤ V
  · exact Or.inr ⟨hA, h12 hA⟩
  by_cases hB : altOn O₂ ≤ V
  · exact Or.inr ⟨h21 hB, hB⟩
  left
  have hV1 : V ⊓ altOn O₁ = ⊥ := hs1.resolve_right hA
  have hV2 : V ⊓ altOn O₂ = ⊥ := hs2.resolve_right hB
  have hcommV : ∀ v ∈ V, ∀ {O : Finset Ω}, altOn O ≤ Y → ∀ l ∈ altOn O,
      v * l * v⁻¹ * l⁻¹ ∈ V := by
    intro v hv O hO l hl
    have := V.mul_mem hv (hVn l (hO hl) v⁻¹ (V.inv_mem hv))
    simpa [mul_assoc] using this
  have hcomm : ∀ v ∈ V, ∀ {O : Finset Ω}, altOn O ≤ Y → V ⊓ altOn O = ⊥ →
      (∀ x, x ∈ O ↔ v x ∈ O) → ∀ l ∈ altOn O, v * l = l * v := by
    intro v hv O hO hVO hvO l hl
    have hu : v * l * v⁻¹ * l⁻¹ ∈ V ⊓ altOn O :=
      ⟨hcommV v hv hO l hl, (altOn O).mul_mem (conj_mem_altOn hvO hl) ((altOn O).inv_mem hl)⟩
    rw [hVO, Subgroup.mem_bot] at hu
    calc v * l = (v * l * v⁻¹ * l⁻¹) * (l * v) := by group
      _ = l * v := by rw [hu, one_mul]
  have stepA : ∀ v ∈ V, (∀ x, x ∈ O₁ ↔ v x ∈ O₁) → v = 1 := by
    intro v hv hv1
    have hv2 : ∀ x, x ∈ O₂ ↔ v x ∈ O₂ := by
      intro x
      have hn : ∀ y, y ∈ O₂ ↔ y ∉ O₁ := fun y =>
        ⟨fun h h' => Finset.disjoint_left.mp hd h' h, fun h => (hcov y).resolve_left h⟩
      rw [hn, hn, hv1]
    ext x
    rcases hcov x with hx | hx
    · exact eq_self_of_commute_altOn h₁ (hcomm v hv hY₁ hV1 hv1) hx
    · exact eq_self_of_commute_altOn h₂ (hcomm v hv hY₂ hV2 hv2) hx
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  rcases hpres v (hVY hv) with hv1 | hv1
  · exact stepA v hv hv1
  · exfalso
    obtain ⟨a, haO, ha⟩ := exists_notMem_of_card_le (O := O₁) (S := ∅) (k := 0) (by simp)
      (by omega)
    obtain ⟨b, hbO, hb⟩ := exists_notMem_of_card_le (O := O₁) (S := {a}) (k := 1) (by simp)
      (by omega)
    obtain ⟨c, hcO, hc⟩ := exists_notMem_of_card_le (O := O₁) (S := {a, b}) (k := 2)
      Finset.card_le_two (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hc
    set l : Perm Ω := swap a b * swap b c with hl
    have hlO : l ∈ altOn O₁ := swap_mul_swap_mem_altOn haO hbO hcO (Ne.symm hb) (Ne.symm hc.2)
    have hla : l a = b := swap_mul_swap_apply_left (Ne.symm hb) (Ne.symm hc.1)
    have hu : v * l * v⁻¹ * l⁻¹ ∈ V := hcommV v hv hY₁ l hlO
    have hvl : v * l * v⁻¹ ∈ altOn O₂ := conj_mem_altOn hv1 hlO
    have hl' : l⁻¹ ∈ altOn O₁ := (altOn O₁).inv_mem hlO
    have hu1 : ∀ x, x ∈ O₁ ↔ (v * l * v⁻¹ * l⁻¹) x ∈ O₁ := by
      intro x
      rw [Perm.mul_apply]
      by_cases hx : x ∈ O₁
      · have hy : l⁻¹ x ∈ O₁ := (mem_iff_apply_mem_of_mem_altOn hl' x).mp hx
        have hy2 : l⁻¹ x ∉ O₂ := fun h => Finset.disjoint_left.mp hd hy h
        rw [((mem_altOn.mp hvl).2 _ hy2)]
        simp only [hx, hy]
      · have hy : l⁻¹ x = x := (mem_altOn.mp hl').2 x hx
        have hx2 : x ∈ O₂ := (hcov x).resolve_left hx
        rw [hy]
        have := (mem_iff_apply_mem_of_mem_altOn hvl x)
        simp only [hx, false_iff]
        intro hmem
        exact Finset.disjoint_left.mp hd hmem (this.mp hx2)
    have h1 := stepA _ hu hu1
    have hxa : (v * l * v⁻¹ * l⁻¹) a = a := by rw [h1]; rfl
    have hy : l⁻¹ a ∈ O₁ := (mem_iff_apply_mem_of_mem_altOn hl' a).mp haO
    have hy2 : l⁻¹ a ∉ O₂ := fun h => Finset.disjoint_left.mp hd hy h
    rw [Perm.mul_apply, (mem_altOn.mp hvl).2 _ hy2] at hxa
    have h3 : a = l a := Perm.inv_eq_iff_eq.mp hxa
    rw [hla] at h3
    exact hb h3.symm

end Partition

section Jordan

open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem alternatingGroup_le_of_cross {O₁ O₂ : Finset Ω} (hd : Disjoint O₁ O₂)
    (hcov : ∀ x, x ∈ O₁ ∨ x ∈ O₂) (h₁ : 4 ≤ O₁.card) (h₂ : 4 ≤ O₂.card)
    {Y : Subgroup (Perm Ω)} (hY₁ : altOn O₁ ≤ Y) (hY₂ : altOn O₂ ≤ Y) {y : Perm Ω} (hy : y ∈ Y)
    {w : Ω} (hw : w ∈ O₁) (hyw : y w ∈ O₂) {u : Ω} (hu : u ∈ O₁) (hyu : y u ∈ O₁) :
    alternatingGroup Ω ≤ Y := by
  have h3 : ∀ {O : Finset Ω}, altOn O ≤ Y → ∀ {a b c : Ω}, a ∈ O → b ∈ O → c ∈ O → a ≠ b →
      b ≠ c → swap a b * swap b c ∈ Y := fun hO _ _ _ ha hb hc hab hbc =>
    hO (swap_mul_swap_mem_altOn ha hb hc hab hbc)
  have horb : ∀ a, ∃ g ∈ Y, g w = a := by
    intro a
    rcases hcov a with ha | ha
    · by_cases haw : a = w
      · exact ⟨1, Y.one_mem, by simp [haw]⟩
      · obtain ⟨d, hdO, hd'⟩ := exists_notMem_of_card_le (O := O₁) (S := {w, a}) (k := 2)
          Finset.card_le_two (by omega)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
        exact ⟨swap w a * swap a d, h3 hY₁ hw ha hdO (Ne.symm haw) (Ne.symm hd'.2),
          swap_mul_swap_apply_left (Ne.symm haw) (Ne.symm hd'.1)⟩
    · by_cases hay : a = y w
      · exact ⟨y, hy, hay.symm⟩
      · obtain ⟨d, hdO, hd'⟩ := exists_notMem_of_card_le (O := O₂) (S := {y w, a}) (k := 2)
          Finset.card_le_two (by omega)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
        refine ⟨(swap (y w) a * swap a d) * y, Y.mul_mem
          (h3 hY₂ hyw ha hdO (Ne.symm hay) (Ne.symm hd'.2)) hy, ?_⟩
        rw [Perm.mul_apply]
        exact swap_mul_swap_apply_left (Ne.symm hay) (Ne.symm hd'.1)
  have hpre : MulAction.IsPretransitive Y Ω := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hg, hga⟩ := horb a
    obtain ⟨g', hg', hgb⟩ := horb b
    refine ⟨⟨g' * g⁻¹, Y.mul_mem hg' (Y.inv_mem hg)⟩, ?_⟩
    show g' (g⁻¹ a) = b
    rw [← hga]
    simpa using hgb
  have hprim : MulAction.IsPreprimitive Y Ω := by
    refine MulAction.IsPreprimitive.of_isTrivialBlock_base (G := Y) u ?_
    intro B huB hB
    have hkey : ∀ g ∈ Y, ∀ a ∈ B, g a ∈ B → ∀ z ∈ B, g z ∈ B := by
      intro g hg a ha hga z hz
      have h1 : (⟨g, hg⟩ : Y) • B = B := hB.smul_eq_of_mem ha hga
      have h2 : (⟨g, hg⟩ : Y) • z ∈ (⟨g, hg⟩ : Y) • B := Set.smul_mem_smul_set hz
      rw [h1] at h2
      exact h2
    by_cases hB2 : ∃ z ∈ B, z ∈ O₂
    · right
      obtain ⟨z, hzB, hzO⟩ := hB2
      have hzO₁ : z ∉ O₁ := fun h => Finset.disjoint_left.mp hd h hzO
      refine Set.eq_univ_of_forall fun a => ?_
      rcases hcov a with ha | ha
      · by_cases hau : a = u
        · rw [hau]
          exact huB
        · obtain ⟨d, hdO, hd'⟩ := exists_notMem_of_card_le (O := O₁) (S := {u, a}) (k := 2)
            Finset.card_le_two (by omega)
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
          have hmem := h3 hY₁ hu ha hdO (Ne.symm hau) (Ne.symm hd'.2)
          have hfz : (swap u a * swap a d) z = z := swap_mul_swap_apply_of_ne
            (fun h => hzO₁ (h ▸ hu)) (fun h => hzO₁ (h ▸ ha)) (fun h => hzO₁ (h ▸ hdO))
          have := hkey _ hmem z hzB (by rw [hfz]; exact hzB) u huB
          rwa [swap_mul_swap_apply_left (Ne.symm hau) (Ne.symm hd'.1)] at this
      · by_cases haz : a = z
        · rw [haz]
          exact hzB
        · obtain ⟨d, hdO, hd'⟩ := exists_notMem_of_card_le (O := O₂) (S := {z, a}) (k := 2)
            Finset.card_le_two (by omega)
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
          have hmem := h3 hY₂ hzO ha hdO (Ne.symm haz) (Ne.symm hd'.2)
          have huO₂ : u ∉ O₂ := fun h => Finset.disjoint_left.mp hd hu h
          have hfu : (swap z a * swap a d) u = u := swap_mul_swap_apply_of_ne
            (fun h => huO₂ (h ▸ hzO)) (fun h => huO₂ (h ▸ ha)) (fun h => huO₂ (h ▸ hdO))
          have := hkey _ hmem u huB (by rw [hfu]; exact huB) z hzB
          rwa [swap_mul_swap_apply_left (Ne.symm haz) (Ne.symm hd'.1)] at this
    · left
      push Not at hB2
      by_cases hsub : B.Subsingleton
      · exact hsub
      · exfalso
        obtain ⟨x, hxB, hxu⟩ : ∃ x ∈ B, x ≠ u := by
          by_contra hcon
          push Not at hcon
          exact hsub fun a ha b hb => (hcon a ha).trans (hcon b hb).symm
        have hxO : x ∈ O₁ := (hcov x).resolve_right (hB2 x hxB)
        have hO₁B : ∀ c ∈ O₁, c ∈ B := by
          intro c hc
          by_cases hcx : c = x
          · rw [hcx]
            exact hxB
          · by_cases hcu : c = u
            · rw [hcu]
              exact huB
            · obtain ⟨d, hdO, hd'⟩ := exists_notMem_of_card_le (O := O₁) (S := {u, x, c})
                (k := 3) Finset.card_le_three (by omega)
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
              have hmem := h3 hY₁ hxO hc hdO (Ne.symm hcx) (Ne.symm hd'.2.2)
              have hfu : (swap x c * swap c d) u = u := swap_mul_swap_apply_of_ne
                (Ne.symm hxu) (Ne.symm hcu) (Ne.symm hd'.1)
              have := hkey _ hmem u huB (by rw [hfu]; exact huB) x hxB
              rwa [swap_mul_swap_apply_left (Ne.symm hcx) (Ne.symm hd'.2.1)] at this
        have hyuB : y u ∈ B := hO₁B _ hyu
        have hywB : y w ∈ B := hkey y hy u huB hyuB w (hO₁B w hw)
        exact Finset.disjoint_right.mp hd hyw ((hcov _).resolve_right (hB2 _ hywB))
  obtain ⟨b, hbO, hb⟩ := exists_notMem_of_card_le (O := O₁) (S := {u}) (k := 1) (by simp)
    (by omega)
  obtain ⟨c, hcO, hc⟩ := exists_notMem_of_card_le (O := O₁) (S := {u, b}) (k := 2)
    Finset.card_le_two (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hc
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (AltGen.isThreeCycle_swap_mul_swap (Ne.symm hb) (Ne.symm hc.1) (Ne.symm hc.2))
    (h3 hY₁ hu hbO hcO (Ne.symm hb) (Ne.symm hc.2))

end Jordan

theorem exists_injective_hom_perm {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {n : ℕ} (hn : 7 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) :
    ∃ ι : X →* Perm (Fin n), Function.Injective ι ∧
      ∀ k : K, ι (k : X) = ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  classical
  let c : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal
  have hcinj : Function.Injective c :=
    GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  have hcsurj : Function.Surjective c :=
    ComponentClassification.CatalogueSchreierAlternating.conjugation_surjective (Or.inr hn)
  let cE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective c ⟨hcinj, hcsurj⟩
  let φ : X →* MulAut K := MulAut.conjNormal
  let ψ : MulAut K ≃* MulAut (alternatingGroup (Fin n)) := MulAut.congr e
  refine ⟨cE.symm.toMonoidHom.comp (ψ.toMonoidHom.comp φ), ?_, ?_⟩
  · refine cE.symm.injective.comp (ψ.injective.comp ?_)
    refine (MonoidHom.ker_eq_bot_iff φ).mp ?_
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [← Subgroup.mem_bot, ← hC, Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) ⟨k, hk⟩)
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * x = (x * k * x⁻¹) * x := by rw [h1]
      _ = x * k := by group
  · intro k
    have hφ : φ (k : X) = MulAut.conj k := MulAut.conjNormal_val
    have hc : c ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) = MulAut.conj (e k) :=
      MulAut.conjNormal_val
    have hψ : ψ (MulAut.conj k) = MulAut.conj (e k) := by
      apply MulEquiv.ext
      intro y
      simp [ψ, MulAut.congr]
    show cE.symm (ψ (φ (k : X))) = _
    rw [MulEquiv.symm_apply_eq, hφ, hψ]
    exact hc.symm

theorem not_pow_three_dvd_card_alternatingGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 3 ∣ Nat.card (alternatingGroup (Fin (2 * p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have : Nontrivial (Fin (2 * p)) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩⟩
  have h2 : 2 * Nat.card (alternatingGroup (Fin (2 * p))) = (2 * p).factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hval : padicValNat p (2 * p).factorial = 2 := by
    rw [mul_comm 2 p, padicValNat_factorial_mul]
    have : padicValNat p (Nat.factorial 2) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      rw [Nat.factorial_two] at h
      have := Nat.le_of_dvd (by decide) h
      omega
    omega
  intro hdvd
  have hne : (2 * p).factorial ≠ 0 := Nat.factorial_ne_zero _
  have : p ^ 3 ∣ (2 * p).factorial := h2 ▸ Dvd.dvd.mul_left hdvd 2
  rw [padicValNat_dvd_iff_le hne, hval] at this
  omega

end AltSurvivor

open AltSurvivor

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem D2AlmostSimple.sylow_eq_of_alternating (h : D2AlmostSimple p X R A X₀ K) (hp5 : 5 ≤ p)
    (e : K ≃* alternatingGroup (Fin (2 * p))) : (R : Subgroup X) = A := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hRK : (R : Subgroup X) ≤ K := h.sylow_le_of_alternating (by omega) e
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp R.isPGroup'
  have hk3 : k ≤ 2 := by
    by_contra hk2
    push Not at hk2
    apply not_pow_three_dvd_card_alternatingGroup hp h.ne_two
    have h1 : p ^ 3 ∣ Nat.card (R : Subgroup X) := by
      rw [hk]
      exact pow_dvd_pow p hk2
    have h2 : Nat.card (R : Subgroup X) ∣ Nat.card K := Subgroup.card_dvd_of_le hRK
    rw [Nat.card_congr e.toEquiv] at h2
    exact h1.trans h2
  refine (Subgroup.eq_of_le_of_card_ge h.A_le ?_).symm
  rw [hk, h.card_A]
  exact Nat.pow_le_pow_right hp.pos hk3

theorem D2AlmostSimple.exists_cycle_data (h : D2AlmostSimple p X R A X₀ K) (hp5 : 5 ≤ p)
    (e : K ≃* alternatingGroup (Fin (2 * p))) :
    ∃ (ι : X →* Perm (Fin (2 * p))) (a₁ a₂ : X) (O₁ O₂ : Finset (Fin (2 * p))),
      Function.Injective ι ∧
      (∀ k : K, ι (k : X) = ((e k : alternatingGroup (Fin (2 * p))) : Perm (Fin (2 * p)))) ∧
      a₁ ∈ A ∧ a₂ ∈ A ∧ O₁.card = p ∧ O₂.card = p ∧ Disjoint O₁ O₂ ∧ (∀ x, x ∈ O₁ ∨ x ∈ O₂) ∧
      (∀ x, ι a₁ x ≠ x ↔ x ∈ O₁) ∧ (∀ x, ι a₂ x ≠ x ↔ x ∈ O₂) ∧ (ι a₁).IsCycle ∧
      (ι a₂).IsCycle := by
  have hp := h.prime
  have hp2 := h.ne_two
  have : K.Normal := h.normal
  obtain ⟨ι, hι, hιK⟩ := exists_injective_hom_perm h.centralizer_eq_bot (by omega : 7 ≤ 2 * p) e
  have hRK : (R : Subgroup X) ≤ K := h.sylow_le_of_alternating (by omega) e
  have hAK : A ≤ K := h.A_le.trans hRK
  have hĀ : IsElemAbelian p ((A.subgroupOf K).map e.toMonoidHom) :=
    elementary_abelian_map p (isElemAbelian_subgroupOf h.elem K) _
  have hĀcard : Nat.card ((A.subgroupOf K).map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, h.card_A]
  have hE : IsElemAbelian p (((A.subgroupOf K).map e.toMonoidHom).map
      (alternatingGroup (Fin (2 * p))).subtype) := elementary_abelian_map p hĀ _
  have hEcard : Nat.card (((A.subgroupOf K).map e.toMonoidHom).map
      (alternatingGroup (Fin (2 * p))).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin (2 * p))).subtype_injective, hĀcard]
  obtain ⟨b₁, hb₁E, b₂, hb₂E, O₁, O₂, hO₁, hO₂, hd, hb₁, hb₂⟩ :=
    exists_cycles_of_isElemAbelian hp hp2 (by omega) hE hEcard
  have key : ∀ b ∈ ((A.subgroupOf K).map e.toMonoidHom).map
      (alternatingGroup (Fin (2 * p))).subtype, ∃ k : K, (k : X) ∈ A ∧
        ((e k : alternatingGroup (Fin (2 * p))) : Perm (Fin (2 * p))) = b := by
    rintro b ⟨ã, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩
  obtain ⟨k₁, hk₁A, hk₁⟩ := key b₁ hb₁E
  obtain ⟨k₂, hk₂A, hk₂⟩ := key b₂ hb₂E
  have hι₁ : ι (k₁ : X) = b₁ := (hιK k₁).trans hk₁
  have hι₂ : ι (k₂ : X) = b₂ := (hιK k₂).trans hk₂
  have hb₁p : b₁ ^ p = 1 := hE.2 b₁ hb₁E
  have hb₂p : b₂ ^ p = 1 := hE.2 b₂ hb₂E
  refine ⟨ι, k₁, k₂, O₁, O₂, hι, hιK, hk₁A, hk₂A, hO₁, hO₂, hd, ?_, ?_, ?_, ?_, ?_⟩
  · have hcard : (O₁ ∪ O₂).card = Fintype.card (Fin (2 * p)) := by
      rw [Finset.card_union_of_disjoint hd, hO₁, hO₂, Fintype.card_fin]
      ring
    intro x
    have hx : x ∈ O₁ ∪ O₂ := Finset.eq_univ_of_card _ hcard ▸ Finset.mem_univ x
    exact Finset.mem_union.mp hx
  · rw [hι₁]
    exact hb₁
  · rw [hι₂]
    exact hb₂
  · rw [hι₁]
    exact isCycle_of_pow_eq_one hp hb₁p hb₁ hO₁
  · rw [hι₂]
    exact isCycle_of_pow_eq_one hp hb₂p hb₂ hO₂

theorem D2AlmostSimple.centralizer_le_of_alternating (h : D2AlmostSimple p X R A X₀ K)
    (hp5 : 5 ≤ p) (e : K ≃* alternatingGroup (Fin (2 * p))) :
    Subgroup.centralizer (A : Set X) ≤ A := by
  obtain ⟨ι, a₁, a₂, O₁, O₂, hι, -, ha₁, ha₂, -, -, hd, hcov, hs₁, hs₂, hcy₁, hcy₂⟩ :=
    h.exists_cycle_data hp5 e
  intro g hg
  have hg₁ : ι g * ι a₁ = ι a₁ * ι g := by
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hg a₁ ha₁).symm]
  have hg₂ : ι g * ι a₂ = ι a₂ * ι g := by
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hg a₂ ha₂).symm]
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_eq hcy₁ hcy₂ hs₁ hs₂ hd hcov hg₁ hg₂
  have hgij : g = a₁ ^ i * a₂ ^ j := hι (by rw [hij, map_mul, map_zpow, map_zpow])
  rw [hgij]
  exact A.mul_mem (A.zpow_mem ha₁ i) (A.zpow_mem ha₂ j)

theorem D2AlmostSimple.dichotomy_of_alternating (h : D2AlmostSimple p X R A X₀ K) (hp5 : 5 ≤ p)
    (e : K ≃* alternatingGroup (Fin (2 * p))) {W : Subgroup X} (hWX : W ≤ X₀)
    (hWn : X₀ ≤ Subgroup.normalizer (W : Set X)) : W = ⊥ ∨ A ≤ W := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : K.Normal := h.normal
  have hRA := h.sylow_eq_of_alternating hp5 e
  obtain ⟨ι, a₁, a₂, O₁, O₂, hι, hιK, ha₁, ha₂, hO₁, hO₂, hd, hcov, hs₁, hs₂, hcy₁, hcy₂⟩ :=
    h.exists_cycle_data hp5 e
  have ha₁1 : a₁ ≠ 1 := fun h1 => hcy₁.ne_one (by rw [h1, map_one])
  have ha₂1 : a₂ ≠ 1 := fun h1 => hcy₂.ne_one (by rw [h1, map_one])
  set Y : Subgroup (Perm (Fin (2 * p))) := X₀.map ι
  set V : Subgroup (Perm (Fin (2 * p))) := W.map ι
  have hN : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set X) ≤ X₀ := fun a haA ha1 g hg =>
    h.normalizer_le_of_le_A (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA)
      (by rwa [Ne, Subgroup.zpowers_eq_bot]) (centralizer_singleton_le_normalizer_zpowers _ hg)
  have hAlt : ∀ a ∈ A, a ≠ 1 → ∀ O O' : Finset (Fin (2 * p)), (∀ x, ι a x ≠ x ↔ x ∈ O') →
      Disjoint O O' → altOn O ≤ Y := by
    intro a haA ha1 O O' hsO' hdis g hg
    rw [mem_altOn] at hg
    let g' : alternatingGroup (Fin (2 * p)) := ⟨g, Perm.mem_alternatingGroup.mpr hg.1⟩
    let k : K := e.symm g'
    have hk : ι (k : X) = g := by
      rw [hιK]
      simp [k, g']
    have hcomm : (k : X) * a = a * (k : X) := by
      apply hι
      rw [map_mul, map_mul, hk]
      refine (Perm.Disjoint.commute fun x => ?_).eq
      by_cases hx : x ∈ O
      · right
        by_contra hne
        exact Finset.disjoint_left.mp hdis hx ((hsO' x).mp hne)
      · left
        exact hg.2 x hx
    exact ⟨k, hN a haA ha1 (Subgroup.mem_centralizer_singleton_iff.mpr hcomm), hk⟩
  have hY₁ : altOn O₁ ≤ Y := hAlt a₂ ha₂ ha₂1 O₁ O₂ hs₂ hd
  have hY₂ : altOn O₂ ≤ Y := hAlt a₁ ha₁ ha₁1 O₂ O₁ hs₁ hd.symm
  have hor : ∀ y ∈ Y, (∀ x ∈ O₁, y x ∈ O₁) ∨ (∀ x ∈ O₁, y x ∈ O₂) := by
    intro y hy
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨u, hu, huy⟩, ⟨w, hw, hwy⟩⟩ := hcon
    have hu' : y u ∈ O₂ := (hcov _).resolve_left huy
    have hw' : y w ∈ O₁ := (hcov _).resolve_right hwy
    have hAltY := alternatingGroup_le_of_cross hd hcov (by omega) (by omega) hY₁ hY₂ hy hu hu'
      hw hw'
    apply h.not_le
    intro k hk
    have hmem : ι k ∈ Y := hAltY (by
      rw [show ι k = ι ((⟨k, hk⟩ : K) : X) from rfl, hιK ⟨k, hk⟩]
      exact (e ⟨k, hk⟩).2)
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hmem
    exact (hι hxk) ▸ hx
  have hpres : ∀ y ∈ Y, (∀ x, x ∈ O₁ ↔ y x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ y x ∈ O₂) := fun y hy =>
    iff_of_forall_mem_or (hO₁.trans hO₂.symm) (hor y hy)
  have hswap : ∃ s ∈ Y, ∀ x, x ∈ O₁ ↔ s x ∈ O₂ := by
    obtain ⟨π, hπ, hπc⟩ : ∃ π : Perm (Fin (2 * p)), Perm.sign π = 1 ∧
        π * ι a₁ * π⁻¹ = ι a₂ := by
      have hsupp : (ι a₁).support.card = (ι a₂).support.card := by
        have e1 : (ι a₁).support = O₁ := by
          ext x
          rw [Perm.mem_support, hs₁]
        have e2 : (ι a₂).support = O₂ := by
          ext x
          rw [Perm.mem_support, hs₂]
        rw [e1, e2, hO₁, hO₂]
      obtain ⟨c, hc⟩ := isConj_iff.mp (hcy₁.isConj hcy₂ hsupp)
      rcases Int.units_eq_one_or (Perm.sign c) with hsc | hsc
      · exact ⟨c, hsc, hc⟩
      · obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ O₁, ∃ y ∈ O₁, x ≠ y :=
          Finset.one_lt_card.mp (by omega)
        have hx2 : ι a₂ x = x := by
          by_contra hne
          exact Finset.disjoint_left.mp hd hx ((hs₂ x).mp hne)
        have hy2 : ι a₂ y = y := by
          by_contra hne
          exact Finset.disjoint_left.mp hd hy ((hs₂ y).mp hne)
        have hfix : ι a₂ * swap x y = swap x y * ι a₂ := by
          rw [mul_swap_eq_swap_mul, hx2, hy2]
        refine ⟨swap x y * c, ?_, ?_⟩
        · rw [map_mul, hsc, Perm.sign_swap hxy]
          rfl
        · calc swap x y * c * ι a₁ * (swap x y * c)⁻¹
              = swap x y * (c * ι a₁ * c⁻¹) * swap x y := by
                rw [mul_inv_rev, swap_inv]
                group
            _ = ι a₂ := by
                rw [hc, ← hfix, mul_assoc, swap_mul_self, mul_one]
    let g : K := e.symm ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩
    have hg : ι (g : X) = π := by
      rw [hιK]
      simp [g]
    have hA1 : A ≠ ⊥ := fun hbot => ha₁1 (Subgroup.mem_bot.mp (hbot ▸ ha₁))
    have : IsMulCommutative (R : Subgroup X) := by
      rw [hRA]
      exact h.elem.1
    have hga : (g : X)⁻¹ * a₂ * g = a₁ := by
      apply hι
      rw [map_mul, map_mul, map_inv, hg, ← hπc]
      group
    have ha₁R : a₁ ∈ (R : Subgroup X) := by
      rw [hRA]
      exact ha₁
    have ha₂R : a₂ ∈ (R : Subgroup X) := by
      rw [hRA]
      exact ha₂
    obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem R a₂ g ha₂R
      (by rw [hga]; exact ha₁R)
    have hnX₀ : n ∈ X₀ := by
      refine h.normalizer_le_of_le_A A le_rfl hA1 ?_
      rw [← hRA]
      exact hn
    refine ⟨ι n, Subgroup.mem_map_of_mem ι hnX₀, fun x => ?_⟩
    have hcomm : ι n * ι a₁ = ι a₂ * ι n := by
      rw [← map_mul, ← map_mul]
      congr 1
      rw [← hga, hn']
      group
    have hx : ι n (ι a₁ x) = ι a₂ (ι n x) := congrArg (fun f : Perm (Fin (2 * p)) => f x) hcomm
    rw [← hs₁, ← hs₂, ← hx]
    exact ⟨fun hne h2 => hne ((ι n).injective h2), fun hne h2 => hne (by rw [h2])⟩
  obtain ⟨s, hsY, hs⟩ := hswap
  have hVY : V ≤ Y := Subgroup.map_mono hWX
  have hVn : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨w, hw, rfl⟩
    refine ⟨x * w * x⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWn hx) w).mp hw
  rcases eq_bot_or_altOn_le hd hcov (by omega) (by omega) hY₁ hY₂ hpres hsY hs hVY hVn with
    hVbot | ⟨hV₁, hV₂⟩
  · left
    rw [eq_bot_iff]
    intro w hw
    have : ι w ∈ V := Subgroup.mem_map_of_mem ι hw
    rw [hVbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (hι (by rw [this, map_one]))
  · right
    have hodd : Odd p := hp.eq_two_or_odd'.resolve_left h.ne_two
    have hmemW : ∀ a ∈ A, ∀ O : Finset (Fin (2 * p)), (∀ x, ι a x ≠ x ↔ x ∈ O) →
        altOn O ≤ V → a ∈ W := by
      intro a haA O hsO hOV
      have hbO : ι a ∈ altOn O := by
        rw [mem_altOn]
        refine ⟨AltThree.sign_eq_one_of_pow_eq_one hodd ?_, fun x hx => ?_⟩
        · rw [← map_pow, h.elem.2 a haA, map_one]
        · by_contra hne
          exact hx ((hsO x).mp hne)
      obtain ⟨w, hw, hwa⟩ := Subgroup.mem_map.mp (hOV hbO)
      exact (hι hwa) ▸ hw
    have ha₁W : a₁ ∈ W := hmemW a₁ ha₁ O₁ hs₁ hV₁
    have ha₂W : a₂ ∈ W := hmemW a₂ ha₂ O₂ hs₂ hV₂
    intro g hg
    have hAc : ∀ u v : A, u * v = v * u := isMulCommutative_iff.1 h.elem.1
    have hg₁ : ι g * ι a₁ = ι a₁ * ι g := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hAc ⟨g, hg⟩ ⟨a₁, ha₁⟩)
    have hg₂ : ι g * ι a₂ = ι a₂ * ι g := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hAc ⟨g, hg⟩ ⟨a₂, ha₂⟩)
    obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_eq hcy₁ hcy₂ hs₁ hs₂ hd hcov hg₁ hg₂
    have hgij : g = a₁ ^ i * a₂ ^ j := hι (by rw [hij, map_mul, map_zpow, map_zpow])
    rw [hgij]
    exact W.mul_mem (W.zpow_mem ha₁W i) (W.zpow_mem ha₂W j)

theorem d2AltSurvivorFacts : D2AltSurvivorFacts := by
  intro X _ _ p hp5 R A X₀ K hK he
  obtain ⟨e⟩ := he
  exact ⟨fun W hW hWn => hK.dichotomy_of_alternating hp5 e hW hWn,
    inf_le_right.trans ((hK.centralizer_le_of_alternating hp5 e).trans
      (hK.sylow_eq_of_alternating hp5 e).ge)⟩

end CFSG.AGLEmbeddingD2
