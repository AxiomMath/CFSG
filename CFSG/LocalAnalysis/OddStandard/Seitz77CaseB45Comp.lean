module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Basic

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_iff_cs {H : Subgroup G} {n : G} :
    n ∈ normalizer (H : Set G) ↔ cs n H = H := by
  constructor
  · intro hn
    ext x
    rw [mem_cs]
    have := mem_normalizer_iff.1 (inv_mem hn) x
    simpa using this.symm
  · intro h
    rw [mem_normalizer_iff]
    intro x
    have := SetLike.ext_iff.1 h (n * x * n⁻¹)
    rw [mem_cs] at this
    have e : n⁻¹ * (n * x * n⁻¹) * n = x := by group
    rw [e] at this
    exact this

theorem commutator_mul_central {H : Type*} [Group H] (n₁ n₂ z₁ z₂ : H)
    (h1 : ∀ g, z₁ * g = g * z₁) (h2 : ∀ g, z₂ * g = g * z₂) :
    n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
  have e1 : ∀ x, z₁ * x * z₁⁻¹ = x := fun x => by
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
      = n₁ * (z₁ * (n₂ * z₂) * z₁⁻¹) * n₁⁻¹ * (z₂⁻¹ * n₂⁻¹) := by group
    _ = n₁ * n₂ * (z₂ * n₁⁻¹) * (z₂⁻¹ * n₂⁻¹) := by rw [e1]; group
    _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
      rw [h2 n₁⁻¹]
      group

structure CompData (G₁ G₂ : Subgroup G) (t : G) : Prop where
  t_sq : t * t = 1
  swap : ∀ x : G, x ∈ G₂ ↔ t⁻¹ * x * t ∈ G₁
  comm : ⁅G₁, G₂⁆ = ⊥
  perfect : ⁅G₁, G₁⁆ = G₁
  simple : IsSimpleGroup (G₁ ⧸ center G₁)

namespace CompData

variable {G₁ G₂ : Subgroup G} {t : G}

theorem t_inv (c : CompData G₁ G₂ t) : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.t_sq

theorem G₂_eq (c : CompData G₁ G₂ t) : G₂ = cs t G₁ := by
  ext x
  rw [mem_cs, c.t_inv, c.swap, c.t_inv]

theorem cs_t_G₁ (c : CompData G₁ G₂ t) : cs t G₁ = G₂ := c.G₂_eq.symm

theorem cs_t_G₂ (c : CompData G₁ G₂ t) : cs t G₂ = G₁ := by
  rw [c.G₂_eq, ← cs_mul, c.t_sq, cs_one]

theorem G₁_ne_bot (c : CompData G₁ G₂ t) : G₁ ≠ ⊥ := by
  intro h
  have := c.simple
  have hn : Nontrivial (G₁ ⧸ center G₁) := IsSimpleGroup.toNontrivial
  have hs : Subsingleton (↥G₁ ⧸ center ↥G₁) := by
    have : Subsingleton ↥G₁ := by rw [h]; infer_instance
    infer_instance
  exact (not_subsingleton _) hs

theorem G₁_ne_G₂ (c : CompData G₁ G₂ t) : G₁ ≠ G₂ := by
  intro h
  apply c.G₁_ne_bot
  have := c.comm
  rw [← h] at this
  rw [← c.perfect, this]

theorem mul_comm_of_mem (c : CompData G₁ G₂ t) {x y : G} (hx : x ∈ G₁) (hy : y ∈ G₂) :
    x * y = y * x := by
  have := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 c.comm) hx
  exact (Subgroup.mem_centralizer_iff.1 this y hy).symm

theorem normalizes_G₁ (c : CompData G₁ G₂ t) {y : G} (hy : y ∈ G₂) {x : G} :
    x ∈ G₁ ↔ y * x * y⁻¹ ∈ G₁ := by
  have key : ∀ w ∈ G₁, y * w * y⁻¹ = w := fun w hw => by
    have h : y * w = w * y := (c.mul_comm_of_mem hw hy).symm
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hx
    rw [key x hx]
    exact hx
  · intro h
    have hw : y * (y * x * y⁻¹) = (y * x * y⁻¹) * y := (c.mul_comm_of_mem h hy).symm
    have : y * x * y⁻¹ = x := by
      have h2 : y * (y * x * y⁻¹) = y * x := by
        rw [hw, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
      exact mul_left_cancel (h2 : y * (y * x * y⁻¹) = y * x)
    rw [← this]
    exact h

theorem normalizes_G₂ (c : CompData G₁ G₂ t) {y : G} (hy : y ∈ G₁) {x : G} :
    x ∈ G₂ ↔ y * x * y⁻¹ ∈ G₂ := by
  have key : ∀ w ∈ G₂, y * w * y⁻¹ = w := fun w hw => by
    have h : y * w = w * y := c.mul_comm_of_mem hy hw
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hx
    rw [key x hx]
    exact hx
  · intro h
    have hw : y * (y * x * y⁻¹) = (y * x * y⁻¹) * y := c.mul_comm_of_mem hy h
    have : y * x * y⁻¹ = x := by
      have h2 : y * (y * x * y⁻¹) = y * x := by
        rw [hw, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
      exact mul_left_cancel (h2 : y * (y * x * y⁻¹) = y * x)
    rw [← this]
    exact h

theorem sup_le_normalizer₁ (c : CompData G₁ G₂ t) : G₁ ⊔ G₂ ≤ normalizer (G₁ : Set G) := by
  refine sup_le Subgroup.le_normalizer ?_
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  exact c.normalizes_G₁ hy

theorem sup_le_normalizer₂ (c : CompData G₁ G₂ t) : G₁ ⊔ G₂ ≤ normalizer (G₂ : Set G) := by
  refine sup_le ?_ Subgroup.le_normalizer
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  exact c.normalizes_G₂ hy

theorem conj_mem_G₁ (c : CompData G₁ G₂ t) {g x : G} (hg : g ∈ G₁ ⊔ G₂) (hx : x ∈ G₁) :
    g * x * g⁻¹ ∈ G₁ :=
  (mem_normalizer_iff.1 (c.sup_le_normalizer₁ hg) x).1 hx

theorem conj_mem_G₂ (c : CompData G₁ G₂ t) {g x : G} (hg : g ∈ G₁ ⊔ G₂) (hx : x ∈ G₂) :
    g * x * g⁻¹ ∈ G₂ :=
  (mem_normalizer_iff.1 (c.sup_le_normalizer₂ hg) x).1 hx

theorem t_mem_normalizer (c : CompData G₁ G₂ t) :
    t ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_cs, cs_sup, c.cs_t_G₁, c.cs_t_G₂, sup_comm]

theorem normal_dich (c : CompData G₁ G₂ t) {N : Subgroup G} (hN : N ≤ G₁)
    (hnorm : ∀ g ∈ G₁, ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    (∀ x ∈ N, ∀ y ∈ G₁, x * y = y * x) ∨ N = G₁ := by
  have := c.simple
  let N' : Subgroup ↥G₁ := N.subgroupOf G₁
  have hN' : N'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hnorm g g.2 x hx⟩
  let π : ↥G₁ →* ↥G₁ ⧸ center ↥G₁ := QuotientGroup.mk' _
  have hmap : (N'.map π).Normal := hN'.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map π) with h | h
  · left
    intro x hx y hy
    have hxN' : (⟨x, hN hx⟩ : ↥G₁) ∈ N' := Subgroup.mem_subgroupOf.2 hx
    have h1 : π ⟨x, hN hx⟩ ∈ N'.map π := Subgroup.mem_map_of_mem _ hxN'
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hN hx⟩ : ↥G₁) ∈ center ↥G₁ := (QuotientGroup.eq_one_iff _).1 h1
    have := Subgroup.mem_center_iff.1 h2 ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · right
    apply le_antisymm hN
    have hsup : N' ⊔ center ↥G₁ = ⊤ := by
      have : (N'.map π).comap π = N' ⊔ π.ker := Subgroup.comap_map_eq π N'
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    calc G₁ = ⁅G₁, G₁⁆ := c.perfect.symm
      _ ≤ N := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        have ha' : (⟨a, ha⟩ : ↥G₁) ∈ N' ⊔ center ↥G₁ := by rw [hsup]; trivial
        have hb' : (⟨b, hb⟩ : ↥G₁) ∈ N' ⊔ center ↥G₁ := by rw [hsup]; trivial
        obtain ⟨y₁, hy₁, z₁, hz₁, e₁⟩ := Subgroup.mem_sup_of_normal_right.1 ha'
        obtain ⟨y₂, hy₂, z₂, hz₂, e₂⟩ := Subgroup.mem_sup_of_normal_right.1 hb'
        have key := commutator_mul_central y₁ y₂ z₁ z₂
          (fun g => (Subgroup.mem_center_iff.1 hz₁ g).symm)
          (fun g => (Subgroup.mem_center_iff.1 hz₂ g).symm)
        rw [e₁, e₂] at key
        have key' := congrArg Subtype.val key
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at key'
        rw [commutatorElement_def, key']
        have h1 : (y₁ : G) ∈ N := Subgroup.mem_subgroupOf.1 hy₁
        have h2 : (y₂ : G) ∈ N := Subgroup.mem_subgroupOf.1 hy₂
        exact N.mul_mem (N.mul_mem (N.mul_mem h1 h2) (N.inv_mem h1)) (N.inv_mem h2)

theorem cs_normal (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) {g k : G} (hg : g ∈ G₁ ⊔ G₂)
    (hk : k ∈ cs n G₁) : g * k * g⁻¹ ∈ cs n G₁ := by
  rw [mem_cs] at hk ⊢
  have hg' : n⁻¹ * g * n ∈ G₁ ⊔ G₂ := by
    have := (mem_normalizer_iff.1 (inv_mem hn) g).1 hg
    simpa using this
  have := c.conj_mem_G₁ hg' hk
  have e : n⁻¹ * g * n * (n⁻¹ * k * n) * (n⁻¹ * g * n)⁻¹ = n⁻¹ * (g * k * g⁻¹) * n := by group
  rwa [e] at this

theorem dich₁ [Finite G] (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    (∀ x ∈ cs n G₁ ⊓ G₁, ∀ y ∈ G₁, x * y = y * x) ∨ cs n G₁ = G₁ := by
  rcases c.normal_dich (N := cs n G₁ ⊓ G₁) inf_le_right
    (fun g hg x hx => ⟨c.cs_normal hn (Subgroup.mem_sup_left hg) hx.1,
      c.conj_mem_G₁ (Subgroup.mem_sup_left hg) hx.2⟩) with h | h
  · exact Or.inl h
  · right
    have hle : G₁ ≤ cs n G₁ := by
      intro x hx
      have : x ∈ cs n G₁ ⊓ G₁ := by rw [h]; exact hx
      exact this.1
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [nat_card_cs])).symm

theorem commutator_eq_bot_aux {K H G₀ : Subgroup G} (hK0 : K ≤ G₀)
    (hHn : ∀ g ∈ G₀, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hKn : ∀ g ∈ G₀, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hH0 : H ≤ G₀) (hKperf : ⁅K, K⁆ = K) (hcent : ∀ x ∈ K ⊓ H, ∀ y ∈ G₀, x * y = y * x) :
    ⁅K, H⁆ = ⊥ := by
  have hz : ∀ k ∈ K, ∀ g ∈ H, ∀ y ∈ G₀, ⁅k, g⁆ * y = y * ⁅k, g⁆ := by
    intro k hk g hg y hy
    refine hcent _ ⟨?_, ?_⟩ y hy
    · have h1 := hKn g (hH0 hg) k⁻¹ (K.inv_mem hk)
      rw [commutatorElement_def]
      have := K.mul_mem hk h1
      simpa [mul_assoc] using this
    · have h1 := hHn k (hK0 hk) g hg
      rw [commutatorElement_def]
      exact H.mul_mem h1 (H.inv_mem hg)
  have h1 : ⁅⁅K, H⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro k hk g hg
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    exact (hz k hk g hg k' (hK0 hk')).symm
  have h2 : ⁅⁅H, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm H K]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := H) h1 h2
  rwa [hKperf] at h3

theorem K_eq_bot (c : CompData G₁ G₂ t) {K : Subgroup G} (hK0 : K ≤ G₁ ⊔ G₂)
    (hKperf : ⁅K, K⁆ = K) (hKn : ∀ g ∈ G₁ ⊔ G₂, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hA : ∀ x ∈ K ⊓ G₁, ∀ y ∈ G₁, x * y = y * x)
    (hB : ∀ x ∈ K ⊓ G₂, ∀ y ∈ G₂, x * y = y * x) : K = ⊥ := by
  have e1 : ⁅K, G₁⁆ = ⊥ := by
    refine commutator_eq_bot_aux hK0 (fun g hg x hx => c.conj_mem_G₁ hg hx) hKn le_sup_left
      hKperf ?_
    intro x hx y hy
    have hxc : G₁ ⊔ G₂ ≤ centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hA x hx z hz).symm
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact c.mul_comm_of_mem hx.2 hz |>.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hxc hy)).symm
  have e2 : ⁅K, G₂⁆ = ⊥ := by
    refine commutator_eq_bot_aux hK0 (fun g hg x hx => c.conj_mem_G₂ hg hx) hKn le_sup_right
      hKperf ?_
    intro x hx y hy
    have hxc : G₁ ⊔ G₂ ≤ centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact c.mul_comm_of_mem hz hx.2
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hB x hx z hz).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hxc hy)).symm
  have hKc : K ≤ centralizer ((K : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    have hk'0 := hK0 hk'
    have hxc : G₁ ⊔ G₂ ≤ centralizer ({k} : Set G) := by
      refine sup_le ?_ ?_
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 e1) hk) z hz)
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 e2) hk) z hz)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hxc hk'0)).symm.symm
  rw [← hKperf, ← Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKc]

theorem comp_perm [Finite G] (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    cs n G₁ = G₁ ∨ cs n G₁ = G₂ := by
  set K := cs n G₁ with hKdef
  have hKperf : ⁅K, K⁆ = K := by rw [hKdef, ← cs_commutator, c.perfect]
  have hcs0 : cs n (G₁ ⊔ G₂) = G₁ ⊔ G₂ := mem_normalizer_iff_cs.1 hn
  have hK0 : K ≤ G₁ ⊔ G₂ := by
    calc K ≤ cs n (G₁ ⊔ G₂) := cs_mono n le_sup_left
      _ = G₁ ⊔ G₂ := hcs0
  have hKn : ∀ g ∈ G₁ ⊔ G₂, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g hg k hk => c.cs_normal hn hg hk
  rcases c.dich₁ hn with hA | hA
  · have hn'' : t⁻¹ * n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) :=
      mul_mem (inv_mem c.t_mem_normalizer) hn
    rcases c.dich₁ hn'' with hB | hB
    · exfalso
      have hB' : ∀ x ∈ K ⊓ G₂, ∀ y ∈ G₂, x * y = y * x := by
        intro x hx y hy
        have hx' : t⁻¹ * x * t ∈ cs (t⁻¹ * n) G₁ ⊓ G₁ := by
          refine ⟨mem_cs.2 ?_, (c.swap x).1 hx.2⟩
          have h1 : n⁻¹ * x * n ∈ G₁ := mem_cs.1 hx.1
          have e : (t⁻¹ * n)⁻¹ * (t⁻¹ * x * t) * (t⁻¹ * n) = n⁻¹ * x * n := by group
          rw [e]
          exact h1
        have h := hB _ hx' (t⁻¹ * y * t) ((c.swap y).1 hy)
        have e1 : t⁻¹ * x * t * (t⁻¹ * y * t) = t⁻¹ * (x * y) * t := by group
        have e2 : t⁻¹ * y * t * (t⁻¹ * x * t) = t⁻¹ * (y * x) * t := by group
        rw [e1, e2] at h
        exact mul_left_cancel (mul_right_cancel h)
      have hKbot := c.K_eq_bot hK0 hKperf hKn hA hB'
      apply c.G₁_ne_bot
      have : cs n⁻¹ K = ⊥ := by rw [hKbot]; exact Subgroup.map_bot _
      rwa [hKdef, cs_inv_cs] at this
    · right
      have h1 : cs t⁻¹ K = G₁ := by rw [hKdef, ← cs_mul]; exact hB
      have h2 : K = cs t G₁ := by
        have := congrArg (cs t) h1
        rwa [← cs_mul, c.t_inv, c.t_sq, cs_one] at this
      rw [h2, c.cs_t_G₁]
  · exact Or.inl hA

end CompData

end CFSG.OddStandard.Seitz77.CaseB45
