module

public import CFSG.GH74.BNPair.Defs

public section

namespace CFSG.GH74.BNPair

open scoped Pointwise

variable {X : Type*} [Group X]

theorem mem_dcoset_iff {B : Subgroup X} {g x : X} :
    x ∈ (B : Set X) * {g} * (B : Set X) ↔ ∃ b ∈ B, ∃ b' ∈ B, x = b * g * b' := by
  simp only [Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, g, rfl, rfl⟩, b', hb', rfl⟩

section DoubleCosets

variable {B N : Subgroup X} [(cartan B N).Normal]

theorem mk_eq_one_iff {n : N} : (n : WeylGroup B N) = 1 ↔ (n : X) ∈ B := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, n.2⟩⟩

omit [(cartan B N).Normal] in
theorem mk_eq_mk_iff {n m : N} :
    (n : WeylGroup B N) = (m : WeylGroup B N) ↔ ((n : X)⁻¹ * m) ∈ B := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, (n⁻¹ * m).2⟩⟩

omit [(cartan B N).Normal] in
theorem mem_dc_iff {w : WeylGroup B N} {x : X} :
    x ∈ dc B N w ↔ ∃ n : N, (n : WeylGroup B N) = w ∧ ∃ b ∈ B, ∃ b' ∈ B, x = b * n * b' := by
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, mem_dcoset_iff.1 hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, mem_dcoset_iff.2 hx⟩

omit [(cartan B N).Normal] in
theorem mem_dc_mk_iff {n : N} {x : X} :
    x ∈ dc B N (n : WeylGroup B N) ↔ ∃ b ∈ B, ∃ b' ∈ B, x = b * n * b' := by
  rw [mem_dc_iff]
  constructor
  · rintro ⟨m, hm, b, hb, b', hb', rfl⟩
    have h : ((m : X)⁻¹ * (n : X)) ∈ B := mk_eq_mk_iff.1 hm
    have h' : ((n : X)⁻¹ * (m : X)) ∈ B := by simpa using B.inv_mem h
    exact ⟨b, hb, ((n : X)⁻¹ * (m : X)) * b', B.mul_mem h' hb',
      by simp only [mul_assoc, mul_inv_cancel_left]⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨n, rfl, b, hb, b', hb', rfl⟩

omit [(cartan B N).Normal] in
theorem mem_dc_of_lift {w : WeylGroup B N} {n : N} (hn : (n : WeylGroup B N) = w) {x : X} :
    x ∈ dc B N w ↔ ∃ b ∈ B, ∃ b' ∈ B, x = b * n * b' := by
  subst hn
  exact mem_dc_mk_iff

omit [(cartan B N).Normal] in
theorem coe_mem_dc (n : N) : (n : X) ∈ dc B N (n : WeylGroup B N) :=
  mem_dc_mk_iff.2 ⟨1, B.one_mem, 1, B.one_mem, by simp⟩

omit [(cartan B N).Normal] in
theorem mul_mem_dc {w : WeylGroup B N} {x b b' : X} (hx : x ∈ dc B N w) (hb : b ∈ B)
    (hb' : b' ∈ B) : b * x * b' ∈ dc B N w := by
  rcases mem_dc_iff.1 hx with ⟨n, hn, c, hc, c', hc', rfl⟩
  exact mem_dc_iff.2 ⟨n, hn, b * c, B.mul_mem hb hc, c' * b', B.mul_mem hc' hb',
    by simp only [mul_assoc]⟩

omit [(cartan B N).Normal] in
theorem mem_dc_of_mem {w : WeylGroup B N} {x y : X} (hx : x ∈ dc B N w) {b b' : X} (hb : b ∈ B)
    (hb' : b' ∈ B) (hy : y = b * x * b') : y ∈ dc B N w :=
  hy ▸ mul_mem_dc hx hb hb'

omit [(cartan B N).Normal] in
theorem dc_subset_of_biinv {T : Set X} (hT : ∀ b ∈ B, ∀ x ∈ T, ∀ b' ∈ B, b * x * b' ∈ T)
    {w : WeylGroup B N} {z : X} (hz : z ∈ dc B N w) (hzT : z ∈ T) : dc B N w ⊆ T := by
  intro y hy
  rcases mem_dc_iff.1 hz with ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩
  rcases (mem_dc_of_lift hn).1 hy with ⟨c₁, hc₁, c₂, hc₂, rfl⟩
  have := hT (c₁ * b₁⁻¹) (B.mul_mem hc₁ (B.inv_mem hb₁)) _ hzT (b₂⁻¹ * c₂)
    (B.mul_mem (B.inv_mem hb₂) hc₂)
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left] using this

omit [(cartan B N).Normal] in
theorem dc_subset_of_mem {w w' : WeylGroup B N} {x : X} (hx : x ∈ dc B N w)
    (hx' : x ∈ dc B N w') : dc B N w ⊆ dc B N w' :=
  dc_subset_of_biinv (fun _ hb _ hy _ hb' => mul_mem_dc hy hb hb') hx hx'

omit [(cartan B N).Normal] in
theorem dc_eq_of_mem {w w' : WeylGroup B N} {x : X} (hx : x ∈ dc B N w) (hx' : x ∈ dc B N w') :
    dc B N w = dc B N w' :=
  (dc_subset_of_mem hx hx').antisymm (dc_subset_of_mem hx' hx)

theorem mem_dc_one {x : X} : x ∈ dc B N (1 : WeylGroup B N) ↔ x ∈ B := by
  rw [mem_dc_of_lift (n := 1) (by simp)]
  constructor
  · rintro ⟨b, hb, b', hb', rfl⟩
    simpa using B.mul_mem hb hb'
  · intro hx
    exact ⟨x, hx, 1, B.one_mem, by simp⟩

theorem dc_one : dc B N (1 : WeylGroup B N) = (B : Set X) :=
  Set.ext fun _ => mem_dc_one

theorem inv_mem_dc {w : WeylGroup B N} {x : X} (hx : x ∈ dc B N w) : x⁻¹ ∈ dc B N w⁻¹ := by
  rcases mem_dc_iff.1 hx with ⟨n, hn, b, hb, b', hb', rfl⟩
  refine mem_dc_iff.2 ⟨n⁻¹, by rw [QuotientGroup.mk_inv, hn], b'⁻¹, B.inv_mem hb', b⁻¹,
    B.inv_mem hb, ?_⟩
  simp [mul_assoc]

theorem inv_mem_dc_iff {w : WeylGroup B N} {x : X} : x⁻¹ ∈ dc B N w⁻¹ ↔ x ∈ dc B N w := by
  refine ⟨fun h => ?_, inv_mem_dc⟩
  simpa using inv_mem_dc h

omit [(cartan B N).Normal] in
theorem mem_dc_mul_dc_biinv (a b : WeylGroup B N) :
    ∀ b₁ ∈ B, ∀ x ∈ dc B N a * dc B N b, ∀ b₂ ∈ B, b₁ * x * b₂ ∈ dc B N a * dc B N b := by
  intro b₁ hb₁ x hx b₂ hb₂
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
  exact Set.mem_mul.2 ⟨b₁ * y, mem_dc_of_mem hy hb₁ B.one_mem (by simp), z * b₂,
    mem_dc_of_mem hz B.one_mem hb₂ (by simp), by simp only [mul_assoc]⟩


theorem dc_mul_subset_of (a b : WeylGroup B N) : dc B N (a * b) ⊆ dc B N a * dc B N b := by
  intro y hy
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, mem_dc_mk_iff] at hy
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hy
  exact Set.mem_mul.2 ⟨b₁ * n, mem_dc_of_mem (coe_mem_dc n) hb₁ B.one_mem (by simp), m * b₂,
    mem_dc_of_mem (coe_mem_dc m) B.one_mem hb₂ (by simp), by simp [mul_assoc]⟩

structure BNCore (B N : Subgroup X) [(cartan B N).Normal] (J : Set (WeylGroup B N)) : Prop where
  mul_self_eq_one : ∀ s ∈ J, s * s = 1
  ne_one : ∀ s ∈ J, s ≠ 1
  mul_subset : ∀ s ∈ J, ∀ w : WeylGroup B N,
    dc B N s * dc B N w ⊆ dc B N (s * w) ∪ dc B N w
  not_subset : ∀ s ∈ J, ¬ dc B N s * dc B N s ⊆ (B : Set X)

theorem IsTitsSystem.bnCore {S : Finset (WeylGroup B N)} (h : IsTitsSystem B N S) :
    BNCore B N (S : Set (WeylGroup B N)) where
  mul_self_eq_one s hs := by
    have h2 := h.involution s hs
    have := pow_orderOf_eq_one s
    rw [h2, sq] at this
    exact this
  ne_one s hs h1 := by
    have h2 := h.involution s hs
    simp [h1] at h2
  mul_subset s hs w := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := mem_dc_iff.1 hy
    obtain ⟨m, hm, b₃, hb₃, b₄, hb₄, rfl⟩ := mem_dc_iff.1 hz
    have hsub := h.mul_subset n m (by simpa [hn] using hs)
    have hmem : (n : X) * (b₂ * b₃) * (m : X) ∈
        ({(n : X)} : Set X) * (B : Set X) * {(m : X)} :=
      Set.mem_mul.2 ⟨(n : X) * (b₂ * b₃), Set.mem_mul.2 ⟨n, rfl, b₂ * b₃, B.mul_mem hb₂ hb₃, rfl⟩,
        m, rfl, rfl⟩
    have key : b₁ * (n : X) * b₂ * (b₃ * (m : X) * b₄) =
        b₁ * ((n : X) * (b₂ * b₃) * (m : X)) * b₄ := by simp only [mul_assoc]
    rw [key]
    rw [hn, hm] at hsub
    rcases hsub hmem with h1 | h1
    · exact Or.inl (mul_mem_dc h1 hb₁ hb₄)
    · exact Or.inr (mul_mem_dc h1 hb₁ hb₄)
  not_subset s hs hss := by
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective s
    have h1 : (n : WeylGroup B N) * n = 1 := by
      have h2 := h.involution _ hs
      have := pow_orderOf_eq_one (n : WeylGroup B N)
      rw [h2, sq] at this
      exact this
    have hnn : (n : X) * n ∈ B := by
      have : ((n * n : N) : WeylGroup B N) = 1 := by rw [QuotientGroup.mk_mul]; exact h1
      simpa using mk_eq_one_iff.1 this
    have hmem : ∀ c ∈ B, (n : X) * c * n ∈ (B : Set X) := by
      intro c hc
      refine hss (Set.mem_mul.2 ⟨n, coe_mem_dc n, c * n, ?_, by simp [mul_assoc]⟩)
      exact mem_dc_of_mem (coe_mem_dc n) hc B.one_mem (by simp)
    refine h.ne n hs (Set.Subset.antisymm ?_ ?_)
    · rintro _ ⟨_, ⟨_, rfl, c, hc, rfl⟩, _, rfl, rfl⟩
      exact hmem c hc
    · intro b hb
      have hc : (n : X)⁻¹ * b * (n : X)⁻¹ ∈ B := by
        have h' : (n : X)⁻¹ * b * (n : X)⁻¹ =
            ((n : X) * (((n : X) * n)⁻¹ * b) * n) * ((n : X) * n)⁻¹ := by group
        rw [h']
        exact B.mul_mem (hmem _ (B.mul_mem (B.inv_mem hnn) hb)) (B.inv_mem hnn)
      exact Set.mem_mul.2 ⟨n * ((n : X)⁻¹ * b * (n : X)⁻¹),
        Set.mem_mul.2 ⟨n, rfl, _, hc, rfl⟩, n, rfl, by group⟩


section Core

variable {J : Set (WeylGroup B N)}

theorem BNCore.inv_eq (hJ : BNCore B N J) {s : WeylGroup B N} (hs : s ∈ J) : s⁻¹ = s :=
  inv_eq_of_mul_eq_one_right (hJ.mul_self_eq_one s hs)

theorem BNCore.mul_subset_right (hJ : BNCore B N J) {s : WeylGroup B N} (hs : s ∈ J)
    (w : WeylGroup B N) : dc B N w * dc B N s ⊆ dc B N (w * s) ∪ dc B N w := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
  have hz' : z⁻¹ ∈ dc B N s := by simpa [hJ.inv_eq hs] using inv_mem_dc hz
  have hy' : y⁻¹ ∈ dc B N w⁻¹ := inv_mem_dc hy
  have h1 := hJ.mul_subset s hs w⁻¹ (Set.mem_mul.2 ⟨z⁻¹, hz', y⁻¹, hy', rfl⟩)
  rcases h1 with h1 | h1
  · left
    simpa [mul_inv_rev, hJ.inv_eq hs] using inv_mem_dc h1
  · right
    simpa using inv_mem_dc h1

theorem BNCore.mul_self_subset (hJ : BNCore B N J) {s : WeylGroup B N} (hs : s ∈ J) :
    dc B N s * dc B N s ⊆ (B : Set X) ∪ dc B N s := by
  have h := hJ.mul_subset s hs s
  rwa [hJ.mul_self_eq_one s hs, dc_one] at h

theorem BNCore.subset_mul_self (hJ : BNCore B N J) {s : WeylGroup B N} (hs : s ∈ J) :
    (B : Set X) ∪ dc B N s ⊆ dc B N s * dc B N s := by
  have hB : (B : Set X) ⊆ dc B N s * dc B N s := by
    rw [← dc_one (B := B) (N := N), ← hJ.mul_self_eq_one s hs]
    exact dc_mul_subset_of s s
  intro x hx
  rcases hx with hx | hx
  · exact hB hx
  · obtain ⟨z, hz, hzB⟩ := Set.not_subset.1 (hJ.not_subset s hs)
    have hz' : z ∈ dc B N s := (hJ.mul_self_subset hs hz).resolve_left hzB
    exact dc_subset_of_biinv (mem_dc_mul_dc_biinv s s) hz' hz hx

theorem BNCore.mul_self (hJ : BNCore B N J) {s : WeylGroup B N} (hs : s ∈ J) :
    dc B N s * dc B N s = (B : Set X) ∪ dc B N s :=
  (hJ.mul_self_subset hs).antisymm (hJ.subset_mul_self hs)

theorem dc_subset_mul (a b : WeylGroup B N) : dc B N (a * b) ⊆ dc B N a * dc B N b :=
  dc_mul_subset_of a b

end Core

end DoubleCosets

end CFSG.GH74.BNPair
