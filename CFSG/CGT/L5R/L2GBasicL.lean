module

public import CFSG.CGT.T75JM.L2GModel

public section

namespace CFSG.CGT.L5R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM

variable {G H : Type*} [Group G] [Group H]

structure TCtxL (T T₁ : Subgroup G) : Prop where
  wc : IsWC T
  inf_bot : T ⊓ T₁ = ⊥
  conj : ∃ s : G, T₁ = conjSubgroup s T
  norm1 : Nat.card (normIn T T₁) = 8
  norm2 : Nat.card (normIn T₁ T) = 8

namespace TCtxL

variable {T T₁ : Subgroup G} (h : TCtxL T T₁)
include h

theorem wc₁ : IsWC T₁ := by
  obtain ⟨s, rfl⟩ := h.conj
  exact h.wc.conj s

theorem elemAbelian₁ : IsElemAbelian 2 T₁ := h.wc₁.1

theorem symm : TCtxL T₁ T where
  wc := h.wc₁
  inf_bot := by rw [inf_comm]; exact h.inf_bot
  conj := by
    obtain ⟨s, hs⟩ := h.conj
    refine ⟨s⁻¹, ?_⟩
    rw [hs, conjSubgroup_conjSubgroup]
    simp [conjSubgroup_one]
  norm1 := h.norm2
  norm2 := h.norm1

theorem mem_normalizer_B_iff {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    n ∈ Subgroup.normalizer ((normIn T₁ T : Subgroup G) : Set G) ↔
      n ∈ Subgroup.normalizer (T₁ : Set G) := by
  constructor
  · intro hnB
    obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_one_lt_card (K := normIn T₁ T)
      (by rw [h.norm2]; norm_num)
    have hb' : n * b * n⁻¹ ∈ normIn T₁ T := (Subgroup.mem_normalizer_iff.1 hnB b).1 hb
    have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
    have hb'T₁ : n * b * n⁻¹ ∈ T₁ := (mem_normIn.1 hb').1
    have hb'1 : n * b * n⁻¹ ≠ 1 := by
      intro h1
      apply hb1
      have : b = n⁻¹ * (n * b * n⁻¹) * n := by group
      rw [this, h1]
      group
    obtain ⟨s, hs⟩ := h.conj
    have hmem1 : n * b * n⁻¹ ∈ conjSubgroup s T := by rw [← hs]; exact hb'T₁
    have hmem2 : n * b * n⁻¹ ∈ conjSubgroup (n * s) T := by
      rw [← conjSubgroup_conjSubgroup, ← hs, mem_conjSubgroup]
      simpa [mul_assoc] using hbT₁
    have heq := inter_unique h.wc hmem1 hmem2 hb'1
    rw [← hs, ← conjSubgroup_conjSubgroup, ← hs] at heq
    rw [mem_normalizer_iff_conjSubgroup_eq]
    exact heq.symm
  · intro hn1
    exact mem_normalizer_inf' hn1 (Subgroup.le_normalizer hn)

theorem mem_normalizer_A_iff {n : G} (hn : n ∈ Subgroup.normalizer (T₁ : Set G)) :
    n ∈ Subgroup.normalizer ((normIn T T₁ : Subgroup G) : Set G) ↔
      n ∈ Subgroup.normalizer (T : Set G) :=
  h.symm.mem_normalizer_B_iff hn

theorem comm_A_B {a b : G} (ha : a ∈ normIn T T₁) (hb : b ∈ normIn T₁ T) : a * b = b * a := by
  have haT : a ∈ T := (mem_normIn.1 ha).1
  have haN₁ : a ∈ Subgroup.normalizer (T₁ : Set G) := (mem_normIn.1 ha).2
  have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hb).2
  have haN : a ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer haT
  have hbN₁ : b ∈ Subgroup.normalizer (T₁ : Set G) := Subgroup.le_normalizer hbT₁
  have h1 : a * b * a⁻¹ ∈ normIn T₁ T :=
    (Subgroup.mem_normalizer_iff.1 ((h.mem_normalizer_B_iff haN).2 haN₁) b).1 hb
  have h2 : b * a * b⁻¹ ∈ normIn T T₁ :=
    (Subgroup.mem_normalizer_iff.1 ((h.mem_normalizer_A_iff hbN₁).2 hbN) a).1 ha
  have hc1 : a * b * a⁻¹ * b⁻¹ ∈ T₁ :=
    T₁.mul_mem (mem_normIn.1 h1).1 (T₁.inv_mem hbT₁)
  have hc2 : a * b * a⁻¹ * b⁻¹ ∈ T := by
    have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [this]
    refine T.mul_mem haT ?_
    have h3 : (b * a * b⁻¹)⁻¹ ∈ T := T.inv_mem (mem_normIn.1 h2).1
    simpa [mul_assoc] using h3
  have hbot : a * b * a⁻¹ * b⁻¹ ∈ T ⊓ T₁ := ⟨hc2, hc1⟩
  rw [h.inf_bot, Subgroup.mem_bot] at hbot
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hbot]; group

theorem inf_centralizer_eq {b : G} (hb : b ∈ normIn T₁ T) (hb1 : b ≠ 1) :
    T ⊓ Subgroup.centralizer ({b} : Set G) = normIn T T₁ := by
  ext t
  constructor
  · intro ht
    obtain ⟨htT, htC⟩ := Subgroup.mem_inf.1 ht
    exact mem_normIn.2 ⟨htT, h.wc₁.centralizer_le_normalizer (mem_normIn.1 hb).1 hb1 htC⟩
  · intro ht
    exact Subgroup.mem_inf.2 ⟨(mem_normIn.1 ht).1,
      Subgroup.mem_centralizer_singleton_iff.2 (h.comm_A_B ht hb)⟩

theorem mem_normalizer_comap_iff (E : OntoEmb H (Subgroup.normalizer (T : Set G))) (x : H) :
    x ∈ Subgroup.normalizer ((T₁.comap E.Φ : Subgroup H) : Set H) ↔
      E.Φ x ∈ Subgroup.normalizer (T₁ : Set G) := by
  constructor
  · intro hx
    refine (h.mem_normalizer_B_iff (E.mem x)).1 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hy
      obtain ⟨z, rfl⟩ := E.surj y hyN
      have hz : z ∈ T₁.comap E.Φ := hyT₁
      have := (Subgroup.mem_normalizer_iff.1 hx z).1 hz
      refine mem_normIn.2 ⟨?_, ?_⟩
      · simpa using this
      · exact (Subgroup.normalizer (T : Set G)).mul_mem
          ((Subgroup.normalizer (T : Set G)).mul_mem (E.mem x) (E.mem z))
          ((Subgroup.normalizer (T : Set G)).inv_mem (E.mem x))
    · intro hy
      obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hy
      have hyN' : y ∈ Subgroup.normalizer (T : Set G) := by
        have h1 := (Subgroup.normalizer (T : Set G)).mul_mem
          ((Subgroup.normalizer (T : Set G)).inv_mem (E.mem x))
          ((Subgroup.normalizer (T : Set G)).mul_mem hyN (E.mem x))
        simpa [mul_assoc] using h1
      obtain ⟨z, rfl⟩ := E.surj y hyN'
      have hz : x * z * x⁻¹ ∈ T₁.comap E.Φ := by simpa using hyT₁
      have := (Subgroup.mem_normalizer_iff.1 hx z).2 hz
      exact mem_normIn.2 ⟨this, hyN'⟩
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 hx (E.Φ z)

end TCtxL

theorem card_inf_centralizer_comap {T : Subgroup G}
    (E : OntoEmb H (Subgroup.normalizer (T : Set G))) {T0 : Subgroup H}
    (hT : ∀ x, x ∈ T0 ↔ E.Φ x ∈ T) (y : H) :
    Nat.card ↥(T0 ⊓ Subgroup.centralizer ({y} : Set H)) =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({E.Φ y} : Set G)) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : ↥(T0 ⊓ Subgroup.centralizer ({y} : Set H)) =>
      (⟨E.Φ x, Subgroup.mem_inf.2 ⟨(hT x).1 (Subgroup.mem_inf.1 x.2).1, by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2]⟩⟩ :
        ↥(T ⊓ Subgroup.centralizer ({E.Φ y} : Set G)))) ⟨?_, ?_⟩)
  · intro x z hxz
    exact Subtype.ext (E.inj (congrArg Subtype.val hxz))
  · rintro ⟨t, ht⟩
    obtain ⟨htT, htC⟩ := Subgroup.mem_inf.1 ht
    obtain ⟨x, rfl⟩ := E.surj t (Subgroup.le_normalizer htT)
    refine ⟨⟨x, Subgroup.mem_inf.2 ⟨(hT x).2 htT, ?_⟩⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply E.inj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 htC

theorem conj_mem_conjSubgroup {T : Subgroup G} {g y : G} (hy : y ∈ conjSubgroup g T) (a : G) :
    a * y * a⁻¹ ∈ conjSubgroup (a * g) T := by
  rw [mem_conjSubgroup] at hy ⊢
  have e : (a * g)⁻¹ * (a * y * a⁻¹) * (a * g) = g⁻¹ * y * g := by group
  rw [e]
  exact hy

end CFSG.CGT.L5R
