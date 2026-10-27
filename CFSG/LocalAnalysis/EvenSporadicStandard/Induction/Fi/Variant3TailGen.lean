module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General

public section

open scoped commutatorElement

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem le_of_isPerfect_of_index_le_two [Finite H] {N L : Subgroup H} [N.Normal]
    (hN : N.index ≤ 2) (hL : Group.IsPerfect ↥L) : L ≤ N := by
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h | h
  · rw [Subgroup.index_eq_one] at h
    rw [h]
    exact le_top
  · have hcard : Nat.card (H ⧸ N) = 2 := by rwa [← Subgroup.index_eq_card]
    have : IsCyclic (H ⧸ N) := isCyclic_of_prime_card hcard
    have : IsMulCommutative (H ⧸ N) := IsCyclic.isMulCommutative
    let f : L →* H ⧸ N := (QuotientGroup.mk' N).comp L.subtype
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    have : Subsingleton f.range := inferInstance
    intro x hx
    have hfx : f ⟨x, hx⟩ = 1 :=
      congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨x, hx⟩) 1)
    exact (QuotientGroup.eq_one_iff (N := N) x).mp hfx

theorem commutator_eq_self_of_perfect {K : Subgroup H} (hK : Group.IsPerfect ↥K) : ⁅K, K⁆ = K := by
  have h := congrArg (Subgroup.map K.subtype) (Group.isPerfect_def.1 hK)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem commutator_mul_mul_of_commute' {a b c d : H} (hbc : Commute b c)
    (hbd : Commute b d) (hda : Commute d a) : ⁅a * b, c * d⁆ = ⁅a, c⁆ := by
  have e1 : b * c * d * b⁻¹ = c * d := by
    rw [hbc.eq, mul_assoc c b d, hbd.eq]
    group
  rw [commutatorElement_def, commutatorElement_def]
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = a * (b * c * d * b⁻¹) * a⁻¹ * d⁻¹ * c⁻¹ := by
        group
    _ = a * c * (d * a⁻¹) * d⁻¹ * c⁻¹ := by rw [e1]; group
    _ = a * c * (a⁻¹ * d) * d⁻¹ * c⁻¹ := by rw [hda.inv_right.eq]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem commutator_mem_of_cosets {O : Subgroup H} {u x y : H}
    (hcomm : ∀ c ∈ O, u * c = c * u)
    (hx : ∃ c ∈ O, x = c ∨ x = u * c) (hy : ∃ c ∈ O, y = c ∨ y = u * c) : ⁅x, y⁆ ∈ O := by
  have key : ∀ z : H, (∃ c ∈ O, z = c ∨ z = u * c) →
      ∃ c ∈ O, ∃ b, (b = 1 ∨ b = u) ∧ z = c * b := by
    rintro z ⟨c, hc, h | h⟩
    · exact ⟨c, hc, 1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨c, hc, u, Or.inr rfl, by rw [h, hcomm c hc]⟩
  obtain ⟨c, hc, b, hb, rfl⟩ := key x hx
  obtain ⟨c', hc', d, hd, rfl⟩ := key y hy
  have hbc : Commute b c' := by
    rcases hb with rfl | rfl
    · exact Commute.one_left _
    · exact hcomm c' hc'
  have hdc : Commute d c := by
    rcases hd with rfl | rfl
    · exact Commute.one_left _
    · exact hcomm c hc
  have hbd : Commute b d := by
    rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;>
      first | exact Commute.refl _ | exact Commute.one_left _ | exact Commute.one_right _
  rw [commutator_mul_mul_of_commute' hbc hbd hdc, commutatorElement_def]
  exact O.mul_mem (O.mul_mem (O.mul_mem hc hc') (O.inv_mem hc)) (O.inv_mem hc')

theorem map_conjHom_eq_of_commute {S : Subgroup H} {x : H} (hx : ∀ s ∈ S, x * s = s * x) :
    S.map (conjHom x) = S := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : x * s * x⁻¹ = s := by rw [hx s hs]; group
    rw [conjHom_apply, this]
    exact hs
  · intro hy
    refine ⟨y, hy, ?_⟩
    rw [conjHom_apply, hx y hy]
    group

theorem mem_normalizer_of_map_conjHom_eq {S : Subgroup H} {g : H} (h : S.map (conjHom g) = S) :
    g ∈ normalizer (S : Set H) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_of_map_eq h hy
  · intro hy
    have := conj_inv_mem_of_map_eq h hy
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at this

theorem eq_one_of_mul_self_eq_one [Finite H] {C N : Subgroup H} [N.Normal] {t c : H}
    (hS : ∀ S : Sylow 2 C, Nat.card S = 2) (htC : t ∈ C) (ht2 : orderOf t = 2) (htN : t ∉ N)
    (hcC : c ∈ C) (hcN : c ∈ N) (hc : c * c = 1) : c = 1 := by
  by_contra hc1
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rwa [pow_two]) hc1
  have key : ∀ (x : H) (hx : x ∈ C), orderOf x = 2 →
      ∃ P : Sylow 2 C, (P : Subgroup C) = zpowers (⟨x, hx⟩ : C) := by
    intro x hx hx2
    have hord : orderOf (⟨x, hx⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
    have hcard : Nat.card (zpowers (⟨x, hx⟩ : C)) = 2 := by rw [Nat.card_zpowers, hord]
    have hp : IsPGroup 2 (zpowers (⟨x, hx⟩ : C)) :=
      IsPGroup.of_card (n := 1) (by rw [hcard]; simp)
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, (Subgroup.eq_of_le_of_card_ge hP (by rw [hcard, hS P])).symm⟩
  obtain ⟨P, hP⟩ := key c hcC hc2
  obtain ⟨Q, hQ⟩ := key t htC ht2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q P
  have hcP : (⟨c, hcC⟩ : C) ∈ (P : Subgroup C) := by rw [hP]; exact mem_zpowers _
  rw [← hg, Sylow.coe_subgroup_smul, hQ, Subgroup.mem_smul_pointwise_iff_exists] at hcP
  obtain ⟨s, hs, hsc⟩ := hcP
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hs
  have hord : orderOf (⟨t, htC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  rcases zpow_eq_one_or_self_of_orderOf_eq_two hord k with h1 | h1
  · rw [h1] at hsc
    have : (⟨c, hcC⟩ : C) = 1 := by rw [← hsc]; simp
    exact hc1 (congrArg Subtype.val this)
  · rw [h1] at hsc
    have h2 : (g : H) * t * (g : H)⁻¹ = c := by
      have := congrArg Subtype.val hsc
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    apply htN
    have : t = (g : H)⁻¹ * c * g := by rw [← h2]; group
    rw [this]
    simpa using Subgroup.Normal.conj_mem inferInstance c hcN (g : H)⁻¹

theorem mem_normalizer_of_mem_centralizer {K L : Subgroup H} {u l x : H}
    (h35 : K = componentProduct K u) (hu₁ : l * u * l⁻¹ ∈ K)
    (hgen : K ⊔ K.map (conjHom l) = L) (hx : x ∈ centralizer (K : Set H)) :
    x ∈ normalizer (L : Set H) := by
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk => (mem_centralizer_iff.1 hx k hk).symm
  have h1 : K.map (conjHom x) = K := map_conjHom_eq_of_commute hxK
  have hcp : componentProduct K (l * u * l⁻¹) = K.map (conjHom l) := by
    rw [componentProduct_conj, ← h35]
  have hxu : x * (l * u * l⁻¹) * x⁻¹ = l * u * l⁻¹ := by
    rw [hxK _ hu₁]; group
  have h2 : (K.map (conjHom l)).map (conjHom x) = K.map (conjHom l) := by
    have := componentProduct_conj K (l * u * l⁻¹) x
    rwa [hxu, hcp, eq_comm] at this
  exact mem_normalizer_of_map_conjHom_eq (by rw [← hgen, Subgroup.map_sup, h1, h2])

theorem exists_mul_of_mem_centralizer [Finite H] {K L : Subgroup H} {u : H}
    (h35 : K = componentProduct K u) (hKL : K ≤ L) (hu2 : orderOf u = 2) (huK : u ∈ K)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l)
    (hZ : ∀ l ∈ L, (∀ k ∈ K, l * k = k * l) → l = 1 ∨ l = u)
    (hmax : ∀ M : Subgroup H, K ≤ M → M ≤ L → M = K ∨ M = L)
    (hstar : ∃ l ∈ L, l * u * l⁻¹ ∈ K ∧ l * u * l⁻¹ ≠ u) {x : H}
    (hx : x ∈ centralizer (K : Set H)) :
    ∃ c ∈ centralizer (L : Set H), x = c ∨ x = u * c := by
  obtain ⟨l, hl, hu₁K, hu₁ne⟩ := hstar
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have hne : K.map (conjHom l) ≠ K := by
    intro heq
    have hcomm : ∀ k ∈ K, k * (l * u * l⁻¹) = (l * u * l⁻¹) * k := by
      intro k hk
      have hk' := conj_inv_mem_of_map_eq heq hk
      have h1 := hKu _ hk'
      calc k * (l * u * l⁻¹) = l * ((l⁻¹ * k * l) * u) * l⁻¹ := by group
        _ = l * (u * (l⁻¹ * k * l)) * l⁻¹ := by rw [h1]
        _ = (l * u * l⁻¹) * k := by group
    have huL : l * u * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl (hKL huK)) (L.inv_mem hl)
    rcases hZ _ huL fun k hk => (hcomm k hk).symm with h | h
    · apply hu1
      have : u = l⁻¹ * (l * u * l⁻¹) * l := by group
      rw [this, h]; group
    · exact hu₁ne h
  have hle : K ⊔ K.map (conjHom l) ≤ L := by
    refine sup_le hKL ?_
    rintro _ ⟨k, hk, rfl⟩
    exact L.mul_mem (L.mul_mem hl (hKL hk)) (L.inv_mem hl)
  have hgen : K ⊔ K.map (conjHom l) = L := by
    rcases hmax _ le_sup_left hle with h | h
    · exfalso
      apply hne
      have hle2 : K.map (conjHom l) ≤ K :=
        calc K.map (conjHom l) ≤ K ⊔ K.map (conjHom l) := le_sup_right
          _ = K := h
      have hcard : Nat.card K = Nat.card (K.map (conjHom l)) :=
        (Subgroup.card_map_of_injective (conjHom_injective l)).symm
      exact Subgroup.eq_of_le_of_card_ge hle2 hcard.le
    · exact h
  have hxN := mem_normalizer_of_mem_centralizer h35 hu₁K hgen hx
  have hxLC : x ∈ L ⊔ centralizer (L : Set H) :=
    normalizer_le_sup_centralizer_of_mulAut_inner hinn hxN
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hxLC
  have hacom : ∀ k ∈ K, a * k = k * a := by
    intro k hk
    have h1 := mem_centralizer_iff.1 hx k hk
    have h2 := mem_centralizer_iff.1 hc k (hKL hk)
    have h3 : a * k * c = k * a * c := by
      calc a * k * c = a * (k * c) := by rw [mul_assoc]
        _ = a * (c * k) := by rw [h2]
        _ = a * c * k := by rw [mul_assoc]
        _ = k * (a * c) := h1.symm
        _ = k * a * c := by rw [mul_assoc]
    exact mul_right_cancel h3
  rcases hZ a ha hacom with h | h
  · exact ⟨c, hc, Or.inl (by rw [h, one_mul])⟩
  · exact ⟨c, hc, Or.inr (by rw [h])⟩

theorem eq_one_or_eq_of_mul_self_eq_one {K L N : Subgroup H} {u x : H} (hu2 : orderOf u = 2)
    (huL : u ∈ L) (huN : u ∈ N)
    (hC : ∀ y ∈ centralizer (K : Set H), ∃ c ∈ centralizer (L : Set H), y = c ∨ y = u * c)
    (hO : ∀ c ∈ centralizer (L : Set H), c ∈ N → c * c = 1 → c = 1)
    (hx : x ∈ centralizer (K : Set H)) (hxN : x ∈ N) (hxx : x * x = 1) : x = 1 ∨ x = u := by
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  obtain ⟨c, hc, h | h⟩ := hC x hx
  · exact Or.inl (h ▸ hO c hc (h ▸ hxN) (h ▸ hxx))
  · right
    have hcN : c ∈ N := by
      have : c = u⁻¹ * x := by rw [h]; group
      rw [this]
      exact N.mul_mem (N.inv_mem huN) hxN
    have hcu : u * c = c * u := mem_centralizer_iff.1 hc u huL
    have hcc : c * c = 1 := by
      calc c * c = (u * u) * (c * c) := by rw [huu, one_mul]
        _ = (u * c) * (u * c) := by
          calc (u * u) * (c * c) = u * (u * c) * c := by group
            _ = u * (c * u) * c := by rw [hcu]
            _ = (u * c) * (u * c) := by group
        _ = x * x := by rw [h]
        _ = 1 := hxx
    rw [h, hO c hc hcN hcc, mul_one]

theorem map_subtype_map_conj' {N : Subgroup H} (A : Subgroup ↥N) (g : ↥N) :
    (A.map (MulAut.conj g).toMonoidHom).map N.subtype =
      (A.map N.subtype).map (MulAut.conj (g : H)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_normalizer_subgroupOf {N K : Subgroup H} {g : ↥N}
    (hg : (g : H) ∈ normalizer (K : Set H)) :
    g ∈ normalizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro n
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact hg (n : H)

theorem stdBare_subgroupOf [Finite H] {N K : Subgroup H} (hKN : K ≤ N)
    (h1 : ∀ g ∈ N, ⁅K, K.map (conjHom g)⁆ ≠ ⊥)
    (h2 : ∀ g ∈ N, g ∉ normalizer (K : Set H) → ∀ x ∈ N, x ∈ centralizer (K : Set H) →
      g⁻¹ * x * g ∈ centralizer (K : Set H) → x * x = 1 → x = 1) :
    StdBare (K.subgroupOf N) := by
  refine ⟨fun g hbot => ?_, fun g hg => ?_⟩
  · apply h1 g g.2
    have h := congrArg (Subgroup.map N.subtype) hbot
    rw [Subgroup.map_commutator, Subgroup.map_bot, map_subtype_map_conj',
      Subgroup.map_subgroupOf_eq_of_le hKN] at h
    exact h
  · by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hodd
    have hxC := x.2.1
    obtain ⟨y, hyC, hyx⟩ := x.2.2
    have hcomm : ∀ z : ↥N, z ∈ centralizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) →
        (z : H) ∈ centralizer (K : Set H) := by
      intro z hz
      refine mem_centralizer_iff.2 fun k hk => ?_
      have := mem_centralizer_iff.1 hz ⟨k, hKN hk⟩ (by simpa [Subgroup.mem_subgroupOf] using hk)
      exact congrArg Subtype.val this
    have hxx : (x : H) * x = 1 := by
      have hxx0 : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
      exact congrArg (fun z => z.1.1) hxx0
    have hyH : (g : H)⁻¹ * (x : ↥N) * (g : H) = (y : H) := by
      have : (g : ↥N) * y * (g : ↥N)⁻¹ = x := hyx
      have h3 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      rw [← h3]; group
    have := h2 g g.2 (fun hn => hg (mem_normalizer_subgroupOf hn)) (x : H) (x : ↥N).2
      (hcomm _ hxC) (by rw [hyH]; exact hcomm _ hyC) hxx
    have hx1 : x = 1 := Subtype.ext (Subtype.ext this)
    rw [hx1, orderOf_one] at hx
    omega

theorem stdBare_subgroupOf_tail [Finite H] {N K L : Subgroup H} {u : H}
    (hKN : K ≤ N) (huK : u ∈ K) (hu2 : orderOf u = 2) (huL : u ∈ L)
    (hKp : Group.IsPerfect ↥K) (h35 : K = componentProduct K u)
    (hC : ∀ y ∈ centralizer (K : Set H), ∃ c ∈ centralizer (L : Set H), y = c ∨ y = u * c)
    (hO : ∀ c ∈ centralizer (L : Set H), c ∈ N → c * c = 1 → c = 1) :
    StdBare (K.subgroupOf N) := by
  have huN : u ∈ N := hKN huK
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  refine stdBare_subgroupOf hKN (fun g hgN hbot => ?_) (fun g hgN hg x hxN hxC hyC hxx => ?_)
  · have hle : K ≤ centralizer ((K.map (conjHom g) : Subgroup H) : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have hKgC : ∀ y ∈ K.map (conjHom g), y ∈ centralizer (K : Set H) := fun y hy =>
      mem_centralizer_iff.2 fun k hk => (mem_centralizer_iff.1 (hle hk) y hy).symm
    have hKgN : ∀ y ∈ K.map (conjHom g), y ∈ N := by
      rintro _ ⟨k, hk, rfl⟩
      exact N.mul_mem (N.mul_mem hgN (hKN hk)) (N.inv_mem hgN)
    have hCN : ∀ y ∈ centralizer (K : Set H), y ∈ N →
        ∃ c ∈ centralizer (L : Set H) ⊓ N, y = c ∨ y = u * c := by
      intro y hy hyN
      obtain ⟨c, hc, h | h⟩ := hC y hy
      · exact ⟨c, ⟨hc, h ▸ hyN⟩, Or.inl h⟩
      · refine ⟨c, ⟨hc, ?_⟩, Or.inr h⟩
        have : c = u⁻¹ * y := by rw [h]; group
        rw [this]
        exact N.mul_mem (N.inv_mem huN) hyN
    have hcomm : ⁅K.map (conjHom g), K.map (conjHom g)⁆ ≤ centralizer (L : Set H) ⊓ N := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact commutator_mem_of_cosets
        (fun c hc => mem_centralizer_iff.1 hc.1 u huL) (hCN x (hKgC x hx) (hKgN x hx))
        (hCN y (hKgC y hy) (hKgN y hy))
    have hperf : ⁅K.map (conjHom g), K.map (conjHom g)⁆ = K.map (conjHom g) := by
      rw [← Subgroup.map_commutator, commutator_eq_self_of_perfect hKp]
    have hmemKg : g * u * g⁻¹ ∈ K.map (conjHom g) := Subgroup.mem_map_of_mem (conjHom g) huK
    have hmem : g * u * g⁻¹ ∈ centralizer (L : Set H) ⊓ N := hcomm (by rw [hperf]; exact hmemKg)
    have hsq : g * u * g⁻¹ * (g * u * g⁻¹) = 1 := by
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [huu]; group
    have := hO _ hmem.1 hmem.2 hsq
    apply hu1
    have e : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [e, this]; group
  · rcases eq_one_or_eq_of_mul_self_eq_one hu2 huL huN hC hO hxC hxN hxx with h | h
    · exact h
    · exfalso
      subst h
      have hyN : g⁻¹ * x * g ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hgN) huN) hgN
      have hyy : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
        calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
          _ = 1 := by rw [huu]; group
      rcases eq_one_or_eq_of_mul_self_eq_one hu2 huL huN hC hO hyC hyN hyy with h1 | h1
      · apply hu1
        have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [e, h1]; group
      · apply hg
        have hgu : g * x = x * g := by
          calc g * x = g * (g⁻¹ * x * g) := by rw [h1]
            _ = x * g := by group
        exact mem_normalizer_of_map_conjHom_eq
          (map_conj_eq_of_hyp35 h35 (mem_centralizer_singleton_iff.2 hgu)).2

theorem solStd_subgroupOf_tail [Finite H] {N K L : Subgroup H} {u : H}
    (hKN : K ≤ N) (hKu : ∀ k ∈ K, k * u = u * k) (huK : u ∈ K) (hu2 : orderOf u = 2)
    (huL : u ∈ L) (hKq : CFSG.IsQuasisimple ↥K) (h35 : K = componentProduct K u)
    (hC : ∀ y ∈ centralizer (K : Set H), ∃ c ∈ centralizer (L : Set H), y = c ∨ y = u * c)
    (hO : ∀ c ∈ centralizer (L : Set H), c ∈ N → c * c = 1 → c = 1) :
    SolStd (K.subgroupOf N) := by
  have huN : u ∈ N := hKN huK
  refine ⟨stdBare_subgroupOf_tail hKN huK hu2 huL hKq.1 h35 hC hO, ⟨u, huN⟩,
    by rw [Subgroup.orderOf_mk]; exact hu2, ?_⟩
  have hKC : K ≤ centralizer ({u} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (hKu k hk)
  have hnorm : (K.subgroupOf (centralizer ({u} : Set H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).2 fun g hg =>
      mem_normalizer_of_map_conjHom_eq (map_conj_eq_of_hyp35 h35 hg).2
  have hcomp : IsCompIn K (centralizer ({u} : Set H)) := isCompIn_of_normal hKC hKq hnorm
  have hcomp2 := isCompIn_subgroupOf (isCompIn_of_le hcomp (le_inf hKC hKN) inf_le_left)
    (inf_le_right : centralizer ({u} : Set H) ⊓ N ≤ N)
  have hcen : (centralizer ({u} : Set H) ⊓ N).subgroupOf N =
      centralizer ({(⟨u, huN⟩ : ↥N)} : Set ↥N) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h, -⟩
      exact Subtype.ext h
    · intro h
      exact ⟨congrArg Subtype.val h, x.2⟩
  rwa [hcen] at hcomp2

end CFSG.EvenSporadicStandard.Induction.Fi.V3
