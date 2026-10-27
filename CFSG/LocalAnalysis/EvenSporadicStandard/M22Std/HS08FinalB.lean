module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Counting

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

namespace FinalData

variable {E N : Subgroup G} {t : G} {F1 F2 F3 : Finset G} (h : FinalData E N t F1 F2 F3)
include h

theorem false_of_card_27 (hF3 : ∀ x ∈ F3, x ∈ conjOrb N t)
    (hF2 : ∀ x ∈ F2, (x ∈ conjOrb N t ↔ t * x ∉ conjOrb N t))
    (hcard : (conjOrb N t).card = 27) (hX6 : (F2.filter (· ∈ conjOrb N t)).card = 6) :
    False := by
  set Ω := conjOrb N t with hΩ
  have htΩ : t ∈ Ω := self_mem_conjOrb N t
  obtain ⟨Y, hY⟩ : ∃ Y : Finset G, Y = F2.filter (· ∉ Ω) := ⟨_, rfl⟩
  have hYmem : ∀ y, y ∈ Y ↔ y ∈ F2 ∧ y ∉ Ω := fun y => by simp [hY]
  have hYcard : Y.card = 6 := by
    have := Finset.card_filter_add_card_filter_not (s := F2) (fun x => x ∈ Ω)
    rw [h.card2, hX6, ← hY] at this
    omega
  have hYt : ∀ y ∈ Y, t * y ∈ Ω := by
    intro y hy
    by_contra hc
    exact ((hYmem y).1 hy).2 ((hF2 y ((hYmem y).1 hy).1).2 hc)
  have hFE : ∀ x, (x ∈ F1 ∨ x ∈ F2 ∨ x ∈ F3) → x ∈ E ∧ x ≠ 1 ∧ x ≠ t := fun x hx =>
    (h.mem_F x).1 hx
  obtain ⟨y₀, hy₀⟩ : Y.Nonempty := Finset.card_pos.1 (by omega)
  have hy₀F2 : y₀ ∈ F2 := ((hYmem y₀).1 hy₀).1
  have hy₀Ω : y₀ ∉ Ω := ((hYmem y₀).1 hy₀).2
  set 𝒴 := conjOrb N y₀ with h𝒴
  have h𝒴Ω : ∀ x ∈ 𝒴, x ∉ Ω := by
    intro x hx hxΩ
    have e1 := conjOrb_eq_of_mem hx
    have e2 : conjOrb N x = conjOrb N t := conjOrb_eq_of_mem hxΩ
    apply hy₀Ω
    have : y₀ ∈ conjOrb N x := by rw [e1]; exact self_mem_conjOrb N y₀
    rwa [e2] at this
  have hY𝒴 : ∀ y ∈ Y, y ∈ 𝒴 := by
    intro y hy
    obtain ⟨n, hn, hnt, h1 | h1⟩ := h.trans2 y₀ hy₀F2 y ((hYmem y).1 hy).1
    · exact mem_conjOrb.2 ⟨n, hn, h1.symm⟩
    · exact absurd (hYt y hy) (h𝒴Ω _ (mem_conjOrb.2 ⟨n, hn, h1.symm⟩))
  have h𝒴sub : ∀ x ∈ 𝒴, x ∈ F1 ∨ x ∈ Y := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_conjOrb.1 hx
    obtain ⟨hE0, h10, ht0⟩ := hFE y₀ (Or.inr (Or.inl hy₀F2))
    have hxE : n * y₀ * n⁻¹ ∈ E := h.norm n hn y₀ hE0
    have hx1 : n * y₀ * n⁻¹ ≠ 1 := by
      intro h1
      apply h10
      calc y₀ = n⁻¹ * (n * y₀ * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    have hxt : n * y₀ * n⁻¹ ≠ t := fun h1 => h𝒴Ω _ hx (h1 ▸ htΩ)
    rcases (h.mem_F _).2 ⟨hxE, hx1, hxt⟩ with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr ((hYmem _).2 ⟨h1, h𝒴Ω _ hx⟩)
    · exact absurd (hF3 _ h1) (h𝒴Ω _ hx)
  obtain ⟨c, hc2, -, hcm⟩ := exists_pair_count N t h.t_sq F1 h.tmul1
    (Finset.card_pos.1 (by rw [h.card1]; norm_num)) h.trans1 𝒴
    (fun n hn _ x => conjOrb_invariant hn)
  rw [h.card1] at hcm
  have hdisj : Disjoint (F1.filter (· ∈ 𝒴)) Y := by
    rw [Finset.disjoint_left]
    intro x hx1 hxY
    exact (Finset.disjoint_left.1 h.disj12) (Finset.mem_filter.1 hx1).1
      ((hYmem x).1 hxY).1
  have h𝒴union : 𝒴 = F1.filter (· ∈ 𝒴) ∪ Y := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases h𝒴sub x hx with h1 | h1
      · exact Or.inl ⟨h1, hx⟩
      · exact Or.inr h1
    · rintro (⟨-, hx⟩ | hx)
      · exact hx
      · exact hY𝒴 x hx
  have hcard𝒴 : 𝒴.card = (F1.filter (· ∈ 𝒴)).card + 6 := by
    have := Finset.card_union_of_disjoint hdisj
    rw [← h𝒴union, hYcard] at this
    exact this
  have hdvd : 𝒴.card ∣ Nat.card N := by
    have := card_conjOrb_mul N y₀
    exact Dvd.intro _ this
  have hNcard : Nat.card N = 27 * 7680 := by rw [h.card_N, hcard]
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  ·
    subst hc0
    have hm0 : (F1.filter (· ∈ 𝒴)).card = 0 := by omega
    rw [Finset.card_eq_zero] at hm0
    have h𝒴Y : 𝒴 = Y := by rw [h𝒴union, hm0, Finset.empty_union]
    have hYinv : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
      intro n hn y hy
      have : n * y * n⁻¹ ∈ 𝒴 := conj_mem_conjOrb hn (hY𝒴 y hy)
      rwa [h𝒴Y] at this
    refine false_of_double_count Ω Y (fun x hx => h.sq x (h.mem_E_of_mem_conjOrb hx)) ?_ hcard
      hYcard ?_
    · intro y hy
      obtain ⟨hyE, hy1, -⟩ := hFE y (Or.inr (Or.inl ((hYmem y).1 hy).1))
      exact ⟨h.sq y hyE, hy1⟩
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := mem_conjOrb.1 hx
      have hW : (Ω.filter fun w => n * t * n⁻¹ * w ∈ Y) =
          (F2.filter (· ∈ Ω)).image (fun w' => n * w' * n⁻¹) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hwΩ, hwY⟩
          have hw' : n⁻¹ * w * n ∈ Ω := by
            have := (conjOrb_invariant (N := N) (x := t) (y := w) (N.inv_mem hn)).1 hwΩ
            simpa using this
          have h1 : t * (n⁻¹ * w * n) ∈ Y := by
            have := hYinv n⁻¹ (N.inv_mem hn) _ hwY
            rwa [show n⁻¹ * (n * t * n⁻¹ * w) * n⁻¹⁻¹ = t * (n⁻¹ * w * n) by group] at this
          have h2 : t * (n⁻¹ * w * n) ∈ F2 := ((hYmem _).1 h1).1
          have h3 : n⁻¹ * w * n ∈ F2 := by
            have := h.tmul2 _ h2
            rwa [← mul_assoc, h.t_sq, one_mul] at this
          exact ⟨n⁻¹ * w * n, ⟨h3, hw'⟩, by group⟩
        · rintro ⟨w', ⟨hw'F2, hw'Ω⟩, rfl⟩
          refine ⟨conj_mem_conjOrb hn hw'Ω, ?_⟩
          have h1 : t * w' ∈ Y := (hYmem _).2 ⟨h.tmul2 _ hw'F2, (hF2 w' hw'F2).1 hw'Ω⟩
          have := hYinv n hn _ h1
          rwa [show n * (t * w') * n⁻¹ = n * t * n⁻¹ * (n * w' * n⁻¹) by group] at this
      rw [hW, Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), hX6]
  ·
    have hm : (F1.filter (· ∈ 𝒴)).card = 15 * c := by omega
    obtain ⟨x, hx⟩ : (F1.filter (· ∈ 𝒴)).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨hxF1, hx𝒴⟩ := Finset.mem_filter.1 hx
    obtain ⟨z, hz1, hoz, hotz⟩ := h.odd1
    obtain ⟨n, hn, -, h1 | h1⟩ := h.trans1 x hxF1 z hz1
    · have hz𝒴 : z ∈ 𝒴 := h1 ▸ conj_mem_conjOrb hn hx𝒴
      have : conjOrb N z = 𝒴 := conjOrb_eq_of_mem hz𝒴
      rw [this] at hoz
      obtain ⟨k, hk⟩ := hoz
      have hc1 : c = 1 := by omega
      subst hc1
      have h21 : 𝒴.card = 21 := by omega
      rw [h21, hNcard] at hdvd
      omega
    · have hz𝒴 : t * z ∈ 𝒴 := h1 ▸ conj_mem_conjOrb hn hx𝒴
      have : conjOrb N (t * z) = 𝒴 := conjOrb_eq_of_mem hz𝒴
      rw [this] at hotz
      obtain ⟨k, hk⟩ := hotz
      have hc1 : c = 1 := by omega
      subst hc1
      have h21 : 𝒴.card = 21 := by omega
      rw [h21, hNcard] at hdvd
      omega

theorem false_of_card_7 (hF2 : ∀ x ∈ F2, (x ∈ conjOrb N t ↔ t * x ∉ conjOrb N t))
    (hcard : (conjOrb N t).card = 7) : False := by
  set Ω := conjOrb N t with hΩ
  let φ : N →* Equiv.Perm Ω :=
    { toFun := fun n => Equiv.subtypeEquiv (MulAut.conj (n : G)).toEquiv
        (fun x => conjOrb_invariant n.2)
      map_one' := by
        ext x
        simp
      map_mul' := fun n m => by
        ext x
        simp [mul_assoc] }
  have hφ : ∀ (n : N) (x : Ω), ((φ n x : Ω) : G) = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have hker : ∀ n : N, n ∈ φ.ker ↔ (n : G) ∈ E := by
    intro n
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : ∀ x ∈ Ω, (n : G) * x * (n : G)⁻¹ = x := fun x hx => by
        have := congrArg Subtype.val (Equiv.Perm.ext_iff.1 h1 ⟨x, hx⟩)
        simpa [hφ] using this
      have hnt : (n : G) * t * (n : G)⁻¹ = t := h2 t (self_mem_conjOrb N t)
      refine h.fix2 n n.2 ?_ ?_
      · calc (n : G) * t = (n : G) * t * (n : G)⁻¹ * n := by group
          _ = t * n := by rw [hnt]
      · intro x hx
        by_cases hxΩ : x ∈ Ω
        · exact h2 x hxΩ
        · have htx : t * x ∈ Ω := by
            by_contra hc
            exact hxΩ ((hF2 x hx).2 hc)
          have h3 := h2 _ htx
          have h4 : (n : G) * (t * x) * (n : G)⁻¹ =
              ((n : G) * t * (n : G)⁻¹) * ((n : G) * x * (n : G)⁻¹) := by
            group
          rw [h4, hnt] at h3
          exact mul_left_cancel h3
    · intro hn
      ext x
      have hxE : (x : G) ∈ E := h.mem_E_of_mem_conjOrb x.2
      have := h.comm _ hn _ hxE
      simp only [Equiv.Perm.coe_one, id_eq]
      rw [hφ]
      calc (n : G) * x * (n : G)⁻¹ = (x : G) * n * (n : G)⁻¹ := by rw [this]
        _ = x := by group
  have hkercard : Nat.card φ.ker = 64 := by
    have : φ.ker = E.subgroupOf N := by
      ext n
      rw [hker, Subgroup.mem_subgroupOf]
    rw [this, ← h.card_E]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv
  have hrange : Nat.card φ.range * Nat.card φ.ker = Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hNc : Nat.card N = 7 * 7680 := by rw [h.card_N, hcard]
  have hΩc : Nat.card Ω = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
  refine no_subgroup_card_840 hΩc φ.range ?_
  rw [hkercard, hNc] at hrange
  omega

theorem «false» : False := by
  set Ω := conjOrb N t with hΩ
  have htΩ : t ∈ Ω := self_mem_conjOrb N t
  have hF2ne : F2.Nonempty := Finset.card_pos.1 (by rw [h.card2]; norm_num)
  have hF3ne : F3.Nonempty := Finset.card_pos.1 (by rw [h.card3]; norm_num)
  obtain ⟨a, ha2, hpair2, hcnt2⟩ := exists_pair_count N t h.t_sq F2 h.tmul2 hF2ne h.trans2 Ω
    (fun n hn _ x => conjOrb_invariant hn)
  obtain ⟨b, hb2, hpair3, hcnt3⟩ := exists_pair_count N t h.t_sq F3 h.tmul3 hF3ne h.trans3 Ω
    (fun n hn _ x => conjOrb_invariant hn)
  rw [h.card2] at hcnt2
  rw [h.card3] at hcnt3
  have hF2t : ∀ x ∈ F2, x ≠ t := fun x hx => ((h.mem_F x).1 (Or.inr (Or.inl hx))).2.2
  have hF3t : ∀ x ∈ F3, x ≠ t := fun x hx => ((h.mem_F x).1 (Or.inr (Or.inr hx))).2.2
  have hΩeq : Ω = insert t (F2.filter (· ∈ Ω) ∪ F3.filter (· ∈ Ω)) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases h.conjOrb_subset hx with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h1, hx⟩)
      · exact Or.inr (Or.inr ⟨h1, hx⟩)
    · rintro (rfl | ⟨-, hx⟩ | ⟨-, hx⟩)
      · exact htΩ
      · exact hx
      · exact hx
  have hdisj : Disjoint (F2.filter (· ∈ Ω)) (F3.filter (· ∈ Ω)) :=
    Finset.disjoint_filter_filter h.disj23
  have htnot : t ∉ F2.filter (· ∈ Ω) ∪ F3.filter (· ∈ Ω) := by
    simp only [Finset.mem_union, Finset.mem_filter, not_or]
    exact ⟨fun h1 => hF2t t h1.1 rfl, fun h1 => hF3t t h1.1 rfl⟩
  have hcardΩ : Ω.card = 1 + (F2.filter (· ∈ Ω)).card + (F3.filter (· ∈ Ω)).card := by
    conv_lhs => rw [hΩeq]
    rw [Finset.card_insert_of_notMem htnot, Finset.card_union_of_disjoint hdisj]
    ring
  obtain ⟨n₁, hn₁, hne⟩ := h.nonfixed
  have hΩ2 : 2 ≤ Ω.card := by
    have h1 : n₁ * t * n₁⁻¹ ∈ Ω := mem_conjOrb.2 ⟨n₁, hn₁, rfl⟩
    have h2 : ({t, n₁ * t * n₁⁻¹} : Finset G) ⊆ Ω := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact htΩ
      · exact h1
    have h3 := Finset.card_le_card h2
    rwa [Finset.card_pair (Ne.symm hne)] at h3
  have hdvdN : Ω.card ∣ Nat.card N := by rw [h.card_N]; exact Dvd.intro _ rfl
  have hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → (∀ j < 6, ¬ 64 ≡ 2 ^ j [MOD p]) → p ∣ Ω.card → False :=
    fun p hp hp2 hmod hd =>
      false_of_prime_dvd E N h.card_E h.norm h.cent hp hp2 hmod (hd.trans hdvdN)
  have hΩcard : Ω.card = 1 + 6 * a + 10 * b := by omega
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · omega
  ·
    exact hprime 11 Nat.prime_eleven (by norm_num) (by decide) (by rw [hΩcard])
  ·
    refine h.false_of_card_21 (fun x hx => (pair0 (hpair2 x hx)).1)
      (fun x hx => (pair2 (hpair3 x hx)).1) (by omega)
  ·
    exact h.false_of_card_7 (fun x hx => pair1 (hpair2 x hx)) (by omega)
  ·
    exact hprime 17 (by norm_num) (by norm_num) (by decide) (by rw [hΩcard])
  ·
    have hX6 : (F2.filter (· ∈ Ω)).card = 6 := by omega
    exact h.false_of_card_27 (fun x hx => (pair2 (hpair3 x hx)).1)
      (fun x hx => pair1 (hpair2 x hx)) (by omega) hX6
  ·
    exact hprime 13 (by norm_num) (by norm_num) (by decide) (by rw [hΩcard])
  ·
    exact hprime 23 (by norm_num) (by norm_num) (by decide) (by rw [hΩcard])
  ·
    exact hprime 11 Nat.prime_eleven (by norm_num) (by decide) (by rw [hΩcard]; norm_num)

end FinalData

end CFSG.EvenSporadicStandard.M22Std
