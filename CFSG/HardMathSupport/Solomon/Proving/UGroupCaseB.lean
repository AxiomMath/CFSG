module

public import CFSG.HardMathSupport.Solomon.Proving.UGroupExists

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G]

theorem card_pow_two_pow_eq_one_le {A : Type} [CommGroup A] [Fintype A] [DecidableEq A] {z : A}
    (hz : ∀ x : A, x ^ 2 = 1 → x = 1 ∨ x = z) (j : ℕ) :
    (Finset.univ.filter (fun x : A => x ^ (2 ^ j) = 1)).card ≤ 2 ^ j := by
  classical
  induction j with
  | zero =>
    rw [pow_zero, Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_one] at ha hb
    rw [ha, hb]
  | succ j ih =>
    set S := Finset.univ.filter (fun x : A => x ^ (2 ^ (j + 1)) = 1) with hS
    set T := Finset.univ.filter (fun x : A => x ^ (2 ^ j) = 1) with hT
    have himg : S.image (fun x : A => x ^ 2) ⊆ T := by
      intro b hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
      simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← pow_mul, ← pow_succ']
      exact hx
    have hfib : ∀ b ∈ S.image (fun x : A => x ^ 2),
        (S.filter (fun x : A => x ^ 2 = b)).card ≤ 2 := by
      intro b hb
      obtain ⟨x₀, -, hx₀⟩ := Finset.mem_image.1 hb
      have hsub : S.filter (fun x : A => x ^ 2 = b) ⊆ {x₀, z * x₀} := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have hy : (x * x₀⁻¹) ^ 2 = 1 := by
          rw [mul_pow, inv_pow, hx.2, hx₀, mul_inv_cancel]
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hz _ hy with h | h
        · exact Or.inl (mul_inv_eq_one.1 h)
        · exact Or.inr (mul_inv_eq_iff_eq_mul.1 h)
      calc (S.filter (fun x : A => x ^ 2 = b)).card ≤ ({x₀, z * x₀} : Finset A).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have hS2 : S.card ≤ 2 * T.card := by
      calc S.card ≤ 2 * (S.image (fun x : A => x ^ 2)).card :=
            Finset.card_le_mul_card_image S 2 hfib
        _ ≤ 2 * T.card := Nat.mul_le_mul_left 2 (Finset.card_le_card himg)
    calc S.card ≤ 2 * T.card := hS2
      _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (j + 1) := by rw [pow_succ, mul_comm]

theorem isCyclic_of_unique_involution {A : Type} [CommGroup A] [Finite A] [DecidableEq A] {z : A}
    (hA : IsPGroup 2 A) (hz : ∀ x : A, x ^ 2 = 1 → x = 1 ∨ x = z) : IsCyclic A := by
  classical
  have := Fintype.ofFinite A
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hA
  rcases n with _ | m
  · exact isCyclic_of_orderOf_eq_card (1 : A) (by rw [orderOf_one, hn, pow_zero])
  · have hcount := card_pow_two_pow_eq_one_le hz m
    have hex : ∃ x : A, x ^ (2 ^ m) ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hall : Finset.univ.filter (fun x : A => x ^ (2 ^ m) = 1) = Finset.univ := by
        ext x
        simp [hcon x]
      rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, hn, pow_succ] at hcount
      have : 0 < 2 ^ m := by positivity
      omega
    obtain ⟨x, hx⟩ := hex
    have hx2 : x ^ (2 ^ (m + 1)) = 1 := by
      have h := pow_card_eq_one (G := A) (x := x)
      rw [← Nat.card_eq_fintype_card, hn] at h
      exact h
    have hord : orderOf x = 2 ^ (m + 1) := orderOf_eq_prime_pow hx hx2
    exact isCyclic_of_orderOf_eq_card x (by rw [hord, hn])

theorem mem_of_centralizes_maxNormalAbelian [Finite G] {T A : Subgroup G} (hT : IsPGroup 2 T)
    (hAT : A ≤ T) (hAn : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ B : Subgroup G, B ≤ T → (∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B) →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → A ≤ B → B ≤ A)
    {c : G} (hcT : c ∈ T) (hc : ∀ a ∈ A, c * a = a * c) : c ∈ A := by
  by_contra hcA
  let A' : Subgroup T := A.subgroupOf T
  have hA'mem : ∀ x : T, x ∈ A' ↔ (x : G) ∈ A := fun x => Subgroup.mem_subgroupOf
  have hA'n : A'.Normal := ⟨fun n hn g => by
    rw [hA'mem] at hn ⊢
    have := hAn (g : G) g.2 n hn
    simpa using this⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  let C : Subgroup T := Subgroup.centralizer (A' : Set T)
  have hCn : C.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro h hh
    have hh' : g⁻¹ * h * g⁻¹⁻¹ ∈ A' := hA'n.conj_mem h hh g⁻¹
    have hn' := hn _ hh'
    have e : h = g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ := by group
    rw [e]
    calc g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ * (g * n * g⁻¹)
        = g * ((g⁻¹ * h * g⁻¹⁻¹) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * h * g⁻¹⁻¹)) * g⁻¹ := by rw [hn']
      _ = g * n * g⁻¹ * (g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹) := by group⟩
  let N : Subgroup (T ⧸ A') := C.map (QuotientGroup.mk' A')
  have hNn : N.Normal := Subgroup.Normal.map hCn (QuotientGroup.mk' A')
    (QuotientGroup.mk'_surjective A')
  let c' : T := ⟨c, hcT⟩
  have hc'C : c' ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (hc (h : G) ((hA'mem h).1 hh)).symm
  have hN1 : N ≠ ⊥ := by
    intro h
    have hmem : (c' : T ⧸ A') ∈ N := Subgroup.mem_map.2 ⟨c', hc'C, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hA'mem] at hmem
    exact hcA hmem
  have hbot := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
  obtain ⟨y, hy1, hy2⟩ : ∃ y ∈ N ⊓ Subgroup.center (T ⧸ A'), y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot (eq_bot_iff.2 fun y hy => by
      rw [Subgroup.mem_bot]
      exact hcon y hy)
  obtain ⟨c'', hc''C, rfl⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hy1).1
  have hcen := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hy1).2
  have hc''A : c'' ∉ A' := fun h => hy2 (QuotientGroup.eq_one_iff c'' |>.2 h)
  have hkey : ∀ t : T, (t * c'')⁻¹ * (c'' * t) ∈ A' := by
    intro t
    have h1 := hcen (QuotientGroup.mk' A' t)
    rw [← map_mul, ← map_mul] at h1
    have h2 : ((t * c'' : T) : T ⧸ A') = ((c'' * t : T) : T ⧸ A') := h1
    rw [QuotientGroup.eq] at h2
    exact h2
  let S : Set G := (A : Set G) ∪ {(c'' : G)}
  let B : Subgroup G := Subgroup.closure S
  have hcomm : ∀ a ∈ A, (c'' : G) * a = a * (c'' : G) := by
    intro a ha
    have hh : (⟨a, hAT ha⟩ : T) ∈ A' := (hA'mem _).2 ha
    have h1 := Subgroup.mem_centralizer_iff.1 hc''C _ hh
    exact (congrArg Subtype.val h1).symm
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hAab x hx y hy
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact (hcomm x hx).symm
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hcomm y hy
    · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; rfl
  have hBT : B ≤ T := by
    refine (Subgroup.closure_le _).2 ?_
    intro s hs
    rcases hs with hs | hs
    · exact hAT hs
    · rw [Set.mem_singleton_iff] at hs; rw [hs]; exact c''.2
  have hgen : ∀ t ∈ T, ∀ s ∈ S, t * s * t⁻¹ ∈ B := by
    intro t ht s hs
    rcases hs with hs | hs
    · exact Subgroup.subset_closure (Or.inl (hAn t ht s hs))
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      have h1 := (hA'mem _).1 (hkey ⟨t, ht⟩⁻¹)
      have e : ((((⟨t, ht⟩ : T)⁻¹ * c'')⁻¹ * (c'' * (⟨t, ht⟩ : T)⁻¹) : T) : G) =
          (c'' : G)⁻¹ * t * ((c'' : G) * t⁻¹) := by
        simp [mul_assoc]
      rw [e] at h1
      have e2 : t * (c'' : G) * t⁻¹ = (c'' : G) * ((c'' : G)⁻¹ * (t : G) * ((c'' : G) * (t : G)⁻¹)) := by
        group
      rw [e2]
      exact B.mul_mem (Subgroup.subset_closure (Or.inr rfl)) (Subgroup.subset_closure (Or.inl h1))
  have hBnorm : ∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B := by
    intro t ht x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact hgen t ht s hs
    | one => simp [B.one_mem]
    | mul x y _ _ hx hy =>
      rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) by group]
      exact B.mul_mem hx hy
    | inv x _ hx =>
      rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group]
      exact B.inv_mem hx
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    have hSB : B ≤ Subgroup.centralizer S := by
      refine (Subgroup.closure_le _).2 ?_
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      exact hSc h hh s hs
    intro a ha b hb
    have hcc := Subgroup.closure_le_centralizer_centralizer S ha
    exact ((Subgroup.mem_centralizer_iff.1 hcc) b (hSB hb)).symm
  have hAB : A ≤ B := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hBA := hmax B (by exact hBT) hBnorm hBab hAB
  have hc''B : (c'' : G) ∈ B := Subgroup.subset_closure (Or.inr rfl)
  exact hc''A ((hA'mem c'').2 (hBA hc''B))

theorem exists_maximal_normal_abelian [Finite G] {T : Subgroup G} {z : G} (hzT : z ∈ T)
    (hzc : ∀ t ∈ T, t * z = z * t) :
    ∃ A : Subgroup G, A ≤ T ∧ z ∈ A ∧ (∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ B : Subgroup G, B ≤ T → (∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B) →
        (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → A ≤ B → B ≤ A) := by
  classical
  let P : Subgroup G → Prop := fun B => B ≤ T ∧ (∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B) ∧
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ z ∈ B
  have hz0 : Commute z z := Commute.refl z
  let A0 : Subgroup G := Subgroup.zpowers z
  have hA0 : P A0 := by
    refine ⟨?_, ?_, ?_, Subgroup.mem_zpowers z⟩
    · exact (Subgroup.zpowers_le).2 hzT
    · intro t ht b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have hc : Commute t z := hzc t ht
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
    · intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (hz0.zpow_zpow k m).eq
  have : Nonempty {B : Subgroup G // P B} := ⟨⟨A0, hA0⟩⟩
  obtain ⟨⟨A, hA⟩, hmaxA⟩ :=
    Finite.exists_max (fun B : {B : Subgroup G // P B} => Nat.card B.1)
  refine ⟨A, hA.1, hA.2.2.2, hA.2.1, hA.2.2.1, ?_⟩
  intro B hBT hBn hBab hAB
  have hPB : P B := ⟨hBT, hBn, hBab, hAB hA.2.2.2⟩
  have hcard : Nat.card B ≤ Nat.card A := hmaxA ⟨B, hPB⟩
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hAB hcard).symm

end CFSG.HardMathSupport.Solomon.Proving

end
