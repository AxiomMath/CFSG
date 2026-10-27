module

public import CFSG.LargeExtraspecial.AS35DHDefs
public import CFSG.LargeExtraspecial.AS35DMinNormal
public import CFSG.LargeExtraspecial.AS35DQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace S14

@[expose] def AschbacherTwoTwoStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N U P : Subgroup G) (z : G),
    U ≤ N → P ≤ N → (∀ u ∈ U, ∀ n ∈ N, u * n = n * u) → (∀ u ∈ U, u * u = 1) →
    U ⊓ P = ⊥ → IsExtraspecialPGroup 2 P → z ∈ P →
    (∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = z) →
    (∀ c ∈ N, c * z = z * c → ∀ q ∈ U ⊔ P, c * q * c⁻¹ ∈ U ⊔ P) →
    (∃ T : Sylow 2 N, ∀ t ∈ (T : Subgroup N), (t : G) * z = z * t) →
    z ∈ (CFSG.pCore 2 N).map N.subtype → ¬ N ≤ centralizer ({z} : Set G) →
    (∀ H : Subgroup G, U ⊔ P ≤ H → H ≤ N → H ≠ N → H ≤ centralizer ({z} : Set G)) →
    N ≤ closure {x | ∃ n ∈ N, ∃ q ∈ U ⊔ P, n * q * n⁻¹ = x} →
      IsSThreeAt z N ∨ IsAFiveAt z N

end S14

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] def IsSThree (N : Subgroup G) : Prop :=
  IsSThreeAt S.z N ∧ Asc77.centerIn S.z N = ⊥ ∧ closure (S.zConj N) ≤ S.QG

@[expose] def IsAFive (N : Subgroup G) : Prop :=
  IsAFiveAt S.z N ∧ Asc77.centerIn S.z N = ⊥

omit [Finite G] in
theorem even_card_of_isPGroup {X : Subgroup G} [Finite X] (hX : IsPGroup 2 X) (h : X ≠ ⊥) :
    Even (Nat.card X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact h (Subgroup.eq_bot_of_card_eq X hk)
  rw [hk]
  exact (Nat.even_pow' hk0).mpr even_two

omit [Finite G] in
theorem pCore_ne_bot_of {H X : Subgroup G} (hXH : X ≤ H)
    (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hX2 : IsPGroup 2 X) (hX1 : X ≠ ⊥) :
    CFSG.pCore 2 H ≠ ⊥ := by
  intro h0
  apply hX1
  have hle : X.subgroupOf H ≤ CFSG.pCore 2 H :=
    le_sSup ⟨⟨fun n hn k => by
      rw [mem_subgroupOf] at hn ⊢
      exact hXn k k.2 n hn⟩, hX2.comap_of_injective H.subtype H.subtype_injective⟩
  rw [h0] at hle
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H := by rw [mem_subgroupOf]; exact hx
  have h1 := hle this
  rw [mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem isExtraspecialPGroup_QG : IsExtraspecialPGroup 2 S.QG :=
  isExtraspecialPGroup_of_mulEquiv (S.Q.equivMapOfInjective S.M.subtype S.M.subtype_injective)
    S.extraspecial

theorem fourEight (h22 : S14.AschbacherTwoTwoStmt) {N : Subgroup G} (hN : S.IsHStar N) :
    S.IsSThree N ∨ S.IsAFive N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hQN, hO2N, hNM⟩, hmin⟩ := hN
  set O := (CFSG.pCore 2 N).map N.subtype with hOdef
  have hOn : ∀ n ∈ N, ∀ x ∈ O, n * x * n⁻¹ ∈ O := by
    rintro n hn _ ⟨x, hx, rfl⟩
    exact ⟨⟨n, hn⟩ * x * ⟨n, hn⟩⁻¹, CFSG.pCore_normal.conj_mem x hx _, rfl⟩
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup.map _
  have hO1 : O ≠ ⊥ := fun h => hO2N ((map_eq_bot_iff_of_injective _ N.subtype_injective).mp h)
  have hON : O ≤ N := map_subtype_le _
  have hzO : S.z ∈ O :=
    S.z_mem_of_normalized (fun q hq x hx => hOn q (hQN hq) x hx) (even_card_of_isPGroup hO2 hO1)
  have hzN : S.z ∈ N := hON hzO
  have hmax : ∀ H : Subgroup G, S.QG ≤ H → H ≤ N → H ≠ N → H ≤ S.M := by
    intro H hQH hHN hne
    by_contra hHM
    have hset : S.IsHSet H := by
      refine ⟨hQH, pCore_ne_bot_of (X := O ⊓ H) inf_le_right ?_ (hO2.to_le inf_le_left) ?_, hHM⟩
      · intro h hh x hx
        exact mem_inf.mpr ⟨hOn h (hHN hh) x (mem_inf.mp hx).1,
          H.mul_mem (H.mul_mem hh (mem_inf.mp hx).2) (H.inv_mem hh)⟩
      · intro h0
        have : S.z ∈ O ⊓ H := mem_inf.mpr ⟨hzO, hQH S.z_mem_QG⟩
        rw [h0, mem_bot] at this
        exact S.z_ne_one this
    exact hne (hmin H hset hHN)
  have hgen : N ≤ closure {x | ∃ n ∈ N, ∃ q ∈ ⊥ ⊔ S.QG, n * q * n⁻¹ = x} := by
    set R := closure {x | ∃ n ∈ N, ∃ q ∈ ⊥ ⊔ S.QG, n * q * n⁻¹ = x} with hR
    have hRN : R ≤ N := by
      rw [hR, closure_le]
      rintro _ ⟨n, hn, q, hq, rfl⟩
      rw [bot_sup_eq] at hq
      exact N.mul_mem (N.mul_mem hn (hQN hq)) (N.inv_mem hn)
    have hQR : S.QG ≤ R := fun q hq => subset_closure ⟨1, N.one_mem, q, by
      rw [bot_sup_eq]; exact hq, by group⟩
    by_contra hNR
    have hRM := hmax R hQR hRN (fun h => hNR (h ▸ le_refl _))
    apply hNM
    intro n hn
    have hc : ∀ q ∈ S.QG, q * (n⁻¹ * S.z * n) = (n⁻¹ * S.z * n) * q := by
      intro q hq
      have h1 : n * q * n⁻¹ ∈ S.M := hRM (subset_closure ⟨n, hn, q, by
        rw [bot_sup_eq]; exact hq, rfl⟩)
      have h2 := S.mem_M_iff.mp h1
      calc q * (n⁻¹ * S.z * n) = n⁻¹ * ((n * q * n⁻¹) * S.z) * n := by group
        _ = n⁻¹ * (S.z * (n * q * n⁻¹)) * n := by rw [h2]
        _ = (n⁻¹ * S.z * n) * q := by group
    have h1 : n⁻¹ * S.z * n ≠ 1 := by
      intro h
      apply S.z_ne_one
      calc S.z = n * (n⁻¹ * S.z * n) * n⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h3 := S.eq_z_of_commute_QG hc h1
    rw [S.mem_M_iff]
    calc n * S.z = n * (n⁻¹ * S.z * n) := by rw [h3]
      _ = S.z * n := by group
  have hsyl : ∃ T : Sylow 2 N, ∀ t ∈ (T : Subgroup N), (t : G) * S.z = S.z * t := by
    have hQ2 : IsPGroup 2 (S.QG.subgroupOf N) :=
      S.isPGroup_QG.comap_of_injective N.subtype N.subtype_injective
    obtain ⟨T, hT⟩ := hQ2.exists_le_sylow
    refine ⟨T, fun t ht => ?_⟩
    have hle : ((T : Subgroup N).map N.subtype) ≤ S.M := by
      refine S.le_M_of_isPGroup (T.isPGroup'.map _) fun q hq => ?_
      exact ⟨⟨q, hQN hq⟩, hT (by rw [mem_subgroupOf]; exact hq), rfl⟩
    exact S.mem_M_iff.mp (hle ⟨t, ht, rfl⟩)
  have h := h22 G N ⊥ S.QG S.z bot_le hQN (fun u hu _ _ => by
      rw [mem_bot] at hu; rw [hu]; group)
    (fun u hu => by rw [mem_bot] at hu; rw [hu, mul_one]) (bot_inf_eq _) S.isExtraspecialPGroup_QG
    S.z_mem_QG (fun x hx hc => S.eq_one_or_z_of_commute hx fun y hy => hc y hy)
    (fun c _ hcz q hq => by
      rw [bot_sup_eq] at hq ⊢
      exact S.conj_mem_QG (S.mem_M_iff.mpr hcz) hq)
    hsyl hzO hNM (fun H hQH hHN hne => hmax H (by rwa [bot_sup_eq] at hQH) hHN hne) hgen
  have hC : Asc77.centerIn S.z N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨-, hxc⟩ := mem_inf.mp hx
    have hxQ : ∀ q ∈ S.QG, q * x = x * q := fun q hq => mem_centralizer_iff.mp hxc q (hQN hq)
    rw [mem_bot]
    by_contra hx1
    have hxz := S.eq_z_of_commute_QG hxQ hx1
    apply hNM
    intro n hn
    have := mem_centralizer_iff.mp hxc n hn
    rw [hxz] at this
    exact S.mem_M_iff.mpr this
  rcases h with h | h
  · left
    refine ⟨h, hC, ?_⟩
    obtain ⟨hcard, -, -, -⟩ := h
    set Ω := S.zConj N with hΩ
    have hzΩ : S.z ∈ Ω := self_mem_conjIn _ _
    rw [closure_le]
    intro v hv
    by_cases hvz : v = S.z
    · rw [hvz]
      exact S.z_mem_QG
    have hfin : Ω.Finite := Set.toFinite _
    have hsub : ({S.z, v} : Set G) ⊆ Ω := by
      rintro x (rfl | rfl)
      · exact hzΩ
      · exact hv
    have hdiff : (Ω \ {S.z, v}).ncard = 1 := by
      rw [Set.ncard_sdiff hsub, hcard, Set.ncard_pair (Ne.symm hvz)]
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hdiff
    have hwΩ : w ∈ Ω := (hw ▸ Set.mem_singleton w : w ∈ Ω \ {S.z, v}).1
    have hwzv : w ≠ S.z ∧ w ≠ v := by
      have := (hw ▸ Set.mem_singleton w : w ∈ Ω \ {S.z, v}).2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
      exact this
    have hmemΩ : ∀ x ∈ Ω, x = S.z ∨ x = v ∨ x = w := by
      intro x hx
      by_cases hxz : x = S.z
      · exact Or.inl hxz
      by_cases hxv : x = v
      · exact Or.inr (Or.inl hxv)
      have : x ∈ Ω \ {S.z, v} := ⟨hx, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hxz, hxv⟩⟩
      rw [hw] at this
      exact Or.inr (Or.inr this)
    have hperm : ∀ q ∈ S.QG, ∀ x ∈ Ω, x ≠ S.z → q * x * q⁻¹ = v ∨ q * x * q⁻¹ = w := by
      intro q hq x hx hxz
      rcases hmemΩ _ (conj_mem_conjIn_of_mem (hQN hq) hx) with h1 | h1 | h1
      · exfalso
        apply hxz
        have hqz : q⁻¹ * S.z * q = S.z := by
          rw [mul_assoc, ← S.z_comm_QG hq]
          group
        calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
          _ = S.z := by rw [h1, hqz]
      · exact Or.inl h1
      · exact Or.inr h1
    have hvC : v * v = 1 := by
      obtain ⟨n, -, rfl⟩ := hv
      rw [show n * S.z * n⁻¹ * (n * S.z * n⁻¹) = n * (S.z * S.z) * n⁻¹ by group, S.z_mul_z]
      group
    set F := S.QG ⊓ centralizer ({v} : Set G) with hF
    have hmemF : ∀ x, x ∈ F ↔ x ∈ S.QG ∧ x * v * x⁻¹ = v := by
      intro x
      rw [hF, mem_inf, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]; group⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        calc x * v = x * v * x⁻¹ * x := by group
          _ = v * x := by rw [h2]
    obtain ⟨q₀, hq₀, hq₀v⟩ : ∃ q ∈ S.QG, q * v * q⁻¹ ≠ v := by
      by_contra! hall
      have hv1 : v ≠ 1 := by
        intro h1
        obtain ⟨n, -, hn⟩ := hv
        apply S.z_ne_one
        calc S.z = n⁻¹ * (n * S.z * n⁻¹) * n := by group
          _ = 1 := by rw [hn, h1]; group
      apply hvz
      refine S.eq_z_of_commute_QG (fun q hq => ?_) hv1
      calc q * v = q * v * q⁻¹ * q := by group
        _ = v * q := by rw [hall q hq]
    have hq₀w : q₀ * v * q₀⁻¹ = w := (hperm q₀ hq₀ v hv hvz).resolve_left hq₀v
    have hrel : F.relIndex S.QG = 2 := by
      rw [relIndex_eq_two_iff]
      refine ⟨q₀, hq₀, fun b hb => xor_iff_iff_not.mpr ?_⟩
      rw [hmemF, hmemF]
      have hbw := hperm b hb w hwΩ hwzv.1
      have hbv := hperm b hb v hv hvz
      have hconj : b * q₀ * v * (b * q₀)⁻¹ = b * w * b⁻¹ := by
        rw [← hq₀w]
        group
      have hinj : b * v * b⁻¹ ≠ b * w * b⁻¹ := by
        intro h1
        apply hwzv.2
        calc w = b⁻¹ * (b * w * b⁻¹) * b := by group
          _ = v := by rw [← h1]; group
      constructor
      · rintro ⟨-, h1⟩ ⟨-, h2⟩
        rw [hconj] at h1
        exact hinj (h2.trans h1.symm)
      · intro h1
        refine ⟨S.QG.mul_mem hb hq₀, ?_⟩
        rw [hconj]
        have hbv' : b * v * b⁻¹ = w := hbv.resolve_left fun h2 => h1 ⟨hb, h2⟩
        rcases hbw with h2 | h2
        · exact h2
        · exact absurd (hbv'.trans h2.symm) hinj
    exact S.mem_QG_of_sq_eq_one_of_commute inf_le_left hrel (by rw [pow_two]; exact hvC)
      fun f hf => ((mem_centralizer_singleton_iff.mp (mem_inf.mp hf).2)).symm
  · exact Or.inr ⟨h, hC⟩

end Setting

end CFSG.LargeExtraspecial
