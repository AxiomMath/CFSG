module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSplit

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup Equiv MulAction

section Perm

private theorem mul_comm_of_sq_eq_one {H : Type*} [Group H] (h : ∀ x : H, x ^ 2 = 1) (x y : H) :
    x * y = y * x := by
  have h1 : ∀ w : H, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h w)
  calc x * y = (x * y)⁻¹ := (h1 _).symm
    _ = y * x := by rw [mul_inv_rev, h1, h1]

private theorem le_div_two_of_two_pow (k : ℕ) : k ≤ 2 ^ k / 2 := by
  rcases k with _ | k
  · simp
  · have := @Nat.lt_two_pow_self k
    rw [pow_succ]
    omega

private theorem le_two_mul_div_four_of_two_pow {k : ℕ} (hk : k ≠ 1) : k ≤ 2 * (2 ^ k / 4) := by
  rcases k with _ | _ | k
  · simp
  · exact absurd rfl hk
  · have := @Nat.lt_two_pow_self k
    rw [pow_succ, pow_succ]
    omega

variable {α : Type*} [Fintype α]

private theorem sq_eq_one_coe {E : Subgroup (Perm α)} (hE : ∀ x ∈ E, x ^ 2 = 1) (x : E) :
    x ^ 2 = 1 :=
  Subtype.ext (by simpa using hE x x.2)

private theorem smul_eq_of_mem_stabilizer {E : Subgroup (Perm α)} (hE : ∀ x ∈ E, x ^ 2 = 1)
    {a : α} {x : E} (hx : x ∈ stabilizer E a) {b : α} (hb : b ∈ orbit E a) : x • b = b := by
  obtain ⟨y, rfl⟩ := mem_orbit_iff.1 hb
  rw [smul_smul, mul_comm_of_sq_eq_one (sq_eq_one_coe hE) x y, mul_smul,
    mem_stabilizer_iff.1 hx]

private theorem exists_ncard_orbit_eq_two_pow {E : Subgroup (Perm α)} (hE : ∀ x ∈ E, x ^ 2 = 1)
    (a : α) : ∃ k, (orbit E a).ncard = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, by simpa using sq_eq_one_coe hE x⟩
  obtain ⟨k, hk⟩ := hp.index (stabilizer E a)
  exact ⟨k, by rw [← index_stabilizer, hk]⟩

private theorem index_iInf_stabilizer_le {E : Subgroup (Perm α)} (hE : ∀ x ∈ E, x ^ 2 = 1)
    (f : ℕ → ℕ) (hf : ∀ a b, f a + f b ≤ f (a + b)) (s : Finset α)
    (hs : ∀ x : E, ∀ a ∈ s, x • a ∈ s)
    (hO : ∀ a ∈ s, (orbit E a).ncard ≤ 2 ^ f (orbit E a).ncard) :
    (⨅ a ∈ s, stabilizer E a).index ≤ 2 ^ f s.card := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · have : (⨅ a ∈ (∅ : Finset α), stabilizer E a) = ⊤ := by simp
      rw [this, index_top]
      exact Nat.one_le_two_pow
    obtain ⟨O, hmemO⟩ : ∃ O : Finset α, ∀ b, b ∈ O ↔ b ∈ orbit E a :=
      ⟨Finset.univ.filter (· ∈ orbit E a), fun b => by simp⟩
    have hOs : O ⊆ s := fun b hb => by
      obtain ⟨y, rfl⟩ := mem_orbit_iff.1 ((hmemO b).1 hb)
      exact hs y a ha
    have haO : a ∈ O := (hmemO a).2 (mem_orbit_self a)
    have hts : s \ O ⊂ s := Finset.sdiff_ssubset hOs ⟨a, haO⟩
    have ht : ∀ x : E, ∀ b ∈ s \ O, x • b ∈ s \ O := by
      intro x b hb
      rw [Finset.mem_sdiff] at hb ⊢
      refine ⟨hs x b hb.1, fun hxb => hb.2 ?_⟩
      rw [hmemO] at hxb ⊢
      obtain ⟨y, hy⟩ := mem_orbit_iff.1 hxb
      exact mem_orbit_iff.2 ⟨x⁻¹ * y, by rw [mul_smul, hy, inv_smul_smul]⟩
    have hsplit : (⨅ b ∈ s, stabilizer E b) =
        (⨅ b ∈ s \ O, stabilizer E b) ⊓ stabilizer E a := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_iInf, mem_stabilizer_iff]
      constructor
      · intro h
        exact ⟨fun b hb => h b (Finset.mem_sdiff.1 hb).1, h a ha⟩
      · rintro ⟨h1, h2⟩ b hb
        by_cases hbO : b ∈ O
        · exact smul_eq_of_mem_stabilizer hE (mem_stabilizer_iff.2 h2) ((hmemO b).1 hbO)
        · exact h1 b (Finset.mem_sdiff.2 ⟨hb, hbO⟩)
    have hOcard : (orbit E a).ncard = O.card := by
      rw [← Set.ncard_coe_finset]
      exact congrArg Set.ncard (Set.ext fun b => (hmemO b).symm.trans Finset.mem_coe.symm)
    rw [hsplit]
    calc ((⨅ b ∈ s \ O, stabilizer E b) ⊓ stabilizer E a).index
        ≤ (⨅ b ∈ s \ O, stabilizer E b).index * (stabilizer E a).index := index_inf_le
      _ ≤ 2 ^ f (s \ O).card * 2 ^ f O.card := by
        refine Nat.mul_le_mul (ih _ hts ht fun b hb => hO b (Finset.mem_sdiff.1 hb).1) ?_
        rw [index_stabilizer, ← hOcard]
        exact hO a ha
      _ = 2 ^ (f (s \ O).card + f O.card) := (pow_add _ _ _).symm
      _ ≤ 2 ^ f s.card := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        rw [← Finset.card_sdiff_add_card_eq_card hOs]
        exact hf _ _

private theorem iInf_stabilizer_univ (E : Subgroup (Perm α)) :
    (⨅ a ∈ (Finset.univ : Finset α), stabilizer E a) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Equiv.ext fun i =>
    mem_stabilizer_iff.1 (mem_iInf.1 (mem_iInf.1 hx i) (Finset.mem_univ i)))

theorem card_le_two_pow_half_of_sq_eq_one (E : Subgroup (Perm α)) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 2 ^ (Fintype.card α / 2) := by
  have h := index_iInf_stabilizer_le hE (· / 2)
    (fun a b => show a / 2 + b / 2 ≤ (a + b) / 2 by omega) Finset.univ
    (fun _ _ _ => Finset.mem_univ _) fun a _ => by
      obtain ⟨k, hk⟩ := exists_ncard_orbit_eq_two_pow hE a
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) (le_div_two_of_two_pow k)
  rwa [iInf_stabilizer_univ, index_bot, Finset.card_univ] at h

theorem card_le_sixteen_of_le_alternatingGroup [DecidableEq α] (hα : Fintype.card α ≤ 11)
    (E : Subgroup (Perm α)) (hE : ∀ x ∈ E, x ^ 2 = 1) (hA : E ≤ alternatingGroup α) :
    Nat.card E ≤ 16 := by
  classical
  by_cases h2 : ∃ a : α, (orbit E a).ncard = 2
  ·
    obtain ⟨a, ha⟩ := h2
    obtain ⟨O, hmemO⟩ : ∃ O : Finset α, ∀ b, b ∈ O ↔ b ∈ orbit E a :=
      ⟨Finset.univ.filter (· ∈ orbit E a), fun b => by simp⟩
    have hOcard : O.card = 2 := by
      rw [← ha, ← Set.ncard_coe_finset]
      exact congrArg Set.ncard (Set.ext fun b => Finset.mem_coe.trans (hmemO b))
    have hs : ∀ x : E, ∀ b ∈ Oᶜ, x • b ∈ Oᶜ := by
      intro x b hb
      rw [Finset.mem_compl] at hb ⊢
      intro hxb
      apply hb
      rw [hmemO] at hxb ⊢
      obtain ⟨y, hy⟩ := mem_orbit_iff.1 hxb
      exact mem_orbit_iff.2 ⟨x⁻¹ * y, by rw [mul_smul, hy, inv_smul_smul]⟩
    have hscard : Oᶜ.card / 2 ≤ 4 := by
      rw [Finset.card_compl, hOcard]
      omega
    have hidx : (⨅ b ∈ Oᶜ, stabilizer E b).index ≤ 16 := by
      refine (index_iInf_stabilizer_le hE (· / 2)
        (fun a b => show a / 2 + b / 2 ≤ (a + b) / 2 by omega) Oᶜ hs fun b _ => ?_).trans ?_
      · obtain ⟨k, hk⟩ := exists_ncard_orbit_eq_two_pow hE b
        rw [hk]
        exact Nat.pow_le_pow_right (by norm_num) (le_div_two_of_two_pow k)
      · exact (Nat.pow_le_pow_right (by norm_num) hscard).trans (by norm_num)
    rcases bot_or_exists_ne_one (⨅ b ∈ Oᶜ, stabilizer E b) with hbot | ⟨y, hy, hy1⟩
    · rwa [hbot, index_bot] at hidx
    ·
      exfalso
      simp only [Subgroup.mem_iInf, mem_stabilizer_iff] at hy
      have hσ1 : (y : Perm α) ≠ 1 := fun h => hy1 (Subtype.ext h)
      have hsupp : (y : Perm α).support ⊆ O := by
        intro b hb
        rw [Perm.mem_support] at hb
        by_contra hbO
        exact hb (hy b (Finset.mem_compl.2 hbO))
      have hcard2 : (y : Perm α).support.card = 2 :=
        le_antisymm (hOcard ▸ Finset.card_le_card hsupp) (Perm.two_le_card_support_of_ne_one hσ1)
      have hsign : Perm.sign (y : Perm α) = -1 := (Perm.card_support_eq_two.1 hcard2).sign_eq
      have hmem : Perm.sign (y : Perm α) = 1 := Perm.mem_alternatingGroup.1 (hA y.2)
      rw [hsign] at hmem
      exact absurd hmem (by decide)
  ·
    have h := index_iInf_stabilizer_le hE (fun m => 2 * (m / 4))
      (fun a b => show 2 * (a / 4) + 2 * (b / 4) ≤ 2 * ((a + b) / 4) by omega) Finset.univ
      (fun _ _ _ => Finset.mem_univ _) fun a _ => by
        obtain ⟨k, hk⟩ := exists_ncard_orbit_eq_two_pow hE a
        rw [hk]
        refine Nat.pow_le_pow_right (by norm_num) (le_two_mul_div_four_of_two_pow ?_)
        rintro rfl
        exact h2 ⟨a, by simpa using hk⟩
    rw [iInf_stabilizer_univ, index_bot, Finset.card_univ] at h
    exact h.trans ((Nat.pow_le_pow_right (by norm_num)
      (show 2 * (Fintype.card α / 4) ≤ 4 by omega)).trans (by norm_num))

end Perm

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem card_le_of_elementary (c : Config G L Q n θ z) {E : Subgroup G}
    (hEC : E ≤ centralizer ({z} : Set G)) (hE2 : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 32 := by
  have hn := c.hn8
  have hEN : E ≤ normalizer (L : Set G) :=
    hEC.trans (AltStdCycTwo.cent_le_normalizer c.ot.std c.ot.cyc)
  let φ : E →* Perm (Fin n) := (AltStdBal.rho θ hn).comp (inclusion hEN)
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map E.subtype ≤ zpowers z := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : AltStdBal.rho θ hn (inclusion hEN x) = 1 := hx
      exact AltStdCycTwo.mem_zpowers_of_two_pow c.ot.cyc c.ot.card
        ⟨(AltStdBal.rho_eq_one_iff θ hn _).1 h1, hEC x.2⟩ (k := 1) (by simpa using hE2 x x.2)
    calc Nat.card φ.ker = Nat.card (φ.ker.map E.subtype) :=
          (card_map_of_injective (subtype_injective E)).symm
      _ ≤ Nat.card (zpowers z) := card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, c.ot.cyc.order]
  have hsq : ∀ y ∈ φ.range, y ^ 2 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hE2 x x.2), map_one]
  have hrange : Nat.card φ.range ≤ 16 := by
    rcases c.shape with h1 | ⟨h9, -⟩
    · have hA : φ.range ≤ alternatingGroup (Fin n) := by
        rintro _ ⟨x, rfl⟩
        exact (AltStdCycTwo.mem_evenAct_iff θ hn (hEN x.2)).1
          (AltStdCycTwo.sup_le_evenAct θ hn (h1 (hEC x.2)))
      exact card_le_sixteen_of_le_alternatingGroup (by simpa using c.small) φ.range hsq hA
    · refine (card_le_two_pow_half_of_sq_eq_one φ.range hsq).trans ?_
      rw [Fintype.card_fin]
      calc 2 ^ (n / 2) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 16 := by norm_num
  have hmul := card_mul_index φ.ker
  rw [index_ker] at hmul
  rw [← hmul]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 2 * 16 := Nat.mul_le_mul hker hrange
    _ = 32 := by norm_num

theorem conj_not_mem_of_elementary (c : Config G L Q n θ z) {T : Subgroup G}
    (hT2 : ∀ x ∈ T, x ^ 2 = 1) (hT : Nat.card T = 64) (g : G) : g * z * g⁻¹ ∉ T := by
  intro hzT
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm_of_sq_eq_one (H := T)
      (fun x => Subtype.ext (by simpa using hT2 x x.2)) ⟨a, ha⟩ ⟨b, hb⟩)
  have hEC : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := hcomm t ht _ hzT
    show g⁻¹ * t * g⁻¹⁻¹ * z = z * (g⁻¹ * t * g⁻¹⁻¹)
    rw [inv_inv]
    calc g⁻¹ * t * g * z = g⁻¹ * (t * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * t) * g := by rw [h]
      _ = z * (g⁻¹ * t * g) := by group
  have hE2 : ∀ x ∈ T.map (MulAut.conj g⁻¹).toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, hT2 t ht, map_one]
  have hcard : Nat.card (T.map (MulAut.conj g⁻¹).toMonoidHom) = 64 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hT]
  have := card_le_of_elementary c hEC hE2
  omega

end CFSG.OddStandard.AltStdSmall4
