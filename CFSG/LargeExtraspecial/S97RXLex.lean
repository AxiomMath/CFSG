module

public import CFSG.LargeExtraspecial.S97RXExt
public import CFSG.LargeExtraspecial.S97RXSR

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k : G}
  {m : S.M}

theorem exists_lex_badPair (hex : ∃ h k m, BadPair S g A h k m) :
    ∃ h k m, BadPair S g A h k m ∧
      (∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
        Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k))) ∧
      (∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
        Nat.card (Ebar S k' ((m' : G) * k')) = Nat.card (Ebar S k ((m : G) * k)) →
        Nat.card (S9.X97 S k m) ≤ Nat.card (S9.X97 S k' m')) := by
  set N := Nat.card S.O
  obtain ⟨h₀, k₀, m₀, hb⟩ := hex
  obtain ⟨⟨h, k, m⟩, hmem, hmax⟩ := Set.exists_max_image
    {p : G × G × S.M | BadPair S g A p.1 p.2.1 p.2.2}
    (fun p => Nat.card (Ebar S p.2.1 ((p.2.2 : G) * p.2.1)) * (N + 1) +
      (N - Nat.card (S9.X97 S p.2.1 p.2.2))) (Set.toFinite _) ⟨⟨h₀, k₀, m₀⟩, hb⟩
  refine ⟨h, k, m, hmem, fun h' k' m' hb' => ?_, fun h' k' m' hb' he => ?_⟩
  · have h1 := hmax ⟨h', k', m'⟩ hb'
    simp only at h1
    have hX : Nat.card (S9.X97 S k m) ≤ N := Subgroup.card_le_card_group _
    by_contra hlt
    push Not at hlt
    have h2 : (Nat.card (Ebar S k ((m : G) * k)) + 1) * (N + 1) ≤
        Nat.card (Ebar S k' ((m' : G) * k')) * (N + 1) := Nat.mul_le_mul_right _ hlt
    have h3 : N - Nat.card (S9.X97 S k m) ≤ N := Nat.sub_le _ _
    nlinarith
  · have h1 := hmax ⟨h', k', m'⟩ hb'
    simp only at h1
    rw [he] at h1
    have hX : Nat.card (S9.X97 S k m) ≤ N := Subgroup.card_le_card_group _
    have hX' : Nat.card (S9.X97 S k' m') ≤ N := Subgroup.card_le_card_group _
    omega

theorem Pair111.card_Lbar_le_two_mul_stab {k' : G} (P : Pair111 S g A h k k') {w : S.Qt}
    (hwA : w ∈ S.clSub A) :
    Nat.card (S.Lbar k) ≤ 2 * Nat.card (S.Lbar k ⊓ ptFix S ((ZMod 2) ∙ w) : Subgroup S.O) := by
  classical
  set St : Subgroup S.O := S.Lbar k ⊓ ptFix S ((ZMod 2) ∙ w) with hSt
  have hfixa : ∀ l ∈ S.Lbar k,
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) = S.cl (k * S.z * k⁻¹) :=
    fun l hl => fix_of_mem_normalizer P.hy.hyp4 (le_normalizer hl)
  have hshift : ∀ l ∈ S.Lbar k, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w →
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + S.cl (k * S.z * k⁻¹) := by
    intro l hl hlw
    rcases mem_span_cl_iff.mp (P.cfg.inc.apply_sub_mem_span P.mem hl hwA) with h0 | h1
    · exact absurd (sub_eq_zero.mp h0) hlw
    · rw [← h1]
      abel
  have ha0 : S.cl (k * S.z * k⁻¹) ≠ 0 := cl_conj_z_ne_zero S P.memQ P.ne
  have hne : w + S.cl (k * S.z * k⁻¹) ≠ w := fun h0 => ha0 (by
    have := congrArg (· - w) h0
    simpa using this)
  let χ : ↥(S.Lbar k) →* Multiplicative (ZMod 2) :=
    { toFun := fun l => if ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w then 1
        else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := by
        intro a b
        have hab : ((a * b : ↥(S.Lbar k)) : S.O) = (a : S.O) * (b : S.O) := rfl
        simp only [hab, coe_mul_apply]
        by_cases ha : ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w <;>
          by_cases hb : ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
        · simp [ha, hb]
        · have e : ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
              w + S.cl (k * S.z * k⁻¹) := by
            rw [hshift _ b.2 hb, map_add, ha, hfixa _ a.2]
          simp [ha, hb, e, hne]
        · have e : ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
              w + S.cl (k * S.z * k⁻¹) := by
            rw [hb, hshift _ a.2 ha]
          simp [ha, hb]
        · have e : ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
              w := by
            rw [hshift _ b.2 hb, map_add, hshift _ a.2 ha, hfixa _ a.2, add_assoc,
              ZModModule.add_self, add_zero]
          simp only [ha, hb, e, ↓reduceIte]
          rfl }
  have hker : χ.ker = St.subgroupOf (S.Lbar k) := by
    ext l
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change (if ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w then 1 else Multiplicative.ofAdd 1) =
      (1 : Multiplicative (ZMod 2)) ↔ (l : S.O) ∈ S.Lbar k ⊓ ptFix S ((ZMod 2) ∙ w)
    by_cases hl : ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
    · simp only [hl, ↓reduceIte, true_iff]
      exact ⟨l.2, BadPair.mem_ptFix_span_iff.mpr hl⟩
    · simp only [hl, ↓reduceIte]
      exact ⟨fun h1 => absurd h1 (by decide),
        fun h1 => absurd (BadPair.mem_ptFix_span_iff.mp h1.2) hl⟩
  have h1 := χ.ker.card_mul_index
  rw [Subgroup.index_ker, hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : St ≤ S.Lbar k)).toEquiv] at h1
  have h2 : Nat.card χ.range ≤ 2 := by
    calc Nat.card χ.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
      _ = 2 := by simp
  rw [← h1]
  exact (Nat.mul_le_mul_left _ h2).trans (by rw [mul_comm])

namespace BadPair

variable (B : BadPair S g A h k m)
include B

omit B in
theorem card_T97_le_of_stab (P : Pair111 S g A h k ((m : G) * k))
    (hE : Ebar S k ((m : G) * k) ≠ ⊥) (hodd : Odd (Nat.card (center (S9.Q97 S k m))))
    {St : Subgroup S.O} (hStL : St ≤ S.Lbar k)
    (hSt : Nat.card (S.Lbar k) ≤ 2 * Nat.card St) {N : Subgroup (Lam97 S k m)}
    (hN : ∀ s : ↥(S9.X97 S k m), (s : S.O) ∈ St → pi97 S k m s ∈ N) :
    Nat.card (T97 S k m k) ≤ 2 * Nat.card N := by
  have X := P.hyp97 hE
  have hStX : St ≤ S9.X97 S k m := hStL.trans le_sup_left
  let ψ : ↥St →* Lam97 S k m := (pi97 S k m).comp (inclusion hStX)
  have hrange : ψ.range ≤ N := by
    rintro _ ⟨s, rfl⟩
    exact hN (inclusion hStX s) s.2
  have hker : Nat.card ψ.ker ≤ Nat.card (Ebar S k ((m : G) * k)) := by
    refine Nat.card_le_card_of_injective (fun s => ⟨((s : ↥St) : S.O), ?_⟩) ?_
    · have hs1 : ψ s = 1 := s.2
      rw [← P.inf_O2Sub_eq]
      exact ⟨hStL (s : ↥St).2, (H97.pi97_eq_one_iff X hodd P.hy.hyp4
        (x := inclusion hStX (s : ↥St)) (hStL (s : ↥St).2)).mp hs1⟩
    · intro a b hab
      exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 := Subgroup.card_le_of_le hrange
  have h3 := P.card_T97_mul hE hodd
  have hE0 : 0 < Nat.card (Ebar S k ((m : G) * k)) := Nat.card_pos
  have h4 : Nat.card ψ.ker * Nat.card ψ.range ≤
      Nat.card (Ebar S k ((m : G) * k)) * Nat.card N := Nat.mul_le_mul hker h2
  have h6 : Nat.card (Ebar S k ((m : G) * k)) * Nat.card (T97 S k m k) ≤
      Nat.card (Ebar S k ((m : G) * k)) * (2 * Nat.card N) := by nlinarith
  exact Nat.le_of_mul_le_mul_left h6 hE0

theorem card_le_two_mul_of_map_eq (hodd : Odd (Nat.card (center (S9.Q97 S k m)))) {y : S.M}
    (hx : S.ρ y ∈ S9.X97 S k m) (hAy : A.map (MulAut.conj (y : G)).toMonoidHom = A) :
    Nat.card (T97 S k m k) ≤ 2 * Nat.card (T97 S k m k ⊓
      normalizer (conjSubgroup (pi97 S k m ⟨S.ρ y, hx⟩) (T97 S k m k) : Set (Lam97 S k m)) :
        Subgroup (Lam97 S k m)) := by
  have P := B.1
  have hE := B.2.1
  have X := P.hyp97 hE
  have hρw : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) =
      S.cl (((y : G) * k) * S.z * ((y : G) * k)⁻¹) := ρ_cl_conj_z S y P.memQ
  have hwA : S.cl (((y : G) * k) * S.z * ((y : G) * k)⁻¹) ∈ S.clSub A := by
    have hmem : ((y : G) * k) * S.z * ((y : G) * k)⁻¹ ∈ A := by
      rw [← hAy]
      exact mem_map_conj_iff.mpr (by
        rw [show (y : G)⁻¹ * ((y : G) * k * S.z * ((y : G) * k)⁻¹) * y = k * S.z * k⁻¹ by group]
        exact P.mem)
    exact S.cl_mem_clSub hmem (conj_mem_QG' S y.2 P.memQ)
  refine card_T97_le_of_stab P hE hodd inf_le_left (P.card_Lbar_le_two_mul_stab hwA) ?_
  intro s hs
  refine ⟨pi97_mem_T97 (mem_inf.mp hs).1,
    (H97.fix_iff X hodd s ⟨S.ρ y, hx⟩).mp ?_⟩
  change ((s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (S.cl (k * S.z * k⁻¹))) = ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹))
  rw [hρw]
  exact mem_ptFix_span_iff.mp (mem_inf.mp hs).2

theorem map_eq_of_ne_bot (hmax : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k)))
    (hodd : Odd (Nat.card (center (S9.Q97 S k m)))) {y : S.M} (hx : S.ρ y ∈ S9.X97 S k m)
    (hc : T97 S k m k ⊓ normalizer (conjSubgroup (pi97 S k m ⟨S.ρ y, hx⟩) (T97 S k m k) :
      Set (Lam97 S k m)) ≠ ⊥) : A.map (MulAut.conj (y : G)).toMonoidHom = A := by
  have P := B.1
  have hE := B.2.1
  have X := P.hyp97 hE
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hc
  have ht1' : t ≠ 1 := fun h0 => ht1 (Subtype.ext h0)
  obtain ⟨htT, htN⟩ := mem_inf.mp ht
  obtain ⟨l, hlL, rfl⟩ := exists_of_mem_T97 htT
  have hfix := (H97.fix_iff X hodd l ⟨S.ρ y, hx⟩).mpr htN
  have hlE : (l : S.O) ∉ Ebar S k ((m : G) * k) := fun h0 => by
    rw [← P.inf_O2Sub_eq] at h0
    exact ht1' ((H97.pi97_eq_one_iff X hodd P.hy.hyp4 hlL).mpr h0.2)
  have hρM : S.ρ y ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hM : (S.ρ y)⁻¹ * (l : S.O) * S.ρ y ∈ S.Mbar :=
    mul_mem (mul_mem (inv_mem hρM) (S9.X97_le_Mbar l.2)) hρM
  have hfix' : ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (k * S.z * k⁻¹))) = ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) :=
    hfix
  have h1 : (((S.ρ y)⁻¹ * (l : S.O) * S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (k * S.z * k⁻¹)) = S.cl (k * S.z * k⁻¹) := by
    rw [coe_mul_apply, coe_mul_apply, hfix', inv_apply_apply_O]
  have hN := mem_normalizer_of_fix P.hy.hyp4.conj_mem P.hy.hyp4.conj_ne (h := 1) hM (by
    simp only [OneMemClass.coe_one, one_mul]
    exact h1)
  simp only [OneMemClass.coe_one, one_mul] at hN
  have hx' : S.ρ y⁻¹ ∈ S9.X97 S k m := by rw [map_inv]; exact inv_mem hx
  have hA := B.map_eq_of_max hmax (y := y⁻¹) hx' hlL hlE (by
    rw [map_inv, inv_inv]
    exact hN)
  have hA' : A.map (MulAut.conj ((y : G)⁻¹)).toMonoidHom = A := by simpa using hA
  calc A.map (MulAut.conj (y : G)).toMonoidHom =
        (A.map (MulAut.conj ((y : G)⁻¹)).toMonoidHom).map (MulAut.conj (y : G)).toMonoidHom := by
        rw [hA']
    _ = A := by simpa using map_conj_inv_map_conj A ((y : G)⁻¹)

theorem card_le_two_mul_of_ne_bot (hmax : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k)))
    (hodd : Odd (Nat.card (center (S9.Q97 S k m)))) {c : Lam97 S k m}
    (hc : T97 S k m k ⊓ normalizer (conjSubgroup c (T97 S k m k) : Set (Lam97 S k m)) ≠ ⊥) :
    Nat.card (T97 S k m k) ≤ 2 * Nat.card (T97 S k m k ⊓
      normalizer (conjSubgroup c (T97 S k m k) : Set (Lam97 S k m)) : Subgroup (Lam97 S k m)) := by
  obtain ⟨x, rfl⟩ := pi97_surjective c
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (S9.X97_le_Mbar x.2)
  have hx : S.ρ y ∈ S9.X97 S k m := hy ▸ x.2
  obtain rfl : x = ⟨S.ρ y, hx⟩ := Subtype.ext hy.symm
  exact B.card_le_two_mul_of_map_eq hodd hx (B.map_eq_of_ne_bot hmax hodd hx hc)

theorem X97_eq_of_inf_eq_bot (hmax : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k)))
    (hmin : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) = Nat.card (Ebar S k ((m : G) * k)) →
      Nat.card (S9.X97 S k m) ≤ Nat.card (S9.X97 S k' m'))
    (hodd : Odd (Nat.card (center (S9.Q97 S k m)))) (h2 : 2 < Nat.card (T97 S k m k))
    {y : S.M} (hx : S.ρ y ∈ S9.X97 S k m)
    (hc : T97 S k m k ⊓ normalizer (conjSubgroup (pi97 S k m ⟨S.ρ y, hx⟩) (T97 S k m k) :
      Set (Lam97 S k m)) = ⊥) : S9.X97 S k y = S9.X97 S k m := by
  have P := B.1
  have hE := B.2.1
  rcases P.cfg.inter y.2 with hA | hdisj
  · exfalso
    have h1 := B.card_le_two_mul_of_map_eq hodd hx hA
    rw [hc, card_bot] at h1
    exact absurd (lt_of_lt_of_le h2 h1) (by norm_num)
  have hmem' : ((y : G) * k) * S.z * ((y : G) * k)⁻¹ ∈ A.map (MulAut.conj (y : G)).toMonoidHom :=
    mem_map_conj_iff.mpr (by
      rw [show (y : G)⁻¹ * ((y : G) * k * S.z * ((y : G) * k)⁻¹) * y = k * S.z * k⁻¹ by group]
      exact P.mem)
  have P₁ : Pair111 S g A (y : G) k ((y : G) * k) :=
    ⟨P.cfg, y.2, hdisj, P.mem, P.ne, hmem', conj_ne_z' S y.2 P.ne⟩
  have hLyk : S.Lbar ((y : G) * k) ≤ S9.X97 S k m := by
    rw [Lbar_mul S y k]
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem hx (mem_sup_left hl)) (inv_mem hx)
  have hle : S9.X97 S k y ≤ S9.X97 S k m := sup_le le_sup_left hLyk
  have hEE : Ebar S k ((m : G) * k) ≤ Ebar S k ((y : G) * k) := by
    intro e he
    have heO : e ∈ O2Sub (S9.X97 S k m) := by
      rw [← P.inf_O2Sub_eq] at he
      exact he.2
    exact ⟨he.1, O2Sub_le_normalizer_Lbar (P.hy.hyp4.mul y) (P.hy.cons.mul y) hLyk
      (Lbar_sup_le_Mbar S _ _) heO⟩
  have hE0 : 0 < Nat.card (Ebar S k ((m : G) * k)) := Nat.card_pos
  have hcE := Subgroup.card_le_of_le hEE
  have hE₁ : Ebar S k ((y : G) * k) ≠ ⊥ := fun h0 => hE (eq_bot_iff.mpr (h0 ▸ hEE))
  by_cases hidx : Nat.card (S.Lbar k) = 2 * Nat.card (Ebar S k ((y : G) * k))
  · exact (P₁.false_of_index_two hE₁ hidx).elim
  have X₁ := P₁.hyp97 hE₁
  have h4₁ := X₁.four_mul_card_le P₁.not_Lbar_le_O2Sub (by rw [P₁.inf_O2Sub_eq]; exact hidx)
  rw [P₁.inf_O2Sub_eq] at h4₁
  have hb : BadPair S g A (y : G) k y := ⟨P₁, hE₁, h4₁⟩
  have h1 := hmax (y : G) k y hb
  have h3 := hmin (y : G) k y hb (le_antisymm h1 hcE)
  exact Subgroup.eq_of_le_of_card_ge hle h3

omit B in
theorem sup_eq_top_of_X97_eq {y : S.M} (hx : S.ρ y ∈ S9.X97 S k m)
    (hX : S9.X97 S k y = S9.X97 S k m) :
    T97 S k m k ⊔ conjSubgroup (pi97 S k m ⟨S.ρ y, hx⟩) (T97 S k m k) = ⊤ := by
  have hLyk : S.Lbar ((y : G) * k) ≤ S9.X97 S k m := hX ▸ le_sup_right
  have hmap : ((S.Lbar k ⊔ S.Lbar ((y : G) * k)).subgroupOf (S9.X97 S k m)).map (pi97 S k m) ≤
      T97 S k m k ⊔ conjSubgroup (pi97 S k m ⟨S.ρ y, hx⟩) (T97 S k m k) := by
    rw [Subgroup.map_le_iff_le_comap, subgroupOf_sup le_sup_left hLyk]
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · exact mem_sup_left (pi97_mem_T97 (mem_subgroupOf.mp hv))
    · have hv' := (mem_Lbar_mul_iff S y k).mp (mem_subgroupOf.mp hv)
      refine mem_sup_right (mem_conjSubgroup.mpr ?_)
      have h1 := pi97_mem_T97 (S := S) (k := k) (m := m) (j := k)
        (x := (⟨S.ρ y, hx⟩ : ↥(S9.X97 S k m))⁻¹ * v * ⟨S.ρ y, hx⟩)
        (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hv')
      simpa only [map_mul, map_inv] using h1
  refine eq_top_iff.mpr fun c _ => ?_
  obtain ⟨u, rfl⟩ := pi97_surjective c
  have hu : (u : S.O) ∈ S.Lbar k ⊔ S.Lbar ((y : G) * k) := hX.ge u.2
  exact hmap (mem_map_of_mem _ (mem_subgroupOf.mpr hu))

theorem sup_eq_top_of_inf_eq_bot (hmax : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) ≤ Nat.card (Ebar S k ((m : G) * k)))
    (hmin : ∀ h' k' (m' : S.M), BadPair S g A h' k' m' →
      Nat.card (Ebar S k' ((m' : G) * k')) = Nat.card (Ebar S k ((m : G) * k)) →
      Nat.card (S9.X97 S k m) ≤ Nat.card (S9.X97 S k' m'))
    (hodd : Odd (Nat.card (center (S9.Q97 S k m)))) (h2 : 2 < Nat.card (T97 S k m k))
    {c : Lam97 S k m}
    (hc : T97 S k m k ⊓ normalizer (conjSubgroup c (T97 S k m k) : Set (Lam97 S k m)) = ⊥) :
    T97 S k m k ⊔ conjSubgroup c (T97 S k m k) = ⊤ := by
  obtain ⟨x, rfl⟩ := pi97_surjective c
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (S9.X97_le_Mbar x.2)
  have hx : S.ρ y ∈ S9.X97 S k m := hy ▸ x.2
  obtain rfl : x = ⟨S.ρ y, hx⟩ := Subtype.ext hy.symm
  exact sup_eq_top_of_X97_eq hx (B.X97_eq_of_inf_eq_bot hmax hmin hodd h2 hx hc)

end BadPair

end CFSG.LargeExtraspecial.S11
