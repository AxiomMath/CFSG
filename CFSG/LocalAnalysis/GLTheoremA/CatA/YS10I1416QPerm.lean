module

public import CFSG.GH74.SmallRanks.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open MulAction

theorem two_mul_le_two_pow (a : ℕ) : 2 * a ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · norm_num
    · have : 2 ≤ 2 ^ a := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
      rw [pow_succ]
      omega

theorem sq_card_le_perm_aux (n : ℕ) : ∀ (α : Type) [Finite α], Nat.card α = n →
    ∀ (E : Subgroup (Equiv.Perm α)), IsElemAbelian 2 E → Nat.card E ^ 2 ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α _ hn E hE
  classical
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have hem : IsEmpty α := by
      haveI := Fintype.ofFinite α
      rw [Nat.card_eq_fintype_card] at hn
      exact Fintype.card_eq_zero_iff.1 (hn.trans h0)
    have hsub : Subsingleton (Equiv.Perm α) := ⟨fun f g => Equiv.ext fun x => isEmptyElim x⟩
    have h1 : Nat.card E ≤ 1 := by
      have : Subsingleton E := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      exact Finite.card_le_one_iff_subsingleton.2 this
    rw [h0, pow_zero]
    have : Nat.card E ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h1 2
    simpa using this
  · haveI : Nonempty α := (Nat.card_pos_iff.1 (hn ▸ hpos)).1
    obtain ⟨x⟩ := ‹Nonempty α›
    haveI : Fintype α := Fintype.ofFinite α
    have hP : IsPGroup 2 E := CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    set O : Set α := MulAction.orbit E x with hO
    set S : Subgroup E := MulAction.stabilizer E x with hSdef
    have hidx : S.index = O.ncard := MulAction.index_stabilizer E x
    have hcardE : Nat.card S * S.index = Nat.card E := Subgroup.card_mul_index S
    have hdvd : S.index ∣ 2 ^ k := by
      rw [← hk, ← hcardE]; exact Dvd.intro_left _ rfl
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hOn : O.ncard = 2 ^ a := hidx.symm.trans ha
    have hsum : O.ncard + Oᶜ.ncard = n := by
      rw [Set.ncard_add_ncard_compl O]
      exact hn
    have hfixO : ∀ g : E, g ∈ S → ∀ y ∈ O, (g : Equiv.Perm α) y = y := by
      intro g hg y hy
      obtain ⟨h, rfl⟩ := hy
      have hgx : (g : Equiv.Perm α) x = x := (MulAction.mem_stabilizer_iff).1 hg
      have hcomm : (g : Equiv.Perm α) * (h : Equiv.Perm α) = (h : Equiv.Perm α) * (g : Equiv.Perm α) :=
        congrArg Subtype.val (hE.1.is_comm.comm g h)
      have h1 : (g : Equiv.Perm α) ((h : Equiv.Perm α) x) =
          (h : Equiv.Perm α) ((g : Equiv.Perm α) x) := by
        have := congrArg (fun σ : Equiv.Perm α => σ x) hcomm
        simpa [Equiv.Perm.mul_apply] using this
      show (g : Equiv.Perm α) ((h : Equiv.Perm α) x) = (h : Equiv.Perm α) x
      rw [h1, hgx]
    have hpres : ∀ g : E, g ∈ S → ∀ y, (y ∉ O ↔ (g : Equiv.Perm α) y ∉ O) := by
      intro g hg y
      constructor
      · intro hy hgy
        apply hy
        have h2 : (g : Equiv.Perm α) ((g : Equiv.Perm α) y) = (g : Equiv.Perm α) y :=
          hfixO g hg _ hgy
        have h3 : (g : Equiv.Perm α) y = y := (g : Equiv.Perm α).injective h2
        rw [h3] at hgy
        exact hgy
      · intro hgy hy
        apply hgy
        rw [hfixO g hg y hy]
        exact hy
    let f : S →* Equiv.Perm {z : α // z ∉ O} :=
      MonoidHom.mk' (fun g => Equiv.Perm.subtypePerm ((g : E) : Equiv.Perm α)
          (fun y => (hpres (g : E) g.2 y).symm))
        (fun a b => Equiv.ext fun z => Subtype.ext rfl)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one f]
      intro g hg1
      have hz : ∀ z, z ∉ O → ((g : E) : Equiv.Perm α) z = z := by
        intro z hz
        have := congrArg (fun σ : Equiv.Perm {w : α // w ∉ O} => ((σ ⟨z, hz⟩ : {w // w ∉ O}) : α)) hg1
        simpa [f, Equiv.Perm.subtypePerm_apply] using this
      apply Subtype.ext
      apply Subtype.ext
      apply Equiv.ext
      intro z
      by_cases hzO : z ∈ O
      · exact hfixO _ g.2 z hzO
      · simpa using hz z hzO
    set T : Subgroup (Equiv.Perm {z : α // z ∉ O}) := f.range with hTdef
    have hTcard : Nat.card T = Nat.card S :=
      (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
    have hTel : IsElemAbelian 2 T := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
      · obtain ⟨a, ha⟩ := a
        obtain ⟨b, hb⟩ := b
        obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 ha
        obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hb
        apply Subtype.ext
        change f u * f v = f v * f u
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hE.1.is_comm.comm u.1 v.1)
      · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hy
        have hu2 : u ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using hE.2 _ u.1.2))
        show f u ^ 2 = 1
        rw [← map_pow, hu2, map_one]
    have hβcard : Nat.card {z : α // z ∉ O} = n - 2 ^ a := by
      have h1 : Nat.card {z : α // z ∉ O} = Oᶜ.ncard := by
        rw [← Nat.card_coe_set_eq]
        rfl
      omega
    have hlt : n - 2 ^ a < n := by
      have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      omega
    have hIH := ih (n - 2 ^ a) hlt {z : α // z ∉ O} hβcard T hTel
    rw [hTcard] at hIH
    have h2a : 2 ^ a ≤ n := by omega
    have hEc : Nat.card E = Nat.card S * 2 ^ a := by
      rw [ha] at hcardE
      exact hcardE.symm
    rw [hEc]
    calc (Nat.card S * 2 ^ a) ^ 2 = Nat.card S ^ 2 * 2 ^ (2 * a) := by
          rw [mul_pow, ← pow_mul, mul_comm a 2]
      _ ≤ 2 ^ (n - 2 ^ a) * 2 ^ (2 ^ a) :=
          Nat.mul_le_mul hIH (Nat.pow_le_pow_right (by norm_num) (two_mul_le_two_pow a))
      _ = 2 ^ n := by
          rw [← pow_add]
          congr 1
          omega

theorem card_sq_le_perm_elemAb (α : Type) [Finite α] (E : Subgroup (Equiv.Perm α))
    (hE : IsElemAbelian 2 E) : Nat.card E ^ 2 ≤ 2 ^ Nat.card α :=
  sq_card_le_perm_aux _ α rfl E hE

theorem card_le_two_pow_of_twoRank_le {X : Type} [Group X] [Finite X] {r : ℕ} (h : twoRank X ≤ r)
    {E : Subgroup X} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE).exists_card_eq
  have h1 := CFSG.SectionRank.le_pRank Nat.one_lt_two le_top hE hk
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (h1.trans h)

theorem le_two_of_two_pow_dvd {j m : ℕ} (hm : Odd m) (h : 2 ^ j ∣ 2 * m) : 2 ^ j ≤ 2 := by
  have hc : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hm)
  have h2 : 2 ^ j ∣ 2 := hc.dvd_of_dvd_mul_right h
  exact Nat.le_of_dvd (by norm_num) h2

theorem twoRank_lt_six_of_center_quotient {J : Type} [Group J] [Finite J]
    (hJ : Group.IsPerfect J) {m : ℕ} (hm : Odd m) (hZ : Nat.card (Subgroup.center J) ∣ 2 * m)
    (hS : ∀ F : Subgroup (J ⧸ Subgroup.center J), IsElemAbelian 2 F → Nat.card F ≤ 16) :
    twoRank J < 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : twoRank J ≤ 5 := by
    show CFSG.Open.pRank 2 (⊤ : Subgroup J) ≤ 5
    refine CFSG.SectionRank.pRank_le Nat.one_lt_two (k := 5) (fun E _ hE => ?_)
    have hP : IsPGroup 2 E := CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE
    obtain ⟨kE, hkE⟩ := hP.exists_card_eq
    set φ : E →* J ⧸ Subgroup.center J :=
      (QuotientGroup.mk' (Subgroup.center J)).comp E.subtype with hφ
    have hcard := Subgroup.card_ker_mul_card_range φ
    have hF : Nat.card φ.range ≤ 16 := by
      apply hS
      have hEE : IsElemAbelian 2 (⊤ : Subgroup E) := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y _ => ?_⟩
        · exact Subtype.ext (hE.1.is_comm.comm a.1 b.1)
        · exact Subtype.ext (by simpa using hE.2 _ y.2)
      rw [MonoidHom.range_eq_map]
      exact CFSG.SectionRank.isElemAbelian_map hEE φ
    have hK2 : Nat.card φ.ker ≤ 2 := by
      have hd : Nat.card φ.ker ∣ 2 ^ kE := by
        rw [← hkE]
        exact Subgroup.card_subgroup_dvd_card φ.ker
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
      have hKz : φ.ker.map E.subtype ≤ Subgroup.center J := by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
        have hk1 : (QuotientGroup.mk (k : J) : J ⧸ Subgroup.center J) = 1 := by
          have := MonoidHom.mem_ker.1 hk
          exact this
        exact QuotientGroup.eq_one_iff _ |>.1 hk1
      have hmap : Nat.card (φ.ker.map E.subtype) = Nat.card φ.ker :=
        Subgroup.card_map_of_injective E.subtype_injective
      have h2 : 2 ^ j ∣ 2 * m := by
        rw [← hj, ← hmap]
        exact (Subgroup.card_dvd_of_le hKz).trans hZ
      rw [hj]
      exact le_two_of_two_pow_dvd hm h2
    have hE32 : Nat.card E ≤ 2 ^ 5 := by
      rw [← hcard]
      calc Nat.card φ.ker * Nat.card φ.range ≤ 2 * 16 := Nat.mul_le_mul hK2 hF
        _ = 2 ^ 5 := by norm_num
    exact hE32
  exact lt_of_le_of_lt hr (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA

end
