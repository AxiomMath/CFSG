module

public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.RankThree.SubgroupLists.SL2Perfect

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Quasithin CFSG.SectionRank.Ccomm

theorem closure_pow_eq_top_of_closure_eq {G : Type} [Group G] {p : ℕ} {P : Subgroup G}
    (h : Subgroup.closure {x : G | x ∈ P ∧ x ^ p = 1} = P) :
    Subgroup.closure {x : ↥P | x ^ p = 1} = ⊤ := by
  have himg : (P.subtype '' {x : ↥P | x ^ p = 1}) = {x : G | x ∈ P ∧ x ^ p = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxp), rfl⟩
  apply Subgroup.map_injective P.subtype_injective
  rw [MonoidHom.map_closure, himg, h, Subgroup.map_top, Subgroup.range_subtype]

theorem eq_bot_of_perfect_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q : Subgroup G) (hQ : IsPGroup p Q) (hperf : ⁅Q, Q⁆ = Q) : Q = ⊥ := by
  by_contra hne
  have hnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  have hsolv : Group.IsSolvable Q := inferInstance
  have hp : Group.IsPerfect Q := Subgroup.isPerfect_iff.mpr hperf
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne (Group.isPerfect_def.mp hp)

theorem card_sl2_five : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
  norm_num

theorem mod_five_of_dvd {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5)
    (h : 5 ∣ (p ^ 2 - 1) * (p ^ 2 - p)) : p % 5 = 1 ∨ p % 5 = 4 := by
  have hz : (((p ^ 2 - 1) * (p ^ 2 - p) : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have hle1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hle2 : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  push_cast [Nat.cast_sub hle1, Nat.cast_sub hle2] at hz
  have hcast : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod p 5).symm
  rw [hcast] at hz
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : p % 5
  · exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero hr))
      (Ne.symm hp5)
  · exact Or.inl rfl
  · exfalso
    revert hz
    decide
  · exfalso
    revert hz
    decide
  · exact Or.inr rfl

theorem a129One : A129One := by
  intro p hp hp2 G _ _ P H hPn hPp hΩ hcl hrk hH hPH
  have hpf : Fact p.Prime := ⟨hp⟩
  have hΩ' : Subgroup.closure {x : ↥P | x ^ p = 1} = ⊤ := closure_pow_eq_top_of_closure_eq hΩ
  have hexp : ∀ x : ↥P, x ^ p = 1 :=
    pow_eq_one_of_classLeTwo hp2 (classLeTwo_top_of hcl) hΩ'
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 2 := by
    rw [pRank_top_subtype]
    exact hrk.le
  obtain ⟨-, hbound⟩ := rank_two_exponent_prime_order_bound hPp hexp hrank
  obtain ⟨hFc, hWcomm, hWpow⟩ := frattini_quotient_elementary hPp
  have := hFc
  obtain ⟨m, hm⟩ := (hPp.to_quotient (frattini ↥P)).exists_card_eq
  have hmle : m ≤ 2 := by
    rw [hm] at hbound
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hbound
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hm
  obtain ⟨ι, hι⟩ := exists_injective_GL_le_two (R := ZMod p) hmle
  let ρ : ↥H →* MulAut ↥P := MulAut.conjNormal.comp H.subtype
  let θ : MulAut (↥P ⧸ frattini ↥P) →* GL (Fin 2) (ZMod p) :=
    ι.comp (elemAutEquivGL e).toMonoidHom
  have hθ : Function.Injective θ := hι.comp (elemAutEquivGL e).injective
  let χ : ↥H →* GL (Fin 2) (ZMod p) := θ.comp ((autQuotient (frattini ↥P)).comp ρ)
  have hker1 : ∀ h : ↥H, χ h = 1 ↔ ρ h ∈ (autQuotient (frattini ↥P)).ker := by
    intro h
    rw [MonoidHom.mem_ker]
    change θ ((autQuotient (frattini ↥P)) (ρ h)) = 1 ↔ _
    rw [← map_one θ, hθ.eq_iff]
  have hker2 : ∀ h : ↥H, ρ h ∈ (autQuotient (frattini ↥P)).ker ↔
      ActsTriviallyOnFrattiniQuotient P (h : G) := by
    intro h
    rw [mem_ker_autQuotient]
    unfold ActsTriviallyOnFrattiniQuotient
    constructor
    · intro hx d hd
      have := hx ⟨d, hd⟩
      refine ⟨_, this, ?_⟩
      simp [ρ, MulAut.conjNormal_apply]
    · intro hx x
      obtain ⟨y, hy, hyx⟩ := hx x x.2
      have : y = x⁻¹ * ρ h x := Subtype.ext (by simpa [ρ, MulAut.conjNormal_apply] using hyx)
      rwa [← this]
  have hHperf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  have hJperf : Group.IsPerfect ↥χ.range := Group.IsPerfect.range χ
  have hJne : χ.range ≠ ⊥ := by
    intro hJ
    have hχ : ∀ h : ↥H, χ h = 1 := fun h => by
      have : χ h ∈ χ.range := ⟨h, rfl⟩
      rw [hJ] at this
      exact Subgroup.mem_bot.mp this
    have hK : ρ.range ≤ (autQuotient (frattini ↥P)).ker := by
      rintro _ ⟨h, rfl⟩
      exact (hker1 h).mp (hχ h)
    have hpK : IsPGroup p ρ.range := (isPGroup_ker_autQuotient_frattini hPp).to_le hK
    have hρperf : ⁅ρ.range, ρ.range⁆ = ρ.range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
    have hbot : ρ.range = ⊥ := eq_bot_of_perfect_of_isPGroup ρ.range hpK hρperf
    apply hPH
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hρ : ρ ⟨h, hh⟩ = 1 := by
      have : ρ ⟨h, hh⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have hc := congrArg (fun a : MulAut ↥P => ((a ⟨x, hx⟩ : ↥P) : G)) hρ
    simp only [ρ, MonoidHom.comp_apply, Subgroup.subtype_apply, MulAut.conjNormal_apply,
      MulAut.one_apply] at hc
    calc h * x = (h * x * h⁻¹) * h := by group
      _ = x * h := by rw [hc]
  refine ⟨χ.ker, inferInstance, fun h => ?_, ?_⟩
  · exact (MonoidHom.mem_ker.trans (hker1 h)).trans (hker2 h)
  · let eQ : ↥H ⧸ χ.ker ≃* ↥χ.range := QuotientGroup.quotientKerEquivRange χ
    rcases CFSG.RankThree.SubgroupLists.perfect_gl2_mulEquiv hp2 χ.range hJne with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact Or.inl ⟨eQ.trans f⟩
    · by_cases hp5 : p = 5
      · subst hp5
        exact Or.inl ⟨eQ.trans f⟩
      · right
        refine ⟨?_, ⟨eQ.trans f⟩⟩
        have h1 : Nat.card ↥χ.range ∣ Nat.card (GL (Fin 2) (ZMod p)) :=
          Subgroup.card_subgroup_dvd_card _
        have h2 : Nat.card ↥χ.range = 120 := (Nat.card_congr f.toEquiv).trans card_sl2_five
        have h5 : 5 ∣ Nat.card (GL (Fin 2) (ZMod p)) := (by norm_num : 5 ∣ 120).trans (h2 ▸ h1)
        rw [card_GL_zmod, Fin.prod_univ_two] at h5
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h5
        exact mod_five_of_dvd hp hp5 h5

end CFSG.QuasithinUnique.Vol2Native
