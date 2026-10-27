module

import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup

@[expose] def KFactOuterThreeRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex), IsRankTwoPlus d.1 →
    RankTwoList d.1 → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 2 q) →
    LieClAut.FieldExponentThree d.1 →
    (∀ q : TauCeti.PrimePower, d.1 = .G2 q → 3 ∣ q.exponent) →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∀ E : Subgroup (MulAut X), E ≤ H → IsElemAbelian 3 E → Nat.card E = 9 →
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X)))

namespace LieClAut

theorem centralizer_inf_range_le_map {Y G : Type*} [Group Y] [Finite Y] [Group G] (ρ : Y →* G)
    (hk : ¬ 3 ∣ Nat.card ρ.ker) {E : Subgroup Y} (hE : IsPGroup 3 E) :
    ρ.range ⊓ centralizer (E.map ρ : Set G) ≤ (centralizer (E : Set Y)).map ρ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  have hmem : QuotientGroup.mk' ρ.ker y ∈
      centralizer ((E.map (QuotientGroup.mk' ρ.ker) : Subgroup (Y ⧸ ρ.ker)) :
        Set (Y ⧸ ρ.ker)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h1 := mem_centralizer_iff.1 hy (ρ e) ⟨e, he, rfl⟩
    apply QuotientGroup.kerLift_injective ρ
    simpa only [map_mul, QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk] using h1
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hk hE] at hmem
  obtain ⟨c, hc, hcy⟩ := hmem
  refine ⟨c, hc, ?_⟩
  have := congrArg (QuotientGroup.kerLift ρ) hcy
  simpa only [QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk] using this

theorem injective_comp_subtype {Y G : Type*} [Group Y] [Finite Y] [Group G] (ρ : Y →* G)
    (hk : ¬ 3 ∣ Nat.card ρ.ker) {E : Subgroup Y} (hE : IsPGroup 3 E) :
    Function.Injective (ρ.comp E.subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (injective_iff_map_eq_one _).2 fun e he => ?_
  obtain ⟨k, hek⟩ := hE e
  have hker : (e : Y) ∈ ρ.ker := he
  have h1 : orderOf (⟨e, hker⟩ : ρ.ker) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one
    (Subtype.ext (by simpa using congrArg Subtype.val hek))
  have h2 : orderOf (⟨e, hker⟩ : ρ.ker) ∣ Nat.card ρ.ker := orderOf_dvd_natCard _
  have h3 : orderOf (⟨e, hker⟩ : ρ.ker) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    rcases j with _ | j
    · simpa using hj
    · exact absurd (hj ▸ h2) fun h => hk ((dvd_pow_self 3 (Nat.succ_ne_zero j)).trans h)
  have := congrArg Subtype.val (orderOf_eq_one_iff.1 h3)
  exact Subtype.ext this

theorem conj_injective_of_center {X : Type*} [Group X] (hc : center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  have hxc : x ∈ center X := mem_center_iff.2 fun y => by
    have h := congrArg (fun τ : MulAut X => τ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hc] at hxc
  exact (mem_bot.1 hxc)

theorem eq_or_eq_inv_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : a = b ∨ a = b⁻¹ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hsub : (zpowers b : Set G).toFinset ⊆ Finset.univ.filter fun x : G => x ^ 3 = 1 :=
    fun x hx => by
      rw [Set.mem_toFinset, SetLike.mem_coe, mem_zpowers_iff] at hx
      obtain ⟨n, rfl⟩ := hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hcard : (Finset.univ.filter fun x : G => x ^ 3 = 1).card ≤
      (zpowers b : Set G).toFinset.card := by
    have h3 : (zpowers b : Set G).toFinset.card = 3 := by
      rw [← Nat.card_eq_card_toFinset]
      exact (Nat.card_zpowers b).trans hbo
    rw [h3]
    exact IsCyclic.card_pow_eq_one_le (by norm_num)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have ha : a ∈ (zpowers b : Set G).toFinset := by
    rw [heq, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ha3⟩
  rw [Set.mem_toFinset, SetLike.mem_coe, mem_zpowers_iff] at ha
  obtain ⟨n, rfl⟩ := ha
  rw [← zpow_mod_orderOf, hbo] at ha1 ⊢
  have h0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h1 : n % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hcases : n % ((3 : ℕ) : ℤ) = 0 ∨ n % ((3 : ℕ) : ℤ) = 1 ∨ n % ((3 : ℕ) : ℤ) = 2 := by
    omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero] at ha1
    exact absurd rfl ha1
  · left
    rw [h, zpow_one]
  · right
    rw [h, eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact (zpow_natCast b 3).trans hb3

theorem comm_of_sylow_comm {X G' : Type*} [Group X] [Group G'] [Finite G'] (e : X ≃* G')
    (h : ∀ S : Sylow 3 G', IsMulCommutative (S : Subgroup G')) :
    ∀ P : Subgroup X, IsPGroup 3 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro P hP a ha b hb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := (hP.map e.toMonoidHom).exists_le_sylow
  have hc := (h S).is_comm.comm ⟨e a, hS ⟨a, ha, rfl⟩⟩ ⟨e b, hS ⟨b, hb, rfl⟩⟩
  apply e.injective
  simpa using congrArg Subtype.val hc

theorem three_le_pRank_of_abelian {X : Type} [Group X] [Finite X] (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H)
    (hab : ∀ P : Subgroup X, IsPGroup 3 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {β : MulAut X} (hβH : β ∈ H) (hβ3 : β ^ 3 = 1)
    (hβn : β ∉ (MulAut.conj : X →* MulAut X).range) {A : Type} [CommGroup A] [Finite A]
    (f : A →* X) (hf : Function.Injective f) (hA3 : ∀ a : A, a ^ 3 = 1) (hA : Nat.card A = 9)
    (hfix : ∀ a, β (f a) = f a) {D : Subgroup (MulAut X)}
    (hD : ∀ δ ∈ D, (∃ k : ℕ, δ ^ 3 ^ k = 1) → δ ∈ (MulAut.conj : X →* MulAut X).range)
    (hγ : ∀ γ ∈ H, γ ^ 3 = 1 → γ ∉ (MulAut.conj : X →* MulAut X).range →
      γ * β⁻¹ ∈ D ∨ γ * β ∈ D)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have hconj := conj_injective_of_center hc
  set F₀ := ((MulAut.conj : X →* MulAut X).comp f).range with hF₀
  have hF₀c : Nat.card F₀ = 9 := by
    rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective (f := (MulAut.conj : X →* MulAut X).comp f)
      (hconj.comp hf)).toEquiv).symm
  have hF₀ab : CFSG.Assembly.IsElemAbelian 3 F₀ := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      exact Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul, mul_comm a b])
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, hA3, map_one]
  have hF₀I : F₀ ≤ I := by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, rfl⟩
  have hcomm : ∀ γ ∈ F₀, γ * β = β * γ := by
    rintro _ ⟨a, rfl⟩
    ext y
    simp only [MonoidHom.comp_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      hfix]
  have hβF₀ : β ∉ F₀ := fun h => hβn (hF₀I h)
  set Q := F₀ ⊔ zpowers β with hQ
  have hQab : CFSG.Assembly.IsElemAbelian 3 Q :=
    CFSG.RankThree.PartTwo.Sec4.isElemAbelian_sup_zpowers hF₀ab hβ3 hcomm
  have hQc : Nat.card Q = 27 := by
    rw [hQ, CFSG.RankThree.PartTwo.Sec4.card_sup_zpowers_of_not_mem hβ3 hcomm hβF₀, hF₀c]
  have hQH : Q ≤ H := sup_le (hF₀I.trans hinn) ((zpowers_le).2 hβH)
  have hkey : ∀ S : Subgroup (MulAut X), S ≤ H → IsPGroup 3 S → β ∈ S → F₀ ≤ S →
      ∀ s ∈ S, s ^ 3 = 1 → ∀ x ∈ F₀, s * x = x * s := by
    intro S hSH hS hβS hF₀S
    have hSI : ∀ a ∈ S, a ∈ I → ∀ x ∈ F₀, a * x = x * a := by
      rintro _ haS ⟨a', rfl⟩ x hx
      obtain ⟨x', rfl⟩ := hF₀I hx
      have hP : IsPGroup 3 (S.comap (MulAut.conj : X →* MulAut X)) :=
        hS.comap_of_injective _ hconj
      have h1 := hab _ hP a' haS x' (hF₀S hx)
      rw [← map_mul, ← map_mul, h1]
    intro s hs hs3 x hx
    by_cases hsI : s ∈ I
    · exact hSI s hs hsI x hx
    have h2 := hcomm x hx
    have h3el : ∀ d ∈ S, ∃ k : ℕ, d ^ 3 ^ k = 1 := fun d hd => by
      obtain ⟨k, hk⟩ := hS ⟨d, hd⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    rcases hγ s (hSH hs) hs3 hsI with hd | hd
    · have hdS : s * β⁻¹ ∈ S := S.mul_mem hs (S.inv_mem hβS)
      have h1 := hSI _ hdS (hD _ hd (h3el _ hdS)) x hx
      calc s * x = (s * β⁻¹) * (β * x) := by group
        _ = (s * β⁻¹) * x * β := by rw [← h2]; group
        _ = x * (s * β⁻¹) * β := by rw [h1]
        _ = x * s := by group
    · have hdS : s * β ∈ S := S.mul_mem hs hβS
      have h1 := hSI _ hdS (hD _ hd (h3el _ hdS)) x hx
      have h2' : x * β⁻¹ = β⁻¹ * x := (Commute.inv_right (show Commute x β from h2)).eq
      calc s * x = (s * β) * (β⁻¹ * x) := by group
        _ = (s * β) * x * β⁻¹ := by rw [← h2']; group
        _ = x * (s * β) * β⁻¹ := by rw [h1]
        _ = x * s := by group
  have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 3) (by rw [hQc]; norm_num)
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hEc]; norm_num)
  obtain ⟨S₀, hS₀⟩ := (hQp.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  obtain ⟨S₁, hS₁⟩ := (hEp.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥H) S₁ S₀
  set S := (S₀ : Subgroup ↥H).map H.subtype with hS
  have hSH : S ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hSp : IsPGroup 3 S := S₀.isPGroup'.map _
  have hQS : Q ≤ S := fun x hx => ⟨⟨x, hQH hx⟩, hS₀ hx, rfl⟩
  set g : MulAut X := (h : MulAut X) with hg
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'S : E' ≤ S := by
    rintro _ ⟨e, he, rfl⟩
    have hmem : (MulAut.conj h).toMonoidHom ⟨e, hEH he⟩ ∈
        ((h • S₁ : Sylow 3 ↥H) : Subgroup ↥H) :=
      Subgroup.mem_map_of_mem _ (hS₁ (show (⟨e, hEH he⟩ : ↥H) ∈ E.comap H.subtype from he))
    rw [hh] at hmem
    exact ⟨_, hmem, by simp [hg]⟩
  have hE'ab : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE _
  have hE'c : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (MulEquiv.injective _), hEc]
  have hE'F : ∀ a ∈ E', ∀ x ∈ F₀, a * x = x * a := fun a ha x hx =>
    hkey S hSH hSp (hQS (mem_sup_right (mem_zpowers β))) (le_sup_left.trans hQS) a (hE'S ha)
      (hE'ab.2 a ha) x hx
  have hmain : ∃ F : Subgroup (MulAut X), F ≤ H ⊓ centralizer (E' : Set (MulAut X)) ∧
      IsElemAbelian 3 F ∧ ∃ k : ℕ, 3 ≤ k ∧ Nat.card F = 3 ^ k := by
    by_cases hEF : E' = F₀
    · refine ⟨Q, le_inf hQH fun q hq => ?_, hQab, 3, le_rfl, by rw [hQc]; norm_num⟩
      rw [mem_centralizer_iff]
      intro a ha
      rw [hEF] at ha
      exact congrArg Subtype.val
        (hQab.1.is_comm.comm ⟨a, le_sup_left (a := F₀) ha⟩ ⟨q, hq⟩)
    · set F₁ := E' ⊔ F₀ with hF₁
      have hF₁ab : IsElemAbelian 3 F₁ :=
        CFSG.Open.IsElemAbelian.sup_of_commute hE'ab hF₀ab hE'F
      have hF₁p : IsPGroup 3 F₁ := fun x => ⟨1, Subtype.ext (by simpa using hF₁ab.2 x x.2)⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF₁p
      refine ⟨F₁, le_inf (sup_le (hE'S.trans hSH) (le_sup_left.trans hQH)) fun y hy => ?_,
        hF₁ab, k, ?_, hk⟩
      · rw [mem_centralizer_iff]
        intro a ha
        exact congrArg Subtype.val
          (hF₁ab.1.is_comm.comm ⟨a, le_sup_left (a := E') ha⟩ ⟨y, hy⟩)
      · have hlt : F₀ < F₁ := by
          refine lt_of_le_of_ne le_sup_right fun h0 => hEF ?_
          have hle : E' ≤ F₀ := by rw [h0]; exact le_sup_left
          exact Subgroup.eq_of_le_of_card_ge hle (by rw [hE'c, hF₀c])
        have h1 : Nat.card F₀ ∣ Nat.card F₁ := Subgroup.card_dvd_of_le hlt.le
        have h2 : Nat.card F₀ < Nat.card F₁ := Subgroup.card_lt_of_lt hlt
        rw [hF₀c, hk] at *
        by_contra hk3
        interval_cases k <;> omega
  obtain ⟨F, hF, hFab, k, hk, hFc⟩ := hmain
  set F' := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hF'le : F' ≤ H ⊓ centralizer (E : Set (MulAut X)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyH := (hF hy).1
    have hyC := (hF hy).2
    have hgH : g ∈ H := h.2
    have hcj : (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := by simp
    rw [hcj]
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hgH) hyH) hgH, ?_⟩
    show g⁻¹ * y * g ∈ centralizer (E : Set (MulAut X))
    rw [mem_centralizer_iff]
    intro e he
    have h1 := mem_centralizer_iff.1 hyC (g * e * g⁻¹) ⟨e, he, by simp⟩
    calc e * (g⁻¹ * y * g) = g⁻¹ * ((g * e * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * e * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * y * g * e := by group
  exact hk.trans (CFSG.SectionRank.le_pRank (by norm_num) hF'le
    (CFSG.SectionRank.isElemAbelian_map hFab _)
    (by rw [hF', Subgroup.card_map_of_injective (MulEquiv.injective _), hFc]))

end LieClAut

theorem kFactTenElevenOneLieAutFieldTwo_of_rankTwo (h : KFactOuterThreeRankTwo) :
    KFactTenElevenOneLieAutFieldTwo := by
  intro Y _ _ L hLn hq hO2 d hd hl hA2 h3 hG he hu hJ hC3 hrk hE hN
  haveI := hLn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  set ρ := LieClAut.conjQuot L with hρ
  have hker : ρ.ker ≤ centralizer (L : Set Y) := fun y hy =>
    LieClAut.mem_centralizer_of_conjQuot_eq_one inferInstance hy
  have hinn : (MulAut.conj : ↥L ⧸ center ↥L →* MulAut (↥L ⧸ center ↥L)).range ≤ ρ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨(l : Y), LieClAut.conjQuot_apply_mem l⟩
  obtain ⟨u, ⟨k, hk⟩, huLC⟩ := hu
  have hout : ρ u ∉ (MulAut.conj : ↥L ⧸ center ↥L →* MulAut (↥L ⧸ center ↥L)).range := by
    rintro ⟨x, hx⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    apply huLC
    have h1 : ρ ((l : Y)⁻¹ * u) = 1 := by
      rw [map_mul, map_inv, ← hx, LieClAut.conjQuot_apply_mem, inv_mul_cancel]
    have h2 := hker h1
    have : u = (l : Y) * ((l : Y)⁻¹ * u) := by group
    rw [this]
    exact Subgroup.mul_mem_sup l.2 h2
  have hk3 : ¬ 3 ∣ Nat.card ρ.ker := fun h =>
    hC3 (h.trans (Subgroup.card_dvd_of_le hker))
  obtain ⟨E₀, hE₀, hE₀c, hE₀r⟩ := hE
  have hE₀p : IsPGroup 3 E₀ := IsPGroup.of_card (n := 2) (by rw [hE₀c]; norm_num)
  have hcard : Nat.card (E₀.map ρ) = 9 := by
    have hr : (ρ.comp E₀.subtype).range = E₀.map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← hE₀c]
    exact (Nat.card_congr (MonoidHom.ofInjective
      (LieClAut.injective_comp_subtype ρ hk3 hE₀p)).toEquiv).symm
  have h3r := h _ d hd hl hA2 h3 hG he (LieClAut.center_quotient_eq_bot hq) ρ.range hinn
    ⟨ρ u, ⟨u, rfl⟩, ⟨k, by rw [← map_pow, hk, map_one]⟩, hout⟩ (E₀.map ρ)
    (map_le_range ρ E₀) (CFSG.SectionRank.isElemAbelian_map hE₀ ρ) hcard
  have h1 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (LieClAut.centralizer_inf_range_le_map ρ hk3 hE₀p)
  have h2 := TenElevenOneLie.pRank_map_le Nat.prime_three ρ hk3 (centralizer (E₀ : Set Y))
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
