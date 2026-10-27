module

public import CFSG.LocalAnalysis.RankTwoShapes.CentralMovement
public import CFSG.LocalAnalysis.RankTwoShapes.ThreeAutomorphism
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourSylow
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour
public import CFSG.LocalAnalysis.RankTwoShapes.AbelianRadical.Wreathed
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.Overgroup

public section

namespace CFSG.RankTwoShapes

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sq_eq_one_of_klein (v : Multiplicative (ZMod (2 ^ 1)) × Multiplicative (ZMod (2 ^ 1))) :
    v ^ 2 = 1 := by
  revert v
  decide

theorem elementary_card_le_four_of_twoRank (h : CFSG.Assembly.twoRank G = 2) (E : Subgroup G)
    (hE : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by simpa using hexp e e.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro r ⟨E', -, -, hcard⟩
    have hle := E'.card_le_card_group
    rw [hcard] at hle
    exact (Nat.lt_two_pow_self (n := r)).le.trans hle
  have hmem : k ∈ {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := ⟨E, le_top, ⟨hE, hexp⟩, hk⟩
  have hle : k ≤ 2 := by
    have := le_csSup hbdd hmem
    unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank at h
    omega
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 4 := by norm_num

theorem exists_elementary_four_of_twoRank (h : CFSG.Assembly.twoRank G = 2) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  have hne : {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k}.Nonempty := by
    refine ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by
      rw [Subgroup.mem_bot] at hx; rw [hx, one_pow]⟩, by simp⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro r ⟨E', -, -, hcard⟩
    have hle := E'.card_le_card_group
    rw [hcard] at hle
    exact (Nat.lt_two_pow_self (n := r)).le.trans hle
  obtain ⟨E, -, hE, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨E, hE, ?_⟩
  unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank at h
  rw [hcard, h]
  norm_num

theorem rank_two_sylow_shapes_of_unitary_exclusion
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : CFSG.Assembly.twoRank G = 2) (S : Sylow 2 G)
    (hunit : ∀ Q : Subgroup G, IsAlperinSubgroup 2 (S : Subgroup G) Q →
      (∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
        CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
          Nonempty (Q ≃* (U : Subgroup H))) →
      3 ∣ ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf
        (Subgroup.normalizer (Q : Set G))).index →
      Q = (S : Subgroup G)) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* DihedralGroup (2 ^ (n - 1)))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) ∨
    (∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty ((S : Subgroup G) ≃* (U : Subgroup H))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Sg := (S : Subgroup G) with hSg
  have hrankS : ∀ E : Subgroup G, E ≤ Sg → IsMulCommutative E → (∀ e ∈ E, e ^ 2 = 1) →
      Nat.card E ≤ 4 := fun E _ hE hexp => elementary_card_le_four_of_twoRank hrank E hE hexp
  obtain ⟨E₀, -, hE₀card⟩ := exists_elementary_four_of_twoRank hrank
  have h2G : 2 ∣ Nat.card G := by
    have := E₀.card_subgroup_dvd_card
    rw [hE₀card] at this
    exact dvd_trans (by norm_num : 2 ∣ 4) this
  have hSne : Sg ≠ ⊥ := S.ne_bot_of_dvd_card h2G
  have : Nontrivial Sg := (Subgroup.nontrivial_iff_ne_bot Sg).mpr hSne
  have hZnt : Nontrivial (Subgroup.center Sg) := S.isPGroup'.center_nontrivial
  have hZ2 : 2 ∣ Nat.card (Subgroup.center Sg) := by
    rcases (S.isPGroup'.to_subgroup (Subgroup.center Sg)).card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card).ne'
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Sg) 2 hZ2
  set zS : Sg := (z : Sg) with hzSdef
  have hzZ : zS ∈ Subgroup.center Sg := z.2
  have hzord : orderOf zS = 2 := by rw [hzSdef, Subgroup.orderOf_coe, hz]
  obtain ⟨g, hgS, hgz⟩ := simple_central_sylow_involution_movement hnonab S zS hzZ hzord
  obtain ⟨Q, hQ, hzQ, n, hnN, hnz⟩ := exists_alperinSubgroup_moving S (x := (zS : G)) zS.2 hgS hgz
  have hQ' := hQ
  obtain ⟨hQS, hcop, hcent, -⟩ := hQ'
  set NQ := Subgroup.normalizer (Q : Set G) with hNQ
  set φ : NQ →* MulAut Q := Q.normalizerMonoidHom with hφ
  have hφapply : ∀ (m : NQ) (q : Q), ((φ m q : Q) : G) = (m : G) * q * (m : G)⁻¹ :=
    fun m q => rfl
  set A : Subgroup (MulAut Q) := φ.range with hA
  have hQp : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  have hQrank : TwoRankLeTwo Q := by
    intro E hE hexp
    have hmap : Nat.card (E.map Q.subtype) = Nat.card E :=
      Subgroup.card_map_of_injective Q.subtype_injective
    rw [← hmap]
    apply hrankS
    · rintro _ ⟨e, -, rfl⟩; exact hQS e.2
    · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      obtain ⟨ea, hea, hea'⟩ := a.2
      obtain ⟨eb, heb, heb'⟩ := b.2
      have hc := congrArg (fun x : E => ((x : Q) : G)) (hE.is_comm.comm ⟨ea, hea⟩ ⟨eb, heb⟩)
      simp only [Subgroup.coe_mul] at hc
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hea', ← heb']
      exact hc
    · rintro _ ⟨e, he, rfl⟩
      have h := congrArg Subtype.val (hexp e he)
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
  set P₀ : Subgroup NQ := (Sg ⊓ NQ).subgroupOf NQ with hP₀
  have hP₀p : IsPGroup 2 P₀ :=
    (S.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hP₀idx : ¬ 2 ∣ P₀.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop
  set P₀s : Sylow 2 NQ := hP₀p.toSylow hP₀idx with hP₀s
  set B : Sylow 2 A := P₀s.mapSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    with hBdef
  set zQ : Q := ⟨(zS : G), hzQ⟩ with hzQdef
  have hzSc : ∀ s ∈ Sg, s * (zS : G) = (zS : G) * s := by
    intro s hs
    have := Subgroup.mem_center_iff.mp hzZ ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hB : ∀ b ∈ (B : Subgroup A), ((b : A) : MulAut Q) zQ = zQ := by
    intro b hb
    rw [hBdef, Sylow.coe_mapSurjective] at hb
    obtain ⟨m, hm, rfl⟩ := hb
    have hm' : m ∈ P₀ := by
      have h1 : m ∈ ((hP₀p.toSylow hP₀idx : Sylow 2 NQ) : Subgroup NQ) := hm
      rwa [IsPGroup.toSylow_coe] at h1
    have hmS : (m : G) ∈ Sg := (Subgroup.mem_subgroupOf.mp hm').1
    apply Subtype.ext
    change (m : G) * (zS : G) * (m : G)⁻¹ = zS
    rw [hzSc _ hmS, mul_inv_cancel_right]
  have hmove : ∃ a ∈ A, a zQ ≠ zQ := by
    refine ⟨φ ⟨n⁻¹, NQ.inv_mem hnN⟩, ⟨_, rfl⟩, ?_⟩
    intro h
    apply hnz
    have h' := congrArg Subtype.val h
    change n⁻¹ * (zS : G) * n⁻¹⁻¹ = zS at h'
    rwa [inv_inv] at h'
  have hzZQ : zQ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    exact hzSc q (hQS q.2)
  have hzQord : orderOf zQ = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (zS : G) = 2
    rw [Subgroup.orderOf_coe, hzord]
  obtain ⟨-, -, α, hαA, hα3, -, hαfpf⟩ :=
    central_involution_three_automorphism hQp hQrank A B hzZQ hzQord hB hmove
  have hα3' : α ^ 3 = 1 := by rw [← hα3]; exact pow_orderOf_eq_one α
  by_cases hQab : IsMulCommutative Q
  ·
    have hQcomm : ∀ a b : Q, a * b = b * a := fun a b => hQab.is_comm.comm a b
    obtain ⟨x, hxmax⟩ := Finite.exists_max (fun y : Q => orderOf y)
    obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hQp) x
    have he1 : 1 ≤ e := by
      by_contra h0
      have he0 : e = 0 := by omega
      have h2 := hxmax zQ
      rw [hzQord, he, he0, pow_zero] at h2
      omega
    obtain ⟨-, -, ⟨eA⟩, -, -, -, htop⟩ :=
      three_automorphism_homocyclic_subgroup hQp hQrank α hα3' hαfpf x hxmax he he1
    have eQ : Q ≃* Multiplicative (ZMod (2 ^ e)) × Multiplicative (ZMod (2 ^ e)) :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr (htop hQcomm)).symm.trans eA)
    have hQcard : Nat.card Q = 4 ^ e := by
      rw [Nat.card_congr eQ.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
        Nat.card_zmod, ← mul_pow]
      norm_num
    by_cases hQeq : Q = Sg
    ·
      have eS : Sg ≃* Multiplicative (ZMod (2 ^ e)) × Multiplicative (ZMod (2 ^ e)) :=
        (MulEquiv.subgroupCongr hQeq).symm.trans eQ
      have he' : e = 1 := homocyclic_sylow_simple_exponent_two hnonab S e he1 ⟨eS⟩
      subst he'
      have hScard : Nat.card Sg = 4 := by rw [← hQeq, hQcard]; norm_num
      have hC2 := sq_eq_one_of_klein
      have hSexp : ∀ s : Sg, s ^ 2 = 1 := by
        intro s
        apply eS.injective
        rw [map_pow, map_one]
        exact hC2 _
      have hSab : ∀ a b : Sg, a * b = b * a := by
        intro a b
        have hQab' := hQcomm ⟨a, hQeq ▸ a.2⟩ ⟨b, hQeq ▸ b.2⟩
        exact Subtype.ext (congrArg (fun x : Q => (x : G)) hQab')
      have hcentS : Subgroup.centralizer ((⊤ : Subgroup Sg) : Set Sg) = ⊤ := by
        rw [eq_top_iff]
        intro s _
        rw [Subgroup.mem_centralizer_iff]
        intro t _
        exact hSab t s
      rcases selfCentralizing_four_shapes S.isPGroup' (⊤ : Subgroup Sg)
          ⟨⟨fun a b => Subtype.ext (hSab a b)⟩⟩ (fun v _ => hSexp v)
          (by rw [Subgroup.card_top]; exact hScard) hcentS with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hQlt : Q < Sg := lt_of_le_of_ne hQS hQeq
    by_cases hQ4 : Nat.card Q = 4
    ·
      have he' : e = 1 := by
        rw [hQcard] at hQ4
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) (hQ4.trans (pow_one 4).symm)
      subst he'
      have hC2 := sq_eq_one_of_klein
      have hQexp : ∀ q : Q, q ^ 2 = 1 := by
        intro q
        apply eQ.injective
        rw [map_pow, map_one]
        exact hC2 _
      set V : Subgroup Sg := Q.subgroupOf Sg with hV
      have hVab : IsMulCommutative V := by
        refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
        have h := hQcomm ⟨((a : Sg) : G), Subgroup.mem_subgroupOf.mp a.2⟩
          ⟨((b : Sg) : G), Subgroup.mem_subgroupOf.mp b.2⟩
        exact congrArg (fun x : Q => (x : G)) h
      have hVexp : ∀ v ∈ V, v ^ 2 = 1 := by
        intro v hv
        have h := congrArg Subtype.val (hQexp ⟨(v : G), Subgroup.mem_subgroupOf.mp hv⟩)
        rw [Subgroup.coe_pow, Subgroup.coe_one] at h
        exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h)
      have hVcard : Nat.card V = 4 := by
        rw [hV, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv, hQ4]
      have hVcent : Subgroup.centralizer (V : Set Sg) = V := by
        apply le_antisymm
        · intro s hs
          rw [hV, Subgroup.mem_subgroupOf]
          apply hcent
          refine ⟨?_, s.2⟩
          show (s : G) ∈ Subgroup.centralizer (Q : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro q hq
          have h := (Subgroup.mem_centralizer_iff.mp hs) ⟨q, hQS hq⟩
            (Subgroup.mem_subgroupOf.mpr hq)
          exact congrArg Subtype.val h
        · intro v hv
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          exact hVab.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩ |> congrArg Subtype.val
      rcases selfCentralizing_four_shapes S.isPGroup' V hVab hVexp hVcard hVcent with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    ·
      have hQgt : 4 < Nat.card Q := by
        have h4 : 4 ≤ 4 ^ e := by
          calc 4 = 4 ^ 1 := by norm_num
            _ ≤ 4 ^ e := Nat.pow_le_pow_right (by norm_num) he1
        omega
      exact Or.inr (Or.inr (Or.inl (abelian_alperin_wreathed S Q hQ hQab hQlt hQgt hrankS)))
  ·
    have hnonabQ : ∃ a b : Q, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hQab ⟨⟨fun a b => h a b⟩⟩
    have hU := free_three_action_unitary_sylow hQp hQrank hnonabQ α hα3' hαfpf
    have h3 : 3 ∣ ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf NQ).index := by
      set M := (Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf NQ with hM
      set ψ := φ.rangeRestrict with hψ
      have hCN : Subgroup.centralizer (Q : Set G) ≤ NQ := Subgroup.centralizer_le_normalizer _
      have hQN : Q ≤ NQ := Subgroup.le_normalizer
      have hkerψ : ψ.ker = (Subgroup.centralizer (Q : Set G)).subgroupOf NQ := by
        rw [hψ, MonoidHom.ker_rangeRestrict, hφ, Subgroup.normalizerMonoidHom_ker]
      have hker : ψ.ker ≤ M := by
        rw [hkerψ, hM, Subgroup.subgroupOf_sup hQN hCN]
        exact le_sup_right
      have hidx := Subgroup.index_map_eq (f := ψ) M φ.rangeRestrict_surjective hker
      have hMmap : M.map ψ = (Q.subgroupOf NQ).map ψ := by
        rw [hM, Subgroup.subgroupOf_sup hQN hCN, Subgroup.map_sup, ← hkerψ,
          (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
      have hMp : IsPGroup 2 (M.map ψ) := by
        rw [hMmap]
        exact (hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm).map ψ
      obtain ⟨k, hk⟩ := hMp.exists_card_eq
      have h3A : 3 ∣ Nat.card A := by
        have := orderOf_dvd_natCard (⟨α, hαA⟩ : A)
        rwa [Subgroup.orderOf_mk, hα3] at this
      have hA := Subgroup.card_mul_index (M.map ψ)
      rw [hk] at hA
      have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
      rw [← hidx]
      have h3' : 3 ∣ 2 ^ k * (M.map ψ).index := by
        rw [hA]; exact h3A
      exact hcop.dvd_of_dvd_mul_left h3'
    have hQeq := hunit Q hQ hU h3
    obtain ⟨H, hHgrp, U, hH, ⟨eQ⟩⟩ := hU
    exact Or.inr (Or.inr (Or.inr ⟨H, hHgrp, U, hH,
      ⟨(MulEquiv.subgroupCongr hQeq).symm.trans eQ⟩⟩))

theorem rank_two_sylow_shapes
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : CFSG.Assembly.twoRank G = 2) (S : Sylow 2 G) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* DihedralGroup (2 ^ (n - 1)))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) ∨
    (∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty ((S : Subgroup G) ≃* (U : Subgroup H))) :=
  rank_two_sylow_shapes_of_unitary_exclusion hnonab hrank S fun Q hQ hU h3 =>
    unitary_alperin_eq_sylow S Q hQ hU h3 fun E _ hE hexp =>
      elementary_card_le_four_of_twoRank hrank E hE hexp

end CFSG.RankTwoShapes
