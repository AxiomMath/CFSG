module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.ThreeData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoCentral

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

@[expose] def conjTab (n : List (Fin 45)) (t : Tab) : Tab := tmul (tmul (wtab n) t) (wtab n.reverse)

theorem rep_conj (n : List (Fin 45)) {g : Equiv.Perm (Fin 45)} {t : Tab} (hr : Rep g t) :
    Rep (wperm n * g * (wperm n)⁻¹) (conjTab n t) := by
  rw [wperm_inv]
  exact rep_mul (rep_mul (rep_wperm n) hr) (rep_wperm _)

theorem P3_cent : P3elems.all (fun t => Q0elems.contains t ||
    decide ((P3elems.filter (commB t)).length ≤ 9)) = true := by
  decide +kernel

theorem c_central : P3gens.all (fun w => commB (wtab cW) (wtab w)) = true := by
  decide +kernel

@[expose] def classOK (i : ℕ) : Bool :=
  match Q0type.getD i 0 with
  | 0 => Q0elems.getD i [] == tid
  | 1 => conjTab (Q0conj.getD i []) (Q0elems.getD i []) == wtab cW ||
      conjTab (Q0conj.getD i []) (Q0elems.getD i []) == tmul (wtab cW) (wtab cW)
  | 2 => conjTab (Q0conj.getD i []) (Q0elems.getD i []) == wtab e0W
  | 3 => conjTab (Q0conj.getD i []) (Q0elems.getD i []) == wtab x0W &&
      normB [Q0conj.getD i []] Q0elems
  | _ => false

theorem Q0_class : (List.range Q0elems.length).all classOK = true := by
  decide +kernel

theorem e0_fix : (List.range 45).all (fun j => !((wtab e0W).getD j 0 == j) ||
    [15, 25, 35].contains j) = true := by
  decide +kernel

@[expose] def e0OK (d : ℕ × List (Fin 45) × ℕ × ℕ) : Bool :=
  ((wtab d.2.1).getD d.1 0 == 0) && decide (d.2.2.1 < Eelems.length) &&
  decide (d.2.2.2 < Kelems.length) &&
  (conjTab d.2.1 (wtab e0W) == tmul (Eelems.getD d.2.2.1 []) (Kelems.getD d.2.2.2 [])) &&
  (Eelems.all fun t => !commB t (conjTab d.2.1 (wtab e0W)) || [tid, tau0Tab].contains t) &&
  (Kelems.all fun t => !(commB t (Kelems.getD d.2.2.2 []) && tmul t t == tid) || t == tid)

theorem e0_data : e0data.all e0OK = true ∧ e0data.map (·.1) = [15, 25, 35] := by
  decide +kernel

theorem card_le_of_tables {H : Subgroup (Equiv.Perm (Fin 45))} {l : List Tab}
    (h : ∀ g ∈ H, ∃ t ∈ l, Rep g t) : Nat.card H ≤ l.length := by
  classical
  choose f hfl hfr using fun g : H => h g g.2
  let F : H → l.toFinset := fun g => ⟨f g, List.mem_toFinset.2 (hfl g)⟩
  have hF : Function.Injective F := by
    intro a b hab
    have e : f a = f b := congrArg Subtype.val hab
    exact Subtype.ext (rep_unique (hfr a) (e ▸ hfr b))
  have h1 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card (α := l.toFinset), Fintype.card_coe] at h1
  exact h1.trans (List.toFinset_card_le l)

theorem mem_sylow_of_central {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {C : Subgroup G} {x : G} (hxC : x ∈ C) (hcomm : ∀ c ∈ C, c * x = x * c) (hx : x ^ p = 1)
    (S : Sylow p C) : x ∈ (S.toSubgroup).map C.subtype := by
  have hnor : (zpowers (⟨x, hxC⟩ : C)).Normal := by
    constructor
    intro n hn c
    have hcz : c * ⟨x, hxC⟩ * c⁻¹ = ⟨x, hxC⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm c c.2, mul_inv_cancel_right]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hcz]
    exact zpow_mem_zpowers _ k
  have hdvd : orderOf (⟨x, hxC⟩ : C) ∣ p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one hx
  have hp : IsPGroup p (zpowers (⟨x, hxC⟩ : C)) := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  exact ⟨⟨x, hxC⟩, hp.le_sylow_of_normal S (mem_zpowers _), rfl⟩

theorem card_centralizer_conj {g : Equiv.Perm (Fin 45)} (hg : g ∈ P) (k : Equiv.Perm (Fin 45)) :
    Nat.card ↥(P ⊓ centralizer ({g * k * g⁻¹} : Set (Equiv.Perm (Fin 45)))) =
      Nat.card ↥(P ⊓ centralizer ({k} : Set (Equiv.Perm (Fin 45)))) := by
  rw [P_inf_centralizer_conj hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]

abbrev Q0 : Subgroup (Equiv.Perm (Fin 45)) := gen (Q0gens.map wperm)

abbrev P3 : Subgroup (Equiv.Perm (Fin 45)) := gen (P3gens.map wperm)

theorem card_Q0 : Nat.card Q0 = 27 := (card_gen_words Q0_enumOK).trans (by decide)
theorem card_P3 : Nat.card P3 = 81 := (card_gen_words P3_enumOK).trans (by decide)
theorem Q0_le_P : Q0 ≤ P := gen_words_le_P Q0gens
theorem P3_le_P : P3 ≤ P := gen_words_le_P P3gens

theorem Q0_le_P3 : Q0 ≤ P3 := by
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_setOf_eq, List.mem_map] at hg ⊢
  obtain ⟨w, hw, rfl⟩ := hg
  exact ⟨w, by simp [P3gens, Q0gens] at hw ⊢; tauto, rfl⟩

theorem card_P3_eq : Nat.card P3 = 3 ^ (Nat.card P).factorization 3 := by
  rw [card_P3, card_P, factorization_three_25920]
  norm_num

theorem card_centralizer_P3_le {p : Equiv.Perm (Fin 45)} (hp : p ∈ P3) (hpQ : p ∉ Q0) :
    Nat.card ↥(P3 ⊓ centralizer ({p} : Set (Equiv.Perm (Fin 45)))) ≤ 9 := by
  obtain ⟨t, ht, hr⟩ := exists_mem_tab P3_enumOK hp
  have h1 := List.all_eq_true.1 P3_cent t ht
  have hQ : Q0elems.contains t = false := by
    by_contra hc
    exact hpQ (mem_gen_of_mem_tab Q0_enumOK (List.contains_iff_mem.1 (Bool.not_eq_false _ ▸ hc)) hr)
  rw [hQ, Bool.false_or, decide_eq_true_eq] at h1
  refine (card_le_of_tables fun g hg => ?_).trans h1
  obtain ⟨s, hs, hsr⟩ := exists_mem_tab P3_enumOK hg.1
  refine ⟨s, List.mem_filter.2 ⟨hs, ?_⟩, hsr⟩
  have hc : g * p = p * g := mem_centralizer_singleton_iff.1 hg.2
  rw [commB, beq_iff_eq]
  exact rep_eq_tab (rep_mul hr hsr) (hc ▸ rep_mul hsr hr)

theorem c_mem_P : wperm cW ∈ P := wperm_mem cW

theorem P3_le_centralizer_c : P3 ≤ centralizer ({wperm cW} : Set (Equiv.Perm (Fin 45))) := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_setOf_eq, List.mem_map] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  have h1 := List.all_eq_true.1 c_central w hw
  rw [commB, beq_iff_eq] at h1
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact (rep_unique (rep_mul (rep_wperm cW) (rep_wperm w))
    (h1 ▸ rep_mul (rep_wperm w) (rep_wperm cW))).symm

theorem dvd_card_centralizer_c_pow (k : ℕ) :
    81 ∣ Nat.card ↥(P ⊓ centralizer ({wperm cW ^ k} : Set (Equiv.Perm (Fin 45)))) := by
  have hle : P3 ≤ P ⊓ centralizer ({wperm cW ^ k} : Set (Equiv.Perm (Fin 45))) := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨P3_le_P hg, ?_⟩
    have hc := mem_centralizer_singleton_iff.1 (P3_le_centralizer_c hg)
    rw [mem_centralizer_singleton_iff]
    exact ((Commute.pow_left hc.symm k).eq).symm
  rw [← card_P3]
  exact Subgroup.card_dvd_of_le hle

theorem exists_common_fixed {p : ℕ} [Fact p.Prime] {V : Subgroup (Equiv.Perm (Fin 45))}
    (hV : IsPGroup p V) {f : Equiv.Perm (Fin 45)} (hcomm : ∀ v ∈ V, v * f = f * v)
    (hcard : ¬ p ∣ Nat.card {j : Fin 45 // f j = j}) :
    ∃ j, f j = j ∧ ∀ v ∈ V, v j = j := by
  have hmem : ∀ v : V, ∀ j : {j : Fin 45 // f j = j}, f ((v : Equiv.Perm (Fin 45)) j.1) =
      (v : Equiv.Perm (Fin 45)) j.1 := by
    intro v j
    have := congrArg (fun σ : Equiv.Perm (Fin 45) => σ j.1) (hcomm v v.2)
    simp only [Equiv.Perm.mul_apply, j.2] at this
    exact this.symm
  letI : MulAction V {j : Fin 45 // f j = j} :=
    { smul := fun v j => ⟨(v : Equiv.Perm (Fin 45)) j.1, hmem v j⟩
      one_smul := fun j => rfl
      mul_smul := fun v w j => rfl }
  obtain ⟨⟨j, hj⟩, hfix⟩ := hV.nonempty_fixed_point_of_prime_not_dvd_card _ hcard
  refine ⟨j, hj, fun v hv => ?_⟩
  have := hfix ⟨v, hv⟩
  exact congrArg Subtype.val this

theorem card_fix_e0 : Nat.card {j : Fin 45 // wperm e0W j = j} = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem comm_K_of_comm {e₁ e₂ k₁ k₂ : Equiv.Perm (Fin 45)} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (h : e₁ * k₁ * (e₂ * k₂) = e₂ * k₂ * (e₁ * k₁)) :
    k₁ * k₂ = k₂ * k₁ := by
  have hn₁ := K_le_normalizer_E hk₁
  have hn₂ := K_le_normalizer_E hk₂
  have h1 : k₁ * e₂ * k₁⁻¹ ∈ E := (mem_normalizer_iff.1 hn₁ e₂).1 he₂
  have h2 : k₂ * e₁ * k₂⁻¹ ∈ E := (mem_normalizer_iff.1 hn₂ e₁).1 he₁
  have key : (e₂ * (k₂ * e₁ * k₂⁻¹))⁻¹ * (e₁ * (k₁ * e₂ * k₁⁻¹)) = k₂ * k₁ * (k₁ * k₂)⁻¹ := by
    have h' : e₁ * (k₁ * e₂ * k₁⁻¹) * (k₁ * k₂) = e₂ * (k₂ * e₁ * k₂⁻¹) * (k₂ * k₁) := by
      calc e₁ * (k₁ * e₂ * k₁⁻¹) * (k₁ * k₂) = e₁ * k₁ * (e₂ * k₂) := by group
        _ = e₂ * k₂ * (e₁ * k₁) := h
        _ = e₂ * (k₂ * e₁ * k₂⁻¹) * (k₂ * k₁) := by group
    calc (e₂ * (k₂ * e₁ * k₂⁻¹))⁻¹ * (e₁ * (k₁ * e₂ * k₁⁻¹))
        = (e₂ * (k₂ * e₁ * k₂⁻¹))⁻¹ * (e₁ * (k₁ * e₂ * k₁⁻¹) * (k₁ * k₂)) * (k₁ * k₂)⁻¹ := by
          group
      _ = (e₂ * (k₂ * e₁ * k₂⁻¹))⁻¹ * (e₂ * (k₂ * e₁ * k₂⁻¹) * (k₂ * k₁)) * (k₁ * k₂)⁻¹ := by
          rw [h']
      _ = k₂ * k₁ * (k₁ * k₂)⁻¹ := by group
  have hE : k₂ * k₁ * (k₁ * k₂)⁻¹ ∈ E := key ▸ mul_mem (inv_mem (mul_mem he₂ h2)) (mul_mem he₁ h1)
  have hK : k₂ * k₁ * (k₁ * k₂)⁻¹ ∈ K := mul_mem (mul_mem hk₂ hk₁) (inv_mem (mul_mem hk₁ hk₂))
  have := eq_one_of_mem_E_of_mem_K hE hK
  rw [mul_inv_eq_one] at this
  exact this.symm

theorem pow_mem_E_mul {e k : Equiv.Perm (Fin 45)} (he : e ∈ E) (hk : k ∈ K) :
    ∀ n : ℕ, (e * k) ^ n * (k ^ n)⁻¹ ∈ E
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mem_E_mul he hk n
    have hkn : k ^ n ∈ K := pow_mem hk n
    have h1 : (k ^ n) * e * (k ^ n)⁻¹ ∈ E :=
      (mem_normalizer_iff.1 (K_le_normalizer_E hkn) e).1 he
    have : (e * k) ^ (n + 1) * (k ^ (n + 1))⁻¹ =
        ((e * k) ^ n * (k ^ n)⁻¹) * ((k ^ n) * e * (k ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [this]
    exact mul_mem ih h1

theorem card_ne_108_e0 :
    Nat.card ↥(P ⊓ centralizer ({wperm e0W} : Set (Equiv.Perm (Fin 45)))) ≠ 108 := by
  intro h108
  set C := P ⊓ centralizer ({wperm e0W} : Set (Equiv.Perm (Fin 45)))
  obtain ⟨S'⟩ : Nonempty (Sylow 2 C) := inferInstance
  set V := (S'.toSubgroup).map C.subtype with hVdef
  have hVC : V ≤ C := Subgroup.map_subtype_le _
  have hfac : (108 : ℕ).factorization 2 = 2 := by
    rw [show (108 : ℕ) = 2 ^ 2 * 27 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hVcard : Nat.card V = 4 := by
    rw [hVdef, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity,
      h108, hfac]
    norm_num
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  have hVcomm : ∀ v ∈ V, v * wperm e0W = wperm e0W * v := fun v hv =>
    mem_centralizer_singleton_iff.1 (hVC hv).2
  obtain ⟨j, hj, hVj⟩ := exists_common_fixed hVp hVcomm (by rw [card_fix_e0]; norm_num)
  have hj' : j.1 ∈ [15, 25, 35] := by
    have h1 := List.all_eq_true.1 e0_fix j.1 (List.mem_range.2 j.2)
    have h2 : (wtab e0W).getD j.1 0 = j.1 := by
      rw [← (rep_wperm e0W).2 j.1 j.2]
      exact congrArg Fin.val hj
    rw [h2, beq_self_eq_true, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h1
    exact h1
  obtain ⟨d, hd, hdj⟩ : ∃ d ∈ e0data, d.1 = j.1 := by
    have := e0_data.2
    rw [← this] at hj'
    obtain ⟨d, hd, hdj⟩ := List.mem_map.1 hj'
    exact ⟨d, hd, hdj⟩
  have hok := List.all_eq_true.1 e0_data.1 d hd
  simp only [e0OK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hc0, hei⟩, hki⟩, hdec⟩, hcE⟩, hcK⟩ := hok
  set c := wperm d.2.1
  set e' := c * wperm e0W * c⁻¹
  have hcP : c ∈ P := wperm_mem _
  have hc0' : c j = 0 := by
    apply Fin.ext
    rw [(rep_wperm d.2.1).2 j.1 j.2, ← hdj]
    exact hc0
  have he'r : Rep e' (conjTab d.2.1 (wtab e0W)) := rep_conj d.2.1 (rep_wperm e0W)
  obtain ⟨ε, hεE, hεr⟩ := exists_mem_rep_of_enumOK (length_words Egens) (rep_words Egens)
    E_enumOK _ hei
  obtain ⟨κ, hκK, hκr⟩ := exists_mem_rep_of_enumOK (length_words Kgens) (rep_words Kgens)
    K_enumOK _ hki
  have he'eq : e' = ε * κ := rep_unique he'r (hdec ▸ rep_mul hεr hκr)
  set V' := V.map (MulAut.conj c).toMonoidHom
  have hV'card : Nat.card V' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hVcard]
  have hV'H0 : ∀ v' ∈ V', v' ∈ H0 := by
    rintro _ ⟨v, hv, rfl⟩
    have hvP : v ∈ P := (hVC hv).1
    have hvP' : c * v * c⁻¹ ∈ P := mul_mem (mul_mem hcP hvP) (inv_mem hcP)
    refine ⟨hvP', (mem_centralizer_tauPerm_iff hvP' 0).2 ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Equiv.Perm.mul_apply]
    have hcinv : c⁻¹ 0 = j := by
      rw [← hc0', ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    rw [hcinv, hVj v hv, hc0']
  have hV'comm : ∀ v' ∈ V', v' * e' = e' * v' := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e']
    have := hVcomm v hv
    calc c * v * c⁻¹ * (c * wperm e0W * c⁻¹) = c * (v * wperm e0W) * c⁻¹ := by group
      _ = c * (wperm e0W * v) * c⁻¹ := by rw [this]
      _ = c * wperm e0W * c⁻¹ * (c * v * c⁻¹) := by group
  have hV'sub : ∀ v' ∈ V', v' = 1 ∨ v' = tauPerm 0 := by
    intro v' hv'
    obtain ⟨ε₁, hε₁, κ₁, hκ₁, hv'eq⟩ := exists_mul_eq_of_mem_H0 (hV'H0 v' hv')
    have hκcomm : κ₁ * κ = κ * κ₁ := by
      apply comm_K_of_comm hε₁ hεE hκ₁ hκK
      rw [hv'eq, ← he'eq]
      exact hV'comm v' hv'
    have hv'4 : v' ^ 4 = 1 := by
      have := pow_card_eq_one' (G := V') (x := ⟨v', hv'⟩)
      have h2 := congrArg Subtype.val this
      simpa [hV'card] using h2
    have hκ4 : κ₁ ^ 4 = 1 := by
      have h1 := pow_mem_E_mul hε₁ hκ₁ 4
      rw [hv'eq, hv'4, one_mul] at h1
      have h2 := eq_one_of_mem_E_of_mem_K (inv_mem_iff.1 h1) (pow_mem hκ₁ 4)
      exact h2
    have hκ2 : κ₁ * κ₁ = 1 := by
      have hdvd18 : orderOf κ₁ ∣ 18 := by
        rw [← card_K]
        have := orderOf_dvd_natCard (⟨κ₁, hκ₁⟩ : K)
        rwa [Subgroup.orderOf_mk] at this
      have hdvd4 : orderOf κ₁ ∣ 4 := orderOf_dvd_of_pow_eq_one hκ4
      have hdvd2 : orderOf κ₁ ∣ 2 := by
        have := Nat.dvd_gcd hdvd18 hdvd4
        simpa using this
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.1 hdvd2
    have hκ1 : κ₁ = 1 := by
      obtain ⟨t, ht, htr⟩ := exists_mem_tab K_enumOK hκ₁
      have h1 := hcK t ht
      have hcomm' : commB t (Kelems.getD d.2.2.2 []) = true := by
        rw [commB, beq_iff_eq]
        exact rep_eq_tab (rep_mul htr hκr) (hκcomm ▸ rep_mul hκr htr)
      have hsq : tmul t t = tid := rep_eq_tab (rep_mul htr htr) (hκ2 ▸ rep_one)
      rw [hcomm', hsq, beq_self_eq_true, Bool.and_true, Bool.not_true, Bool.false_or,
        beq_iff_eq] at h1
      exact rep_unique (h1 ▸ htr) rep_one
    rw [hκ1, mul_one] at hv'eq
    subst hv'eq
    obtain ⟨t, ht, htr⟩ := exists_mem_tab E_enumOK hε₁
    have h1 := hcE t ht
    have hcomm' : commB t (conjTab d.2.1 (wtab e0W)) = true := by
      rw [commB, beq_iff_eq]
      exact rep_eq_tab (rep_mul htr he'r) ((hV'comm _ hv') ▸ rep_mul he'r htr)
    rw [hcomm', Bool.not_true, Bool.false_or] at h1
    exact eq_one_or_tau_of_rep_mem htr h1
  have hle : Nat.card V' ≤ 2 := by
    have hsub : (V' : Set (Equiv.Perm (Fin 45))) ⊆ {1, tauPerm 0} := fun v hv => hV'sub v hv
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have e : Nat.card V' = (V' : Set (Equiv.Perm (Fin 45))).ncard := Nat.card_coe_set_eq _
    rw [e]
    exact this.trans ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  omega

theorem exists_conj_x0_of_mem_Q0 {y : Equiv.Perm (Fin 45)} (hy : y ∈ Q0)
    (hcard : Nat.card ↥(P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 45)))) = 108) :
    ∃ n ∈ P, n ∈ normalizer (Q0 : Set (Equiv.Perm (Fin 45))) ∧ wperm x0W = n * y * n⁻¹ := by
  obtain ⟨i, hi, hr⟩ := (mem_gen_words Q0_enumOK y).1 hy
  have hc := List.all_eq_true.1 Q0_class i (List.mem_range.2 hi)
  set n := Q0conj.getD i []
  have hnr : Rep (wperm n * y * (wperm n)⁻¹) (conjTab n (Q0elems.getD i [])) := rep_conj n hr
  have hcn := card_centralizer_conj (wperm_mem n) y
  unfold classOK at hc
  split at hc
  ·
    rw [beq_iff_eq] at hc
    have hy1 : y = 1 := rep_unique (hc ▸ hr) rep_one
    subst hy1
    have : P ⊓ centralizer ({1} : Set (Equiv.Perm (Fin 45))) = P := by
      rw [Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
    rw [this, card_P] at hcard
    norm_num at hcard
  ·
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hc
    rcases hc with hc | hc
    · have hyc : wperm n * y * (wperm n)⁻¹ = wperm cW ^ 1 := by
        rw [pow_one]; exact rep_unique (hc ▸ hnr) (rep_wperm cW)
      have := dvd_card_centralizer_c_pow 1
      rw [← hyc, hcn, hcard] at this
      norm_num at this
    · have hyc : wperm n * y * (wperm n)⁻¹ = wperm cW ^ 2 := by
        rw [pow_two]; exact rep_unique (hc ▸ hnr) (rep_mul (rep_wperm cW) (rep_wperm cW))
      have := dvd_card_centralizer_c_pow 2
      rw [← hyc, hcn, hcard] at this
      norm_num at this
  ·
    rw [beq_iff_eq] at hc
    have hye : wperm n * y * (wperm n)⁻¹ = wperm e0W := rep_unique (hc ▸ hnr) (rep_wperm e0W)
    exact absurd (by rw [← hye, hcn, hcard]) card_ne_108_e0
  ·
    rw [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hc, hN⟩ := hc
    refine ⟨wperm n, wperm_mem n, ?_, (rep_unique (hc ▸ hnr) (rep_wperm x0W)).symm⟩
    refine mem_normalizer_of_conj_mem' Q0 _ fun x hx => ?_
    obtain ⟨t, ht, htr⟩ := exists_mem_tab Q0_enumOK hx
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hN n (List.mem_singleton_self _)) t ht
    rw [List.contains_iff_mem] at h1
    exact mem_gen_of_mem_tab Q0_enumOK h1 (rep_conj n htr)
  · exact absurd hc (by simp)

theorem exists_conj_x0 {x : Equiv.Perm (Fin 45)} (hxP : x ∈ P) (hx3 : x ^ 3 = 1)
    (hcard : Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 45)))) = 108) :
    ∃ h ∈ P, x = h * wperm x0W * h⁻¹ := by
  set C := P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 45)))
  have hxC : x ∈ C := ⟨hxP, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨S'⟩ : Nonempty (Sylow 3 C) := inferInstance
  set D := (S'.toSubgroup).map C.subtype with hDdef
  have hDC : D ≤ C := Subgroup.map_subtype_le _
  have hfac : (108 : ℕ).factorization 3 = 3 := by
    rw [show (108 : ℕ) = 3 ^ 3 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hDcard : Nat.card D = 27 := by
    rw [hDdef, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity,
      hcard, hfac]
    norm_num
  have hxD : x ∈ D := mem_sylow_of_central hxC
    (fun c hc => (mem_centralizer_singleton_iff.1 hc.2)) hx3 S'
  have hDP : D ≤ P := hDC.trans inf_le_left
  have hDp : IsPGroup 3 (D.subgroupOf P) :=
    IsPGroup.of_card (n := 3) (by rw [card_subgroupOf_of_le hDP, hDcard]; norm_num)
  obtain ⟨S, hS⟩ := hDp.exists_le_sylow
  set SP := (S.toSubgroup).map P.subtype with hSPdef
  have hSPP : SP ≤ P := Subgroup.map_subtype_le _
  have hSPcard : Nat.card SP = 3 ^ (Nat.card P).factorization 3 := by
    rw [hSPdef, Subgroup.card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity]
  have hDSP : D ≤ SP := by
    intro d hd
    exact ⟨⟨d, hDP hd⟩, hS (mem_subgroupOf.2 hd), rfl⟩
  obtain ⟨g, hgP, hg⟩ := exists_conj_eq_of_card P3_le_P hSPP card_P3_eq hSPcard
  set x' := g⁻¹ * x * g
  have hconj : ∀ d ∈ D, g⁻¹ * d * g ∈ P3 := by
    intro d hd
    have := hDSP hd
    rw [hg] at this
    obtain ⟨s, hs, hsd⟩ := this
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsd
    rw [← hsd]
    simpa [mul_assoc] using hs
  have hx'P3 : x' ∈ P3 := hconj x hxD
  have hx'Q : x' ∈ Q0 := by
    by_contra hx'Q
    have h9 := card_centralizer_P3_le hx'P3 hx'Q
    set D' := D.map (MulAut.conj g⁻¹).toMonoidHom
    have hD' : D' ≤ P3 ⊓ centralizer ({x'} : Set (Equiv.Perm (Fin 45))) := by
      rintro _ ⟨d, hd, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine Subgroup.mem_inf.2 ⟨hconj d hd, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hdx : d * x = x * d := mem_centralizer_singleton_iff.1 (hDC hd).2
      calc g⁻¹ * d * g * x' = g⁻¹ * (d * x) * g := by simp only [x']; group
        _ = g⁻¹ * (x * d) * g := by rw [hdx]
        _ = x' * (g⁻¹ * d * g) := by simp only [x']; group
    have h27 : Nat.card D' = 27 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hDcard]
    have := Subgroup.card_le_of_le hD'
    omega
  have hcard' : Nat.card ↥(P ⊓ centralizer ({x'} : Set (Equiv.Perm (Fin 45)))) = 108 := by
    have := card_centralizer_conj (inv_mem hgP) x
    simpa [x'] using this.trans hcard
  obtain ⟨n, hnP, -, hn⟩ := exists_conj_x0_of_mem_Q0 hx'Q hcard'
  refine ⟨g * n⁻¹, mul_mem hgP (inv_mem hnP), ?_⟩
  rw [hn]
  simp only [x']
  group

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
