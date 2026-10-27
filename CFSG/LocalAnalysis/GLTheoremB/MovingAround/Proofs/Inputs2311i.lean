module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311h2
public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane4

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311i

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX TauCeti CFSG.Open
  CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen UniSeitzPlanes)

section F4TwoPalin

theorem cert5_gens_palin : ∀ g ∈ cert5.gens, g.1.reverse = g.1 := by
  decide

theorem cert7_gens_palin : ∀ g ∈ cert7.gens, g.1.reverse = g.1 := by
  decide

end F4TwoPalin

section F4TwoNative

set_option linter.unusedSectionVars false


theorem evalG_wordOfCodes_mul_self_of_palin {K : Type} [Field K] [CharP K 2] {w : List ℕ}
    (hw : w.reverse = w) : evalG K (wordOfCodes w) * evalG K (wordOfCodes w) = 1 := by
  have h := evalG_inv (K := K) (wordOfCodes w)
  have h2 : (wordOfCodes w).reverse = wordOfCodes w := by
    rw [wordOfCodes, ← List.map_reverse, hw]
  rw [h2] at h
  nth_rw 1 [← h]
  exact inv_mul_cancel _

theorem uniClosure_eq_top_of_planeCert_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (c : PlaneCert) (hc : c.check = true)
    (hpal : ∀ g ∈ c.gens, g.1.reverse = g.1) [hp : Fact c.p.Prime]
    (h3 : ¬ c.p ^ 3 ∣ Nat.card (adjointGroup ReeTag.F4.tag K))
    {E₁ : Subgroup (adjointGroup ReeTag.F4.tag K)} (hE₁ : Nat.card E₁ = c.p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  obtain ⟨hAp, hBp, hAB, hA1, hBA, hgens, htargets⟩ := c.facts (K := K) hc
  set A := evalG K (wordOfCodes c.wa) with hAdef
  set B := evalG K (wordOfCodes c.wb) with hBdef
  have hE₀ : Nat.card (Subgroup.closure ({A, B} : Set (adjointGroup ReeTag.F4.tag K))) =
      c.p ^ 2 := card_closure_pair hAp hBp hAB hA1 hBA h3
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq h3 hE₀ hE₁
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  rw [hg]
  set E₀ := Subgroup.closure ({A, B} : Set (adjointGroup ReeTag.F4.tag K)) with hE₀def
  set S := {k : adjointGroup ReeTag.F4.tag K | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧
    ∃ m : ℕ, k ^ (2 ^ m) = 1} with hSdef
  have hAE : A ∈ E₀ := Subgroup.subset_closure (by simp)
  have hBE : B ∈ E₀ := Subgroup.subset_closure (by simp)
  have hsmem : ∀ k : ℕ, evalG K (wordOfCodes (c.gens.getD k ([], 0, 0)).1) ∈
      Subgroup.closure S := by
    intro k
    by_cases hk : k < c.gens.length
    · have hmem : c.gens.getD k ([], 0, 0) ∈ c.gens := by
        rw [List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      obtain ⟨hne, hcomm⟩ := hgens _ hmem
      refine Subgroup.subset_closure ⟨A ^ (c.gens.getD k ([], 0, 0)).2.1 *
        B ^ (c.gens.getD k ([], 0, 0)).2.2, mul_mem (pow_mem hAE _) (pow_mem hBE _), hne, hcomm, 1,
        ?_⟩
      rw [pow_one, pow_two]
      exact evalG_wordOfCodes_mul_self_of_palin (hpal _ hmem)
    · rw [List.getD_eq_default _ _ (not_lt.1 hk)]
      simp [wordOfCodes]
  have htarg : ∀ t < 8, evalG K (wordOfCodes (targetWord t)) ∈ Subgroup.closure S := by
    intro t ht
    rw [← htargets t ht]
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact hsmem k
  rw [eq_top_iff, ← closure_xElement_yElement (τ := ReeTag.F4.tag) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c', rfl | rfl⟩
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [xElement_zero]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg i.val (by omega)
      rwa [show targetWord i.val = targetWord (⟨i.val, hi⟩ : Fin 4).val from rfl,
        evalG_targetWord_x (K := K) ⟨i.val, hi⟩] at this
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [show yElement (τ := ReeTag.F4.tag) (K := K) i 0 = 1 from
        Subtype.ext (Units.ext (yOp_zero i))]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg (i.val + 4) (by omega)
      rw [show targetWord (i.val + 4) = targetWord ((⟨i.val, hi⟩ : Fin 4).val + 4) from rfl,
        evalG_targetWord_y (K := K) ⟨i.val, hi⟩] at this
      rw [yElement_one_eq]
      exact this

theorem f4TwoFiveSevenUniNative_even (K : Type) [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) {p : ℕ} (hp : p = 5 ∨ p = 7)
    (E₀ : Subgroup (adjointGroup .F4 K)) (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have hc := (Certificates.certificate14997 : cert5.check = true ∧ cert7.check = true)
  rcases hp with rfl | rfl
  · have : Fact (Nat.Prime cert5.p) := ⟨by show Nat.Prime 5; norm_num⟩
    exact uniClosure_eq_top_of_planeCert_two hK cert5 hc.1 cert5_gens_palin (by rw [hG]; decide)
      hE₀c
  · have : Fact (Nat.Prime cert7.p) := ⟨by show Nat.Prime 7; norm_num⟩
    exact uniClosure_eq_top_of_planeCert_two hK cert7 hc.2 cert7_gens_palin (by rw [hG]; decide)
      hE₀c

end F4TwoNative

section F4TwoCat

set_option linter.unusedSectionVars false


theorem uniSeitzPlanes_F4Two_fiveSeven_even :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
      ∃ q : PrimePower, d.1 = .F4 q ∧ q.card = 2 ∧ (p = 5 ∨ p = 7) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hn, q, hq, hq2, hp57⟩
  obtain rfl : d = .F4 q := hq
  have hqp : q.p = 2 := by
    have h1 : q.p ∣ 2 := by
      rw [← hq2, PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.uniPlaneGen_cat_even
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 LieTypeIndex.characteristic_F4 hv hqp ?_ hE hc hin hn
  intro K _ _ _ hKq _ E₀ _ hE₀c _
  exact f4TwoFiveSevenUniNative_even K (hKq.trans hq2) hp57 E₀ hE₀c

end F4TwoCat

section Generic

theorem closure_two_pow_eq_top_of_isPerfect {H : Type*} [Group H] [Finite H] [Group.IsPerfect H] :
    Subgroup.closure {x : H | ∃ n : ℕ, x ^ (2 ^ n) = 1} = ⊤ := by
  classical
  set N := Subgroup.closure {x : H | ∃ n : ℕ, x ^ (2 ^ n) = 1} with hN
  haveI hNn : N.Normal := by
    constructor
    intro n hn g
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := hx
      exact Subgroup.subset_closure ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have h1 := N.mul_mem hx hy
      have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      rw [e]
      exact h1
    | inv x _ hx =>
      have h1 := N.inv_mem hx
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact h1
  have hodd : Odd (Nat.card (H ⧸ N)) := by
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card (H ⧸ N) := by omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hu : (x ^ m) ^ (2 ^ k) = 1 := by rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
    have huN : x ^ m ∈ N := Subgroup.subset_closure ⟨k, hu⟩
    have hym : (QuotientGroup.mk x : H ⧸ N) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact huN
    have h3 := orderOf_dvd_of_pow_eq_one hym
    rw [hy] at h3
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)
  haveI : Group.IsSolvable (H ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hne
  haveI : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

theorem map_le_uniClosure_of_cover {H G : Type*} [Group H] [Group G] [Finite H] {p r : ℕ}
    [Fact p.Prime] (ψ : H →* G) (hker : ¬ p ∣ Nat.card ψ.ker) (X : Subgroup H)
    (hH : ∀ F : Subgroup H, IsElemAbelian p F → Nat.card F = p ^ 2 →
      X ≤ Subgroup.closure {h : H | ∃ x ∈ F, x ≠ 1 ∧ Commute h x ∧ ∃ n : ℕ, h ^ (r ^ n) = 1})
    (F : Subgroup G) (hF : F ≤ ψ.range) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    X.map ψ ≤ Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x ∧ ∃ n : ℕ, g ^ (r ^ n) = 1} := by
  classical
  set ψ' : H →* ψ.range := ψ.rangeRestrict with hψ'
  have hker' : ¬ p ∣ Nat.card ψ'.ker := by
    rw [hψ', ψ.ker_rangeRestrict]
    exact hker
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup F := IsPGroup.commGroupOfCardEqPrimeSq hFc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : F) ⟨b, hb⟩)
  set F1 : Subgroup ψ.range := F.subgroupOf ψ.range with hF1def
  have hF1 : IsElemAbelian p F1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hFp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.exists_lift_elemAbelian_of_coprime_ker ψ'
      ψ.rangeRestrict_surjective hker' hF1
  have hcardF1 : Nat.card F1 = p ^ 2 := by
    rw [← hFc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← hcardF1, ← hmapE',
      CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker ψ' hdisE']
  rw [Subgroup.map_le_iff_le_comap]
  refine (hH E' hE'ea hcardE').trans ?_
  rw [Subgroup.closure_le]
  rintro k ⟨x, hx, hx1, hkx, n, hn⟩
  have hxF : ψ x ∈ F := by
    have h1 : ψ' x ∈ F1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact h1
  have hx1' : ψ x ≠ 1 := by
    intro h1
    apply hx1
    refine Subgroup.disjoint_def.mp hdisE' hx ?_
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h1
  exact Subgroup.mem_comap.2
    (Subgroup.subset_closure ⟨ψ x, hxF, hx1', hkx.map ψ, n, by rw [← map_pow, hn, map_one]⟩)

theorem range_inr_le_uniClosure_prod {A B : Type*} [Group A] [Group B] {p r : ℕ} [Fact p.Prime]
    (hBr : Subgroup.closure {b : B | ∃ n : ℕ, b ^ (r ^ n) = 1} = ⊤)
    (hB : ∀ F : Subgroup B, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {b : B | ∃ x ∈ F, x ≠ 1 ∧ Commute b x ∧ ∃ n : ℕ, b ^ (r ^ n) = 1} = ⊤)
    (F : Subgroup (A × B)) (hF : IsElemAbelian p F) (hc : Nat.card F = p ^ 2) :
    (MonoidHom.inr A B).range ≤
      Subgroup.closure {h : A × B | ∃ x ∈ F, x ≠ 1 ∧ Commute h x ∧ ∃ n : ℕ, h ^ (r ^ n) = 1} := by
  classical
  rintro _ ⟨b, rfl⟩
  by_cases hx : ∃ x ∈ F, x ≠ 1 ∧ x.2 = 1
  · obtain ⟨x, hxF, hx1, hx2⟩ := hx
    have hb : b ∈ Subgroup.closure {b : B | ∃ n : ℕ, b ^ (r ^ n) = 1} := by
      rw [hBr]
      exact Subgroup.mem_top _
    have hmap := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
    rw [MonoidHom.map_closure] at hmap
    refine Subgroup.closure_mono ?_ hmap
    rintro _ ⟨b', ⟨n, hn⟩, rfl⟩
    refine ⟨x, hxF, hx1, Prod.ext (by simp) (by simp [hx2]), n, ?_⟩
    rw [← map_pow, hn, map_one]
  · push Not at hx
    have hdis : Disjoint F (MonoidHom.snd A B).ker := by
      rw [Subgroup.disjoint_def]
      intro x hx' hx1
      by_contra hne
      exact hx x hx' hne (MonoidHom.mem_ker.1 hx1)
    have hFB : IsElemAbelian p (F.map (MonoidHom.snd A B)) := hF.map _
    have hcardFB : Nat.card (F.map (MonoidHom.snd A B)) = p ^ 2 := by
      rw [CFSG.LieType.SeitzGeneration.ExcHigh.card_map_eq_of_disjoint_ker _ hdis, hc]
    have htop := hB _ hFB hcardFB
    have hb : b ∈ Subgroup.closure {b : B | ∃ f ∈ F.map (MonoidHom.snd A B), f ≠ 1 ∧
        Commute b f ∧ ∃ n : ℕ, b ^ (r ^ n) = 1} := by
      rw [htop]
      exact Subgroup.mem_top _
    have hmap := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
    rw [MonoidHom.map_closure] at hmap
    refine Subgroup.closure_mono ?_ hmap
    rintro _ ⟨b', ⟨_, ⟨x, hxF, rfl⟩, hf1, hcb, n, hn⟩, rfl⟩
    refine ⟨x, hxF, fun h => hf1 (by simp [h]), ?_, n, ?_⟩
    · exact Prod.ext (by simp) (by simpa using hcb.eq)
    · rw [← map_pow, hn, map_one]

theorem uniClosure_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {r : ℕ}
    {E : Subgroup G}
    (h : Subgroup.closure {k : H | ∃ x ∈ E.map e.toMonoidHom, x ≠ 1 ∧ Commute k x ∧
      ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤) :
    Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧ ∃ n : ℕ, k ^ (r ^ n) = 1} = ⊤ := by
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [Subgroup.map_top_of_surjective _ e.symm.surjective, MonoidHom.map_closure] at hmap
  rw [eq_top_iff, ← hmap, Subgroup.closure_le]
  rintro _ ⟨k, ⟨_, ⟨x, hx, rfl⟩, hx1, hkx, n, hn⟩, rfl⟩
  refine Subgroup.subset_closure ⟨x, hx, fun h1 => hx1 (by rw [h1, map_one]), ?_, n, ?_⟩
  · have h1 := hkx.map e.symm.toMonoidHom
    simpa using h1
  · rw [← map_pow, hn, map_one]

theorem exists_two_pow_eq_one_of_mem_unipotent
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {G : Subgroup (ModGL τ K)} (y : G)
    (hy : (y : ModGL τ K) ∈ posUnipotent τ K ∨ (y : ModGL τ K) ∈ negUnipotent τ K) :
    ∃ m : ℕ, y ^ (2 ^ m) = 1 := by
  obtain ⟨-, hP, -, hN⟩ := (CFSG.Blueprint.Chevalley.positive_root_triangularity.{0, 0} τ).2 K 2
  rcases hy with h | h
  · obtain ⟨m, hm⟩ := hP ⟨_, h⟩
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
  · obtain ⟨m, hm⟩ := hN ⟨_, h⟩
    exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩

theorem isElemAbelian_of_exponent_card_sq {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {E₀ : Subgroup G}
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) : IsElemAbelian p E₀ := by
  have hcomm₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E₀ := IsPGroup.commGroupOfCardEqPrimeSq hE₀c
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E₀) ⟨b, hb⟩)
  exact ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm₀ a a.2 b b.2), hE₀p⟩

end Generic

section TwE6ThreeFour

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.RankThree.E6

set_option linter.unusedSectionVars false


variable {k K : Type} [Field k] [Finite k] [CharP k 2] [Field K] [Finite K] [Algebra k K]

theorem twE6ThreeUniNative_of_subfield (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} [hpF : Fact p.Prime]
    (hp5 : 5 ≤ p) (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 3)
    (E₀ : Subgroup ↥(twistedE6RootGroup K σ)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hpF.out
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
    intro c
    rw [hσ, ← hk, ← map_pow]
    congr 1
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hp' : p ∣ Nat.card k ^ 2 + Nat.card k + 1 := by
    rw [hk]
    exact CFSG.HardMathSupport.Lang.AnisoE6.dvd_sq_add_add_one_of_orderOf_eq_three hp he
  have hTG : SylowTorus (twistedE6RootGroup K σ) p 2 :=
    sylowTorus_twistedE6_three Nat.prime_two hf K hK σ hσ hp he
  have hTΓ : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2 :=
    (sylowTorus_F4_three k hp (by omega) hp').of_mulEquiv (e6FixedF4EquivAll k).symm
  have hinj := phiG_injective σ hfix
  obtain ⟨e, ⟨γ, hγ, rfl⟩, heord, hecomm⟩ := exists_e1 (K := K) (algebraMap k K) hp'
  set γΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨γ, hγ⟩ with hγΓ
  have hordγ : orderOf γΓ = p := by
    rw [← Subgroup.orderOf_coe, show (γΓ : ModGL TwistTag.E6.tag k) = γ from rfl,
      ← orderOf_injective (baseChangeGL (algebraMap k K)) (baseChangeGL_injective _) γ]
    exact heord
  obtain ⟨EΓ, hEΓ, hEΓc, hγE⟩ := exists_plane_containing_of_sylowTorus hTΓ hordγ
  set ι := phiG σ hfix with hιdef
  set EH : Subgroup (twistedE6RootGroup K σ) := EΓ.map ι with hEHdef
  have hEH : IsElemAbelian p EH :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEΓ ι
  have hEHc : Nat.card EH = p ^ 2 := by
    rw [hEHdef, Subgroup.card_map_of_injective hinj, hEΓc]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_sylowTorus hTG (isElemAbelian_of_exponent_card_sq hE₀p hE₀c) hE₀c
    hEH hEHc
  have hclΓ : Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
      ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1} = ⊤ := by
    refine uniClosure_eq_top_of_mulEquiv (e6FixedF4EquivAll k) ?_
    have hF₁p : ∀ x ∈ EΓ.map (e6FixedF4EquivAll k).toMonoidHom, x ^ p = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEΓ.2 x hx, map_one]
    have hF₁c : Nat.card (EΓ.map (e6FixedF4EquivAll k).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (f := (e6FixedF4EquivAll k).toMonoidHom)
        (e6FixedF4EquivAll k).injective, hEΓc]
    by_cases hk4 : 4 ≤ Nat.card k
    · exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.f4ThreeUniNative_even k hk4 hp hp5
        (by rw [hk]; exact he) _ hF₁p hF₁c
    · have hf1 : f = 1 := by
        by_contra hne
        apply hk4
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hk2 : Nat.card k = 2 := by rw [hk, hf1]; norm_num
      have hp7 : p = 7 := by
        rw [hk2] at hp'
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hp')
      exact f4TwoFiveSevenUniNative_even k hk2 (Or.inr hp7) _ hF₁c
  set M := Subgroup.closure {x : twistedE6RootGroup K σ | ∃ y ∈ EH, y ≠ 1 ∧ Commute x y ∧
    ∃ m : ℕ, x ^ (2 ^ m) = 1} with hM
  have hH : ∀ x, ι x ∈ M := by
    intro x
    have hx : x ∈ Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1} := by
      rw [hclΓ]
      exact Subgroup.mem_top x
    have hle : (Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1}).map ι ≤ M := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨z, ⟨y, hy, hy1, hzy, m, hm⟩, rfl⟩
      exact ⟨ι y, ⟨y, hy, rfl⟩, fun h => hy1 (hinj (h.trans (map_one _).symm)), hzy.map ι, m,
        by rw [← map_pow, hm, map_one]⟩
    exact hle ⟨x, hx, rfl⟩
  set eG : twistedE6RootGroup K σ := ι γΓ with heGdef
  have heG : eG ∈ EH := ⟨γΓ, hγE, rfl⟩
  have heG1 : eG ≠ 1 := by
    intro h
    have h1 : orderOf eG = p := by
      rw [heGdef, orderOf_injective ι hinj γΓ, hordγ]
    rw [h, orderOf_one] at h1
    exact hp.one_lt.ne h1
  have hcomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) →
      ∀ d : K, Commute (eG : ModGL TwistTag.E6.tag K) (xUnit Tag.E6 K i d) ∧
        Commute (eG : ModGL TwistTag.E6.tag K) (yUnit Tag.E6 K i d) :=
    hecomm
  have hgen : ∀ y : twistedE6RootGroup K σ,
      Commute (y : ModGL TwistTag.E6.tag K) (eG : ModGL TwistTag.E6.tag K) →
        (∃ m : ℕ, y ^ (2 ^ m) = 1) → y ∈ M :=
    fun y hy hy2 => Subgroup.subset_closure ⟨eG, heG, heG1, Subtype.ext hy.eq, hy2⟩
  have hsub : ∀ x : twistedE6RootGroup K σ, x ∈ M →
      (x : ModGL TwistTag.E6.tag K) ∈ M.map (twistedE6RootGroup K σ).subtype :=
    fun x hx => ⟨x, hx, rfl⟩
  have hmemX : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype ∧
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype := by
    intro a c
    have hXG : (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
    have hYG : (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ _ _ _)
    have hX2 := exists_two_pow_eq_one_of_mem_unipotent (G := twistedE6RootGroup K σ) ⟨_, hXG⟩
      (Or.inl (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a c)).1)
    have hY2 := exists_two_pow_eq_one_of_mem_unipotent (G := twistedE6RootGroup K σ) ⟨_, hYG⟩
      (Or.inr (Subgroup.mem_inf.1 (orbitY_mem_graphFixedNegUnipotent _ σ.toRingHom a c)).1)
    obtain ⟨a, ha⟩ := a
    have ha4 : a < 4 := ha
    interval_cases a
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨0, ha⟩ (Or.inl rfl) c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm hX2),
        hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm hY2)⟩
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨1, ha⟩ (Or.inr rfl) c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm hX2),
        hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm hY2)⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_two, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 3) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 3) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_two]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_two]
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_three, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨0, by decide⟩ (e6Index 1) orbitWord_f4_zero c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 1) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 1) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_three]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_three]
  have hG : twistedE6RootGroup K σ ≤ M.map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [(hmemX a c).1, (hmemX a c).2]
  have hmain : M = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    obtain ⟨y, hy, hyx⟩ := hG x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  rw [hg]
  exact hmain

theorem twE6FourUniNative_of_subfield (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} [hpF : Fact p.Prime]
    (hp5 : 5 ≤ p) (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 4)
    (E₀ : Subgroup ↥(twistedE6RootGroup K σ)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x ∧ ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hpF.out
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
    intro c
    rw [hσ, ← hk, ← map_pow]
    congr 1
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hp' : p ∣ Nat.card k ^ 2 + 1 := by
    rw [hk]
    exact dvd_sq_add_one_of_orderOf_eq_four hp he
  have hTG : SylowTorus (twistedE6RootGroup K σ) p 2 :=
    sylowTorus_twistedE6_four Nat.prime_two hf K hK σ hσ hp he
  have hTΓ : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2 :=
    (sylowTorus_F4_four k hp (by omega) hp').of_mulEquiv (e6FixedF4EquivAll k).symm
  have hinj := phiG_injective σ hfix
  obtain ⟨e, ⟨γ, hγ, rfl⟩, heord, hecomm⟩ := exists_e4 (K := K) (algebraMap k K) hp'
  set γΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨γ, hγ⟩ with hγΓ
  have hordγ : orderOf γΓ = p := by
    rw [← Subgroup.orderOf_coe, show (γΓ : ModGL TwistTag.E6.tag k) = γ from rfl,
      ← orderOf_injective (baseChangeGL (algebraMap k K)) (baseChangeGL_injective _) γ]
    exact heord
  obtain ⟨EΓ, hEΓ, hEΓc, hγE⟩ := exists_plane_containing_of_sylowTorus hTΓ hordγ
  set ι := phiG σ hfix with hιdef
  set EH : Subgroup (twistedE6RootGroup K σ) := EΓ.map ι with hEHdef
  have hEH : IsElemAbelian p EH :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEΓ ι
  have hEHc : Nat.card EH = p ^ 2 := by
    rw [hEHdef, Subgroup.card_map_of_injective hinj, hEΓc]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_sylowTorus hTG (isElemAbelian_of_exponent_card_sq hE₀p hE₀c) hE₀c
    hEH hEHc
  have hclΓ : Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
      ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1} = ⊤ := by
    refine uniClosure_eq_top_of_mulEquiv (e6FixedF4EquivAll k) ?_
    have hF₁p : ∀ x ∈ EΓ.map (e6FixedF4EquivAll k).toMonoidHom, x ^ p = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEΓ.2 x hx, map_one]
    have hF₁c : Nat.card (EΓ.map (e6FixedF4EquivAll k).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (f := (e6FixedF4EquivAll k).toMonoidHom)
        (e6FixedF4EquivAll k).injective, hEΓc]
    by_cases hk4 : 4 ≤ Nat.card k
    · exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311h.f4FourUniNative_even k hk4 p hp5 hp' _
        hF₁p hF₁c
    · have hf1 : f = 1 := by
        by_contra hne
        apply hk4
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hk2 : Nat.card k = 2 := by rw [hk, hf1]; norm_num
      have hp5' : p = 5 := by
        rw [hk2] at hp'
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hp')
      exact f4TwoFiveSevenUniNative_even k hk2 (Or.inl hp5') _ hF₁c
  set M := Subgroup.closure {x : twistedE6RootGroup K σ | ∃ y ∈ EH, y ≠ 1 ∧ Commute x y ∧
    ∃ m : ℕ, x ^ (2 ^ m) = 1} with hM
  have hH : ∀ x, ι x ∈ M := by
    intro x
    have hx : x ∈ Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1} := by
      rw [hclΓ]
      exact Subgroup.mem_top x
    have hle : (Subgroup.closure {x : twistedFixedGroup TwistTag.E6 k (RingHom.id k) |
        ∃ y ∈ EΓ, y ≠ 1 ∧ Commute x y ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1}).map ι ≤ M := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨z, ⟨y, hy, hy1, hzy, m, hm⟩, rfl⟩
      exact ⟨ι y, ⟨y, hy, rfl⟩, fun h => hy1 (hinj (h.trans (map_one _).symm)), hzy.map ι, m,
        by rw [← map_pow, hm, map_one]⟩
    exact hle ⟨x, hx, rfl⟩
  set eG : twistedE6RootGroup K σ := ι γΓ with heGdef
  have heG : eG ∈ EH := ⟨γΓ, hγE, rfl⟩
  have heG1 : eG ≠ 1 := by
    intro h
    have h1 : orderOf eG = p := by
      rw [heGdef, orderOf_injective ι hinj γΓ, hordγ]
    rw [h, orderOf_one] at h1
    exact hp.one_lt.ne h1
  have hcomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 5) →
      ∀ d : K, Commute (eG : ModGL TwistTag.E6.tag K) (xUnit Tag.E6 K i d) ∧
        Commute (eG : ModGL TwistTag.E6.tag K) (yUnit Tag.E6 K i d) :=
    hecomm
  have hgen : ∀ y : twistedE6RootGroup K σ,
      Commute (y : ModGL TwistTag.E6.tag K) (eG : ModGL TwistTag.E6.tag K) →
        (∃ m : ℕ, y ^ (2 ^ m) = 1) → y ∈ M :=
    fun y hy hy2 => Subgroup.subset_closure ⟨eG, heG, heG1, Subtype.ext hy.eq, hy2⟩
  have hsub : ∀ x : twistedE6RootGroup K σ, x ∈ M →
      (x : ModGL TwistTag.E6.tag K) ∈ M.map (twistedE6RootGroup K σ).subtype :=
    fun x hx => ⟨x, hx, rfl⟩
  have hnΓ : nElt TwistTag.E6.tag k ωwWord ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) :=
    nElt_flatten_mem k ωwFold
  set nΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨_, hnΓ⟩ with hnΓdef
  set nG : twistedE6RootGroup K σ := ι nΓ with hnGdef
  have hnG : (nG : ModGL TwistTag.E6.tag K) = nElt TwistTag.E6.tag K ωwWord :=
    baseChangeGL_nElt (algebraMap k K) Tag.E6 ωwWord
  have hmemX : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype ∧
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        M.map (twistedE6RootGroup K σ).subtype := by
    intro a c
    have hXG : (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
    have hYG : (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ _ _ _)
    have hX2 := exists_two_pow_eq_one_of_mem_unipotent (G := twistedE6RootGroup K σ) ⟨_, hXG⟩
      (Or.inl (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a c)).1)
    have hY2 := exists_two_pow_eq_one_of_mem_unipotent (G := twistedE6RootGroup K σ) ⟨_, hYG⟩
      (Or.inr (Subgroup.mem_inf.1 (orbitY_mem_graphFixedNegUnipotent _ σ.toRingHom a c)).1)
    obtain ⟨a, ha⟩ := a
    have ha4 : a < 4 := ha
    interval_cases a
    · have h := commute_orbitXY_zero σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm hX2),
        hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm hY2)⟩
    ·
      obtain ⟨hX1, hY1⟩ := orbitXY_one_mem_rootSpan σ.toRingHom c
      have hcS0 : ∀ γ ∈ S₀, ∀ c : K, Commute (eG : ModGL TwistTag.E6.tag K)
          (pinnedX Tag.E6 K γ c) := by
        intro γ hγ c
        rcases hγ with rfl | rfl | rfl | rfl
        · rw [pinnedX_single]; exact (hcomm _ (Or.inl rfl) c).1
        · rw [pinnedX_neg_single]; exact (hcomm _ (Or.inl rfl) c).2
        · rw [pinnedX_single]; exact (hcomm _ (Or.inr rfl) c).1
        · rw [pinnedX_neg_single]; exact (hcomm _ (Or.inr rfl) c).2
      have hconj : ∀ z : twistedE6RootGroup K σ,
          (z : ModGL TwistTag.E6.tag K) ∈ rootSpan Tag.E6 K S₂ → (∃ m : ℕ, z ^ (2 ^ m) = 1) →
            z ∈ M := by
        intro z hz hz2
        set y : twistedE6RootGroup K σ := nG⁻¹ * z * nG with hy
        have hy' : (y : ModGL TwistTag.E6.tag K) ∈ rootSpan Tag.E6 K S₀ := by
          have e : (y : ModGL TwistTag.E6.tag K) =
              (nElt TwistTag.E6.tag K ωwWord)⁻¹ * (z : ModGL TwistTag.E6.tag K) *
                nElt TwistTag.E6.tag K ωwWord := by
            rw [hy]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnG]
          rw [e]
          exact nElt_inv_conj_mem_rootSpan K ωwWord ωw_inv_S₂ hz
        have hyc := commute_of_forall_pinnedX K hcS0 hy'
        have hy2 : ∃ m : ℕ, y ^ (2 ^ m) = 1 := by
          obtain ⟨m, hm⟩ := hz2
          refine ⟨m, ?_⟩
          rw [hy, show nG⁻¹ * z * nG = nG⁻¹ * z * nG⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv, hm,
            mul_one, inv_mul_cancel]
        have hycl : y ∈ M := hgen y hyc.symm hy2
        have : z = nG * y * nG⁻¹ := by rw [hy]; group
        rw [this]
        exact mul_mem (mul_mem (hH nΓ) hycl) (inv_mem (hH nΓ))
      exact ⟨hsub ⟨_, hXG⟩ (hconj ⟨_, hXG⟩ hX1 hX2), hsub ⟨_, hYG⟩ (hconj ⟨_, hYG⟩ hY1 hY2)⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_two, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 3) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 3) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_two]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_two]
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_three, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨0, by decide⟩ (e6Index 1) orbitWord_f4_zero c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 1) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 1) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_three]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_three]
  have hG : twistedE6RootGroup K σ ≤ M.map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [(hmemX a c).1, (hmemX a c).2]
  have hmain : M = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    obtain ⟨y, hy, hyx⟩ := hG x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniClosure_eq_top_of_conj g ?_
  rw [hg]
  exact hmain

end TwE6ThreeFour

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311i
