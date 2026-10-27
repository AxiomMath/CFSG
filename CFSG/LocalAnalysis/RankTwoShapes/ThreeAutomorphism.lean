module

public import CFSG.LocalAnalysis.RankTwoShapes.OrderSixtyFour
public import CFSG.Milestones.CLS_connectivity_MacWilliams_four_generator
public import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniAutomorphismKernel
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.RankTwoShapes

universe u

theorem pow_three_eq_one_of_pow_nine {E : Type u} [Group E] [Finite E] (hE : Nat.card E ∣ 16)
    (ψ : MulAut E) (hψ : ψ ^ 9 = 1) : ψ ^ 3 = 1 := by
  classical
  let : Fintype E := Fintype.ofFinite E
  have hiter : ∀ (k : ℕ) (f : E), (ψ ^ k) f = (⇑ψ)^[k] f := by
    intro k
    induction k with
    | zero => intro f; rfl
    | succ k ih =>
      intro f
      rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  have hper : ∀ f : E, Function.IsPeriodicPt ψ 9 f := fun f => by
    change (⇑ψ)^[9] f = f
    rw [← hiter, hψ, MulAut.one_apply]
  have hmp : ∀ f : E, (ψ ^ 3) f ≠ f → Function.minimalPeriod ψ f = 9 := by
    intro f hf
    have hd := (hper f).minimalPeriod_dvd
    have h3 : ¬ Function.minimalPeriod ψ f ∣ 3 := by
      intro h
      apply hf
      rw [hiter]
      exact Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr h
    have hmem : Function.minimalPeriod ψ f ∈ Nat.divisors 9 :=
      Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have hdiv9 : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv9] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact absurd (show Function.minimalPeriod ψ f ∣ 3 by rw [h]; exact one_dvd 3) h3
    · exact absurd (show Function.minimalPeriod ψ f ∣ 3 by rw [h]) h3
    · exact h
  have horbit_card : ∀ f : E, (ψ ^ 3) f ≠ f →
      ((Finset.range 9).image (fun k => (⇑ψ)^[k] f)).card = 9 := by
    intro f hf
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := ψ) (x := f)
    rw [hmp f hf] at hinj
    exact hinj (by simpa using hi) (by simpa using hj) hij
  by_contra hne
  obtain ⟨e, he⟩ : ∃ e, (ψ ^ 3) e ≠ e := by
    by_contra h
    push Not at h
    exact hne (MulEquiv.ext h)
  set O := (Finset.range 9).image (fun k => (⇑ψ)^[k] e) with hO
  have hOcard : O.card = 9 := horbit_card e he
  have hfix : ∀ f, f ∉ O → (ψ ^ 3) f = f := by
    intro f hfO
    by_contra hf
    set O' := (Finset.range 9).image (fun k => (⇑ψ)^[k] f) with hO'
    have hO'card : O'.card = 9 := horbit_card f hf
    have hdisj : Disjoint O O' := by
      rw [Finset.disjoint_left]
      intro w hwO hwO'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hwO
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hwO'
      apply hfO
      have hj9 : j < 9 := Finset.mem_range.mp hj
      have hf' : f = (⇑ψ)^[9 - j + i] e := by
        rw [Function.iterate_add_apply, ← hji, ← Function.iterate_add_apply,
          Nat.sub_add_cancel hj9.le]
        exact (hper f).symm
      rw [hf', ← (hper e).iterate_mod_apply]
      exact Finset.mem_image.mpr ⟨(9 - j + i) % 9, Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)),
        rfl⟩
    have hcard := Finset.card_union_of_disjoint hdisj
    have hle := Finset.card_le_univ (O ∪ O')
    have hEcard : Fintype.card E ≤ 16 := by
      rw [← Nat.card_eq_fintype_card]; exact Nat.le_of_dvd (by norm_num) hE
    omega
  let F : Subgroup E := MonoidHom.eqLocus (ψ ^ 3).toMonoidHom (MonoidHom.id E)
  have hF : ∀ f, f ∈ F ↔ f ∉ O := by
    intro f
    constructor
    · intro hf hfO
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hfO
      apply he
      have h : (ψ ^ 3) ((⇑ψ)^[i] e) = (⇑ψ)^[i] e := hf
      rw [← hiter, ← MulAut.mul_apply, ← pow_add, add_comm, pow_add, MulAut.mul_apply] at h
      exact (ψ ^ i).injective h
    · intro hfO
      exact hfix f hfO
  have hFset : (F : Set E) = (↑O : Set E)ᶜ := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_compl_iff]
    exact hF f
  have hOle : O.card ≤ Nat.card E := by
    rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ O
  have hFcard : Nat.card F + 9 = Nat.card E := by
    have h1 : Nat.card F = Nat.card E - 9 := by
      calc Nat.card F = (F : Set E).ncard := Nat.card_coe_set_eq _
        _ = ((↑O : Set E)ᶜ).ncard := by rw [hFset]
        _ = Nat.card E - (↑O : Set E).ncard := Set.ncard_compl _
        _ = Nat.card E - 9 := by rw [Set.ncard_coe_finset, hOcard]
    omega
  have hFdvd : Nat.card F ∣ Nat.card E := Subgroup.card_subgroup_dvd_card F
  have hE16 : Nat.card E = 16 := by
    have hdiv : Nat.card E ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hE, by norm_num⟩
    have h16 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [h16] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    have hpos : 0 < Nat.card F := Nat.card_pos
    rcases hdiv with h | h | h | h | h <;> omega
  rw [hE16] at hFcard hFdvd
  have hF7 : Nat.card F = 7 := by omega
  rw [hF7] at hFdvd
  norm_num at hFdvd

theorem central_involution_three_automorphism
    {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hrank : TwoRankLeTwo Q) (A : Subgroup (MulAut Q)) (B : Sylow 2 A)
    {z : Q} (hzZ : z ∈ Subgroup.center Q) (hz : orderOf z = 2)
    (hB : ∀ b ∈ (B : Subgroup A), ((b : A) : MulAut Q) z = z)
    (hmove : ∃ a ∈ A, a z ≠ z) :
    Nat.card (omegaSub (Subgroup.center Q) inferInstance 1) = 4 ∧
      (∀ t : Q, t ^ 2 = 1 → t ∈ omegaSub (Subgroup.center Q) inferInstance 1) ∧
      ∃ α ∈ A, orderOf α = 3 ∧
        (∀ v ∈ omegaSub (Subgroup.center Q) inferInstance 1, v ≠ 1 → α v ≠ v) ∧
        (∀ q : Q, α q = q → q = 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := omegaSub (Subgroup.center Q) inferInstance 1 with hV
  have hVZ : V ≤ Subgroup.center Q := omegaSub_le _ _ 1
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by simpa using hv.2
  have hzV : z ∈ V := ⟨hzZ, by rw [pow_one, ← hz]; exact pow_orderOf_eq_one z⟩
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz; norm_num at hz
  have hVinv : ∀ σ : MulAut Q, ∀ v ∈ V, σ v ∈ V := by
    intro σ v hv
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      have h := Subgroup.mem_center_iff.mp hv.1 (σ.symm g)
      have h' := congrArg σ h
      simpa using h'
    · rw [← map_pow, hv.2, map_one]
  have hVcard : Nat.card V = 4 := by
    have hle : Nat.card V ≤ 4 :=
      hrank V (omegaSub_isMulCommutative _ _ 1) hVexp
    obtain ⟨k, hk⟩ := (hQ.to_subgroup V).exists_card_eq
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    have hk1 : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero, Nat.card_eq_one_iff_unique] at hk
      have := hk.1.elim ⟨z, hzV⟩ ⟨1, V.one_mem⟩
      exact hz1 (congrArg Subtype.val this)
    rcases (show k = 1 ∨ k = 2 by omega) with h1 | h2
    · exfalso
      rw [h1, pow_one] at hk
      obtain ⟨a, ha, haz⟩ := hmove
      apply haz
      have hzp : Subgroup.zpowers z = V := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzV)
        rw [hk, Nat.card_zpowers, hz]
      have haV : a z ∈ Subgroup.zpowers z := hzp ▸ hVinv a z hzV
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp haV
      have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, ← hz, pow_orderOf_eq_one]
      rcases Int.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
      · exfalso
        rw [hn, ← two_mul, zpow_mul, hz2, one_zpow] at hm
        exact hz1 (a.injective (by rw [← hm, map_one]))
      · rw [← hm, hn, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]
    · rw [hk, h2]; norm_num
  have hinvol : ∀ t : Q, t ^ 2 = 1 → t ∈ V :=
    sq_eq_one_mem_of_central_four hrank V hVZ hVexp hVcard
  let stab := MulAction.stabilizer A z
  have hstab_mem : ∀ a : A, a ∈ stab ↔ (a : MulAut Q) z = z := fun a => Iff.rfl
  have hBstab : (B : Subgroup A) ≤ stab := fun b hb => (hstab_mem b).mpr (hB b hb)
  have horbit : (MulAction.orbit A z).ncard ≤ 3 := by
    have hsub : MulAction.orbit A z ⊆ (V : Set Q) \ {1} := by
      rintro _ ⟨a, rfl⟩
      refine ⟨hVinv a z hzV, ?_⟩
      intro h1
      exact hz1 ((a : MulAut Q).injective (by rw [map_one]; exact h1))
    have h3 : ((V : Set Q) \ {1}).ncard = 3 := by
      rw [Set.ncard_sdiff_singleton_of_mem V.one_mem, ← Nat.card_coe_set_eq]
      change Nat.card V - 1 = 3
      rw [hVcard]
    exact h3 ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
  have hindex : stab.index = 3 := by
    rw [MulAction.index_stabilizer] at *
    have hodd : ¬ 2 ∣ (MulAction.orbit A z).ncard := by
      rw [← MulAction.index_stabilizer]
      intro h2
      exact Sylow.not_dvd_index B (h2.trans (Subgroup.index_dvd_of_le hBstab))
    have hne1 : (MulAction.orbit A z).ncard ≠ 1 := by
      rw [← MulAction.index_stabilizer]
      intro htop
      rw [Subgroup.index_eq_one] at htop
      obtain ⟨a, ha, haz⟩ := hmove
      have hmem : (⟨a, ha⟩ : A) ∈ MulAction.stabilizer A z := by
        rw [htop]; exact Subgroup.mem_top _
      exact haz ((hstab_mem ⟨a, ha⟩).mp hmem)
    have hpos : 0 < (MulAction.orbit A z).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.mpr ⟨z, MulAction.mem_orbit_self z⟩
    omega
  obtain ⟨P3⟩ := (inferInstance : Nonempty (Sylow 3 A))
  obtain ⟨θ, hθP, hθz⟩ : ∃ θ ∈ (P3 : Subgroup A), ¬ θ ∈ stab := by
    by_contra h
    push Not at h
    have hle : (P3 : Subgroup A) ≤ stab := fun θ hθ => h θ hθ
    apply Sylow.not_dvd_index P3
    rw [← Subgroup.relIndex_mul_index hle, hindex]
    exact dvd_mul_left 3 _
  have hθmove : (θ : MulAut Q) z ≠ z := fun h => hθz ((hstab_mem θ).mpr h)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P3.isPGroup' ⟨θ, hθP⟩
  have hθord : orderOf (θ : MulAut Q) = 3 ^ k := by
    rw [← hk, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hθord
      exact hθmove (by rw [hθord, MulAut.one_apply])
    by_contra hk1
    have hk2 : 2 ≤ k := by omega
    have hE8 : ∀ E : Subgroup Q, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8 := by
      intro E _ hE
      have := hrank E hE.1 hE.2
      omega
    obtain ⟨X, hXcard, hXgen⟩ :=
      CFSG.Milestones.cls_connectivity_macwilliams_four_generator Q hQ hE8 ⊤
    have : Fact (IsPGroup 2 Q) := ⟨hQ⟩
    have hquot : Nat.card (Q ⧸ frattini Q) ∣ 16 := by
      have : IsElementaryAbelian 2 (Q ⧸ frattini Q) := isElementaryAbelian_quotient_frattini
      rw [elementaryAbelian_card_eq_pow_generatorRank (p := 2) (Q ⧸ frattini Q)]
      have hrk : generatorRank (Q ⧸ frattini Q) ≤ 4 := by
        apply le_trans _ hXcard
        apply Nat.sInf_le
        refine ⟨fun i => QuotientGroup.mk' (frattini Q) (X.equivFin.symm i : Q), ?_⟩
        have hrange : Set.range (fun i => QuotientGroup.mk' (frattini Q) (X.equivFin.symm i : Q)) =
            (QuotientGroup.mk' (frattini Q)) '' (X : Set Q) := by
          ext w
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨_, (X.equivFin.symm i).2, rfl⟩
          · rintro ⟨q, hq, rfl⟩
            exact ⟨X.equivFin ⟨q, hq⟩, by simp⟩
        rw [hrange, ← MonoidHom.map_closure, hXgen, ← MonoidHom.range_eq_map,
          QuotientGroup.range_mk']
      exact (Nat.pow_dvd_pow 2 hrk).trans (by norm_num)
    set ρ := CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction (frattini Q)
      with hρ
    have hθk : (θ : MulAut Q) ^ (3 ^ k) = 1 := by rw [← hθord]; exact pow_orderOf_eq_one _
    have hψ := pow_three_eq_one_of_pow_nine hquot (ρ ((θ : MulAut Q) ^ (3 ^ (k - 2)))) (by
      rw [← map_pow, ← pow_mul, show 3 ^ (k - 2) * 9 = 3 ^ k by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega, hθk, map_one])
    rw [← map_pow, ← pow_mul] at hψ
    have hker : (θ : MulAut Q) ^ (3 ^ (k - 2) * 3) ∈ ρ.ker := hψ
    have hpg := CFSG.RankThreeEvenClassification.Helpers.frattini_automorphism_kernel_isPGroup
      2 Nat.prime_two hQ
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hpg ⟨_, hker⟩
    rw [Subgroup.orderOf_mk] at hj
    have h3 : orderOf ((θ : MulAut Q) ^ (3 ^ (k - 2) * 3)) = 3 := by
      rw [orderOf_pow' _ (by positivity), hθord]
      have hpow : 3 ^ (k - 2) * 3 = 3 ^ (k - 1) := by
        rw [← pow_succ]; congr 1; omega
      rw [hpow, Nat.gcd_eq_right (Nat.pow_dvd_pow 3 (Nat.sub_le k 1))]
      have : 3 ^ k = 3 ^ (k - 1) * 3 := by rw [← pow_succ]; congr 1; omega
      rw [this, Nat.mul_div_cancel_left _ (by positivity)]
    rw [h3] at hj
    have h2 : (2 : ℕ) ∣ 3 := by
      rcases j with _ | j
      · norm_num at hj
      · rw [hj, pow_succ]; exact dvd_mul_left 2 _
    norm_num at h2
  set α := (θ : MulAut Q) with hαdef
  have hα3 : orderOf α = 3 := by rw [hθord, hk1, pow_one]
  have hαcube : ∀ q : Q, α (α (α q)) = q := by
    intro q
    have h := pow_orderOf_eq_one α
    rw [hα3] at h
    have := congrArg (fun σ : MulAut Q => σ q) h
    simpa [pow_succ] using this
  have hnofix : ∀ v ∈ V, v ≠ 1 → α v ≠ v := by
    intro v hv hv1 hαv
    obtain ⟨u, huV, hu1, huv⟩ : ∃ u ∈ V, u ≠ 1 ∧ u ≠ v := by
      by_contra h
      push Not at h
      have hsub : (V : Set Q) ⊆ {1, v} := by
        intro w hw
        by_cases hw1 : w = 1
        · simp [hw1]
        · simp [h w hw hw1]
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Nat.card_coe_set_eq] at hle
      change Nat.card V ≤ _ at hle
      rw [hVcard] at hle
      have := Set.ncard_pair (Ne.symm hv1)
      have h2 : ({1, v} : Set Q).ncard ≤ 2 := Set.ncard_insert_le _ _ |>.trans (by simp)
      omega
    have huvV : u * v ∈ V := V.mul_mem huV hv
    have hcomm : Commute u v := Subgroup.mem_center_iff.mp (hVZ hv) u
    have huv1 : u * v ≠ 1 := by
      intro h
      have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
      apply huv
      rw [this]
      exact (eq_inv_of_mul_eq_one_left (by rw [← sq]; exact hVexp v hv)).symm
    have huvu : u * v ≠ u := fun h => hv1 (mul_left_cancel (h.trans (mul_one u).symm))
    have huvv : u * v ≠ v := fun h => hu1 (mul_right_cancel (h.trans (one_mul v).symm))
    have hcases := mem_of_card_eq_four hVcard V.one_mem hv huV huvV hv1.symm hu1.symm huv1.symm
      huv.symm huvv.symm huvu.symm (hVinv α u huV)
    have hαu : α u = u := by
      rcases hcases with h | h | h | h
      · exact absurd (α.injective (h.trans (map_one α).symm)) hu1
      · exact absurd (α.injective (h.trans hαv.symm)) huv
      · exact h
      · exfalso
        have h2 : α (α u) = u := by
          rw [h, map_mul, h, hαv, mul_assoc, ← sq, hVexp v hv, mul_one]
        have h3 := hαcube u
        rw [h2, h] at h3
        exact huvu h3
    apply hθmove
    rcases mem_of_card_eq_four hVcard V.one_mem hv huV huvV hv1.symm hu1.symm huv1.symm
      huv.symm huvv.symm huvu.symm hzV with h | h | h | h
    · exact absurd h hz1
    · rw [h, hαv]
    · rw [h, hαu]
    · rw [h, map_mul, hαu, hαv]
  have hfpf : ∀ q : Q, α q = q → q = 1 := by
    intro q hq
    by_contra hq1
    let C : Subgroup Q := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Q)
    have hqC : q ∈ C := hq
    have hCnt : Nontrivial C := ⟨⟨⟨q, hqC⟩, 1, fun h => hq1 (congrArg Subtype.val h)⟩⟩
    have hCp : IsPGroup 2 C := hQ.to_subgroup C
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (by
      obtain ⟨n, hn⟩ := hCp.exists_card_eq
      rcases n with _ | n
      · rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
        exact absurd hn.1 (not_subsingleton C)
      · rw [hn, pow_succ]; exact dvd_mul_left 2 _)
    have ht2 : (t : Q) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
    have ht1 : (t : Q) ≠ 1 := by
      intro h
      have : t = 1 := Subtype.ext h
      rw [this, orderOf_one] at ht
      norm_num at ht
    exact hnofix t (hinvol t ht2) ht1 t.2
  exact ⟨hVcard, hinvol, α, θ.2, hα3, hnofix, hfpf⟩

end CFSG.RankTwoShapes
