module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.AutomizerExclusion
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.LyonsUnitaryFour

section Helpers

variable {H : Type*} [Group H]

theorem conj_mem_map_of_characteristic {X : Subgroup H} {D : Subgroup X} [hD : D.Characteristic]
    {g : H} (hg : g ∈ Subgroup.normalizer (X : Set H)) {x : H} (hx : x ∈ D.map X.subtype) :
    g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

variable [Finite H]

theorem map_oddCore_le_oddCore_of_isSubnormal {X : Subgroup H} (hX : X.IsSubnormal) :
    (CFSG.oddCore X).map X.subtype ≤ CFSG.oddCore H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.oddCore X).map X.subtype ≤ (CFSG.oddCore Y).map Y.subtype := by
    intro X Y hXY hYN
    have := oddCore_characteristic X
    have hLY : (CFSG.oddCore X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.oddCore X).map X.subtype).subgroupOf Y ≤ CFSG.oddCore Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using conj_mem_map_of_characteristic (hYN y.2) hl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective]
        exact odd_card_oddCore X
    calc (CFSG.oddCore X).map X.subtype
        = (((CFSG.oddCore X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.oddCore Y).map Y.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    have := oddCore_characteristic (⊤ : Subgroup H)
    apply le_sSup
    refine ⟨⟨fun l hl g => conj_mem_map_of_characteristic ?_ hl⟩, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top g
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact odd_card_oddCore _
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

theorem eq_bot_of_isSubnormal_of_odd (hcore : CFSG.oddCore H = ⊥) {K : Subgroup H}
    (hK : K.IsSubnormal) (hodd : Odd (Nat.card K)) : K = ⊥ := by
  have htop : CFSG.oddCore K = ⊤ := by
    apply le_antisymm le_top
    exact le_sSup ⟨inferInstance, by rw [Subgroup.card_top]; exact hodd⟩
  have h := map_oddCore_le_oddCore_of_isSubnormal hK
  rw [htop, hcore, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact le_bot_iff.mp h

omit [Finite H] in
theorem map_pCore_le_pCore_of_isSubnormal {p : ℕ} {X : Subgroup H} (hX : X.IsSubnormal) :
    (CFSG.pCore p X).map X.subtype ≤ CFSG.pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using conj_mem_map_of_characteristic (hYN y.2) hl
      · exact ((CFSG.pCore_isPGroup).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => conj_mem_map_of_characteristic ?_ hl⟩,
      (CFSG.pCore_isPGroup).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

omit [Finite H] in
theorem sylow_normal_of_isSubnormal {p : ℕ} [Fact p.Prime] (P : Sylow p H)
    (hP : (P : Subgroup H).IsSubnormal) : (P : Subgroup H).Normal := by
  have htop : CFSG.pCore p (P : Subgroup H) = ⊤ := by
    apply le_antisymm le_top
    exact le_sSup ⟨inferInstance, P.isPGroup'.of_equiv Subgroup.topEquiv.symm⟩
  have h := map_pCore_le_pCore_of_isSubnormal (p := p) hP
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have h2 : CFSG.pCore p H ≤ P := IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup P
  rw [← le_antisymm h2 h]
  exact CFSG.pCore_normal

end Helpers

variable {H : Type} [Group H] [Finite H]

theorem core_free_normal_sylow (hcore : CFSG.oddCore H = ⊥) (P : Sylow 2 H)
    (hP : IsElementarySixteenOrderFiveAutomizer (P : Subgroup H)) : (P : Subgroup H).Normal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨e⟩, hidx, hirr⟩ := hP
  set Pg := (P : Subgroup H) with hPg
  set N := Subgroup.normalizer (Pg : Set H) with hN
  set C := Subgroup.centralizer (Pg : Set H) with hC
  by_contra hPn
  obtain ⟨T, ⟨hTsub, hPT⟩, hTmin⟩ := WellFounded.has_min wellFounded_lt
    {X : Subgroup H | X.IsSubnormal ∧ Pg ≤ X} ⟨⊤, Subgroup.IsSubnormal.top, le_top⟩
  have hTmin' : ∀ X : Subgroup H, X.IsSubnormal → Pg ≤ X → X ≤ T → X = T := fun X hX hPX hXT =>
    by_contra fun hne => hTmin X ⟨hX, hPX⟩ (lt_of_le_of_ne hXT hne)
  set P' : Sylow 2 T := P.subtype hPT with hP'
  have hP'coe : (P' : Subgroup T) = Pg.subgroupOf T := Sylow.coe_subtype _ _
  have hP'map : (P' : Subgroup T).map T.subtype = Pg := by
    rw [hP'coe, Subgroup.map_subgroupOf_eq_of_le hPT]
  set N' := Subgroup.normalizer ((P' : Subgroup T) : Set T) with hN'
  set C' := Subgroup.centralizer ((P' : Subgroup T) : Set T) with hC'
  have hmemN' : ∀ t' : T, t' ∈ N' → (t' : H) ∈ N := by
    intro t' ht'
    have h : (t' : H) ∈ (Subgroup.normalizer ((Pg.subgroupOf T : Subgroup T) : Set T)).map
        T.subtype := ⟨t', by rw [← hP'coe]; exact ht', rfl⟩
    rw [map_normalizer_subgroupOf_eq hPT] at h
    exact h.1
  have hmemC : ∀ t' : T, (t' : H) ∈ C → t' ∈ C' := by
    intro t' ht'
    rw [hC', Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have hx' : (x : H) ∈ Pg := by
      have := hx
      rw [SetLike.mem_coe, hP'coe, Subgroup.mem_subgroupOf] at this
      exact this
    exact (Subgroup.mem_centralizer_iff.mp ht') _ hx'
  by_cases hNC : N' ≤ C'
  · have hcomp := MonoidHom.ker_transferSylow_isComplement' P' hNC
    set Q' := (MonoidHom.transferSylow P' hNC).ker with hQ'
    have hQodd : Odd (Nat.card Q') := by
      have hnd := P'.not_dvd_index
      rw [hcomp.index_eq_card] at hnd
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
    have hQsub : (Q'.map T.subtype).IsSubnormal := by
      refine Subgroup.IsSubnormal.step _ T (Subgroup.map_subtype_le _) hTsub ?_
      have h : (Q'.map T.subtype).subgroupOf T = Q' :=
        Subgroup.comap_map_eq_self_of_injective T.subtype_injective Q'
      rw [h]
      infer_instance
    have hQbot := eq_bot_of_isSubnormal_of_odd hcore hQsub
      (by rwa [Subgroup.card_map_of_injective T.subtype_injective])
    rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at hQbot
    have hPtop : (P' : Subgroup T) = ⊤ := by
      have := hcomp.sup_eq_top
      rwa [hQbot, bot_sup_eq] at this
    rw [hP'coe, Subgroup.subgroupOf_eq_top] at hPtop
    have hTP : T = Pg := le_antisymm hPtop hPT
    have hPsub : Pg.IsSubnormal := hTP ▸ hTsub
    exact hPn (sylow_normal_of_isSubnormal P hPsub)
  obtain ⟨t', ht'N, ht'C⟩ := Set.not_subset.mp hNC
  have htN : (t' : H) ∈ N := hmemN' t' ht'N
  have htC : (t' : H) ∉ C := fun h => ht'C (hmemC t' h)
  have hinvN := fun A hAP hA => invariant_of_generator hidx htN htC (A := A) hAP hA
  have hTsimple : IsSimpleGroup T := by
    have hnt : Nontrivial T := ⟨⟨t', 1, fun h => ht'C (h ▸ Subgroup.one_mem _)⟩⟩
    refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun K' hK' => ?_ }
    set K := K'.map T.subtype with hK
    have hKT : K ≤ T := Subgroup.map_subtype_le _
    have hKsubT : K.subgroupOf T = K' :=
      Subgroup.comap_map_eq_self_of_injective T.subtype_injective K'
    have hKsub : K.IsSubnormal :=
      Subgroup.IsSubnormal.step K T hKT hTsub (by rw [hKsubT]; exact hK')
    have hA : ∀ a ∈ K ⊓ Pg, (t' : H) * a * (t' : H)⁻¹ ∈ K ⊓ Pg := by
      rintro a ⟨haK, haP⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htN a).mp haP⟩
      obtain ⟨a', ha', rfl⟩ := haK
      exact ⟨t' * a' * t'⁻¹, hK'.conj_mem a' ha' t', by simp⟩
    rcases hirr (K ⊓ Pg) inf_le_right (hinvN _ inf_le_right hA) with hbot | htop
    · left
      have hinf : (P' : Subgroup T) ⊓ K' = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxP, hxK⟩ := Subgroup.mem_inf.mp hx
        have hxP' : (x : H) ∈ Pg := by
          rw [hP'coe, Subgroup.mem_subgroupOf] at hxP
          exact hxP
        have hmem : (x : H) ∈ K ⊓ Pg := ⟨⟨x, hxK, rfl⟩, hxP'⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
      obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal P' (N := K')
      rw [hinf, Subgroup.bot_subgroupOf] at hQ
      have hcard := Sylow.card_eq_multiplicity Q
      rw [hQ, Subgroup.card_bot] at hcard
      have hv : (Nat.card K').factorization 2 = 0 := by
        by_contra hv
        have h2 : 2 ≤ 2 ^ (Nat.card K').factorization 2 :=
          Nat.le_self_pow hv 2
        omega
      have hodd : Odd (Nat.card K) := by
        rw [Subgroup.card_map_of_injective T.subtype_injective]
        refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 => ?_)
        have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
        omega
      have hKbot := eq_bot_of_isSubnormal_of_odd hcore hKsub hodd
      rw [hK, Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at hKbot
      exact hKbot
    · right
      have hPK : Pg ≤ K := by
        rw [← htop]
        exact inf_le_left
      have hKeq := hTmin' K hKsub hPK hKT
      apply Subgroup.map_injective T.subtype_injective
      rw [← hK, hKeq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨x, hxP, hxt⟩ : ∃ x ∈ Pg, x * (t' : H) ≠ (t' : H) * x := by
    by_contra hall
    push Not at hall
    exact htC (Subgroup.mem_centralizer_iff.mpr hall)
  have hnonab : ∃ a b : T, a * b ≠ b * a :=
    ⟨⟨x, hPT hxP⟩, t', fun h => hxt (congrArg Subtype.val h)⟩
  have hidx' : (C'.subgroupOf N').index = 5 := by
    let ρ : N' →* N ⧸ C.subgroupOf N :=
      (QuotientGroup.mk' (C.subgroupOf N)).comp
        { toFun := fun n => ⟨((n : T) : H), hmemN' n n.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
    have hker : ρ.ker = C'.subgroupOf N' := by
      ext n
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      simp only [ρ, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      constructor
      · exact hmemC (n : T)
      · intro hn
        rw [hC, Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : (⟨y, hPT hy⟩ : T) ∈ (P' : Subgroup T) := by
          rw [hP'coe, Subgroup.mem_subgroupOf]
          exact hy
        exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hn) _ hy')
    have hrange : ρ.range = ⊤ := by
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hne : ρ ⟨t', ht'N⟩ ≠ 1 := by
        intro h
        exact ht'C ((Subgroup.mem_subgroupOf).mp (hker ▸ (MonoidHom.mem_ker.mpr h)))
      rw [eq_top_iff, ← zpowers_eq_top_of_prime_card hidx hne, Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    rw [← hker, Subgroup.index_ker, hrange, Subgroup.card_top]
    exact hidx
  have hirr' : ∀ A' : Subgroup T, A' ≤ P' →
      (∀ n ∈ N', ∀ a ∈ A', n * a * n⁻¹ ∈ A') → A' = ⊥ ∨ A' = P' := by
    intro A' hA'P hA'
    have hAP : A'.map T.subtype ≤ Pg := by
      rw [← hP'map]
      exact Subgroup.map_mono hA'P
    have hAt : ∀ a ∈ A'.map T.subtype, (t' : H) * a * (t' : H)⁻¹ ∈ A'.map T.subtype := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨t' * a * t'⁻¹, hA' t' ht'N a ha, by simp⟩
    rcases hirr _ hAP (hinvN _ hAP hAt) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).mp h
    · right
      apply Subgroup.map_injective T.subtype_injective
      rw [h, hP'map]
  exact simple_elementary_sixteen_order_five_automizer_impossible hnonab P'
    ⟨(MulEquiv.subgroupCongr hP'coe).trans ((Subgroup.subgroupOfEquivOfLe hPT).trans e)⟩
    hidx' hirr'

theorem core_free_elementary_sixteen_order_five_normal_sylow (hcore : CFSG.oddCore H = ⊥)
    (P : Sylow 2 H) (hiso : Nonempty ((P : Subgroup H) ≃* Multiplicative (Fin 4 → ZMod 2)))
    (hindex : ((Subgroup.centralizer ((P : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((P : Subgroup H) : Set H))).index = 5)
    (hirreducible : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup H) : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
        A = ⊥ ∨ A = P) :
    (P : Subgroup H).Normal ∧ Subgroup.centralizer ((P : Subgroup H) : Set H) = P ∧
      Nat.card H = 80 ∧
      ∃ h : H, orderOf h = 5 ∧ (P : Subgroup H) ⊔ Subgroup.zpowers h = ⊤ ∧
        (P : Subgroup H) ⊓ Subgroup.zpowers h = ⊥ ∧
        (∀ A : Subgroup H, A ≤ P → (∀ a ∈ A, h * a * h⁻¹ ∈ A) → A = ⊥ ∨ A = P) ∧
        ∀ x ∈ (P : Subgroup H), h * x * h⁻¹ = x → x = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsElementarySixteenOrderFiveAutomizer (P : Subgroup H) := ⟨hiso, hindex, hirreducible⟩
  have hnormal := core_free_normal_sylow hcore P hP
  obtain ⟨⟨e⟩, hidx, hirr⟩ := hP
  obtain ⟨hcard16, hcomm, hsq⟩ := elementarySixteen_facts e
  set Pg := (P : Subgroup H) with hPg
  set C := Subgroup.centralizer (Pg : Set H) with hC
  have hNtop : Subgroup.normalizer (Pg : Set H) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hnormal
  have hPC : Pg ≤ C := fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  set A : Subgroup C := Pg.subgroupOf C with hA
  have hAcenter : A ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp y.2) x (Subgroup.mem_subgroupOf.mp hx)).symm
  have hAcard : Nat.card A = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).trans hcard16
  have hAodd : Odd A.index := by
    have hSyl : ¬ 2 ∣ Pg.index := P.not_dvd_index
    have hdvd : A.index ∣ Pg.index := Subgroup.relIndex_dvd_index_of_le hPC
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSyl)) hdvd
  have hcop : Nat.Coprime (Nat.card A) A.index := by
    rw [hAcard, show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hAodd)
  obtain ⟨K, hKcard, hAK, -, -, hKchar, -⟩ := central_hall_direct_complement A hAcenter hcop
  have hKbot : K.map C.subtype = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore]
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_map_of_injective C.subtype_injective, hKcard]
    exact hAodd
  rw [Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at hKbot
  rw [hKbot, sup_bot_eq, hA, Subgroup.subgroupOf_eq_top] at hAK
  have hCP : C = Pg := le_antisymm hAK hPC
  have hidxP : Pg.index = 5 := by
    rw [hNtop, hCP, ← Subgroup.relIndex, Subgroup.relIndex_top_right] at hidx
    exact hidx
  have hcardH : Nat.card H = 80 := by
    rw [← Pg.card_mul_index, hcard16, hidxP]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 (by rw [hcardH]; norm_num)
  have hhP : h ∉ Pg := by
    intro hhP
    have h2 : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq h hhP)
    rw [hh] at h2
    norm_num at h2
  have hhN : h ∈ Subgroup.normalizer (Pg : Set H) := by rw [hNtop]; exact Subgroup.mem_top h
  have hhC : h ∉ C := by rw [hCP]; exact hhP
  refine ⟨hnormal, hCP, hcardH, h, hh, ?_, ?_, ?_, ?_⟩
  · apply Subgroup.eq_top_of_card_eq
    have h16 : 16 ∣ Nat.card (Pg ⊔ Subgroup.zpowers h : Subgroup H) :=
      hcard16 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h5 : 5 ∣ Nat.card (Pg ⊔ Subgroup.zpowers h : Subgroup H) := by
      have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers h ≤ Pg ⊔ _)
      rwa [Nat.card_zpowers, hh] at this
    have h80 : 80 ∣ Nat.card (Pg ⊔ Subgroup.zpowers h : Subgroup H) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h16 h5
    have hle : Nat.card (Pg ⊔ Subgroup.zpowers h : Subgroup H) ≤ 80 :=
      hcardH ▸ Subgroup.card_le_card_group _
    rw [hcardH]
    exact le_antisymm hle (Nat.le_of_dvd (Nat.card_pos) h80)
  · rw [eq_bot_iff]
    rintro x ⟨hxP, hxh⟩
    rw [Subgroup.mem_bot]
    have h1 : orderOf x ∣ 5 := hh ▸ orderOf_dvd_of_mem_zpowers hxh
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq x hxP)
    have h3 : orderOf x ∣ Nat.gcd 5 2 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 5 2 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  · intro B hBP hB
    exact hirr B hBP (invariant_of_generator hidx hhN hhC hBP hB)
  · intro x hxP hx
    set F := Pg ⊓ Subgroup.centralizer ({h} : Set H) with hF
    have hFinv : ∀ a ∈ F, h * a * h⁻¹ ∈ F := by
      rintro a ⟨haP, haC⟩
      have hah : a * h = h * a := Subgroup.mem_centralizer_singleton_iff.mp haC
      have : h * a * h⁻¹ = a := by rw [← hah, mul_inv_cancel_right]
      rw [this]
      exact ⟨haP, haC⟩
    rcases hirr F inf_le_left (invariant_of_generator hidx hhN hhC inf_le_left hFinv) with
      hbot | htop
    · have hxh : x * h = h * x := by
        calc x * h = (h * x * h⁻¹) * h := by rw [hx]
          _ = h * x := by group
      have hxF : x ∈ F := ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hxh⟩
      rw [hbot, Subgroup.mem_bot] at hxF
      exact hxF
    · exfalso
      apply hhC
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyF : y ∈ F := by rw [htop]; exact hy
      exact Subgroup.mem_centralizer_singleton_iff.mp hyF.2

end CFSG.LyonsUnitaryFour
