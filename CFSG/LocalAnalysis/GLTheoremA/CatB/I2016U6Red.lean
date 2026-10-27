module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma103
public import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Cat
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1210

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB
  CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YD4

theorem exists_center_two_part {Q : Type} [Group Q] [Finite Q] (σ : MulAut Q)
    (h2 : 2 ∣ Nat.card ↥(Subgroup.center Q)) :
    ∃ R : Subgroup Q, R ≠ ⊥ ∧ IsPGroup 2 ↥R ∧ R ≤ Subgroup.center Q ∧
      R.map σ.toMonoidHom = R := by
  have hcenter : ∀ τ : MulAut Q, ∀ x ∈ Subgroup.center Q, τ x ∈ Subgroup.center Q := by
    intro τ x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro z
    have h := hx (τ.symm z)
    have h' := congrArg τ h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  let R : Subgroup Q :=
    { carrier := {x | x ∈ Subgroup.center Q ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}
      mul_mem' := by
        rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
        refine ⟨Subgroup.mul_mem _ ha hb, k + l, ?_⟩
        have hcomm : Commute a b := (Subgroup.mem_center_iff.1 hb a)
        rw [hcomm.mul_pow, pow_add, pow_mul, hk, one_pow, mul_comm (2 ^ k), pow_mul, hl, one_pow,
          mul_one]
      one_mem' := ⟨Subgroup.one_mem _, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        exact ⟨Subgroup.inv_mem _ ha, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hRτ : ∀ τ : MulAut Q, ∀ x ∈ R, τ x ∈ R := by
    rintro τ x ⟨hx, k, hk⟩
    exact ⟨hcenter τ x hx, k, by rw [← map_pow, hk, map_one]⟩
  refine ⟨R, ?_, ?_, fun x hx => hx.1, ?_⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) 2 h2
    apply (Subgroup.nontrivial_iff_ne_bot R).1
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    refine ⟨(z : Q), ⟨z.2, 1, by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      simpa using congrArg Subtype.val this⟩, ?_⟩
    intro h
    have hz1 : z = 1 := Subtype.ext h
    rw [hz1, orderOf_one] at hz
    omega
  · intro x
    obtain ⟨_, k, hk⟩ := x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · refine Subgroup.ext fun y => ?_
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hRτ σ x hx
    · intro hy
      exact ⟨σ.symm y, hRτ σ.symm y hy, by simp⟩

theorem card_S6 : Nat.card LevelLieU6.S6 = 9196830720 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := CFSG.Fischer.F4) Nat.prime_two
    le_rfl CatB.U52Layer.hF4card (by norm_num)]
  decide

theorem exists_lift_two_subgroup {Q S : Type} [Group Q] [Finite Q] [Group S] (π : Q →* S)
    (hπs : Function.Surjective π) (hπk : ∀ x, π x = 1 → x ∈ Subgroup.center Q)
    {Rb : Subgroup S} (hRb0 : Rb ≠ ⊥) (hRb2 : IsPGroup 2 ↥Rb) {X : Subgroup Q}
    (hX : ∀ x ∈ X, ∀ y ∈ Rb, π x * y * (π x)⁻¹ ∈ Rb) (σ : MulAut Q)
    (hσ : ∀ x, π (σ x) ∈ Rb ↔ π x ∈ Rb) :
    ∃ R : Subgroup Q, R ≠ ⊥ ∧ IsPGroup 2 ↥R ∧ X ≤ Subgroup.normalizer (R : Set Q) ∧
      R.map σ.toMonoidHom = R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite S := Finite.of_surjective π hπs
  let Rh : Subgroup Q := Rb.comap π
  let φ : ↥Rh →* ↥Rb := (π.comp Rh.subtype).codRestrict Rb (fun x => x.2)
  have hφapply : ∀ x : ↥Rh, ((φ x : ↥Rb) : S) = π (x : Q) := fun x => rfl
  have hφsurj : Function.Surjective φ := by
    intro u
    obtain ⟨x, hx⟩ := hπs (u : S)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show π x ∈ Rb
      rw [hx]; exact u.2
    · apply Subtype.ext
      exact hx
  have hφker : φ.ker ≤ Subgroup.center ↥Rh := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : Q) * (x : Q) = (x : Q) * (y : Q)
    have h1 : π (x : Q) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [hφapply] using h
    exact Subgroup.mem_center_iff.mp (hπk _ h1) (y : Q)
  haveI : Group.IsNilpotent ↥Rb := hRb2.isNilpotent
  haveI : Group.IsNilpotent ↥Rh := Subgroup.isNilpotent_of_ker_le_center φ hφker
  obtain ⟨𝒬 : Sylow 2 ↥Rh⟩ := (inferInstance : Nonempty (Sylow 2 ↥Rh))
  let R : Subgroup Q := (𝒬 : Subgroup ↥Rh).map Rh.subtype
  have h𝒬n : (𝒬 : Subgroup ↥Rh).Normal := inferInstance
  have hmem2 : ∀ g : Q, g ∈ Rh → (∃ k : ℕ, g ^ 2 ^ k = 1) → g ∈ R := by
    rintro g hg ⟨k, hk⟩
    have : (⟨g, hg⟩ : ↥Rh) ∈ 𝒬 :=
      CFSG.GroupTheory.mem_sylow_of_pow_eq_one h𝒬n (k := k) (Subtype.ext (by simpa using hk))
    exact Subgroup.mem_map.mpr ⟨_, this, rfl⟩
  have hRpow : ∀ g ∈ R, ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := 𝒬.isPGroup' ⟨q, hq⟩
    exact ⟨k, by simpa using congrArg (fun x : ↥(𝒬 : Subgroup ↥Rh) => ((x : ↥Rh) : Q)) hk⟩
  have hRleRh : ∀ g ∈ R, g ∈ Rh := by
    rintro _ ⟨q, _, rfl⟩
    exact q.2
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have h2U0 : 2 ∣ Nat.card ↥Rb := by
      obtain ⟨k, hkpos, hk⟩ := hRb2.nontrivial_iff_card.mp ((Subgroup.nontrivial_iff_ne_bot Rb).mpr hRb0)
      rw [hk]
      simpa using Nat.pow_dvd_pow 2 hkpos
    have h2U : 2 ∣ Nat.card ↥Rh :=
      dvd_trans h2U0 (Subgroup.card_dvd_of_surjective hφsurj)
    have hQne : (𝒬 : Subgroup ↥Rh) ≠ ⊥ := Sylow.ne_bot_of_dvd_card 𝒬 h2U
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective (f := Rh.subtype)
      (H := (𝒬 : Subgroup ↥Rh)) Subtype.coe_injective).mp hbot)
  · exact 𝒬.isPGroup'.map Rh.subtype
  · have hfwd : ∀ x ∈ X, ∀ h ∈ R, x * h * x⁻¹ ∈ R := by
      intro x hx h hh
      have hhRh := hRleRh h hh
      have hmem : x * h * x⁻¹ ∈ Rh := by
        show π (x * h * x⁻¹) ∈ Rb
        rw [map_mul, map_mul, map_inv]
        exact hX x hx (π h) hhRh
      obtain ⟨k, hk⟩ := hRpow h hh
      exact hmem2 _ hmem ⟨k, by rw [conj_pow, hk]; simp⟩
    rw [Subgroup.le_normalizer_iff]
    exact hfwd
  · refine Subgroup.ext fun y => ?_
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hmem : σ q ∈ Rh := (hσ q).2 (hRleRh q hq)
      obtain ⟨k, hk⟩ := hRpow q hq
      exact hmem2 _ hmem ⟨k, by rw [← map_pow, hk, map_one]⟩
    · intro hy
      refine ⟨σ.symm y, ?_, by simp⟩
      have hmem : σ.symm y ∈ Rh := by
        have := (hσ (σ.symm y)).1
        simp only [MulEquiv.apply_symm_apply] at this
        exact this (hRleRh y hy)
      obtain ⟨k, hk⟩ := hRpow y hy
      exact hmem2 _ hmem ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem false_of_subnormal_top {Q S : Type} [Group Q] [Group S] [IsSimpleGroup S] [Finite S]
    (π : Q →* S) (hπs : Function.Surjective π) (hπk : ∀ x, π x = 1 → x ∈ Subgroup.center Q)
    {I : Subgroup Q} (hI : CFSG.Open.IsSubnormal I ⊤)
    {Tq : Type} [Group Tq] [IsSimpleGroup Tq] [Finite Tq] (hTnc : ¬ ∀ a b : Tq, a * b = b * a)
    (Ψ : ↥I →* Tq) (hΨ : Function.Surjective Ψ) (hcard : Nat.card S ≠ Nat.card Tq) : False := by
  have hIs' : CFSG.Open.IsSubnormal (I.map π) ⊤ := by
    have h := CFSG.Open.IsSubnormal.map π hI
    rwa [Subgroup.map_top_of_surjective π hπs] at h
  rcases CFSG.Open.IsSubnormal.eq_bot_or_top hIs' with hbot | htop
  · apply hTnc
    intro s t
    obtain ⟨a, rfl⟩ := hΨ s
    obtain ⟨b, rfl⟩ := hΨ t
    have haI : π (a : Q) = 1 := by
      have : π (a : Q) ∈ I.map π := Subgroup.mem_map_of_mem π a.2
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have ha : (a : Q) ∈ Subgroup.center Q := hπk _ haI
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.1 ha b).symm
  · obtain ⟨φI, hφI, -⟩ := descend_simple hTnc π hπk Ψ hΨ
    have hrt : (π.comp I.subtype).range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact htop
    haveI : IsSimpleGroup ↥(π.comp I.subtype).range := by
      rw [hrt]
      exact Subgroup.topEquiv.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φI.ker with hk | hk
    · have hinj : Function.Injective φI := (MonoidHom.ker_eq_bot_iff φI).1 hk
      have hc1 : Nat.card ↥(π.comp I.subtype).range = Nat.card Tq :=
        Nat.card_congr (Equiv.ofBijective φI ⟨hinj, hφI⟩)
      have hc2 : Nat.card ↥(π.comp I.subtype).range = Nat.card S := by
        rw [hrt]
        exact Subgroup.card_top
      exact hcard (hc2.symm.trans hc1)
    · apply hTnc
      intro s t
      obtain ⟨x, rfl⟩ := hφI s
      obtain ⟨y, rfl⟩ := hφI t
      have h1 : φI x = 1 := MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top x)
      have h2 : φI y = 1 := MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top y)
      rw [h1, h2]

@[expose] def U6Key : Prop :=
  ∀ (β : MulAut LevelLieU6.S6), β ^ 3 = 1 → β ≠ 1 →
  ∀ (H P T : Subgroup LevelLieU6.S6),
    (∀ x ∈ H, β x = x) → I2016.HasA6Quot H → (∀ x ∈ P, β x = x) →
    (∃ (Tq : Type) (_ : Group Tq) (f : ↥P →* Tq), Function.Surjective f ∧ IsSimpleGroup Tq ∧
        Nat.card Tq = 25920 ∧ Nat.Coprime 3 (Nat.card f.ker)) →
    T ≠ ⊥ → IsPGroup 2 ↥T → T.map β.toMonoidHom = T →
    H ≤ Subgroup.normalizer (T : Set LevelLieU6.S6) →
    ∃ R : Subgroup LevelLieU6.S6, R ≠ ⊥ ∧ IsPGroup 2 ↥R ∧
      P ≤ Subgroup.normalizer (R : Set LevelLieU6.S6) ∧ R.map β.toMonoidHom = R

theorem i2016FactU6_of_key (hKey : U6Key) : I2016.I2016FactU6 := by
  intro Q _ _ σ A I T hQ hcat hσ3 hAσ hA6 hIs hIt hT0 hT2 hTσ hAN
  classical
  by_cases hZ2 : 2 ∣ Nat.card ↥(Subgroup.center Q)
  · obtain ⟨R, hR0, hR2, hRc, hRσ⟩ := exists_center_two_part σ hZ2
    refine ⟨R, hR0, hR2, ?_, hRσ⟩
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hcomm : ∀ y ∈ R, x * y * x⁻¹ = y := fun y hy => by
      rw [(Subgroup.mem_center_iff.1 (hRc hy) x)]
      group
    constructor
    · intro hh
      rw [hcomm h hh]
      exact hh
    · intro hh
      have h1 : x * h * x⁻¹ = h := by
        have hc : x⁻¹ * (x * h * x⁻¹) = (x * h * x⁻¹) * x⁻¹ :=
          Subgroup.mem_center_iff.1 (hRc hh) x⁻¹
        have e : x * h * x⁻¹ = x⁻¹ * (x * h * x⁻¹) * x := by
          rw [hc]; group
        rw [e]
        group
      rw [← h1]
      exact hh
  · haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
    have hcat9 : catalogIs (Q ⧸ Subgroup.center Q) S9.isU6two := hcat
    obtain ⟨eS⟩ := HSubT.nonempty_S6_of_isU6two hcat9
    haveI : IsSimpleGroup LevelLieU6.S6 := LevelLieU6.isSimple_S6
    haveI : Finite LevelLieU6.S6 := Nat.finite_of_card_ne_zero (by rw [card_S6]; norm_num)
    let π : Q →* LevelLieU6.S6 := eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
    have hπs : Function.Surjective π := eS.surjective.comp (QuotientGroup.mk'_surjective _)
    have hπk : ∀ x, π x = 1 → x ∈ Subgroup.center Q := by
      intro x hx
      have h1 : eS (QuotientGroup.mk x) = 1 := hx
      have h2 : (QuotientGroup.mk x : Q ⧸ Subgroup.center Q) = 1 :=
        (map_eq_one_iff eS eS.injective).1 h1
      exact (QuotientGroup.eq_one_iff x).1 h2
    let ū : MulAut (Q ⧸ Subgroup.center Q) := u4AutQuot Q σ
    have hū3 : ū ^ 3 = 1 := by
      have h : u4AutQuotHom Q (σ ^ 3) = 1 := by rw [hσ3, map_one]
      rw [map_pow] at h
      exact h
    let β : MulAut LevelLieU6.S6 := MulAut.congr eS ū
    have hβ3 : β ^ 3 = 1 := by rw [← map_pow, hū3, map_one]
    have hβπ : ∀ x : Q, β (π x) = π (σ x) := by
      intro x
      show eS (ū (eS.symm (eS (QuotientGroup.mk x)))) = eS (QuotientGroup.mk (σ x))
      rw [MulEquiv.symm_apply_apply]
      show eS (u4AutQuot Q σ (QuotientGroup.mk x)) = _
      rw [u4AutQuot_mk]
    have hTinj : ∀ t ∈ T, π t = 1 → t = 1 := by
      intro t htT ht1
      have hcen := hπk t ht1
      obtain ⟨k, hk⟩ := hT2 ⟨t, htT⟩
      have hord : orderOf (t : Q) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hZ : orderOf (⟨t, hcen⟩ : ↥(Subgroup.center Q)) ∣ Nat.card ↥(Subgroup.center Q) :=
        orderOf_dvd_natCard _
      have hord' : orderOf (⟨t, hcen⟩ : ↥(Subgroup.center Q)) = orderOf t := by
        rw [← Subgroup.orderOf_coe]
      obtain ⟨j, hj, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      by_contra hne
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hj2
        exact hne (orderOf_eq_one_iff.1 hj2)
      apply hZ2
      refine dvd_trans ?_ (hord' ▸ hZ)
      rw [hj2]
      exact dvd_pow_self 2 hj0
    have hT0' : T.map π ≠ ⊥ := by
      intro hbot
      obtain ⟨⟨t, htT⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT0
      have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
      have : π t ∈ T.map π := Subgroup.mem_map_of_mem π htT
      rw [hbot, Subgroup.mem_bot] at this
      exact ht1 (hTinj t htT this)
    have hT2' : IsPGroup 2 ↥(T.map π) := hT2.map π
    have hTβ : (T.map π).map β.toMonoidHom = T.map π := by
      refine Subgroup.ext fun y => ?_
      constructor
      · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨σ t, (by
          have : σ t ∈ T.map σ.toMonoidHom := Subgroup.mem_map_of_mem _ ht
          rwa [hTσ] at this), (hβπ t).symm⟩
      · rintro ⟨t, ht, rfl⟩
        have : t ∈ T.map σ.toMonoidHom := by rw [hTσ]; exact ht
        obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.1 this
        exact ⟨π u, ⟨u, hu, rfl⟩, by
          show β (π u) = π t
          rw [hβπ]
          exact congrArg π hut⟩
    obtain ⟨A₀, S₆, hS₆g, f, hA₀A, hSc, hf⟩ := hA6
    obtain ⟨hSsimp, hS360⟩ := CatB.I1431YU5.isA6_isSimpleGroup hSc
    haveI : IsSimpleGroup S₆ := hSsimp
    have hS₆nc : ¬ ∀ a b : S₆, a * b = b * a :=
      U4Sp8.not_comm_of_simple_of_card (by rw [hS360]; norm_num)
    obtain ⟨φh, hφh, -⟩ := descend_simple hS₆nc π hπk f hf
    have hA6H : I2016.HasA6Quot (π.comp A₀.subtype).range :=
      ⟨(π.comp A₀.subtype).range, S₆, hS₆g, φh, le_rfl, hSc, hφh⟩
    have hHN : (π.comp A₀.subtype).range ≤
        Subgroup.normalizer ((T.map π : Subgroup _) : Set _) := by
      rintro _ ⟨a, rfl⟩
      exact Subgroup.le_normalizer_map π ⟨(a : Q), hAN (hA₀A a.2), rfl⟩
    have hHfix : ∀ x ∈ (π.comp A₀.subtype).range, β x = x := by
      rintro _ ⟨a, rfl⟩
      show β (π (a : Q)) = π (a : Q)
      rw [hβπ, hAσ (hA₀A a.2)]
    have hIcat : catalogIs (PSimple 3 I) S9.isU4two := by
      obtain ⟨i, hi, ⟨e⟩⟩ := hIt.1
      exact ⟨i, I1431Y.isU4two_of_isPSp43 hi, ⟨e⟩⟩
    haveI hT4s : IsSimpleGroup (PSimple 3 I) :=
      CFSG.LocalAnalysis.GLTheoremA.S10.isSimple_of_isU4two hIcat
    have hT4c : Nat.card (PSimple 3 I) = 25920 := card_of_catalogIs_u4two hIcat
    haveI : Finite (PSimple 3 I) := Nat.finite_of_card_ne_zero (by rw [hT4c]; norm_num)
    have hT4nc := not_comm_of_card_25920 hT4c
    let Ψ : ↥I →* PSimple 3 I :=
      (QuotientGroup.mk' (Subgroup.center (PQuot 3 I))).comp
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I))
    have hΨ : Function.Surjective Ψ :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    obtain ⟨φI, hφI, hφIe⟩ := descend_simple hT4nc π hπk Ψ hΨ
    have hIfix : ∀ x ∈ I, σ x = x := fun x hx => hIs.le hx
    have hPfix : ∀ x ∈ (π.comp I.subtype).range, β x = x := by
      rintro _ ⟨a, rfl⟩
      show β (π (a : Q)) = π (a : Q)
      rw [hβπ, hIfix a a.2]
    have hker3 : Nat.Coprime 3 (Nat.card φI.ker) := by
      have hcen : Subgroup.center (PQuot 3 I) = ⊥ := by
        have h1 := hIt.2
        rw [Subgroup.card_eq_one] at h1
        exact h1
      have hΨker : Ψ.ker = GLAPPrimeCore 3 ↥I := by
        ext x
        rw [MonoidHom.mem_ker]
        show (QuotientGroup.mk' (Subgroup.center (PQuot 3 I)))
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) x) = 1 ↔ _
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcen, Subgroup.mem_bot,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hkerm : φI.ker = Ψ.ker.map (π.comp I.subtype).rangeRestrict := by
        refine Subgroup.ext fun y => ?_
        constructor
        · intro hy
          obtain ⟨x, rfl⟩ := (π.comp I.subtype).rangeRestrict_surjective y
          refine ⟨x, ?_, rfl⟩
          show x ∈ Ψ.ker
          rw [MonoidHom.mem_ker, ← hφIe]
          exact hy
        · rintro ⟨x, hx, rfl⟩
          rw [MonoidHom.mem_ker, hφIe]
          exact hx
      have hdvd : Nat.card φI.ker ∣ Nat.card Ψ.ker := by
        rw [hkerm]
        exact Subgroup.card_map_dvd _ _
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥I)) :=
        CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥I)
      rw [hΨker] at hdvd
      exact Nat.Coprime.coprime_dvd_right hdvd hcop
    by_cases hβ1 : β = 1
    ·
      exfalso
      have hσ1 : σ = 1 := by
        refine mulAut_eq_one_of_central hQ.1 σ fun x => hπk _ ?_
        rw [map_mul, map_inv, ← hβπ x, hβ1, MulAut.one_apply, inv_mul_cancel]
      have hfix : I2016.fixSub σ = ⊤ := by
        rw [eq_top_iff]
        intro x _
        show σ x = x
        rw [hσ1]
        rfl
      rw [hfix] at hIs
      exact false_of_subnormal_top π hπs hπk hIs hT4nc Ψ hΨ (by rw [card_S6, hT4c]; norm_num)
    · obtain ⟨Rb, hRb0, hRb2, hRbP, hRbβ⟩ := hKey β hβ3 hβ1 (π.comp A₀.subtype).range
        (π.comp I.subtype).range (T.map π) hHfix hA6H hPfix
        ⟨PSimple 3 I, inferInstance, φI, hφI, hT4s, hT4c, hker3⟩ hT0' hT2' hTβ hHN
      refine exists_lift_two_subgroup π hπs hπk hRb0 hRb2 (X := I) ?_ σ ?_
      · intro x hx y hy
        have hxP : π x ∈ (π.comp I.subtype).range := ⟨⟨x, hx⟩, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (hRbP hxP) y).1 hy
      · intro x
        constructor
        · intro h
          have h2 : β (π x) ∈ Rb := by rw [hβπ]; exact h
          rw [← hRbβ] at h2
          obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 h2
          have hzπ : z = π x := β.injective hzx
          rw [← hzπ]
          exact hz
        · intro h
          have h2 : β (π x) ∈ Rb.map β.toMonoidHom := Subgroup.mem_map_of_mem _ h
          rw [hRbβ, hβπ] at h2
          exact h2

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

end
