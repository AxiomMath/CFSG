module

public import CFSG.LieType.Steinberg.CentralExt.E6E7Multiplier
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Chevalley.ExceptionalFieldFourCover
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LieType.Steinberg.Adjoint.Perfect

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits
  CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.FieldFour

theorem mem_center_of_forall_commutator_mem_center {P : Type*} [Group P] [Group.IsPerfect P]
    {y : P} (h : ∀ g, ⁅y, g⁆ ∈ Subgroup.center P) : y ∈ Subgroup.center P := by
  let _ := TorusLift.centerCommGroup P
  let φ : P →* Subgroup.center P :=
    { toFun := fun g => ⟨⁅y, g⁆, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆
        have hb := Subgroup.mem_center_iff.1 (h b) a
        have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hb, mul_inv_cancel_right]) }
  have hker : commutator P ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have h1 : φ g = 1 := hker (Subgroup.mem_top g)
  have h2 : ⁅y, g⁆ = 1 := congrArg Subtype.val h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem exists_section_of_ker_eq_bot {G : Type} [Group G] [Finite G] [Group.IsPerfect G] {p : ℕ}
    (htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* G),
      Function.Surjective η → η.ker ≤ Subgroup.center P → IsPGroup p η.ker → η.ker = ⊥)
    (E : Type) [Group E] [Finite E] (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) :
    ∃ σ : G →* E, ∀ g, π (σ g) = g := by
  set P := CFSG.Quasithin.perfectCore (⊤ : Subgroup E)
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect _)
  set η : P →* G := π.comp P.subtype
  have hmap : P.map π = ⊤ := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_top_of_surjective π hπ]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect (by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top)
  have hη : Function.Surjective η := fun g => by
    have hg : g ∈ P.map π := hmap ▸ Subgroup.mem_top g
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : η.ker ≤ Subgroup.center P := fun x hx => by
    have hx' : (x : E) ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)
    exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 (hcen hx') y)
  have hpη : IsPGroup p η.ker := fun x => by
    obtain ⟨n, hn⟩ := hp ⟨((x : P) : E), MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : π.ker => (y : E)) hn
    simpa using this
  have hinj : Function.Injective η := (MonoidHom.ker_eq_bot_iff η).1 (htriv P η hη hker hpη)
  let e : P ≃* G := MulEquiv.ofBijective η ⟨hinj, hη⟩
  exact ⟨P.subtype.comp e.symm.toMonoidHom, fun g => e.apply_symm_apply g⟩

theorem exists_section_of_coprime
    {K : Type} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (E : Type) [Group E] [Finite E] (π : E →* K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : p.Coprime (Nat.card π.ker)) : ∃ σ : K →* E, ∀ g, π (σ g) = g := by
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hC
  exact (existsUnique_section_of_sl2_lift hct hext hE.param hE.rankOne hπ hcen hC' fun ρ => by
    obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' ρ
    exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

theorem hopfMultiplier_of_isogeny {G A : Type} [Group G] [Group A] [Finite A] [Group.IsPerfect G]
    (θ : G →* A) (hθ : Function.Surjective θ) (hker : θ.ker = Subgroup.center G)
    (hZ : Subgroup.center A = ⊥)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* G), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : G →* E, ∀ g, π (σ g) = g) :
    commutator (A ⧸ Subgroup.center A) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (A ⧸ Subgroup.center A) ≃*
        Subgroup.center G) := by
  set q : G →* A ⧸ Subgroup.center A := (QuotientGroup.mk' (Subgroup.center A)).comp θ
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hθ
  have hqker : q.ker = Subgroup.center G := by
    rw [← hker]
    ext g
    simp only [q, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot]
  have hperf : Group.IsPerfect (A ⧸ Subgroup.center A) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ⟨?_⟩⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover (A ⧸ Subgroup.center A)) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (A ⧸ Subgroup.center A) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hqker.le
      fun π hπ hcen => hsplit _ π hπ hcen)
  exact (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans (MulEquiv.subgroupCongr hqker))

theorem hopfMultiplier_subsingleton {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (hZ : Subgroup.center G = ⊥)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* G), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : G →* E, ∀ g, π (σ g) = g) :
    commutator (G ⧸ Subgroup.center G) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) := by
  obtain ⟨h1, ⟨e⟩⟩ := hopfMultiplier_of_isogeny (MonoidHom.id G) Function.surjective_id
    (by rw [hZ, MonoidHom.ker_id]) hZ hsplit
  refine ⟨h1, ?_⟩
  have : Subsingleton (Subgroup.center G) := by
    rw [hZ]
    infer_instance
  exact e.toEquiv.subsingleton


section Adjoint

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem f4_four_exists_section (hK : Nat.card K = 2 ^ 2) (E : Type) [Group E] [Finite E]
    (π : E →* adjointGroup .F4 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .F4 K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(adjointGroup .F4 K) := isPerfect_f4 K
  obtain ⟨-, ⟨O⟩, -, -⟩ := f4_conclusionB K
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun _ _ _ _ η hη hC' h2 =>
        ExceptionalCover.ker_eq_bot_of_adjointGroup_four (Or.inl rfl) hK η hη hC' h2)
      E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => exists_section_of_coprime (f4_isCTGroupDatum K)
      (f4_steinbergExtras K) (f4_chevalleyExtras K O C hC) E' π' hπ' hcen' hc')

theorem e8_four_exists_section (hK : Nat.card K = 2 ^ 2) (E : Type) [Group E] [Finite E]
    (π : E →* adjointGroup .E8 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .E8 K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(adjointGroup .E8 K) := isPerfect_e8 K
  obtain ⟨-, ⟨O⟩, -, -⟩ := e8_conclusionB K
  obtain ⟨C, -, hC⟩ := e8_commutatorFormula K O
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun _ _ _ _ η hη hC' h2 => ExceptionalCover.ker_eq_bot_of_adjointGroup_four
        (Or.inr (Or.inr (Or.inr rfl))) hK η hη hC' h2)
      E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => exists_section_of_coprime (e8_isCTGroupDatum K)
      (e8_steinbergExtras K) (e8_chevalleyExtras K O C hC) E' π' hπ' hcen' hc')

theorem f4_four_hopfMultiplier (hK : Nat.card K = 2 ^ 2) :
    commutator (AdjointQuotient .F4 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .F4 K) := isPerfect_f4 K
  exact hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun E _ _ π hπ hcen => f4_four_exists_section hK E π hπ hcen

theorem e8_four_hopfMultiplier (hK : Nat.card K = 2 ^ 2) :
    commutator (AdjointQuotient .E8 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .E8 K) := isPerfect_e8 K
  exact hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun E _ _ π hπ hcen => e8_four_exists_section hK E π hπ hcen

end Adjoint


section Minuscule

variable {K : Type} [Field K] [Finite K]

theorem finite_minGroup'
    {τ : Tag} {D : MinData τ}
    (hV : D.Valid) : Finite ↥(hV.minGroup K) := by
  have : Finite (Module.End K (Fin D.d →₀ K)) := Module.finite_of_finite K
  infer_instance

theorem e6Isogeny_ker_eq_center :
    (e6Isogeny K).ker = Subgroup.center ↥(e6Data_valid.minGroup K) :=
  le_antisymm (ker_le_center_of_isQuasisimple (isQuasisimple_e6 K) (e6Isogeny_ne_one K))
    (MinusculeClosed.center_le_ker_of_surjective (e6Isogeny_surjective K)
      center_adjointGroup_eq_bot)

theorem e7Isogeny_ker_eq_center :
    (e7Isogeny K).ker = Subgroup.center ↥(e7Data_valid.minGroup K) :=
  le_antisymm (ker_le_center_of_isQuasisimple (isQuasisimple_e7 K) (exists_e7Isogeny_ne_one K))
    (MinusculeClosed.center_le_ker_of_surjective (e7Isogeny_surjective K)
      center_adjointGroup_eq_bot)

section E6

variable
  [CharP K 2]

theorem e6_four_ker_eq_bot (hK : Nat.card K = 2 ^ 2) (P : Type) [Group P] [Finite P]
    [Group.IsPerfect P] (η : P →* e6Data_valid.minGroup K) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := e6Isogeny K
  set η' : P →* adjointGroup .E6 K := θ.comp η
  have hcen' : η'.ker ≤ Subgroup.center P := fun y hy => by
    refine mem_center_of_forall_commutator_mem_center fun g => hC ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hyZ : η y ∈ Subgroup.center ↥(e6Data_valid.minGroup K) := by
      rw [← e6Isogeny_ker_eq_center]
      exact hy
    exact (Subgroup.mem_center_iff.1 hyZ (η g)).symm
  set N := CoprimeSplit.copPart 2 η'.ker hcen'
  have hN : N ≤ η'.ker := fun _ h => h.1
  let η'' : P ⧸ N →* adjointGroup .E6 K := QuotientGroup.lift N η' hN
  have hη''e : ∀ e : P, η'' (e : P ⧸ N) = η' e := fun e => rfl
  have hη'' : Function.Surjective η'' := fun g => by
    obtain ⟨e, rfl⟩ := ((e6Isogeny_surjective K).comp hη) g
    exact ⟨(e : P ⧸ N), rfl⟩
  have : Group.IsPerfect (P ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hker'' : η''.ker ≤ Subgroup.center (P ⧸ N) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ η'.ker := by
      rw [MonoidHom.mem_ker, ← hη''e]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hcen' he) z']
  have h2'' : IsPGroup 2 η''.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ η'.ker := by
      rw [MonoidHom.mem_ker, ← hη''e]
      exact hy
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := 2) hcen' he
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have hbot := ExceptionalCover.ker_eq_bot_of_adjointGroup_four (Or.inr (Or.inl rfl)) hK η''
    hη'' hker'' h2''
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ η'.ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx, map_one]
  have hxN : x ∈ N := by
    have hq : (x : P ⧸ N) ∈ η''.ker := by
      rw [MonoidHom.mem_ker, hη''e]
      exact hx'
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hq
    exact hq
  obtain ⟨n, hn⟩ := h2 ⟨x, hx⟩
  have hx1 : x ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hcop : Nat.Coprime (orderOf x) (2 ^ n) :=
    Nat.Coprime.pow_right n (CoprimeSplit.mem_copPart.1 hxN).2.symm
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
  exact Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hx1)

theorem e6_four_exists_section (hK : Nat.card K = 2 ^ 2) (E : Type) [Group E] [Finite E]
    (π : E →* e6Data_valid.minGroup K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e6Data_valid.minGroup K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(e6Data_valid.minGroup K) := isPerfect_e6 K
  have := finite_minGroup' (K := K) e6Data_valid
  obtain ⟨-, ⟨O⟩, -, -⟩ := e6_conclusionB K
  obtain ⟨C, -, hC⟩ := e6Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E6) O
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun P _ _ _ η hη hC' h2 => e6_four_ker_eq_bot hK P η hη hC' h2) E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => exists_section_of_coprime (e6Datum_isCTGroupDatum K)
      (e6Datum_steinbergExtras K) (e6_chevalleyExtras K O C hC) E' π' hπ' hcen' hc')

theorem e6_four_hopfMultiplier (hK : Nat.card K = 2 ^ 2) :
    commutator (AdjointQuotient .E6 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K) ≃*
        Multiplicative (ZMod (Nat.gcd 3 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e6Data_valid.minGroup K) := isPerfect_e6 K
  obtain ⟨hperf, ⟨e⟩⟩ := hopfMultiplier_of_isogeny (e6Isogeny K) (e6Isogeny_surjective K)
    e6Isogeny_ker_eq_center center_adjointGroup_eq_bot
    fun E _ _ π hπ hcen => e6_four_exists_section hK E π hπ hcen
  obtain ⟨hcard, hcyc⟩ := MinusculeClosed.card_center_e6 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E6

section E7

variable
  [CharP K 2]

omit [CharP K 2] in
theorem e7Isogeny_injective_four (hK : Nat.card K = 2 ^ 2) : Function.Injective (e7Isogeny K) := by
  have hZ : Subgroup.center ↥(e7Data_valid.minGroup K) = ⊥ := by
    have h1 := (MinusculeClosed.card_center_e7 K).1
    rw [hK] at h1
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using h1)
  rw [← MonoidHom.ker_eq_bot_iff, e7Isogeny_ker_eq_center, hZ]

theorem e7_four_ker_eq_bot (hK : Nat.card K = 2 ^ 2) (P : Type) [Group P] [Finite P]
    [Group.IsPerfect P] (η : P →* e7Data_valid.minGroup K) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have hθ := e7Isogeny_injective_four hK
  have hker : ((e7Isogeny K).comp η).ker = η.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h => hθ (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩
  rw [← hker]
  exact ExceptionalCover.ker_eq_bot_of_adjointGroup_four (Or.inr (Or.inr (Or.inl rfl))) hK _
    ((e7Isogeny_surjective K).comp hη) (hker ▸ hC) (hker ▸ h2)

theorem e7_four_exists_section (hK : Nat.card K = 2 ^ 2) (E : Type) [Group E] [Finite E]
    (π : E →* e7Data_valid.minGroup K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e7Data_valid.minGroup K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥(e7Data_valid.minGroup K) := isPerfect_e7 K
  have := finite_minGroup' (K := K) e7Data_valid
  obtain ⟨-, ⟨O⟩, -, -⟩ := e7_conclusionB K
  obtain ⟨C, -, hC⟩ := e7Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E7) O
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => exists_section_of_ker_eq_bot
      (fun P _ _ _ η hη hC' h2 => e7_four_ker_eq_bot hK P η hη hC' h2) E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => exists_section_of_coprime (e7Datum_isCTGroupDatum K)
      (e7Datum_steinbergExtras K) (e7_chevalleyExtras K O C hC) E' π' hπ' hcen' hc')

theorem e7_four_hopfMultiplier (hK : Nat.card K = 2 ^ 2) :
    commutator (AdjointQuotient .E7 K) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
  have : Group.IsPerfect ↥(e7Data_valid.minGroup K) := isPerfect_e7 K
  obtain ⟨hperf, ⟨e⟩⟩ := hopfMultiplier_of_isogeny (e7Isogeny K) (e7Isogeny_surjective K)
    e7Isogeny_ker_eq_center center_adjointGroup_eq_bot
    fun E _ _ π hπ hcen => e7_four_exists_section hK E π hπ hcen
  obtain ⟨hcard, hcyc⟩ := MinusculeClosed.card_center_e7 K
  rw [← hcard]
  exact ⟨hperf, ⟨e.trans (zmodCyclicMulEquiv hcyc).symm⟩⟩

end E7

end Minuscule

end CFSG.LieType.Steinberg.CentralExt.FieldFour
