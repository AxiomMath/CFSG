module

public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenSL
public import CFSG.CGT.PushingUpLit.BHS.NatSL2
public import CFSG.CGT.PushingUpLit.BHS5.Gen

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS
  CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem map_commSub_mem {D : Subgroup V} {X : Subgroup (MulAut V)} {b : MulAut V}
    (hbX : ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hbD : ∀ d ∈ D, b d ∈ D) :
    ∀ c ∈ commSub D X, b c ∈ commSub D X := by
  intro c hc
  refine Subgroup.closure_induction (p := fun c _ => b c ∈ commSub D X) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨x, hx, d, hd, rfl⟩
    have h0 : (b * x * b⁻¹) (b d) = b (x d) := by
      simp [MulAut.mul_apply]
    have h1 : b (x d * d⁻¹) = (b * x * b⁻¹) (b d) * (b d)⁻¹ := by
      rw [map_mul, map_inv, h0]
    rw [h1]
    exact Subgroup.subset_closure ⟨b * x * b⁻¹, hbX x hx, b d, hbD d hd, rfl⟩
  · rw [map_one]
    exact (commSub D X).one_mem
  · intro a a' _ _ ha ha'
    rw [map_mul]
    exact (commSub D X).mul_mem ha ha'
  · intro a _ ha
    rw [map_inv]
    exact (commSub D X).inv_mem ha

theorem exists_fixed_not_mem_fixV (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {L S T : Subgroup (MulAut V)} (hL : IsSLNatSection L ⊤ (fixV L) n) (hG : SylowGood L)
    (hS : IsSylowOf 2 S L) (hT : IsPGroup 2 ↥T)
    (hTS : T ≤ Subgroup.normalizer (S : Set (MulAut V)))
    (hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ∃ v : V, v ∉ fixV L ∧ ∀ t ∈ T, t v = v := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨K, hKL, hKS, hKN, hKcard, hKfpf⟩ := hL.exists_complement hn1 hS
  have hKnorm : K ≤ Subgroup.normalizer (S : Set (MulAut V)) :=
    le_sup_left.trans (hKN.le.trans inf_le_left)
  have hDinv : ∀ x ∈ Subgroup.normalizer (S : Set (MulAut V)), ∀ d ∈ fixV S, x d ∈ fixV S :=
    fun x hx d hd => (mem_fixV_normalizer_iff hx d).2 hd
  have hDK : ∀ y ∈ K, ∀ m ∈ fixV S, y m ∈ fixV S := fun y hy m hm => hDinv y (hKnorm hy) m hm
  have hD₀K : commSub (fixV S) (K ⊔ S) = commSub (fixV S) K := by
    apply le_antisymm
    · rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, d, hd, rfl⟩
      have hx' : x ∈ ((K ⊔ S : Subgroup (MulAut V)) : Set (MulAut V)) := hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K S hKnorm] at hx'
      obtain ⟨k, hk, s, hs, rfl⟩ := hx'
      have h1 : (k * s) d * d⁻¹ = k d * d⁻¹ := by
        rw [MulAut.mul_apply, hd s hs]
      show (k * s) d * d⁻¹ ∈ commSub (fixV S) K
      rw [h1]
      exact Subgroup.subset_closure ⟨k, hk, d, hd, rfl⟩
    · exact commSub_mono le_rfl le_sup_left
  have hne : commSub (fixV S) K ≠ ⊥ := by
    intro hbot
    rw [commSub_eq_bot_iff] at hbot
    have hcardS := hL.card_fixV_sylow hn1 hG hS
    have hle : ¬ fixV S ≤ fixV L := by
      intro hle
      have h1 := Subgroup.card_le_of_le hle
      rw [hcardS] at h1
      have hpos : 0 < Nat.card (fixV L) := Nat.card_pos
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
      nlinarith
    obtain ⟨d, hdS, hdL⟩ := IsConcreteLE.not_le_iff_exists.1 hle
    have hKbot : K ≠ ⊥ := by
      intro hK
      rw [hK, Subgroup.card_bot] at hKcard
      have h2 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hKbot
    have hdk : (k : MulAut V) d ≠ d := by
      intro hkd
      apply hdL
      refine hKfpf k k.2 (fun h => hk1 (Subtype.ext h)) d ?_
      rw [hkd, mul_inv_cancel]
      exact (fixV L).one_mem
    exact hdk (hbot hdS k k.2)
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h2 : 0 < 2 ^ n := by positivity
    rw [Nat.odd_iff]
    omega
  obtain ⟨-, hinf⟩ := B1.coprime_decomp hV hKodd hDK
  have hfix : commSub (fixV S) K ⊓ fixV K = ⊥ := by
    refine eq_bot_iff.2 fun m hm => ?_
    have hmD : m ∈ fixV S := commSub_le_of_invariant hDK hm.1
    have : m ∈ (fixV S ⊓ fixV K) ⊓ commSub (fixV S) K := ⟨⟨hmD, hm.2⟩, hm.1⟩
    rw [hinf] at this
    exact this
  have hinvT : ∀ b ∈ T, ∀ c ∈ commSub (fixV S) K, b c ∈ commSub (fixV S) K := by
    intro b hb c hc
    rw [← hD₀K] at hc ⊢
    refine map_commSub_mem (fun x hx => ?_) (fun d hd => hDinv b (hTS hb) d hd) c hc
    rw [hKN] at hx ⊢
    exact ⟨(Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem (hTS hb) hx.1)
      ((Subgroup.normalizer _).inv_mem (hTS hb)), (Subgroup.mem_normalizer_iff.1 (hTL hb) x).1 hx.2⟩
  obtain ⟨m, hmD₀, hm1, hmT⟩ := B1.exists_fixed_ne_one hV hT hinvT hne
  refine ⟨m, fun hmL => hm1 ?_, hmT⟩
  have hmK : m ∈ fixV K := fixV_anti hKL hmL
  have : m ∈ commSub (fixV S) K ⊓ fixV K := ⟨hmD₀, hmK⟩
  rw [hfix] at this
  exact this

omit [Finite V] in
theorem IsSLNatSection.inf_centSub_eq_bot {n : ℕ} {E : Subgroup (MulAut V)} {P Z : Subgroup V}
    (hnat : IsSLNatSection E P Z n) : E ⊓ centSub P = ⊥ := by
  obtain ⟨-, θ, β, hβs, -, hβe⟩ := hnat
  refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
  obtain ⟨heE, hecen⟩ := he
  have h1 : θ ⟨e, heE⟩ = 1 := by
    apply eq_one_of_forall_smul_vec
    intro v
    obtain ⟨p, hp⟩ := hβs (Multiplicative.ofAdd v)
    have hpW : (e : MulAut V) p ∈ P := by rw [hecen p p.2]; exact p.2
    have hp' : (⟨e p, hpW⟩ : ↥P) = p := Subtype.ext (hecen p p.2)
    have := hβe ⟨e, heE⟩ p hpW
    rw [hp', hp] at this
    have h2 := congrArg Multiplicative.toAdd this
    have h3 : (θ ⟨e, heE⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec v = v := by
      simpa only [toAdd_ofAdd] using h2.symm
    exact h3
  have : (⟨e, heE⟩ : ↥E) = 1 := θ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

omit [Finite V] in
theorem isSLNatSection_autSub {n : ℕ} {E : Subgroup (MulAut V)} {P : Subgroup V}
    (hnat : IsSLNatSection E P (P ⊓ fixV E) n) (hEst : E ≤ stabSub P) :
    IsSLNatSection (autSub E P) (⊤ : Subgroup ↥P) (fixV (autSub E P)) n := by
  have hEcen : E ⊓ centSub P = ⊥ := IsSLNatSection.inf_centSub_eq_bot hnat
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_autSub hEst hEcen
  refine ⟨fun x _ p _ => trivial, φ.symm.trans θ, β.comp (Subgroup.topEquiv (G := ↥P)).toMonoidHom,
    hβs.comp (Subgroup.topEquiv (G := ↥P)).surjective, ?_, ?_⟩
  · ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show β (p : ↥P) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, mem_fixV_autSub]
    constructor
    · intro h g hg _
      exact h.2 g hg
    · intro h
      exact ⟨(p : ↥P).2, fun g hg => h g hg (hEst hg)⟩
  · intro x p hp
    obtain ⟨e, rfl⟩ := φ.surjective x
    have hep : (e : MulAut V) (p : ↥P) ∈ P := by
      have h2 := (((φ e : ↥(autSub E P)) : MulAut ↥P) (p : ↥P)).2
      rw [hφ e p] at h2
      exact h2
    show β ⟨_, _⟩ = _
    rw [show (φ.symm.trans θ) (φ e) = θ e by simp]
    exact (congrArg β (Subtype.ext (hφ e p))).trans (hβe e p hep)

theorem isSylowOf_autSub {E S : Subgroup (MulAut V)} {U : Subgroup V} (hEst : E ≤ stabSub U)
    (hEcen : E ⊓ centSub U = ⊥) (hS : IsSylowOf 2 S E) :
    IsSylowOf 2 (autSub S U) (autSub E U) := by
  have hSE : S ≤ E := hS.1
  have hSst : S ≤ stabSub U := hSE.trans hEst
  have hScen : S ⊓ centSub U = ⊥ := eq_bot_iff.2 (hEcen ▸ inf_le_inf_right _ hSE)
  have hcS : Nat.card (autSub S U) = Nat.card S := by
    have := card_autSub_mul hSst
    rwa [hScen, Subgroup.card_bot, mul_one] at this
  have hcE : Nat.card (autSub E U) = Nat.card E := by
    have := card_autSub_mul hEst
    rwa [hEcen, Subgroup.card_bot, mul_one] at this
  have hle : autSub S U ≤ autSub E U := autSub_mono hSE U
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS.2.1
    exact IsPGroup.iff_card.2 ⟨k, hcS.trans hk⟩
  · have h1 := Subgroup.relIndex_mul_card (autSub S U) (autSub E U)
    have h2 := Subgroup.relIndex_mul_card S E
    rw [inf_eq_left.2 hle, hcS, hcE] at h1
    rw [inf_eq_left.2 hSE] at h2
    have hpos : 0 < Nat.card S := Nat.card_pos
    have h3 : (autSub S U).relIndex (autSub E U) = S.relIndex E :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    rw [h3]
    exact hS.2.2

theorem isSylowOf_two_of_card_sl {G : Type*} [Group G] [Finite G] {S L : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (hSL : S ≤ L) (hS : Nat.card S = 2 ^ n)
    (hL : Nat.card L = 2 ^ n * (4 ^ n - 1)) : IsSylowOf 2 S L := by
  refine ⟨hSL, IsPGroup.iff_card.2 ⟨n, hS⟩, ?_⟩
  have h1 := Subgroup.relIndex_mul_card S L
  rw [inf_eq_left.2 hSL, hS, hL] at h1
  have h2 : S.relIndex L = 4 ^ n - 1 := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos two_pos n)
    rw [h1, mul_comm]
  rw [h2]
  have h3 : 2 ∣ 4 ^ n := dvd_pow (by norm_num) (by omega)
  have h4 : 0 < 4 ^ n := by positivity
  omega

omit [Finite V] in
theorem isQuadratic_autSub {A : Subgroup (MulAut V)} {W : Subgroup V}
    (hquad : ∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ W, a' (a w * w⁻¹) = a w * w⁻¹) :
    IsQuadratic (autSub A W) := by
  rw [IsQuadratic, commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩ y hy
  obtain ⟨⟨a, ha⟩, haA, rfl⟩ := mem_autSub.1 hx
  obtain ⟨⟨a', ha'⟩, ha'A, rfl⟩ := mem_autSub.1 hy
  exact Subtype.ext (hquad a haA a' ha'A v v.2)

theorem sylowGood_autSub {n : ℕ} (hn : 2 ≤ n) {E A : Subgroup (MulAut V)} {W : Subgroup V}
    (hAst : A ≤ stabSub W) (hL : IsSLNatSection (autSub E W) ⊤ (fixV (autSub E W)) n)
    (hAE : autSub A W ≤ autSub E W) (hcard : Nat.card (autSub A W) = 2 ^ n)
    (hquad : ∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ W, a' (a w * w⁻¹) = a w * w⁻¹)
    (hidx : (fixV A).relIndex W = (cenIn A W).relIndex A) : SylowGood (autSub E W) := by
  have hn1 : 1 ≤ n := by omega
  refine IsSLNatSection.sylowGood_of_exists (L := autSub E W) (autSub A W)
    (isSylowOf_two_of_card_sl hn1 hAE hcard (hL.card_L hn1)) (isQuadratic_autSub hquad) ?_
  have hcardA : Nat.card (autSub A W) = (cenIn A W).relIndex A := card_autSub_eq_relIndex hAst
  have hcardF : Nat.card (fixV (autSub A W)) = Nat.card ↥(fixV A ⊓ W) := by
    have h1 := map_subtype_fixV_autSub hAst
    have h2 : Nat.card ((fixV (autSub A W)).map W.subtype) = Nat.card (fixV (autSub A W)) :=
      Subgroup.card_map_of_injective W.subtype_injective
    rw [h1, inf_comm] at h2
    exact h2.symm
  have hcardW : (fixV A).relIndex W * Nat.card ↥(fixV A ⊓ W) = Nat.card ↥W :=
    Subgroup.relIndex_mul_card (fixV A) W
  rw [hcardA, hcardF, ← hidx, hcardW]

theorem exists_fixed_commV_sl (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {G E A S T₁ : Subgroup (MulAut V)} (hEG : E ≤ G) (hsub : CFSG.Open.IsSubnormal E G)
    (hAG : A ≤ G) (hA : IsOff A)
    (hnat : IsSLNatSection E (commV E) (commV E ⊓ fixV E) n) (hEA : ⁅E, A⁆ ≠ ⊥)
    (hS : IsSylowOf 2 S E) (hT₁ : IsPGroup 2 ↥T₁)
    (hT₁E : T₁ ≤ Subgroup.normalizer (E : Set (MulAut V)))
    (hT₁S : T₁ ≤ Subgroup.normalizer (S : Set (MulAut V))) :
    ∃ u ∈ commV E, u ∈ fixV T₁ ∧ u ∉ fixV E := by
  obtain ⟨hAN, hAE, hcardA, hquad, hidx⟩ := two_sixteen_sl hV hn hA hAG hEG hsub hnat hEA
  have hEst : E ≤ stabSub (commV E) :=
    Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hAst : A ≤ stabSub (commV E) := hAN.trans (normalizer_commV_le_stabSub E)
  have hT₁st : T₁ ≤ stabSub (commV E) := hT₁E.trans (normalizer_commV_le_stabSub E)
  have hEcen : E ⊓ centSub (commV E) = ⊥ := IsSLNatSection.inf_centSub_eq_bot hnat
  have hL := isSLNatSection_autSub hnat hEst
  have hG' := sylowGood_autSub hn hAst hL hAE hcardA hquad hidx
  have hW : ∀ w : ↥(commV E), w ^ 2 = 1 := fun w => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hV w)
  have hTbar : IsPGroup 2 ↥(autSub T₁ (commV E)) :=
    (hT₁.comap_subtype (K := stabSub (commV E))).map (resHom (commV E))
  obtain ⟨m, hmL, hmT⟩ := exists_fixed_not_mem_fixV hW hn hL hG'
    (isSylowOf_autSub hEst hEcen hS) hTbar (autSub_le_normalizer hT₁S) (autSub_le_normalizer hT₁E)
  refine ⟨(m : V), m.2, fun t ht => ?_, fun hu => hmL (mem_fixV_autSub.2 fun g hg _ => hu g hg)⟩
  exact congrArg Subtype.val
    (hmT (resHom (commV E) ⟨t, hT₁st ht⟩) (mem_autSub.2 ⟨⟨t, hT₁st ht⟩, ht, rfl⟩))

end CFSG.CGT.PushingUpLit.BHS5
