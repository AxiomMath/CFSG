module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInvHub

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open scoped commutatorElement

theorem dihedral_three {G : Type*} [Group G] {a b : G} {ka kb : ℕ}
    (ha : a ^ 2 ∈ Subgroup.center G) (hb : b ^ 2 ∈ Subgroup.center G)
    (hw : (a * b) ^ 3 ∈ Subgroup.center G) (hka : a ^ (2 ^ ka) = 1) (hkb : b ^ (2 ^ kb) = 1)
    (h3 : 3 ∣ orderOf (a * b)) : ∃ s : ℕ, orderOf ((a * b) ^ (2 ^ s)) = 3 := by
  set w := a * b with hwdef
  have hzac : ∀ g : G, g * a ^ 2 = a ^ 2 * g := fun g => Subgroup.mem_center_iff.1 ha g
  have hzbc : ∀ g : G, g * b ^ 2 = b ^ 2 * g := fun g => Subgroup.mem_center_iff.1 hb g
  have h1 : a * w * a⁻¹ = b * a := by
    calc a * w * a⁻¹ = (a * a) * b * a⁻¹ := by rw [hwdef]; group
      _ = b * (a * a) * a⁻¹ := by rw [← pow_two, ← hzac b]
      _ = b * a := by group
  have h2 : b * a = w⁻¹ * (a ^ 2 * b ^ 2) := by
    have e : b ^ 2 * a = a * b ^ 2 := (hzbc a).symm
    calc b * a = b⁻¹ * (b ^ 2 * a) := by group
      _ = b⁻¹ * (a * b ^ 2) := by rw [e]
      _ = w⁻¹ * (a ^ 2 * b ^ 2) := by rw [hwdef]; group
  have hζmem : a ^ 2 * b ^ 2 ∈ Subgroup.center G := Subgroup.mul_mem _ ha hb
  have hζ : Commute w⁻¹ (a ^ 2 * b ^ 2) := Subgroup.mem_center_iff.1 hζmem w⁻¹
  have h3c : (a * w * a⁻¹) ^ 3 = w ^ 3 := by
    have : (a * w * a⁻¹) ^ 3 = a * w ^ 3 * a⁻¹ := by
      rw [conj_pow]
    rw [this, Subgroup.mem_center_iff.1 hw a, mul_inv_cancel_right]
  have h4 : (a * w * a⁻¹) ^ 3 = (w⁻¹) ^ 3 * (a ^ 2 * b ^ 2) ^ 3 := by
    rw [h1, h2, hζ.mul_pow]
  have h5 : w ^ 6 = (a ^ 2 * b ^ 2) ^ 3 := by
    have : w ^ 3 = (w⁻¹) ^ 3 * (a ^ 2 * b ^ 2) ^ 3 := h3c.symm.trans h4 |>.symm.symm
    calc w ^ 6 = w ^ 3 * w ^ 3 := by rw [← pow_add]
      _ = w ^ 3 * ((w⁻¹) ^ 3 * (a ^ 2 * b ^ 2) ^ 3) := by rw [← this]
      _ = (a ^ 2 * b ^ 2) ^ 3 := by rw [inv_pow, mul_inv_cancel_left]
  have hζ2 : (a ^ 2 * b ^ 2) ^ (2 ^ (ka + kb + 1)) = 1 := by
    have hc : Commute (a ^ 2) (b ^ 2) := Subgroup.mem_center_iff.1 hb (a ^ 2)
    have e1 : (a ^ 2) ^ (2 ^ (ka + kb + 1)) = 1 := by
      rw [← pow_mul, show 2 * 2 ^ (ka + kb + 1) = 2 ^ ka * (2 * 2 ^ (kb + 1)) by ring, pow_mul,
        hka, one_pow]
    have e2 : (b ^ 2) ^ (2 ^ (ka + kb + 1)) = 1 := by
      rw [← pow_mul, show 2 * 2 ^ (ka + kb + 1) = 2 ^ kb * (2 * 2 ^ (ka + 1)) by ring, pow_mul,
        hkb, one_pow]
    rw [hc.mul_pow, e1, e2, one_mul]
  have h6 : w ^ (6 * 2 ^ (ka + kb + 1)) = 1 := by
    rw [pow_mul, h5, ← pow_mul, mul_comm, pow_mul, hζ2, one_pow]
  have hfin : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.2 ⟨_, by positivity, h6⟩
  have ho0 : orderOf w ≠ 0 := (orderOf_pos_iff.2 hfin).ne'
  obtain ⟨s, o', hodd, hos⟩ := Nat.exists_eq_two_pow_mul_odd ho0
  have hdvd : orderOf w ∣ 3 * 2 ^ (ka + kb + 2) := by
    have := orderOf_dvd_of_pow_eq_one h6
    rwa [show 6 * 2 ^ (ka + kb + 1) = 3 * 2 ^ (ka + kb + 2) by ring] at this
  have hcop : Nat.Coprime o' (2 ^ (ka + kb + 2)) := Nat.Coprime.pow_right _ hodd.coprime_two_right
  have ho'3 : o' ∣ 3 := by
    have h1 : o' ∣ 3 * 2 ^ (ka + kb + 2) := (Dvd.intro_left _ hos.symm).trans hdvd
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop h1
  have h3o' : 3 ∣ o' := by
    have h31 : 3 ∣ 2 ^ s * o' := hos ▸ h3
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)) h31)
  have ho'eq : o' = 3 := Nat.dvd_antisymm ho'3 h3o'
  refine ⟨s, ?_⟩
  rw [orderOf_pow' _ (by positivity : 2 ^ s ≠ 0), hos, ho'eq,
    Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]

section Core

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem node_parabolic {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M)
    (hT : (S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
      (posUnipotent D).map π) (i : Fin D.rank) :
    ∃ P : Subgroup K, borel D H ≤ P ∧ rankOne D.rootGroup i ≤ P ∧
      IsMinOverBorel L S₀
        (((P.map π).comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hqker : q.ker = Z := by rw [hqdef, QuotientGroup.ker_mk']
  obtain ⟨S, hSS⟩ := McLaughlin.Lie.exists_sylow_of_isSylowTwoOf hS
  have hS₀L : S₀ ≤ L := hS.1
  set S₀' : Subgroup ↥L := S₀.subgroupOf L with hS₀'
  have hker_le_B : π.ker ≤ borel D H := fun z hz =>
    CFSG.ClassicalInvolution.WeakCT.normalizer_posUnipotent_le_borel h.ct h.extras
      (Subgroup.center_le_normalizer (posUnipotent D : Set K) (h.ker_central z hz))
  have hNY : Subgroup.normalizer (((S₀').map q : Subgroup _) : Set _) = (borel D H).map π := by
    rw [hqdef, hT]
    exact h.normalizer_map_posUnipotent
  have hBL : Subgroup.normalizer (S₀' : Set ↥L) = ((borel D H).map π).comap q := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_comap, ← hNY]
      exact Subgroup.le_normalizer_map q ⟨x, hx, rfl⟩
    · intro hx
      rw [Subgroup.mem_comap, ← hNY] at hx
      have h1 := normalizer_map_le S hq (by rw [hqker]) (by
        rw [hSS]
        exact hx)
      obtain ⟨x', hx', hxx'⟩ := h1
      have hz : x'⁻¹ * x ∈ Z := by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
      have : x = x' * (x'⁻¹ * x) := by group
      rw [this]
      refine Subgroup.mul_mem _ (by rwa [hSS] at hx')
        (Subgroup.center_le_normalizer (S₀' : Set ↥L) hz)
  obtain ⟨P, hBP, hLP, hPne, hmin⟩ := exists_minOver_of_node h.ct h.extras i
  have hcomapP : (P.map π).comap π = P := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.2 ((hker_le_B).trans hBP)
  have hY1 : (borel D H).map π ≤ P.map π := Subgroup.map_mono hBP
  have hY2 : (borel D H).map π ≠ P.map π := by
    intro heq
    apply hPne
    have := congrArg (Subgroup.comap π) heq
    rw [hcomapP, Subgroup.comap_map_eq, sup_eq_left.2 hker_le_B] at this
    exact this.symm
  have hY3 : ∀ Q : Subgroup (↥L ⧸ Z), (borel D H).map π ≤ Q → Q ≤ P.map π →
      Q = (borel D H).map π ∨ Q = P.map π := by
    intro Q hBQ hQP
    have hBc : borel D H ≤ Q.comap π := fun b hb => hBQ ⟨b, hb, rfl⟩
    have hQc : Q.comap π ≤ P := by
      have := Subgroup.comap_mono (f := π) hQP
      rwa [hcomapP] at this
    have hQ := Subgroup.map_comap_eq_self_of_surjective h.surj Q
    rcases hmin _ hBc hQc with h1 | h1
    · left; rw [← hQ, h1]
    · right; rw [← hQ, h1]
  set PL : Subgroup ↥L := (P.map π).comap q with hPL
  set BL : Subgroup ↥L := ((borel D H).map π).comap q with hBLdef
  have hBW : L ⊓ Subgroup.normalizer (S₀ : Set W) = BL.map L.subtype := by
    rw [show BL = Subgroup.normalizer (S₀' : Set ↥L) from hBL.symm, map_normalizer_eq_inf', hS₀',
      Subgroup.map_subgroupOf_eq_of_le hS₀L, inf_comm]
  have hZBL : Z ≤ BL := by
    intro z hz
    rw [hBLdef, Subgroup.mem_comap]
    have : q z = 1 := by rw [← MonoidHom.mem_ker, hqker]; exact hz
    rw [this]
    exact one_mem _
  have hPmin : IsMinOverBorel L S₀ (PL.map L.subtype) := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [hBW]
      refine lt_of_le_of_ne (Subgroup.map_mono (Subgroup.comap_mono hY1)) fun heq => ?_
      have h1 : BL = PL := Subgroup.map_injective L.subtype_injective heq
      have h2 := congrArg (Subgroup.map q) h1
      rw [hBLdef, hPL, Subgroup.map_comap_eq_self_of_surjective hq,
        Subgroup.map_comap_eq_self_of_surjective hq] at h2
      exact hY2 h2
    · intro Q hQ1 hQ2
      rw [hBW] at hQ1 ⊢
      have hQL : Q ≤ L := hQ2.trans (Subgroup.map_subtype_le _)
      have hQe : (Q.subgroupOf L).map L.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQL
      have hB' : BL ≤ Q.subgroupOf L := by
        have h1 : BL.map L.subtype ≤ (Q.subgroupOf L).map L.subtype := by rw [hQe]; exact hQ1
        exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 h1
      have hP' : Q.subgroupOf L ≤ PL := by
        have h1 : (Q.subgroupOf L).map L.subtype ≤ PL.map L.subtype := by rw [hQe]; exact hQ2
        exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 h1
      have hlow : (borel D H).map π ≤ (Q.subgroupOf L).map q := by
        have := Subgroup.map_mono (f := q) hB'
        rwa [hBLdef, Subgroup.map_comap_eq_self_of_surjective hq] at this
      have hup : (Q.subgroupOf L).map q ≤ P.map π := by
        have := Subgroup.map_mono (f := q) hP'
        rwa [hPL, Subgroup.map_comap_eq_self_of_surjective hq] at this
      have hQ' : (Q.subgroupOf L).map q = ((Q.subgroupOf L).map q) := rfl
      have hcm : ((Q.subgroupOf L).map q).comap q = Q.subgroupOf L := by
        rw [Subgroup.comap_map_eq, hqker]
        exact sup_eq_left.2 (hZBL.trans hB')
      rcases hY3 _ hlow hup with h1 | h1
      · left
        rw [← hQe]
        congr 1
        rw [← hcm, h1]
      · right
        rw [← hQe]
        congr 1
        rw [← hcm, h1]
  exact ⟨P, hBP, hLP, hPmin⟩

end Core

theorem commutator_mul_central {G : Type*} [Group G] {g h z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅g * z, h * w⁆ = ⁅g, h⁆ := by
  have h1 : ∀ x : G, x * z = z * x := fun x => Subgroup.mem_center_iff.1 hz x
  have h2 : ∀ x : G, x * w = w * x := fun x => Subgroup.mem_center_iff.1 hw x
  have e : ∀ x : G, z * x * z⁻¹ = x := fun x => by
    rw [mul_inv_eq_iff_eq_mul]; exact (h1 x).symm
  have e' : ∀ x : G, w * x * w⁻¹ = x := fun x => by
    rw [mul_inv_eq_iff_eq_mul]; exact (h2 x).symm
  calc ⁅g * z, h * w⁆ = g * (z * (h * w) * z⁻¹) * g⁻¹ * (h * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅g, h * w⁆ := by rw [e, commutatorElement_def]
    _ = g * h * (w * g⁻¹ * w⁻¹) * h⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅g, h⁆ := by rw [e', commutatorElement_def]

section Main

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem exists_two_lift {L : Subgroup W} {π : K →* ↥L ⧸ Subgroup.center ↥L} (P : Subgroup K)
    {x : K} (hx : ∃ k : ℕ, x ^ 2 ^ k = 1) (hxP : x ∈ P) :
    ∃ a : ↥L, QuotientGroup.mk' (Subgroup.center ↥L) a = π x ∧
      a ∈ (P.map π).comap (QuotientGroup.mk' (Subgroup.center ↥L)) ∧ ∃ k : ℕ, orderOf a = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  obtain ⟨xt, hxt⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) (π x)
  have hxtP : xt ∈ (P.map π).comap q := by
    rw [Subgroup.mem_comap]
    change q xt ∈ P.map π
    rw [hxt]
    exact ⟨x, hxP, rfl⟩
  have hx2 : ∃ k : ℕ, orderOf (q xt) = 2 ^ k := by
    obtain ⟨k, hk⟩ := hx
    have hd : orderOf (π x) ∣ 2 ^ k :=
      (orderOf_map_dvd π x).trans (orderOf_dvd_of_pow_eq_one hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨j, by rw [hxt]; exact hj⟩
  obtain ⟨e, ⟨k, hk⟩, hfe⟩ := exists_pElement_lift q (p := 2) hx2
  exact ⟨xt ^ e, by rw [hq, hfe]; exact hxt, Subgroup.pow_mem _ hxtP e, k, hk⟩

theorem chevGen_data {L S₀ : Subgroup W} (hL : Open.IsQuasisimple ↥L) (hS : IsSylowTwoOf S₀ L)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M)
    (h3 : ∀ i, HasInvolThree D i) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      ∃ P : Fin D.rank → Subgroup W, (∀ i, IsMinOverBorel L S₀ (P i)) ∧
      L = ⨆ i, pElementSubgroup 2 (P i) ∧
      (∀ i, ∃ x ∈ pElementSubgroup 2 (P i), orderOf x = 3 ∧
        x ∉ (Subgroup.center ↥L).map L.subtype) ∧
      ∀ i, ∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ rankOne D.rootGroup i →
        ∃ a : ↥L, QuotientGroup.mk' (Subgroup.center ↥L) a = π' x ∧
          (a : W) ∈ pElementSubgroup 2 (P i) ∧ ∃ k : ℕ, orderOf a = 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS h
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hqker : q.ker = Z := by rw [hqdef, QuotientGroup.ker_mk']
  have hrk : 0 < D.rank := by
    by_contra hr0
    have h0 : D.rank = 0 := Nat.eq_zero_of_not_pos hr0
    have hemp : IsEmpty (Fin D.rank) := by rw [h0]; infer_instance
    have hU : posUnipotent D = ⊥ := by
      refine iSup₂_eq_bot.2 fun γ hγ => ?_
      exfalso
      have : ht γ = 0 := by simp [ht, Finset.univ_eq_empty]
      have := hγ.2
      omega
    have hB : borel D H = ⊥ := by
      rw [LieType.Steinberg.borel, hU, iSup_of_empty, bot_sup_eq]
    have hK : (⊤ : Subgroup K) = ⊥ := by
      have h1 := eq_borel_sup_rankOne hπ'.ct hπ'.extras (A := ⊤) le_top
      rw [hB, bot_sup_eq] at h1
      rw [h1]
      exact iSup₂_eq_bot.2 fun i => isEmptyElim i
    have hsub : Subsingleton K := ⟨fun x y => by
      have hx : x ∈ (⊤ : Subgroup K) := trivial
      have hy : y ∈ (⊤ : Subgroup K) := trivial
      rw [hK, Subgroup.mem_bot] at hx hy
      rw [hx, hy]⟩
    have hsub' : Subsingleton (↥L ⧸ Z) := hπ'.surj.subsingleton
    obtain ⟨x, y, hxy⟩ := hL.2.toNontrivial.exists_pair_ne
    exact hxy (hsub'.elim x y)
  choose Pk hBP hLP hmin using fun i => node_parabolic hS hπ' hT i
  set PL : Fin D.rank → Subgroup ↥L := fun i => ((Pk i).map π').comap q with hPL
  have hlift : ∀ i, ∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Pk i →
      ∃ a : ↥L, q a = π' x ∧ (a : W) ∈ pElementSubgroup 2 ((PL i).map L.subtype) ∧
        ∃ k : ℕ, orderOf a = 2 ^ k := by
    intro i x hx hxP
    obtain ⟨a, haq, haP, k, hk⟩ := exists_two_lift (π := π') (Pk i) hx hxP
    refine ⟨a, haq, Subgroup.subset_closure ⟨⟨a, haP, rfl⟩, k, ?_⟩, k, hk⟩
    rw [Subgroup.orderOf_coe]; exact hk
  have hroot2 : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → ∀ x ∈ D.rootGroup γ, ∃ k : ℕ, x ^ 2 ^ k = 1 :=
    fun γ hγ x hx => by
      obtain ⟨k, hk⟩ := hπ'.pGroup γ hγ ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hαroot : ∀ i : Fin D.rank, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)⟩
  refine ⟨π', hπ', fun i => (PL i).map L.subtype, hmin, ?_, ?_, ?_⟩
  · set P : Fin D.rank → Subgroup W := fun i => (PL i).map L.subtype with hPdef
    have hPL_le : ∀ i, P i ≤ L := fun i => (hmin i).1
    set G' : Subgroup W := ⨆ i, pElementSubgroup 2 (P i) with hG'
    have hG'L : G' ≤ L := iSup_le fun i => (pElementSubgroup_le _).trans (hPL_le i)
    have hS0 : ∀ i, S₀ ≤ pElementSubgroup 2 (P i) := by
      intro i s hs
      have hsL : s ∈ L ⊓ Subgroup.normalizer (S₀ : Set W) :=
        ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
      have hsP : s ∈ P i := (hmin i).2.1.le hsL
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS.2.1) ⟨s, hs⟩
      refine Subgroup.subset_closure ⟨hsP, k, ?_⟩
      have := hk
      rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk] at this
    set i₀ : Fin D.rank := ⟨0, hrk⟩
    set Gs : Subgroup ↥L := G'.subgroupOf L with hGs
    have hrank : ∀ i, (rankOne D.rootGroup i).map π' ≤ Gs.map q := by
      intro i
      have hroot : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → D.rootGroup γ ≤ rankOne D.rootGroup i →
          (D.rootGroup γ).map π' ≤ Gs.map q := by
        rintro γ hγ hγL _ ⟨x, hx, rfl⟩
        obtain ⟨a, haq, haW, -⟩ := hlift i x (hroot2 γ hγ x hx) (hLP i (hγL hx))
        exact ⟨a, (Subgroup.mem_subgroupOf).2 (le_iSup (fun i => pElementSubgroup 2 (P i)) i haW),
          haq⟩
      show (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map π' ≤ _
      rw [Subgroup.map_sup]
      exact sup_le (hroot _ (hαroot i).1 le_sup_left) (hroot _ (hαroot i).2 le_sup_right)
    have hU : (posUnipotent D).map π' ≤ Gs.map q := by
      rw [← hT]
      refine Subgroup.map_mono fun s hs => ?_
      exact (Subgroup.mem_subgroupOf).2
        (le_iSup (fun i => pElementSubgroup 2 (P i)) i₀ (hS0 i₀ hs))
    have hK : (⊤ : Subgroup K) ≤ posUnipotent D ⊔ ⨆ i, rankOne D.rootGroup i := by
      have h1 := eq_borel_sup_rankOne hπ'.ct hπ'.extras (A := ⊤) le_top
      rw [h1]
      refine sup_le (sup_le (le_sup_of_le_right (iSup_mono fun i => hπ'.ct.H_le i))
        le_sup_left) (iSup₂_le fun i _ => le_sup_of_le_right (le_iSup _ i))
    have htop : Gs.map q = ⊤ := by
      rw [eq_top_iff, ← Subgroup.map_top_of_surjective π' hπ'.surj]
      refine (Subgroup.map_mono hK).trans ?_
      rw [Subgroup.map_sup, Subgroup.map_iSup]
      exact sup_le hU (iSup_le hrank)
    have hLG : (⊤ : Subgroup ↥L) ≤ Gs := by
      have hc : (⊤ : Subgroup ↥L) = ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ := by
        rw [← commutator_def]; exact hL.1.symm
      rw [hc, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have hmem : ∀ g : ↥L, ∃ g' ∈ Gs, g'⁻¹ * g ∈ Subgroup.center ↥L := fun g => by
        have hg : q g ∈ Gs.map q := by rw [htop]; trivial
        obtain ⟨g', hg', e⟩ := hg
        refine ⟨g', hg', ?_⟩
        have : g'⁻¹ * g ∈ q.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
        rwa [hqker] at this
      obtain ⟨g₁', hg₁', hz₁⟩ := hmem g₁
      obtain ⟨g₂', hg₂', hz₂⟩ := hmem g₂
      have e : ⁅g₁, g₂⁆ = ⁅g₁', g₂'⁆ := by
        have h1 : g₁ = g₁' * (g₁'⁻¹ * g₁) := by group
        have h2 : g₂ = g₂' * (g₂'⁻¹ * g₂) := by group
        conv_lhs => rw [h1, h2]
        exact commutator_mul_central hz₁ hz₂
      rw [e, commutatorElement_def]
      exact Gs.mul_mem (Gs.mul_mem (Gs.mul_mem hg₁' hg₂') (Gs.inv_mem hg₁')) (Gs.inv_mem hg₂')
    exact le_antisymm (fun g hg => (Subgroup.mem_subgroupOf).1 (hLG (Subgroup.mem_top ⟨g, hg⟩)))
      hG'L
  · intro i
    obtain ⟨x₀, hx₀, y₀, hy₀, hx2, hy2, hxy3, c, hc⟩ := h3 i
    have hx₀P : x₀ ∈ Pk i := hLP i (Subgroup.mem_sup_left hx₀)
    have hy₀P : y₀ ∈ Pk i := hLP i (Subgroup.mem_sup_right hy₀)
    obtain ⟨a, haq, haW, ka, hka⟩ := hlift i x₀ ⟨1, by simpa [pow_one, pow_two] using hx2⟩ hx₀P
    obtain ⟨b, hbq, hbW, kb, hkb⟩ := hlift i y₀ ⟨1, by simpa [pow_one, pow_two] using hy2⟩ hy₀P
    have hu : q (a * b) = π' (x₀ * y₀) := by rw [map_mul, haq, hbq, map_mul]
    have hu3 : q (a * b) ^ 3 = 1 := by rw [hu, ← map_pow, hxy3, map_one]
    have hu1 : q (a * b) ≠ 1 := by
      intro h1
      rw [hu] at h1
      have hker : x₀ * y₀ ∈ π'.ker := h1
      exact hc (Subgroup.mem_center_iff.1 (hπ'.ker_central _ hker) c).symm
    have hord : orderOf (q (a * b)) = 3 := orderOf_eq_prime hu3 hu1
    have h3dvd : 3 ∣ orderOf (a * b) := hord ▸ orderOf_map_dvd q (a * b)
    have hmemZ : ∀ z : ↥L, q z = 1 → z ∈ Z := fun z hz => by
      rw [← hqker]; exact hz
    have ha2 : a ^ 2 ∈ Subgroup.center ↥L :=
      hmemZ _ (by rw [map_pow, haq, ← map_pow, pow_two, hx2, map_one])
    have hb2 : b ^ 2 ∈ Subgroup.center ↥L :=
      hmemZ _ (by rw [map_pow, hbq, ← map_pow, pow_two, hy2, map_one])
    have hw3 : (a * b) ^ 3 ∈ Subgroup.center ↥L := hmemZ _ (by rw [map_pow]; exact hu3)
    have hka' : a ^ 2 ^ ka = 1 := hka ▸ pow_orderOf_eq_one a
    have hkb' : b ^ 2 ^ kb = 1 := hkb ▸ pow_orderOf_eq_one b
    obtain ⟨t, ht⟩ := dihedral_three ha2 hb2 hw3 hka' hkb' h3dvd
    refine ⟨(((a * b) ^ 2 ^ t : ↥L) : W), ?_, ?_, ?_⟩
    · have : (((a * b) ^ 2 ^ t : ↥L) : W) = ((a : W) * (b : W)) ^ 2 ^ t := by simp
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mul_mem _ haW hbW) _
    · rw [Subgroup.orderOf_coe]; exact ht
    · rintro ⟨z, hz, hzx⟩
      have hzw : z = (a * b) ^ 2 ^ t := Subtype.ext hzx
      have hzq : q ((a * b) ^ 2 ^ t) = 1 := by
        rw [← hzw]
        exact MonoidHom.mem_ker.1 (by rw [hqker]; exact hz)
      rw [map_pow, ← orderOf_dvd_iff_pow_eq_one, hord] at hzq
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hzq
      omega

  · intro i x hx hxR
    obtain ⟨a, haq, haW, k, hk⟩ := hlift i x hx (hLP i hxR)
    exact ⟨a, haq, haW, k, hk⟩

theorem chevGen_core {L S₀ : Subgroup W} (hL : Open.IsQuasisimple ↥L) (hS : IsSylowTwoOf S₀ L)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M)
    (h3 : ∀ i, HasInvolThree D i) :
    ∃ P : Fin D.rank → Subgroup W, (∀ i, IsMinOverBorel L S₀ (P i)) ∧
      L = ⨆ i, pElementSubgroup 2 (P i) ∧
      ∀ i, ∃ x ∈ pElementSubgroup 2 (P i), orderOf x = 3 ∧
        x ∉ (Subgroup.center ↥L).map L.subtype := by
  obtain ⟨π', -, P, h1, h2, h3', -⟩ := chevGen_data hL hS h h3
  exact ⟨P, h1, h2, h3'⟩

end Main

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
