module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YLemma42T1

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def imgOf (X J : Subgroup G) : Subgroup (X ⧸ CFSG.Assembly.oddCore X) :=
  (J.subgroupOf X).map (QuotientGroup.mk' (CFSG.Assembly.oddCore X))

@[expose] def imgΩ (X : Subgroup G) (ΩX : Set (Subgroup G)) :
    Set (Subgroup (X ⧸ CFSG.Assembly.oddCore X)) :=
  imgOf X '' ΩX

omit [Finite G] in
theorem imgOf_mono {X A B : Subgroup G} (h : A ≤ B) : imgOf X A ≤ imgOf X B :=
  map_mono fun x (hx : x ∈ A.subgroupOf X) => (show (x : G) ∈ B from h hx)

omit [Finite G] in
theorem card_imgOf_dvd {X J : Subgroup G} (hJX : J ≤ X) :
    Nat.card (imgOf X J) ∣ Nat.card J := by
  rw [imgOf, ← card_subgroupOf_of_le hJX]
  exact Subgroup.card_map_dvd (H := J.subgroupOf X)
    (QuotientGroup.mk' (CFSG.Assembly.oddCore X))

theorem card_imgOf_of_isPGroup {X T : Subgroup G} (hT : IsPGroup 2 T) (hTX : T ≤ X) :
    Nat.card (imgOf X T) = Nat.card T := by
  rw [imgOf, card_map_of_injOn _ (mk_injOn hT), card_subgroupOf_of_le hTX]

theorem factorization_card_imgOf {X J : Subgroup G} (hJX : J ≤ X) :
    (Nat.card (imgOf X J)).factorization 2 = (Nat.card J).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  have hT1 := card_imgOf_of_isPGroup hT.isPGroup (hT.le.trans hJX)
  rw [hT.card_eq] at hT1
  have hdvd1 : Nat.card (imgOf X T) ∣ Nat.card (imgOf X J) :=
    card_dvd_of_le (imgOf_mono hT.le)
  have hdvd2 := card_imgOf_dvd (X := X) hJX
  rw [hT1] at hdvd1
  have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have hJb0 : Nat.card (imgOf X J) ≠ 0 := Nat.card_pos.ne'
  apply le_antisymm
  · exact (Nat.factorization_le_iff_dvd hJb0 hJ0).mpr hdvd2 2
  · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hJb0).mp hdvd1

theorem isSylowOf_imgOf {X T J : Subgroup G} (hT : IsSylowOf 2 T J) (hJX : J ≤ X) :
    IsSylowOf 2 (imgOf X T) (imgOf X J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply isSylowOf_of_card (imgOf_mono hT.le)
  rw [card_imgOf_of_isPGroup hT.isPGroup (hT.le.trans hJX), hT.card_eq,
    factorization_card_imgOf hJX]

omit [Finite G] in
theorem map_rightConjugate {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A)
    (g : A) : (AschbacherTightEmbedding.rightConjugate H g).map f =
      AschbacherTightEmbedding.rightConjugate (H.map f) (f g) := by
  ext y
  simp only [mem_map, mem_rightConjugate_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨g * h * g⁻¹, hh, by simp [map_mul, map_inv]⟩
  · rintro ⟨h, hh, hy⟩
    refine ⟨g⁻¹ * h * g, by simpa [mul_assoc] using hh, ?_⟩
    rw [map_mul, map_mul, map_inv, hy]
    group

omit [Finite G] in
theorem imgOf_rightConjugate (X J : Subgroup G) (x : X) :
    imgOf X (AschbacherTightEmbedding.rightConjugate J x) =
      AschbacherTightEmbedding.rightConjugate (imgOf X J)
        (QuotientGroup.mk' (CFSG.Assembly.oddCore X) x) := by
  rw [imgOf, imgOf, rightConjugate_subgroupOf, map_rightConjugate]

omit [Finite G] in
theorem sSup_imgΩ {X : Subgroup G} {ΩX : Set (Subgroup G)} (hgen : sSup ΩX = X) :
    sSup (imgΩ X ΩX) = ⊤ := by
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore X)
  set M := (sSup (imgΩ X ΩX)).comap π
  have hle : ∀ J ∈ ΩX, J ≤ X := fun J hJ => (le_sSup hJ).trans hgen.le
  have hJM : ∀ J ∈ ΩX, J ≤ M.map X.subtype := by
    intro J hJ x hx
    have hxX : x ∈ X := hle J hJ hx
    refine ⟨⟨x, hxX⟩, ?_, rfl⟩
    exact (le_sSup (show imgOf X J ∈ imgΩ X ΩX from Set.mem_image_of_mem _ hJ))
      (Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, hx, rfl⟩)
  have hXM : X ≤ M.map X.subtype := hgen.symm.le.trans (sSup_le hJM)
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨x', hx', hxx'⟩ := hXM x.2
  have : x' = x := Subtype.ext hxx'
  rw [← this]
  exact hx'

omit [Finite G] in
theorem oUpperTwoPrime_imgOf {X J : Subgroup G} (hJX : J ≤ X) (hJ : oUpperTwoPrime J = J) :
    oUpperTwoPrime (imgOf X J) = imgOf X J := by
  apply le_antisymm (oUpperTwoPrime_le _)
  have h1 : J.subgroupOf X = oUpperTwoPrime (J.subgroupOf X) := by
    rw [oUpperTwoPrime_subgroupOf hJX, hJ]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [h1] at hx
  refine closure_induction (p := fun x _ =>
    (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) x ∈ oUpperTwoPrime (imgOf X J))
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨hxJ, k, hxk⟩
    exact subset_closure ⟨Subgroup.mem_map.mpr ⟨x, hxJ, rfl⟩, k, by rw [← map_pow, hxk, map_one]⟩
  · rw [map_one]
    exact one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]
    exact mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact inv_mem ha

theorem nonempty_mulEquiv_imgOf {X T : Subgroup G} (hT : IsPGroup 2 T) (hTX : T ≤ X) :
    Nonempty (T ≃* imgOf X T) := by
  let f : T →* imgOf X T :=
    { toFun := fun t => ⟨QuotientGroup.mk' _ ⟨t, hTX t.2⟩,
        Subgroup.mem_map.mpr ⟨⟨t, hTX t.2⟩, t.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul (QuotientGroup.mk' (CFSG.Assembly.oddCore X))
        (⟨a, hTX a.2⟩ : X) (⟨b, hTX b.2⟩ : X)) }
  refine ⟨MulEquiv.ofBijective f ⟨fun a b hab => ?_, ?_⟩⟩
  · have h1 : (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) ((⟨a, hTX a.2⟩ : X)⁻¹ *
        ⟨b, hTX b.2⟩) = 1 := by
      rw [map_mul, map_inv]
      have := congrArg Subtype.val hab
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk] at this
      rw [this, inv_mul_cancel]
    have h2 := mk_injOn hT _ (show ((⟨a, hTX a.2⟩ : X)⁻¹ * ⟨b, hTX b.2⟩) ∈ T.subgroupOf X from
      mul_mem (inv_mem a.2) b.2) h1
    have h3 := congrArg Subtype.val h2
    simp only [coe_mul, coe_inv, OneMemClass.coe_one] at h3
    exact Subtype.ext (by simpa [inv_mul_eq_one] using h3)
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] in
theorem isDihedralTwoGroup_of_mulEquiv' {A B : Type} [Group A] [Group B] {P : Subgroup A}
    {Q : Subgroup B} (e : P ≃* Q) (h : IsDihedralTwoGroup Q) : IsDihedralTwoGroup P := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  exact ⟨n, hn, ⟨e.trans f⟩⟩

omit [Finite G] in
theorem IsTwoNil.rightConjugate {K R : Subgroup G} (h : IsTwoNil K R) {c : G} (hc : c ∈ K) :
    IsTwoNil K (AschbacherTightEmbedding.rightConjugate R c) := by
  intro k hk
  obtain ⟨o, ho, r, hr, hor⟩ := h (c * k * c⁻¹) (mul_mem (mul_mem hc hk) (inv_mem hc))
  refine ⟨c⁻¹ * o * c, ?_, c⁻¹ * r * c, ?_, ?_⟩
  · have := (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K (inv_mem hc)) o).mp ho
    simpa using this
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hr
  · calc k = c⁻¹ * (c * k * c⁻¹) * c := by group
      _ = c⁻¹ * o * c * (c⁻¹ * r * c) := by rw [hor]; group

theorem exists_sylow_imgOf_le {X J : Subgroup G} (hJX : J ≤ X)
    {P : Subgroup (X ⧸ CFSG.Assembly.oddCore X)} (hP : IsPGroup 2 P) (hPJ : P ≤ imgOf X J) :
    ∃ T : Subgroup G, IsSylowOf 2 T J ∧ P ≤ imgOf X T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_le hP hPJ
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  obtain ⟨k, hk, hkQ⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem
    (isSylowOf_imgOf hT hJX) hQ
  obtain ⟨j, hj, rfl⟩ := hk
  have hjJ : (j : G) ∈ J := hj
  refine ⟨AschbacherTightEmbedding.rightConjugate T (j : G)⁻¹, ?_, ?_⟩
  · have h1 := isSylowOf_rightConjugate hT (j : G)⁻¹
    rwa [(rightConjugate_eq_self_iff J _).mpr (le_normalizer (inv_mem hjJ))] at h1
  · intro x hx
    have h2 := (hkQ x).mp (hPQ hx)
    have h3 : imgOf X (AschbacherTightEmbedding.rightConjugate T ((j⁻¹ : X) : G)) =
        AschbacherTightEmbedding.rightConjugate (imgOf X T)
          (QuotientGroup.mk' (CFSG.Assembly.oddCore X) j⁻¹) := imgOf_rightConjugate X T j⁻¹
    simp only [coe_inv] at h3
    rw [h3, mem_rightConjugate_iff, map_inv, inv_inv]
    exact h2

theorem isSylowOf_oddCore_sup {X : Subgroup G} {P : Subgroup X} (hP : IsPGroup 2 P) :
    IsSylowOf 2 P (CFSG.Assembly.oddCore X ⊔ P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨le_sup_right, hP, fun hdvd => ?_⟩
  rw [relIndex_sup_eq_relIndex_of_normal] at hdvd
  have h1 : P.relIndex (CFSG.Assembly.oddCore X) ∣ Nat.card (CFSG.Assembly.oddCore X) :=
    Subgroup.index_dvd_card _
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.Asc76.L26.odd_card_oddCore X))
    (even_iff_two_dvd.mpr (hdvd.trans h1))

omit [Finite G] in
theorem comap_eq_oddCore_sup {X : Subgroup G} {P : Subgroup (X ⧸ CFSG.Assembly.oddCore X)}
    {Q : Subgroup X} (hQ : Q.map (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) = P) :
    P.comap (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) = CFSG.Assembly.oddCore X ⊔ Q := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap, ← hQ] at hx
    obtain ⟨q, hq, hqx⟩ := hx
    have h1 : q⁻¹ * x ∈ CFSG.Assembly.oddCore X := QuotientGroup.eq.mp hqx
    have h2 : x * q⁻¹ ∈ CFSG.Assembly.oddCore X := by
      have := (inferInstance : (CFSG.Assembly.oddCore X).Normal).conj_mem _ h1 q
      simpa [mul_assoc] using this
    have : x = (x * q⁻¹) * q := by group
    rw [this]
    exact mul_mem (mem_sup_left h2) (mem_sup_right hq)
  · refine sup_le (fun o ho => ?_) (fun q hq => ?_)
    · rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff o).mpr ho]
      exact one_mem _
    · rw [mem_comap, ← hQ]
      exact mem_map_of_mem _ hq

omit [Finite G] in
theorem map_comap_inf_subgroupOf {X T : Subgroup G} {P : Subgroup (X ⧸ CFSG.Assembly.oddCore X)}
    (hPT : P ≤ imgOf X T) :
    (P.comap (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) ⊓ T.subgroupOf X).map
      (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) = P := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_inf.mp hx).1
  · intro p hp
    obtain ⟨t, ht, rfl⟩ := hPT hp
    exact ⟨t, mem_inf.mpr ⟨hp, ht⟩, rfl⟩

theorem odd_card_inf_imgOf (hΩ : Assumption41 Ω) {X J L : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω)
    (hJX : J ≤ X) (hLX : L ≤ X) (hne : imgOf X J ≠ imgOf X L) :
    Odd (Nat.card (imgOf X J ⊓ imgOf X L : Subgroup (X ⧸ CFSG.Assembly.oddCore X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Assembly.oddCore X
  set π := QuotientGroup.mk' O
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (imgOf X J ⊓ imgOf X L)
  obtain ⟨T₁, hT₁, hPT₁⟩ := exists_sylow_imgOf_le hJX hP.isPGroup (hP.le.trans inf_le_left)
  obtain ⟨T₂, hT₂, hPT₂⟩ := exists_sylow_imgOf_le hLX hP.isPGroup (hP.le.trans inf_le_right)
  set P₁ := P.comap π ⊓ T₁.subgroupOf X
  set P₂ := P.comap π ⊓ T₂.subgroupOf X
  have hP₁ : P₁.map π = P := map_comap_inf_subgroupOf hPT₁
  have hP₂ : P₂.map π = P := map_comap_inf_subgroupOf hPT₂
  have hP₁2 : IsPGroup 2 P₁ := (hT₁.isPGroup.comap_subtype (K := X)).to_le inf_le_right
  have hP₂2 : IsPGroup 2 P₂ := (hT₂.isPGroup.comap_subtype (K := X)).to_le inf_le_right
  have hsup : O ⊔ P₁ = O ⊔ P₂ := by
    rw [← comap_eq_oddCore_sup hP₁, ← comap_eq_oddCore_sup hP₂]
  have hS₁ : IsSylowOf 2 P₁ (O ⊔ P₂) := hsup ▸ isSylowOf_oddCore_sup hP₁2
  obtain ⟨c, hc, hcP⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem
    (isSylowOf_oddCore_sup hP₂2) hS₁
  have hc' : c ∈ ((O ⊔ P₂ : Subgroup X) : Set X) := hc
  rw [normal_mul] at hc'
  obtain ⟨o, ho, p, hp, rfl⟩ := hc'
  have hP₁L : ∀ x ∈ P₁, ((x : G) ∈ J ∧ (x : G) ∈
      AschbacherTightEmbedding.rightConjugate L ((o : X) : G)⁻¹) := by
    intro x hx
    refine ⟨hT₁.le (mem_inf.mp hx).2, ?_⟩
    have h1 := (hcP x).mp hx
    have h2 : (p : X) * ((o * p)⁻¹ * x * (o * p)) * p⁻¹ ∈ T₂.subgroupOf X :=
      mul_mem (mul_mem (mem_inf.mp hp).2 (mem_inf.mp h1).2) (inv_mem (mem_inf.mp hp).2)
    have h3 : (p : X) * ((o * p)⁻¹ * x * (o * p)) * p⁻¹ = o⁻¹ * x * o := by group
    rw [h3] at h2
    rw [mem_rightConjugate_iff, inv_inv]
    have := hT₂.le (show (((o⁻¹ * x * o : X)) : G) ∈ T₂ from h2)
    simpa using this
  have hJL : J ≠ AschbacherTightEmbedding.rightConjugate L ((o : X) : G)⁻¹ := by
    intro h
    apply hne
    rw [h]
    have h1 := imgOf_rightConjugate X L o⁻¹
    simp only [coe_inv] at h1
    rw [h1, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (o⁻¹ : X)).mpr (inv_mem ho),
      rightConjugate_one]
  have hbot : P₁.map X.subtype = ⊥ := by
    have h1 := Assumption41.inf_eq_bot hΩ hJ (hΩ.conj_mem L hL _) hJL
      (hP₁2.map X.subtype) (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := hx
        exact (hP₁L y hy).1) (Q := P₁.map X.subtype) (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := hx
        exact (hP₁L y hy).2)
    rwa [inf_idem] at h1
  have hP₁bot : P₁ = ⊥ := (map_eq_bot_iff_of_injective _ X.subtype_injective).mp hbot
  have hPbot : P = ⊥ := by rw [← hP₁, hP₁bot, Subgroup.map_bot]
  have h1 := hP.card_eq
  rw [hPbot, card_bot] at h1
  have h2 : (Nat.card (imgOf X J ⊓ imgOf X L :
      Subgroup (X ⧸ CFSG.Assembly.oddCore X))).factorization 2 = 0 := by
    have := (Nat.pow_eq_one.mp h1.symm)
    omega
  rw [Nat.factorization_eq_zero_iff] at h2
  rcases h2 with h2 | h2 | h2
  · exact absurd Nat.prime_two h2
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  · exact absurd h2 Nat.card_pos.ne'

theorem dihedral_imgOf (hΩ : Assumption41 Ω) {X J : Subgroup G} (hJ : J ∈ Ω) (hJX : J ≤ X)
    {R : Subgroup (X ⧸ CFSG.Assembly.oddCore X)} (hR : IsSylowOf 2 R (imgOf X J)) :
    IsDihedralTwoGroup R ∧ ¬ IsMulCommutative R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  obtain ⟨e₁⟩ := IsSylowOf.nonempty_mulEquiv hR (isSylowOf_imgOf hT hJX)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_imgOf hT.isPGroup (hT.le.trans hJX)
  have e := e₁.trans e₂.symm
  obtain ⟨hd, hc⟩ := hΩ.dihedral J hJ T hT
  exact ⟨isDihedralTwoGroup_of_mulEquiv' e hd, fun h => hc (isMulCommutative_of_mulEquiv e.symm)⟩

theorem imgOf_oddCoreIn_le {X J : Subgroup G} (hJX : J ≤ X) :
    imgOf X (oddCoreIn J) ≤ oddCoreIn (imgOf X J) := by
  apply le_oddCoreIn_of_le_normalizer (imgOf_mono (oddCoreIn_le J))
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x * w * x⁻¹, ?_, by simp [MulAut.conj_apply]⟩
    have := (mem_normalizer_iff.mp (le_normalizer_oddCoreIn J (show (x : G) ∈ J from hx)) w).mp hw
    show x * w * x⁻¹ ∈ (oddCoreIn J).subgroupOf X
    rw [mem_subgroupOf]
    simpa using this
  · exact (odd_card_oddCoreIn J).of_dvd_nat
      (card_imgOf_dvd ((oddCoreIn_le J).trans hJX))

theorem isTwoNil_imgOf {X J : Subgroup G} (hJX : J ≤ X)
    (hnil : ∀ T, IsSylowOf 2 T J → IsTwoNil J T) {R : Subgroup (X ⧸ CFSG.Assembly.oddCore X)}
    (hR : IsSylowOf 2 R (imgOf X J)) : IsTwoNil (imgOf X J) R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  have h1 : IsTwoNil (imgOf X J) (imgOf X T) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := hk
    obtain ⟨o, ho, r, hr, hor⟩ := hnil T hT x hx
    have hoX : o ∈ X := ((oddCoreIn_le J).trans hJX) ho
    have hrX : r ∈ X := hJX (hT.le hr)
    refine ⟨QuotientGroup.mk' _ ⟨o, hoX⟩, imgOf_oddCoreIn_le hJX
      (Subgroup.mem_map.mpr ⟨⟨o, hoX⟩, ho, rfl⟩), QuotientGroup.mk' _ ⟨r, hrX⟩,
      Subgroup.mem_map.mpr ⟨⟨r, hrX⟩, hr, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hor
  obtain ⟨k, hk, hkR⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem
    (isSylowOf_imgOf hT hJX) hR
  have hReq : R = AschbacherTightEmbedding.rightConjugate (imgOf X T) k⁻¹ := by
    ext x
    rw [hkR, mem_rightConjugate_iff, inv_inv]
  rw [hReq]
  exact h1.rightConjugate (inv_mem hk)

theorem assumption41_imgΩ (hΩ : Assumption41 Ω) {X : Subgroup G} {ΩX : Set (Subgroup G)}
    (hsub : ΩX ⊆ Ω) (hinv : ∀ J ∈ ΩX, ∀ x ∈ X, AschbacherTightEmbedding.rightConjugate J x ∈ ΩX)
    (hgen : sSup ΩX = X) : Assumption41 (imgΩ X ΩX) := by
  have hle : ∀ J ∈ ΩX, J ≤ X := fun J hJ => (le_sSup hJ).trans hgen.le
  refine ⟨CFSG.ComponentClassification.Asc76.L26.oddCore_quotient_oddCore_eq_bot (G := X),
    ?_, sSup_imgΩ hgen, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨J, hJ, rfl⟩ y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨_, hinv J hJ x x.2, imgOf_rightConjugate X J x⟩
  · rintro _ ⟨J, hJ, rfl⟩ _ ⟨L, hL, rfl⟩ hne
    rw [factorization_card_imgOf (hle J hJ), factorization_card_imgOf (hle L hL)]
    by_cases h : J = L
    · rw [h]
    exact hΩ.twoPart J (hsub hJ) L (hsub hL) h
  · rintro _ ⟨J, hJ, rfl⟩ _ ⟨L, hL, rfl⟩ hne
    exact odd_card_inf_imgOf hΩ (hsub hJ) (hsub hL) (hle J hJ) (hle L hL) hne
  · rintro _ ⟨J, hJ, rfl⟩
    exact oUpperTwoPrime_imgOf (hle J hJ) (hΩ.perfect J (hsub hJ))
  · rintro _ ⟨J, hJ, rfl⟩ R hR
    exact dihedral_imgOf hΩ (hsub hJ) (hle J hJ) hR

end CFSG.ComponentClassification.Asc76.Sec4
