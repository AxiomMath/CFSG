module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

namespace Good

private theorem inj_of_odd_ker {A B : Type*} [Group A] [Group B] {f : A →* B} {U : Subgroup A}
    (hU : IsPGroup 2 U) (hker : Odd (Nat.card f.ker)) {a b : A} (ha : a ∈ U) (hb : b ∈ U)
    (hab : f a = f b) : a = b := by
  have hc : a⁻¹ * b ∈ U := U.mul_mem (U.inv_mem ha) hb
  have hk : a⁻¹ * b ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  obtain ⟨k, hk2⟩ := IsPGroup.iff_orderOf.mp hU ⟨a⁻¹ * b, hc⟩
  rw [Subgroup.orderOf_mk] at hk2
  have hdvd : orderOf (a⁻¹ * b) ∣ Nat.card f.ker := by
    rw [← Subgroup.orderOf_mk (a⁻¹ * b) hk]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card f.ker) :=
    (Nat.coprime_two_left.mpr hker).pow_left k
  rw [hk2] at hdvd
  have h1 : orderOf (a⁻¹ * b) = 1 := by rw [hk2]; exact hcop.eq_one_of_dvd hdvd
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h1)

private theorem orderOf_map_eq {A B : Type*} [Group A] [Group B] {f : A →* B} {U : Subgroup A}
    (hinj : ∀ a b : A, a ∈ U → b ∈ U → f a = f b → a = b) {a : A} (ha : a ∈ U) :
    orderOf (f a) = orderOf a := by
  refine Nat.dvd_antisymm (orderOf_map_dvd f a) (orderOf_dvd_of_pow_eq_one ?_)
  have h1 : f (a ^ orderOf (f a)) = f 1 := by
    rw [map_pow, pow_orderOf_eq_one, map_one]
  exact hinj _ _ (U.pow_mem ha _) U.one_mem h1

private theorem card_map_of_inj {A B : Type*} [Group A] [Group B] {f : A →* B} {U : Subgroup A}
    (hinj : ∀ a b : A, a ∈ U → b ∈ U → f a = f b → a = b) :
    Nat.card (U.map f) = Nat.card U := by
  refine (Nat.card_eq_of_bijective (f.subgroupMap U) ⟨fun a b hab => ?_,
    f.subgroupMap_surjective U⟩).symm
  exact Subtype.ext (hinj a b a.2 b.2 (congrArg Subtype.val hab))

private theorem exists_sylow_subgroupOf {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N : Subgroup H) [N.Normal] (P : Sylow p H) :
    ∃ Q : Sylow p N, (Q : Subgroup N) = (P : Subgroup H).subgroupOf N := by
  let intersection := (P : Subgroup H).subgroupOf N
  have hintersectionP : IsPGroup p intersection := P.isPGroup'.comap_subtype
  obtain ⟨relative, hrelative⟩ := hintersectionP.exists_le_sylow
  let mapped := (relative : Subgroup N).map N.subtype
  have hmappedP : IsPGroup p mapped := relative.isPGroup'.map N.subtype
  obtain ⟨overgroup, hovergroup⟩ := hmappedP.exists_le_sylow
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq H overgroup P
  have hconjugateSylow : (overgroup : Subgroup H).map (MulAut.conj actor).toMonoidHom =
      (P : Subgroup H) := by
    rw [← hactor, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  let conjugated := mapped.map (MulAut.conj actor).toMonoidHom
  have hconjugatedSylow : conjugated ≤ (P : Subgroup H) := by
    rw [← hconjugateSylow]
    exact Subgroup.map_mono hovergroup
  have hconjugatedNormal : conjugated ≤ N := by
    intro element hmem
    obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨relativeElement, _, rfl⟩ := Subgroup.mem_map.mp horiginal
    exact (inferInstance : N.Normal).conj_mem relativeElement relativeElement.property actor
  have hle : conjugated ≤ (P : Subgroup H) ⊓ N := le_inf hconjugatedSylow hconjugatedNormal
  have hcardConjugated : Nat.card conjugated = Nat.card (relative : Subgroup N) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective,
      Subgroup.card_map_of_injective N.subtype_injective]
  have hcardIntersection : Nat.card ↥((P : Subgroup H) ⊓ N) = Nat.card intersection := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective N.subtype_injective]
  have hcardGe : Nat.card (relative : Subgroup N) ≤ Nat.card intersection := by
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardConjugated, hcardIntersection] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  exact ⟨relative, (Subgroup.eq_of_le_of_card_ge hrelative hcardGe).symm⟩

private theorem mul_e (x y : WrE) : (x * y).e = xor x.e y.e := by
  rw [WrE.mul_def]; split <;> rfl

private theorem mem_wrR_iff {x : WrE} : x ∈ wrR ↔ x.a ∈ R ∧ x.b ∈ R := Iff.rfl

private theorem mem_ssS_iff {x : WrE} : x ∈ ssS ↔ x.e = false ∧ x.a ∈ S ∧ x.b ∈ S := Iff.rfl

private theorem conj_mem_ssS {c x : WrE} (hc : c ∈ wrR)
    (hx : x ∈ ssS) : c * x * c⁻¹ ∈ ssS := by
  rcases c with ⟨ca, cb, ce⟩
  rcases x with ⟨xa, xb, xe⟩
  obtain ⟨hxe, hxa, hxb⟩ := mem_ssS_iff.mp hx
  obtain ⟨hca, hcb⟩ := mem_wrR_iff.mp hc
  simp only at hxe hxa hxb hca hcb
  subst hxe
  cases ce
  · show (⟨ca * xa * ca⁻¹, cb * xb * cb⁻¹, false⟩ : WrE) ∈ ssS
    exact mem_ssS_iff.mpr ⟨rfl, conj_mem_S hca hxa, conj_mem_S hcb hxb⟩
  · show (⟨cb * xb * cb⁻¹, ca * xa * ca⁻¹, false⟩ : WrE) ∈ ssS
    exact mem_ssS_iff.mpr ⟨rfl, conj_mem_S hcb hxb, conj_mem_S hca hxa⟩

private theorem card_ssS_eq_sq : Nat.card ssS = Nat.card S ^ 2 := by
  let e : ssS ≃ S × S :=
    { toFun := fun x => (⟨x.1.a, (mem_ssS_iff.mp x.2).2.1⟩, ⟨x.1.b, (mem_ssS_iff.mp x.2).2.2⟩)
      invFun := fun p => ⟨⟨p.1.1, p.2.1, false⟩, mem_ssS_iff.mpr ⟨rfl, p.1.2, p.2.2⟩⟩
      left_inv := by
        rintro ⟨⟨xa, xb, xe⟩, hx⟩
        have hxe : xe = false := (mem_ssS_iff.mp hx).1
        subst hxe
        rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, sq]

section Model

variable {G : Type} [Group G] [Finite G] {M K T : Subgroup G} {t : G} {ρ : ↥M →* WrE}

private theorem ker_eq (hρ : TwModel M K t ρ) : ρ.ker = pPrimeCore 2 ↥M := by
  ext m
  rw [MonoidHom.mem_ker, hρ.ker_iff m]
  exact Subgroup.mem_map_iff_mem M.subtype_injective

private theorem odd_card_ker (hρ : TwModel M K t ρ) : Odd (Nat.card ρ.ker) := by
  rw [ker_eq hρ]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem normal_comap_ssS (hρ : TwModel M K t ρ) :
    (ssS.comap ρ).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_ssS (hρ.mem_wrR g) hn⟩

private theorem ssS_le_range (hρ : TwModel M K t ρ) : ssS ≤ ρ.range := by
  rintro ⟨xa, xb, xe⟩ hx
  obtain ⟨hxe, hxa, hxb⟩ := mem_ssS_iff.mp hx
  simp only at hxe hxa hxb
  subst hxe
  obtain ⟨m, -, hm⟩ := hρ.K_surj xa hxa
  obtain ⟨m', -, hm'⟩ := hρ.Kt_surj xb hxb
  refine MonoidHom.mem_range.mpr ⟨m * m', ?_⟩
  rw [map_mul, hm, hm']
  simp [WrE.mul_def]

private theorem card_ss_eq (hρ : TwModel M K t ρ)
    (hsyl : ∃ P : Sylow 2 ↥M, (P : Subgroup ↥M) = T.subgroupOf M)
    (hinj : ∀ a b : ↥M, a ∈ T.subgroupOf M → b ∈ T.subgroupOf M → ρ a = ρ b → a = b) :
    Nat.card ↥(imgT T M ρ ⊓ ssS) = 2 ^ 12 := by
  obtain ⟨P, hP⟩ := hsyl
  haveI : (ssS.comap ρ).Normal := normal_comap_ssS hρ
  obtain ⟨Q, hQ⟩ := exists_sylow_subgroupOf (ssS.comap ρ) P
  have hrange : (ρ.comp (ssS.comap ρ).subtype).range = ssS := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr (ssS_le_range hρ)
  have hLt : Nat.card (ρ.comp (ssS.comap ρ).subtype).ker * Nat.card ssS =
      Nat.card (ssS.comap ρ) := by
    have := Subgroup.card_ker_mul_card_range (ρ.comp (ssS.comap ρ).subtype)
    rwa [hrange] at this
  have hkerodd : Odd (Nat.card (ρ.comp (ssS.comap ρ).subtype).ker) := by
    have hle : (ρ.comp (ssS.comap ρ).subtype).ker.map (ssS.comap ρ).subtype ≤ ρ.ker := by
      rintro _ ⟨l, hl, rfl⟩
      exact hl
    refine (odd_card_ker hρ).of_dvd_nat ?_
    rw [← Subgroup.card_map_of_injective (ssS.comap ρ).subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have h2 : (Nat.card (ssS.comap ρ)).factorization 2 = 12 := by
    rw [← hLt, card_ssS_eq_sq, card_S]
    have hn : Nat.card (ρ.comp (ssS.comap ρ).subtype).ker ≠ 0 := hkerodd.pos.ne'
    have h : Nat.card (ρ.comp (ssS.comap ρ).subtype).ker * 20160 ^ 2 =
        2 ^ 12 * (Nat.card (ρ.comp (ssS.comap ρ).subtype).ker * 315 ^ 2) := by ring
    have hodd : Odd (Nat.card (ρ.comp (ssS.comap ρ).subtype).ker * 315 ^ 2) :=
      hkerodd.mul (⟨49612, by norm_num⟩ : Odd (315 ^ 2))
    rw [h, Nat.factorization_def _ Nat.prime_two,
      padicValNat.mul (by positivity) (mul_ne_zero hn (by norm_num)), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]
  have hX : imgT T M ρ ⊓ ssS = ((T.subgroupOf M) ⊓ ssS.comap ρ).map ρ := by
    ext x
    constructor
    · rintro ⟨⟨m, hm, rfl⟩, hx⟩
      exact ⟨m, ⟨hm, hx⟩, rfl⟩
    · rintro ⟨m, ⟨hm, hl⟩, rfl⟩
      exact ⟨⟨m, hm, rfl⟩, hl⟩
  have hcard : Nat.card (((T.subgroupOf M) ⊓ ssS.comap ρ).map ρ) =
      Nat.card ↥((T.subgroupOf M) ⊓ ssS.comap ρ) :=
    card_map_of_inj (fun a b ha hb hab => hinj a b ha.1 hb.1 hab)
  rw [hX, hcard]
  have hQc : Nat.card ↥((T.subgroupOf M) ⊓ ssS.comap ρ) =
      Nat.card (Q : Subgroup (ssS.comap ρ)) := by
    rw [hQ, hP, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective (ssS.comap ρ).subtype_injective]
  rw [hQc, Q.card_eq_multiplicity, h2]

private theorem exists_lift_swap (hρ : TwModel M K t ρ) {g : WrE} (hg : g ∈ imgT T M ρ)
    (he : g.e = true) :
    ∃ y : ↥M, y ∈ T.subgroupOf M ∧ (y : G) ∉ normalizer (K : Set G) ∧ ρ y = g := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨y, hy, (hρ.swap_iff y).mp he, rfl⟩

private theorem field_h13 (hρ : TwModel M K t ρ)
    (hinj : ∀ a b : ↥M, a ∈ T.subgroupOf M → b ∈ T.subgroupOf M → ρ a = ρ b → a = b)
    (hinv : ∀ y ∈ M, orderOf y = 2 → y ∈ normalizer (K : Set G)) :
    ∀ g ∈ imgT T M ρ, g.e = true → g * g ≠ 1 := by
  intro g hg he hgg
  obtain ⟨y, hy, hyK, rfl⟩ := exists_lift_swap hρ hg he
  have hyy : y * y = 1 := by
    refine hinj (y * y) 1 ((T.subgroupOf M).mul_mem hy hy) (T.subgroupOf M).one_mem ?_
    rw [map_mul, hgg, map_one]
  have hord : orderOf (y : G) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      exact congrArg Subtype.val hyy
    · intro h1
      exact hyK (h1 ▸ (normalizer (K : Set G)).one_mem)
  exact hyK (hinv (y : G) y.2 hord)

private theorem field_h14 (hρ : TwModel M K t ρ) (hTM : T ≤ M)
    (hu : ∃ u ∈ T, u ∉ normalizer (K : Set G) ∧ u ^ 4 = 1) :
    ∃ g ∈ imgT T M ρ, g.e = true ∧ g ^ 4 = 1 := by
  obtain ⟨u, huT, huK, hu4⟩ := hu
  have hu' : (⟨u, hTM huT⟩ : ↥M) ∈ T.subgroupOf M := huT
  refine ⟨ρ ⟨u, hTM huT⟩, Subgroup.mem_map_of_mem ρ hu', (hρ.swap_iff _).mpr huK, ?_⟩
  rw [← map_pow]
  have h4 : (⟨u, hTM huT⟩ : ↥M) ^ 4 = 1 := Subtype.ext hu4
  rw [h4, map_one]

private theorem field_h20 (hρ : TwModel M K t ρ)
    (hE5 : ∀ v ∈ T, v ∉ normalizer (K : Set G) → v * v ∉ withKernel K) :
    ∀ g ∈ imgT T M ρ, g.e = true → (g * g).a ∉ S := by
  intro g hg he hS
  obtain ⟨y, hy, hyK, rfl⟩ := exists_lift_swap hρ hg he
  have hyyK : ((y * y : ↥M) : G) ∈ normalizer (K : Set G) := by
    by_contra hn
    have h1 := (hρ.swap_iff (y * y)).mpr hn
    rw [map_mul, mul_e, he] at h1
    exact absurd h1 (by decide)
  have hwk : ((y * y : ↥M) : G) ∈ withKernel K :=
    (hρ.withKernel_iff (y * y) hyyK).mpr (by rwa [map_mul])
  exact hE5 (y : G) hy hyK hwk

private theorem field_h22 (hρ : TwModel M K t ρ) (hTM : T ≤ M)
    (hinj : ∀ a b : ↥M, a ∈ T.subgroupOf M → b ∈ T.subgroupOf M → ρ a = ρ b → a = b)
    (hE7 : ∀ v ∈ T, v ∉ normalizer (K : Set G) →
      (∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf v ≤ orderOf y) →
      ¬ ∃ F ≤ T ⊓ centralizer ({v * v} : Set G), IsEightGroup F ∧
        ∃ w ∈ T ⊓ centralizer ({v * v} : Set G), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧
          w ∉ F) :
    ∀ g ∈ imgT T M ρ, g.e = true → (∀ h ∈ imgT T M ρ, h.e = true → orderOf g ≤ orderOf h) →
      ¬ ∃ F ≤ imgT T M ρ ⊓ centralizer ({g * g} : Set WrE), IsEightGroup F ∧
        ∃ w ∈ imgT T M ρ ⊓ centralizer ({g * g} : Set WrE), w * w = 1 ∧
          (∀ e ∈ F, w * e = e * w) ∧ w ∉ F := by
  intro g hg he hmin
  obtain ⟨v, hv, hvK, rfl⟩ := exists_lift_swap hρ hg he
  rintro ⟨F', hF', ⟨⟨hFcomm, hFsq⟩, hF8⟩, w', hw', hw'2, hw'F, hw'nF⟩
  have hvmin : ∀ y ∈ T, y ∉ normalizer (K : Set G) → orderOf (v : G) ≤ orderOf y := by
    intro y hy hyK
    have hy' : (⟨y, hTM hy⟩ : ↥M) ∈ T.subgroupOf M := hy
    have h1 := hmin (ρ ⟨y, hTM hy⟩) (Subgroup.mem_map_of_mem ρ hy') ((hρ.swap_iff _).mpr hyK)
    rw [orderOf_map_eq hinj hv, orderOf_map_eq hinj hy'] at h1
    calc orderOf (v : G) = orderOf v := Subgroup.orderOf_coe v
      _ ≤ orderOf (⟨y, hTM hy⟩ : ↥M) := h1
      _ = orderOf y := Subgroup.orderOf_mk y (hTM hy)
  refine hE7 (v : G) hv hvK hvmin ?_
  have hcomm : ∀ {m c : ↥M}, m ∈ T.subgroupOf M → c ∈ T.subgroupOf M →
      ρ m * ρ c = ρ c * ρ m → m * c = c * m := fun hm hc h =>
    hinj _ _ ((T.subgroupOf M).mul_mem hm hc) ((T.subgroupOf M).mul_mem hc hm)
      (by rw [map_mul, map_mul, h])
  have hvv : v * v ∈ T.subgroupOf M := (T.subgroupOf M).mul_mem hv hv
  let F₀ : Subgroup ↥M := F'.comap ρ ⊓ T.subgroupOf M
  have hF₀c : ∀ m ∈ F₀, (m : G) ∈ centralizer ({(v : G) * v} : Set G) := by
    intro m hm
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hF' hm.1).2
    have h2 : m * (v * v) = (v * v) * m := hcomm hm.2 hvv (by rw [map_mul]; exact h1)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h2)
  have hF₀map : F₀.map ρ = F' := by
    ext f
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm.1
    · intro hf
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (hF' hf).1
      exact ⟨m, ⟨hf, hm⟩, rfl⟩
  have hF₀card : Nat.card (F₀.map M.subtype) = 8 := by
    have h1 : Nat.card (F₀.map ρ) = Nat.card F₀ :=
      card_map_of_inj (U := F₀) (fun a b ha hb hab => hinj a b ha.2 hb.2 hab)
    rw [Subgroup.card_map_of_injective M.subtype_injective, ← h1, hF₀map, hF8]
  obtain ⟨⟨w₀, hw₀, rfl⟩, hw'c⟩ := hw'
  refine ⟨F₀.map M.subtype, ?_, ⟨⟨?_, ?_⟩, hF₀card⟩, (w₀ : G), ⟨hw₀, ?_⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨hm.2, hF₀c m hm⟩
  · rintro _ ⟨m₁, hm₁, rfl⟩ _ ⟨m₂, hm₂, rfl⟩
    exact congrArg Subtype.val (hcomm hm₁.2 hm₂.2 (hFcomm _ hm₁.1 _ hm₂.1))
  · rintro _ ⟨m, hm, rfl⟩
    have h1 : m * m = 1 := hinj _ _ ((T.subgroupOf M).mul_mem hm.2 hm.2)
      (T.subgroupOf M).one_mem (by rw [map_mul, hFsq _ hm.1, map_one])
    exact congrArg Subtype.val h1
  · have h1 := Subgroup.mem_centralizer_singleton_iff.mp hw'c
    have h2 : w₀ * (v * v) = (v * v) * w₀ := hcomm hw₀ hvv (by rw [map_mul]; exact h1)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h2)
  · have h1 : w₀ * w₀ = 1 := hinj _ _ ((T.subgroupOf M).mul_mem hw₀ hw₀)
      (T.subgroupOf M).one_mem (by rw [map_mul, hw'2, map_one])
    exact congrArg Subtype.val h1
  · rintro _ ⟨m, hm, rfl⟩
    exact congrArg Subtype.val (hcomm hw₀ hm.2 (hw'F _ hm.1))
  · intro hmem
    obtain ⟨m, hm, hmw⟩ := Subgroup.mem_map.mp hmem
    have h1 : m = w₀ := Subtype.ext hmw
    subst h1
    exact hw'nF hm.1

end Model

end Good

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}

theorem goodX_of_twModel (h : TwHyp G a x J S' W K T t)
    {ρ : ↥(normalizer (W : Set G)) →* WrE} (hρ : TwModel (normalizer (W : Set G)) K t ρ) :
    GoodX ((T.subgroupOf (normalizer (W : Set G))).map ρ) := by
  obtain ⟨hTM, P, hP⟩ := h.hTsyl
  have hT2 : IsPGroup 2 ↥(T.subgroupOf (normalizer (W : Set G))) := by
    rw [← hP]; exact P.isPGroup'
  have hinj : ∀ a b : ↥(normalizer (W : Set G)), a ∈ T.subgroupOf (normalizer (W : Set G)) →
      b ∈ T.subgroupOf (normalizer (W : Set G)) → ρ a = ρ b → a = b :=
    fun a b ha hb hab => Good.inj_of_odd_ker hT2 (Good.odd_card_ker hρ) ha hb hab
  have htT' : (⟨t, hTM h.htT⟩ : ↥(normalizer (W : Set G))) ∈
      T.subgroupOf (normalizer (W : Set G)) := h.htT
  exact
    { le_wrR := fun y hy => by
        obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.mp hy
        exact hρ.mem_wrR m
      two := hT2.map ρ
      card_ss := Good.card_ss_eq hρ ⟨P, hP⟩ hinj
      swap := ⟨ρ ⟨t, hTM h.htT⟩, Subgroup.mem_map_of_mem ρ htT', (hρ.swap_iff _).mpr h.htK⟩
      h13 := Good.field_h13 hρ hinj h.hinv
      h14 := Good.field_h14 hρ hTM h.hu
      h20 := Good.field_h20 hρ h.hE5
      h22 := Good.field_h22 hρ hTM hinj h.hE7 }

end CFSG.ComponentClassification.GrSLit.L34Tw
