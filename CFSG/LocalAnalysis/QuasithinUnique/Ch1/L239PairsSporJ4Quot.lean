
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4QuotBase

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTOutNorm

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.Mathieu

theorem starOK_gen
    {k : ℕ} (hk : k < 3) {i : ℕ} (hi : i < 24) :
    StarOK (xJ k) i ((starPermOf k).getD i 0) := by
  intro c hc
  obtain ⟨-, -, hact⟩ := star_perm_facts k hk
  have hℓ : ((k : ℤ) + 1) ∈ letters := by interval_cases k <;> simp [letters]
  have hx : XJ ((k : ℤ) + 1) = xJ k := by
    interval_cases k
    · simpa using XJ_one
    · simpa using XJ_two
    · simpa using XJ_three
  refine ⟨act ((k : ℤ) + 1) c, hact i hi c hc, ?_⟩
  rw [← hx]
  exact hX_all j4Facts.mat hℓ c

theorem starOK_closure
    : ∀ g ∈ Hj, ∀ i < 24, ∃ i' < 24, StarOK g i i' := by
  intro g hg
  have hg' : g ∈ Submonoid.closure ({xJ 0, xJ 1, xJ 2} : Set J) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact fun i hi => ⟨_, (star_perm_facts 0 (by norm_num)).2.1 i hi, starOK_gen (by norm_num) hi⟩
    · exact fun i hi => ⟨_, (star_perm_facts 1 (by norm_num)).2.1 i hi, starOK_gen (by norm_num) hi⟩
    · exact fun i hi => ⟨_, (star_perm_facts 2 (by norm_num)).2.1 i hi, starOK_gen (by norm_num) hi⟩
  | one => exact fun i hi => ⟨i, hi, starOK_one i⟩
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨i', hi', h1⟩ := hy i hi
    obtain ⟨i'', hi'', h2⟩ := hx i' hi'
    exact ⟨i'', hi'', starOK_mul h1 h2⟩

theorem starOK_unique
    {g : J} {i i' i'' : ℕ} (hi : i < 24) (hi' : i' < 24) (hi'' : i'' < 24)
    (h1 : StarOK g i i') (h2 : StarOK g i i'') : i' = i'' := by
  by_contra hne
  obtain ⟨-, -, -, hdis, hint, -⟩ := star_facts
  obtain ⟨c₁, hc₁, c₂, hc₂, hc12⟩ := hdis i hi
  obtain ⟨d₁, hd₁, e₁⟩ := h1 c₁ hc₁
  obtain ⟨d₁', hd₁', e₁'⟩ := h2 c₁ hc₁
  obtain ⟨d₂, hd₂, e₂⟩ := h1 c₂ hc₂
  obtain ⟨d₂', hd₂', e₂'⟩ := h2 c₂ hc₂
  have hM := j4Facts.mat
  have hd1 : d₁ = d₁' :=
    eta_inj hM d₁ (mem_star_lt hi' hd₁) d₁' (mem_star_lt hi'' hd₁') (e₁.symm.trans e₁')
  have hd2 : d₂ = d₂' :=
    eta_inj hM d₂ (mem_star_lt hi' hd₂) d₂' (mem_star_lt hi'' hd₂') (e₂.symm.trans e₂')
  have hd12 : d₁ ≠ d₂ := by
    intro h
    apply hc12
    have : eta uJ 11 c₁ = eta uJ 11 c₂ := by
      have h3 : g * eta uJ 11 c₁ * g⁻¹ = g * eta uJ 11 c₂ * g⁻¹ := by rw [e₁, e₂, h]
      simpa using h3
    exact eta_inj hM c₁ (mem_star_lt hi hc₁) c₂ (mem_star_lt hi hc₂) this
  exact hd12 (hint i' hi' i'' hi'' hne d₁ hd₁ (hd1 ▸ hd₁') d₂ hd₂ (hd2 ▸ hd₂'))

noncomputable def starMap
    (g : Hj) (i : Fin 24) : Fin 24 :=
  ⟨(starOK_closure g.1 g.2 i i.2).choose, (starOK_closure g.1 g.2 i i.2).choose_spec.1⟩

theorem starMap_spec
    (g : Hj) (i : Fin 24) : StarOK (g : J) i (starMap g i) :=
  (starOK_closure g.1 g.2 i i.2).choose_spec.2

theorem starMap_eq
    {g : Hj} {i i' : Fin 24} (h : StarOK (g : J) i i') : starMap g i = i' :=
  Fin.ext (starOK_unique i.2 (starMap g i).2 i'.2 (starMap_spec g i) h)

theorem starMap_mul
    (g h : Hj) (i : Fin 24) : starMap (g * h) i = starMap g (starMap h i) :=
  starMap_eq (starOK_mul (starMap_spec h i) (starMap_spec g (starMap h i)))

theorem starMap_one
    (i : Fin 24) : starMap 1 i = i :=
  starMap_eq (by simpa using starOK_one i)

noncomputable def starHom :
    Hj →* Equiv.Perm (Fin 24) where
  toFun g :=
    { toFun := starMap g
      invFun := starMap g⁻¹
      left_inv := fun i => by rw [← starMap_mul, inv_mul_cancel, starMap_one]
      right_inv := fun i => by rw [← starMap_mul, mul_inv_cancel, starMap_one] }
  map_one' := by ext i; exact congrArg Fin.val (starMap_one i)
  map_mul' g h := by ext i; exact congrArg Fin.val (starMap_mul g h i)

instance hjQuotNormal :
    ((Eg uJ 11).subgroupOf Hj).Normal :=
  (Subgroup.normal_subgroupOf_iff Eg_le_Hj).2 fun h g hh hg =>
    Hj_normalizes_Eg j4Facts.mat g hg h hh

theorem starHom_xJ
    {k : ℕ} (hk : k < 3) : starHom ⟨xJ k, xJ_mem hk⟩ = tauOf k := by
  ext i
  have h := starMap_eq (g := ⟨xJ k, xJ_mem hk⟩) (i := i)
    (i' := ⟨(starPermOf k).getD i 0, (star_perm_facts k hk).2.1 i i.2⟩) (starOK_gen hk i.2)
  have h2 := (tau_facts k hk).1 i
  show (starMap ⟨xJ k, xJ_mem hk⟩ i : ℕ) = (tauOf k i : ℕ)
  rw [h, h2]

theorem range_starHom
    : starHom.range = Subgroup.closure {tauOf 0, tauOf 1, tauOf 2} := by
  have htop : Subgroup.closure ((((↑) : Hj → J)) ⁻¹' ({xJ 0, xJ 1, xJ 2} : Set J)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  congr 1
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with h | h | h
    · have : x = ⟨xJ 0, xJ_mem (by norm_num)⟩ := Subtype.ext h
      rw [this, starHom_xJ (by norm_num)]; exact Or.inl rfl
    · have : x = ⟨xJ 1, xJ_mem (by norm_num)⟩ := Subtype.ext h
      rw [this, starHom_xJ (by norm_num)]; exact Or.inr (Or.inl rfl)
    · have : x = ⟨xJ 2, xJ_mem (by norm_num)⟩ := Subtype.ext h
      rw [this, starHom_xJ (by norm_num)]; exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨xJ 0, xJ_mem (by norm_num)⟩, Or.inl rfl, starHom_xJ (by norm_num)⟩
    · exact ⟨⟨xJ 1, xJ_mem (by norm_num)⟩, Or.inr (Or.inl rfl), starHom_xJ (by norm_num)⟩
    · exact ⟨⟨xJ 2, xJ_mem (by norm_num)⟩, Or.inr (Or.inr rfl), starHom_xJ (by norm_num)⟩

theorem ker_starHom :
    starHom.ker = (Eg uJ 11).subgroupOf Hj := by
  have hM := j4Facts.mat
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hfix : ∀ i : Fin 24, starMap g i = i := fun i => by
      have := congrArg (fun p : Equiv.Perm (Fin 24) => p i) hg
      simpa [starHom] using this
    have hOK : ∀ i < 24, StarOK (g : J) i i := fun i hi => by
      have := starMap_spec g ⟨i, hi⟩
      rwa [hfix ⟨i, hi⟩] at this
    obtain ⟨-, -, -, -, hint, hcov, hbasis⟩ := star_facts
    have hduad : ∀ d ∈ duadMasks, (g : J) * eta uJ 11 d * (g : J)⁻¹ = eta uJ 11 d := by
      intro d hd
      obtain ⟨i, hi, j, hj, hij, hdi, hdj⟩ := hcov d hd
      obtain ⟨c₁, hc₁, e₁⟩ := hOK i hi d hdi
      obtain ⟨c₂, hc₂, e₂⟩ := hOK j hj d hdj
      have hc12 : c₁ = c₂ :=
        eta_inj hM c₁ (mem_star_lt hi hc₁) c₂ (mem_star_lt hj hc₂) (e₁.symm.trans e₂)
      have hc1d : c₁ = d := hint i hi j hj hij c₁ hc₁ (hc12 ▸ hc₂) d hdi hdj
      rw [e₁, hc1d]
    have hle : Eg uJ 11 ≤ Subgroup.centralizer ({(g : J)} : Set J) := by
      rw [Eg, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 := hduad (2 ^ j) (hbasis j hj)
      rw [eta_two_pow hj] at h1
      calc (g : J) * uJ j = ((g : J) * uJ j * (g : J)⁻¹) * (g : J) := by group
        _ = uJ j * (g : J) := by rw [h1]
    have hcomm : ∀ y ∈ Eg uJ 11, (g : J) * y = y * (g : J) := fun y hy =>
      Subgroup.mem_centralizer_iff.1 (hle hy) (g : J) rfl
    exact centralizer_Hj hM j4Facts g g.2 hcomm
  · intro hg
    ext i
    have hOK : StarOK (g : J) i i := fun c hc => by
      refine ⟨c, hc, ?_⟩
      have hc' : eta uJ 11 c ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl c
      have := Eg_comm (elem_uJ hM) hg hc'
      calc (g : J) * eta uJ 11 c * (g : J)⁻¹ = eta uJ 11 c * (g : J) * (g : J)⁻¹ := by rw [this]
        _ = eta uJ 11 c := by group
    exact congrArg Fin.val (starMap_eq (g := g) (i := i) hOK)

theorem card_Hj_quotient
    : Nat.card (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) = 244823040 := by
  have hM := j4Facts.mat
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Eg uJ 11).subgroupOf Hj)
  have h2 : Nat.card ((Eg uJ 11).subgroupOf Hj) = 2 ^ 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).toEquiv]
    exact card_Eg_uJ hM
  rw [card_Hj j4Facts, h2] at h1
  omega

theorem range_starHom_eq
    : starHom.range = CFSG.Blueprint.NativeSporadic.M24 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [range_starHom, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> exact tauOf_mem (by norm_num)
  · rw [card_M24]
    have : Nat.card starHom.range = 244823040 := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange starHom).toEquiv, ker_starHom,
        card_Hj_quotient]
    omega

theorem isSimpleGroup_Hj_quotient
    : IsSimpleGroup (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) := by
  have e1 : (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) ≃* ↥starHom.range :=
    (QuotientGroup.quotientMulEquivOfEq ker_starHom.symm).trans
      (QuotientGroup.quotientKerEquivRange starHom)
  have e2 : ↥starHom.range ≃* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    MulEquiv.subgroupCongr range_starHom_eq
  have := fam_m24_simplicity.2.2
  exact (e1.trans e2).isSimpleGroup

theorem goodLocal_Hj :
    GoodLocal Hj := by
  have hM := j4Facts.mat
  refine goodLocal_of_simple_quotient Hj (Eg uJ 11) Eg_le_Hj (isPGroup_Eg (elem_uJ hM))
    ((Subgroup.normal_subgroupOf_iff Eg_le_Hj).2 fun h g hh hg => Hj_normalizes_Eg hM g hg h hh)
    (centralizer_Hj hM j4Facts) isSimpleGroup_Hj_quotient ?_ ?_
  · intro h2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    rw [card_Hj_quotient] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ ⟨81607680, by norm_num⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  · rw [card_Hj_quotient]
    exact not_chi0Order_M24

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
