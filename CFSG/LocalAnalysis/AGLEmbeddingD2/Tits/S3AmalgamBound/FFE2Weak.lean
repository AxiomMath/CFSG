module

public import CFSG.Quasithin.Background.C1PackNat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}
  {H T M : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem Blocks.card_le_two' (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : I.card ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨L₁, hL₁, L₂, hL₂, L₃, hL₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  set X := autI hV H with hX
  have hmemX : ∀ g : H, convHom hV H hHN g ∈ X := fun g => by
    rw [hX, ← range_convHom hV H hHN]
    exact ⟨g, rfl⟩
  let φ : H →* X := (convHom hV H hHN).codRestrict X hmemX
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [hX, ← range_convHom hV H hHN] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKX : autI hV (twoResidual H) ≤ X := autI_mono hV (twoResidual_le H)
  set K3 : Subgroup X := (autI hV (twoResidual H)).subgroupOf X with hK3
  have hK3p : IsPGroup 3 K3 :=
    (B.isPGroup_autI_twoResidual h hsolv hred hJ).of_equiv (Subgroup.subgroupOfEquivOfLe hKX).symm
  have hK3n : K3.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [hK3, Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨a, haK, hak⟩ := (mem_autI hV).1 hk
    obtain ⟨b, hbH, hbg⟩ := (mem_autI hV).1 g.2
    have hbab : ((b * a * b⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈ twoResidual H := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H hbH) a).mp haK
    refine (mem_autI hV).2 ⟨b * a * b⁻¹, hbab, ?_⟩
    simp only [map_mul, map_inv, hak, hbg, Subgroup.coe_mul, Subgroup.coe_inv]
  have hK3le : K3 ≤ CFSG.Open.pCore 3 X := CFSG.LieType.BorelTits.le_pCore 3 hK3n hK3p
  have hsolvX : Group.IsSolvable X := isSolvable_autI hV hHN hsolv
  have hO2X : CFSG.Open.pCore 2 X = ⊥ := by
    set P2 := CFSG.Open.pCore 2 X with hP2
    have hP2n : P2.Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hP2p : IsPGroup 2 P2 := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have h1 : P2.map X.subtype = ⊥ := by
      refine eq_bot_of_normal_isPGroup hV hred (Subgroup.map_subtype_le P2) ?_
        (hP2p.map X.subtype)
      have : (P2.map X.subtype).subgroupOf X = P2 :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective P2
      rw [this]
      exact hP2n
    exact (Subgroup.map_eq_bot_iff_of_injective P2 X.subtype_injective).mp h1
  have h2P : ∀ y : X, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore 3 X := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hy
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H g hgH
    refine ⟨k, hK3le ?_⟩
    rw [hK3, Subgroup.mem_subgroupOf, Subgroup.coe_pow, ← map_pow]
    exact convI_mem_autI hV hk _
  have hF := centralizer_pCore_le Nat.prime_three h2P hO2X hsolvX
  have hA := (A1c.A131Concl_of_surjective (p := 3) (by norm_num) hF _ ↥X
    (MonoidHom.id ↥X) Function.surjective_id rfl hSQT).1
  obtain ⟨t, htL, -, -, ht2⟩ := B.exists_orderOf_eq_two hred h.isSylow hL₁
  obtain ⟨f₂, hf₂L, hf₂K, hf₂3⟩ := B.exists_orderOf_eq_three hL₂
  obtain ⟨f₃, hf₃L, hf₃K, hf₃3⟩ := B.exists_orderOf_eq_three hL₃
  set t' : X := ⟨t, B.le_autI hL₁ htL⟩ with ht'
  have ht'2 : orderOf t' = 2 := by rw [ht', Subgroup.orderOf_mk, ht2]
  set T' : Subgroup X := Subgroup.zpowers t' with hT'
  have hT'p : IsPGroup 2 T' := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one])
  have hT'1 : T' ≠ ⊥ := by
    intro he
    have h1 : t' ∈ T' := Subgroup.mem_zpowers t'
    rw [he, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at ht'2
    norm_num at ht'2
  have hcyc := hA T' hT'p hT'1
  set C := CFSG.Open.pCore 3 X ⊓ Subgroup.centralizer (T' : Set X) with hC
  have hmemC : ∀ (f : MulAut (IntMod V hV)) (L : Subgroup (MulAut (IntMod V hV))), L ∈ I →
      L ≠ L₁ → f ∈ L → f ∈ autI hV (twoResidual H) →
        ∃ hf : f ∈ X, (⟨f, hf⟩ : X) ∈ C := by
    intro f L hL hLL hfL hfK
    refine ⟨hKX hfK, Subgroup.mem_inf.mpr ⟨hK3le (Subgroup.mem_subgroupOf.mpr hfK), ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute t' ⟨f, hKX hfK⟩ := Subtype.ext (B.comm hL₁ hL hLL.symm htL hfL)
    exact (hc.zpow_left i).eq
  obtain ⟨hf₂X, hf₂C⟩ := hmemC f₂ L₂ hL₂ (Ne.symm h12) hf₂L hf₂K
  obtain ⟨hf₃X, hf₃C⟩ := hmemC f₃ L₃ hL₃ (Ne.symm h13) hf₃L hf₃K
  have : IsCyclic C := hcyc
  let : Fintype C := Fintype.ofFinite _
  set a : C := ⟨⟨f₂, hf₂X⟩, hf₂C⟩ with ha
  set b : C := ⟨⟨f₃, hf₃X⟩, hf₃C⟩ with hb
  have hinj : ∀ x y : C, ((x : X) : MulAut (IntMod V hV)) = ((y : X) : MulAut (IntMod V hV)) →
      x = y := fun x y hxy => Subtype.ext (Subtype.ext hxy)
  have hf₂1 : f₂ ≠ 1 := fun he => by rw [he, orderOf_one] at hf₂3; norm_num at hf₂3
  have hf₃1 : f₃ ≠ 1 := fun he => by rw [he, orderOf_one] at hf₃3; norm_num at hf₃3
  have hf₂sq : f₂ ^ 2 ≠ 1 := fun he => by
    have := orderOf_dvd_of_pow_eq_one he
    rw [hf₂3] at this
    norm_num at this
  have hf₂f₂ : f₂ ≠ f₂ ^ 2 := fun he => hf₂1 (by
    have : f₂ * 1 = f₂ * f₂ := by rw [mul_one, ← pow_two, ← he]
    exact (mul_left_cancel this).symm)
  have hf₃L₂ : ∀ y ∈ L₂, f₃ ≠ y := fun y hy he =>
    hf₃1 (B.eq_one_of_mem_of_mem hL₃ hL₂ h23 hf₃L (he ▸ hy))
  have hsub : ({1, a, a ^ 2, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · apply hinj
      simp [ha, ← hf₂3, pow_orderOf_eq_one]
    · apply hinj
      simp only [ha, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← pow_mul, mul_comm, pow_mul, ← hf₂3, pow_orderOf_eq_one, one_pow]
    · apply hinj
      simp [hb, ← hf₃3, pow_orderOf_eq_one]
  have hcard4 : ({1, a, a ^ 2, b} : Finset C).card = 4 := by
    have h1a : (1 : C) ≠ a := fun he => hf₂1 (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have h1a2 : (1 : C) ≠ a ^ 2 := fun he => hf₂sq (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have h1b : (1 : C) ≠ b := fun he => hf₃1 (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have haa2 : a ≠ a ^ 2 := fun he => hf₂f₂ (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he)
    have hab : a ≠ b := fun he => hf₃L₂ f₂ hf₂L (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have ha2b : a ^ 2 ≠ b := fun he => hf₃L₂ (f₂ ^ 2) (L₂.pow_mem hf₂L 2) (congrArg
      (fun x : C => ((x : X) : MulAut (IntMod V hV))) he).symm
    rw [Finset.card_insert_of_notMem (by simp [h1a, h1a2, h1b]),
      Finset.card_insert_of_notMem (by simp [haa2, hab]), Finset.card_pair ha2b]
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 3) (by norm_num)
  have := Finset.card_le_card hsub
  omega

theorem Blocks.card_eq_one_or_two' (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : I.card = 1 ∨ I.card = 2 := by
  have h1 := (B.nonempty h.isSylow hred hJ).card_pos
  have h2 := B.card_le_two' h hsolv hSQT hred hJ
  omega

theorem Blocks.eq_singleton_or_pair' (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    (∃ L₁ ∈ I, ∀ L ∈ I, L = L₁) ∨
      ∃ L₁ ∈ I, ∃ L₂ ∈ I, L₁ ≠ L₂ ∧ ∀ L ∈ I, L = L₁ ∨ L = L₂ := by
  classical
  rcases B.card_eq_one_or_two' h hsolv hSQT hred hJ with h1 | h2
  · obtain ⟨L₁, hL₁⟩ := Finset.card_eq_one.mp h1
    refine Or.inl ⟨L₁, by rw [hL₁]; exact Finset.mem_singleton_self _, fun L hL => ?_⟩
    rw [hL₁] at hL
    exact Finset.mem_singleton.mp hL
  · obtain ⟨L₁, L₂, hne, hI⟩ := Finset.card_eq_two.mp h2
    refine Or.inr ⟨L₁, by rw [hI]; simp, L₂, by rw [hI]; simp, hne, fun L hL => ?_⟩
    rw [hI] at hL
    simpa using hL

theorem Blocks.fixV_twoResidual_inf' (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commSub ⊤ L = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwK, hwL⟩
  rw [Subgroup.mem_bot]
  rcases B.eq_singleton_or_pair' h hsolv hSQT hred hJ with ⟨L₁, hL₁, hI⟩ |
    ⟨L₁, hL₁, L₂, hL₂, hne, hI⟩
  · rw [iSup_eq_of_singleton hL₁ hI] at hwL
    obtain ⟨f, hfL, hfK, hf3⟩ := B.exists_orderOf_eq_three hL₁
    exact B.eq_one_of_orderOf_eq_three hL₁ hfL hf3 hwL (hwK f hfK)
  · rw [iSup_eq_of_pair hL₁ hL₂ hI] at hwL
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hwL
    obtain ⟨f₁, hf₁L, hf₁K, hf₁3⟩ := B.exists_orderOf_eq_three hL₁
    obtain ⟨f₂, hf₂L, hf₂K, hf₂3⟩ := B.exists_orderOf_eq_three hL₂
    have h12 : f₁ w₂ = w₂ := B.hb.triv L₁ (B.sub hL₁) L₂ (B.sub hL₂) hne f₁ hf₁L w₂ hw₂
    have h21 : f₂ w₁ = w₁ := B.hb.triv L₂ (B.sub hL₂) L₁ (B.sub hL₁) (Ne.symm hne) f₂ hf₂L w₁ hw₁
    have e1 := hwK f₁ hf₁K
    rw [map_mul, h12, mul_left_inj] at e1
    have e2 := hwK f₂ hf₂K
    rw [map_mul, h21, mul_right_inj] at e2
    rw [B.eq_one_of_orderOf_eq_three hL₁ hf₁L hf₁3 hw₁ e1,
      B.eq_one_of_orderOf_eq_three hL₂ hf₂L hf₂3 hw₂ e2, one_mul]

theorem Blocks.fixV_twoResidual' (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    fixV (autI hV (twoResidual H)) = fixV (autI hV (thompsonJ H)) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hKJ : autI hV (twoResidual H) ≤ autI hV (thompsonJ H) :=
    autI_mono hV (twoResidual_le_thompsonJ h hred hJ)
  refine le_antisymm (fun v hv => ?_) (B1.fixV_le_fixV hKJ)
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq] at hdec
  have hv' : v ∈ fixV (autI hV (thompsonJ H)) ⊔ ⨆ L ∈ I, commSub ⊤ L := by
    rw [hdec.1]
    exact Subgroup.mem_top v
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.mp hv'
  have hcK : c ∈ fixV (autI hV (twoResidual H)) := B1.fixV_le_fixV hKJ hc
  have hwK : w ∈ fixV (autI hV (twoResidual H)) := by
    have := (fixV (autI hV (twoResidual H))).mul_mem
      ((fixV (autI hV (twoResidual H))).inv_mem hcK) hv
    simpa using this
  have hw1 : w = 1 := by
    have hmem : w ∈ fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commSub ⊤ L := ⟨hwK, hw⟩
    rw [B.fixV_twoResidual_inf' h hsolv hSQT hred hJ, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hw1, mul_one]
  exact hc

theorem Blocks.autI_baum' (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    autI hV (baum T) = autI hV (thompsonJ T) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hT := h.isSylow
  refine le_antisymm (fun x hx => ?_) (autI_mono hV (thompsonJ_le_baum T))
  have hxH : x ∈ autI hV H := autI_mono hV (inf_le_left.trans hT.1) hx
  have hex : ∀ L, ∃ t : MulAut (IntMod V hV), L ∈ I →
      t ∈ L ∧ t ∈ autI hV (thompsonJ T) ∧ orderOf t = 2 := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨t, htL, -, htJ, ht2⟩ := B.exists_orderOf_eq_two hred hT hL
      exact ⟨t, fun _ => ⟨htL, htJ, ht2⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose t ht using hex
  have hexc : ∀ L, ∃ c : IntMod V hV, L ∈ I → c ∈ commSub ⊤ L ∧ c ≠ 1 ∧ t L c = c := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨c, hc, hc1, htc⟩ := B.exists_fix hL (ht L hL).1 (ht L hL).2.2
      exact ⟨c, fun _ => ⟨hc, hc1, htc⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose c hc using hexc
  have hJTeq := B.autI_thompsonJ_eq hT hsolv hred hJ t (fun L hL => ht L hL)
  have hcfix : ∀ L ∈ I, c L ∈ fixV (autI hV (thompsonJ T)) := by
    intro L hL y hy
    rw [hJTeq] at hy
    have hle : (⨆ L' ∈ I, Subgroup.zpowers (t L')) ≤
        MulAction.stabilizer (MulAut (IntMod V hV)) (c L) := by
      refine iSup₂_le fun L' hL' => Subgroup.zpowers_le.2 ?_
      rw [MulAction.mem_stabilizer_iff]
      by_cases hLL : L' = L
      · subst hLL
        exact (hc L' hL).2.2
      · exact B.hb.triv L' (B.sub hL') L (B.sub hL) hLL (t L') (ht L' hL').1 (c L) (hc L hL).1
    exact hle hy
  have hxc : ∀ L ∈ I, x (c L) = c L := fun L hL => baum_fix hred hT hx (hcfix L hL)
  have hloc : ∀ L ∈ I, ∃ l ∈ Subgroup.zpowers (t L),
      ∀ u ∈ commSub (⊤ : Subgroup (IntMod V hV)) L, x u = l u := fun L hL =>
    B.exists_local hL hxH (ht L hL).1 (ht L hL).2.2 (hc L hL).1 (hc L hL).2.1 (hc L hL).2.2
      (hxc L hL)
  have hJTJH : autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
    autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
  have hxC : ∀ u ∈ fixV (autI hV (thompsonJ H)), x u = u := fun u hu =>
    baum_fix hred hT hx (B1.fixV_le_fixV hJTJH hu)
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq] at hdec
  have hJTle : ∀ L ∈ I, Subgroup.zpowers (t L) ≤ autI hV (thompsonJ T) := fun L hL =>
    Subgroup.zpowers_le.2 (ht L hL).2.1
  rcases B.eq_singleton_or_pair' h hsolv hSQT hred hJ with ⟨L₁, hL₁, hI⟩ |
    ⟨L₁, hL₁, L₂, hL₂, hne, hI⟩
  · obtain ⟨l₁, hl₁, hxl₁⟩ := hloc L₁ hL₁
    have hl₁L : l₁ ∈ L₁ := Subgroup.zpowers_le.2 (ht L₁ hL₁).1 hl₁
    have hl₁J : l₁ ∈ autI hV (thompsonJ H) := B.le_thompsonJ hL₁ hl₁L
    rw [iSup_eq_of_singleton hL₁ hI] at hdec
    have hy : x * l₁⁻¹ = 1 := by
      refine eq_one_of_fix_sup hdec.1 (fun u hu => ?_) (fun u hu => ?_)
      · rw [MulAut.mul_apply, hu l₁⁻¹ ((autI hV (thompsonJ H)).inv_mem hl₁J), hxC u hu]
      · have hu' : l₁⁻¹ u ∈ commSub (⊤ : Subgroup (IntMod V hV)) L₁ :=
          B.hb.stab L₁ (B.sub hL₁) _ (L₁.inv_mem hl₁L) u hu
        rw [MulAut.mul_apply, hxl₁ _ hu', ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [mul_inv_eq_one] at hy
    rw [hy]
    exact hJTle L₁ hL₁ hl₁
  · obtain ⟨l₁, hl₁, hxl₁⟩ := hloc L₁ hL₁
    obtain ⟨l₂, hl₂, hxl₂⟩ := hloc L₂ hL₂
    have hl₁L : l₁ ∈ L₁ := Subgroup.zpowers_le.2 (ht L₁ hL₁).1 hl₁
    have hl₂L : l₂ ∈ L₂ := Subgroup.zpowers_le.2 (ht L₂ hL₂).1 hl₂
    have hl₁J : l₁ ∈ autI hV (thompsonJ H) := B.le_thompsonJ hL₁ hl₁L
    have hl₂J : l₂ ∈ autI hV (thompsonJ H) := B.le_thompsonJ hL₂ hl₂L
    rw [iSup_eq_of_pair hL₁ hL₂ hI] at hdec
    have htop : fixV (autI hV (thompsonJ H)) ⊔ (commSub ⊤ L₁ ⊔ commSub ⊤ L₂) = ⊤ := hdec.1
    have hy : x * (l₁ * l₂)⁻¹ = 1 := by
      refine eq_one_of_fix_sup htop (fun u hu => ?_) (fun u hu => ?_)
      · rw [MulAut.mul_apply, hu _ ((autI hV (thompsonJ H)).inv_mem
          ((autI hV (thompsonJ H)).mul_mem hl₁J hl₂J)), hxC u hu]
      · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
        have hu₁' : l₁⁻¹ u₁ ∈ commSub (⊤ : Subgroup (IntMod V hV)) L₁ :=
          B.hb.stab L₁ (B.sub hL₁) _ (L₁.inv_mem hl₁L) u₁ hu₁
        have hu₂' : l₂⁻¹ u₂ ∈ commSub (⊤ : Subgroup (IntMod V hV)) L₂ :=
          B.hb.stab L₂ (B.sub hL₂) _ (L₂.inv_mem hl₂L) u₂ hu₂
        have h1 : (l₁ * l₂)⁻¹ u₁ = l₁⁻¹ u₁ := by
          rw [mul_inv_rev, MulAut.mul_apply, B.hb.triv L₂ (B.sub hL₂) L₁ (B.sub hL₁)
            (Ne.symm hne) _ (L₂.inv_mem hl₂L) _ hu₁']
        have h2 : (l₁ * l₂)⁻¹ u₂ = l₂⁻¹ u₂ := by
          rw [mul_inv_rev, MulAut.mul_apply, B.hb.triv L₁ (B.sub hL₁) L₂ (B.sub hL₂) hne _
            (L₁.inv_mem hl₁L) _ hu₂]
        rw [MulAut.mul_apply, map_mul, h1, h2, map_mul, hxl₁ _ hu₁', hxl₂ _ hu₂',
          ← MulAut.mul_apply, ← MulAut.mul_apply, mul_inv_cancel, mul_inv_cancel,
          MulAut.one_apply, MulAut.one_apply]
    rw [mul_inv_eq_one] at hy
    rw [hy]
    exact (autI hV (thompsonJ T)).mul_mem (hJTle L₁ hL₁ hl₁) (hJTle L₂ hL₂ hl₂)

end E2

open E2 in
theorem E2_3_one_of_isSolvable' {G : Type*} [Group G] [Finite G] {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    twoResidual H ≤ thompsonJ H ∧
    ∃ I : Finset (Subgroup (MulAut (IntMod V hV))),
      (I.card = 1 ∨ I.card = 2) ∧
      autI hV (thompsonJ H) = ⨆ L ∈ I, L ∧
      (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
      (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
      (∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L') ∧
      (∀ L ∈ I, ActsAsNaturalL2 L (commV L)) ∧
      fixV (autI hV (twoResidual H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
      fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commV L = ⊥ ∧
      (∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have h3 := hSQT
  obtain ⟨𝓗, I, B⟩ := exists_blocks hV hred hsolv h.isSylow hJ
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq, ← B.fixV_twoResidual' h hsolv h3 hred hJ] at hdec
  refine ⟨twoResidual_le_thompsonJ h hred hJ, I, B.card_eq_one_or_two' h hsolv h3 hred hJ, B.eq,
    fun L hL L' hL' hne a ha b hb => B.comm hL hL' hne ha hb, fun L hL => B.inf_biSup_ne hL,
    fun L hL L' hL' => B.transitive h hred hJ hL hL', fun L hL => ?_, ?_, ?_, fun L hL => ?_⟩
  · rw [commV_eq_commSub]
    exact actsAsNaturalL2_of_full hW (B.hb.card_comm L (B.sub hL)) (B.hb.le_stabSub (B.sub hL))
      (B.hb.inf_centSub (B.sub hL)) (B.hb.autSub_eq_top L (B.sub hL))
  · simp only [commV_eq_commSub]
    exact hdec.1
  · simp only [commV_eq_commSub]
    exact hdec.2
  · simp only [commV_eq_commSub]
    refine le_bot_iff.1 ?_
    calc commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' ≤
        commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' :=
          inf_le_inf_left _ (iSup₂_mono' fun L' hL' => ⟨L', B.sub hL', le_rfl⟩)
      _ = ⊥ := B.hb.commSub_inf_biSup_ne_eq_bot hW (B.sub hL)

open E2 in
theorem E2_3_two_sylow_of_isSolvable' {G : Type*} [Group G] [Finite G] {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV H)) ≤ 2)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    autI hV (baum T) = autI hV (thompsonJ T) ∧
      IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) := by
  have h3 := hSQT
  obtain ⟨𝓗, I, B⟩ := exists_blocks hV hred hsolv h.isSylow hJ
  obtain ⟨-, hsyl, -⟩ := B2F.structure_of_not_le hV hred hsolv h.isSylow hJ
  exact ⟨B.autI_baum' h hsolv h3 hred hJ, hsyl⟩

end CFSG.Quasithin

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
open scoped commutatorElement
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem exists_single_block' {P S MP V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic P S MP) (hsolv : Group.IsSolvable ↥P)
    (hSQT : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV P)) ≤ 2) (hred : IsTwoReducedIn P V)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G)) (hS : baum S = S) :
    ∃ L : Subgroup (MulAut (IntMod V hV)), autI hV P = L ∧ ActsAsNaturalL2 L (commV L) := by
  classical
  obtain ⟨hKJ, I, hcard, hJeq, hcomm, hind, htrans, hnat, -, -, -⟩ :=
    E2_3_one_of_isSolvable' hV h hsolv hSQT hred hJ
  obtain ⟨hSb, -⟩ := E2_3_two_sylow_of_isSolvable' hV h hsolv hSQT hred hJ
  rw [hS] at hSb
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hSP : S ≤ P := h.isSylow.1
  have hSJ : autI hV S ≤ ⨆ L ∈ I, L :=
    hSb ▸ ((autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJeq.le)
  have hLne : ∀ L ∈ I, L ≠ ⊥ := by
    intro L hL hL0
    obtain ⟨e, -, -⟩ := hnat L hL
    have h1 : Nat.card ↥L = Nat.card SL2F2 := Nat.card_congr e.toEquiv
    rw [hL0, Subgroup.card_bot, card_sl2F2] at h1
    omega
  have hI : ∃ L, I = {L} := by
    rcases hcard with h1 | h2
    · exact Finset.card_eq_one.1 h1
    · exfalso
      obtain ⟨L₁, L₂, hne, rfl⟩ := Finset.card_eq_two.1 h2
      have hm₁ : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
      have hm₂ : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))) := by simp
      obtain ⟨t, ht1, ht2⟩ := htrans L₁ hm₁ L₂ hm₂
      have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hcomm L₁ hm₁ L₂ hm₂ hne
      have hsup2 : (⨆ L ∈ ({L₁, L₂} : Finset (Subgroup (MulAut (IntMod V hV)))), L) = L₁ ⊔ L₂ := by
        apply le_antisymm
        · refine iSup₂_le fun L hL => ?_
          rcases Finset.mem_insert.1 hL with rfl | hL
          · exact le_sup_left
          · rw [Finset.mem_singleton.1 hL]
            exact le_sup_right
        · exact sup_le (le_iSup₂_of_le L₁ hm₁ le_rfl) (le_iSup₂_of_le L₂ hm₂ le_rfl)
      have htsup : t ∈ L₁ ⊔ L₂ := hsup2 ▸ hSJ ht1
      have hxfix : ∀ a ∈ L₁, ∀ y ∈ L₂, a * y * a⁻¹ = y := fun a ha y hy => by
        rw [hc a ha y hy, mul_inv_cancel_right]
      have hnormL₂ : L₁ ≤ Subgroup.normalizer (L₂ : Set (MulAut (IntMod V hV))) := fun a ha => by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hxL
          rwa [hxfix a ha x hxL]
        · intro hxL
          have h1 := hxfix a⁻¹ (L₁.inv_mem ha) _ hxL
          have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
          rw [h2] at h1
          rw [h1]
          exact hxL
      obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hnormL₂).1 htsup
      have hinf : L₁ ⊓ L₂ = ⊥ := by
        refine le_bot_iff.1 ((inf_le_inf_left L₁ ?_).trans (hind L₁ hm₁).le)
        exact le_iSup₂_of_le L₂ hm₂ (le_iSup (fun _ : L₂ ≠ L₁ => L₂) hne.symm)
      apply hLne L₂ hm₂
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ B1.conjAut (a * b) L₁ := ht2 ▸ hx
      rw [B1.mem_conjAut] at h1
      have h2 : (a * b)⁻¹ * x * (a * b) ∈ L₂ := by
        have h3 : (a * b)⁻¹ * x * (a * b) = b⁻¹ * x * b := by
          have h4 := hxfix a⁻¹ (L₁.inv_mem ha) x hx
          calc (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
            _ = b⁻¹ * x * b := by
              have : a⁻¹ * x * a = x := by simpa using h4
              rw [this]
        rw [h3]
        exact L₂.mul_mem (L₂.mul_mem (L₂.inv_mem hb) hx) hb
      have h5 : (a * b)⁻¹ * x * (a * b) ∈ L₁ ⊓ L₂ := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot] at h5
      have : x = 1 := by
        have h6 : x = (a * b) * ((a * b)⁻¹ * x * (a * b)) * (a * b)⁻¹ := by group
        rw [h6, h5]
        group
      exact (Subgroup.mem_bot).2 this
  obtain ⟨L, rfl⟩ := hI
  refine ⟨L, ?_, hnat L (Finset.mem_singleton_self L)⟩
  have hJL : autI hV (thompsonJ P) = L := by simpa using hJeq
  apply le_antisymm
  · rw [← sup_twoResidual_eq h.isSylow,
      autI_sup hV (hSP.trans hPN) ((twoResidual_le P).trans hPN)]
    refine sup_le ?_ ?_
    · rw [hSb]
      exact (autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJL.le
    · exact (autI_mono hV hKJ).trans hJL.le
  · rw [← hJL]
    exact autI_mono hV (B6.thompsonJ_le P)

theorem inClassG_of_solvable_minParabolic' {P S MP : Subgroup G} (h : MinParabolic P S MP)
    (hF : CharTwo P) (hsolv : Group.IsSolvable ↥P)
    (hSQT : ∀ hV : IsElemAbelian 2 (VZ S P), CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hV P)) ≤ 2)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S P : Set G)) (hS : baum S = S) :
    InClassG P S := by
  obtain ⟨-, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo h.isSylow hF (le_refl _)
  obtain ⟨L, hL, hnat⟩ := exists_single_block' hVel h hsolv (hSQT hVel) hred hJ hS
  obtain ⟨hn1, -, -⟩ := isNatL2Section_fstarPre hVel hred.2.1 hL hnat
  exact ⟨h.isSylow, hF, (minParabolic_iff.1 h).1, 1, le_rfl, hn1⟩

end CFSG.Quasithin.C1Pack
