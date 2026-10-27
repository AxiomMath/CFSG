module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeModel3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAlpha
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeModel2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172X
open CFSG.LocalAnalysis.GLTheoremA.S10 (cs)
open scoped commutatorElement

theorem max_field {Ω : Type} [Group Ω] [Finite Ω] {B L : Subgroup Ω} {x : Ω}
    {G₀ : Type} [Group G₀] [Finite G₀] (M : S172Model L B G₀)
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L) (hLn : L.Normal)
    (hnoZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    (hmax : CFSG.LocalAnalysis.GLTheoremA.S171.MaxG 3 B) :
    ∀ E : Subgroup G₀, IsElemAbelian 3 E → TwoLocal E →
      Nat.card E ≤ Nat.card M.β.range := by
  classical
  haveI := hLn
  have hBker := M.card_ker_β hcfg.prime hcfg.elem hcfg.mem hcfg.ne_one hcfg.cent
  have hBcard := Subgroup.card_ker_mul_card_range M.β
  rw [hBker] at hBcard
  intro E hEel hEtwo
  obtain ⟨P, hP2, hP1, hEP⟩ := hEtwo
  have hPmap : (E.comap M.π).map M.π = E :=
    Subgroup.map_comap_eq_self_of_surjective M.surj E
  obtain ⟨R, -, hRel, hRmap, hRcardE⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_elemAbelian_lift
      hcfg.prime (by simpa [M.ker_π] using hnoZ) hPmap hEel
  obtain ⟨Q, hQ1, hQ2, hRQ⟩ :=
    CFSG.RankThree.CentralCover.exists_two_subgroup_normalized_of_cover M.surj
      (by simpa [M.ker_π] using le_rfl) hP1 hP2 (S := R) (by
        intro y hy u hu
        have hyE : M.π y ∈ E := by
          rw [← hRmap]
          exact Subgroup.mem_map_of_mem M.π hy
        exact (Subgroup.mem_normalizer_iff.1 (hEP hyE) u).1 hu)
  let E0 : Subgroup Ω := R.map L.subtype
  have hE0el : IsElemAbelian 3 E0 := hRel.map L.subtype
  have hE0card : Nat.card E0 = Nat.card E := by
    dsimp only [E0]
    rw [Subgroup.card_map_of_injective L.subtype_injective, hRcardE]
  have hE0L : E0 ≤ L := Subgroup.map_subtype_le R
  let Q' : Subgroup Ω := Q.map L.subtype
  have hQ'1 : Q' ≠ ⊥ := by
    intro h
    have h' : Q.map L.subtype = ⊥ := by simpa [Q'] using h
    exact hQ1 (Subgroup.map_injective L.subtype_injective (by rw [h', Subgroup.map_bot]))
  have hQ'2 : IsPGroup 2 Q' := hQ2.map L.subtype
  have hE0N : E0 ≤ Subgroup.normalizer (Q' : Set Ω) := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 he
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      obtain ⟨q0, hq0, rfl⟩ := Subgroup.mem_map.1 hq
      have h1 : r * q0 * r⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 (hRQ hr) q0).1 hq0
      exact Subgroup.mem_map.2 ⟨r * q0 * r⁻¹, h1, rfl⟩
    · intro hq
      obtain ⟨q0, hq0, hqeq⟩ := Subgroup.mem_map.1 hq
      have h1 : r⁻¹ * q0 * r ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.1 (hRQ (R.inv_mem hr)) q0).1 hq0
      have hqeq' : q = (r : Ω)⁻¹ * L.subtype q0 * (r : Ω) := by
        calc q = (r : Ω)⁻¹ * ((r : Ω) * q * (r : Ω)⁻¹) * (r : Ω) := by group
          _ = (r : Ω)⁻¹ * L.subtype q0 * (r : Ω) := by
            rw [show (r : Ω) * q * (r : Ω)⁻¹ = L.subtype q0 from hqeq.symm]
      rw [hqeq']
      exact Subgroup.mem_map.2 ⟨r⁻¹ * q0 * r, h1, rfl⟩
  have hxL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hxQ' : Subgroup.zpowers x ≤ Subgroup.normalizer (Q' : Set Ω) := by
    refine (Subgroup.zpowers_le.2 ?_).trans
      (Subgroup.centralizer_le_normalizer (Q' : Set Ω))
    exact Subgroup.centralizer_le (Subgroup.map_subtype_le Q) hxL
  have hFN : E0 ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (Q' : Set Ω) :=
    sup_le hE0N hxQ'
  have hxE0 : x ∉ E0 := by
    intro hx
    have hxL' : x ∈ L := hE0L hx
    have hxcenter : (⟨x, hxL'⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 hxL (g : Ω) g.2
    have hord : orderOf x = 3 :=
      orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
    have hdvd : 3 ∣ Nat.card (Subgroup.center ↥L) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hxcenter
      rw [Subgroup.orderOf_mk, hord] at h
      exact h
    exact hnoZ hdvd
  have hcomm : ∀ a ∈ E0, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    rintro _ ⟨r, -, rfl⟩ _ hb
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.zpowers_le.2 hxL hb) (r : Ω) r.2
  have hxel : IsElemAbelian 3 (Subgroup.zpowers x) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a rfl b rfl; rfl
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hcfg.elem.2 x hcfg.mem
  have hinf : E0 ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha0, hax⟩
    rw [Subgroup.mem_bot]
    have haL : a ∈ L := hE0L ha0
    have haC : a ∈ Subgroup.centralizer (L : Set Ω) := (Subgroup.zpowers_le.2 hxL) hax
    have hacenter : (⟨a, haL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 haC (g : Ω) g.2
    have ha3 : a ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hax
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hcfg.elem.2 x hcfg.mem, one_zpow]
    have hord : orderOf (⟨a, haL⟩ : ↥L) ∣ 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one ha3
    have hzc : orderOf (⟨a, haL⟩ : ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hacenter
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnoZ
    have h1 : orderOf (⟨a, haL⟩ : ↥L) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hzc
    exact Subtype.ext_iff.1 (orderOf_eq_one_iff.1 h1)
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (E0 : Set Ω) := by
    refine (Subgroup.zpowers_le.2 ?_).trans
      (Subgroup.centralizer_le_normalizer (E0 : Set Ω))
    refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    exact hcomm a ha x (Subgroup.mem_zpowers x)
  have hFcard : Nat.card (E0 ⊔ Subgroup.zpowers x : Subgroup Ω) = 3 * Nat.card E := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (E0 : Subgroup Ω) (Subgroup.zpowers x : Subgroup Ω) hnorm
      (disjoint_iff.mpr hinf)]
    rw [Nat.card_zpowers, orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one,
      hE0card]
    ring
  have hFel : IsElemAbelian 3 (E0 ⊔ Subgroup.zpowers x : Subgroup Ω) :=
    hE0el.sup_of_commute hxel hcomm
  have hle := hmax _ Q' hFel hQ'2 hQ'1 hFN
  rw [hFcard] at hle
  have hle' : 3 * Nat.card E ≤ 3 * Nat.card M.β.range := by
    calc 3 * Nat.card E ≤ Nat.card B := hle
      _ = 3 * Nat.card M.β.range := hBcard.symm
  exact Nat.le_of_mul_le_mul_left hle' (by norm_num)

theorem inf_centralizer_eq_zpowers_of_cfg171 {Ω : Type} [Group Ω] [Finite Ω]
    {B L : Subgroup Ω} {x : Ω}
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L) {D' : Subgroup Ω}
    (hD'B : D' ≤ B) (hxD' : x ∈ D') :
    D' ⊓ Subgroup.centralizer (L : Set Ω) = Subgroup.zpowers x := by
  apply le_antisymm
  · intro b hb
    exact (hcfg.cent b (hD'B hb.1)).1 hb.2
  · rw [le_inf_iff]
    exact ⟨Subgroup.zpowers_le.2 hxD',
      Subgroup.zpowers_le.2 ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x))⟩

namespace S172Model

variable {Ω : Type} [Group Ω] [Finite Ω] {B L : Subgroup Ω}
variable {G₀ : Type} [Group G₀] [Finite G₀]

theorem card_img_eq_prime171 (M : S172Model L B G₀) {x : Ω}
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L) {D' : Subgroup Ω}
    (hD'B : D' ≤ B) (hxD' : x ∈ D') (hcard : Nat.card D' = 3 ^ 2) :
    Nat.card (M.img D') = 3 := by
  have hp := hcfg.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have h1 := M.card_img_mul_card_inf hD'B
  rw [inf_centralizer_eq_zpowers_of_cfg171 hcfg hD'B hxD', Nat.card_zpowers,
    orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one, hcard] at h1
  have h1' : Nat.card (M.img D') * 3 = 3 * 3 := by
    rw [pow_two] at h1
    exact h1
  omega

theorem exists_isE2_img_eq171 (M : S172Model L B G₀) {x : Ω}
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    {y : G₀} (hy : y ∈ M.β.range) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) :
    ∃ D₁ : Subgroup Ω, D₁ ≤ B ∧ (∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set Ω) → b ∈ D₁) ∧
      M.img D₁ = Subgroup.zpowers y ∧ IsElemAbelian 3 D₁ ∧ Nat.card D₁ = 3 ^ 2 ∧ x ∈ D₁ := by
  have hp := hcfg.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hyr : Subgroup.zpowers y ≤ M.β.range := Subgroup.zpowers_le.2 hy
  have hxD₁ : x ∈ M.preimg (Subgroup.zpowers y) :=
    M.centralizer_le_preimg _ x hcfg.mem ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x))
  refine ⟨M.preimg (Subgroup.zpowers y), M.preimg_le _, M.centralizer_le_preimg _,
    M.img_preimg hyr, hcfg.elem.mono (M.preimg_le _), ?_, hxD₁⟩
  have h1 := M.card_img_mul_card_inf (M.preimg_le (Subgroup.zpowers y))
  rw [M.img_preimg hyr, inf_centralizer_eq_zpowers_of_cfg171 hcfg (M.preimg_le _) hxD₁,
    Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy3 hy1,
    orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one] at h1
  rw [← h1]
  ring

end S172Model

theorem smallOrd_of_glaSmall {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (h : GLASmall K) : HStdExcl.SmallOrd K := by
  rcases h with hU | hA
  · left
    have hsimple : IsSimpleGroup ↥K := isSimpleGroup_of_isU42 hU
    have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
      by_contra h
      push_neg at h
      haveI : IsMulCommutative ↥K := ⟨⟨fun a b => h a b⟩⟩
      have hp := IsSimpleGroup.prime_card (α := ↥K)
      have hcard := CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU
      rw [hcard] at hp
      norm_num at hp
    have hcenter : Subgroup.center ↥K = ⊥ :=
      CFSG.GorensteinWalter.Helpers.center_eq_bot_of_noncommutative hnc
    rw [hcenter, Nat.card_congr QuotientGroup.quotientBot.toEquiv,
      CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU]
  · obtain ⟨e⟩ := hA
    right
    exact CFSG.ComponentClassification.CatFC.card_quotient_center_alt6 e

theorem smallOrd_central_map {Ω G : Type} [Group Ω] [Finite Ω] [Group G] [Finite G]
    {Src : Subgroup Ω} (φ : ↥Src →* G)
    (hperf : Group.IsPerfect ↥Src) (hker : φ.ker ≤ Subgroup.center ↥Src)
    (h : HStdExcl.SmallOrd Src) : HStdExcl.SmallOrd φ.range := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central
    φ.rangeRestrict φ.rangeRestrict_surjective hperf (by
      intro x hx
      exact hker (by simpa using hx))
  unfold HStdExcl.SmallOrd at h ⊢
  rwa [← Nat.card_congr e.toEquiv]

theorem exists_stdAt171 {Ω : Type} [Group Ω] [Finite Ω] {B L : Subgroup Ω}
    {G₀ : Type} [Group G₀] [Finite G₀] (M : S172Model L B G₀) {D K : Subgroup Ω} {x : Ω}
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hstd : GLAStdSubPre 3 B x L D K) :
    ∃ d ∈ M.β.range, d ≠ 1 ∧ StdAt M.β.range d := by
  have hp := hcfg.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hDB, hDe, hDc, hxmem, hKeq, hKc, hDK⟩ := hstd
  obtain ⟨d, hd⟩ := exists_zpowers_eq_of_card_eq_prime (p := 3)
    (S172Model.card_img_eq_prime171 M hcfg hDB hxmem hDc)
  have hdr : d ∈ M.β.range := M.img_le_range D (hd ▸ Subgroup.mem_zpowers d)
  have hKc' : IsComponentOf (GLALayer (L ⊓ cs D)) (L ⊓ cs D) := by
    rw [← hKeq]
    exact hKc
  have hcenteq : Subgroup.centralizer (M.img D : Set G₀) = Subgroup.centralizer ({d} : Set G₀) := by
    rw [← hd, centralizer_zpowers_eq]
  have hd1 : d ≠ 1 := by
    intro hd1
    have hc := S172Model.card_img_eq_prime171 M hcfg hDB hxmem hDc
    rw [← hd, hd1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc
    norm_num at hc
  refine ⟨d, hdr, hd1, ?_, ?_⟩
  · rw [← hcenteq]
    exact (M.isComponentOf_glaLayer_centralizer_img_iff hDB).2
      ((isComponentOf_glaLayer_csIn_iff L D).2 hKc')
  · rw [← hcenteq, ← M.img_cs_glaLayer hDB hKc', ← hKeq, ← M.img_inf_left, ← hDK, ← hd]

theorem modelRed_holds : ModelRed := by
  intro Ω _ _ B x L hK hcfg hLn hmax hex hsmall hT G₀ _ _ hAut hθ hnoZ
  classical
  haveI := hLn
  obtain ⟨D, K, hstd⟩ := hex
  obtain ⟨θ⟩ := hθ
  obtain ⟨T, hTN, hTx, hT2, hBT, hTne⟩ := hT
  have hBin := mem_sup_centralizer_of_autThreePowInner hLn hcfg.qs hcfg.elem hAut θ
  obtain ⟨M⟩ := S172Model.nonempty_of_mem_sup hLn hBin θ
  have hxL : L ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 ((hcfg.cent x hcfg.mem).2
      (Subgroup.mem_zpowers x)) l hl)
  have hdir : IsDirectZpowersInf B x L :=
    isDirectZpowersInf_of_le_sup_centralizer hLn hcfg.elem hcfg.mem hcfg.ne_one hxL hBin
      hcfg.cent hnoZ hcfg.cyc
  have hker := M.card_ker_β hcfg.prime hcfg.elem hcfg.mem hcfg.ne_one hcfg.cent
  have hBcard := Subgroup.card_ker_mul_card_range M.β
  rw [hker] at hBcard
  have hElem : IsElemAbelian 3 M.β.range := M.isElemAbelian_range_β hcfg.elem
  have hTwo : TwoLocal M.β.range :=
    twoLocal_range M hcfg.elem hcfg.mem hcfg.ne_one hTx hTN hT2 hBT hTne hdir
  have hMax : ∀ E : Subgroup G₀, IsElemAbelian 3 E → TwoLocal E →
      Nat.card E ≤ Nat.card M.β.range :=
    max_field M hcfg hLn hnoZ hmax
  obtain ⟨d, hdB, hd1, hStdAt⟩ := exists_stdAt171 M hcfg hstd
  have hSmall : ∀ y ∈ M.β.range, y ≠ 1 → StdAt M.β.range y →
      HStdExcl.SmallOrd (GLALayer (Subgroup.centralizer ({y} : Set G₀))) := by
    intro y hy hy1 hyStd
    have hy3 : y ^ 3 = 1 := hElem.2 y hy
    obtain ⟨D₁, hD₁B, hD₁cent, hD₁img, hD₁el, hD₁card, hxD₁⟩ :=
      S172Model.exists_isE2_img_eq171 M hcfg hy hy1 hy3
    let K₁ : Subgroup Ω := GLALayer (L ⊓ cs D₁)
    have hK₁comp : IsComponentOf K₁ (L ⊓ cs D₁) := by
      have hc : IsComponentOf (GLALayer (csIn L D₁)) (csIn L D₁) :=
        (M.isComponentOf_glaLayer_centralizer_img_iff hD₁B).1 (by
          rw [hD₁img, centralizer_zpowers_eq]
          exact hyStd.1)
      exact (isComponentOf_glaLayer_csIn_iff L D₁).1 hc
    have hK₁L : K₁ ≤ L := hK₁comp.1.trans inf_le_left
    have hcentY : Subgroup.centralizer (M.img D₁ : Set G₀) =
        Subgroup.centralizer ({y} : Set G₀) := by
      rw [hD₁img, centralizer_zpowers_eq]
    have hD₁K : D₁ = B ⊓ cs K₁ := by
      refine M.eq_inf_of_img_eq hD₁B hD₁cent
        (fun b _ hbc => Subgroup.centralizer_le (fun a ha => hK₁L ha) hbc) ?_
      rw [M.img_cs_glaLayer hD₁B hK₁comp, hcentY, hyStd.2, hD₁img]
    have hstd₁ : GLAStdSubPre 3 B x L D₁ K₁ :=
      ⟨hD₁B, hD₁el, hD₁card, hxD₁, rfl, hK₁comp, hD₁K⟩
    have hsmallK₁ : GLASmall K₁ := hsmall D₁ K₁ hstd₁
    have hSoK₁ : HStdExcl.SmallOrd K₁ := smallOrd_of_glaSmall hsmallK₁
    let φ : ↥K₁ →* G₀ := M.π.comp (Subgroup.inclusion hK₁L)
    have hperf : Group.IsPerfect ↥K₁ := ⟨hK₁comp.2.2.1⟩
    have hφker : φ.ker ≤ Subgroup.center ↥K₁ := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hzL : (z : Ω) ∈ L := hK₁L z.2
      have hzpi : M.π (⟨(z : Ω), hzL⟩ : ↥L) = 1 := by
        have h := hz
        rw [MonoidHom.mem_ker] at h
        exact h
      have hzc : (⟨(z : Ω), hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [← M.ker_π]
        exact hzpi
      have hwL : (w : Ω) ∈ L := hK₁L w.2
      have hcomm := Subgroup.mem_center_iff.1 hzc (⟨(w : Ω), hwL⟩ : ↥L)
      simpa using congrArg Subtype.val hcomm
    have hSoφ : HStdExcl.SmallOrd φ.range :=
      smallOrd_central_map φ hperf hφker hSoK₁
    let K₀ : Subgroup ↥L := GLALayer (csIn L D₁)
    have hK₁eq : K₁ = K₀.map L.subtype := by
      dsimp [K₁, K₀]
      exact (glaLayer_csIn_map L D₁).symm
    have hK₀map : GLALayer (Subgroup.centralizer ({y} : Set G₀)) = K₀.map M.π := by
      rw [← hcentY]
      exact M.glaLayer_centralizer_img hD₁B
    have hrange' : φ.range = K₀.map M.π := by
      ext g
      constructor
      · rintro ⟨z, rfl⟩
        have hzmem : (z : Ω) ∈ K₀.map L.subtype := by
          rw [← hK₁eq]
          exact z.2
        obtain ⟨k0, hk0, hzk⟩ := Subgroup.mem_map.1 hzmem
        refine Subgroup.mem_map.2 ⟨k0, hk0, ?_⟩
        change (M.π k0 : G₀) = M.π ⟨(z : Ω), hK₁L z.2⟩
        congr 1
        apply Subtype.ext
        exact hzk
      · rintro ⟨k0, hk0, rfl⟩
        refine ⟨⟨L.subtype k0, ?_⟩, ?_⟩
        · rw [hK₁eq]
          exact Subgroup.mem_map.2 ⟨k0, hk0, rfl⟩
        · rfl
    have hrange : φ.range = GLALayer (Subgroup.centralizer ({y} : Set G₀)) := by
      rw [hrange', hK₀map]
    rwa [hrange] at hSoφ
  refine ⟨M.β.range, hElem, ?_, ?_, hTwo, hMax, ⟨d, hdB, hd1, hStdAt⟩, hSmall⟩
  · have h4 := hcfg.card_ge
    rw [← hBcard] at h4
    omega
  · have hBle := bCardLe_holds Ω B x L hcfg ⟨D, K, hstd⟩ hsmall
    rw [← hBcard] at hBle
    omega

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
