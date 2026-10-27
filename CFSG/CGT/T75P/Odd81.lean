module

public import CFSG.CGT.T75P.Final81
public import CFSG.CGT.T75P.Inputs

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75Q CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem Std81.exists_classD_not_mem (s : Std81 T T₁) {Y : Subgroup G} (hY : Y ≠ ⊤) :
    ∃ x ∈ classD T, x ∉ Y := by
  classical
  have hsimple : IsSimpleGroup G := s.hc.hy.simple
  by_contra hcon
  push Not at hcon
  apply hY
  have hle : Subgroup.normalClosure (T : Set G) ≤ Y := by
    refine (Subgroup.closure_le _).2 ?_
    intro a ha
    obtain ⟨b, hb, hab⟩ := Group.mem_conjugatesOfSet_iff.1 ha
    obtain ⟨g, hg⟩ := isConj_iff.1 hab
    by_cases hb1 : b = 1
    · rw [← hg, hb1]
      simp
    · have := classD_conj (mem_classD_of_mem hb hb1) g⁻¹
      have e : g⁻¹⁻¹ * b * g⁻¹ = a := by rw [← hg]; group
      rw [e] at this
      exact hcon a this
  have hne : Subgroup.normalClosure (T : Set G) ≠ ⊥ := by
    intro h
    obtain ⟨t, ht, ht1⟩ := s.exists_ne_one
    apply ht1
    have : t ∈ Subgroup.normalClosure (T : Set G) := Subgroup.le_normalClosure ht
    rw [h, Subgroup.mem_bot] at this
    exact this
  have htop : Subgroup.normalClosure (T : Set G) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
  rw [eq_top_iff, ← htop]
  exact hle

theorem Std81.exists_S₁ (s : Std81 T T₁) (hInd : SimpleCaseUpTo (Nat.card G))
    (h215 : Lemma215Stmt) (hL : ListWCIdentification) {c₁ : G}
    (hc₁C : c₁ ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) (hc₁2 : c₁ * c₁ = 1)
    (hc₁1 : c₁ ≠ 1)
    (hmax : ∀ c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G), c * c = 1 → c ≠ 1 →
      Nat.card (Yc T c) ≤ Nat.card (Yc T c₁)) :
    ∃ S₁ : Subgroup G, S₁ ≤ Subgroup.centralizer (Yc T c₁ : Set G) ∧ IsPGroup 2 S₁ ∧
      ¬ 2 ∣ (S₁.subgroupOf (Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))).index ∧
      S₁ ≠ ⊥ := by
  classical
  have hfin : Finite G := s.finite
  have hsimple : IsSimpleGroup G := s.hc.hy.simple
  set C : Subgroup G := Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) with hCdef
  set Y : Subgroup G := Yc T c₁ with hYdef
  have hY : GoodY T Y := s.goodY_Yc hc₁C hc₁1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 ((Subgroup.zpowers c₁).subgroupOf C) := by
    intro q
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 q.2)
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    show ((q : ↥C) : G) ^ 2 ^ 1 = 1
    have hqj : ((q : ↥C) : G) = c₁ ^ j := hj.symm
    rw [hqj, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : c₁ ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact hc₁2
    rw [Nat.cast_ofNat, this, one_zpow]
  obtain ⟨𝒮, h𝒮⟩ := hQ2.exists_le_sylow
  set S₁ : Subgroup G := (𝒮 : Subgroup ↥C).map C.subtype with hS₁def
  have hS₁C : S₁ ≤ C := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hS₁2 : IsPGroup 2 S₁ := by
    intro x
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_map.1 x.2)
    obtain ⟨n, hn⟩ := 𝒮.isPGroup' ⟨y, hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(𝒮 : Subgroup ↥C) => (((z : ↥C)) : G)) hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [← hyx]
    exact this
  have hS₁sub : S₁.subgroupOf C = (𝒮 : Subgroup ↥C) :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hc₁S : c₁ ∈ S₁ :=
    ⟨⟨c₁, hc₁C⟩, h𝒮 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers c₁)), rfl⟩
  have hc₁B : c₁ ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Yc_comm hy).symm
  refine ⟨S₁, ?_, hS₁2, ?_, ?_⟩
  · rcases s.type_dich hInd h215 hL hY with hYU | hnine
    · intro x hx
      have hxC : x ∈ Subgroup.centralizer (ugen T : Set G) := s.centralizer_eq ▸ hS₁C hx
      rwa [hYU]
    · obtain ⟨e⟩ := hnine
      by_contra hS₁B
      set B : Subgroup G := Subgroup.centralizer (Y : Set G) with hBdef
      have hY_le : ∀ c' ∈ B, Y ≤ Yc T c' := by
        intro c' hc'
        refine (Subgroup.closure_le _).2 ?_
        rintro f ⟨hfD, hfc⟩
        exact subset_Yc hfD (Subgroup.mem_centralizer_iff.1 hc' f (subset_Yc hfD hfc)).symm
      let Q' : Subgroup ↥S₁ := (S₁ ⊓ B).subgroupOf S₁
      have hQ'lt : Q' < ⊤ := by
        refine lt_top_iff_ne_top.2 fun h => hS₁B ?_
        intro x hx
        have : (⟨x, hx⟩ : ↥S₁) ∈ Q' := by rw [h]; trivial
        exact (Subgroup.mem_subgroupOf.1 this).2
      have hnil : Group.IsNilpotent ↥S₁ := hS₁2.isNilpotent
      have hlt : Q' < Subgroup.normalizer (Q' : Set ↥S₁) :=
        Group.normalizerCondition_of_isNilpotent Q' hQ'lt
      obtain ⟨n, hn, hnQ'⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hlt).2
      have hnS : (n : G) ∈ S₁ := n.2
      have hnB : (n : G) ∉ B := fun hnB => hnQ' (Subgroup.mem_subgroupOf.2 ⟨hnS, hnB⟩)
      have hnorm : ∀ q ∈ S₁ ⊓ B, (n : G) * q * (n : G)⁻¹ ∈ S₁ ⊓ B := by
        intro q hq
        have hqQ' : (⟨q, hq.1⟩ : ↥S₁) ∈ Q' := Subgroup.mem_subgroupOf.2 hq
        have := ((Subgroup.mem_normalizer_iff.1 hn) ⟨q, hq.1⟩).1 hqQ'
        exact Subgroup.mem_subgroupOf.1 this
      have hc'mem : (n : G) * c₁ * (n : G)⁻¹ ∈ S₁ ⊓ B := hnorm c₁ ⟨hc₁S, hc₁B⟩
      have hc'B : (n : G) * c₁ * (n : G)⁻¹ ∈ B := hc'mem.2
      have hc'C : (n : G) * c₁ * (n : G)⁻¹ ∈ C := hS₁C hc'mem.1
      have hc'2 : ((n : G) * c₁ * (n : G)⁻¹) * ((n : G) * c₁ * (n : G)⁻¹) = 1 := by
        calc ((n : G) * c₁ * (n : G)⁻¹) * ((n : G) * c₁ * (n : G)⁻¹)
            = (n : G) * (c₁ * c₁) * (n : G)⁻¹ := by group
          _ = 1 := by rw [hc₁2]; group
      have hc'1 : (n : G) * c₁ * (n : G)⁻¹ ≠ 1 := by
        intro h
        apply hc₁1
        calc c₁ = (n : G)⁻¹ * ((n : G) * c₁ * (n : G)⁻¹) * (n : G) := by group
          _ = 1 := by rw [h]; group
      have hcard := hmax _ hc'C hc'2 hc'1
      have heq : Y = Yc T ((n : G) * c₁ * (n : G)⁻¹) :=
        Subgroup.eq_of_le_of_card_ge (hY_le _ hc'B) hcard
      have hle2 : Yc T ((n : G) * c₁ * (n : G)⁻¹) ≤ conjSubgroup (n : G) Y :=
        Yc_conj_le (n : G) c₁
      have hYconj : Y ≤ conjSubgroup (n : G) Y := heq.le.trans hle2
      have heq2 : Y = conjSubgroup (n : G) Y :=
        Subgroup.eq_of_le_of_card_ge hYconj (by rw [card_conjSubgroup])
      have hsN : (n : G) ∈ Subgroup.normalizer (Y : Set G) :=
        mem_normalizer_of_conjSubgroup_eq heq2.symm
      have hcent := s.centralizes_of_normalizes hY.ugen_le hY.gen e (hS₁C hnS) hsN
      exact hnB (Subgroup.mem_centralizer_iff.2 fun y hy => (hcent y hy).symm)
  · rw [hS₁sub]
    exact 𝒮.not_dvd_index
  · intro h
    have : c₁ ∈ (⊥ : Subgroup G) := h ▸ hc₁S
    exact hc₁1 (Subgroup.mem_bot.1 this)

theorem Std81.false_of_even (s : Std81 T T₁) (hInd : SimpleCaseUpTo (Nat.card G))
    (h215 : Lemma215Stmt) (hL : ListWCIdentification)
    (hev : 2 ∣ Nat.card ↥(Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))) : False := by
  classical
  have hfin : Finite G := s.finite
  have hsimple : IsSimpleGroup G := s.hc.hy.simple
  have hna := s.hc.hy.nonab
  have hWC := s.hc.hy.pair.wc
  set C : Subgroup G := Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) with hCdef
  have hHU : hSub T (normIn T₁ T) ≤ ugen T := hSub_le_ugen s.hc (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 hev
  have hc₀2 : ((c₀ : ↥C) : G) * ((c₀ : ↥C) : G) = 1 := by
    have : c₀ ^ 2 = 1 := by rw [← hc₀]; exact pow_orderOf_eq_one c₀
    have h := congrArg (fun z : ↥C => (z : G)) this
    simpa [pow_two] using h
  have hc₀1 : ((c₀ : ↥C) : G) ≠ 1 := by
    intro h
    have : c₀ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hc₀
    omega
  let 𝒳 : Set G := {c | c ∈ C ∧ c * c = 1 ∧ c ≠ 1}
  obtain ⟨c₁, hc₁X, hmax⟩ := Set.exists_max_image 𝒳 (fun c => Nat.card (Yc T c)) (Set.toFinite _)
    ⟨(c₀ : G), c₀.2, hc₀2, hc₀1⟩
  obtain ⟨hc₁C, hc₁2, hc₁1⟩ := hc₁X
  have hmax' : ∀ c ∈ C, c * c = 1 → c ≠ 1 → Nat.card (Yc T c) ≤ Nat.card (Yc T c₁) :=
    fun c hc hc2 hc1 => hmax c ⟨hc, hc2, hc1⟩
  set Y : Subgroup G := Yc T c₁ with hYdef
  have hY : GoodY T Y := s.goodY_Yc hc₁C hc₁1
  have hHY : hSub T (normIn T₁ T) ≤ Y := hHU.trans hY.ugen_le
  have hF1 : ∀ c ∈ Subgroup.centralizer (Y : Set G), c ≠ 1 → c * c = 1 →
      ∀ d ∈ classD T, c * d = d * c → d ∈ Y := by
    intro c hcY hc1 hc2 d hd hcd
    have hcC : c ∈ C := Subgroup.centralizer_le hHY hcY
    have hYle : Y ≤ Yc T c := by
      refine (Subgroup.closure_le _).2 ?_
      rintro f ⟨hfD, hfc⟩
      exact subset_Yc hfD (Subgroup.mem_centralizer_iff.1 hcY f (subset_Yc hfD hfc)).symm
    have heq : Y = Yc T c := Subgroup.eq_of_le_of_card_ge hYle (hmax' c hcC hc2 hc1)
    rw [heq]
    exact subset_Yc hd hcd
  have hCU : ∀ c ∈ C, c ∈ ugen T → ∀ u ∈ ugen T, c * u = u * c := by
    intro c hc _ u hu
    have : c ∈ Subgroup.centralizer (ugen T : Set G) := s.centralizer_eq ▸ hc
    exact (Subgroup.mem_centralizer_iff.1 this u hu).symm
  have hZ : ∀ c ∈ Y ⊓ Subgroup.centralizer (Y : Set G), c * c = 1 → c = 1 := by
    refine no_involution_of_odd_center (s.Z_odd hY.ugen_le hY.gen ?_)
    intro c hcC hcY u hu
    rcases s.type_dich hInd h215 hL hY with hYU | hnine
    · have : c ∈ Subgroup.centralizer (ugen T : Set G) := s.centralizer_eq ▸ hcC
      exact (Subgroup.mem_centralizer_iff.1 this u (hYU ▸ hu)).symm
    · obtain ⟨e⟩ := hnine
      exact s.centralizes_of_normalizes hY.ugen_le hY.gen e hcC (Subgroup.le_normalizer hcY) u hu
  have hZU : ∀ z ∈ ugen T ⊓ Subgroup.centralizer (ugen T : Set G), z * z = 1 → z = 1 := by
    refine no_involution_of_odd_center (s.Z_odd le_rfl ?_ ?_)
    · rw [ugen]
      refine (Subgroup.closure_le _).2 fun δ hδ => Subgroup.subset_closure ?_
      exact ⟨gammaD_subset_classD hδ, gammaD_subset_ugen hδ⟩
    · intro c hcC hcU u hu
      exact hCU c hcC hcU u hu
  have hD : DihHyp T Y :=
    ⟨hWC, s.h66', fun d hd hdY x hx hxd => s.closed_Yc hc₁C hd hdY hx hxd, hF1, hZ⟩
  obtain ⟨S₁, hS₁B, hS₁2, hS₁odd, hne⟩ := s.exists_S₁ hInd h215 hL hc₁C hc₁2 hc₁1 hmax'
  have hS₁C : S₁ ≤ C := hS₁B.trans (Subgroup.centralizer_le hHY)
  by_cases hrank : ∀ α ∈ S₁, ∀ β ∈ S₁, α * α = 1 → β * β = 1 → α * β = β * α →
      α = 1 ∨ β = 1 ∨ α = β
  · exact rank_one_81 s hna hS₁C hS₁2 hS₁odd hne hrank
  · push Not at hrank
    obtain ⟨α, hα, β, hβ, hα2, hβ2, hαβ, hne1, hne2, hne3⟩ := hrank
    obtain ⟨x, hx, hxY⟩ := s.exists_classD_not_mem hY.ne_top
    exact s.final_step hInd h215 hL hY hD hZU hx hxY (hS₁B hα) (hS₁B hβ) hα2 hβ2 hne1 hne2
      hne3 hαβ

theorem odd81_of_inputs (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (h66 : Sec66)
    (h215 : Lemma215Stmt) (hL : ListWCIdentification) : Odd81 := by
  intro G _ T T₁ hy hq hT hnat
  have hc := sec6Ctx_of_natural h214 hInv hIso hy hq hT hnat
  have s : Std81 T T₁ := ⟨h1, h62, h63, h66, hc, hnat⟩
  rw [relIndex_eq_card_centralizer h62 h63 hc hnat chain3]
  by_contra hodd
  exact s.false_of_even hy.ind h215 hL (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd))

end CFSG.CGT.T75P
