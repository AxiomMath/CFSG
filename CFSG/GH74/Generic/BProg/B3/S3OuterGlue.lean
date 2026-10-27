module

public import CFSG.GH74.Generic.BProg.B3.S3FusionI
public import CFSG.GH74.Generic.BProg.B1.Lift1
public import CFSG.GH74.Generic.BProg.B2.TwoA7Geo

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterGlue

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.L5U5 Subgroup S3Fusion

variable {G : Type} [Group G] [Finite G]

theorem piC_pLayerOf_mem {x : G} {K : Subgroup G}
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)) {t : G}
    (ht : t ∈ pLayerOf 2 (centralizer ({x} : Set G))) :
    t ∈ centralizer ({x} : Set G) ∧ ∃ k ∈ S3.imgBar x K,
      ∃ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)),
        piC x t = k * c := by
  set Kb : Subgroup (CentralizerBar x) := S3.imgBar x K with hKb
  set M : Subgroup (CentralizerBar x) := Kb ⊔ centralizer (Kb : Set (CentralizerBar x)) with hM
  have hle : pLayerOf 2 (centralizer ({x} : Set G)) ≤ Pre x M := by
    refine sSup_le fun L hL => ?_
    intro l hl
    have hlC : l ∈ centralizer ({x} : Set G) := hL.1 hl
    refine ⟨hlC, ?_⟩
    have hcomp : IsComponent (S3.imgBar x L) := isComponent_imgBar hL
    have hmem : piC x l ∈ S3.imgBar x L :=
      mem_imgBar.2 ⟨⟨l, hlC⟩, hl, (piC_of_mem x hlC).symm⟩
    obtain ⟨m, hmK, hmc⟩ := hshape.perfect_le hcomp.1.1 _ hmem
    have h1 : piC x l = (piC x l * m⁻¹) * m := by group
    rw [h1]
    exact M.mul_mem (Subgroup.mem_sup_right hmc) (Subgroup.mem_sup_left hmK)
  obtain ⟨htC, htM⟩ := hle ht
  have : Kb.Normal := hshape.normal
  obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.1 htM
  exact ⟨htC, k, hk, c, hc, hkc.symm⟩

theorem exists_invol_lift {x : G} {L : Subgroup G} (hLC : L ≤ centralizer ({x} : Set G))
    {tb : CentralizerBar x}
    (htb : tb ∈ (L.subgroupOf (centralizer ({x} : Set G))).map (proj x)) (ht2 : tb * tb = 1)
    (ht1 : tb ≠ 1) : ∃ t ∈ L, t * t = 1 ∧ t ≠ 1 ∧ piC x t = tb := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀, rfl⟩ := htb
  have ht₀L : (t₀ : G) ∈ L := ht₀
  have ht₀C : (t₀ : G) ∈ centralizer ({x} : Set G) := t₀.2
  have hn0 : orderOf (t₀ : G) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  set t₁ : G := (t₀ : G) ^ m with ht₁
  have hmdvd : m ∣ orderOf (t₀ : G) := ⟨2 ^ a, by rw [hnm, mul_comm]⟩
  have hord : orderOf t₁ = 2 ^ a := by
    rw [ht₁, orderOf_pow_of_dvd hm.pos.ne' hmdvd, hnm, Nat.mul_div_cancel _ hm.pos]
  have ht₁L : t₁ ∈ L := pow_mem ht₀L m
  have ht₁C : t₁ ∈ centralizer ({x} : Set G) := hLC ht₁L
  have hp : IsPGroup 2 ↥(Subgroup.zpowers t₁) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hord])
  have hTC : Subgroup.zpowers t₁ ≤ centralizer ({x} : Set G) := Subgroup.zpowers_le.2 ht₁C
  have hpi : piC x t₁ = proj x t₀ ^ m := by
    rw [ht₁, piC_of_mem x ht₁C]
    exact map_pow (proj x) t₀ m
  have hpow : proj x t₀ ^ m = proj x t₀ := by
    obtain ⟨j, hj⟩ := hm
    rw [hj, pow_succ, pow_mul, sq, ht2, one_pow, one_mul]
  have hpi1 : piC x t₁ = proj x t₀ := hpi.trans hpow
  have hsq : t₁ * t₁ = 1 := by
    refine eq_one_of_piC_eq_one hp hTC (Subgroup.mul_mem _ (Subgroup.mem_zpowers t₁)
      (Subgroup.mem_zpowers t₁)) ?_
    rw [piC_mul x ht₁C ht₁C, hpi1, ht2]
  refine ⟨t₁, ht₁L, hsq, fun h => ht1 ?_, hpi1⟩
  rw [← hpi1, h, piC_one]

@[expose] def Lemma302OuterFact : Prop :=
  ∀ {X : Type} [Group X] [Finite X] {Kb : Subgroup X}, Kb.Normal → IsSimpleGroup ↥Kb → QShape3 ↥Kb →
    ∀ {u : X}, orderOf u = 2 → (∀ k ∈ Kb, ∃ g ∈ Kb, u * g * u⁻¹ ≠ k * g * k⁻¹) →
      ∃ Lb : Subgroup X, IsPCompIn 2 (Kb ⊓ centralizer ({u} : Set X)) Lb ∧
        ∃ t ∈ Lb, orderOf t = 2 ∧ ∃ k ∈ Kb, k * u * k⁻¹ = u * t

theorem outerCaseFusion_of_fact (hfact : Lemma302OuterFact) {x : G} {K : Subgroup G}
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)) (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) {y : G} (hyK : y ∈ K) (hy : orderOf y = 2) :
    OuterCaseFusion x K y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u huC hu2 hune hconj hout
  obtain ⟨g, hg⟩ := hconj
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  set Kb : Subgroup (CentralizerBar x) := S3.imgBar x K with hKbdef
  have hu1 : u ≠ 1 := by
    intro h
    have hx1 : x = 1 := by
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e, hg, h]
      group
    rw [hx1, orderOf_one] at hx
    omega
  have huord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  set ub : CentralizerBar x := piC x u with hub
  have hub2 : ub * ub = 1 := by rw [hub, ← piC_mul x huC huC, hu2, piC_one]
  have hub1 : ub ≠ 1 := fun h => hu1 (eq_one_of_piC_eq_one (isPGroup_zpowers_of_involution hu2)
    (Subgroup.zpowers_le.2 huC) (Subgroup.mem_zpowers u) h)
  have hubord : orderOf ub = 2 := orderOf_eq_prime (by rw [sq]; exact hub2) hub1
  have hout' : ∀ k ∈ Kb, ∃ g ∈ Kb, ub * g * ub⁻¹ ≠ k * g * k⁻¹ := by
    intro k hk
    by_contra hcon
    push Not at hcon
    apply hout
    refine ⟨k, hk, k⁻¹ * ub, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := hcon h hh
    calc h * (k⁻¹ * ub) = k⁻¹ * (k * h * k⁻¹) * ub := by group
      _ = k⁻¹ * (ub * h * ub⁻¹) * ub := by rw [h1]
      _ = (k⁻¹ * ub) * h := by group
  have hnorm : Kb.Normal := hshape.normal
  have hsimple : IsSimpleGroup ↥Kb := by
    have e : (↥Kb ⧸ center ↥Kb) ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq hshape.centerless).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).mp hshape.quasi.2.1
  have h3 : QShape3 ↥Kb := by
    obtain ⟨t, p, f, ht, hp, hp2, h5, hm⟩ := hshape.model
    refine ⟨p, f, hp, hp2, by omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm
  obtain ⟨Lb, hLb, tb, htbL, htb2, kb, hkbK, hkb⟩ := hfact hnorm hsimple h3 hubord hout'
  have htb2' : tb * tb = 1 := by
    have := pow_orderOf_eq_one tb
    rwa [htb2, pow_two] at this
  have htb1 : tb ≠ 1 := fun h => by
    rw [h, orderOf_one] at htb2
    omega
  have hxu : x * u = u * x := (mem_centralizer_singleton_iff.mp huC).symm
  have hbar : bar x u = ub := (bar_of_mem huC).trans (piC_of_mem x huC).symm
  have hLb' :
      IsPCompIn 2 (centralizer ({bar x u} : Set (CentralizerBar x)) ⊓ S3.imgBar x K) Lb := by
    rw [hbar, inf_comm]
    exact hLb
  obtain ⟨hLcomp, hLmap⟩ := B1.isPCompIn_liftAt hxu huord hK hLb'
  set Lg : Subgroup G := liftAt x u Lb with hLg
  have hLgY : Lg ≤ centralizer ((closure ({x, u} : Set G) : Subgroup G) : Set G) := hLcomp.1
  have hLgC : Lg ≤ centralizer ({x} : Set G) := hLgY.trans (B1.centralizer_closure_pair_le_left x u)
  obtain ⟨t, htL, ht2, ht1, hpit⟩ := exists_invol_lift hLgC (by rw [hLmap]; exact htbL) htb2' htb1
  have hxcl : x ∈ (closure ({x, u} : Set G) : Subgroup G) := Subgroup.subset_closure (by simp)
  have hucl : u ∈ (closure ({x, u} : Set G) : Subgroup G) := Subgroup.subset_closure (by simp)
  have htY := Subgroup.mem_centralizer_iff.1 (hLgY htL)
  have hxt : x * t = t * x := htY x hxcl
  have hut : u * t = t * u := htY u hucl
  have htC : t ∈ centralizer ({x} : Set G) := hLgC htL
  have hbal : Lg ≤ pLayerOf 2 (centralizer ({u} : Set G)) := by
    refine (le_sSup hLcomp : Lg ≤ pLayerOf 2 _).trans ?_
    have h1 : centralizer ((closure ({x, u} : Set G) : Subgroup G) : Set G) =
        centralizer ({u} : Set G) ⊓ centralizer ((zpowers x : Subgroup G) : Set G) := by
      rw [B1.centralizer_closure_pair, inf_comm, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure]
    rw [h1]
    exact B2.SD.TwoA7Geo.pLayerOf_inf_centralizer_le_two
      (Subgroup.zpowers_le.2 (mem_centralizer_singleton_iff.mpr hxu))
      (isPGroup_zpowers_of_involution hx2)
  have htlay : t ∈ pLayerOf 2 (centralizer ({u} : Set G)) := hbal htL
  set t' : G := g⁻¹ * t * g with ht'
  have hcen : centralizer ({u} : Set G) = Stage1.Thm3.Sec4.cmap g (centralizer ({x} : Set G)) := by
    rw [← hg]
    exact (Stage1.Thm2.Recip.map_centralizer_singleton_conj x g).symm
  have ht'lay : t' ∈ pLayerOf 2 (centralizer ({x} : Set G)) := by
    have : t ∈ Stage1.Thm3.Sec4.cmap g (pLayerOf 2 (centralizer ({x} : Set G))) := by
      rw [← Stage1.Thm3.Sec4.pLayerOf_cmap, ← hcen]
      exact htlay
    exact Stage1.Thm3.Sec4.mem_cmap.1 this
  obtain ⟨ht'C, k₁, hk₁, c₁, hc₁, hpit'⟩ := piC_pLayerOf_mem hshape ht'lay
  have ht'2 : t' * t' = 1 := by
    calc t' * t' = g⁻¹ * (t * t) * g := by rw [ht']; group
      _ = 1 := by rw [ht2]; group
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    have e : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [e, ← ht', h]
    group
  obtain ⟨κ, hκK, hκ⟩ := mem_imgBar.1 hkbK
  have hκC : (κ : G) ∈ centralizer ({x} : Set G) := κ.2
  have hvC : (κ : G) * u * (κ : G)⁻¹ ∈ centralizer ({x} : Set G) :=
    ((centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hκC huC)
      ((centralizer ({x} : Set G)).inv_mem hκC))
  have hv2 : ((κ : G) * u * (κ : G)⁻¹) * ((κ : G) * u * (κ : G)⁻¹) = 1 := by
    calc ((κ : G) * u * (κ : G)⁻¹) * ((κ : G) * u * (κ : G)⁻¹) = (κ : G) * (u * u) * (κ : G)⁻¹ := by
          group
      _ = 1 := by rw [hu2]; group
  have hwC : u * t ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).mul_mem huC htC
  have hw2 : (u * t) * (u * t) = 1 := by
    calc (u * t) * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [← hut]
      _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [hu2, ht2]; group
  have hpiκ : piC x (κ : G) = kb := by rw [piC_of_mem x hκC]; exact hκ
  have hpiv : piC x ((κ : G) * u * (κ : G)⁻¹) = ub * tb := by
    rw [piC_conj x hκC huC, hpiκ, ← hkb]
  have hpiw : piC x (u * t) = ub * tb := by rw [piC_mul x huC htC, hpit]
  obtain ⟨r, hrC, hr⟩ := exists_conj_of_piC_eq hvC hwC hv2 hw2 (hpiv.trans hpiw.symm)
  have hxt' : ∃ g₂ : G, g₂ * x * g₂⁻¹ = x * t' := by
    refine ⟨g⁻¹ * (r * (κ : G) * g), ?_⟩
    have h1 : r * (κ : G) * g * x * (r * (κ : G) * g)⁻¹ = u * t := by
      calc r * (κ : G) * g * x * (r * (κ : G) * g)⁻¹
          = r * ((κ : G) * (g * x * g⁻¹) * (κ : G)⁻¹) * r⁻¹ := by group
        _ = u * t := by rw [hg]; exact hr
    calc g⁻¹ * (r * (κ : G) * g) * x * (g⁻¹ * (r * (κ : G) * g))⁻¹
        = g⁻¹ * (r * (κ : G) * g * x * (r * (κ : G) * g)⁻¹) * g := by group
      _ = g⁻¹ * (u * t) * g := by rw [h1]
      _ = (g⁻¹ * u * g) * t' := by rw [ht']; group
      _ = x * t' := by
        have : g⁻¹ * u * g = x := by rw [← hg]; group
        rw [this]
  have hxt'C : x * t' ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).mul_mem hxC ht'C
  have hxt'comm : x * t' = t' * x := (mem_centralizer_singleton_iff.mp ht'C).symm
  have hxt'2 : (x * t') * (x * t') = 1 := by
    calc (x * t') * (x * t') = x * (t' * x) * t' := by group
      _ = x * (x * t') * t' := by rw [← hxt'comm]
      _ = (x * x) * (t' * t') := by group
      _ = 1 := by rw [hx2, ht'2]; group
  have hxt'ne : x * t' ≠ x := fun h => ht'1 (by simpa using h)
  have hin : ∃ k ∈ S3.imgBar x K, ∃ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)), piC x (x * t') = k * c := by
    refine ⟨k₁, hk₁, xbar x * c₁, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 := Subgroup.mem_centralizer_iff.1 hc₁ h hh
      calc h * (xbar x * c₁) = xbar x * (h * c₁) := by rw [← mul_assoc, hshape.xh_cent h, mul_assoc]
        _ = xbar x * (c₁ * h) := by rw [h1]
        _ = (xbar x * c₁) * h := by rw [mul_assoc]
    · rw [piC_mul x hxC ht'C, hpit', piC_x, ← mul_assoc, ← hshape.xh_cent k₁, mul_assoc]
  exact fusion_of_inner hshape hx (hK.1 hyK) hyK hy hxt'C hxt'2 hxt'ne hxt' hin

end S3OuterGlue

end CFSG.GH74.Generic.BProg.B3
