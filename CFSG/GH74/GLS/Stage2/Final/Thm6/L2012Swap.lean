module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Fus1
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Lift
public import CFSG.GH74.GLS.Stage2.Final.M12Odd
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012CBar

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20

section FactN

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem fact_N {k : Kind} (hctx : Stage2Ctx G z k S) (hmax : IsCoatom (Cen z))
    (hne : pPrimeCore 2 ↥(Cen z) ≠ ⊥) {g : G} (hkey : ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z) :
    g * z * g⁻¹ = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := hctx.central.1
  have hconj_le : (OddCore z).map (MulAut.conj g).toMonoidHom ≤ OddCore z := by
    rintro _ ⟨a, ha, rfl⟩
    exact hkey a ha
  have hconj_eq : (OddCore z).map (MulAut.conj g).toMonoidHom = OddCore z := by
    apply Subgroup.eq_of_le_of_card_ge hconj_le
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hgA : g ∈ normalizer ((OddCore z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hkey x hx
    · intro hx
      have : g * x * g⁻¹ ∈ (OddCore z).map (MulAut.conj g).toMonoidHom := by rw [hconj_eq]; exact hx
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        simpa using h1
      rw [← this]
      exact hy
  rcases (hmax.le_iff.1 (Cen_le_normalizer_OddCore z)) with hN | hN
  · exfalso
    have hnorm : (OddCore z).Normal := Subgroup.normalizer_eq_top_iff.1 hN
    rcases (hctx.std.kps.1).eq_bot_or_eq_top_of_normal (OddCore z) with hbot | htop
    · apply hne
      have : (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype = ⊥ := hbot
      exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥(Cen z))
        (Cen z).subtype_injective).1 this
    · have hzA : z ∈ OddCore z := by rw [htop]; exact mem_top z
      have := coprime_orderOf_of_mem_OddCore hzA
      rw [hz2] at this
      exact absurd this (by norm_num)
  · rw [hN] at hgA
    have := Subgroup.mem_centralizer_singleton_iff.1 hgA
    rw [this]
    group

end FactN

section Setup

variable {G : Type} [Group G] [Finite G]

structure FusedSetup (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z))
    (K₁ K₂ U : Subgroup G) (g : G) : Prop where
  ctx : Stage2Ctx G z (Kind.l4 ε) S
  L4 : Stage1L4 G z S ε q L₁ L₂
  comp : CompData z K₁ K₂ L₁ L₂
  q9 : q ≠ 9
  coatom : IsCoatom (Cen z)
  odd_ne : pPrimeCore 2 ↥(Cen z) ≠ ⊥
  US : U ≤ S
  U4 : IVK.IsFourSubgroup U
  Un : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U
  zU : z ∈ U
  gN : g ∈ normalizer (U : Set G)
  gz : g * z * g⁻¹ ≠ z

end Setup

section Swap

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ U : Subgroup G} {g : G}

theorem mem_normalizer_K₁_of_odd (hK : CompData z K₁ K₂ L₁ L₂) {c : G} (hcC : c ∈ Cen z)
    (hodd : Odd (orderOf c)) : c ∈ normalizer (K₁ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcinvC : c⁻¹ ∈ Cen z := (Cen z).inv_mem hcC
  have hcinvodd : Odd (orderOf c⁻¹) := by rwa [orderOf_inv]
  constructor
  · intro hx
    exact (hK.odd_norm c hcC hodd).1 x hx
  · intro hx
    have := (hK.odd_norm c⁻¹ hcinvC hcinvodd).1 _ hx
    simpa [mul_assoc] using this

theorem swap_exists
    (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∃ (e : G) (_ : e ∈ Cen z), (∀ a ∈ K₁, e * a * e⁻¹ ∈ K₂) ∧ (∀ b ∈ K₂, e * b * e⁻¹ ∈ K₁) ∧
      ∀ a ∈ OddCore z, e * (g * a * g⁻¹) = (g * a * g⁻¹) * e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hctx, hL4, hK, hq9, hmax, hne, hUS, hU4, hUn, hzU, hg, hgz⟩ := h
  have hP := hL4.pair
  have hz2' : orderOf z = 2 := hctx.orderOf_z
  have hzz : z * z = 1 := by
    have : z ^ 2 = 1 := by rw [← hz2']; exact pow_orderOf_eq_one z
    simpa [pow_two] using this
  have hz1 : z ≠ 1 := by intro e; rw [e, orderOf_one] at hz2'; omega
  have hSC : S ≤ Cen z := hctx.S_le_Cen
  have hLU : U ≤ LC z := hP.base.four_le U hUS hU4 hUn
  have hUC : U ≤ Cen z := hUS.trans hSC
  have hUsup := U_le_sup hP hK hSC hLU hUS hU4
  have hgU : ∀ u : G, u ∈ U ↔ g * u * g⁻¹ ∈ U := Subgroup.mem_normalizer_iff.1 hg
  have hgU' : ∀ u ∈ U, g⁻¹ * u * g ∈ U := by
    intro u hu
    refine (hgU _).2 ?_
    have : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    rw [this]
    exact hu
  set t : G := g * z * g⁻¹ with ht
  have htU : t ∈ U := (hgU z).1 hzU
  have ht1 : t ≠ 1 := by
    intro h1
    apply hz1
    have h2 : z = g⁻¹ * t * g := by rw [ht]; group
    rw [h2, h1]; group
  have htz : t ≠ z := hgz
  have htt : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [ht]; group
      _ = 1 := by rw [hzz]; group
  obtain ⟨y₀, hy₀sup, hy₀2, hy₀U, hy₀c⟩ := exists_y₀ hP hK hq9 hUsup hU4 hzU htU hz1 ht1 htz
  set e : G := g * y₀ * g⁻¹ with he
  have hee : e * e = 1 := by
    calc e * e = g * (y₀ * y₀) * g⁻¹ := by rw [he]; group
      _ = 1 := by rw [hy₀2]; group
  have hy₀z : y₀ * z = z * y₀ := hy₀c z hzU
  have heC : e ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hy₀c _ (hgU' z hzU)
    calc e * z = g * (y₀ * (g⁻¹ * z * g)) * g⁻¹ := by rw [he]; group
      _ = g * ((g⁻¹ * z * g) * y₀) * g⁻¹ := by rw [h1]
      _ = z * e := by rw [he]; group
  have het : e * t = t * e := by
    calc e * t = g * (y₀ * z) * g⁻¹ := by rw [he, ht]; group
      _ = g * (z * y₀) * g⁻¹ := by rw [hy₀z]
      _ = t * e := by rw [he, ht]; group
  have heU : e ∉ U := fun h' => hy₀U ((hgU y₀).2 h')
  have htC : t ∈ Cen z := hUC htU
  have hzC : z ∈ Cen z := mem_Cen_self z
  set tt : ↥(Cen z) := ⟨t, htC⟩ with htt'
  set ee : ↥(Cen z) := ⟨e, heC⟩ with hee'
  have htt2 : tt * tt = 1 := Subtype.ext htt
  have hee2 : ee * ee = 1 := Subtype.ext hee
  have hete : ee * tt = tt * ee := Subtype.ext het
  have p₁ := pair₁_of_stage1 hP
  have hsup : L₁ ⊔ L₂ = LBar z := hP.prod.1
  have hzbar : toBar z ⟨z, hzC⟩ ∈ L₁ ⊓ L₂ := by
    have hzL : toBar z ⟨z, hzC⟩ ∈ L₁ ⊔ L₂ := by
      rw [hsup]; exact ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr (hLU hzU), rfl⟩
    have hcen : ∀ c : CentralizerBar z, toBar z ⟨z, hzC⟩ * c = c * toBar z ⟨z, hzC⟩ :=
      fun c => ((Subgroup.mem_center_iff.1 (toBar_z_mem_center z)) c).symm
    have h2 : toBar z ⟨z, hzC⟩ ∈ L₂ := p₁.mem_of_cen hzL (fun c _ => hcen c)
    exact ⟨p₁.cen' h2 (fun c _ => (hcen c).symm), h2⟩
  have hzbar1 : toBar z ⟨z, hzC⟩ ≠ 1 := by
    intro h'
    have := eq_one_of_toBar_eq_one z (x := ⟨z, hzC⟩) (Subtype.ext hzz) h'
    exact hz1 (congrArg Subtype.val this)
  have hinfz : ∀ x : ↥(Cen z), x * x = 1 → toBar z x ∈ L₁ ⊓ L₂ → x = 1 ∨ x = ⟨z, hzC⟩ := by
    intro x hx hxI
    refine eq_one_or_eq_z_of_toBar z hzz hx ?_
    rcases p₁.inf_cases hzbar hzbar1 hxI with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  have hAU : ∀ a ∈ OddCore z, ∀ u ∈ U, a * u = u * a := fun a ha u hu =>
    hK.oddcomm a ha u (by rw [hK.layer]; exact hUsup u hu)
  have hAR : ∀ a ∈ OddCore z, a * y₀ = y₀ * a := fun a ha =>
    hK.oddcomm a ha y₀ (by rw [hK.layer]; exact hy₀sup)
  have hcommU : ∀ a ∈ OddCore z, ∀ u ∈ U, (g * a * g⁻¹) * u = u * (g * a * g⁻¹) := by
    intro a ha u hu
    have h1 := hAU a ha _ (hgU' u hu)
    calc g * a * g⁻¹ * u = g * (a * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * a) * g⁻¹ := by rw [h1]
      _ = u * (g * a * g⁻¹) := by group
  have hgC : ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ Cen z := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcommU a ha z hzU
  set Bg : Subgroup G := (OddCore z).map (MulAut.conj g).toMonoidHom with hBg
  have hBgmem : ∀ x : G, x ∈ Bg ↔ ∃ a ∈ OddCore z, g * a * g⁻¹ = x := by
    intro x
    rw [hBg, Subgroup.mem_map]
    rfl
  have hBgC : Bg ≤ Cen z := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hBgmem x).1 hx
    exact hgC a ha
  have hBb : ∀ x : CentralizerBar z, x ∈ barOf z Bg ↔
      ∃ c : ↥(Cen z), (c : G) ∈ Bg ∧ toBar z c = x := by
    intro x
    unfold barOf
    rw [Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf]
  have hAodd : ∀ a ∈ OddCore z, Odd (orderOf a) := fun a ha =>
    L20.odd_orderOf_of_mem_pPrimeCoreOf (F := Cen z) ha
  have hBodd : Odd (Nat.card ↥(barOf z Bg)) := by
    have h1 : Nat.card ↥(barOf z Bg) ∣ Nat.card ↥(Bg.subgroupOf (Cen z)) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(Bg.subgroupOf (Cen z)) = Nat.card ↥Bg :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBgC).toEquiv
    have h3 : Nat.card ↥Bg = Nat.card ↥(OddCore z) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have h4 : Odd (Nat.card ↥(OddCore z)) := by
      show Odd (Nat.card ↥((pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype))
      rw [Subgroup.card_map_of_injective (Cen z).subtype_injective]
      exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
    exact h4.of_dvd_nat (h1.trans (dvd_of_eq (h2.trans h3)))
  have hBt : ∀ b ∈ barOf z Bg, b * toBar z tt = toBar z tt * b := by
    intro b hb
    obtain ⟨c, hcB, rfl⟩ := (hBb b).1 hb
    obtain ⟨a, ha, hac⟩ := (hBgmem c).1 hcB
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (c : G) * t = t * (c : G)
    rw [← hac]
    exact hcommU a ha t htU
  have hBn : ∀ m : CentralizerBar z, m * toBar z tt = toBar z tt * m →
      ∀ b ∈ barOf z Bg, m * b * m⁻¹ ∈ barOf z Bg := by
    intro m hm b hb
    obtain ⟨x, rfl, hxt⟩ := exists_lift_centralizer z htt2 hm
    obtain ⟨c, hcB, rfl⟩ := (hBb b).1 hb
    refine (hBb _).2 ⟨x * c * x⁻¹, ?_, by simp [map_mul, map_inv]⟩
    obtain ⟨a, ha, hac⟩ := (hBgmem c).1 hcB
    have hxt' : (x : G) * t = t * (x : G) := congrArg Subtype.val hxt
    have hy : g⁻¹ * (x : G) * g ∈ Cen z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * (x : G) * g * z = g⁻¹ * ((x : G) * t) * g := by rw [ht]; group
        _ = g⁻¹ * (t * (x : G)) * g := by rw [hxt']
        _ = z * (g⁻¹ * (x : G) * g) := by rw [ht]; group
    have hyN := Cen_le_normalizer_OddCore z hy
    have hya : g⁻¹ * (x : G) * g * a * (g⁻¹ * (x : G) * g)⁻¹ ∈ OddCore z :=
      (Subgroup.mem_normalizer_iff.1 hyN a).1 ha
    refine (hBgmem _).2 ⟨_, hya, ?_⟩
    have h5 : ((x * c * x⁻¹ : ↥(Cen z)) : G) = (x : G) * (c : G) * (x : G)⁻¹ := rfl
    rw [h5, ← hac]
    group
  have hec : ∀ a ∈ OddCore z, e * (g * a * g⁻¹) = (g * a * g⁻¹) * e := by
    intro a ha
    have h1 := hAR a ha
    calc e * (g * a * g⁻¹) = g * (y₀ * a) * g⁻¹ := by rw [he]; group
      _ = g * (a * y₀) * g⁻¹ := by rw [h1]
      _ = (g * a * g⁻¹) * e := by rw [he]; group
  have hBe : ∀ b ∈ barOf z Bg, toBar z ee * b = b * toBar z ee := by
    intro b hb
    obtain ⟨c, hcB, rfl⟩ := (hBb b).1 hb
    obtain ⟨a, ha, hac⟩ := (hBgmem c).1 hcB
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show e * (c : G) = (c : G) * e
    rw [← hac]
    exact hec a ha
  have htL : toBar z tt ∈ L₁ ⊔ L₂ := by
    rw [hsup]; exact ⟨tt, Subgroup.mem_subgroupOf.mpr (hLU htU), rfl⟩
  have ht2' : toBar z tt * toBar z tt = 1 := by rw [← map_mul, htt2, map_one]
  have he2' : toBar z ee * toBar z ee = 1 := by rw [← map_mul, hee2, map_one]
  have het' : toBar z ee * toBar z tt = toBar z tt * toBar z ee := by
    rw [← map_mul, ← map_mul, hete]
  have htI : toBar z tt ∉ L₁ ⊓ L₂ := by
    intro h'
    rcases hinfz tt htt2 h' with h'' | h''
    · exact ht1 (congrArg Subtype.val h'')
    · exact htz (congrArg Subtype.val h'')
  have heI : toBar z ee ∉ L₁ ⊓ L₂ := by
    intro h'
    apply heU
    rcases hinfz ee hee2 h' with h'' | h''
    · have : e = 1 := congrArg Subtype.val h''
      rw [this]; exact U.one_mem
    · have : e = z := congrArg Subtype.val h''
      rw [this]; exact hzU
  have hetI : toBar z ee * toBar z tt ∉ L₁ ⊓ L₂ := by
    intro h'
    apply heU
    have hett : (ee * tt) * (ee * tt) = 1 := by
      calc (ee * tt) * (ee * tt) = ee * (tt * ee) * tt := by group
        _ = ee * (ee * tt) * tt := by rw [hete]
        _ = (ee * ee) * (tt * tt) := by group
        _ = 1 := by rw [hee2, htt2, one_mul]
    have h'' := hinfz (ee * tt) hett (by rw [map_mul]; exact h')
    have hetU : e * t ∈ U := by
      rcases h'' with h'' | h''
      · have : e * t = 1 := congrArg Subtype.val h''
        rw [this]; exact U.one_mem
      · have : e * t = z := congrArg Subtype.val h''
        rw [this]; exact hzU
    have : e = (e * t) * t⁻¹ := by group
    rw [this]
    exact mul_mem hetU (inv_mem htU)
  have hswap : L208g2.cj (toBar z ee) L₁ = L₂ := by
    by_contra hnsw
    have hN : toBar z ee ∈ Nrm L₁ := L208g2.cj_eq_iff.1 ((cj_L₁_cases hP _).resolve_right hnsw)
    have hBN : barOf z Bg ≤ Nrm L₁ := by
      intro x hx
      obtain ⟨c, hcB, rfl⟩ := (hBb x).1 hx
      obtain ⟨a, ha, hac⟩ := (hBgmem c).1 hcB
      have hcodd : Odd (orderOf (c : G)) := by
        rw [← hac]
        have := MulEquiv.orderOf_eq (MulAut.conj g) a
        simp only [MulAut.conj_apply] at this
        rw [this]
        exact hAodd a ha
      have hcN := mem_normalizer_K₁_of_odd hK c.2 hcodd
      have := bar_mem_normalizer_image c.2 hcN
      rw [hK.bar₁] at this
      exact this
    have hBb0 : barOf z Bg = ⊥ :=
      ykey_l4 hctx.sylow hSC hL4 htL ht2' htI hN he2' het' heI hetI hBN hBodd hBt (fun m _ => hBn m) hBe
    have hkey : ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z := by
      intro a ha
      let c : ↥(Cen z) := ⟨g * a * g⁻¹, hgC a ha⟩
      have hcB : toBar z c ∈ barOf z Bg := (hBb _).2 ⟨c, (hBgmem _).2 ⟨a, ha, rfl⟩, rfl⟩
      rw [hBb0, Subgroup.mem_bot] at hcB
      have hker : c ∈ pPrimeCore 2 ↥(Cen z) := by
        rw [← ker_toBar z]
        exact hcB
      exact ⟨c, hker, rfl⟩
    exact hgz (fact_N hctx hmax hne hkey)
  obtain ⟨hs1, hs2⟩ := hK.swap e heC hswap
  exact ⟨e, heC, hs1, hs2, hec⟩

end Swap

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
