module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2YShape
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Quat
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Lift
public import CFSG.GH74.GLS.Stage2.Final.M12Odd

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.L208Key
  CFSG.GH74.GLS.Stage2.Final

section Key

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem g2_key (hctx : Stage2Ctx G z Kind.g2 S) (h4a : Thm4a (Cen z)) (h4c : Thm4c z (Cen z))
    {U : Subgroup G} (hUS : U ≤ S) (hU4 : IVK.IsFourSubgroup U) (hzU : z ∈ U)
    (hUn : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U)
    {g : G} (hg : g ∈ normalizer (U : Set G)) (hgz : g * z * g⁻¹ ≠ z) :
    ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg2 := L26.g2_data hctx
  obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg2.shape
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hzz : z * z = 1 := by
    have : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
    simpa [pow_two] using this
  have hz1 : z ≠ 1 := by intro e; rw [e, orderOf_one] at hz2; omega
  have hLU : U ≤ LC z := hg2.base.four_le U hUS hU4 hUn
  have hUC : U ≤ Cen z := hUS.trans hctx.S_le_Cen
  have hRU : U ≤ RC S z := le_inf hUS hLU
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
    intro h
    apply hz1
    have h1 : z = g⁻¹ * t * g := by rw [ht]; group
    rw [h1, h]; group
  have htz : t ≠ z := hgz
  have htt : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [ht]; group
      _ = 1 := by rw [hzz]; group
  obtain ⟨n, A, B, hAB, hA, hB⟩ := hsh.2.2.2.2.2.2.1
  have hzR : ∀ r ∈ RC S z, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.1 (hctx.S_le_Cen hr.1)
  obtain ⟨y₀, hy₀R, hy₀2, hy₀U, hy₀c⟩ :=
    exists_involution_comm_U_of_quatProd hAB hA hB hRU hU4 hzU htU hz1 hzR htz ht1
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
  have heU : e ∉ U := fun h => hy₀U ((hgU y₀).2 h)
  have htC : t ∈ Cen z := hUC htU
  have hzC : z ∈ Cen z := mem_Cen_self z
  set tt : ↥(Cen z) := ⟨t, htC⟩ with htt'
  set ee : ↥(Cen z) := ⟨e, heC⟩ with hee'
  have htt2 : tt * tt = 1 := Subtype.ext htt
  have hee2 : ee * ee = 1 := Subtype.ext hee
  have hete : ee * tt = tt * ee := Subtype.ext het
  have hsup := sup_eq hsh
  have p₁ := pair₁ hsh
  have hzbar : toBar z ⟨z, hzC⟩ ∈ L₁ ⊓ L₂ := by
    have hzL : toBar z ⟨z, hzC⟩ ∈ L₁ ⊔ L₂ := by
      rw [hsup]; exact ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr (hLU hzU), rfl⟩
    have hcen : ∀ c : CentralizerBar z, toBar z ⟨z, hzC⟩ * c = c * toBar z ⟨z, hzC⟩ :=
      fun c => ((Subgroup.mem_center_iff.1 (toBar_z_mem_center z)) c).symm
    have h2 : toBar z ⟨z, hzC⟩ ∈ L₂ := p₁.mem_of_cen hzL (fun c _ => hcen c)
    exact ⟨p₁.cen' h2 (fun c _ => (hcen c).symm), h2⟩
  have hzbar1 : toBar z ⟨z, hzC⟩ ≠ 1 := by
    intro h
    have := eq_one_of_toBar_eq_one z (x := ⟨z, hzC⟩) (Subtype.ext hzz) h
    exact hz1 (congrArg Subtype.val this)
  have hinfz : ∀ x : ↥(Cen z), x * x = 1 → toBar z x ∈ L₁ ⊓ L₂ →
      x = 1 ∨ x = ⟨z, hzC⟩ := by
    intro x hx hxI
    refine eq_one_or_eq_z_of_toBar z hzz hx ?_
    rcases p₁.inf_cases hzbar hzbar1 hxI with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hAU := g2_U_centralizes_oddCore hctx h4a h4c hUS hU4 hUn
  have hAR := g2_R_centralizes_oddCore hctx h4a h4c
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
  have hBe : ∀ b ∈ barOf z Bg, toBar z ee * b = b * toBar z ee := by
    intro b hb
    obtain ⟨c, hcB, rfl⟩ := (hBb b).1 hb
    obtain ⟨a, ha, hac⟩ := (hBgmem c).1 hcB
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show e * (c : G) = (c : G) * e
    rw [← hac]
    have h1 := hAR a ha y₀ hy₀R
    calc e * (g * a * g⁻¹) = g * (y₀ * a) * g⁻¹ := by rw [he]; group
      _ = g * (a * y₀) * g⁻¹ := by rw [h1]
      _ = (g * a * g⁻¹) * e := by rw [he]; group
  have htL : toBar z tt ∈ LBar z := ⟨tt, Subgroup.mem_subgroupOf.mpr (hLU htU), rfl⟩
  have ht2' : toBar z tt * toBar z tt = 1 := by rw [← map_mul, htt2, map_one]
  have he2' : toBar z ee * toBar z ee = 1 := by rw [← map_mul, hee2, map_one]
  have het' : toBar z ee * toBar z tt = toBar z tt * toBar z ee := by
    rw [← map_mul, ← map_mul, hete]
  have htI : toBar z tt ∉ L₁ ⊓ L₂ := by
    intro h
    rcases hinfz tt htt2 h with h' | h'
    · exact ht1 (congrArg Subtype.val h')
    · exact htz (congrArg Subtype.val h')
  have heI : toBar z ee ∉ L₁ ⊓ L₂ := by
    intro h
    apply heU
    rcases hinfz ee hee2 h with h' | h'
    · have : e = 1 := congrArg Subtype.val h'
      rw [this]; exact U.one_mem
    · have : e = z := congrArg Subtype.val h'
      rw [this]; exact hzU
  have hetI : toBar z ee * toBar z tt ∉ L₁ ⊓ L₂ := by
    intro h
    apply heU
    have hett : (ee * tt) * (ee * tt) = 1 := by
      calc (ee * tt) * (ee * tt) = ee * (tt * ee) * tt := by group
        _ = ee * (ee * tt) * tt := by rw [hete]
        _ = (ee * ee) * (tt * tt) := by group
        _ = 1 := by rw [hee2, htt2, one_mul]
    have h' := hinfz (ee * tt) hett (by rw [map_mul]; exact h)
    have hetU : e * t ∈ U := by
      rcases h' with h' | h'
      · have : e * t = 1 := congrArg Subtype.val h'
        rw [this]; exact U.one_mem
      · have : e * t = z := congrArg Subtype.val h'
        rw [this]; exact hzU
    have : e = (e * t) * t⁻¹ := by group
    rw [this]
    exact mul_mem hetU (inv_mem htU)
  have hBb0 : barOf z Bg = ⊥ :=
    ykey_of_shape hctx hsh htL ht2' htI he2' het' heI hetI hBodd hBt hBn hBe
  intro a ha
  let c : ↥(Cen z) := ⟨g * a * g⁻¹, hgC a ha⟩
  have hcB : toBar z c ∈ barOf z Bg := (hBb _).2 ⟨c, (hBgmem _).2 ⟨a, ha, rfl⟩, rfl⟩
  rw [hBb0, Subgroup.mem_bot] at hcB
  have hker : c ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← ker_toBar z]
    exact hcB
  exact ⟨c, hker, rfl⟩

end Key

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
