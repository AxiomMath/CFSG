module

public import CFSG.Quasithin.H13.U3S1344
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1342
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L139

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_H1_of_Y_F4 (h1222 : Stmt12_2_2_F4) (S : A6.Setting134 G T L V) {H Y : Subgroup G}
    (hTsyl : IsSylowTwoOf T H) (hHY : H ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G))
    (hAut : autOn Y V = autOn (L₁Of L (fsuV1 T V)) V)
    (hYC2 : IsPGroup 2 ↥(Y ⊓ centralizer (V : Set G))) :
    (centralizerMod (pCoreOf 2 Y) H Y).relIndex H = 2 ∧
      IsSylowTwoOf (r1Of T L V) (centralizerMod (pCoreOf 2 Y) H Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  have hYN : Y ≤ normalizer (V : Set G) := hYM.trans (A6.Setting134.normalizer_L_le_F4 S h1222)
  set O := pCoreOf 2 Y with hOdef
  have hOY : O ≤ Y := LieType.BorelTits.pCoreOf_le 2 Y
  have hHO : H ≤ normalizer (O : Set G) :=
    hHY.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hTH : T ≤ H := hTsyl.1
  have hconjY : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y := fun h hh y hy =>
    (mem_normalizer_iff.1 (hHY hh) y).1 hy
  have hconjO : ∀ h ∈ H, ∀ o ∈ O, h * o * h⁻¹ ∈ O := fun h hh o ho =>
    (mem_normalizer_iff.1 (hHO hh) o).1 ho

  have hρmul : ∀ (a b : G) (ha : a ∈ normalizer (V : Set G)) (hb : b ∈ normalizer (V : Set G)),
      S.frame.ρ ⟨a * b, mul_mem ha hb⟩ = S.frame.ρ ⟨a, ha⟩ * S.frame.ρ ⟨b, hb⟩ :=
    fun a b ha hb => map_mul S.frame.ρ ⟨a, ha⟩ ⟨b, hb⟩
  have hρinv : ∀ (a : G) (ha : a ∈ normalizer (V : Set G)),
      S.frame.ρ ⟨a⁻¹, inv_mem ha⟩ = (S.frame.ρ ⟨a, ha⟩)⁻¹ :=
    fun a ha => map_inv S.frame.ρ ⟨a, ha⟩

  have hYA4 : ∀ y (hyY : y ∈ Y), InA4 (S.frame.ρ ⟨y, hYN hyY⟩) := by
    intro y hyY
    have hmem : conjAct V ⟨y, hYN hyY⟩ ∈ autOn L₁ V := by
      rw [← hAut]
      exact ⟨⟨y, hYN hyY⟩, mem_subgroupOf.2 hyY, rfl⟩
    obtain ⟨l, hl, hle⟩ := hmem
    rw [← (s134_conjAct_eq_iff_rho S l ⟨y, hYN hyY⟩).1 hle]
    exact s134_rho_L1 S l.2 (mem_subgroupOf.1 hl)

  obtain ⟨y₀, hy₀Y, hy₀⟩ : ∃ (y₀ : G) (hy₀Y : y₀ ∈ Y), S.frame.ρ ⟨y₀, hYN hy₀Y⟩ = c012 := by
    obtain ⟨l, hlL1, hlN, hl⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
      c012_props.2.2
    have hmem : conjAct V ⟨l, hlN⟩ ∈ autOn Y V := by
      rw [hAut]
      exact ⟨⟨l, hlN⟩, mem_subgroupOf.2 hlL1, rfl⟩
    obtain ⟨y, hy, hye⟩ := hmem
    refine ⟨y, mem_subgroupOf.1 hy, ?_⟩
    rw [← hl]
    exact (s134_conjAct_eq_iff_rho S y ⟨l, hlN⟩).1 hye

  have hO : ∀ y (hyY : y ∈ Y), y ∈ O ↔ S.frame.ρ ⟨y, hYN hyY⟩ ∈ K4List := by
    intro y hyY
    constructor
    · intro hyO
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨y, hyO⟩
      have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine A4_two_K4 _ (hYA4 y hyY) (pow_sixteen_of_two_pow (k := k) ?_)
      rw [← map_pow]
      have : (⟨y, hYN hyY⟩ : ↥(normalizer (V : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk')
      rw [this, map_one]
    · intro hyK
      let K : Subgroup G :=
        { carrier := {x | ∃ hx : x ∈ Y, S.frame.ρ ⟨x, hYN hx⟩ ∈ K4List}
          one_mem' := ⟨one_mem _, by
            rw [show (⟨1, hYN (one_mem Y)⟩ : ↥(normalizer (V : Set G))) = 1 from rfl, map_one]
            decide⟩
          mul_mem' := fun {a b} ha hb => by
            obtain ⟨haY, ha⟩ := ha
            obtain ⟨hbY, hb⟩ := hb
            refine ⟨mul_mem haY hbY, ?_⟩
            rw [hρmul a b (hYN haY) (hYN hbY)]
            exact K4_mul _ ha _ hb
          inv_mem' := fun {a} ha => by
            obtain ⟨haY, ha⟩ := ha
            refine ⟨inv_mem haY, ?_⟩
            rw [hρinv a (hYN haY)]
            exact K4_inv _ ha }
      have hKY : K ≤ Y := fun x hx => hx.1
      have hKO : K ≤ O := by
        refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hKY
          ?_ ?_
        · refine (normal_subgroupOf_iff_le_normalizer hKY).2 fun g hg => ?_
          have key : ∀ g ∈ Y, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
            intro g hg x hx
            obtain ⟨hxY, hx⟩ := hx
            refine ⟨mul_mem (mul_mem hg hxY) (inv_mem hg), ?_⟩
            rw [hρmul _ _ (mul_mem (hYN hg) (hYN hxY)) (inv_mem (hYN hg)),
              hρmul _ _ (hYN hg) (hYN hxY), hρinv _ (hYN hg)]
            exact K4_normal_A4 _ (hYA4 g hg) _ hx
          rw [mem_normalizer_iff]
          intro x
          refine ⟨key g hg x, fun hx => ?_⟩
          have := key g⁻¹ (inv_mem hg) _ hx
          simpa [mul_assoc] using this
        · rintro ⟨x, hxY, hx⟩
          have hx2 : x * x ∈ Y ⊓ centralizer (V : Set G) := by
            refine mem_inf.2 ⟨mul_mem hxY hxY, (s134_rho_eq_one_iff S
              ⟨x * x, mul_mem (hYN hxY) (hYN hxY)⟩).1 ?_⟩
            rw [hρmul _ _ (hYN hxY) (hYN hxY)]
            exact K4_sq _ hx
          obtain ⟨j, hj⟩ := hYC2 ⟨x * x, hx2⟩
          have hj' : (x * x) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
          refine ⟨j + 1, Subtype.ext ?_⟩
          simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
          calc x ^ 2 ^ (j + 1) = (x ^ 2) ^ 2 ^ j := by rw [← pow_mul, pow_succ, mul_comm]
            _ = (x * x) ^ 2 ^ j := by rw [pow_two]
            _ = 1 := hj'
      exact hKO ⟨hyY, hyK⟩
  have hρY : ∀ (y : G) (hyY : y ∈ Y), y ∈ O ↔ S.frame.ρ ⟨y, hYN hyY⟩ ∈ K4List := hO
  have hy₀O : y₀ ∉ O := fun h => c012_not_K4.1 (by rw [← hy₀]; exact (hO y₀ hy₀Y).1 h)
  set H₁ := centralizerMod O H Y with hH₁def

  have hmemH₁ : ∀ h ∈ H, h * y₀ * h⁻¹ * y₀⁻¹ ∈ O → h ∈ H₁ := by
    intro h hh hhy
    refine mem_centralizerMod.2 ⟨hh, hHO hh, fun y hyY => ?_⟩
    have hw := hconjY h hh y₀ hy₀Y
    have hwκ : S.frame.ρ ⟨h * y₀ * h⁻¹, hYN hw⟩ * c012⁻¹ ∈ K4List := by
      have := (hO _ (mul_mem hw (inv_mem hy₀Y))).1 hhy
      rwa [hρmul _ _ (hYN hw) (inv_mem (hYN hy₀Y)), hρinv _ (hYN hy₀Y), hy₀] at this
    have hhyY : h * y * h⁻¹ * y⁻¹ ∈ Y := mul_mem (hconjY h hh y hyY) (inv_mem hyY)
    set b := S.frame.ρ ⟨h * y₀ * h⁻¹, hYN hw⟩ with hb
    set a := S.frame.ρ ⟨y, hYN hyY⟩ with ha
    have hb' : b = (b * c012⁻¹) * c012 := by group
    have hgoal : S.frame.ρ ⟨h * y * h⁻¹, hYN (hconjY h hh y hyY)⟩ * a⁻¹ ∈ K4List →
        h * y * h⁻¹ * y⁻¹ ∈ O := by
      intro hK
      refine (hO _ hhyY).2 ?_
      rw [hρmul _ _ (hYN (hconjY h hh y hyY)) (inv_mem (hYN hyY)), hρinv _ (hYN hyY)]
      exact hK
    rcases A4_dec a (hYA4 y hyY) with h1 | h1 | h1
    ·
      have hyO := (hO y hyY).2 h1
      exact mul_mem (hconjO h hh y hyO) (inv_mem hyO)
    ·
      refine hgoal ?_
      have hyy : y * y₀⁻¹ ∈ O := (hO _ (mul_mem hyY (inv_mem hy₀Y))).2 (by
        rw [hρmul _ _ (hYN hyY) (inv_mem (hYN hy₀Y)), hρinv _ (hYN hy₀Y), hy₀]
        exact h1)
      have hκ := (hO _ (hconjY h hh _ (hOY hyy))).1 (hconjO h hh _ hyy)
      have e : h * y * h⁻¹ = h * (y * y₀⁻¹) * h⁻¹ * (h * y₀ * h⁻¹) := by group
      have hρe : S.frame.ρ ⟨h * y * h⁻¹, hYN (hconjY h hh y hyY)⟩ =
          S.frame.ρ ⟨h * (y * y₀⁻¹) * h⁻¹, hYN (hconjY h hh _ (hOY hyy))⟩ * b := by
        rw [hb, ← hρmul]
        congr 1
        exact Subtype.ext e
      rw [hρe]
      have ha' : a = (a * c012⁻¹) * c012 := by group
      rw [ha', hb']
      exact cosF1 _ h1 _ hwκ _ hκ
    ·
      refine hgoal ?_
      have hyy : y * y₀ ∈ O := (hO _ (mul_mem hyY hy₀Y)).2 (by
        rw [hρmul _ _ (hYN hyY) (hYN hy₀Y), hy₀]
        exact h1)
      have hκ := (hO _ (hconjY h hh _ (hOY hyy))).1 (hconjO h hh _ hyy)
      have e : h * y * h⁻¹ = h * (y * y₀) * h⁻¹ * (h * y₀ * h⁻¹)⁻¹ := by group
      have hρe : S.frame.ρ ⟨h * y * h⁻¹, hYN (hconjY h hh y hyY)⟩ =
          S.frame.ρ ⟨h * (y * y₀) * h⁻¹, hYN (hconjY h hh _ (hOY hyy))⟩ * b⁻¹ := by
        rw [hb, ← hρinv, ← hρmul]
        congr 1
        exact Subtype.ext e
      rw [hρe]
      have ha' : a = (a * c012) * c012⁻¹ := by group
      rw [ha', hb']
      exact cosF2 _ h1 _ hwκ _ hκ

  obtain ⟨hτD, hτA, hτc, hτK⟩ := tau_facts
  obtain ⟨t, htT, htρ⟩ := S.frame.DA_T _ hτD hτA
  have htH : (t : G) ∈ H := hTH htT
  set y₀' : ↥(normalizer (V : Set G)) := ⟨y₀, hYN hy₀Y⟩ with hy₀'
  have hconjN : ∀ (g : ↥(normalizer (V : Set G))) (u : G) (huY : u ∈ Y)
      (hg : (g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ Y),
      S.frame.ρ ⟨(g : G) * u * (g : G)⁻¹ * u⁻¹, hYN hg⟩ =
        S.frame.ρ g * S.frame.ρ ⟨u, hYN huY⟩ * (S.frame.ρ g)⁻¹ * (S.frame.ρ ⟨u, hYN huY⟩)⁻¹ := by
    intro g u huY hg
    have e : (⟨(g : G) * u * (g : G)⁻¹ * u⁻¹, hYN hg⟩ : ↥(normalizer (V : Set G))) =
        g * ⟨u, hYN huY⟩ * g⁻¹ * ⟨u, hYN huY⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]

  have htH₁ : (t : G) ∉ H₁ := by
    intro h
    have h1 := (mem_centralizerMod.1 h).2.2 y₀ hy₀Y
    have hY1 : (t : G) * y₀ * (t : G)⁻¹ * y₀⁻¹ ∈ Y :=
      mul_mem (hconjY _ htH y₀ hy₀Y) (inv_mem hy₀Y)
    have h2 := (hO _ hY1).1 h1
    rw [hconjN t y₀ hy₀Y hY1, htρ, hy₀] at h2
    exact hτK h2

  have hcases : ∀ h ∈ H, h ∈ H₁ ∨ h * t ∈ H₁ := by
    intro h hh
    have hw := hconjY h hh y₀ hy₀Y
    have hwY : h * y₀ * h⁻¹ * y₀⁻¹ ∈ Y := mul_mem hw (inv_mem hy₀Y)
    have hρw : S.frame.ρ ⟨h * y₀ * h⁻¹ * y₀⁻¹, hYN hwY⟩ =
        S.frame.ρ ⟨h * y₀ * h⁻¹, hYN hw⟩ * c012⁻¹ := by
      rw [hρmul _ _ (hYN hw) (inv_mem (hYN hy₀Y)), hρinv _ (hYN hy₀Y), hy₀]
    rcases A4_dec _ (hYA4 _ hw) with h1 | h1 | h1
    · exfalso
      apply hy₀O
      have h2 := hconjO h⁻¹ (inv_mem hh) _ ((hO _ hw).2 h1)
      have e : h⁻¹ * (h * y₀ * h⁻¹) * h⁻¹⁻¹ = y₀ := by group
      rwa [e] at h2
    · left
      exact hmemH₁ h hh ((hO _ hwY).2 (by rw [hρw]; exact h1))
    · right
      refine hmemH₁ (h * t) (mul_mem hh htH) ?_

      have ht1 := hconjY _ htH y₀ hy₀Y
      have ho₁Y : (t : G) * y₀ * (t : G)⁻¹ * y₀ ∈ Y := mul_mem ht1 hy₀Y
      have ho₁ : (t : G) * y₀ * (t : G)⁻¹ * y₀ ∈ O := (hO _ ho₁Y).2 (by
        have e : (⟨(t : G) * y₀ * (t : G)⁻¹ * y₀, hYN ho₁Y⟩ : ↥(normalizer (V : Set G))) =
            t * y₀' * t⁻¹ * y₀' := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, htρ, hy₀', hy₀, hτc]
        simp [K4List])
      have hκ := (hO _ (hconjY h hh _ (hOY ho₁))).1 (hconjO h hh _ ho₁)
      have hY2 : h * ↑t * y₀ * (h * ↑t)⁻¹ * y₀⁻¹ ∈ Y :=
        mul_mem (hconjY _ (mul_mem hh htH) y₀ hy₀Y) (inv_mem hy₀Y)
      refine (hO _ hY2).2 ?_
      have e : h * ↑t * y₀ * (h * ↑t)⁻¹ * y₀⁻¹ =
          h * ((t : G) * y₀ * (t : G)⁻¹ * y₀) * h⁻¹ * (h * y₀ * h⁻¹)⁻¹ * y₀⁻¹ := by group
      have hρe : S.frame.ρ ⟨h * ↑t * y₀ * (h * ↑t)⁻¹ * y₀⁻¹, hYN hY2⟩ =
          S.frame.ρ ⟨h * ((t : G) * y₀ * (t : G)⁻¹ * y₀) * h⁻¹, hYN (hconjY h hh _ (hOY ho₁))⟩ *
            (S.frame.ρ ⟨h * y₀ * h⁻¹, hYN hw⟩)⁻¹ * c012⁻¹ := by
        rw [← hy₀, ← hρinv _ (hYN hy₀Y), ← hρinv _ (hYN hw), ← hρmul, ← hρmul]
        congr 1
        exact Subtype.ext e
      rw [hρe]
      have hb : S.frame.ρ ⟨h * y₀ * h⁻¹, hYN hw⟩ =
          (S.frame.ρ ⟨h * y₀ * h⁻¹, hYN hw⟩ * c012) * c012⁻¹ := by group
      rw [hb]
      exact cosF3 _ h1 _ hκ

  have hidx : H₁.relIndex H = 2 := by
    rw [relIndex]
    refine Subgroup.index_eq_two_iff.2 ⟨⟨t, htH⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases hcases b b.2 with h | h
    · exact Or.inr ⟨h, fun hbt => htH₁ (by
        have := mul_mem (inv_mem h) hbt
        simpa using this)⟩
    · exact Or.inl ⟨h, fun hb => htH₁ (by
        have := mul_mem (inv_mem hb) h
        simpa using this)⟩

  have hR : T ⊓ H₁ = r1Of T L V := by
    apply le_antisymm
    · rintro x ⟨hxT, hxH₁⟩
      refine (s134_mem_r1Of_iff S).2 ⟨hxT, fun hxN => ?_⟩
      have h1 := (mem_centralizerMod.1 hxH₁).2.2 y₀ hy₀Y
      have hY1 : x * y₀ * x⁻¹ * y₀⁻¹ ∈ Y :=
        mul_mem (hconjY _ (hTH hxT) y₀ hy₀Y) (inv_mem hy₀Y)
      have h2 := (hO _ hY1).1 h1
      rw [hconjN ⟨x, hxN⟩ y₀ hy₀Y hY1, hy₀] at h2
      exact D_cent _ (S.frame.T_D ⟨x, hxN⟩ hxT) h2
    · intro x hx
      obtain ⟨hxT, hxK⟩ := (s134_mem_r1Of_iff S).1 hx
      have hxN := S.frame.T_le hxT
      refine mem_inf.2 ⟨hxT, mem_centralizerMod.2 ⟨hTH hxT, hHO (hTH hxT), fun y hyY => ?_⟩⟩
      have hY1 : x * y * x⁻¹ * y⁻¹ ∈ Y := mul_mem (hconjY _ (hTH hxT) y hyY) (inv_mem hyY)
      refine (hO _ hY1).2 ?_
      rw [hconjN ⟨x, hxN⟩ y hyY hY1]
      exact K4x_comm_A4 _ (hxK hxN) _ (hYA4 y hyY)

  have hH₁H : H₁ ≤ H := centralizerMod_le_left O H Y
  have hkey : ∀ g ∈ H, ∀ x ∈ H₁, g * x * g⁻¹ ∈ H₁ := by
    intro g hg x hx
    obtain ⟨hxH, -, hxc⟩ := mem_centralizerMod.1 hx
    refine mem_centralizerMod.2 ⟨mul_mem (mul_mem hg hxH) (inv_mem hg),
      hHO (mul_mem (mul_mem hg hxH) (inv_mem hg)), fun y hyY => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Y := by
      have := hconjY g⁻¹ (inv_mem hg) y hyY
      simpa using this
    have e : g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
        g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact hconjO g hg _ (hxc _ hy')
  have hHN : H ≤ normalizer (H₁ : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hkey g hg x, fun hx => ?_⟩
    have := hkey g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this
  refine ⟨hidx, ?_⟩
  have := A4.isSylowTwoOf_inf_normal hTsyl hH₁H hHN
  rwa [hR] at this

@[expose] def Stmt13_4_4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : A6.Setting134 G T L V) (z : G),
    z ∈ fsuV1 T V → z ∉ centralizer (L : Set G) →
    ∀ H VH : Subgroup G, InHz T L V z H → IsTwoReducedIn H VH →
      quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ (VH ⊔ zpowers z) ≠ ⊥ →

      H ⊓ centralizer (VH : Set G) ≤ normalizer (L : Set G) ∧

      ((oTwoRes (H ⊓ centralizer (VH : Set G)) = ⊥ ∧
          H ⊓ centralizer (VH : Set G) = pCoreOf 2 H ∧
          pCoreOf 2 H ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧
          pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ r1Of T L V) ∨
        ∃ Lp : Subgroup G,
          (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
            Lp = L₁Of L (fsuV1 T V)) ∧
          (IsHatA6 L → Lp = l1plus T L V) ∧
          Lp = oTwoRes (H ⊓ centralizer (VH : Set G)) ∧ H ≤ normalizer (Lp : Set G) ∧
          (centralizerMod (pCoreOf 2 Lp) H Lp).relIndex H = 2 ∧
          IsSylowTwoOf (r1Of T L V) (centralizerMod (pCoreOf 2 Lp) H Lp)) ∧

      ¬ l2Of S ≤ H ∧ (IsHatA6 L → ¬ l2plusOf S ≤ H)

theorem stmt13_4_4_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1226 : Stmt12_2_6_F4)
    (h1228 : Stmt12_2_8_F4) (h1338 : A6.Stmt13_3_8_F4) (hL1 : Stmt13_2_2_9L1_F4) : Stmt13_4_4_F4 := by
  intro G _ _ T L V S z hz hzL H VH hHz hred hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hL1TH, hO2H⟩, hHzC, hHM⟩ := hHz
  have hTH : T ≤ H := le_sup_right.trans hL1TH
  have hTsyl : IsSylowTwoOf T H := A5.isSylowTwoOf_of_le S.h13.sylow hTH

  have h1 : H ⊓ centralizer (VH : Set G) ≤ normalizer (L : Set G) :=
    s134_centralizer_VH_le S hHzC hX
  set Y := oTwoRes (H ⊓ centralizer (VH : Set G)) with hYdef
  have hYH : Y ≤ H := (oTwoRes_le _).trans inf_le_left
  have hHN : H ≤ normalizer ((H ⊓ centralizer (VH : Set G) : Subgroup G) : Set G) := fun h hh =>
    mem_normalizer_inf (le_normalizer hh) (normalizer_le_normalizer_centralizer' VH (hred.2.1 hh))
  have hHY : H ≤ normalizer (Y : Set G) := hHN.trans (normalizer_le_normalizer_oTwoRes _)
  have hY2 : oTwoRes Y = Y := le_antisymm (oTwoRes_le _) (oTwoRes_le_oTwoRes _)
  have hYv : Y ≤ normalizer (L : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf ((oTwoRes_le _).trans h1) (hYH.trans hHzC)
  let F : Frame139 T L V := ⟨S.frame.ρ, S.frame.L_le, S.frame.T_le, s134_rho_eq_one_iff S,
    S.frame.image_L, S.frame.T_D, s134_pres45 S⟩
  have core := stmt13_3_9_core_F4 h1332 h1226 h1228 h1338 hL1 S.h13 S.irr (s134_isA6On S)
    ⟨hTH, hO2H⟩ hHM hY2 hYH hHY hz hzL hYv F
    (fun y hy hyN => s134_mem_normalizer_V1 S hz hzL hyN (hYv hy).2)
  refine ⟨h1, ?_, ?_⟩
  · rcases core with hY | ⟨hAut, hA6c, hhatc, hYC2⟩
    · left
      have hP : IsPGroup 2 ↥(H ⊓ centralizer (VH : Set G)) := isPGroup_of_oTwoRes_eq_bot hY
      have hle1 : H ⊓ centralizer (VH : Set G) ≤ pCoreOf 2 H :=
        CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ inf_le_left
          ((normal_subgroupOf_iff_le_normalizer inf_le_left).2 hHN) hP
      have hle2 : pCoreOf 2 H ≤ H ⊓ centralizer (VH : Set G) := by
        refine le_inf (LieType.BorelTits.pCoreOf_le 2 H) (hred.2.2.2 _
          (LieType.BorelTits.pCoreOf_le 2 H) (LieType.BorelTits.le_normalizer_pCoreOf 2 H)
          fun d hd => ?_)
        obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨d, hd⟩
        refine ⟨k, ?_⟩
        have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [this]
        exact one_mem _
      have hOT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
      have hO2 : pCoreOf 2 H ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
          (hL1TH.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 H))
          (LieType.BorelTits.pCoreOf_isPGroup 2 H)
      exact ⟨hY, le_antisymm hle1 hle2, hO2, s134_pCoreOf_L1T_le_r1Of S⟩
    · right
      obtain ⟨hidx, hsyl⟩ := s134_H1_of_Y_F4 h1222 S hTsyl hHY ((oTwoRes_le _).trans h1) hAut hYC2
      exact ⟨Y, hA6c, hhatc, rfl, hHY, hidx, hsyl⟩
  · obtain ⟨n1, n2⟩ := s134_not_L2_le S hz hzL
    exact ⟨fun h => n1 (h.trans hHzC), fun _ h => n2 (h.trans hHzC)⟩

end CFSG.Quasithin.H13.U3
