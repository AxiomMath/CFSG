module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf
public import CFSG.Quasithin.Vol2.KGFactC31Hex

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin.J4Fam CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem false_of_two_actions {B S : Type} [Group B] [Finite B] [Group S] [Finite S]
    [hSs : IsSimpleGroup S] (hS : Nat.card S = 168)
    (ρ : B →* Equiv.Perm (Fin 5)) (hρ : ρ.range = alternatingGroup (Fin 5))
    (α : B →* S) (hα : Function.Surjective α)
    (hker : ρ.ker ⊓ α.ker = CFSG.pCore 2 B)
    (hcard : ∀ X Y : Subgroup (B ⧸ CFSG.pCore 2 B), X.Normal → Y.Normal →
      CFSG.IsQuasisimple ↥X → CFSG.IsQuasisimple ↥Y → Nat.card X = Nat.card Y) : False := by
  set P := CFSG.pCore 2 B with hP
  have hPρ : P ≤ ρ.ker := hker ▸ inf_le_left
  have hPα : P ≤ α.ker := hker ▸ inf_le_right
  let ρb : B ⧸ P →* Equiv.Perm (Fin 5) := QuotientGroup.lift P ρ hPρ
  let αb : B ⧸ P →* S := QuotientGroup.lift P α hPα
  have hρb : ∀ b : B, ρb (b : B ⧸ P) = ρ b := fun b => QuotientGroup.lift_mk P hPρ b
  have hαb : ∀ b : B, αb (b : B ⧸ P) = α b := fun b => QuotientGroup.lift_mk P hPα b
  have hαbs : Function.Surjective αb := by
    intro s
    obtain ⟨b, rfl⟩ := hα s
    exact ⟨b, hαb b⟩
  have hρbr : ρb.range = alternatingGroup (Fin 5) := by
    rw [← hρ]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨b, (hρb b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, hρb b⟩
  have hinter : ∀ x : B ⧸ P, ρb x = 1 → αb x = 1 → x = 1 := by
    intro x h1 h2
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hρb] at h1
    rw [hαb] at h2
    have hb : b ∈ P := hker ▸ ⟨h1, h2⟩
    exact (QuotientGroup.eq_one_iff b).mpr hb
  have hcardB : Nat.card (B ⧸ P) = Nat.card ρb.ker * Nat.card ρb.range :=
    by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρb.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρb).toEquiv, mul_comm]
  have hcardB' : Nat.card (B ⧸ P) = Nat.card αb.ker * Nat.card S := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup αb.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective αb hαbs).toEquiv, mul_comm]
  have h60 : Nat.card ρb.range = 60 := by rw [hρbr, card_alt5]
  have hSna := nonabelian_of_card168 hS
  have hA5 := alt5_simple
  set X := ρb.ker with hX
  set Y := αb.ker with hY
  have hXinj : Function.Injective (αb.comp X.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : ρb (x : B ⧸ P) = 1 := x.2
    have h2 : αb (x : B ⧸ P) = 1 := hx
    exact Subgroup.mem_bot.mpr (Subtype.ext (hinter _ h1 h2))
  have hYinj : Function.Injective (ρb.comp Y.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : ρb (x : B ⧸ P) = 1 := hx
    have h2 : αb (x : B ⧸ P) = 1 := x.2
    exact Subgroup.mem_bot.mpr (Subtype.ext (hinter _ h1 h2))
  have hXtop : X.map αb = ⊤ := by
    have hn : (X.map αb).Normal := (MonoidHom.normal_ker ρb).map αb hαbs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.map αb) with hb | ht
    · exfalso
      have hX1 : X = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h2 : αb x = 1 := by
          have : αb x ∈ X.map αb := Subgroup.mem_map_of_mem αb hx
          rwa [hb, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (hinter x hx h2)
      rw [hX1, Subgroup.card_bot, one_mul, h60] at hcardB
      rw [hcardB, hS] at hcardB'
      have : 168 ∣ 60 := ⟨Nat.card αb.ker, by rw [hcardB']; ring⟩
      norm_num at this
    · exact ht
  have hYtop : Y.map ρb = alternatingGroup (Fin 5) := by
    have hle : Y.map ρb ≤ alternatingGroup (Fin 5) := by
      rw [← hρbr]
      exact Subgroup.map_le_range ρb Y
    have hn : ((Y.map ρb).subgroupOf (alternatingGroup (Fin 5))).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      obtain ⟨y, hy, hya⟩ := ha
      have hg : (g : Equiv.Perm (Fin 5)) ∈ ρb.range := by rw [hρbr]; exact g.2
      obtain ⟨x, hx⟩ := hg
      refine ⟨x * y * x⁻¹, (MonoidHom.normal_ker αb).conj_mem y hy x, ?_⟩
      rw [map_mul, map_mul, map_inv, hx, hya]
      rfl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Y.map ρb).subgroupOf (alternatingGroup (Fin 5))) with hb | ht
    · exfalso
      have hY1 : Y = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 : ρb x = 1 := by
          have hm : ρb x ∈ Y.map ρb := Subgroup.mem_map_of_mem ρb hx
          have hm' : (⟨ρb x, hle hm⟩ : ↥(alternatingGroup (Fin 5))) ∈
              (Y.map ρb).subgroupOf (alternatingGroup (Fin 5)) := Subgroup.mem_subgroupOf.mpr hm
          rw [hb, Subgroup.mem_bot] at hm'
          exact congrArg Subtype.val hm'
        exact Subgroup.mem_bot.mpr (hinter x h1 hx)
      rw [hY1, Subgroup.card_bot, one_mul, hS] at hcardB'
      rw [hcardB', h60] at hcardB
      have : 60 ∣ 168 := ⟨Nat.card ρb.ker, by rw [hcardB]; ring⟩
      norm_num at this
    · apply le_antisymm hle
      intro g hg
      have : (⟨g, hg⟩ : ↥(alternatingGroup (Fin 5))) ∈
          (Y.map ρb).subgroupOf (alternatingGroup (Fin 5)) := by rw [ht]; trivial
      exact Subgroup.mem_subgroupOf.mp this
  have hXs : Function.Surjective (αb.comp X.subtype) := by
    intro s
    have : s ∈ X.map αb := by rw [hXtop]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  let eX : ↥X ≃* S := MulEquiv.ofBijective (αb.comp X.subtype) ⟨hXinj, hXs⟩
  have hYm : ∀ y : ↥Y, ρb y ∈ alternatingGroup (Fin 5) := fun y => by
    rw [← hYtop]; exact Subgroup.mem_map_of_mem ρb y.2
  let ρY : ↥Y →* ↥(alternatingGroup (Fin 5)) := (ρb.comp Y.subtype).codRestrict _ hYm
  have hρYi : Function.Injective ρY := fun a b h => hYinj (congrArg Subtype.val h)
  have hρYs : Function.Surjective ρY := by
    intro g
    have : (g : Equiv.Perm (Fin 5)) ∈ Y.map ρb := by rw [hYtop]; exact g.2
    obtain ⟨y, hy, hyg⟩ := this
    exact ⟨⟨y, hy⟩, Subtype.ext hyg⟩
  let eY : ↥Y ≃* ↥(alternatingGroup (Fin 5)) := MulEquiv.ofBijective ρY ⟨hρYi, hρYs⟩
  have hqX : CFSG.IsQuasisimple ↥X :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm
      (CFSG.Quasithin.KGC31.Hex.isQuasisimple_of_simple hSs hSna)
  have hqY : CFSG.IsQuasisimple ↥Y :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eY.symm
      (CFSG.Quasithin.KGC31.Hex.isQuasisimple_of_simple hA5 alt5_nonabelian)
  have h := hcard X Y (MonoidHom.normal_ker ρb) (MonoidHom.normal_ker αb) hqX hqY
  rw [Nat.card_congr eX.toEquiv, Nat.card_congr eY.toEquiv, hS, card_alt5] at h
  norm_num at h

end CFSG.SectionRank.QTK.Insp443
