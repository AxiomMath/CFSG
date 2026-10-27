module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGBasic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGAlt
import CFSG.GH74.GLS.Balance.Bender.AuxSylow
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ

open CFSG.Open CFSG.GH74.Uniqueness.SU CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGB Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem sup_le_normalizer (c : KQCfg A p Kb Sb Bb Mb z) : Kb ⊔ Sb ≤ normalizer (Kb : Set A) :=
  sup_le Subgroup.le_normalizer c.S_le_K

theorem center_trivial (c : KQCfg A p Kb Sb Bb Mb z) {k : A} (hk : k ∈ Kb)
    (h : ∀ l ∈ Kb, k * l = l * k) : k = 1 := by
  haveI := c.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Kb) with hbot | htop
  · have hmem : (⟨k, hk⟩ : ↥Kb) ∈ Subgroup.center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (h g g.2).symm
    rw [hbot] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  · obtain ⟨a, b, hab⟩ := c.nonab
    exfalso
    apply hab
    have : a ∈ Subgroup.center ↥Kb := by
      rw [htop]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

theorem centralizer_inf_sup_eq_bot (c : KQCfg A p Kb Sb Bb Mb z) :
    centralizer (Kb : Set A) ⊓ (Kb ⊔ Sb) = ⊥ := by
  set X : Subgroup A := Kb ⊔ Sb with hX
  set C : Subgroup A := centralizer (Kb : Set A) ⊓ X with hC
  have hXn : X ≤ normalizer (Kb : Set A) := sup_le_normalizer c
  have hXC : X ≤ normalizer (C : Set A) := fun x hx =>
    mem_normalizer_inf' (mem_normalizer_centralizer' (hXn hx)) (Subgroup.le_normalizer hx)
  have hBX : Bb ≤ normalizer (X : Set A) := fun b hb =>
    mem_normalizer_sup' (c.B_le_K hb) (c.B_le_S hb)
  have hBC : Bb ≤ normalizer (C : Set A) := fun b hb =>
    mem_normalizer_inf' (mem_normalizer_centralizer' (c.B_le_K hb)) (hBX hb)
  have hSC : Sb ≤ normalizer (C : Set A) := fun s hs => hXC (Subgroup.mem_sup_right hs)
  have hC2 : IsPGroup 2 C := by
    intro g
    obtain ⟨s, hs, k, hk, hgsk⟩ := exists_mul_of_le_normalizer c.S_le_K g.2.2
    obtain ⟨a, ha⟩ := c.S_two ⟨s, hs⟩
    have hsa : s ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨k', hk', hm⟩ := pow_mul_mem (c.S_le_K hs) hk (2 ^ a)
    have hpowK : (g : A) ^ (2 ^ a) ∈ Kb := by
      rw [hgsk, hm, hsa, one_mul]
      exact hk'
    have hpowC : (g : A) ^ (2 ^ a) ∈ C := C.pow_mem g.2 _
    have h1 : (g : A) ^ (2 ^ a) = 1 :=
      center_trivial c hpowK fun l hl => (mem_centralizer_iff.mp hpowC.1 l hl).symm
    exact ⟨a, Subtype.ext (by simpa using h1)⟩
  have hCS : C ≤ Sb := by
    have hT2 : IsPGroup 2 (Sb ⊔ C : Subgroup A) :=
      CFSG.GH74.GLS.Balance.isPGroup_sup_of_le_normalizer c.S_two hC2 hSC
    have hBT : Bb ≤ normalizer ((Sb ⊔ C : Subgroup A) : Set A) := fun b hb =>
      mem_normalizer_sup' (c.B_le_S hb) (hBC hb)
    have := c.max_S (Sb ⊔ C) hT2 hBT le_sup_left
    exact le_sup_right.trans this.le
  by_contra hne
  have hmem := c.cover C hCS hne hSC hBC
  exact c.not_le fun k hk => hmem (hXC (Subgroup.mem_sup_left hk))

theorem eq_one_of_centralizes (c : KQCfg A p Kb Sb Bb Mb z) {x : A} (hx : x ∈ Kb ⊔ Sb)
    (h : ∀ k ∈ Kb, x * k = k * x) : x = 1 := by
  have hmem : x ∈ centralizer (Kb : Set A) ⊓ (Kb ⊔ Sb) :=
    ⟨mem_centralizer_iff.mpr fun k hk => (h k hk).symm, hx⟩
  rw [centralizer_inf_sup_eq_bot c] at hmem
  exact Subgroup.mem_bot.mp hmem

def conjAut {K : Subgroup A} (g : normalizer (K : Set A)) : MulAut ↥K where
  toFun k := ⟨g.1 * k.1 * g.1⁻¹, (mem_normalizer_iff.mp g.2 k.1).mp k.2⟩
  invFun k := ⟨g.1⁻¹ * k.1 * g.1, by
    have e : g.1 * (g.1⁻¹ * k.1 * g.1) * g.1⁻¹ = k.1 := by group
    exact (mem_normalizer_iff.mp g.2 _).mpr (by rw [e]; exact k.2)⟩
  left_inv k := by
    apply Subtype.ext
    show g.1⁻¹ * (g.1 * k.1 * g.1⁻¹) * g.1 = k.1
    group
  right_inv k := by
    apply Subtype.ext
    show g.1 * (g.1⁻¹ * k.1 * g.1) * g.1⁻¹ = k.1
    group
  map_mul' a b := by
    apply Subtype.ext
    show g.1 * (a.1 * b.1) * g.1⁻¹ = g.1 * a.1 * g.1⁻¹ * (g.1 * b.1 * g.1⁻¹)
    group

def conjHom (K : Subgroup A) : normalizer (K : Set A) →* MulAut ↥K :=
  MonoidHom.mk' conjAut fun a b => by
    ext k
    show (a * b).1 * k.1 * (a * b).1⁻¹ = a.1 * (b.1 * k.1 * b.1⁻¹) * a.1⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem exists_B1 (c : KQCfg A p Kb Sb Bb Mb z) (hAut : KFactAutAltOrder) {n : ℕ}
    (e : ↥Kb ≃* alternatingGroup (Fin n)) (hpn : p ≤ n) (hn : n < 2 * p) :
    ∃ b ∈ Bb, b ≠ 1 ∧ ∀ k ∈ Kb, b * k = k * b := by
  by_contra hcon
  push Not at hcon
  have hn5 : 5 ≤ n := c.five_le.trans hpn
  set φ : ↥Bb →* MulAut ↥Kb := (conjHom Kb).comp (Subgroup.inclusion c.B_le_K) with hφ
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun b hb => ?_
    by_contra hb1
    have hb1' : (b : A) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨k, hk, hne⟩ := hcon b b.2 hb1'
    apply hne
    have := congrArg (fun f : MulAut ↥Kb => ((f ⟨k, hk⟩ : ↥Kb) : A)) hb
    simp only [hφ, MonoidHom.comp_apply, conjHom, MonoidHom.mk'_apply, conjAut,
      MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_inclusion, MulAut.one_apply] at this
    have h2 : (b : A) * k * (b : A)⁻¹ = k := this
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hdvd : p ^ 2 ∣ Nat.card (MulAut ↥Kb) := by
    rw [← c.B_card]
    exact Subgroup.card_dvd_of_injective φ hinj
  have hdvd2 : p ^ 2 ∣ 2 * n.factorial :=
    hdvd.trans (hAut ↥Kb n hn5 ⟨e⟩)
  exact KGAlt.not_sq_dvd_two_mul_factorial c.prime c.five_le hpn hn hdvd2

theorem centralizes_X (c : KQCfg A p Kb Sb Bb Mb z) {b : A} (hb : b ∈ Bb)
    (hbK : ∀ k ∈ Kb, b * k = k * b) : ∀ x ∈ Kb ⊔ Sb, b * x = x * b := by
  intro x hx
  obtain ⟨s, hs, k, hk, rfl⟩ := exists_mul_of_le_normalizer c.S_le_K hx
  have hbs : b * s = s * b := by
    set d : A := b * s * b⁻¹ * s⁻¹ with hd
    have hbsS : b * s * b⁻¹ ∈ Sb := (mem_normalizer_iff.mp (c.B_le_S hb) s).mp hs
    have hdS : d ∈ Sb := Sb.mul_mem hbsS (Sb.inv_mem hs)
    have hdX : d ∈ Kb ⊔ Sb := Subgroup.mem_sup_right hdS
    have hdc : ∀ l ∈ Kb, d * l = l * d := by
      intro l hl
      have hk₁ : s⁻¹ * l * s ∈ Kb := by
        have e : s * (s⁻¹ * l * s) * s⁻¹ = l := by group
        exact (mem_normalizer_iff.mp (c.S_le_K hs) _).mpr (by rw [e]; exact hl)
      have hinv : b⁻¹ * (s⁻¹ * l * s) = (s⁻¹ * l * s) * b⁻¹ :=
        (Commute.inv_left (show Commute b (s⁻¹ * l * s) from hbK _ hk₁)).eq
      calc d * l = b * s * (b⁻¹ * (s⁻¹ * l * s)) * s⁻¹ := by rw [hd]; group
        _ = b * s * ((s⁻¹ * l * s) * b⁻¹) * s⁻¹ := by rw [hinv]
        _ = (b * l) * s * b⁻¹ * s⁻¹ := by group
        _ = (l * b) * s * b⁻¹ * s⁻¹ := by rw [hbK l hl]
        _ = l * d := by rw [hd]; group
    have hd1 : d = 1 := eq_one_of_centralizes c hdX hdc
    have : b * s * b⁻¹ * s⁻¹ = 1 := hd1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  calc b * (s * k) = (b * s) * k := by group
    _ = s * b * k := by rw [hbs]
    _ = s * (b * k) := by group
    _ = s * (k * b) := by rw [hbK k hk]
    _ = s * k * b := by group

theorem B_eq_sup (c : KQCfg A p Kb Sb Bb Mb z) {b : A} (hb : b ∈ Bb) (hb1 : b ≠ 1)
    (hbK : ∀ k ∈ Kb, b * k = k * b) : Bb = zpowers z ⊔ zpowers b := by
  have hp := c.prime
  have hzp : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [c.z_order] at this
  have hbp : b ^ p = 1 := (SU1.isElemAbelian_iff.mp c.B_elem).2 b hb
  have hnot : b ∉ zpowers z := by
    intro hmem
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hmem
    have hbKb : z ^ i ∈ Kb := Subgroup.zpow_mem _ c.z_mem_K i
    exact hb1 (center_trivial c hbKb fun l hl => hbK l hl)
  have hcomm : ∀ e ∈ zpowers z, e * b = b * e := by
    intro e he
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute z b from (hbK z c.z_mem_K).symm) i).eq
  have hle : zpowers z ⊔ zpowers b ≤ Bb :=
    sup_le (zpowers_le.mpr c.z_mem_B) (zpowers_le.mpr hb)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers z) hbp hnot hcomm,
    Nat.card_zpowers, c.z_order, c.B_card, pow_two]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ
