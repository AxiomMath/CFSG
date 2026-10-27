module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldCore
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixStrong

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_of_abelian {G N : Subgroup X} (hNG : N ≤ G)
    (hGN : G ≤ Subgroup.normalizer (N : Set X)) (hab : IsMulCommutative N)
    (hO : CFSG.oddCore G = ⊥) : IsPGroup 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let No : Subgroup X :=
    { carrier := {x | x ∈ N ∧ Odd (orderOf x)}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨N.mul_mem ha.1 hb.1, ?_⟩
        have hc : Commute a b := congrArg Subtype.val (hab.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
        exact Odd.of_dvd_nat (Odd.of_dvd_nat (ha.2.mul hb.2) (Nat.lcm_dvd_mul _ _))
          hc.orderOf_mul_dvd_lcm
      one_mem' := ⟨N.one_mem, by rw [orderOf_one]; exact odd_one⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [orderOf_inv]; exact ha.2⟩ }
  have hNoN : No ≤ N := fun x hx => hx.1
  have hNoG : G ≤ Subgroup.normalizer (No : Set X) := by
    intro x hx
    have hconj : ∀ y : X, y ∈ G → ∀ a ∈ No, y * a * y⁻¹ ∈ No := by
      intro y hy a ha
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hGN hy) a).mp ha.1, ?_⟩
      have h1 := orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective a
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      rw [h1]
      exact ha.2
    exact mem_normalizer_of_conj_le (hconj x hx) (by simpa using hconj x⁻¹ (G.inv_mem hx))
  have hNoodd : Odd (Nat.card No) := by
    by_contra h2
    have h2' : 2 ∣ Nat.card No := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h2)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    have h1 : orderOf (y : X) = 2 := by rw [Subgroup.orderOf_coe, hy]
    have h3 : Odd (orderOf (y : X)) := y.2.2
    rw [h1] at h3
    exact (Nat.not_odd_iff_even.mpr even_two) h3
  have hle := le_map_oddCore (hNoN.trans hNG) hNoG hNoodd
  rw [hO, Subgroup.map_bot, le_bot_iff] at hle
  intro x
  have hx0 : orderOf (x : X) ≠ 0 := (orderOf_pos (x : X)).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hx0
  refine ⟨k, Subtype.ext ?_⟩
  have hpow : (x : X) ^ (2 ^ k) ∈ No := by
    refine ⟨N.pow_mem x.2 _, ?_⟩
    rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left m (pow_pos two_pos k)]
    exact hm
  rw [hle, Subgroup.mem_bot] at hpow
  simpa using hpow

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem commutator_eq_bot_of_lt (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (hO : CFSG.oddCore G = ⊥) (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G)
    {L : Subgroup X} (hLn : L.Normal) (hLG : L < G) : ⁅L, T⁆ = ⊥ := by
  have hTN : T ≤ Subgroup.normalizer (L : Set X) := fun t _ => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top t
  rcases c.sub_normal htop hO IH hnn hLn hLG.le (card_sup_lt c.frame hLG hTN) with
    hc | ⟨-, -, -, -, -, -, -, hMB⟩
  · exact hc
  · exfalso
    have hGL : G ≤ L := hMG ▸ (hMB.trans (commutator_le_of_le_normalizer hTN))
    exact hLG.not_ge hGL

theorem commute_omegaOne_Z (c : Conf46 G T S Q H g) {t z : X} (ht : t ∈ T)
    (hz : z ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) : t * z = z * t :=
  congrArg Subtype.val (c.isMulCommutative_W.is_comm.comm ⟨t, Subgroup.mem_sup_left ht⟩
    ⟨z, (omegaOne_le _ hz).1⟩)

theorem stronglyClosed_omegaOne_top (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    {z x : X} (hz : z ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) (hS : x⁻¹ * z * x ∈ S) :
    x⁻¹ * z * x ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  have hx : x ∈ G ⊔ T := htop ▸ Subgroup.mem_top x
  obtain ⟨t, ht, h, hh, rfl⟩ := c.frame.mem_sup_iff.mp hx
  have heq : (t * h)⁻¹ * z * (t * h) = h⁻¹ * z * h := by
    have h1 := c.commute_omegaOne_Z ht hz
    calc (t * h)⁻¹ * z * (t * h) = h⁻¹ * (t⁻¹ * (z * t)) * h := by group
      _ = h⁻¹ * (t⁻¹ * (t * z)) * h := by rw [h1]
      _ = h⁻¹ * z * h := by group
  rw [heq] at hS ⊢
  exact c.stronglyClosed_omegaOne htop IH hnn hz hh hS

theorem goldschmidt_one (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G) :
    goldschmidtLayer G = ⊤ ∧ ⁅G, G⁆ = G ∧
    pCoreOf 2 G ≤ Subgroup.centralizer (G : Set X) ∧
    omegaOne ((T ⊔ rightConjugate T g) ⊓ G) = pCoreOf 2 G ⊔ omegaOne (S ⊓ G) ∧
    ∀ K : Subgroup G, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hZab : IsMulCommutative Z₁ :=
    isMulCommutative_of_le ((omegaOne_le _).trans inf_le_left) c.isMulCommutative_W
  have hZS : Z₁ ≤ S := (omegaOne_le _).trans (inf_le_left.trans c.W_le_S)
  have hZG : Z₁ ≤ G := (omegaOne_le _).trans inf_le_right
  have hSX : IsSylowOf 2 S ⊤ := htop ▸ c.sylowFrame.sylow
  obtain ⟨-, hS2, hidx⟩ := isSylowOf_iff.mp hSX
  rw [Subgroup.relIndex_top_right] at hidx
  set SY : Sylow 2 X := hS2.toSylow hidx with hSYdef
  have hSYc : (SY : Subgroup X) = S := IsPGroup.toSylow_coe hS2 hidx
  have hcl : ∀ a ∈ Z₁, ∀ x : X, x⁻¹ * a * x ∈ (SY : Subgroup X) → x⁻¹ * a * x ∈ Z₁ := by
    intro a ha x hx
    rw [hSYc] at hx
    exact c.stronglyClosed_omegaOne_top htop IH hnn ha hx
  obtain ⟨ha, hb, hcomp⟩ := goldschmidt_subgroup hG SY (hSYc ▸ hZS) hZab hcl hMG hO
  rw [hSYc] at hb
  set E := goldschmidtLayer G with hEdef
  have hEc : E.Characteristic := by
    rw [hEdef, goldschmidtLayer_eq_layer]
    exact CFSG.LocalCores.layer_characteristic
  set EX := E.map G.subtype with hEXdef
  have hEXG : EX ≤ G := Subgroup.map_subtype_le _
  have hEXn : EX.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro x _
    exact mem_normalizer_map_of_characteristic _ (by
      rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x)
  have hPZ : pCoreOf 2 G ≤ Z₁ := by
    have h1 : CFSG.Open.pCore 2 G ≤ Z₁.subgroupOf G := hb ▸ le_sup_left
    have h2 := Subgroup.map_mono (f := G.subtype) h1
    rw [Subgroup.subgroupOf_map_subtype] at h2
    exact h2.trans inf_le_left
  have hGsup : pCoreOf 2 G ⊔ EX = G := by
    have h1 := congrArg (Subgroup.map G.subtype) ha
    rwa [Subgroup.map_sup, map_subtype_top] at h1
  have hEtop : E = ⊤ := by
    by_contra hne
    have hlt : EX < G := by
      refine lt_of_le_of_ne hEXG fun heq => hne ?_
      apply Subgroup.map_injective G.subtype_injective
      rw [← hEXdef, heq, map_subtype_top]
    have hc := c.commutator_eq_bot_of_lt htop hO IH hnn hMG hEXn hlt
    have hTC : G ≤ Subgroup.centralizer (T : Set X) := by
      rw [← hGsup]
      refine sup_le ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact c.commute_omegaOne_Z ht (hPZ hp)
    apply c.ne
    rw [rightConjugate_eq_self_iff]
    exact Subgroup.centralizer_le_normalizer _ (hTC c.mem)
  have hlayer : CFSG.layer G = ⊤ := by rw [← goldschmidtLayer_eq_layer]; exact hEtop
  refine ⟨hEtop, ?_, ?_, ?_, hcomp⟩
  ·
    have h1 := CFSG.LocalCores.layer_perfect (G := G)
    rw [hlayer] at h1
    have h2 := congrArg (Subgroup.map G.subtype) h1
    rwa [Subgroup.map_commutator, map_subtype_top] at h2
  ·
    have hsol : Group.IsSolvable (CFSG.Open.pCore 2 G) := by
      have := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := G)).isNilpotent
      infer_instance
    have hsub : (CFSG.Open.pCore 2 G).IsSubnormal :=
      (CFSG.LieType.BorelTits.pCore_normal 2 (G := G)).isSubnormal
    have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsol hsub).2
    rw [hlayer] at hcomm
    intro y hy
    change y ∈ (CFSG.Open.pCore 2 G).map G.subtype at hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : ⁅(⟨x, hx⟩ : G), p⁆ ∈ ⁅(⊤ : Subgroup G), CFSG.Open.pCore 2 G⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hp
    rw [hcomm, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hx⟩ : G) * p = p * ⟨x, hx⟩ := by
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    exact congrArg Subtype.val h2
  ·
    have h1 := congrArg (Subgroup.map G.subtype) hb
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZG, Subgroup.map_sup,
      MonoidHom.map_closure] at h1
    rw [h1, omegaOne]
    congr 2
    ext x
    constructor
    · rintro ⟨y, ⟨⟨hyS, -⟩, hy2⟩, rfl⟩
      exact ⟨⟨Subgroup.mem_subgroupOf.mp hyS, y.2⟩, by simpa using congrArg Subtype.val hy2⟩
    · rintro ⟨⟨hxS, hxG⟩, hx2⟩
      refine ⟨⟨x, hxG⟩, ⟨⟨Subgroup.mem_subgroupOf.mpr hxS, ?_⟩, ?_⟩, rfl⟩
      · rw [hEtop]; exact Subgroup.mem_top _
      · exact Subtype.ext (by simpa using hx2)

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
