module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Layer
public import CFSG.GH74.Generic.BProg.B3.S3Sec29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3Sec29C

variable {G : Type} [Group G] [Finite G]

section PartC

variable {x y : G} {K A B Q D J R : Subgroup G}

theorem le_Jstar (B J : Subgroup G) : J ≤ Jstar B J := fun j hj =>
  le_iSup₂ (f := fun g (_ : g ∈ B) => J.map (MulAut.conj g).toMonoidHom) 1 B.one_mem
    ⟨j, hj, by simp⟩

theorem Jstar_le_pLayer (hB : B ≤ centralizer ({y} : Set G))
    (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) :
    Jstar B J ≤ pLayerOf 2 (centralizer ({y} : Set G)) := by
  refine iSup₂_le fun g hg => ?_
  have hX : (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({y} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hB hg))
  have h1 := Stage1.Thm2.Recip.isPCompIn_map_conj hJ g
  rw [hX] at h1
  exact le_sSup h1

theorem map_conj_Jstar_le {g : G} (hg : g ∈ B) :
    (Jstar B J).map (MulAut.conj g).toMonoidHom ≤ Jstar B J := by
  refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun b hb => ?_)
  rintro _ ⟨j, hj, rfl⟩
  have : (MulAut.conj g).toMonoidHom ((MulAut.conj b).toMonoidHom j) =
      (MulAut.conj (g * b)).toMonoidHom j := by simp [MulAut.conj_apply, mul_assoc]
  show (MulAut.conj g).toMonoidHom ((MulAut.conj b).toMonoidHom j) ∈ Jstar B J
  rw [this]
  exact le_iSup₂ (f := fun g (_ : g ∈ B) => J.map (MulAut.conj g).toMonoidHom) (g * b)
    (mul_mem hg hb) ⟨j, hj, rfl⟩

theorem mem_normalizer_Jstar {g : G} (hg : g ∈ B) : g ∈ normalizer ((Jstar B J : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => map_conj_Jstar_le hg ⟨z, hz, rfl⟩, fun hz => ?_⟩
  have := map_conj_Jstar_le (inv_mem hg) ⟨_, hz, rfl⟩
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem zstar_Jstar_le_cSec (hB : B ≤ centralizer ({y} : Set G))
    (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) : Zstar (Jstar B J) ≤ cSec J := by
  intro z hz
  obtain ⟨hzJ, hzS⟩ := Subgroup.mem_inf.1 hz
  have hzN : z ∈ normalizer (J : Set G) :=
    Stage1.Thm2.Recip.pLayerOf_le_normalizer hJ (Jstar_le_pLayer hB hJ hzJ)
  refine ⟨hzN, TwoThin.mem_normalizer_pPrimeCoreOf hzN, fun j hj => ?_⟩
  have h1 : ⁅j, z⁆ ∈ pPrimeCoreOf 2 (Jstar B J) := hzS.2.2 j (le_Jstar B J hj)
  have h2 : ⁅j, z⁆ ∈ J := by
    have : ⁅j, z⁆ = j * (z * j⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem hj ((Subgroup.mem_normalizer_iff.1 hzN j⁻¹).1 (inv_mem hj))
  exact S3Ctx29Layer.inf_pPrimeCoreOf_le (le_Jstar B J) ⟨h2, h1⟩

theorem Zstar_conj_mem (X : Subgroup G) {g z : G} (hg : g ∈ normalizer (X : Set G))
    (hz : z ∈ Zstar X) : g * z * g⁻¹ ∈ Zstar X :=
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_inf.1 hz).1,
    Stage1.Thm2.Recip.cSec_conj X hg (Subgroup.mem_inf.1 hz).2⟩

end PartC

section Central

theorem exists_involution_central {F P : Subgroup G} (hP : IsPGroup 2 ↥P) (hFP : F ≤ P) (hF : F ≠ ⊥)
    (hnorm : ∀ p ∈ P, ∀ f ∈ F, p * f * p⁻¹ ∈ F) :
    ∃ z ∈ F, orderOf z = 2 ∧ ∀ p ∈ P, p * z = z * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  set H : Subgroup ↥P := F.subgroupOf P with hH
  have hHn : H.Normal := ⟨fun n hn g => by
    have h1 : (n : G) ∈ F := Subgroup.mem_subgroupOf.1 hn
    exact Subgroup.mem_subgroupOf.2 (hnorm g g.2 n h1)⟩
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hF
    rw [eq_bot_iff]
    intro f hf
    have : (⟨f, hFP hf⟩ : ↥P) ∈ H := Subgroup.mem_subgroupOf.2 hf
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set X : Subgroup ↥P := H ⊓ Subgroup.center ↥P with hXdef
  have hXp : IsPGroup 2 ↥X := hP.to_subgroup X
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hXp
  have hn1 : n ≠ 0 := by
    rintro rfl
    have : Nat.card ↥X = 1 := by simpa using hn
    exact hX (Subgroup.card_eq_one.1 this)
  have hdvd : 2 ∣ Nat.card ↥X := by
    rw [hn]
    exact dvd_pow_self 2 hn1
  obtain ⟨⟨z', hz'X⟩, hz'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 hdvd
  have hz'o : orderOf z' = 2 := by
    have := hz'
    rwa [Subgroup.orderOf_mk] at this
  refine ⟨(z' : G), Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hz'X).1, ?_, fun p hp => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hz'o
  · have := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hz'X).2 ⟨p, hp⟩
    exact congrArg Subtype.val this

end Central

end S3Sec29C

end CFSG.GH74.Generic.BProg.B3
