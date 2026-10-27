module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcF4TwoTorus
import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.KE

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem false_of_sylowTorus (h : QSNL 5 S B T x D K) (hZ : Subgroup.center ↥K = ⊥)
    (hH : ∃ H : Subgroup Ω, H ≤ K ∧ (∀ g ∈ H, g ^ 5 = 1) ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a)
    {R : Type} [Group R] (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) {m : ℕ} (hT : SylowTorus R 5 m) :
    False := by
  obtain ⟨H, hHK, hH5, a, ha, b, hb, hab⟩ := hH
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := h.cfg.std
  have hKS : K ≤ S := hKcomp.1.trans inf_le_left
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥S →* R, ∀ s, φ s = θ (s : ↥S ⧸ Subgroup.center ↥S) :=
    ⟨θ.toMonoidHom.comp (QuotientGroup.mk' _), fun _ => rfl⟩
  have hP : IsPGroup 5 ((H.subgroupOf S).map φ) := by
    rintro ⟨_, s, hs, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hs5 : s ^ 5 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hH5 _ (Subgroup.mem_subgroupOf.1 hs))
    change φ s ^ 5 ^ 1 = 1
    rw [pow_one, ← map_pow, hs5, map_one]
  set a' : ↥S := ⟨a, hKS (hHK ha)⟩
  set b' : ↥S := ⟨b, hKS (hHK hb)⟩
  have hcomm : φ a' * φ b' = φ b' * φ a' :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.mul_comm_of_sylowTorus hT hP
      (Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.2 ha))
      (Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.2 hb))
  have hc : a' * b' * (b' * a')⁻¹ ∈ Subgroup.center ↥S := by
    have h1 : φ (a' * b' * (b' * a')⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hcomm, mul_inv_cancel]
    rwa [hφ, map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h1
  have hcK : a * b * (b * a)⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (hHK ha) (hHK hb)) (K.inv_mem (K.mul_mem (hHK hb) (hHK ha)))
  have hcZ : (⟨_, hcK⟩ : ↥K) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 fun k => by
    have e := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨k, hKS k.2⟩)
    exact Subtype.ext e
  rw [hZ, Subgroup.mem_bot] at hcZ
  have h1 : a * b * (b * a)⁻¹ = 1 := congrArg Subtype.val hcZ
  exact hab (mul_inv_eq_one.1 h1)

private theorem orderOf_five_of_dvd_add_one {n : ℕ} (h5 : 5 ∣ n + 1) :
    orderOf (n : ZMod 5) = 2 := by
  rw [← ZMod.natCast_mod, show n % 5 = 4 by omega]
  exact orderOf_eq_prime (by decide) (by decide)

section Cert


theorem sylowTorus_E6_five_of_dvd_add_one (F : Type) [Field F] [Finite F]
    (h5 : 5 ∣ Nat.card F + 1) : SylowTorus (adjointGroup .E6 F) 5 4 :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.sylowTorus_of_blocks_of_three_lt 3
    (Or.inl ⟨rfl, rfl⟩) F Nat.prime_five (by norm_num) (by omega)
    (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2] e6Two_charpoly e6Two_pow
    (orderOf_five_of_dvd_add_one h5) (by decide) (by decide) (by decide)

theorem sylowTorus_F4_five_of_dvd_sub_one (F : Type) [Field F] [Finite F]
    (h5 : 5 ∣ Nat.card F - 1) : SylowTorus (adjointGroup .F4 F) 5 4 := by
  have := Fact.mk Nat.prime_five
  have : Finite (adjointGroup .F4 F) := generated_group_finite .F4 F
  set H := (torusGroup .F4 F).subgroupOf (adjointGroup .F4 F)
  have hHc : IsMulCommutative H := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup a.2)
      (torusGroup_le_diagonalGroup b.2)))⟩⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 H))
  have hPp : IsPGroup 5 ((P : Subgroup H).map H.subtype) := P.isPGroup'.map _
  have hPidx : ¬ 5 ∣ ((P : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with hdvd | hdvd
    · exact P.not_dvd_index hdvd
    · exact CFSG.StandardType.TableBF4.not_dvd_index_torusGroup Nat.prime_five le_rfl h5 hdvd
  refine SylowTorus.of_sylow_le hHc (hPp.toSylow hPidx) (Subgroup.map_subtype_le _) ?_
  have he : torsionSubgroup H hHc 5 = CFSG.StandardType.TableBF4.torusPow F 5 :=
    Subgroup.ext fun _ => Iff.rfl
  rw [he, CFSG.StandardType.TableBF4.card_torusPow Nat.prime_five h5]

theorem sylowTorus_F4_five_of_dvd_add_one (F : Type) [Field F] [Finite F]
    (h5 : 5 ∣ Nat.card F + 1) : SylowTorus (adjointGroup .F4 F) 5 4 :=
  CFSG.StandardType.OrdPInnerExc.sylowTorus_F4_two F Nat.prime_five (by norm_num)
    (orderOf_five_of_dvd_add_one h5)

end Cert

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
