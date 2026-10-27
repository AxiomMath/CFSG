module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCMat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCExtra
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSOutModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSVPairs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

section Row


theorem co1_quot2Data : Quot2Data (triHom : C₁ →* Equiv.Perm (Fin 1365)) twoBD where
  D_le := twoBD_le_range
  range_le := range_le
  simple := isSimpleGroup_twoBD
  noncomm := ⟨xD, yD, xD_yD_ne⟩
  index_two := exists_card_range
  ker_two := exists_card_ker
  big := by
    obtain ⟨t, -, h8⟩ := exists_card_range_ker
    have hk : Nat.card (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker ≤ 8 :=
      Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ h8)
    calc (Nat.card (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker).factorial ≤ (8 : ℕ).factorial :=
          Nat.factorial_le hk
      _ < Nat.card twoBD := by
          rw [card_twoBD]
          norm_num [Nat.factorial]

theorem twoAdic_twoBD : twoAdic twoBD = 12 := by
  unfold twoAdic
  rw [card_twoBD, show (251596800 : ℕ) = 2 ^ 12 * 61425 by norm_num]
  exact factorization_two_pow_mul 12 (by norm_num) (by norm_num)

@[expose] def co1E : Subgroup GL24 := GA ⊓ Subgroup.centralizer {A₁}

@[expose] def co1Back : ↥co1E →* C₁ where
  toFun e := liftC e.1 e.2
  map_one' := ιC_injective (by
    show (1 : GL24) = ιC 1
    rw [map_one])
  map_mul' e e' := ιC_injective (by
    show (e * e' : ↥co1E).1 = ιC (liftC e.1 e.2 * liftC e'.1 e'.2)
    rw [map_mul]
    rfl)

theorem co1Back_bijective : Function.Bijective co1Back := by
  refine ⟨fun a b h => Subtype.ext ?_, fun c => ⟨⟨ιC c, coe_mem_C₁ c⟩, ?_⟩⟩
  · have := congrArg ιC h
    exact this
  · apply ιC_injective
    rfl

@[expose] def co1Phi : ↥co1E →* Equiv.Perm (Fin 1365) := triHom.comp co1Back

theorem Quot2Data.comp_bijective {C C' Y : Type*} [Group C] [Group C'] [Group Y] {φ : C →* Y}
    {D : Subgroup Y} (h : Quot2Data φ D) (ζ : C' →* C) (hζ : Function.Bijective ζ) :
    Quot2Data (φ.comp ζ) D :=
  h.comp_equiv (MulEquiv.ofBijective ζ hζ)

theorem co1A_pow' : ((co1A : GA) : GL24) ^ 5 = 1 := by
  have := congrArg Subtype.val co1A_pow
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at this

theorem co1B_pow' : ((co1B : GA) : GL24) ^ 5 = 1 := by
  have := congrArg Subtype.val co1B_pow
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at this

theorem co1_outModel : Nonempty (OutRowModel (GA : Subgroup GL24) co1E co1Phi twoBD A₁) := by
  obtain ⟨Z, l, hZ, hZcl, hZZ, hZ1, hlG, hl, hgen, hnc, S, hSD, hScard, hSζ, hSfuse⟩ :=
    co1_mat_facts
  have hS : Nat.card S = 2 ^ twoAdic twoBD := by
    rw [hScard, twoAdic_twoBD]
    norm_num
  have hxx : xBar * xBar = 1 := by
    rw [← sq, ← orderOf_xBar]
    exact pow_orderOf_eq_one _
  have hy1 : yBar ≠ 1 := by
    intro h
    have := orderOf_yBar
    rw [h, orderOf_one] at this
    omega
  have hcl : Subgroup.closure {triHom (⟨co1A, co1A_mem⟩ : C₁), triHom (⟨co1B, co1B_mem⟩ : C₁)} =
      twoBD := by
    rw [triHom_co1A, triHom_co1B]
    exact closure_pair_eq_of_simple hxx hy1 isSimpleGroup_twoBD
  refine ⟨{
    quot := co1_quot2Data.comp_bijective co1Back co1Back_bijective
    A := ((co1A : GA) : GL24)
    B := ((co1B : GA) : GL24)
    z := Z
    l := l
    t_mem := A₁_mem
    E_iff := ?_
    A_mem := co1A_memE
    B_mem := co1B_memE
    A_odd := ?_
    B_odd := ?_
    gen_card := ?_
    z_mem := hZcl
    z_sq := hZZ
    z_ne := hZ1
    z_two := ?_
    l_mem := hlG
    l_conj := hl
    gen := hgen
    z_not_conj := hnc
    D_fuse := twoCentralFused_of_sylow hSD hS hSfuse }⟩
  · intro y
    rw [co1E, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  · exact Odd.of_dvd_nat (by decide : Odd 5) (orderOf_dvd_of_pow_eq_one
      (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact co1A_pow')))
  · exact Odd.of_dvd_nat (by decide : Odd 5) (orderOf_dvd_of_pow_eq_one
      (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact co1B_pow')))
  · have h2 : Subgroup.closure {co1Phi ⟨((co1A : GA) : GL24), co1A_memE⟩,
        co1Phi ⟨((co1B : GA) : GL24), co1B_memE⟩} = twoBD := hcl
    rw [h2]
  · intro hz _
    exact twoAdic_le_of_sylow_centralizer hSD hS (fun x hx => hSζ x hx)

end Row

end CFSG.EvenSporadicStandard.Solomon78
