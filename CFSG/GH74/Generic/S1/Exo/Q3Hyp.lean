module

public import CFSG.GH74.Generic.S1.Exo.Q3Chain
public import CFSG.GH74.Generic.S1.Exo.Q3Bal
public import CFSG.GH74.Generic.S1.Exo.Nb3Defs

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
  CFSG.Assembly.LowTwoRank CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

omit [Finite G] in
theorem le_bot_of_le_barSub_bot {c : G} {M : Subgroup (CentralizerBar c)}
    (h : M ≤ S45.barSub c (⊥ : Subgroup G)) : M = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨g, hg, hgb, rfl⟩ := S45.mem_barSub.1 (h hm)
  have : g = 1 := hgb
  have h1 : (⟨g, hg⟩ : ↥(centralizer ({c} : Set G))) = 1 := Subtype.ext this
  rw [Subgroup.mem_bot, h1, map_one]

theorem nbhd3Hyp_of_classical (hSB : Balance.SolvableL2PrimeBalance) (hF : Nat.card F = 3) {x c : G}
    (D : LayerData x (StatedSL 4 F)) (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hgen : Gen4 G) (hkgh : KGH G) (hx : orderOf x = 2) (hxK : xbar x ∈ D.K)
    (hDc : D.ι (linZ0 F) = c) (hc2 : orderOf c = 2) (hcx : c ≠ x) :
    ∃ (y : CentralizerBar c) (JA JB : Subgroup (CentralizerBar c)),
      Nbhd3Hyp (CentralizerBar c) (xbar c) y JA JB := by
  classical
  have hcC : c ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hcx' : c ∈ centralizer ({x} : Set G) := hDc ▸ D.ι_mem_cent _
  have hxc : x ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2
    (mem_centralizer_singleton_iff.1 hcx').symm
  have hxcC : x * c ∈ centralizer ({c} : Set G) := Subgroup.mul_mem _ hxc hcC
  have hc2' : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hx2' : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc2
    omega
  have hcomm : x * c = c * x := (mem_centralizer_singleton_iff.1 hcx').symm
  have hxc2 : (x * c) * (x * c) = 1 := by
    calc x * c * (x * c) = x * (c * x) * c := by group
      _ = x * (x * c) * c := by rw [← hcomm]
      _ = (x * x) * (c * c) := by group
      _ = 1 := by rw [hx2', hc2', one_mul]
  have hxc1 : x * c ≠ 1 := by
    intro h
    have : x = c⁻¹ := eq_inv_of_mul_eq_one_left h
    apply hcx
    rw [this]
    exact eq_inv_of_mul_eq_one_left hc2'
  have hBA := blkA3_le_cent D hDc
  have hBB := blkB3_le_cent D hDc
  have hBAx := blkA3_le_centY D (y := x)
  have hBBx := blkB3_le_centY D (y := x)
  have hcA := c_mem_blkA3 D hDc
  have hycB := yc_mem_blkB3 D hF hDc hx hxK
  have hcenA := blkA3_center_eq D hF hDc hc1
  have hcenB := blkB3_center_eq D hF hDc hx hxK hxc1
  have hinjA := blkA3_proj_inj D hF hDc
  have hinjB := blkB3_proj_inj D hF hDc
  have hcenterB := yc_mem_center_blkB3 D hF hDc hx hxK
  set ybar : CentralizerBar c := proj c ⟨x * c, hxcC⟩ with hybar
  have hwy : xbar c * ybar = proj c ⟨x, hxc⟩ := by
    change proj c ⟨c, hcC⟩ * proj c ⟨x * c, hxcC⟩ = proj c ⟨x, hxc⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change c * (x * c) = x
    calc c * (x * c) = (c * x) * c := by rw [mul_assoc]
      _ = (x * c) * c := by rw [← hcomm]
      _ = x * (c * c) := by rw [mul_assoc]
      _ = x := by rw [hc2', mul_one]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hybar_sq : ybar * ybar = 1 := by
    rw [hybar, ← map_mul]
    have : (⟨x * c, hxcC⟩ : ↥(centralizer ({c} : Set G))) * ⟨x * c, hxcC⟩ = 1 := Subtype.ext hxc2
    rw [this, map_one]
  have hybar_ne : ybar ≠ 1 := fun h => hxc1 (S45.eq_one_of_proj_eq_one_of_sq hxcC h hxc2)
  have hw_ne_y : xbar c ≠ ybar := by
    intro h
    have h1 : proj c ⟨x, hxc⟩ = 1 := by
      rw [← hwy, ← h]
      exact xbar_mul_self hc2
    exact hx1 (S45.eq_one_of_proj_eq_one_of_sq hxc h1 hx2')
  obtain ⟨σ⟩ := sl2_equiv_zmod3 (F₀ := F) hF
  have hJrA : blkA3 D ≤ D.ι.range := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hJrB : blkB3 D ≤ D.ι.range := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hbalA := solv_balance_barC hSB hxc hx hBA hBAx hinjA
    (subnormal_of_normalized D hxc hBA hJrA (fun s hs j hj => blkA3_normalized D hF hDc s hs j hj))
    ⟨(blkA3_equiv D).symm.trans σ⟩ (blkA3_odd_free D hF)
  have hbalB := solv_balance_barC hSB hxc hx hBB hBBx hinjB
    (subnormal_of_normalized D hxc hBB hJrB (fun s hs j hj => blkB3_normalized D hF hDc s hs j hj))
    ⟨(blkB3_equiv D).symm.trans σ⟩ (blkB3_odd_free D hF)
  refine ⟨ybar, S45.barSub c (blkA3 D), S45.barSub c (blkB3 D), ?_⟩
  refine
    { core := barC_core
      gen4 := barC_gen4 hgen
      kgroup := barC_kgroup hs hn hkgh hc2
      gh := barC_gh hs hn hkgh hc2
      c_central := fun h => xbar_comm c h
      c_sq := xbar_mul_self hc2
      c_ne_one := xbar_ne_one hc2
      y_sq := hybar_sq
      y_ne_one := hybar_ne
      c_ne_y := hw_ne_y
      c_mem := S45.proj_mem_barSub hcC hcA
      y_mem := S45.proj_mem_barSub hxcC hycB
      y_cent := ?_
      sl2A := barSub_hasSL2Model_of_inj hBA hinjA hF (blkA3_equiv D)
      sl2B := barSub_hasSL2Model_of_inj hBB hinjB hF (blkB3_equiv D)
      centA := barSub_cent_of_inj hBA hinjA hcA hc2' hc1 hcenA
      centB := barSub_cent_of_inj hBB hinjB hycB hxc2 hxc1 hcenB
      comm := ?_
      perfect_free := ?_
      balA := hbalA
      balB := hbalB }
  · intro b hb
    obtain ⟨g, hg, hgB, rfl⟩ := S45.mem_barSub.1 hb
    rw [hybar, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_center_iff.1 hcenterB ⟨g, hgB⟩
    exact (congrArg Subtype.val this).symm
  · intro a ha b hb
    obtain ⟨g, hg, hgA, rfl⟩ := S45.mem_barSub.1 ha
    obtain ⟨g', hg', hgB', rfl⟩ := S45.mem_barSub.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact blkA3_comm_blkB3 D g hgA g' hgB'
  · intro M hM hMc
    rw [hwy] at hMc
    have h1 := perfect_le_barSub_resCent hxc hx2' hM hMc
    rw [resCent_eq_bot_q3 D hF hDc] at h1
    exact le_bot_of_le_barSub_bot h1

end CFSG.GH74.Generic.S1.Exo
