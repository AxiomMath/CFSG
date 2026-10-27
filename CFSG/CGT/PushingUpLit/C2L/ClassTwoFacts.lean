module

public import CFSG.CGT.PushingUpLit.C2L.LemmaM
public import CFSG.CGT.PushingUpLit.T2KSW.WCoverChain

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement
open T2KSW.Aux

theorem classLETwo_map_conj {G : Type} [Group G] {T : Subgroup G} (h : ClassLETwo T) (g : G) :
    ClassLETwo (T.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
  have h1 := h a ha b hb c hc
  calc ⁅⁅(MulAut.conj g).toMonoidHom a, (MulAut.conj g).toMonoidHom b⁆,
        (MulAut.conj g).toMonoidHom c⁆ = (MulAut.conj g).toMonoidHom ⁅⁅a, b⁆, c⁆ := by
        simp only [map_commutatorElement]
    _ = 1 := by rw [h1, map_one]

namespace ClassTwoSetup

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}
variable (hc : ClassTwoSetup G L M T n)
include hc

theorem ZR_le_oTwoIn : ZR L T ≤ oTwoIn L := by
  intro z hz
  obtain ⟨hzR, hzc⟩ := mem_ZR.1 hz
  have hzD : z ∈ Dc L T := ⟨hzR.1, Subgroup.mem_centralizer_iff.2 fun v hv =>
    hzc v (blockU_le_Rl hc.LM hc.MN hc.hT hv)⟩
  rw [← Rl_inf_Dc hc.natBlock hc.LM hc.MN hc.hT]
  exact ⟨hzR, hzD⟩

theorem Ec_inf_blockU : Ec L T ⊓ blockU L = blockZ L := by
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx =>
    ⟨⟨NatBlock.blockU_le_sylow hc.LM hc.MN hc.hT hx.1, hx.2⟩, hx.1⟩⟩

theorem ZT_eq_ZR_sup_Ec : ZT T = ZR L T ⊔ Ec L T := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzT, hzc⟩ := mem_ZT.1 hz
    exact hc.facts.cent_R_le ⟨hzT, Subgroup.mem_centralizer_iff.2 fun r hr => (hzc r (Rl_le_T hr))⟩
  · exact sup_le hc.facts.ZR_le hc.EZ

theorem Ec_le_normalizer_of_le {S : Subgroup G} (hS : S ≤ T) :
    Ec L T ≤ Subgroup.normalizer (S : Set G) := fun e he => by
  have hcomm : ∀ e ∈ Ec L T, ∀ y ∈ T, e * y * e⁻¹ = y := fun e he y hy => by
    rw [← (mem_ZT.1 (hc.EZ he)).2 y hy]
    simp
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [hcomm e he z (hS hz)]
    exact hz
  · intro hz
    have hy : e * z * e⁻¹ ∈ T := hS hz
    have h2 := hcomm e⁻¹ ((Ec L T).inv_mem he) _ hy
    have h3 : e⁻¹ * (e * z * e⁻¹) * e⁻¹⁻¹ = z := by group
    rw [h3] at h2
    rw [h2]
    exact hz

theorem mul_self_of_mem_blockU_sup_Ec : ∀ x ∈ blockU L ⊔ Ec L T, x * x = 1 := by
  intro x hx
  obtain ⟨v, hv, e, he, rfl⟩ :=
    (mem_sup_iff_mul (blockU_le_normalizer_Ec hc.LM hc.MN hc.hT)).1 hx
  have hv2 : v * v = 1 := by
    simpa [pow_two] using hc.natBlock.isElemAbelian_blockU.2 v hv
  have he2 : e * e = 1 := by simpa [pow_two] using hc.sec4.S_elem.2 e he
  have hve : v * e = e * v := Subgroup.mem_centralizer_iff.1 he.2 v (blockU_le L hv)
  calc v * e * (v * e) = v * (e * v) * e := by group
    _ = v * (v * e) * e := by rw [← hve]
    _ = (v * v) * (e * e) := by group
    _ = 1 := by rw [hv2, he2, one_mul]

theorem ZT_le_blockU_sup_Ec (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) :
    ZT T ≤ blockU L ⊔ Ec L T := by
  rw [hc.ZT_eq_ZR_sup_Ec]
  exact sup_le (hc.ZR_le_oTwoIn.trans hWVE) le_sup_right

theorem elem_ZT (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) : ∀ z ∈ ZT T, z * z = 1 :=
  fun z hz => hc.mul_self_of_mem_blockU_sup_Ec z (hc.ZT_le_blockU_sup_Ec hWVE hz)

theorem card_blockU_sup_Ec :
    Nat.card ↥(blockU L ⊔ Ec L T) = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by
  have hEn : Ec L T ≤ Subgroup.normalizer (blockU L : Set G) :=
    (Ec_le_T.trans hc.TM).trans (NatBlock.le_normalizer_blockU_of_le hc.MN)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hEn
  rw [inf_comm, hc.Ec_inf_blockU, hc.natBlock.card_blockU] at h1
  have hpos : 0 < Nat.card ↥(blockZ L) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

theorem card_ZT (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) :
    Nat.card ↥(ZT T) = 2 ^ n * Nat.card ↥(Ec L T) := by
  obtain ⟨H, hA⟩ := exists_utri_coord hc.natBlock hc.LM hc.MN hc.hT
  have hZR := ZR_eq_ellTilde_sup H hc.hT hA hWVE
  have hZT : ZT T = ellTilde H.D ⊔ Ec L T := by
    rw [hc.ZT_eq_ZR_sup_Ec, hZR]
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
    · exact sup_le_sup_right le_sup_left _
  have hℓV : ellTilde H.D ≤ blockU L := ellTilde_le_blockU _
  have hℓT : ellTilde H.D ≤ T := hℓV.trans (NatBlock.blockU_le_sylow hc.LM hc.MN hc.hT)
  have hℓE : ellTilde H.D ⊓ Ec L T = blockZ L := by
    apply le_antisymm
    · intro x ⟨hxℓ, hxE⟩
      rw [← hc.Ec_inf_blockU]
      exact ⟨hxE, hℓV hxℓ⟩
    · intro v hv
      have hvE : v ∈ Ec L T ⊓ blockU L := by rw [hc.Ec_inf_blockU]; exact hv
      refine ⟨⟨blockZ_le_blockU L hv, ?_⟩, hvE.1⟩
      rw [(H.D.ψe_eq_zero_iff (blockZ_le_blockU L hv)).2 hv]
      rfl
  have h1 := card_sup_mul_card_inf_of_le_normalizer (hc.Ec_le_normalizer_of_le hℓT)
  rw [hℓE, ← hZT] at h1
  have hcard : Nat.card ↥(ellTilde H.D) = 2 ^ n * Nat.card ↥(blockZ L) := by
    have h2 := card_ellTilde_mul H.nat H.D
    rw [H.nat.card_blockU, sq] at h2
    have hpos : 0 < 2 ^ n := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h2]
    ring
  rw [hcard] at h1
  have hpos : 0 < Nat.card ↥(blockZ L) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

end ClassTwoSetup

end CFSG.CGT.PushingUpLit.C2L
