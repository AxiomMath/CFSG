module

public import CFSG.CGT.PushingUpLit.C2L.GomiMax
public import CFSG.CGT.PushingUpLit.T2KSW.ClassThreeWC
import CFSG.CGT.PushingUpLit.E3A.Borel
import CFSG.CGT.PushingUpLit.T2K.SixD
import CFSG.CGT.PushingUpLit.A78.OppSL2

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement
open T2KSW.Aux

theorem sylow_of_isSylowOf_top {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) : ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  have h := isSylowOf_iff.1 hT
  exact ⟨h.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using h.2.2), rfl⟩

structure ClassTwoSetup (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) : Prop where
  sec4 : Sec4 G L M T n
  MN : M ≤ Subgroup.normalizer (L : Set G)
  ME : M ≤ Subgroup.normalizer (Ec L T : Set G)
  ne_bot : Ec L T ≠ ⊥
  facts : RDFacts L T
  hRD : T ≤ Rl L T ⊔ Dc L T
  class2 : ClassLETwo T
  EZ : Ec L T ≤ ZT T

namespace ClassTwoSetup

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

section Basic

variable (hc : ClassTwoSetup G L M T n)
include hc

theorem natBlock : NatBlock L n := hc.sec4.hyp.natBlock

theorem LM : L ≤ M := hc.sec4.hyp.le

theorem hT : IsSylowOf 2 T M := hc.sec4.sylow

theorem TM : T ≤ M := hc.sec4.sylow.le

theorem eq_bot_of_normal_odd {K : Subgroup G} (hKM : K ≤ M)
    (hKn : M ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) : K = ⊥ := by
  have hloc : CFSG.Assembly.IsTwoLocal M := hc.sec4.hyp.maxLocal.1
  have h1 := hc.sec4.hyp.charTwo M hloc
  rw [assembly_pCoreOf_two_eq_oTwoIn] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (isPGroup_oTwoIn M)
  have hdisj : Disjoint K (oTwoIn M) := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd))
  have hKC : K ≤ Subgroup.centralizer (oTwoIn M : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hoM : o ∈ M := (oTwoIn_le M) ho
    have h2 : ⁅x, o⁆ ∈ K := by
      have : o * x⁻¹ * o⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hKn hoM) x⁻¹).1 (K.inv_mem hx)
      have e : ⁅x, o⁆ = x * (o * x⁻¹ * o⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact K.mul_mem hx this
    have h3 : ⁅x, o⁆ ∈ oTwoIn M := by
      have : x * o * x⁻¹ ∈ oTwoIn M := conj_mem_oTwoIn (Subgroup.le_normalizer (hKM hx)) ho
      have e : ⁅x, o⁆ = (x * o * x⁻¹) * o⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (oTwoIn M).mul_mem this ((oTwoIn M).inv_mem ho)
    have h4 : ⁅x, o⁆ = 1 := by
      have := Subgroup.disjoint_def.1 hdisj h2 h3
      exact this
    have := commutatorElement_eq_one_iff_mul_comm.1 h4
    exact this.symm
  have hKO : K ≤ oTwoIn M := fun x hx => h1 (Subgroup.mem_inf.2 ⟨hKM hx, hKC hx⟩)
  exact ClassThree.eq_bot_of_isPGroup_of_le_of_odd ((isPGroup_oTwoIn M).to_le hKO) le_rfl hodd

theorem le_normalizer_C0 :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  fun _ hm => mem_normalizer_inf (Subgroup.le_normalizer hm)
    (mem_normalizer_centralizer_of_le hc.MN hm)

theorem isSylowOf_Ec_C0 :
    IsSylowOf 2 (Ec L T) (M ⊓ Subgroup.centralizer (L : Set G)) := by
  have := hc.hT.inf_of_le_normalizer (N := M ⊓ Subgroup.centralizer (L : Set G)) inf_le_left
    hc.le_normalizer_C0
  have e : T ⊓ (M ⊓ Subgroup.centralizer (L : Set G)) = Ec L T := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxT, -, hxC⟩
      exact ⟨hxT, hxC⟩
    · rintro ⟨hxT, hxC⟩
      exact ⟨hxT, hc.TM hxT, hxC⟩
  rwa [e] at this

theorem C0_inf_centralizer_Ec :
    (M ⊓ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.centralizer (Ec L T : Set G) = Ec L T := by
  set Z : Subgroup G := (M ⊓ Subgroup.centralizer (L : Set G)) ⊓
    Subgroup.centralizer (Ec L T : Set G) with hZ
  have hE_abel : ∀ e ∈ Ec L T, ∀ e' ∈ Ec L T, e * e' = e' * e := fun e he e' he' =>
    congrArg Subtype.val (hc.sec4.S_elem.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
  have hEZ : Ec L T ≤ Z := fun e he =>
    ⟨⟨hc.TM he.1, he.2⟩, Subgroup.mem_centralizer_iff.2 fun e' he' => hE_abel e' he' e he⟩
  have hZM : Z ≤ M := inf_le_left.trans inf_le_left
  have hEsyl : IsSylowOf 2 (Ec L T) Z := hc.isSylowOf_Ec_C0.of_le hEZ inf_le_left
  have hZn : M ≤ Subgroup.normalizer (Z : Set G) := fun m hm =>
    mem_normalizer_inf (hc.le_normalizer_C0 hm) (mem_normalizer_centralizer (hc.ME hm))
  obtain ⟨P, hP⟩ := hEsyl.exists_sylow_eq_subgroupOf
  have hcent : ∀ z : ↥Z, ∀ e ∈ (P : Subgroup ↥Z), e * z = z * e := by
    intro z e he
    rw [hP] at he
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 z.2.2 (e : G) he)
  have hPn : Subgroup.normalizer (P : Set ↥Z) ≤ Subgroup.centralizer (P : Set ↥Z) := fun z _ =>
    Subgroup.mem_centralizer_iff.2 fun e he => hcent z e he
  set φ : ↥Z →* ↥P := MonoidHom.transferSylow P hPn with hφ
  have hker_odd : Odd (Nat.card φ.ker) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (MonoidHom.not_dvd_card_ker_transferSylow P hPn))
  have hodd_ker : ∀ z : ↥Z, Odd (orderOf z) → z ∈ φ.ker := by
    intro z hz
    obtain ⟨j, hj⟩ := P.isPGroup' (φ z)
    have h1 : orderOf (φ z) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have h2 : orderOf (φ z) ∣ orderOf z := orderOf_map_dvd φ z
    have hcop : Nat.gcd (2 ^ j) (orderOf z) = 1 :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hz)
    have h3 : orderOf (φ z) ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  set Ko : Subgroup G := φ.ker.map Z.subtype with hKo
  have hKoodd : Odd (Nat.card Ko) := by
    rw [hKo, Subgroup.card_map_of_injective Z.subtype_injective]
    exact hker_odd
  have hKoM : Ko ≤ M := (Subgroup.map_subtype_le _).trans hZM
  have hKon : M ≤ Subgroup.normalizer (Ko : Set G) := by
    have key : ∀ m ∈ M, ∀ x ∈ Ko, m * x * m⁻¹ ∈ Ko := by
      intro m hm x hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hy : m * (k : G) * m⁻¹ ∈ Z := by
        have := (Subgroup.mem_normalizer_iff.1 (hZn hm) (k : G)).1 k.2
        exact this
      have hord : Odd (orderOf (⟨m * (k : G) * m⁻¹, hy⟩ : ↥Z)) := by
        have h1 : orderOf (⟨m * (k : G) * m⁻¹, hy⟩ : ↥Z) = orderOf (k : G) := by
          rw [← Subgroup.orderOf_coe]
          exact (MulAut.conj m).orderOf_eq (k : G)
        rw [h1]
        have h2 : orderOf (k : G) ∣ Nat.card Ko :=
          Subgroup.orderOf_dvd_natCard Ko ⟨k, hk, rfl⟩
        exact Odd.of_dvd_nat hKoodd h2
      exact ⟨⟨m * (k : G) * m⁻¹, hy⟩, hodd_ker _ hord, rfl⟩
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key m hm y, fun hy => ?_⟩
    have := key m⁻¹ (M.inv_mem hm) _ hy
    simpa [mul_assoc] using this
  have hKo1 : Ko = ⊥ := hc.eq_bot_of_normal_odd hKoM hKon hKoodd
  have hker1 : φ.ker = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ Z.subtype_injective).1 hKo1
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker1
  have hZ2 : IsPGroup 2 ↥Z := P.isPGroup'.of_injective φ hinj
  exact hEsyl.eq_of_le hEZ le_rfl hZ2

end Basic

section Dnormal

variable (hc : ClassTwoSetup G L M T n)
include hc

theorem Dc_isPGroup : IsPGroup 2 ↥(Dc L T) := hc.hT.isPGroup.to_le Dc_le_T

theorem Dc_ne_bot : Dc L T ≠ ⊥ := fun h =>
  hc.sec4.hyp.blockU_ne_bot
    (le_bot_iff.1 (h ▸ blockU_le_Dc hc.natBlock hc.LM hc.MN hc.hT))

theorem Dc_le_centralizer_Ec : Dc L T ≤ Subgroup.centralizer (Ec L T : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.2 fun _ he => ((mem_ZT.1 (hc.EZ he)).2 x hx.1).symm

theorem Dc_eq_inf_centralizer_Ec :
    Dc L T = (M ⊓ Subgroup.centralizer (blockU L : Set G)) ⊓
      Subgroup.centralizer (Ec L T : Set G) := by
  apply le_antisymm
  · intro x hx
    exact ⟨⟨hc.TM hx.1, hx.2⟩, hc.Dc_le_centralizer_Ec hx⟩
  · rintro x ⟨hxQ, hxE⟩
    rw [Qc_eq_Dc_sup hc.natBlock hc.MN hc.hT] at hxQ
    have hDn : Dc L T ≤ Subgroup.normalizer
        ((M ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
      (Dc_le_T.trans hc.TM).trans hc.le_normalizer_C0
    obtain ⟨d, hd, c, hc0, rfl⟩ := (mem_sup_iff_mul hDn).1 hxQ
    have hcE : c ∈ Subgroup.centralizer (Ec L T : Set G) := by
      have := (Subgroup.centralizer (Ec L T : Set G)).mul_mem
        ((Subgroup.centralizer (Ec L T : Set G)).inv_mem (hc.Dc_le_centralizer_Ec hd)) hxE
      simpa using this
    have hcEc : c ∈ Ec L T := by
      rw [← hc.C0_inf_centralizer_Ec]
      exact ⟨hc0, hcE⟩
    exact (Dc L T).mul_mem hd (Ec_le_Dc hcEc)

theorem M_le_normalizer_Dc : M ≤ Subgroup.normalizer (Dc L T : Set G) := by
  intro m hm
  rw [hc.Dc_eq_inf_centralizer_Ec]
  exact mem_normalizer_inf (NatBlock.le_normalizer_centralizer hc.MN hm)
    (mem_normalizer_centralizer (hc.ME hm))

theorem oTwoIn_le_cenW {N : Subgroup G} (hLN : L ≤ N) (hNM : N ≤ M) :
    oTwoIn N ≤ cenW L M := by
  intro x hx
  have hxN : x ∈ N := oTwoIn_le N hx
  refine mem_cenW.2 ⟨hNM hxN, hc.MN (hNM hxN), fun l hl => ?_⟩
  have h1 : ⁅x, l⁆ ∈ oTwoIn N := by
    have : l * x⁻¹ * l⁻¹ ∈ oTwoIn N :=
      conj_mem_oTwoIn (Subgroup.le_normalizer (hLN hl)) ((oTwoIn N).inv_mem hx)
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact (oTwoIn N).mul_mem hx this
  have h2 : ⁅x, l⁆ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (hc.MN (hNM hxN)) l).1 hl
    have e : ⁅x, l⁆ = (x * l * x⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact L.mul_mem this (L.inv_mem hl)
  have hnorm : L ≤ Subgroup.normalizer ((oTwoIn N ⊓ L : Subgroup G) : Set G) := fun l' hl' =>
    mem_normalizer_inf (le_normalizer_oTwoIn N (hLN hl')) (Subgroup.le_normalizer hl')
  have hle : oTwoIn N ⊓ L ≤ oTwoIn L :=
    le_oTwoIn_of_normal inf_le_right hnorm ((isPGroup_oTwoIn N).to_le inf_le_left)
  exact hle ⟨h1, h2⟩

theorem oTwoIn_eq_Dc {N : Subgroup G} (hLN : L ≤ N) (hTN : T ≤ N) (hNM : N ≤ M) :
    oTwoIn N = Dc L T := by
  apply le_antisymm
  · have h1 : oTwoIn N ≤ T := oTwoIn_le_of_isSylowOf (hc.hT.of_le hTN hNM)
    rw [Dc_eq_inf_cenW hc.natBlock hc.MN hc.hT]
    exact le_inf h1 (hc.oTwoIn_le_cenW hLN hNM)
  · exact le_oTwoIn_of_normal (Dc_le_T.trans hTN) (fun x hx => hc.M_le_normalizer_Dc (hNM hx))
      hc.Dc_isPGroup

theorem oTwoIn_M_eq_Dc : oTwoIn M = Dc L T := hc.oTwoIn_eq_Dc hc.LM hc.TM le_rfl

theorem oTwoIn_sup_eq_Dc : oTwoIn (L ⊔ T) = Dc L T :=
  hc.oTwoIn_eq_Dc le_sup_left le_sup_right (sup_le hc.LM hc.TM)

theorem normalizer_Dc_eq : Subgroup.normalizer (Dc L T : Set G) = M := by
  by_contra hne
  have hlt : M < Subgroup.normalizer (Dc L T : Set G) :=
    lt_of_le_of_ne hc.M_le_normalizer_Dc (Ne.symm hne)
  exact hc.sec4.hyp.maxLocal.2 _ hlt ⟨Dc L T, hc.Dc_ne_bot, hc.Dc_isPGroup, rfl⟩

theorem not_twoClosed_M : ¬ TwoClosed M := by
  intro h2
  have hu := twoClosed_iff_forall_eq.1 h2
  obtain ⟨S, hS, hMS⟩ := h2
  have hST : S = T := hu S T hS hc.hT
  obtain ⟨S', hS'⟩ := sylow_of_isSylowOf_top hc.sec4.sylowG
  have hsolv := E3A.isSolvable_normalizer_sylow S'
  have hLT : L ≤ Subgroup.normalizer ((S' : Subgroup G) : Set G) := by
    rw [hS', ← hST]
    exact hc.LM.trans hMS
  have : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLT)
  exact hc.natBlock.not_isSolvable this

theorem gomiH_Dc : GomiH (Dc L T) :=
  ⟨hc.Dc_ne_bot, by rw [hc.normalizer_Dc_eq]; exact hc.not_twoClosed_M,
    by rw [hc.normalizer_Dc_eq]; exact hc.oTwoIn_M_eq_Dc⟩

theorem gomiHIn_Dc : GomiHIn T (Dc L T) := ⟨hc.gomiH_Dc, Dc_le_T⟩

end Dnormal

section TI

variable (hc : ClassTwoSetup G L M T n)
include hc

theorem Rl_sup_Dc_eq : Rl L T ⊔ Dc L T = T :=
  le_antisymm (sup_le Rl_le_T Dc_le_T) hc.hRD

theorem card_T : Nat.card T = 2 ^ n * Nat.card (Dc L T) := by
  have := card_Rl_sup_Dc hc.natBlock hc.LM hc.MN hc.hT
  rwa [hc.Rl_sup_Dc_eq] at this

theorem oTwoIn_le_Rl : oTwoIn L ≤ Rl L T :=
  fun _ hw => ⟨NatBlock.oTwoIn_le_sylow hc.LM hc.MN hc.hT hw, oTwoIn_le L hw⟩

theorem L_inf_Dc : L ⊓ Dc L T = oTwoIn L := by
  apply le_antisymm
  · rw [← L_inf_cenW hc.natBlock hc.LM]
    exact inf_le_inf_left L (by rw [Dc_eq_inf_cenW hc.natBlock hc.MN hc.hT]; exact inf_le_right)
  · exact le_inf (oTwoIn_le L) (oTwoIn_le_Dc hc.natBlock hc.LM hc.MN hc.hT)

theorem map_conj_oTwoIn {a : G} (ha : a ∈ M) :
    (oTwoIn L).map (MulAut.conj a).toMonoidHom = oTwoIn L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (normalizer_le_normalizer_oTwoIn L (hc.MN ha))

theorem map_conj_L {a : G} (ha : a ∈ M) : L.map (MulAut.conj a).toMonoidHom = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (hc.MN ha)

theorem map_conj_Dc {a : G} (ha : a ∈ M) : (Dc L T).map (MulAut.conj a).toMonoidHom = Dc L T :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (hc.M_le_normalizer_Dc ha)

theorem ker_phi :
    hc.natBlock.natData.φ.ker = (oTwoIn L).subgroupOf L := by
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact hc.natBlock.natData.φ_ker l

theorem card_map_phi {H : Subgroup G} (hHL : H ≤ L) (hWH : oTwoIn L ≤ H) :
    Nat.card ((H.subgroupOf L).map hc.natBlock.natData.φ) * Nat.card (oTwoIn L) =
      Nat.card H := by
  set φ := hc.natBlock.natData.φ with hφ
  set K : Subgroup ↥L := H.subgroupOf L with hK
  let ψ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := φ.comp K.subtype
  have hrange : ψ.range = K.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerle : φ.ker ≤ K := by
    rw [hc.ker_phi]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hWH (Subgroup.mem_subgroupOf.1 hx))
  have hker : Nat.card ψ.ker = Nat.card (oTwoIn L) := by
    have h1 : Nat.card ψ.ker = Nat.card ↥(φ.ker) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨((x : K) : ↥L), x.2⟩
          invFun := fun y => ⟨⟨(y : ↥L), hkerle y.2⟩, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, hc.ker_phi]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (oTwoIn_le L)).toEquiv
  have hKH : Nat.card K = Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  rw [← hKH, Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker]

theorem mem_oTwoIn_of_inv_mul_mem {R₁ R₂ : Subgroup G} (h₁ : R₁ ≤ L) (h₂ : R₂ ≤ L)
    (hW₁ : oTwoIn L ≤ R₁) (hW₂ : oTwoIn L ≤ R₂)
    (hc₁ : Nat.card R₁ = 2 ^ n * Nat.card (oTwoIn L))
    (hc₂ : Nat.card R₂ = 2 ^ n * Nat.card (oTwoIn L)) (hne : R₁ ≠ R₂) {x y : G}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (hxy : y⁻¹ * x ∈ oTwoIn L) : x ∈ oTwoIn L := by
  set φ := hc.natBlock.natData.φ with hφ
  set A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    (R₁.subgroupOf L).map φ with hA
  set B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    (R₂.subgroupOf L).map φ with hB
  have hpos : 0 < Nat.card (oTwoIn L) := Nat.card_pos
  have hAc : Nat.card A = 2 ^ n := by
    have := hc.card_map_phi h₁ hW₁
    rw [hc₁] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hBc : Nat.card B = 2 ^ n := by
    have := hc.card_map_phi h₂ hW₂
    rw [hc₂] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hker : ∀ l : ↥L, φ l = 1 ↔ (l : G) ∈ oTwoIn L := hc.natBlock.natData.φ_ker
  have hAB : A ≠ B := by
    intro hAB
    apply hne
    have hle : R₁ ≤ R₂ := by
      intro r hr
      have hrA : φ ⟨r, h₁ hr⟩ ∈ A := ⟨⟨r, h₁ hr⟩, Subgroup.mem_subgroupOf.2 hr, rfl⟩
      rw [hAB] at hrA
      obtain ⟨s, hs, hsr⟩ := hrA
      have hmem : (s : G)⁻¹ * r ∈ oTwoIn L := by
        have : φ (s⁻¹ * ⟨r, h₁ hr⟩) = 1 := by rw [map_mul, map_inv, hsr, inv_mul_cancel]
        exact (hker _).1 this
      have := R₂.mul_mem (Subgroup.mem_subgroupOf.1 hs) (hW₂ hmem)
      simpa using this
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc₁, hc₂])
  have hopp := CFSG.CGT.PushingUpLit.A78.opposite_of_card_eq_SL2
    (by have := hc.natBlock.two_le; omega : n ≠ 0) hAc hBc hAB
  have hxL : x ∈ L := h₁ hx
  have hyL : y ∈ L := h₂ hy
  have hxA : φ ⟨x, hxL⟩ ∈ A := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have hxB : φ ⟨x, hxL⟩ ∈ B := by
    have hyB : φ ⟨y, hyL⟩ ∈ B := ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    have : φ (⟨y, hyL⟩⁻¹ * ⟨x, hxL⟩) = 1 := (hker _).2 hxy
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    rwa [← this]
  have h1 : φ ⟨x, hxL⟩ ∈ A ⊓ B := ⟨hxA, hxB⟩
  rw [hopp.inf_eq_bot, Subgroup.mem_bot] at h1
  exact (hker _).1 h1

theorem inf_map_conj_eq_Dc {a : G} (ha : a ∈ M) (hna : a ∉ Subgroup.normalizer (T : Set G)) :
    T ⊓ T.map (MulAut.conj a).toMonoidHom = Dc L T := by
  have hTa : T.map (MulAut.conj a).toMonoidHom =
      (Rl L T).map (MulAut.conj a).toMonoidHom ⊔ Dc L T := by
    have := congrArg (fun K => K.map (MulAut.conj a).toMonoidHom) hc.Rl_sup_Dc_eq
    simp only [Subgroup.map_sup, hc.map_conj_Dc ha] at this
    exact this.symm
  apply le_antisymm
  · rintro x ⟨hxT, hxTa⟩
    have hx1 : x ∈ Rl L T ⊔ Dc L T := by rw [hc.Rl_sup_Dc_eq]; exact hxT
    have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
      (Rl_le_T.trans hc.TM).trans hc.M_le_normalizer_Dc
    have hRn' : (Rl L T).map (MulAut.conj a).toMonoidHom ≤
        Subgroup.normalizer (Dc L T : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      exact hc.M_le_normalizer_Dc (M.mul_mem (M.mul_mem ha (hc.TM (Rl_le_T hr))) (M.inv_mem ha))
    rw [hTa] at hxTa
    obtain ⟨r, hr, d, hd, hxrd⟩ := (mem_sup_iff_mul hRn).1 hx1
    obtain ⟨r', hr', d', hd', hxrd'⟩ := (mem_sup_iff_mul hRn').1 hxTa
    have hrL : r ∈ L := Rl_le_L hr
    have hr'L : r' ∈ L := by
      have := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) (Rl_le_L : Rl L T ≤ L)
      rw [hc.map_conj_L ha] at this
      exact this hr'
    have hu : r'⁻¹ * r ∈ Dc L T := by
      have e : r'⁻¹ * r = d' * d⁻¹ := by
        have : r * d = r' * d' := hxrd.symm.trans hxrd'
        calc r'⁻¹ * r = r'⁻¹ * (r * d) * d⁻¹ := by group
          _ = r'⁻¹ * (r' * d') * d⁻¹ := by rw [this]
          _ = d' * d⁻¹ := by group
      rw [e]
      exact (Dc L T).mul_mem hd' ((Dc L T).inv_mem hd)
    have hu' : r'⁻¹ * r ∈ oTwoIn L := by
      rw [← hc.L_inf_Dc]
      exact ⟨L.mul_mem (L.inv_mem hr'L) hrL, hu⟩
    have hW₂ : oTwoIn L ≤ (Rl L T).map (MulAut.conj a).toMonoidHom := by
      have := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hc.oTwoIn_le_Rl
      rwa [hc.map_conj_oTwoIn ha] at this
    have hne : Rl L T ≠ (Rl L T).map (MulAut.conj a).toMonoidHom := by
      intro heq
      apply hna
      refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
      show T.map (MulAut.conj a).toMonoidHom = T
      rw [hTa, ← heq, hc.Rl_sup_Dc_eq]
    have hr_W : r ∈ oTwoIn L := hc.mem_oTwoIn_of_inv_mul_mem Rl_le_L
      (((Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) Rl_le_L).trans
        (hc.map_conj_L ha).le))
      hc.oTwoIn_le_Rl hW₂ (card_Rl hc.natBlock hc.LM hc.MN hc.hT)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj a).injective,
        card_Rl hc.natBlock hc.LM hc.MN hc.hT]) hne hr hr' hu'
    rw [hxrd]
    exact (Dc L T).mul_mem (oTwoIn_le_Dc hc.natBlock hc.LM hc.MN hc.hT hr_W) hd
  · refine le_inf Dc_le_T ?_
    have := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) (Dc_le_T : Dc L T ≤ T)
    rwa [hc.map_conj_Dc ha] at this

theorem le_Dc_of_gomiHIn {H : Subgroup G} (hH : GomiHIn T H)
    (hN : Subgroup.normalizer (H : Set G) ≤ M) : H ≤ Dc L T := by
  have hTn : T ≤ Subgroup.normalizer (H : Set G) :=
    hH.1.le_normalizer_of_classLETwo hc.sec4.hyp.charTwo hc.class2 hH.2
  have hsyl : IsSylowOf 2 T (Subgroup.normalizer (H : Set G)) :=
    hc.sec4.sylowG.of_le hTn le_top
  have hnc := hH.1.not_twoClosed
  rw [twoClosed_iff_forall_eq] at hnc
  push Not at hnc
  obtain ⟨S₁, S₂, hS₁, hS₂, hne⟩ := hnc
  obtain ⟨S, hS, hST⟩ : ∃ S, IsSylowOf 2 S (Subgroup.normalizer (H : Set G)) ∧ S ≠ T := by
    by_cases h1 : S₁ = T
    · exact ⟨S₂, hS₂, fun h2 => hne (h1.trans h2.symm)⟩
    · exact ⟨S₁, hS₁, h1⟩
  obtain ⟨a, haN, rfl⟩ := exists_eq_map_conj_of_isSylowOf hsyl hS
  have hna : a ∉ Subgroup.normalizer (T : Set G) := fun h =>
    hST (Subgroup.mem_normalizer_iff_map_conj_eq.1 h)
  have hHa : H.map (MulAut.conj a).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 haN
  have hle : H ≤ T ⊓ T.map (MulAut.conj a).toMonoidHom := by
    refine le_inf hH.2 ?_
    have := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hH.2
    rwa [hHa] at this
  rw [hc.inf_map_conj_eq_Dc (hN haN) hna] at hle
  exact hle

theorem not_normalizer_le_M_of_gomiD {D₂ : Subgroup G} (h : GomiD T D₂) (hne : D₂ ≠ Dc L T) :
    ¬ Subgroup.normalizer (D₂ : Set G) ≤ M := by
  intro hN
  have hle : D₂ ≤ Dc L T := hc.le_Dc_of_gomiHIn h.1 hN
  exact hne (le_antisymm hle (h.2 hc.gomiHIn_Dc hle))

end TI

end ClassTwoSetup

end CFSG.CGT.PushingUpLit.C2L
