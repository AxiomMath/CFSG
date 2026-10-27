module

public import CFSG.CGT.PushingUpLit.T2KSW.WCover
public import CFSG.CGT.PushingUpLit.T2KSW.ClassThree
public import CFSG.CGT.PushingUpLit.T2KSW.ZStarE

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement
open Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem Ec_inf_oTwoIn_le_ZR : Ec L T ⊓ oTwoIn L ≤ ZR L T := by
  rintro e ⟨he, heW⟩
  refine mem_ZR.2 ⟨⟨he.1, oTwoIn_le L heW⟩, fun r hr => ?_⟩
  exact Subgroup.mem_centralizer_iff.1 he.2 r (Rl_le_L hr)

theorem blockU_le_normalizer_Ec (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : IsSylowOf 2 T M) : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
  (NatBlock.blockU_le_sylow hLM hMN hT).trans (le_normalizer_Ec hMN hT.le)

theorem ZR_eq_ellTilde_sup (H : CoordData G L M n) (hT : IsSylowOf 2 T M) (hA : H.Adapted T)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) : ZR L T = ellTilde H.D ⊔ (Ec L T ⊓ oTwoIn L) := by
  refine le_antisymm ?_ (sup_le (ellTilde_le_ZR H hT hA) Ec_inf_oTwoIn_le_ZR)
  intro z hz
  obtain ⟨hzR, hzc⟩ := mem_ZR.1 hz
  have hzD : z ∈ Dc L T := ⟨hzR.1, Subgroup.mem_centralizer_iff.2 fun v hv =>
    hzc v (blockU_le_Rl H.le H.normal hT hv)⟩
  have hzW : z ∈ oTwoIn L := by
    rw [← Rl_inf_Dc H.nat H.le H.normal hT]
    exact ⟨hzR, hzD⟩
  obtain ⟨v, hv, e, he, rfl⟩ :=
    (mem_sup_iff_mul (blockU_le_normalizer_Ec H.le H.normal hT)).1 (hWVE hzW)
  have heW : e ∈ oTwoIn L := by
    have := (oTwoIn L).mul_mem ((oTwoIn L).inv_mem (blockU_le_oTwoIn L hv)) hzW
    simpa using this
  obtain ⟨r₀, hr₀, hr₀W⟩ := exists_mem_Rl_not_mem_oTwoIn H.nat H.le H.normal hT
  have hvc : r₀ * v * r₀⁻¹ = v := by
    have h1 : r₀ * e = e * r₀ := Subgroup.mem_centralizer_iff.1 he.2 r₀ (Rl_le_L hr₀)
    have h2 : r₀ * (v * e) = (v * e) * r₀ := hzc r₀ hr₀
    have h3 : r₀ * v = v * r₀ := by
      have : r₀ * v * e = v * r₀ * e := by
        calc r₀ * v * e = r₀ * (v * e) := by group
          _ = (v * e) * r₀ := h2
          _ = v * (e * r₀) := by group
          _ = v * (r₀ * e) := by rw [h1]
          _ = v * r₀ * e := by group
      exact mul_right_cancel this
    rw [h3, mul_inv_cancel_right]
  exact mul_mem (Subgroup.mem_sup_left (mem_ellTilde_of_conj_eq H hA hr₀ hr₀W hv hvc))
    (Subgroup.mem_sup_right ⟨he, heW⟩)

theorem sq_mem_ZR_of_wleVE (H : CoordData G L M n) (hT : IsSylowOf 2 T M) (hA : H.Adapted T)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {r : G} (hr : r ∈ Rl L T) : r ^ 2 ∈ ZR L T := by
  have hVn := blockU_le_normalizer_Ec H.le H.normal hT
  have hr2 : r ^ 2 ∈ oTwoIn L := by
    obtain ⟨s, hs⟩ := hA r hr.2 hr.1
    exact H.sq_mem_oTwoIn_of_utri hr.2 hs
  by_cases hrW : r ∈ oTwoIn L
  · obtain ⟨v, hv, e, he, rfl⟩ := (mem_sup_iff_mul hVn).1 (hWVE hrW)
    have hv2 : v ^ 2 = 1 := H.nat.sq_eq_one_of_mem_blockU hv
    have hve : v * e = e * v := Subgroup.mem_centralizer_iff.1 he.2 v (blockU_le L hv)
    have heW : e ∈ oTwoIn L := by
      have := (oTwoIn L).mul_mem ((oTwoIn L).inv_mem (blockU_le_oTwoIn L hv)) hrW
      simpa using this
    have e2 : (v * e) ^ 2 = e ^ 2 := by
      calc (v * e) ^ 2 = v * (e * v) * e := by rw [pow_two]; group
        _ = v * (v * e) * e := by rw [hve]
        _ = v ^ 2 * e ^ 2 := by rw [pow_two, pow_two]; group
        _ = e ^ 2 := by rw [hv2, one_mul]
    rw [e2]
    exact Ec_inf_oTwoIn_le_ZR ⟨(Ec L T).pow_mem he 2, (oTwoIn L).pow_mem heW 2⟩
  · obtain ⟨v, hv, e, he, hve⟩ := (mem_sup_iff_mul hVn).1 (hWVE hr2)
    have heW : e ∈ oTwoIn L := by
      have := (oTwoIn L).mul_mem ((oTwoIn L).inv_mem (blockU_le_oTwoIn L hv)) hr2
      rw [hve] at this
      simpa using this
    have hrc : r * v * r⁻¹ = v := by
      have h1 : r * e = e * r := Subgroup.mem_centralizer_iff.1 he.2 r hr.2
      have h2 : r * r ^ 2 = r ^ 2 * r := by group
      have h3 : r * v * e = v * r * e := by
        calc r * v * e = r * (v * e) := by group
          _ = r * r ^ 2 := by rw [← hve]
          _ = r ^ 2 * r := h2
          _ = (v * e) * r := by rw [hve]
          _ = v * (e * r) := by group
          _ = v * (r * e) := by rw [h1]
          _ = v * r * e := by group
      rw [mul_right_cancel h3, mul_inv_cancel_right]
    rw [hve]
    exact mul_mem (ellTilde_le_ZR H hT hA (mem_ellTilde_of_conj_eq H hA hr hrW hv hrc))
      (Ec_inf_oTwoIn_le_ZR ⟨he, heW⟩)

theorem comm_mem_ZR_of_wleVE (H : CoordData G L M n) (hT : IsSylowOf 2 T M) (hA : H.Adapted T)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {x y : G} (hx : x ∈ Rl L T) (hy : y ∈ Rl L T) :
    ⁅x, y⁆ ∈ ZR L T := by
  have key : ∀ x ∈ Rl L T, ⁅x⁻¹, y⁆ ∈ ZR L T := by
    intro x hx
    have hX : (x ^ 2 * y ^ 2)⁻¹ * (x * y) ^ 2 ∈ ZR L T :=
      mul_mem (inv_mem (mul_mem (sq_mem_ZR_of_wleVE H hT hA hWVE hx)
        (sq_mem_ZR_of_wleVE H hT hA hWVE hy))) (sq_mem_ZR_of_wleVE H hT hA hWVE (mul_mem hx hy))
    have e : ⁅x⁻¹, y⁆ = (y ^ 2 * ((x ^ 2 * y ^ 2)⁻¹ * (x * y) ^ 2)) * (y ^ 2)⁻¹ := by
      simp only [commutatorElement_def, pow_two]
      group
    have hc := (mem_ZR.1 hX).2 (y ^ 2) ((Rl L T).pow_mem hy 2)
    rw [e, hc]
    simpa using hX
  have := key x⁻¹ (inv_mem hx)
  simpa using this

theorem card_ZR_sup_Ec_le_of_wleVE (H : CoordData G L M n) (hT : IsSylowOf 2 T M)
    (hA : H.Adapted T) (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) :
    Nat.card ↥(ZR L T ⊔ Ec L T) ≤ 2 ^ n * Nat.card ↥(Ec L T) := by
  have hZ : ZR L T ⊔ Ec L T = ellTilde H.D ⊔ Ec L T := by
    rw [ZR_eq_ellTilde_sup H hT hA hWVE]
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
    · exact sup_le_sup_right le_sup_left _
  have hℓn : ellTilde H.D ≤ Subgroup.normalizer (Ec L T : Set G) :=
    (ellTilde_le_blockU _).trans (blockU_le_normalizer_Ec H.le H.normal hT)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hℓn
  have hℓcard : Nat.card (ellTilde H.D) = 2 ^ n * Nat.card (blockZ L) := by
    have h1 := card_ellTilde_mul H.nat H.D
    rw [H.nat.card_blockU, sq] at h1
    have hpos : 0 < 2 ^ n := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  have hcZ : blockZ L ≤ Ec L T ⊓ ellTilde H.D := by
    refine le_inf ?_ ?_
    · exact fun v hv => ⟨NatBlock.blockU_le_sylow H.le H.normal hT (blockZ_le_blockU L hv),
        NatBlock.blockZ_le_centralizer L hv⟩
    · intro v hv
      refine ⟨blockZ_le_blockU L hv, ?_⟩
      rw [(H.D.ψe_eq_zero_iff (blockZ_le_blockU L hv)).2 hv]
      rfl
  have hle : Nat.card ↥(blockZ L) ≤ Nat.card ↥(Ec L T ⊓ ellTilde H.D) :=
    Subgroup.card_le_of_le hcZ
  have hcpos : 0 < Nat.card ↥(blockZ L) := Nat.card_pos
  have h2 : Nat.card ↥(Ec L T ⊔ ellTilde H.D) * Nat.card ↥(blockZ L) ≤
      (2 ^ n * Nat.card ↥(Ec L T)) * Nat.card ↥(blockZ L) := by
    calc Nat.card ↥(Ec L T ⊔ ellTilde H.D) * Nat.card ↥(blockZ L)
        ≤ Nat.card ↥(Ec L T ⊔ ellTilde H.D) * Nat.card ↥(Ec L T ⊓ ellTilde H.D) :=
          Nat.mul_le_mul_left _ hle
      _ = Nat.card ↥(Ec L T) * Nat.card ↥(ellTilde H.D) := hprod
      _ = (2 ^ n * Nat.card ↥(Ec L T)) * Nat.card ↥(blockZ L) := by rw [hℓcard]; ring
  rw [hZ, sup_comm]
  exact Nat.le_of_mul_le_mul_right h2 hcpos

theorem card_ZR_sup_Ec_le' (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) :
    Nat.card ↥(ZR L T ⊔ Ec L T) ≤ 2 ^ n * Nat.card ↥(Ec L T) := by
  obtain ⟨H, hA⟩ := exists_utri_coord hs.hyp.natBlock hs.hyp.le (hs.hyp.normal hE1) hs.sylow
  exact card_ZR_sup_Ec_le_of_wleVE H hs.sylow hA hWVE

theorem rdFacts_of_wleVE (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) :
    (∀ d ∈ Dc L T, ∀ d' ∈ Dc L T, d ^ 2 ∈ Ec L T ∧ ⁅d, d'⁆ ∈ Ec L T) ∧
    Rl L T ⊓ Dc L T = oTwoIn L ∧
    Nat.card (Rl L T) = 2 ^ n * Nat.card (oTwoIn L) ∧
    (∀ r ∈ Rl L T, r ^ 2 ∈ oTwoIn L) ∧
    Nat.card (Dc L T) ≤ 2 ^ n * Nat.card ↥(Ec L T ⊔ blockU L) ∧
    (∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w) ∧
    (T ≤ L ⊔ cenW L M ↔ T ≤ Rl L T ⊔ Dc L T) ∧
    (T ≤ Rl L T ⊔ Dc L T →
      ZR L T ≤ ZT T ∧ ⁅⁅T, T⁆, T⁆ ≤ Ec L T ∧ ⁅T, T⁆ ≤ ZR L T ⊔ Ec L T ∧
        (∀ t ∈ T, t ^ 2 ∈ ZR L T ⊔ Ec L T) ∧ ⁅Rl L T, T⁆ ≤ ZR L T ∧
        (T ⊓ Subgroup.centralizer (Rl L T : Set G) ≤ ZR L T ⊔ Ec L T) ∧
        ZT T ≤ ZR L T ⊔ Ec L T) := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  obtain ⟨H, hA⟩ := exists_utri_coord h hLM hMN hT
  have hWD : ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w := Dc_centralizes_oTwoIn hs hE1
  have hinf := inf_sup_cenW h hLM hMN hT
  refine ⟨fun d hd d' hd' => ⟨Dc_sq_mem_Ec h hMN hT hd, Dc_comm_mem_Ec h hMN hT hd hd'⟩,
    Rl_inf_Dc h hLM hMN hT, card_Rl h hLM hMN hT, fun r hr => ?_, card_Dc_le h hLM hMN hT, hWD,
    ⟨fun hTK => ?_, fun hTRD => ?_⟩, fun hTRD => ?_⟩
  · obtain ⟨s, hs'⟩ := hA r hr.2 hr.1
    exact H.sq_mem_oTwoIn_of_utri hr.2 hs'
  · rw [← hinf]
    exact le_inf le_rfl hTK
  · exact hTRD.trans (hinf ▸ inf_le_right)
  · have hX : Rl L T ≤ T ⊓ (Rl L T ⊔ Dc L T) := le_inf Rl_le_T le_sup_left
    have h3 : 3 ≤ (Rl L T ⊓ Dc L T).relIndex (Rl L T) := by
      rw [relIndex_Rl_inf_Dc h hLM hMN hT]
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
      omega
    exact rd_class_facts h hLM hMN hT hWD
      (fun x hx y hy => comm_mem_ZR_of_wleVE H hT hA hWVE hx hy)
      (fun r hr => sq_mem_ZR_of_wleVE H hT hA hWVE hr)
      (fun d hd r hr => comm_Dc_Rl_mem_ZR H hT hA hd hr)
      (Dc_inf_centralizer_le H hT hA hX h3) hTRD

theorem rdFacts_struct_of_wleVE (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (hRD : T ≤ Rl L T ⊔ Dc L T) : RDFacts L T := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := rdFacts_of_wleVE hs hE1 hWVE
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h hRD
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem ClassThreeSetup.of_wleVE (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hs : Sec4 G L M T n) (hE : Ec L T ≠ ⊥) (hnc : ¬ ClassLETwo T)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (hRD : T ≤ Rl L T ⊔ Dc L T) :
    ClassThreeSetup G L M T n := by
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  obtain ⟨-, -, hME⟩ := hs.hyp.four_four hE1 hE8 h25 hs.sylow
  have hfacts := rdFacts_struct_of_wleVE hs hE1 hWVE hRD
  exact ⟨hs, hMN, hME, hE, hfacts, exists_comm3_ne_one hs hMN hfacts hRD hnc⟩

theorem false_of_classThree'
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (hList : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} (hs : Sec4 G L M T n)
    (hE : Ec L T ≠ ⊥) (hnc : ¬ ClassLETwo T)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (hRD : T ≤ Rl L T ⊔ Dc L T) : False := by
  have hc : ClassThreeSetup G L M T n :=
    ClassThreeSetup.of_wleVE hE1 hE8 h25 hs hE hnc hWVE hRD
  have : IsSimpleGroup G := hs.hyp.simple
  have hstd : CFSG.CGT.Timmesfeld75.StdPair G (Ec L T) :=
    stdPair_of_weaklyClosed hSCL hList (ClassThree.exists_noncomm_of_natBlock hs.hyp.natBlock)
      Ec_le_T hE hs.S_elem hc.normalizer_Ec_eq hs.sylow hs.sylowG
      (fun g hg => hc.Ec_inf_conj_eq_bot hg) (fun g hg => weaklyClosed_Ec hc g hg)
  exact list_false hs.hyp.two_le hs.hyp.natBlock.perfect
    (ClassThree.ne_bot_of_natBlock hs.hyp.natBlock) hs.sylowG (le_centralizer_inf_centralizer L T)
    (card_Ec_lt_card_T hc hRD) hstd

end CFSG.CGT.PushingUpLit.T2KSW
