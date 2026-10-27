module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321QA

public section
namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem inf_centralizer_L_eq_bot_F4 (he : Step3_3_21e_F4) (h : Hyp331 G T M L D)
    (e : Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hmod : Mod3321 T L) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hUn : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer ht) (mem_normalizer_centralizer (hTL ht))
  obtain ⟨v, hv, hv1, hvC⟩ := exists_mem_center_of_ne_bot h.sylow.1 inf_le_left hUn hne
  set X : Subgroup G := T ⊓ Subgroup.centralizer (L : Set G) ⊓
    Subgroup.centralizer (T : Set G) with hX
  have hvX : v ∈ X := ⟨hv, hvC⟩
  have hX2 : IsPGroup 2 X := h.sylow.1.to_le (inf_le_left.trans inf_le_left)
  have hXne : X ≠ ⊥ := fun hb => hv1 (by rw [hb] at hvX; exact hvX)
  have hdvd : 2 ∣ Nat.card ↥X := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hXne
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq X hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hw2 : (w : G) ^ 2 = 1 := by
    have h1 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    simpa using congrArg Subtype.val h1
  have hw1 : (w : G) ≠ 1 := by
    intro h1
    have h2 : w = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hw
    exact absurd hw (by norm_num)
  have hwZ : (w : G) ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨w.2.1.1, w.2.2⟩, hw2⟩
  have h1 : (w : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hwZ, w.2.1.2⟩
  rw [he G T M L D h e hmod, Subgroup.mem_bot] at h1
  exact hw1 h1

theorem exists_decomp_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4) {α : ↥L →* SL4}
    (hD : FData G T M L D α) {t : G} (ht : t ∈ T) :
    ∃ s ∈ T ⊓ L, s⁻¹ * t ∈ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨hML, -⟩ := h14 G T M L D hD.hyp
  obtain ⟨y, hyU, hy⟩ := hD.exists_conj ht
  have hyU' := hyU
  rw [← hD.mapU] at hyU'
  obtain ⟨s, hs, hse⟩ := hyU'
  have hs' : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hs
  set c : G := (s : G)⁻¹ * t with hc
  have hcT : c ∈ T := T.mul_mem (T.inv_mem hs'.1) ht
  have hcL : ∀ l : ↥L, ∃ k : ↥L, α k = 1 ∧ c * (l : G) * c⁻¹ = k * l := by
    intro l
    have hx : t * (l : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.TL ht) l).mp l.2
    let m : ↥L := s⁻¹ * ⟨t * l * t⁻¹, hx⟩ * s
    have hm : (m : G) = c * l * c⁻¹ := by
      show (s : G)⁻¹ * (t * l * t⁻¹) * s = c * l * c⁻¹
      rw [hc]
      group
    refine ⟨m * l⁻¹, ?_, by rw [Subgroup.coe_mul, Subgroup.coe_inv, hm]; group⟩
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hy l hx, hse]
    group
  have hcV : c ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    have hle : vPlus L T ≤ Subgroup.centralizer ({c} : Set G) := by
      refine (vPlus_le_conjClosure hML).trans (conjClosure_le fun l hl z hz => ?_)
      obtain ⟨k, hk1, hk⟩ := hcL ⟨l, hl⟩
      have hkV : (k : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := (hD.kerV k).1 hk1
      have hlz : l * z * l⁻¹ ∈ vPlus L T := by
        show l * z * l⁻¹ ∈ conjClosure (quasithinOmegaOneCenter T) (mPlus L T)
        rw [hML]
        exact Subgroup.subset_closure ⟨l, hl, z, hz, rfl⟩
      have hcz := conj_omegaOneCenter hcT hz
      have h1 : c * (l * z * l⁻¹) * c⁻¹ = l * z * l⁻¹ := by
        have e1 : c * (l * z * l⁻¹) * c⁻¹ =
            (c * l * c⁻¹) * (c * z * c⁻¹) * (c * l * c⁻¹)⁻¹ := by group
        rw [e1, hcz, hk]
        have h2 := Subgroup.mem_centralizer_iff.1 hkV _ hlz
        calc (k : G) * l * z * ((k : G) * l)⁻¹ = ((k : G) * (l * z * l⁻¹)) * (k : G)⁻¹ := by
              group
          _ = ((l * z * l⁻¹) * k) * (k : G)⁻¹ := by rw [← h2]
          _ = l * z * l⁻¹ := by group
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc l * z * l⁻¹ * c = (c * (l * z * l⁻¹) * c⁻¹) * c := by rw [h1]
        _ = c * (l * z * l⁻¹) := by group
    exact Subgroup.mem_centralizer_iff.2 fun v hv =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hle hv))
  obtain ⟨⟨-, hCT⟩, -⟩ := h7 G T M L D hD.hyp
  rw [hML] at hCT
  refine ⟨s, hs', ?_⟩
  rw [← hCT]
  exact ⟨hcT, hcV⟩

theorem pCoreOf_LT_eq_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4) (h : Hyp331 G T M L D) :
    T ⊓ Subgroup.centralizer (vPlus L T : Set G) = pCoreOf 2 (L ⊔ T) := by
  obtain ⟨hML, -⟩ := h14 G T M L D h
  obtain ⟨⟨-, hCT⟩, -⟩ := h7 G T M L D h
  rw [hML] at hCT
  exact hCT

theorem sq_eq_one_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4) (h : Hyp331 G T M L D)
    (hCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T)
    {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) : q ^ 2 = 1 := by
  have hqT := pCoreOf_LT_le h hq
  have hqC : q ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    rw [← pCoreOf_LT_eq_F4 h7 h14 h] at hq
    exact hq.2
  have hVe := (Hyp331.vPlus_reduced h.toSetup331).2.1
  rw [sq]
  have hq2 : q * q ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem hqT hqT, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    set c := q * l * q⁻¹ * l⁻¹ with hc
    have hcV : c ∈ vPlus L T := hQV q hq l hl
    have hqc : q * c * q⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.1 hqC c hcV
      rw [← this, mul_inv_cancel_right]
    have hc2 : c * c = 1 := by
      have := hVe.2 c hcV
      rwa [sq] at this
    have e1 : q * l * q⁻¹ = c * l := by rw [hc]; group
    have e2 : q * q * l * (q * q)⁻¹ = l := by
      calc q * q * l * (q * q)⁻¹ = q * (q * l * q⁻¹) * q⁻¹ := by group
        _ = q * (c * l) * q⁻¹ := by rw [e1]
        _ = (q * c * q⁻¹) * (q * l * q⁻¹) := by group
        _ = c * (c * l) := by rw [hqc, e1]
        _ = (c * c) * l := by group
        _ = l := by rw [hc2, one_mul]
    calc l * (q * q) = (q * q * l * (q * q)⁻¹) * (q * q) := by rw [e2]
      _ = q * q * l := by group
  rw [hCL, Subgroup.mem_bot] at hq2
  exact hq2

theorem isElemAbelian_pCoreOf_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4) (h : Hyp331 G T M L D)
    (hCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T) :
    IsElemAbelian 2 (pCoreOf 2 (L ⊔ T)) := by
  have hsq := fun q (hq : q ∈ pCoreOf 2 (L ⊔ T)) => sq_eq_one_F4 h7 h14 h hCL hQV hq
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hsq⟩
  have ha := hsq a a.2
  have hb := hsq b b.2
  have hab := hsq _ (Subgroup.mul_mem _ a.2 b.2)
  rw [sq] at ha hb hab
  show (a : G) * b = b * a
  calc (a : G) * b = (a * b)⁻¹ := (eq_inv_of_mul_eq_one_left hab).trans rfl
    _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [inv_eq_of_mul_eq_one_left hb, inv_eq_of_mul_eq_one_left ha]

end CFSG.Quasithin.H13.L3321
