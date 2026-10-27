module

public import CFSG.CGT.PushingUpLit.T2KSW.RD
public import CFSG.CGT.PushingUpLit.T2KSW.Coord

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KR CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization
open Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

abbrev ZR (L T : Subgroup G) : Subgroup G := (Subgroup.center ↥(Rl L T)).map (Rl L T).subtype

abbrev ZT (T : Subgroup G) : Subgroup G := (Subgroup.center ↥T).map T.subtype

omit [Finite G] in
theorem ZR_eq : ZR L T = Rl L T ⊓ Subgroup.centralizer (Rl L T : Set G) := map_center_subtype _

omit [Finite G] in
theorem ZT_eq : ZT T = T ⊓ Subgroup.centralizer (T : Set G) := map_center_subtype _

omit [Finite G] in
theorem mem_ZR {z : G} : z ∈ ZR L T ↔ z ∈ Rl L T ∧ ∀ r ∈ Rl L T, r * z = z * r := by
  rw [ZR_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

omit [Finite G] in
theorem mem_ZT {z : G} : z ∈ ZT T ↔ z ∈ T ∧ ∀ t ∈ T, t * z = z * t := by
  rw [ZT_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

omit [Finite G] in
theorem ZR_le_Rl : ZR L T ≤ Rl L T := by
  rw [ZR_eq]
  exact inf_le_left

theorem conj_comm_blockU (h : NatBlock L n) {r : G} (hrN : r ∈ Subgroup.normalizer (L : Set G))
    (hr2 : r ^ 2 ∈ oTwoIn L) {u : G} (hu : u ∈ blockU L) :
    r * (r * u * r⁻¹ * u⁻¹) * r⁻¹ = r * u * r⁻¹ * u⁻¹ := by
  have hbV : r * u * r⁻¹ ∈ blockU L := conj_mem_blockU hrN hu
  have hu1 : u⁻¹ = u := by
    have := h.sq_eq_one_of_mem_blockU hu
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  have hb1 : (r * u * r⁻¹)⁻¹ = r * u * r⁻¹ := by
    have := h.sq_eq_one_of_mem_blockU hbV
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  have hcomm : u * (r * u * r⁻¹) = (r * u * r⁻¹) * u := h.blockU_comm u hu _ hbV
  have hw : u * r ^ 2 = r ^ 2 * u := blockU_comm_of_short h.short u hu _ hr2
  have hrb : r * (r * u * r⁻¹) * r⁻¹ = u := by
    calc r * (r * u * r⁻¹) * r⁻¹ = (r * r) * u * (r * r)⁻¹ := by group
      _ = u := by rw [← pow_two, ← hw]; group
  calc r * (r * u * r⁻¹ * u⁻¹) * r⁻¹
      = (r * (r * u * r⁻¹) * r⁻¹) * (r * u⁻¹ * r⁻¹) := by group
    _ = u * (r * u * r⁻¹)⁻¹ := by rw [hrb]; congr 1; group
    _ = u * (r * u * r⁻¹) := by rw [hb1]
    _ = (r * u * r⁻¹) * u := hcomm
    _ = r * u * r⁻¹ * u⁻¹ := by rw [hu1]

@[expose] def ellTilde (D : NatData L n) : Subgroup G where
  carrier := {v | v ∈ blockU L ∧ D.ψe v 1 = 0}
  one_mem' := ⟨one_mem _, by rw [D.ψe_one]; rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [D.ψe_mul ha.1 hb.1, Pi.add_apply, ha.2, hb.2, add_zero]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
    rw [D.ψe_inv ha.1, Pi.neg_apply, ha.2, neg_zero]⟩

omit [Finite G] in
theorem mem_ellTilde {D : NatData L n} {v : G} : v ∈ ellTilde D ↔ v ∈ blockU L ∧ D.ψe v 1 = 0 :=
  Iff.rfl

omit [Finite G] in
theorem ellTilde_le_blockU (D : NatData L n) : ellTilde D ≤ blockU L := fun _ hv => hv.1

omit [Finite G] in
theorem uMat_mulVec_zero {n : ℕ} (s : Fq n) (w : Fin 2 → Fq n) :
    ((uMat s : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w 0
      = w 0 + s * w 1 := by
  rw [mulVec_two_zero, uMat_coe]
  simp

omit [Finite G] in
theorem uMat_mulVec_one {n : ℕ} (s : Fq n) (w : Fin 2 → Fq n) :
    ((uMat s : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w 1
      = w 1 := by
  rw [mulVec_two_one, uMat_coe]
  simp

theorem phi0 (H : CoordData G L M n) (hA : H.Adapted T) {r : G} (hr : r ∈ Rl L T) {v : G}
    (hv : v ∈ ellTilde H.D) : r * v * r⁻¹ = v := by
  obtain ⟨hrT, hrL⟩ := hr
  obtain ⟨s, hs⟩ := hA r hrL hrT
  have hrN : r ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hrL
  by_cases hs0 : s = 0
  · have hφ1 : H.D.φ ⟨r, hrL⟩ = 1 := by rw [hs, hs0, uMat_zero]
    have hrW : r ∈ oTwoIn L := (H.D.φ_ker ⟨r, hrL⟩).1 hφ1
    have := blockU_comm_of_short H.nat.short v hv.1 r hrW
    rw [← this, mul_inv_cancel_right]
  · have hr2 : r ^ 2 ∈ oTwoIn L := H.sq_mem_oTwoIn_of_utri hrL hs
    have hw1 : H.D.ψe v 1 = 0 := hv.2
    obtain ⟨u, huV, hu⟩ := H.D.exists_ψe ![0, H.D.ψe v 0 / s]
    have hbV : r * u * r⁻¹ ∈ blockU L := conj_mem_blockU hrN huV
    have haV : r * u * r⁻¹ * u⁻¹ ∈ blockU L := mul_mem hbV (inv_mem huV)
    have hψa : H.D.ψe (r * u * r⁻¹ * u⁻¹) = H.D.ψe v := by
      rw [H.D.ψe_mul hbV (inv_mem huV), H.D.ψe_inv huV, H.D.ψe_conj hrL huV, hs, hu]
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Pi.add_apply, Pi.neg_apply]
        rw [uMat_mulVec_zero]
        simp [mul_div_cancel₀ _ hs0]
      · simp only [Fin.mk_one, Pi.add_apply, Pi.neg_apply]
        rw [uMat_mulVec_one, hw1]
        simp
    have hmem : (r * u * r⁻¹ * u⁻¹)⁻¹ * v ∈ blockU L := mul_mem (inv_mem haV) hv.1
    have hz : (r * u * r⁻¹ * u⁻¹)⁻¹ * v ∈ blockZ L := by
      refine (H.D.ψe_eq_zero_iff hmem).1 ?_
      rw [H.D.ψe_mul (inv_mem haV) hv.1, H.D.ψe_inv haV, hψa]
      abel
    have hzc : r * ((r * u * r⁻¹ * u⁻¹)⁻¹ * v) * r⁻¹ = (r * u * r⁻¹ * u⁻¹)⁻¹ * v := by
      have := Subgroup.mem_centralizer_iff.1 (NatBlock.blockZ_le_centralizer L hz) r hrL
      rw [this, mul_inv_cancel_right]
    calc r * v * r⁻¹
        = (r * (r * u * r⁻¹ * u⁻¹) * r⁻¹) *
          (r * ((r * u * r⁻¹ * u⁻¹)⁻¹ * v) * r⁻¹) := by group
      _ = (r * u * r⁻¹ * u⁻¹) * ((r * u * r⁻¹ * u⁻¹)⁻¹ * v) := by
        rw [conj_comm_blockU H.nat hrN hr2 huV, hzc]
      _ = v := by group

theorem exists_mem_Rl_not_mem_oTwoIn (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    ∃ r ∈ Rl L T, r ∉ oTwoIn L := by
  by_contra hcon
  have hle : Rl L T ≤ oTwoIn L := fun r hr => by_contra fun hrW => hcon ⟨r, hr, hrW⟩
  have h1 : Nat.card (Rl L T) ≤ Nat.card (oTwoIn L) := Subgroup.card_le_of_le hle
  rw [card_Rl h hLM hMN hT] at h1
  have hpos : 0 < Nat.card (oTwoIn L) := Nat.card_pos
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  nlinarith

theorem blockU_le_Rl (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : blockU L ≤ Rl L T :=
  fun _ hv => ⟨NatBlock.blockU_le_sylow hLM hMN hT hv, blockU_le L hv⟩

theorem mem_ellTilde_of_conj_eq (H : CoordData G L M n) (hA : H.Adapted T) {r : G}
    (hr : r ∈ Rl L T) (hrW : r ∉ oTwoIn L) {v : G} (hv : v ∈ blockU L)
    (hc : r * v * r⁻¹ = v) : v ∈ ellTilde H.D := by
  obtain ⟨hrT, hrL⟩ := hr
  obtain ⟨s, hs⟩ := hA r hrL hrT
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hrW ((H.D.φ_ker ⟨r, hrL⟩).1 (by rw [hs, uMat_zero]))
  refine ⟨hv, ?_⟩
  have h1 := H.D.ψe_conj hrL hv
  rw [hc, hs] at h1
  have h2 := congrFun h1 0
  rw [uMat_mulVec_zero] at h2
  have h3 : s * H.D.ψe v 1 = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h3).resolve_left hs0

theorem ellTilde_le_ZR (H : CoordData G L M n) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hA : H.Adapted T) : ellTilde H.D ≤ ZR L T := by
  intro v hv
  refine mem_ZR.2 ⟨blockU_le_Rl H.le H.normal hT (ellTilde_le_blockU _ hv), fun r hr => ?_⟩
  have := phi0 H hA hr hv
  rw [← mul_inv_eq_iff_eq_mul]
  exact this

theorem card_ellTilde_mul (h : NatBlock L n) (D : NatData L n) :
    Nat.card (ellTilde D) * 2 ^ n = Nat.card (blockU L) := by
  have hn : n ≠ 0 := by have := h.two_le; omega
  let f : ↥(blockU L) →* Multiplicative (Fq n) :=
    MonoidHom.mk' (fun v => Multiplicative.ofAdd (D.ψe (v : G) 1)) fun a b => by
      rw [← ofAdd_add]
      show Multiplicative.ofAdd (D.ψe ((a : G) * b) 1) = _
      rw [D.ψe_mul a.2 b.2]
      rfl
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v, hv, hva⟩ := D.exists_ψe ![0, Multiplicative.toAdd a]
    refine ⟨⟨v, hv⟩, ?_⟩
    show Multiplicative.ofAdd (D.ψe v 1) = a
    rw [hva]
    rfl
  have h1 := Subgroup.card_ker_mul_card_of_surjective hf
  have hker : f.ker = (ellTilde D).subgroupOf (blockU L) := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_ellTilde]
    show Multiplicative.ofAdd (D.ψe (v : G) 1) = 1 ↔ _
    constructor
    · intro hv
      exact ⟨v.2, hv⟩
    · intro hv
      exact hv.2
  have hcard : Nat.card f.ker = Nat.card (ellTilde D) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ellTilde_le_blockU D)).toEquiv
  have hq : Nat.card (Multiplicative (Fq n)) = 2 ^ n := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fq n) ≃ _)]
    exact GaloisField.card 2 n hn
  rw [← h1, hcard, hq]

theorem comm_Dc_Rl_mem_ZR (H : CoordData G L M n) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hA : H.Adapted T) {d : G} (hd : d ∈ Dc L T) {r : G}
    (hr : r ∈ Rl L T) : ⁅d, r⁆ ∈ ZR L T := by
  have hQ : d⁻¹ ∈ Qc L M := ⟨M.inv_mem (hT.le hd.1), Subgroup.inv_mem _ hd.2⟩
  obtain ⟨s, hs⟩ := hA r hr.2 hr.1
  have hV : delta d⁻¹ r ∈ blockU L := H.nat.delta_mem H.normal hQ hr.2
  have hψ : H.D.ψe (delta d⁻¹ r) 1 = 0 := H.ψe_delta_one hQ hr.2 hs
  have hmem : delta d⁻¹ r ∈ ZR L T := ellTilde_le_ZR H hT hA ⟨hV, hψ⟩
  have e : ⁅d, r⁆ = delta d⁻¹ r := by simp [delta, commutatorElement_def]
  rw [e]
  exact hmem

theorem Dc_inf_centralizer_le (H : CoordData G L M n) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hA : H.Adapted T) {X : Subgroup G} (hX : X ≤ T ⊓ (Rl L T ⊔ Dc L T))
    (h3 : 3 ≤ (X ⊓ Dc L T).relIndex X) :
    Dc L T ⊓ Subgroup.centralizer (X : Set G) ≤ Ec L T ⊔ ZR L T := by
  classical
  rintro d ⟨hdD, hdC⟩
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc H.normal hT.le)
  have hdQ : d ∈ Qc L M := ⟨hT.le hdD.1, hdD.2⟩
  have hdinv : d⁻¹ ∈ Dc L T := inv_mem hdD
  have hcard : 3 ≤ Nat.card (↥X ⧸ (X ⊓ Dc L T).subgroupOf X) := by
    rw [← Subgroup.index_eq_card]
    exact h3
  have : Fintype (↥X ⧸ (X ⊓ Dc L T).subgroupOf X) := Fintype.ofFinite _
  have h3' : 2 < Fintype.card (↥X ⧸ (X ⊓ Dc L T).subgroupOf X) := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3'
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨x₃, rfl⟩ := QuotientGroup.mk_surjective c
  have hq : ∀ x y : ↥X, (x : G)⁻¹ * (y : G) ∈ Dc L T →
      (QuotientGroup.mk x : ↥X ⧸ (X ⊓ Dc L T).subgroupOf X) = QuotientGroup.mk y := by
    intro x y hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact ⟨X.mul_mem (X.inv_mem x.2) y.2, hxy⟩
  have hdec : ∀ x : ↥X, ∃ r ∈ Rl L T, ∃ q ∈ Dc L T, (x : G) = r * q := fun x =>
    (mem_sup_iff_mul hRn).1 (hX x.2).2
  choose r hr q hqD hxrq using hdec
  have hrL : ∀ x : ↥X, r x ∈ L := fun x => (hr x).2
  have hs : ∀ x : ↥X, ∃ s : Fq n, H.D.φ ⟨r x, hrL x⟩ = uMat s := fun x =>
    hA (r x) (hrL x) (hr x).1
  choose s hsφ using hs
  have hsne : ∀ x y : ↥X, (QuotientGroup.mk x : ↥X ⧸ (X ⊓ Dc L T).subgroupOf X) ≠
      QuotientGroup.mk y → s x ≠ s y := by
    intro x y hxy hss
    apply hxy
    apply hq
    have hφ : H.D.φ ⟨(r x)⁻¹ * r y, mul_mem (inv_mem (hrL x)) (hrL y)⟩ = 1 := by
      have e : (⟨(r x)⁻¹ * r y, mul_mem (inv_mem (hrL x)) (hrL y)⟩ : ↥L) =
          (⟨r x, hrL x⟩ : ↥L)⁻¹ * ⟨r y, hrL y⟩ := rfl
      rw [e, map_mul, map_inv, hsφ x, hsφ y, hss, inv_mul_cancel]
    have hW : (r x)⁻¹ * r y ∈ oTwoIn L := (H.D.φ_ker _).1 hφ
    have hWD : (r x)⁻¹ * r y ∈ Dc L T := oTwoIn_le_Dc H.nat H.le H.normal hT hW
    have hxy' : (x : G)⁻¹ * (y : G) = (q x)⁻¹ * ((r x)⁻¹ * r y) * q y := by
      rw [hxrq x, hxrq y]
      group
    rw [hxy']
    exact mul_mem (mul_mem (inv_mem (hqD x)) hWD) (hqD y)
  have hψ : ∀ x : ↥X, H.D.ψe (delta d (r x)) = 0 := by
    intro x
    have hcomm : (x : G) * d = d * (x : G) := Subgroup.mem_centralizer_iff.1 hdC x x.2
    rw [hxrq x] at hcomm
    have hρL := hrL x
    have hqx := hqD x
    have heE : d⁻¹ * q x * d * (q x)⁻¹ ∈ Ec L T := by
      have := Dc_comm_mem_Ec H.nat H.normal hT hdinv hqx
      simpa [commutatorElement_def] using this
    have hρe : r x * (d⁻¹ * q x * d * (q x)⁻¹) = (d⁻¹ * q x * d * (q x)⁻¹) * r x :=
      Subgroup.mem_centralizer_iff.1 heE.2 (r x) hρL
    have h1 : r x * d * (d⁻¹ * q x * d * (q x)⁻¹) = d * r x := by
      calc r x * d * (d⁻¹ * q x * d * (q x)⁻¹) = (r x * q x * d) * (q x)⁻¹ := by group
        _ = (d * (r x * q x)) * (q x)⁻¹ := by rw [hcomm]
        _ = d * r x := by group
    have hdel : delta d (r x) = (d⁻¹ * q x * d * (q x)⁻¹)⁻¹ := by
      calc delta d (r x)
          = d⁻¹ * (r x * d * (d⁻¹ * q x * d * (q x)⁻¹)) * (d⁻¹ * q x * d * (q x)⁻¹)⁻¹ *
            (r x)⁻¹ := by simp only [delta]; group
        _ = d⁻¹ * (d * r x) * (d⁻¹ * q x * d * (q x)⁻¹)⁻¹ * (r x)⁻¹ := by rw [h1]
        _ = r x * (d⁻¹ * q x * d * (q x)⁻¹)⁻¹ * (r x)⁻¹ := by group
        _ = (d⁻¹ * q x * d * (q x)⁻¹)⁻¹ := by
          have hc : Commute (r x) (d⁻¹ * q x * d * (q x)⁻¹) := hρe
          rw [hc.inv_right.eq]
          group
    have hVm : delta d (r x) ∈ blockU L := H.nat.delta_mem H.normal hdQ hρL
    have hZm : delta d (r x) ∈ blockZ L := by
      have hC : delta d (r x) ∈ Subgroup.centralizer (L : Set G) := by
        rw [hdel]
        exact (Subgroup.centralizer (L : Set G)).inv_mem heE.2
      exact Subgroup.mem_inf.2 ⟨hVm, hC⟩
    exact (H.D.ψe_eq_zero_iff hVm).2 hZm
  have hs12 := hsne x₁ x₂ hab
  have hs13 := hsne x₁ x₃ hac
  have hs23 := hsne x₂ x₃ hbc
  obtain ⟨v, hvV, hv1, hvC⟩ : ∃ v ∈ blockU L, H.D.ψe v 1 = 0 ∧
      d * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    by_cases h1 : s x₁ = 0
    · exact H.exists_blockU_of_two_roots ⟨d, hdQ⟩ (hrL x₂) (hrL x₃) (hsφ x₂) (hsφ x₃)
        (fun h => hs12 (h1.trans h.symm)) (fun h => hs13 (h1.trans h.symm)) hs23 (hψ x₂) (hψ x₃)
    · by_cases h2 : s x₂ = 0
      · exact H.exists_blockU_of_two_roots ⟨d, hdQ⟩ (hrL x₁) (hrL x₃) (hsφ x₁) (hsφ x₃)
          h1 (fun h => hs23 (h2.trans h.symm)) hs13 (hψ x₁) (hψ x₃)
      · exact H.exists_blockU_of_two_roots ⟨d, hdQ⟩ (hrL x₁) (hrL x₂) (hsφ x₁) (hsφ x₂)
          h1 h2 hs12 (hψ x₁) (hψ x₂)
  have hvT : v ∈ T := NatBlock.blockU_le_sylow H.le H.normal hT hvV
  have hE : d * v⁻¹ ∈ Ec L T := ⟨T.mul_mem hdD.1 (T.inv_mem hvT), hvC⟩
  have hvZ : v ∈ ZR L T := ellTilde_le_ZR H hT hA ⟨hvV, hv1⟩
  have := mul_mem (Subgroup.mem_sup_left hE) (Subgroup.mem_sup_right hvZ)
  simpa using this

namespace Aux

omit [Finite G] in
theorem comm_mem_of_abelian_mod {A B N S : Subgroup G} (hNS : N ≤ S)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hAS : A ≤ S) (hBS : B ≤ S)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hS : S ≤ A ⊔ B)
    (hAA : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ N) (hBB : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ N)
    (hAB' : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ N := by
  have hnorm : (N.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNS).2 hSN
  let π : ↥S →* ↥S ⧸ N.subgroupOf S := QuotientGroup.mk' (N.subgroupOf S)
  have hπ : ∀ (x y : G) (hx : x ∈ S) (hy : y ∈ S), ⁅x, y⁆ ∈ N →
      Commute (π ⟨x, hx⟩) (π ⟨y, hy⟩) := by
    intro x y hx hy hxy
    have h1 : (⁅(⟨x, hx⟩ : ↥S), ⟨y, hy⟩⁆ : ↥S) ∈ N.subgroupOf S := hxy
    have h2 : π ⁅(⟨x, hx⟩ : ↥S), ⟨y, hy⟩⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul hAB).1 (hS hx)
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_mul hAB).1 (hS hy)
  have e : ∀ (a b : G) (ha : a ∈ A) (hb : b ∈ B) (hx : a * b ∈ S),
      π ⟨a * b, hx⟩ = π ⟨a, hAS ha⟩ * π ⟨b, hBS hb⟩ := fun a b ha hb hx => by
    rw [← map_mul]
    rfl
  have c1 : Commute (π ⟨a, hAS ha⟩) (π ⟨a', hAS ha'⟩) := hπ _ _ _ _ (hAA a ha a' ha')
  have c2 : Commute (π ⟨a, hAS ha⟩) (π ⟨b', hBS hb'⟩) := hπ _ _ _ _ (hAB' a ha b' hb')
  have c3 : Commute (π ⟨b, hBS hb⟩) (π ⟨a', hAS ha'⟩) := (hπ _ _ _ _ (hAB' a' ha' b hb)).symm
  have c4 : Commute (π ⟨b, hBS hb⟩) (π ⟨b', hBS hb'⟩) := hπ _ _ _ _ (hBB b hb b' hb')
  have hc : Commute (π ⟨a * b, hx⟩) (π ⟨a' * b', hy⟩) := by
    rw [e a b ha hb hx, e a' b' ha' hb' hy]
    exact (c1.mul_right c2).mul_left (c3.mul_right c4)
  have h1 : π ⁅(⟨a * b, hx⟩ : ↥S), ⟨a' * b', hy⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hc
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

end Aux

theorem rd_class_facts (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hWD : ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w)
    (hRcl : ∀ x ∈ Rl L T, ∀ y ∈ Rl L T, ⁅x, y⁆ ∈ ZR L T) (hRsq : ∀ r ∈ Rl L T, r ^ 2 ∈ ZR L T)
    (hRD : ∀ d ∈ Dc L T, ∀ r ∈ Rl L T, ⁅d, r⁆ ∈ ZR L T)
    (hfix : Dc L T ⊓ Subgroup.centralizer (Rl L T : Set G) ≤ Ec L T ⊔ ZR L T)
    (hTRD : T ≤ Rl L T ⊔ Dc L T) :
    ZR L T ≤ ZT T ∧ ⁅⁅T, T⁆, T⁆ ≤ Ec L T ∧ ⁅T, T⁆ ≤ ZR L T ⊔ Ec L T ∧
      (∀ t ∈ T, t ^ 2 ∈ ZR L T ⊔ Ec L T) ∧ ⁅Rl L T, T⁆ ≤ ZR L T ∧
      (T ⊓ Subgroup.centralizer (Rl L T : Set G) ≤ ZR L T ⊔ Ec L T) ∧
      ZT T ≤ ZR L T ⊔ Ec L T := by
  have hTM : T ≤ M := hT.le
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hTM)
  have hdec : ∀ t ∈ T, ∃ r ∈ Rl L T, ∃ d ∈ Dc L T, t = r * d := fun t ht =>
    (mem_sup_iff_mul hRn).1 (hTRD ht)
  have hVR : blockU L ≤ Rl L T := blockU_le_Rl hLM hMN hT
  have hZRW : ZR L T ≤ oTwoIn L := by
    intro z hz
    obtain ⟨hzR, hzc⟩ := mem_ZR.1 hz
    have hzD : z ∈ Dc L T := ⟨hzR.1, Subgroup.mem_centralizer_iff.2 fun v hv => hzc v (hVR hv)⟩
    rw [← Rl_inf_Dc h hLM hMN hT]
    exact ⟨hzR, hzD⟩
  have hZcomm : ∀ z ∈ ZR L T, ∀ t ∈ T, t * z = z * t := by
    intro z hz t ht
    obtain ⟨r, hr, d, hd, rfl⟩ := hdec t ht
    have h1 : d * z = z * d := (hWD z (hZRW hz) d hd).symm
    have h2 : r * z = z * r := (mem_ZR.1 hz).2 r hr
    calc r * d * z = r * (d * z) := by group
      _ = r * (z * d) := by rw [h1]
      _ = (r * z) * d := by group
      _ = (z * r) * d := by rw [h2]
      _ = z * (r * d) := by group
  have hZT : ZR L T ≤ ZT T := fun z hz =>
    mem_ZT.2 ⟨Rl_le_T (ZR_le_Rl hz), hZcomm z hz⟩
  have hconj : ∀ z ∈ ZR L T, ∀ t ∈ T, t * z * t⁻¹ = z := by
    intro z hz t ht
    rw [hZcomm z hz t ht, mul_inv_cancel_right]
  have hTZn : T ≤ Subgroup.normalizer (ZR L T : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hconj y hy t ht]
      exact hy
    · intro hy
      have := hconj _ hy t⁻¹ (T.inv_mem ht)
      have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rw [e] at this
      rw [this]
      exact hy
  have hTEn : T ≤ Subgroup.normalizer (Ec L T : Set G) := le_normalizer_Ec hMN hTM
  have hNn : T ≤ Subgroup.normalizer ((ZR L T ⊔ Ec L T : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_sup (hTZn ht) (hTEn ht)
  have hNT : ZR L T ⊔ Ec L T ≤ T := sup_le (ZR_le_Rl.trans Rl_le_T) Ec_le_T
  have hb : ⁅T, T⁆ ≤ ZR L T ⊔ Ec L T := by
    refine Subgroup.commutator_le.2 ?_
    refine comm_mem_of_abelian_mod (A := Rl L T) (B := Dc L T) hNT hNn Rl_le_T Dc_le_T hRn hTRD
      (fun a ha a' ha' => Subgroup.mem_sup_left (hRcl a ha a' ha'))
      (fun b hb b' hb' => Subgroup.mem_sup_right (Dc_comm_mem_Ec h hMN hT hb hb'))
      (fun a ha b hb => by
        have h2 : ⁅a, b⁆ ∈ ZR L T := by
          rw [← commutatorElement_inv]
          exact (ZR L T).inv_mem (hRD b hb a ha)
        exact Subgroup.mem_sup_left h2)
  have hc : ⁅⁅T, T⁆, T⁆ ≤ Ec L T := by
    refine (Subgroup.commutator_mono hb le_rfl).trans ?_
    refine Subgroup.commutator_le.2 fun g hg t ht => ?_
    have hZRn : ZR L T ≤ Subgroup.normalizer (Ec L T : Set G) :=
      (ZR_le_Rl.trans Rl_le_T).trans hTEn
    obtain ⟨z, hz, e, he, rfl⟩ := (mem_sup_iff_mul hZRn).1 hg
    have hid : ⁅z * e, t⁆ = z * ⁅e, t⁆ * z⁻¹ * ⁅z, t⁆ := by
      simp only [commutatorElement_def]
      group
    have hzt : ⁅z, t⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hZcomm z hz t ht).symm
    have hmemE : ⁅e, t⁆ ∈ Ec L T := by
      have h1 : t * e⁻¹ * t⁻¹ ∈ Ec L T :=
        (Subgroup.mem_normalizer_iff.1 (hTEn ht) e⁻¹).1 ((Ec L T).inv_mem he)
      have e' : ⁅e, t⁆ = e * (t * e⁻¹ * t⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e']
      exact (Ec L T).mul_mem he h1
    have hcomm : z * ⁅e, t⁆ * z⁻¹ = ⁅e, t⁆ := by
      have := hZcomm z hz ⁅e, t⁆ (comm_mem_subgroup (Ec_le_T he) ht)
      rw [← this, mul_inv_cancel_right]
    rw [hid, hzt, mul_one, hcomm]
    exact hmemE
  have hd : ∀ t ∈ T, t ^ 2 ∈ ZR L T ⊔ Ec L T := by
    intro t ht
    obtain ⟨r, hr, d, hd, rfl⟩ := hdec t ht
    have hcZ : ⁅d, r⁆ ∈ ZR L T := hRD d hd r hr
    have h1 : r * ⁅d, r⁆ * r⁻¹ = ⁅d, r⁆ := by
      rw [(mem_ZR.1 hcZ).2 r hr, mul_inv_cancel_right]
    have e : (r * d) ^ 2 = ⁅d, r⁆ * r ^ 2 * d ^ 2 := by
      calc (r * d) ^ 2 = (r * ⁅d, r⁆ * r⁻¹) * r ^ 2 * d ^ 2 := by
            simp only [commutatorElement_def, pow_two]
            group
        _ = ⁅d, r⁆ * r ^ 2 * d ^ 2 := by rw [h1]
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hcZ) (Subgroup.mem_sup_left (hRsq r hr)))
      (Subgroup.mem_sup_right (Dc_sq_mem_Ec h hMN hT hd))
  have he : ⁅Rl L T, T⁆ ≤ ZR L T := by
    refine Subgroup.commutator_le.2 fun r hr t ht => ?_
    obtain ⟨r', hr', d, hd, rfl⟩ := hdec t ht
    have e : ⁅r, r' * d⁆ = ⁅r, r'⁆ * (r' * ⁅r, d⁆ * r'⁻¹) := by
      simp only [commutatorElement_def]
      group
    have h1 : ⁅r, d⁆ ∈ ZR L T := by
      rw [← commutatorElement_inv]
      exact (ZR L T).inv_mem (hRD d hd r hr)
    have h2 : r' * ⁅r, d⁆ * r'⁻¹ = ⁅r, d⁆ := by
      rw [(mem_ZR.1 h1).2 r' hr', mul_inv_cancel_right]
    rw [e, h2]
    exact (ZR L T).mul_mem (hRcl r hr r' hr') h1
  have hf : T ⊓ Subgroup.centralizer (Rl L T : Set G) ≤ ZR L T ⊔ Ec L T := by
    rintro t ⟨htT, htC⟩
    obtain ⟨r, hr, d, hd, rfl⟩ := hdec t htT
    have hrC : r ∈ Subgroup.centralizer (blockU L : Set G) := by
      have h1 : r * d ∈ Subgroup.centralizer (blockU L : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVR) htC
      have h2 : d⁻¹ ∈ Subgroup.centralizer (blockU L : Set G) :=
        (Subgroup.centralizer (blockU L : Set G)).inv_mem hd.2
      have := (Subgroup.centralizer (blockU L : Set G)).mul_mem h1 h2
      simpa using this
    have hrW : r ∈ oTwoIn L := by
      rw [← Rl_inf_Dc h hLM hMN hT]
      exact ⟨hr, hr.1, hrC⟩
    have htD : r * d ∈ Dc L T := (Dc L T).mul_mem (oTwoIn_le_Dc h hLM hMN hT hrW) hd
    have := hfix ⟨htD, htC⟩
    rwa [sup_comm] at this
  refine ⟨hZT, hc, hb, hd, he, hf, ?_⟩
  intro t ht
  obtain ⟨htT, htc⟩ := mem_ZT.1 ht
  exact hf ⟨htT, Subgroup.mem_centralizer_iff.2 fun r hr => htc r (Rl_le_T hr)⟩

theorem rd_fixed_points (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {X : Subgroup G} (hX : X ≤ T ⊓ (Rl L T ⊔ Dc L T))
    (h3 : 3 ≤ (X ⊓ Dc L T).relIndex X) :
    Dc L T ⊓ Subgroup.centralizer (X : Set G) ≤ Ec L T ⊔ ZR L T := by
  obtain ⟨H, hA⟩ := exists_utri_coord hs.hyp.natBlock hs.hyp.le (hs.hyp.normal hE1) hs.sylow
  exact Dc_inf_centralizer_le H hs.sylow hA hX h3

end CFSG.CGT.PushingUpLit.T2KSW
