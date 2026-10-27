module

public import CFSG.CGT.PushingUpLit.T2KSW.FieldAutWeakClosure
public import CFSG.CGT.PushingUpLit.T2KSW.FieldAutFamily
public import CFSG.CGT.PushingUpLit.T2KSW.WCoverChain

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KR CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.JonesParshall
open scoped commutatorElement
open Aux

namespace Syl

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

@[expose] def LemmaCNT (L T A : Subgroup G) : Prop :=
  ∀ B : Subgroup G, B ≤ T → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → ¬ B ≤ Rl L T ⊔ Dc L T →
    Nat.card B < Nat.card A ∧ (B ⊓ Ec L T = ⊥ → 2 * Nat.card B < Nat.card A)

omit [Finite G] in
theorem mem_normalizer_of_comm_mem {B : Subgroup G} {x : G} (hx : ∀ b ∈ B, ⁅x, b⁆ ∈ B)
    (hx' : ∀ b ∈ B, ⁅x⁻¹, b⁆ ∈ B) : x ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by simp [commutatorElement_def]
  constructor
  · intro hy
    rw [e1]
    exact B.mul_mem (hx y hy) hy
  · intro hy
    have e2 : y = ⁅x⁻¹, x * y * x⁻¹⁆ * (x * y * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact B.mul_mem (hx' _ hy) hy

omit [Finite G] in
theorem le_normalizer_of_comm_mem {X B : Subgroup G} (h : ∀ x ∈ X, ∀ b ∈ B, ⁅x, b⁆ ∈ B) :
    X ≤ Subgroup.normalizer (B : Set G) :=
  fun x hx => mem_normalizer_of_comm_mem (h x hx) (h x⁻¹ (X.inv_mem hx))

omit [Finite G] in
theorem normalizer_map_conj_le {A M : Subgroup G} (hAN : Subgroup.normalizer (A : Set G) ≤ M)
    (g : G) :
    Subgroup.normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      M.map (MulAut.conj g).toMonoidHom := by
  intro t ht
  rw [mem_map_conj_iff]
  apply hAN
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have h1 := Subgroup.mem_normalizer_iff.1 ht (g * a * g⁻¹)
  rw [mem_map_conj_iff, mem_map_conj_iff] at h1
  have e1 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
  have e2 : g⁻¹ * (t * (g * a * g⁻¹) * t⁻¹) * g = (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ := by
    group
  rw [e1, e2] at h1
  exact h1

theorem mem_of_map_conj_le_Dc (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsMaximalFamily L T A) {g : G}
    (hBD : A.map (MulAut.conj g).toMonoidHom ≤ Dc L T) : g ∈ M := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hWD : ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w := Dc_centralizes_oTwoIn hs hE1
  set B : Subgroup G := A.map (MulAut.conj g).toMonoidHom with hB
  have hW'C : (oTwoIn L).map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer (A : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hgaD : g * a * g⁻¹ ∈ Dc L T := hBD ⟨a, ha, by simp⟩
    have h1 := hWD w hw _ hgaD
    have e1 : (MulAut.conj g⁻¹).toMonoidHom w * a = g⁻¹ * (w * (g * a * g⁻¹)) * g := by
      simp [mul_assoc]
    have e2 : a * (MulAut.conj g⁻¹).toMonoidHom w = g⁻¹ * ((g * a * g⁻¹) * w) * g := by
      simp [mul_assoc]
    rw [e2, ← h1, e1]
  have hW'2 : IsPGroup 2 ↥((oTwoIn L).map (MulAut.conj g⁻¹).toMonoidHom) :=
    (isPGroup_oTwoIn L).map _
  have hsylow : IsSylowOf 2 A (Subgroup.centralizer (A : Set G)) :=
    family_isSylowOf_centralizer hs hE1 hA
  have hAc : A ≤ Subgroup.centralizer (A : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hA.1.comm b hb a ha
  have hsup2 : IsPGroup 2 ↥(A ⊔ (oTwoIn L).map (MulAut.conj g⁻¹).toMonoidHom) :=
    IsPGroup.to_sup_of_normal_left' hsylow.isPGroup hW'2
      (hW'C.trans (Subgroup.centralizer_le_normalizer _))
  have hsupA : A ⊔ (oTwoIn L).map (MulAut.conj g⁻¹).toMonoidHom = A :=
    hsylow.eq_of_le le_sup_left (sup_le hAc hW'C) hsup2
  have hW'A : (oTwoIn L).map (MulAut.conj g⁻¹).toMonoidHom ≤ A :=
    le_sup_right.trans hsupA.le
  have hWB : oTwoIn L ≤ B := by
    intro w hw
    rw [hB, mem_map_conj_iff]
    exact hW'A ⟨w, hw, by simp⟩
  have hLB : L ≤ Subgroup.normalizer (B : Set G) := by
    refine le_normalizer_of_comm_mem fun l hl b hb => ?_
    have hbD : b ∈ Dc L T := hBD hb
    have h1 : ⁅b, l⁆ ∈ oTwoIn L := h.comm_centralizer_mem_oTwoIn hMN ⟨hs.sylow.le hbD.1, hbD.2⟩ hl
    rw [← commutatorElement_inv]
    exact B.inv_mem (hWB h1)
  have hLM' : L ≤ M.map (MulAut.conj g).toMonoidHom :=
    hLB.trans (normalizer_map_conj_le (family_normalizer_le hs hE1 hA.1) g)
  have hmax : IsMaximalTwoLocal (M.map (MulAut.conj g).toMonoidHom) :=
    CFSG.RankThree.PartTwo.Late.isMaximalTwoLocal_map hs.hyp.maxLocal (MulAut.conj g)
  have hmem : M.map (MulAut.conj g).toMonoidHom ∈ maximalTwoLocalsContaining (L : Set G) :=
    ⟨hmax, fun x hx => hLM' hx⟩
  rw [hs.hyp.unique] at hmem
  exact CFSG.RankThree.PartTwo.Late.mem_of_map_conj_eq_of_isMaximalTwoLocal hs.hyp.maxLocal hmem


omit [Finite G] in
theorem mem_normalizer_of_forall_comm {X : Subgroup G} {x : G} (h : ∀ y ∈ X, x * y = y * x) :
    x ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : ∀ z ∈ X, x * z * x⁻¹ = z := fun z hz => by rw [h z hz]; group
  constructor
  · intro hy
    rw [e y hy]
    exact hy
  · intro hy
    have h1 := h _ hy
    have h2 : x * y * x⁻¹ = y := by
      have : x * (x * y * x⁻¹) = x * y := by rw [h1]; group
      exact mul_left_cancel this
    rwa [h2] at hy

theorem ZR_le_oTwoIn (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    ZR L T ≤ oTwoIn L := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  intro z hz
  obtain ⟨hzR, hzc⟩ := mem_ZR.1 hz
  have hzD : z ∈ Dc L T := ⟨hzR.1, Subgroup.mem_centralizer_iff.2 fun v hv =>
    hzc v (blockU_le_Rl hLM hMN hs.sylow hv)⟩
  rw [← Rl_inf_Dc h hLM hMN hs.sylow]
  exact ⟨hzR, hzD⟩

theorem comm_mem_ZR_sup_Ec (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) :
    ∀ x ∈ Rl L T ⊔ Dc L T, ∀ y ∈ Rl L T ⊔ Dc L T, ⁅x, y⁆ ∈ ZR L T ⊔ Ec L T := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  obtain ⟨H, hAd⟩ := exists_utri_coord h hLM hMN hT
  have hWD : ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w := Dc_centralizes_oTwoIn hs hE1
  have hZW := ZR_le_oTwoIn hs hE1
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  have hRN : Rl L T ≤ Subgroup.normalizer ((ZR L T ⊔ Ec L T : Subgroup G) : Set G) := fun r hr =>
    mem_normalizer_sup
      (mem_normalizer_of_forall_comm fun z hz => (mem_ZR.1 hz).2 r hr)
      (mem_normalizer_of_forall_comm fun e he => (Subgroup.mem_centralizer_iff.1 he.2 r
        (Rl_le_L hr)))
  have hDN : Dc L T ≤ Subgroup.normalizer ((ZR L T ⊔ Ec L T : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_sup
      (mem_normalizer_of_forall_comm fun z hz => (hWD z (hZW hz) d hd).symm)
      (mem_normalizer_Ec hMN (hT.le (Dc_le_T hd)) (Subgroup.le_normalizer (Dc_le_T hd)))
  refine comm_mem_of_abelian_mod (A := Rl L T) (B := Dc L T) (N := ZR L T ⊔ Ec L T)
    (S := Rl L T ⊔ Dc L T) (sup_le (ZR_le_Rl.trans le_sup_left) (Ec_le_Dc.trans le_sup_right))
    (sup_le hRN hDN) le_sup_left le_sup_right hRn le_rfl
    (fun a ha a' ha' => Subgroup.mem_sup_left (comm_mem_ZR_of_wleVE H hT hAd hWVE ha ha'))
    (fun b hb b' hb' => Subgroup.mem_sup_right (Dc_comm_mem_Ec h hMN hT hb hb'))
    (fun a ha b hb => ?_)
  have h2 : ⁅a, b⁆ ∈ ZR L T := by
    rw [← commutatorElement_inv]
    exact (ZR L T).inv_mem (comm_Dc_Rl_mem_ZR H hT hAd hb ha)
  exact Subgroup.mem_sup_left h2

theorem relIndex_Dc_Rl_sup_Dc (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    (Dc L T).relIndex (Rl L T ⊔ Dc L T) = 2 ^ n := by
  have h1 := Subgroup.relIndex_mul_card (H := Dc L T) (K := Rl L T ⊔ Dc L T)
  rw [inf_of_le_left le_sup_right, card_Rl_sup_Dc hs.hyp.natBlock hs.hyp.le (hs.hyp.normal hE1)
    hs.sylow] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

theorem normal_of_three_le (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsFamily L T A)
    {B : Subgroup G} (hBT : B ≤ Rl L T ⊔ Dc L T) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card B = Nat.card A) (h3 : 3 ≤ (B ⊓ Dc L T).relIndex B) :
    Rl L T ⊔ Dc L T ≤ Subgroup.normalizer (B : Set G) := by
  have hX : B ≤ T ⊓ (Rl L T ⊔ Dc L T) := le_inf (hBT.trans (sup_le Rl_le_T Dc_le_T)) hBT
  have hfix := rd_fixed_points hs hE1 hX h3
  have hBD : B ⊓ Dc L T ≤ Ec L T ⊔ ZR L T := fun x hx =>
    hfix ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun b hb => hcomm b hb x hx.1⟩
  have hq : (2 : ℕ) ^ n * (2 ^ n * Nat.card ↥(Ec L T)) =
      (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by ring
  have hZE : Nat.card ↥(Ec L T ⊔ ZR L T) ≤ 2 ^ n * Nat.card ↥(Ec L T) := by
    rw [sup_comm]
    exact card_ZR_sup_Ec_le' hs hE1 hWVE
  have h1 : (B ⊓ Dc L T).relIndex B * Nat.card ↥(B ⊓ Dc L T) = Nat.card B := by
    have := Subgroup.relIndex_mul_card (H := B ⊓ Dc L T) (K := B)
    rwa [inf_of_le_left inf_le_left] at this
  have hp : (B ⊓ Dc L T).relIndex B ≤ 2 ^ n := by
    rw [Subgroup.inf_relIndex_left, ← relIndex_Dc_Rl_sup_Dc hs hE1]
    exact Subgroup.relIndex_le_of_le_right hBT (by
      rw [relIndex_Dc_Rl_sup_Dc hs hE1]
      positivity)
  have hb : Nat.card ↥(B ⊓ Dc L T) ≤ 2 ^ n * Nat.card ↥(Ec L T) :=
    (Subgroup.card_le_of_le hBD).trans hZE
  have hAcard := family_card_le hs hE1 hA
  set p := (B ⊓ Dc L T).relIndex B with hpdef
  set b := Nat.card ↥(B ⊓ Dc L T) with hbdef
  have hbpos : 0 < b := Nat.card_pos
  have hpb : p * b ≤ (2 ^ n) * (2 ^ n * Nat.card ↥(Ec L T)) :=
    Nat.mul_le_mul hp hb
  have hbEq : b = 2 ^ n * Nat.card ↥(Ec L T) := by
    by_contra hne
    have hlt : b < 2 ^ n * Nat.card ↥(Ec L T) := lt_of_le_of_ne hb hne
    have : p * b < (2 ^ n) * (2 ^ n * Nat.card ↥(Ec L T)) := by
      calc p * b ≤ 2 ^ n * b := Nat.mul_le_mul_right _ hp
        _ < 2 ^ n * (2 ^ n * Nat.card ↥(Ec L T)) := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    omega
  have hBDeq : B ⊓ Dc L T = Ec L T ⊔ ZR L T :=
    Subgroup.eq_of_le_of_card_ge hBD (by rw [← hbEq] at hZE; exact hZE)
  intro x hx
  refine mem_normalizer_of_comm_mem (fun y hy => ?_) (fun y hy => ?_)
  · have hc := comm_mem_ZR_sup_Ec hs hE1 hWVE x hx y (hBT hy)
    rw [sup_comm, ← hBDeq] at hc
    exact hc.1
  · have hx' : x⁻¹ ∈ Rl L T ⊔ Dc L T := (Rl L T ⊔ Dc L T).inv_mem hx
    have hc := comm_mem_ZR_sup_Ec hs hE1 hWVE x⁻¹ hx' y (hBT hy)
    rw [sup_comm, ← hBDeq] at hc
    exact hc.1


section Coords

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

open Classical in
@[expose] noncomputable def vcoG (u : G) : Fin 2 → Fq n :=
  if h : u ∈ Qc L M then H.vco ⟨u, h⟩ else 0

open Classical in
@[expose] noncomputable def thetaG (u : G) : Fq n :=
  if h : u ∈ Qc L M then H.theta ⟨u, h⟩ else 0

theorem vcoG_of_mem {u : G} (hu : u ∈ Qc L M) : vcoG H u = H.vco ⟨u, hu⟩ := by
  simp [vcoG, hu]

theorem thetaG_of_mem {u : G} (hu : u ∈ Qc L M) : thetaG H u = H.theta ⟨u, hu⟩ := by
  simp [thetaG, hu]

theorem vcoG_mul {u u' : G} (hu : u ∈ Qc L M) (hu' : u' ∈ Qc L M) :
    vcoG H (u * u') = vcoG H u + vcoG H u' := by
  rw [vcoG_of_mem H (mul_mem hu hu'), vcoG_of_mem H hu, vcoG_of_mem H hu']
  exact (H.vco_mul ⟨u, hu⟩ ⟨u', hu'⟩).1

theorem thetaG_mul {u u' : G} (hu : u ∈ Qc L M) (hu' : u' ∈ Qc L M) :
    thetaG H (u * u') = thetaG H u + thetaG H u' := by
  rw [thetaG_of_mem H (mul_mem hu hu'), thetaG_of_mem H hu, thetaG_of_mem H hu']
  exact (H.vco_mul ⟨u, hu⟩ ⟨u', hu'⟩).2

theorem vcoG_one : vcoG H 1 = 0 := by
  have h := vcoG_mul H (one_mem (Qc L M)) (one_mem (Qc L M))
  rw [one_mul] at h
  exact left_eq_add.1 h

theorem thetaG_one : thetaG H 1 = 0 := by
  have h := thetaG_mul H (one_mem (Qc L M)) (one_mem (Qc L M))
  rw [one_mul] at h
  exact left_eq_add.1 h

theorem vcoG_inv {u : G} (hu : u ∈ Qc L M) : vcoG H u⁻¹ = - vcoG H u := by
  have h := vcoG_mul H ((Qc L M).inv_mem hu) hu
  rw [inv_mul_cancel, vcoG_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem thetaG_inv {u : G} (hu : u ∈ Qc L M) : thetaG H u⁻¹ = - thetaG H u := by
  have h := thetaG_mul H ((Qc L M).inv_mem hu) hu
  rw [inv_mul_cancel, thetaG_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem coordsG_eq_zero_iff {u : G} (hu : u ∈ Qc L M) :
    (vcoG H u = 0 ∧ thetaG H u = 0) ↔ u ∈ Subgroup.centralizer (L : Set G) := by
  rw [vcoG_of_mem H hu, thetaG_of_mem H hu]
  exact H.coords_eq_zero_iff ⟨u, hu⟩

theorem coordsG_blockU {v : G} (hv : v ∈ blockU L) :
    vcoG H v = H.D.ψe v ∧ thetaG H v = 0 := by
  have hvQ : v ∈ Qc L M := H.blockU_le_Qc hv
  rw [vcoG_of_mem H hvQ, thetaG_of_mem H hvQ]
  exact H.vco_blockU hv

theorem thetaG_eq_zero_iff {u : G} (hu : u ∈ Qc L M) :
    thetaG H u = 0 ↔ ∃ v ∈ blockU L, u * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [thetaG_of_mem H hu]
  exact H.theta_eq_zero_iff ⟨u, hu⟩

theorem ψe_delta_uMatG {u : G} (hu : u ∈ Qc L M) {x : G} (hx : x ∈ L) {s : Fq n}
    (hφ : H.D.φ ⟨x, hx⟩ = uMat s) :
    H.D.ψe (delta u x) = ![s * vcoG H u 1 + thetaG H u * sqrtF s, 0] := by
  rw [vcoG_of_mem H hu, thetaG_of_mem H hu]
  exact H.ψe_delta_uMat ⟨u, hu⟩ hx hφ


theorem coordsG_of_mem_Ec (hT : IsSylowOf 2 T M) {u : G} (hu : u ∈ Ec L T) :
    vcoG H u = 0 ∧ thetaG H u = 0 :=
  (coordsG_eq_zero_iff H ⟨hT.le hu.1, Subgroup.centralizer_le
    (SetLike.coe_subset_coe.2 (blockU_le L)) hu.2⟩).2 hu.2

theorem ψe_delta_eq_zero_of_comm (hT : IsSylowOf 2 T M) {d : G} (hd : d ∈ Dc L T) {r q : G}
    (hr : r ∈ Rl L T) (hq : q ∈ Dc L T) (hcomm : (r * q) * d = d * (r * q)) :
    H.D.ψe (delta d r) = 0 := by
  have hdinv : d⁻¹ ∈ Dc L T := inv_mem hd
  have hdQ : d ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hT.le hd.1, hd.2⟩
  have hρL : r ∈ L := hr.2
  have heE : d⁻¹ * q * d * q⁻¹ ∈ Ec L T := by
    have := Dc_comm_mem_Ec H.nat H.normal hT hdinv hq
    simpa [commutatorElement_def] using this
  have hρe : r * (d⁻¹ * q * d * q⁻¹) = (d⁻¹ * q * d * q⁻¹) * r :=
    Subgroup.mem_centralizer_iff.1 heE.2 r hρL
  have h1 : r * d * (d⁻¹ * q * d * q⁻¹) = d * r := by
    calc r * d * (d⁻¹ * q * d * q⁻¹) = (r * q * d) * q⁻¹ := by group
      _ = (d * (r * q)) * q⁻¹ := by rw [hcomm]
      _ = d * r := by group
  have hdel : delta d r = (d⁻¹ * q * d * q⁻¹)⁻¹ := by
    calc delta d r
        = d⁻¹ * (r * d * (d⁻¹ * q * d * q⁻¹)) * (d⁻¹ * q * d * q⁻¹)⁻¹ * r⁻¹ := by
          simp only [delta]; group
      _ = d⁻¹ * (d * r) * (d⁻¹ * q * d * q⁻¹)⁻¹ * r⁻¹ := by rw [h1]
      _ = r * (d⁻¹ * q * d * q⁻¹)⁻¹ * r⁻¹ := by group
      _ = (d⁻¹ * q * d * q⁻¹)⁻¹ := by
        have hc : Commute r (d⁻¹ * q * d * q⁻¹) := hρe
        rw [hc.inv_right.eq]
        group
  have hVm : delta d r ∈ blockU L := H.nat.delta_mem H.normal hdQ hρL
  have hZm : delta d r ∈ blockZ L := by
    have hC : delta d r ∈ Subgroup.centralizer (L : Set G) := by
      rw [hdel]
      exact (Subgroup.centralizer (L : Set G)).inv_mem heE.2
    exact Subgroup.mem_inf.2 ⟨hVm, hC⟩
  exact (H.D.ψe_eq_zero_iff hVm).2 hZm

theorem rel_of_comm (hT : IsSylowOf 2 T M) {u : G} (hu : u ∈ Dc L T) {r q : G}
    (hr : r ∈ Rl L T) (hq : q ∈ Dc L T) {s : Fq n} (hφ : H.D.φ ⟨r, hr.2⟩ = uMat s)
    (hcomm : (r * q) * u = u * (r * q)) :
    s * vcoG H u 1 + thetaG H u * sqrtF s = 0 := by
  have hψ := ψe_delta_eq_zero_of_comm H hT hu hr hq hcomm
  have hQ : u ∈ Qc L M := ⟨hT.le hu.1, hu.2⟩
  rw [ψe_delta_uMatG H hQ hr.2 hφ] at hψ
  have := congrFun hψ 0
  simpa using this

theorem mem_Ec_of_coords (hT : IsSylowOf 2 T M) {u : G} (hu : u ∈ Dc L T) {s : Fq n}
    (hs0 : s ≠ 0) (hrel : s * vcoG H u 1 + thetaG H u * sqrtF s = 0) (h0 : vcoG H u 0 = 0)
    (hθ : thetaG H u = 0) : u ∈ Ec L T := by
  have h1 : vcoG H u 1 = 0 := by
    rw [hθ, zero_mul, add_zero] at hrel
    exact (mul_eq_zero.1 hrel).resolve_left hs0
  have hv : vcoG H u = 0 := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hQ : u ∈ Qc L M := ⟨hT.le hu.1, hu.2⟩
  exact ⟨hu.1, (coordsG_eq_zero_iff H hQ).1 ⟨hv, hθ⟩⟩

@[expose] noncomputable def w0Hom (K : Subgroup G) (hK : K ≤ Qc L M) :
    ↥K →* Multiplicative (Fq n) where
  toFun u := Multiplicative.ofAdd (vcoG H (u : G) 0)
  map_one' := by
    show Multiplicative.ofAdd (vcoG H 1 0) = 1
    rw [vcoG_one]
    rfl
  map_mul' u u' := by
    show Multiplicative.ofAdd (vcoG H ((u : G) * u') 0) = _
    rw [vcoG_mul H (hK u.2) (hK u'.2)]
    rfl

@[expose] noncomputable def thetaHom (K : Subgroup G) (hK : K ≤ Qc L M) :
    ↥K →* Multiplicative (Fq n) where
  toFun u := Multiplicative.ofAdd (thetaG H (u : G))
  map_one' := by
    show Multiplicative.ofAdd (thetaG H 1) = 1
    rw [thetaG_one]
    rfl
  map_mul' u u' := by
    show Multiplicative.ofAdd (thetaG H ((u : G) * u')) = _
    rw [thetaG_mul H (hK u.2) (hK u'.2)]
    rfl

end Coords

theorem card_le_ker_mul {K X Y : Type*} [Group K] [Finite K] [Group X] [Finite X] [Group Y]
    [Finite Y] (f : K →* X) (θ : K →* Y) :
    Nat.card K ≤ Nat.card (f.prod θ).ker * (Nat.card X * Nat.card θ.range) ∧
      (Nat.card K = Nat.card (f.prod θ).ker * (Nat.card X * Nat.card θ.range) →
        ∀ (x : X) (y : Y), y ∈ θ.range → ∃ k, f k = x ∧ θ k = y) := by
  have hmul := Subgroup.card_ker_mul_card_range (f.prod θ)
  have hmem : ∀ p : (f.prod θ).range, p.1.2 ∈ θ.range := by
    rintro ⟨p, k, rfl⟩
    exact ⟨k, rfl⟩
  let φ : (f.prod θ).range → X × θ.range := fun p => (p.1.1, ⟨p.1.2, hmem p⟩)
  have hφ : Function.Injective φ := by
    intro p p' h
    have h1 : (φ p).1 = (φ p').1 := congrArg Prod.fst h
    have h2 : (φ p).2 = (φ p').2 := congrArg Prod.snd h
    have h2' : p.1.2 = p'.1.2 := congrArg Subtype.val h2
    exact Subtype.ext (Prod.ext h1 h2')
  have hcard : Nat.card (f.prod θ).range ≤ Nat.card X * Nat.card θ.range := by
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_prod] at this
  have hkpos : 0 < Nat.card (f.prod θ).ker := Nat.card_pos
  refine ⟨?_, fun heq x y hy => ?_⟩
  · rw [← hmul]
    exact Nat.mul_le_mul_left _ hcard
  · have h1 : Nat.card (f.prod θ).range = Nat.card X * Nat.card θ.range := by
      apply Nat.eq_of_mul_eq_mul_left hkpos
      rw [hmul, heq]
    have hbij : Function.Bijective φ := by
      refine hφ.bijective_of_nat_card_le ?_
      rw [Nat.card_prod, h1]
    obtain ⟨p, hp⟩ := hbij.2 (x, ⟨y, hy⟩)
    have hp1 : (φ p).1 = x := congrArg Prod.fst (hp.trans rfl)
    have hp2 : p.1.2 = y := congrArg Subtype.val (congrArg Prod.snd hp)
    obtain ⟨k, hk⟩ := p.2
    refine ⟨k, ?_, ?_⟩
    · have := congrArg Prod.fst hk
      exact this.trans hp1
    · have := congrArg Prod.snd hk
      exact this.trans hp2



section Count

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

omit [Finite G] in
theorem Dc_le_Qc (hT : IsSylowOf 2 T M) : Dc L T ≤ Qc L M := fun _ hu => ⟨hT.le hu.1, hu.2⟩

theorem card_thetaRange_le (K : Subgroup G) (hK : K ≤ Qc L M) :
    Nat.card ↥(thetaHom H K hK).range ≤ Nat.card (Fq n) := by
  have h1 := Subgroup.card_le_card_group (thetaHom H K hK).range
  rwa [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fq n) ≃ Fq n)] at h1

theorem exists_of_card_thetaRange_eq (K : Subgroup G) (hK : K ≤ Qc L M)
    (h : Nat.card ↥(thetaHom H K hK).range = Nat.card (Fq n)) (t : Fq n) :
    ∃ u ∈ K, thetaG H u = t := by
  have h1 : (thetaHom H K hK).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fq n) ≃ Fq n)]
  have h2 : Multiplicative.ofAdd t ∈ (thetaHom H K hK).range := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨u, hu⟩ := h2
  exact ⟨u, u.2, congrArg Multiplicative.toAdd hu⟩

theorem thetaG_eq_zero_of_card_thetaRange_eq_one (K : Subgroup G) (hK : K ≤ Qc L M)
    (h : Nat.card ↥(thetaHom H K hK).range = 1) {u : G} (hu : u ∈ K) : thetaG H u = 0 := by
  have h1 : (thetaHom H K hK).range = ⊥ := Subgroup.eq_bot_of_card_eq _ h
  have h2 : thetaHom H K hK ⟨u, hu⟩ ∈ (thetaHom H K hK).range := ⟨⟨u, hu⟩, rfl⟩
  rw [h1, Subgroup.mem_bot] at h2
  exact congrArg Multiplicative.toAdd h2

theorem count_comm (hT : IsSylowOf 2 T M) {r q : G} (hr : r ∈ Rl L T) (hq : q ∈ Dc L T)
    {s : Fq n} (hφ : H.D.φ ⟨r, hr.2⟩ = uMat s) (hs0 : s ≠ 0) {K : Subgroup G}
    (hKD : K ≤ Dc L T) (hKc : ∀ u ∈ K, (r * q) * u = u * (r * q)) :
    Nat.card K ≤ Nat.card ↥(K ⊓ Ec L T) *
      (Nat.card (Fq n) * Nat.card ↥(thetaHom H K (hKD.trans (Dc_le_Qc hT))).range) ∧
    (Nat.card K = Nat.card ↥(K ⊓ Ec L T) *
      (Nat.card (Fq n) * Nat.card ↥(thetaHom H K (hKD.trans (Dc_le_Qc hT))).range) →
      ∀ (a t : Fq n), (∃ u ∈ K, thetaG H u = t) → ∃ u ∈ K, vcoG H u 0 = a ∧ thetaG H u = t) := by
  set hKQ : K ≤ Qc L M := hKD.trans (Dc_le_Qc hT) with hKQdef
  set f := w0Hom H K hKQ with hf
  set θ := thetaHom H K hKQ with hθ
  have hker : (f.prod θ).ker = (K ⊓ Ec L T).subgroupOf K := by
    ext ⟨u, hu⟩
    simp only [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : vcoG H u 0 = 0 := by simpa [hf, w0Hom] using h1
      have hth : thetaG H u = 0 := by simpa [hθ, thetaHom] using h2
      exact ⟨hu, mem_Ec_of_coords H hT (hKD hu) hs0
        (rel_of_comm H hT (hKD hu) hr hq hφ (hKc u hu)) h0 hth⟩
    · rintro ⟨-, hE⟩
      obtain ⟨h0, hth⟩ := coordsG_of_mem_Ec H hT hE
      refine ⟨?_, ?_⟩
      · show Multiplicative.ofAdd (vcoG H u 0) = 1
        rw [h0]
        rfl
      · show Multiplicative.ofAdd (thetaG H u) = 1
        rw [hth]
        rfl
  have hkc : Nat.card (f.prod θ).ker = Nat.card ↥(K ⊓ Ec L T) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcl := card_le_ker_mul f θ
  rw [hkc, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fq n) ≃ Fq n)] at hcl
  refine ⟨hcl.1, fun heq a t ⟨u, hu, hut⟩ => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := hcl.2 heq (Multiplicative.ofAdd a) (Multiplicative.ofAdd t)
    ⟨⟨u, hu⟩, by simpa [hθ, thetaHom] using hut⟩
  exact ⟨k, k.2, by simpa [hf, w0Hom] using congrArg Multiplicative.toAdd hk1,
    by simpa [hθ, thetaHom] using congrArg Multiplicative.toAdd hk2⟩

end Count


theorem two_mul_card_le_of_lt {X Y : Subgroup G} (hXY : X < Y) :
    2 * Nat.card X ≤ Nat.card Y := by
  have h1 : X.relIndex Y * Nat.card ↥(X ⊓ Y) = Nat.card Y :=
    Subgroup.relIndex_mul_card (H := X) (K := Y)
  rw [inf_of_le_left hXY.le] at h1
  have h2 : X.relIndex Y ≠ 1 := fun h => hXY.not_ge (Subgroup.relIndex_eq_one.1 h)
  have h3 : X.relIndex Y ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : 2 ≤ X.relIndex Y := by omega
  rw [← h1]
  exact Nat.mul_le_mul_right _ h4

theorem mul_inv_mem_of_card_le_two_mul {X Y : Subgroup G} (hXY : X < Y)
    (hcard : Nat.card Y ≤ 2 * Nat.card X) {a b : G} (ha : a ∈ Y) (haX : a ∉ X) (hb : b ∈ Y)
    (hbX : b ∉ X) : a * b⁻¹ ∈ X := by
  have h1 : X.relIndex Y * Nat.card ↥(X ⊓ Y) = Nat.card Y :=
    Subgroup.relIndex_mul_card (H := X) (K := Y)
  rw [inf_of_le_left hXY.le] at h1
  have h2 : X.relIndex Y ≠ 1 := fun h => hXY.not_ge (Subgroup.relIndex_eq_one.1 h)
  have h3 : X.relIndex Y ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpos : 0 < Nat.card X := Nat.card_pos
  have h4 : X.relIndex Y ≤ 2 := by
    by_contra hcon
    have : 3 * Nat.card X ≤ X.relIndex Y * Nat.card X := Nat.mul_le_mul_right _ (by omega)
    omega
  have h5 : (X.subgroupOf Y).index = 2 := by
    have : X.relIndex Y = 2 := by omega
    exact this
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.1 h5
  have hdisj : ∀ x : ↥Y, x ∉ X.subgroupOf Y → x * c ∈ X.subgroupOf Y := by
    intro x hx
    rcases hc x with ⟨h, -⟩ | ⟨h, h'⟩
    · exact h
    · exact absurd h hx
  have hac := hdisj ⟨a, ha⟩ haX
  have hbc := hdisj ⟨b, hb⟩ hbX
  have := (X.subgroupOf Y).mul_mem hac ((X.subgroupOf Y).inv_mem hbc)
  have e : ((⟨a, ha⟩ : ↥Y) * c) * ((⟨b, hb⟩ : ↥Y) * c)⁻¹ = ⟨a, ha⟩ * ⟨b, hb⟩⁻¹ := by group
  rw [e] at this
  exact this

structure C2Data {L M : Subgroup G} (T : Subgroup G) {n : ℕ} (H : CoordData G L M n)
    (B : Subgroup G) (s : Fq n) : Prop where
  le : B ≤ Rl L T ⊔ Dc L T
  comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  ne_zero : s ≠ 0
  rel : ∀ u ∈ B ⊓ Dc L T, s * vcoG H u 1 + thetaG H u * sqrtF s = 0
  surj : ∀ a t : Fq n, ∃ u ∈ B ⊓ Dc L T, vcoG H u 0 = a ∧ thetaG H u = t
  idx : Nat.card ↥(Ec L T) ≤ 2 * Nat.card ↥(B ⊓ Ec L T)
  centE : B ⊓ Ec L T < Ec L T → ∀ d ∈ Dc L T, (∀ e ∈ Ec L T, d * e = e * d) → thetaG H d = 0

section Normal

variable {L M T : Subgroup G} {n : ℕ} {H : CoordData G L M n} {B : Subgroup G} {s : Fq n}

omit [Finite G] in
theorem Ec_le_Dc' : Ec L T ≤ Dc L T := Ec_le_Dc

theorem C2Data.dec (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hD : C2Data T H B s) :
    ∀ d ∈ Dc L T, ∃ k ∈ B ⊓ Dc L T, ∃ y ∈ blockU L ⊔ Ec L T, d = k * y := by
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  have hVT : blockU L ≤ T := NatBlock.blockU_le_sylow hLM hMN hT
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    blockU_le_normalizer_Ec hLM hMN hT
  intro d hd
  obtain ⟨u, hu, -, hθ⟩ := hD.surj 0 (thetaG H d)
  have huQ : u ∈ Qc L M := ⟨hT.le hu.2.1, hu.2.2⟩
  have hdQ : d ∈ Qc L M := ⟨hT.le hd.1, hd.2⟩
  have hu'D : u⁻¹ * d ∈ Dc L T := (Dc L T).mul_mem ((Dc L T).inv_mem hu.2) hd
  have hu'Q : u⁻¹ * d ∈ Qc L M := ⟨hT.le hu'D.1, hu'D.2⟩
  have hθ0 : thetaG H (u⁻¹ * d) = 0 := by
    rw [thetaG_mul H ((Qc L M).inv_mem huQ) hdQ, thetaG_inv H huQ, hθ]
    exact neg_add_cancel _
  obtain ⟨v, hv, hvc⟩ := (thetaG_eq_zero_iff H hu'Q).1 hθ0
  have hvE : u⁻¹ * d * v⁻¹ ∈ Ec L T :=
    ⟨T.mul_mem hu'D.1 (T.inv_mem (hVT hv)), hvc⟩
  refine ⟨u, hu, u⁻¹ * d, ?_, by group⟩
  have e : u⁻¹ * d = (u⁻¹ * d * v⁻¹) * v := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hvE hv


theorem sup_blockU_Ec_comm (hs : Sec4 G L M T n) {y e : G} (hy : y ∈ blockU L ⊔ Ec L T)
    (he : e ∈ Ec L T) : y * e = e * y := by
  have hle : blockU L ⊔ Ec L T ≤ Subgroup.centralizer ({e} : Set G) := by
    refine sup_le (fun v hv => ?_) (fun e' he' => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 he.2 v (blockU_le L hv)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Ec_comm_of_sec4 hs he' he
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem C2Data.centralizes_EB (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hD : C2Data T H B s) {d e : G} (hd : d ∈ Dc L T) (he : e ∈ B ⊓ Ec L T) :
    d * e = e * d := by
  obtain ⟨k, hk, y, hy, rfl⟩ := hD.dec hs hE1 d hd
  have h1 : k * e = e * k := hD.comm k hk.1 e he.1
  have h2 : y * e = e * y := sup_blockU_Ec_comm hs hy he.2
  calc k * y * e = k * (y * e) := by group
    _ = k * (e * y) := by rw [h2]
    _ = (k * e) * y := by group
    _ = (e * k) * y := by rw [h1]
    _ = e * (k * y) := by group

theorem C2Data.comm_mem_EB (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hD : C2Data T H B s) {k e : G} (hk : k ∈ B ⊓ Dc L T) (he : e ∈ Ec L T) :
    ⁅k, e⁆ ∈ B ⊓ Ec L T := by
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  by_cases heB : e ∈ B
  · have : ⁅k, e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hD.comm k hk.1 e heB)
    rw [this]
    exact one_mem _
  · have hlt : B ⊓ Ec L T < Ec L T := lt_of_le_of_ne inf_le_right fun h =>
      heB (show e ∈ B ⊓ Ec L T by rw [h]; exact he).1
    have hkn : k ∈ Subgroup.normalizer (Ec L T : Set G) :=
      le_normalizer_Ec hMN hs.sylow.le (Dc_le_T hk.2)
    have he' : k * e * k⁻¹ ∈ Ec L T := (Subgroup.mem_normalizer_iff.1 hkn e).1 he
    have he'B : k * e * k⁻¹ ∉ B := fun h => heB (by
      have := B.mul_mem (B.mul_mem (B.inv_mem hk.1) h) hk.1
      simpa [mul_assoc] using this)
    have := mul_inv_mem_of_card_le_two_mul hlt hD.idx he' (fun h => he'B h.1) he
      (fun h => heB h.1)
    have e1 : ⁅k, e⁆ = (k * e * k⁻¹) * e⁻¹ := by simp [commutatorElement_def]
    rw [e1]
    exact this

theorem C2Data.comm_Dc_mem_EB (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hD : C2Data T H B s) : ∀ d ∈ Dc L T, ∀ d' ∈ Dc L T, ⁅d, d'⁆ ∈ B ⊓ Ec L T := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    blockU_le_normalizer_Ec hLM hMN hT
  refine comm_mem_of_abelian_mod (A := B ⊓ Dc L T) (B := blockU L ⊔ Ec L T)
    (N := B ⊓ Ec L T) (S := Dc L T) (inf_le_right.trans Ec_le_Dc)
    (fun d hd => mem_normalizer_of_forall_comm fun e he => hD.centralizes_EB hs hE1 hd he)
    inf_le_right (sup_le (blockU_le_Dc h hLM hMN hT) Ec_le_Dc) (fun k hk => ?_)
    (fun d hd => ?_) (fun a ha a' ha' => ?_) (fun y hy y' hy' => ?_) (fun k hk y hy => ?_)
  · exact mem_normalizer_sup
      (mem_normalizer_of_forall_comm fun v hv =>
        (Subgroup.mem_centralizer_iff.1 hk.2.2 v hv).symm)
      (le_normalizer_Ec hMN hT.le (Dc_le_T hk.2))
  · obtain ⟨k, hk, y, hy, rfl⟩ := hD.dec hs hE1 d hd
    exact Subgroup.mul_mem_sup hk hy
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (hD.comm a ha.1 a' ha'.1)]
    exact one_mem _
  · have hab := sup_comm_of_comm (A := blockU L) (B := Ec L T)
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.1 hb.2 a (blockU_le L ha)))
      h.blockU_comm (fun b hb b' hb' => Ec_comm_of_sec4 hs hb hb') y hy y' hy'
    rw [commutatorElement_eq_one_iff_mul_comm.2 hab]
    exact one_mem _
  · obtain ⟨v, hv, e, he, rfl⟩ := (mem_sup_iff_mul hVn).1 hy
    have h1 : ⁅k, e⁆ ∈ B ⊓ Ec L T := hD.comm_mem_EB hs hE1 hk he
    have h2 : k * v = v * k := (Subgroup.mem_centralizer_iff.1 hk.2.2 v hv).symm
    have h3 : v * ⁅k, e⁆ = ⁅k, e⁆ * v := Subgroup.mem_centralizer_iff.1 h1.2.2 v (blockU_le L hv)
    have e1 : ⁅k, v * e⁆ = ⁅k, v⁆ * (v * ⁅k, e⁆ * v⁻¹) := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅k, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h2
    rw [e1, e2, one_mul, h3, mul_inv_cancel_right]
    exact h1


theorem coords_of_mem_ZR (hs : Sec4 G L M T n) (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T)
    (hAd : H.Adapted T) {z : G} (hz : z ∈ ZR L T) :
    vcoG H z 1 = 0 ∧ thetaG H z = 0 := by
  have hT : IsSylowOf 2 T M := hs.sylow
  rw [ZR_eq_ellTilde_sup H hT hAd hWVE] at hz
  have hℓn : ellTilde H.D ≤ Subgroup.normalizer ((Ec L T ⊓ oTwoIn L : Subgroup G) : Set G) :=
    fun a ha => mem_normalizer_of_forall_comm fun y hy =>
      Subgroup.mem_centralizer_iff.1 hy.1.2 a (blockU_le L ha.1)
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_mul hℓn).1 hz
  have haQ : a ∈ Qc L M := H.blockU_le_Qc ha.1
  have hbQ : b ∈ Qc L M := ⟨hT.le hb.1.1, Subgroup.centralizer_le
    (SetLike.coe_subset_coe.2 (blockU_le L)) hb.1.2⟩
  rw [vcoG_mul H haQ hbQ, thetaG_mul H haQ hbQ]
  obtain ⟨hb1, hb2⟩ := coordsG_of_mem_Ec H hT hb.1
  obtain ⟨ha1, ha2⟩ := coordsG_blockU H ha.1
  rw [ha1, ha2, hb1, hb2]
  exact ⟨by simpa using ha.2, add_zero _⟩

theorem C2Data.ZR_le (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (hAd : H.Adapted T) (hD : C2Data T H B s) :
    ZR L T ≤ B ⊓ Dc L T := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  have hWD : ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w := Dc_centralizes_oTwoIn hs hE1
  intro z hz
  have hzW := ZR_le_oTwoIn hs hE1 hz
  have hzD : z ∈ Dc L T := oTwoIn_le_Dc h hLM hMN hT hzW
  have hzQ : z ∈ Qc L M := ⟨hT.le hzD.1, hzD.2⟩
  obtain ⟨hz1, hzθ⟩ := coords_of_mem_ZR hs hWVE hAd hz
  obtain ⟨u, hu, hu0, huθ⟩ := hD.surj (vcoG H z 0) 0
  have huQ : u ∈ Qc L M := ⟨hT.le hu.2.1, hu.2.2⟩
  have hu1 : vcoG H u 1 = 0 := by
    have := hD.rel u hu
    rw [huθ, zero_mul, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hD.ne_zero
  have hu'D : u⁻¹ * z ∈ Dc L T := (Dc L T).mul_mem ((Dc L T).inv_mem hu.2) hzD
  have hE' : u⁻¹ * z ∈ Ec L T := by
    have hu'Q : u⁻¹ * z ∈ Qc L M := ⟨hT.le hu'D.1, hu'D.2⟩
    have hv : vcoG H (u⁻¹ * z) = 0 := by
      rw [vcoG_mul H ((Qc L M).inv_mem huQ) hzQ, vcoG_inv H huQ]
      funext i
      fin_cases i
      · simp [hu0]
      · simp [hu1, hz1]
    have hθ : thetaG H (u⁻¹ * z) = 0 := by
      rw [thetaG_mul H ((Qc L M).inv_mem huQ) hzQ, thetaG_inv H huQ, huθ, hzθ]
      simp
    exact ⟨hu'D.1, (coordsG_eq_zero_iff H hu'Q).1 ⟨hv, hθ⟩⟩
  have hE'B : u⁻¹ * z ∈ B := by
    by_contra hnot
    have hlt : B ⊓ Ec L T < Ec L T := lt_of_le_of_ne inf_le_right fun h' =>
      hnot (show u⁻¹ * z ∈ B ⊓ Ec L T by rw [h']; exact hE').1
    obtain ⟨d, hd, -, hdθ⟩ := hD.surj 0 1
    have h2 : d * (u⁻¹ * z) = (u⁻¹ * z) * d := by
      have h3 : d * u⁻¹ = u⁻¹ * d := hD.comm d hd.1 u⁻¹ (B.inv_mem hu.1)
      have h4 : z * d = d * z := hWD z hzW d hd.2
      calc d * (u⁻¹ * z) = (d * u⁻¹) * z := by group
        _ = (u⁻¹ * d) * z := by rw [h3]
        _ = u⁻¹ * (d * z) := by group
        _ = u⁻¹ * (z * d) := by rw [h4]
        _ = (u⁻¹ * z) * d := by group
    have hdc : ∀ e ∈ Ec L T, d * e = e * d := by
      intro e he
      by_cases heB : e ∈ B
      · exact hD.centralizes_EB hs hE1 hd.2 ⟨heB, he⟩
      · have hmem := mul_inv_mem_of_card_le_two_mul hlt hD.idx he (fun h => heB h.1) hE'
          (fun h => hnot h.1)
        have h1 : d * (e * (u⁻¹ * z)⁻¹) = (e * (u⁻¹ * z)⁻¹) * d :=
          hD.centralizes_EB hs hE1 hd.2 hmem
        calc d * e = d * ((e * (u⁻¹ * z)⁻¹) * (u⁻¹ * z)) := by group
          _ = (d * (e * (u⁻¹ * z)⁻¹)) * (u⁻¹ * z) := by group
          _ = ((e * (u⁻¹ * z)⁻¹) * d) * (u⁻¹ * z) := by rw [h1]
          _ = (e * (u⁻¹ * z)⁻¹) * (d * (u⁻¹ * z)) := by group
          _ = (e * (u⁻¹ * z)⁻¹) * ((u⁻¹ * z) * d) := by rw [h2]
          _ = e * d := by group
    have := hD.centE hlt d hd.2 hdc
    rw [hdθ] at this
    exact one_ne_zero this
  have hzB : z ∈ B := by
    have := B.mul_mem hu.1 hE'B
    simpa using this
  exact ⟨hzB, hzD⟩

theorem C2Data.normalizer_le (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (hAd : H.Adapted T) (hD : C2Data T H B s) :
    Rl L T ⊔ Dc L T ≤ Subgroup.normalizer (B : Set G) := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  have hWD : ∀ w ∈ oTwoIn L, ∀ d ∈ Dc L T, w * d = d * w := Dc_centralizes_oTwoIn hs hE1
  have hZW := ZR_le_oTwoIn hs hE1
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  have hZB := hD.ZR_le hs hE1 hWVE hAd
  have hc : ∀ x ∈ Rl L T ⊔ Dc L T, ∀ y ∈ Rl L T ⊔ Dc L T,
      ⁅x, y⁆ ∈ ZR L T ⊔ (B ⊓ Ec L T) := by
    refine comm_mem_of_abelian_mod (A := Rl L T) (B := Dc L T) (N := ZR L T ⊔ (B ⊓ Ec L T))
      (S := Rl L T ⊔ Dc L T)
      (sup_le (ZR_le_Rl.trans le_sup_left) (inf_le_right.trans (Ec_le_Dc.trans le_sup_right)))
      (sup_le ?_ ?_) le_sup_left le_sup_right hRn le_rfl
      (fun a ha a' ha' => Subgroup.mem_sup_left (comm_mem_ZR_of_wleVE H hT hAd hWVE ha ha'))
      (fun d hd d' hd' => Subgroup.mem_sup_right (hD.comm_Dc_mem_EB hs hE1 d hd d' hd'))
      (fun a ha d hd => ?_)
    · intro r hr
      exact mem_normalizer_sup
        (mem_normalizer_of_forall_comm fun z hz => (mem_ZR.1 hz).2 r hr)
        (mem_normalizer_of_forall_comm fun e he =>
          Subgroup.mem_centralizer_iff.1 he.2.2 r (Rl_le_L hr))
    · intro d hd
      exact mem_normalizer_sup
        (mem_normalizer_of_forall_comm fun z hz => (hWD z (hZW hz) d hd).symm)
        (mem_normalizer_of_forall_comm fun e he => hD.centralizes_EB hs hE1 hd he)
    · have h2 : ⁅a, d⁆ ∈ ZR L T := by
        rw [← commutatorElement_inv]
        exact (ZR L T).inv_mem (comm_Dc_Rl_mem_ZR H hT hAd hd ha)
      exact Subgroup.mem_sup_left h2
  have hle : ZR L T ⊔ (B ⊓ Ec L T) ≤ B := sup_le (hZB.trans inf_le_left) inf_le_left
  refine le_normalizer_of_comm_mem fun x hx b hb => hle (hc x hx b (hD.le hb))


theorem thetaG_eq_zero_of_mem_sup (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {y : G} (hy : y ∈ blockU L ⊔ Ec L T) : thetaG H y = 0 := by
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    blockU_le_normalizer_Ec hLM hMN hT
  obtain ⟨v, hv, e, he, rfl⟩ := (mem_sup_iff_mul hVn).1 hy
  have hvQ : v ∈ Qc L M := H.blockU_le_Qc hv
  have heQ : e ∈ Qc L M := ⟨hT.le he.1, Subgroup.centralizer_le
    (SetLike.coe_subset_coe.2 (blockU_le L)) he.2⟩
  rw [thetaG_mul H hvQ heQ, (coordsG_blockU H hv).2, (coordsG_of_mem_Ec H hT he).2, add_zero]

theorem thetaG_eq_zero_of_cent (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {A : Subgroup G} (hA : IsMaximalFamily L T A) (hAeq : A = blockU L ⊔ Ec L T) {d : G}
    (hd : d ∈ Dc L T) (hdc : ∀ e ∈ Ec L T, d * e = e * d) : thetaG H d = 0 := by
  have hle : A ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hAeq]
    refine sup_le (fun v hv => ?_) (fun e he => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hd.2 v hv
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hdc e he).symm
  have hdA : d ∈ A := by
    rw [← family_Dc_inf_centralizer_eq hs hE1 hA]
    refine ⟨hd, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
  rw [hAeq] at hdA
  exact thetaG_eq_zero_of_mem_sup hs hE1 hdA

theorem card_thetaRange_eq_one_of (K : Subgroup G) (hK : K ≤ Qc L M)
    (h : ∀ u ∈ K, thetaG H u = 0) : Nat.card ↥(thetaHom H K hK).range = 1 := by
  have : (thetaHom H K hK).range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨u, rfl⟩
    show Multiplicative.ofAdd (thetaG H (u : G)) = 1
    rw [h u u.2]
    rfl
  rw [this]
  exact Subgroup.card_bot


theorem arith_one {q e eb θk k : ℕ} (hq : 0 < q) (he : 0 < e) (hθq : θk ≤ q)
    (hF : k ≤ eb * (q * θk)) (hm : 2 * k = q ^ 2 * e) (h2eb : 2 * eb ≤ e) :
    θk = q ∧ e = 2 * eb ∧ k = eb * (q * θk) := by
  have h1 : (e * q) * q ≤ (e * q) * θk := by
    calc (e * q) * q = q ^ 2 * e := by ring
      _ = 2 * k := hm.symm
      _ ≤ 2 * (eb * (q * θk)) := Nat.mul_le_mul_left _ hF
      _ = (2 * eb) * (q * θk) := by ring
      _ ≤ e * (q * θk) := Nat.mul_le_mul_right _ h2eb
      _ = (e * q) * θk := by ring
  have hθ : θk = q := le_antisymm hθq (Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos he hq))
  subst hθ
  have h3 : θk ^ 2 * e ≤ θk ^ 2 * (2 * eb) := by
    calc θk ^ 2 * e = 2 * k := hm.symm
      _ ≤ 2 * (eb * (θk * θk)) := Nat.mul_le_mul_left _ hF
      _ = θk ^ 2 * (2 * eb) := by ring
  have h4 : e ≤ 2 * eb := Nat.le_of_mul_le_mul_left h3 (by positivity)
  have h5 : e = 2 * eb := le_antisymm h4 (by omega)
  refine ⟨rfl, h5, ?_⟩
  have : 2 * k = 2 * (eb * (θk * θk)) := by rw [hm, h5]; ring
  omega

theorem arith_two {q e eb θk k : ℕ} (hq : 0 < q) (he : 0 < e) (hebe : eb ≤ e) (hθq : θk ≤ q)
    (hF : k ≤ eb * (q * θk)) (hm : k = q ^ 2 * e) :
    θk = q ∧ eb = e ∧ k = eb * (q * θk) := by
  have heb : eb = e := by
    by_contra hne
    have hlt : eb < e := lt_of_le_of_ne hebe hne
    have h1 : eb * (q * θk) ≤ eb * (q * q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hθq)
    have h2 : eb * (q * q) < e * (q * q) := Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos hq hq)
    have h3 : q ^ 2 * e = e * (q * q) := by ring
    omega
  subst heb
  have h1 : (eb * q) * q ≤ (eb * q) * θk := by
    calc (eb * q) * q = q ^ 2 * eb := by ring
      _ = k := hm.symm
      _ ≤ eb * (q * θk) := hF
      _ = (eb * q) * θk := by ring
  have hθ : θk = q := le_antisymm hθq (Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos he hq))
  subst hθ
  refine ⟨rfl, rfl, ?_⟩
  rw [hm]
  ring

theorem normal_of_le_two (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsMaximalFamily L T A)
    {B : Subgroup G} (hBT : B ≤ Rl L T ⊔ Dc L T) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card B = Nat.card A) (hBD : ¬ B ≤ Dc L T)
    (h2 : (B ⊓ Dc L T).relIndex B ≤ 2) : Rl L T ⊔ Dc L T ≤ Subgroup.normalizer (B : Set G) := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  obtain ⟨H, hAd⟩ := exists_utri_coord h hLM hMN hT
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  obtain ⟨x, hxB, hxD⟩ := Set.not_subset.1 hBD
  obtain ⟨r, hr, q', hq', hxe⟩ := (mem_sup_iff_mul hRn).1 (hBT hxB)
  obtain ⟨s, hφ⟩ := hAd r hr.2 hr.1
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hxD
    have hφ1 : H.D.φ ⟨r, hr.2⟩ = 1 := by rw [hφ, uMat_zero]
    have hrW : r ∈ oTwoIn L := (H.D.φ_ker ⟨r, hr.2⟩).1 hφ1
    rw [hxe]
    exact (Dc L T).mul_mem (oTwoIn_le_Dc h hLM hMN hT hrW) hq'
  set K : Subgroup G := B ⊓ Dc L T with hK
  have hKD : K ≤ Dc L T := inf_le_right
  have hKB : K ≤ B := inf_le_left
  have hKQ : K ≤ Qc L M := hKD.trans (Dc_le_Qc hT)
  have hKc : ∀ u ∈ K, (r * q') * u = u * (r * q') := fun u hu => by
    rw [← hxe]
    exact hcomm x hxB u hu.1
  have hrel : ∀ u ∈ K, s * vcoG H u 1 + thetaG H u * sqrtF s = 0 :=
    fun u hu => rel_of_comm H hT (hKD hu) hr hq' hφ (hKc u hu)
  have hidx2 : K.relIndex B = 2 := by
    have h1 : K.relIndex B ≠ 1 := fun h' => hxD (((Subgroup.relIndex_eq_one.1 h') hxB).2)
    have h0 : K.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hBK : Nat.card B = 2 * Nat.card K := by
    have := Subgroup.relIndex_mul_card (H := K) (K := B)
    rw [hidx2, inf_of_le_left hKB] at this
    exact this.symm
  have hKE : K ⊓ Ec L T = B ⊓ Ec L T := by
    ext y
    simp only [Subgroup.mem_inf, hK]
    constructor
    · rintro ⟨⟨hyB, -⟩, hyE⟩
      exact ⟨hyB, hyE⟩
    · rintro ⟨hyB, hyE⟩
      exact ⟨⟨hyB, Ec_le_Dc hyE⟩, hyE⟩
  have hcnt := count_comm H hT hr hq' hφ hs0 hKD hKc
  rw [hKE] at hcnt
  have hn0 : n ≠ 0 := by have := h.two_le; omega
  have hFcard : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n hn0
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hqpos : 0 < 2 ^ n := by omega
  have hepos : 0 < Nat.card ↥(Ec L T) := Nat.card_pos
  have hθk : Nat.card ↥(thetaHom H K hKQ).range ≤ 2 ^ n :=
    (card_thetaRange_le H K hKQ).trans hFcard.le
  have hEBle : Nat.card ↥(B ⊓ Ec L T) ≤ Nat.card ↥(Ec L T) := Subgroup.card_le_of_le inf_le_right
  have hAlow : (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) ≤ Nat.card A := family_card_le hs hE1 hA.1
  have hVEdvd : (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) ∣ Nat.card A := by
    rw [← card_sup_blockU_Ec hs hE1]
    exact Subgroup.card_dvd_of_le (sup_le (blockU_le_family hA.1) (Ec_le_family hA.1))
  have hF1 : Nat.card K ≤ Nat.card ↥(B ⊓ Ec L T) *
      (2 ^ n * Nat.card ↥(thetaHom H K hKQ).range) := by
    have := hcnt.1
    rwa [hFcard] at this
  have hkm : 2 * Nat.card K = Nat.card A := by rw [← hcard, hBK]
  have hmupper : Nat.card A ≤ 2 * ((2 ^ n) ^ 2 * Nat.card ↥(Ec L T)) := by
    calc Nat.card A = 2 * Nat.card K := hkm.symm
      _ ≤ 2 * (Nat.card ↥(B ⊓ Ec L T) * (2 ^ n * Nat.card ↥(thetaHom H K hKQ).range)) :=
        Nat.mul_le_mul_left _ hF1
      _ ≤ 2 * (Nat.card ↥(Ec L T) * (2 ^ n * 2 ^ n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hEBle (Nat.mul_le_mul_left _ hθk))
      _ = 2 * ((2 ^ n) ^ 2 * Nat.card ↥(Ec L T)) := by ring
  obtain ⟨c, hc⟩ := hVEdvd
  have hPpos : 0 < (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by positivity
  have hc1 : 1 ≤ c := by
    by_contra hc0
    have : c = 0 := by omega
    rw [this, mul_zero] at hc
    have := Nat.card_pos (α := ↥A)
    omega
  have hc2 : c ≤ 2 := by
    by_contra hc3
    have : (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) * 3 ≤ Nat.card A := by
      rw [hc]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  have key : Nat.card ↥(thetaHom H K hKQ).range = 2 ^ n ∧
      Nat.card K = Nat.card ↥(B ⊓ Ec L T) * (2 ^ n * Nat.card ↥(thetaHom H K hKQ).range) ∧
      Nat.card ↥(Ec L T) ≤ 2 * Nat.card ↥(B ⊓ Ec L T) ∧
      (B ⊓ Ec L T < Ec L T → A = blockU L ⊔ Ec L T) := by
    obtain rfl | rfl : c = 1 ∨ c = 2 := by omega
    ·
      have hAeq : A = blockU L ⊔ Ec L T := family_eq_sup_of_card_eq hs hE1 hA.1 (by
        rw [hc, mul_one])
      have hlt : Nat.card ↥(B ⊓ Ec L T) < Nat.card ↥(Ec L T) := by
        by_contra hnlt
        have hebeq : Nat.card ↥(B ⊓ Ec L T) = Nat.card ↥(Ec L T) := le_antisymm hEBle (by omega)
        have hEB : B ⊓ Ec L T = Ec L T :=
          Subgroup.eq_of_le_of_card_ge inf_le_right hebeq.ge
        have hth : ∀ u ∈ K, thetaG H u = 0 := fun u hu =>
          thetaG_eq_zero_of_cent hs hE1 hA hAeq (hKD hu) (fun e he =>
            hcomm u hu.1 e (show e ∈ B ⊓ Ec L T by rw [hEB]; exact he).1)
        have hθ1 := card_thetaRange_eq_one_of K hKQ hth
        rw [hθ1] at hF1
        have h3 : (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) ≤ 2 * (Nat.card ↥(Ec L T) * 2 ^ n) := by
          calc (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) = Nat.card A := by rw [hc, mul_one]
            _ = 2 * Nat.card K := hkm.symm
            _ ≤ 2 * (Nat.card ↥(B ⊓ Ec L T) * (2 ^ n * 1)) := Nat.mul_le_mul_left _ hF1
            _ ≤ 2 * (Nat.card ↥(Ec L T) * (2 ^ n * 1)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hEBle)
            _ = 2 * (Nat.card ↥(Ec L T) * 2 ^ n) := by ring
        have h4 : (2 ^ n) * (2 ^ n * Nat.card ↥(Ec L T)) ≤ 2 * (2 ^ n * Nat.card ↥(Ec L T)) := by
          calc (2 ^ n) * (2 ^ n * Nat.card ↥(Ec L T)) = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by
                ring
            _ ≤ 2 * (Nat.card ↥(Ec L T) * 2 ^ n) := h3
            _ = 2 * (2 ^ n * Nat.card ↥(Ec L T)) := by ring
        have h5 := Nat.le_of_mul_le_mul_right h4 (Nat.mul_pos hqpos hepos)
        omega
      have hltsub : B ⊓ Ec L T < Ec L T := lt_of_le_of_ne inf_le_right fun h' => by
        rw [h'] at hlt
        exact lt_irrefl _ hlt
      have h2eb := two_mul_card_le_of_lt hltsub
      have := arith_one hqpos hepos hθk hF1 (by rw [hkm, hc, mul_one]) h2eb
      obtain ⟨hθ, he2, hk⟩ := this
      exact ⟨hθ, hk, he2.le, fun _ => hAeq⟩
    · have hkP : Nat.card K = (2 ^ n) ^ 2 * Nat.card ↥(Ec L T) := by
        have : 2 * Nat.card K = 2 * ((2 ^ n) ^ 2 * Nat.card ↥(Ec L T)) := by
          rw [hkm, hc]
          ring
        omega
      obtain ⟨hθ, heb, hk⟩ := arith_two hqpos hepos hEBle hθk hF1 hkP
      refine ⟨hθ, hk, by omega, fun hlt => ?_⟩
      exfalso
      have hEB : B ⊓ Ec L T = Ec L T := Subgroup.eq_of_le_of_card_ge inf_le_right heb.ge
      rw [hEB] at hlt
      exact lt_irrefl _ hlt
  obtain ⟨hθeq, hkeq, hidx, hcentA⟩ := key
  have hD : C2Data T H B s :=
    { le := hBT
      comm := hcomm
      ne_zero := hs0
      rel := hrel
      surj := fun a t => by
        have hall : ∀ t : Fq n, ∃ u ∈ K, thetaG H u = t :=
          exists_of_card_thetaRange_eq H K hKQ (hθeq.trans hFcard.symm)
        exact hcnt.2 (by rw [hFcard]; exact hkeq) a t (hall t)
      idx := hidx
      centE := fun hlt d hd hdc => thetaG_eq_zero_of_cent hs hE1 hA (hcentA hlt) hd hdc }
  exact hD.normalizer_le hs hE1 hWVE hAd


theorem normal_of_not_le_Dc (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G} (hA : IsMaximalFamily L T A)
    {B : Subgroup G} (hBT : B ≤ Rl L T ⊔ Dc L T) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card B = Nat.card A) (hBD : ¬ B ≤ Dc L T) :
    Rl L T ⊔ Dc L T ≤ Subgroup.normalizer (B : Set G) := by
  by_cases h3 : 3 ≤ (B ⊓ Dc L T).relIndex B
  · exact normal_of_three_le hs hE1 hWVE hA.1 hBT hcomm hcard h3
  · exact normal_of_le_two hs hE1 hWVE hA hBT hcomm hcard hBD (by omega)

end Normal

theorem sylow_type (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hA78 : Aschbacher78OneGen) (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G}
    (hA : IsMaximalFamily L T A) (hCNT : LemmaCNT L T A) {g : G}
    (hg : A.map (MulAut.conj g).toMonoidHom ≤ M) :
    ∃ m ∈ M, A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj m).toMonoidHom := by
  have hAT : A ≤ T := hA.1.le_Dc.trans Dc_le_T
  have hP : IsPGroup 2 ↥(A.map (MulAut.conj g).toMonoidHom) :=
    (hs.sylow.isPGroup.to_le hAT).map _
  obtain ⟨k, hkM, hkT⟩ := exists_conj_le_of_isPGroup hs.sylow hP hg
  set g' : G := k * g with hg'
  set B : Subgroup G := A.map (MulAut.conj g').toMonoidHom with hB
  have hBeq : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom = B := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [hg', MulAut.conj_apply, mul_assoc]
  have hBT : B ≤ T := hBeq ▸ hkT
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g' * a * g'⁻¹ * (g' * b * g'⁻¹) = g' * (a * b) * g'⁻¹ := by group
      _ = g' * (b * a) * g'⁻¹ := by rw [hA.1.comm a ha b hb]
      _ = g' * b * g'⁻¹ * (g' * a * g'⁻¹) := by group
  have hcard : Nat.card B = Nat.card A := card_map_conj A g'
  have hg'M : g' ∈ M := by
    by_cases hT1 : B ≤ Rl L T ⊔ Dc L T
    · by_cases hBD : B ≤ Dc L T
      · exact mem_of_map_conj_le_Dc hs hE1 hA hBD
      · exact WeakCl.mem_of_le_normalizer_map_conj hs hE1 hA78 (family_normalizer_le hs hE1 hA.1)
          (normal_of_not_le_Dc hs hE1 hWVE hA hT1 hcomm hcard hBD)
    · exact absurd (hCNT B hBT hcomm hT1).1 (by rw [hcard]; exact lt_irrefl _)
  have hgM : g ∈ M := by
    have := M.mul_mem (M.inv_mem hkM) hg'M
    simpa [hg'] using this
  exact ⟨g, hgM, rfl⟩

end Syl

end CFSG.CGT.PushingUpLit.T2KSW
