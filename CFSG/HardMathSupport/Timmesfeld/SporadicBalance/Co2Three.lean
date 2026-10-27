
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import Certificates.Certificate13636

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Schreier.Co3.Native CFSG.RankThree.PartTwo.Sec4.Item434SporE81

section Facts

theorem Qg_le : Qg ≤ co2P := Certificates.certificate13636.1

theorem card_Qg : Nat.card Qg = 729 := Certificates.certificate13636.2.1

theorem qPts_size : (qCert2 ()).pts.size = 729 := Certificates.certificate13636.2.2.1

theorem qPts_valid : ∀ k < 729, validA 2300 (qCert2 ()).pts[k]! = true :=
  Certificates.certificate13636.2.2.2.1

theorem mem_Qg_iff_qPts : ∀ x, x ∈ Qg ↔ ∃ k < 729, permOfArr 2300 (qCert2 ()).pts[k]! = x :=
  Certificates.certificate13636.2.2.2.2.1

theorem dGenP_facts :
    ∀ i < 4, validA 2300 (dGens ())[i]! = true ∧ dGenP i ∈ co2P ∧ dGenP i ^ 3 = 1 :=
  Certificates.certificate13636.2.2.2.2.2.1

theorem dGenP_comm : ∀ i < 4, ∀ j < 4, Commute (dGenP i) (dGenP j) :=
  Certificates.certificate13636.2.2.2.2.2.2.1

theorem dEltP_inj : ∀ k < 81, ∀ k' < 81, dEltP k = dEltP k' → k = k' :=
  Certificates.certificate13636.2.2.2.2.2.2.2.1

theorem card_centralizer_hyp_le : ∀ B : Subgroup (Equiv.Perm (Fin 2300)),
    (∀ b ∈ B, ∃ k < 81, b = dEltP k) → Nat.card B * 3 = 81 →
      Nat.card ↥(Subgroup.centralizer (B : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) ≤ 162 :=
  Certificates.certificate13636.2.2.2.2.2.2.2.2.1

theorem eq_dEltP_of_commute :
    ∀ c ∈ co2P, (∀ k < 81, Commute c (dEltP k)) → ∃ k < 81, c = dEltP k :=
  Certificates.certificate13636.2.2.2.2.2.2.2.2.2.1

theorem exists_conj_eq_dEltP :
    ∀ x ∈ co2P, orderOf x = 3 → ∃ h ∈ co2P, ∃ k < 81, h * x * h⁻¹ = dEltP k :=
  Certificates.certificate13636.2.2.2.2.2.2.2.2.2.2

end Facts

section Chain

end Chain

section D

theorem rep_dGen {i : ℕ} (hi : i < 4) : Rep 2300 (dGens ())[i]! (dPerm ⟨i, hi⟩) :=
  rep_of_validA (dGenP_facts i hi).1

theorem dPerm_pow (i : Fin 4) : dPerm i ^ 3 = 1 := (dGenP_facts i i.2).2.2

theorem dPerm_comm (i j : Fin 4) : Commute (dPerm i) (dPerm j) := dGenP_comm i i.2 j j.2

theorem dPerm_mem (i : Fin 4) : dPerm i ∈ co2P := (dGenP_facts i i.2).2.1

@[expose] noncomputable def φ : Multiplicative (Fin 4 → ZMod 3) →* Equiv.Perm (Fin 2300) :=
  Co3T.vecProdHom dPerm dPerm_comm dPerm_pow

theorem φ_apply (a : Fin 4 → ZMod 3) :
    φ (Multiplicative.ofAdd a) = Co3T.vecProd dPerm a := rfl

theorem rep_dElts {k : ℕ} (hk : k < 81) :
    Rep 2300 (dElts ())[k]! (φ (Multiplicative.ofAdd (vec k))) := by
  rw [φ_apply, vecProd_eq]
  have he : (dElts ())[k]! = dProd (dGens ()) k := by
    rw [dElts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rw [he, dProd]
  simp only [vec_val]
  exact rep_compA (rep_powArr (rep_dGen (by norm_num)) _) (rep_compA (rep_powArr
    (rep_dGen (by norm_num)) _) (rep_compA (rep_powArr (rep_dGen (by norm_num)) _)
      (rep_powArr (rep_dGen (by norm_num)) _)))

theorem φ_vec_eq {k : ℕ} (hk : k < 81) : φ (Multiplicative.ofAdd (vec k)) = dEltP k :=
  (CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_dElts hk)).symm

theorem φ_eq_dEltP (a : Multiplicative (Fin 4 → ZMod 3)) :
    φ a = dEltP (idx (Multiplicative.toAdd a)) := by
  rw [← φ_vec_eq (idx_lt _), vec_idx, ofAdd_toAdd]

theorem φ_injective : Function.Injective φ := by
  intro a b hab
  rw [φ_eq_dEltP, φ_eq_dEltP] at hab
  have := congrArg vec (dEltP_inj _ (idx_lt _) _ (idx_lt _) hab)
  rw [vec_idx, vec_idx] at this
  exact Multiplicative.toAdd.injective this

@[expose] noncomputable def Dg : Subgroup (Equiv.Perm (Fin 2300)) := φ.range

theorem Dg_comm : ∀ x ∈ Dg, ∀ y ∈ Dg, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem Dg_pow_three : ∀ x ∈ Dg, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 from rfl,
      zero_mul]
  rw [this, map_one]

theorem card_Dg : Nat.card Dg = 81 := by
  rw [Dg, MonoidHom.range_eq_map, Subgroup.card_map_of_injective φ_injective, Subgroup.card_top,
    Co3T.card_vec]
  norm_num

theorem isPGroup_Dg : IsPGroup 3 ↥Dg := IsPGroup.of_card (n := 4) (by rw [card_Dg]; norm_num)

theorem Dg_le : Dg ≤ co2P := by
  rintro _ ⟨a, rfl⟩
  change Co3T.vecProd dPerm a.toAdd ∈ co2P
  rw [vecProd_eq]
  have h := dPerm_mem
  exact co2P.mul_mem (co2P.pow_mem (h 0) _) (co2P.mul_mem (co2P.pow_mem (h 1) _)
    (co2P.mul_mem (co2P.pow_mem (h 2) _) (co2P.pow_mem (h 3) _)))

theorem mem_Dg_of_inD {a : Array ℕ} {A : Equiv.Perm (Fin 2300)} (ha : Rep 2300 a A)
    (h : inD (dElts ()) a = true) : A ∈ Dg := by
  unfold inD at h
  obtain ⟨i, hi, hai⟩ := anyLt_true h
  rw [(eqA_iff ha (rep_dElts hi)).1 hai]
  exact ⟨_, rfl⟩

theorem dEltP_mem_Dg {k : ℕ} (hk : k < 81) : dEltP k ∈ Dg := by
  rw [← φ_vec_eq hk]
  exact ⟨_, rfl⟩

end D

section HypCard

theorem card_centralizer_inf_le {B : Subgroup (Equiv.Perm (Fin 2300))} (hBD : B ≤ Dg)
    (hB : Nat.card B * 3 = 81) :
    Nat.card ↥(Subgroup.centralizer (B : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) ≤ 162 := by
  refine card_centralizer_hyp_le B (fun b hb => ?_) hB
  obtain ⟨a, rfl⟩ := hBD hb
  exact ⟨_, idx_lt _, φ_eq_dEltP a⟩

theorem centralizer_Dg_inf_eq :
    Subgroup.centralizer (Dg : Set (Equiv.Perm (Fin 2300))) ⊓ co2P = Dg := by
  refine le_antisymm (fun c hc => ?_) fun x hx =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun b hb => Dg_comm b hb x hx, Dg_le hx⟩
  obtain ⟨hcC, hcP⟩ := Subgroup.mem_inf.1 hc
  have hcomm : ∀ k < 81, Commute c (dEltP k) := fun k hk =>
    ((Subgroup.mem_centralizer_iff.1 hcC) _ (dEltP_mem_Dg hk)).symm
  obtain ⟨k, hk, rfl⟩ := eq_dEltP_of_commute c hcP hcomm
  exact dEltP_mem_Dg hk

end HypCard

section DCore

@[expose] noncomputable def Tg : Subgroup ↥co2P := Dg.subgroupOf co2P

theorem card_Tg : Nat.card Tg = 81 := by
  rw [Tg, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Dg_le).toEquiv, card_Dg]

theorem Tg_elemAbelian : IsElemAbelian 3 Tg := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact Dg_comm _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact Dg_pow_three _ (Subgroup.mem_subgroupOf.1 hx)

theorem isPGroup_centralizer_Tg : IsPGroup 3 ↥(Subgroup.centralizer (Tg : Set ↥co2P)) := by
  refine isPGroup_of_map_le (X := Dg) isPGroup_Dg fun c hc => ?_
  rw [← centralizer_Dg_inf_eq]
  refine Subgroup.mem_inf.2 ⟨?_, c.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc ⟨d, Dg_le hd⟩
    (Subgroup.mem_subgroupOf.2 hd))

theorem gLAPPrimeCoreOf_centralizer_of_index {B : Subgroup ↥co2P} (hBT : B ≤ Tg)
    (hidx : B.relIndex Tg = 3) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer (B : Set ↥co2P)) = ⊥ := by
  set B' := B.map co2P.subtype with hB'
  have hB'D : B' ≤ Dg := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hBT hx)
  have hcard : Nat.card B' * 3 = 81 := by
    rw [Subgroup.card_map_of_injective co2P.subtype_injective]
    have h := Subgroup.relIndex_mul_card B Tg
    rw [inf_eq_left.2 hBT, hidx, card_Tg] at h
    omega
  have hle := card_centralizer_inf_le hB'D hcard
  have hTB : Tg ≤ Subgroup.centralizer (B : Set ↥co2P) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subtype.ext (Dg_comm _ (Subgroup.mem_subgroupOf.1 (hBT hb)) _
      (Subgroup.mem_subgroupOf.1 ht))
  refine Co2T.gLAPPrimeCoreOf_eq_bot_of_card_lt_three_mul hTB
    (IsPGroup.of_card (n := 4) (by rw [card_Tg]; norm_num)) isPGroup_centralizer_Tg ?_
  rw [card_Tg]
  have hmap : Nat.card ↥(Subgroup.centralizer (B : Set ↥co2P)) ≤
      Nat.card ↥(Subgroup.centralizer (B' : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) := by
    rw [← Subgroup.card_map_of_injective co2P.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, c.2⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc b hb)
  omega

theorem gLAPPrimeCoreOf_eq_bot_of_mem_Dg {s : ↥co2P} (hs : orderOf s = 3)
    (hsD : (s : Equiv.Perm (Fin 2300)) ∈ Dg) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥co2P)) = ⊥ :=
  gLAPPrimeCoreOf_eq_bot_of_elemAbelian Nat.prime_three Tg_elemAbelian
    (Subgroup.mem_subgroupOf.2 hsD) hs (fun _ hBT hidx =>
      gLAPPrimeCoreOf_centralizer_of_index hBT hidx)
    (gLAPPrimeCoreOf_eq_bot_of_isPGroup Nat.prime_three isPGroup_centralizer_Tg)

end DCore

section Fusion

theorem exists_conj_mem_Dg {x : Equiv.Perm (Fin 2300)} (hx : x ∈ co2P) (hxo : orderOf x = 3) :
    ∃ h ∈ co2P, h * x * h⁻¹ ∈ Dg := by
  obtain ⟨h, hh, k, hk, e⟩ := exists_conj_eq_dEltP x hx hxo
  exact ⟨h, hh, e ▸ dEltP_mem_Dg hk⟩

end Fusion

theorem oPrimeCoreTrivialAt_co2P : OPrimeCoreTrivialAt 3 ↥co2P := by
  intro s hs
  have hso : orderOf (s : Equiv.Perm (Fin 2300)) = 3 := by rw [Subgroup.orderOf_coe]; exact hs
  obtain ⟨h, hhP, hD⟩ := exists_conj_mem_Dg s.2 hso
  set h' : ↥co2P := ⟨h, hhP⟩ with hh'
  have hval : ((h' * s * h'⁻¹ : ↥co2P) : Equiv.Perm (Fin 2300)) = h * (s : Equiv.Perm (Fin 2300)) *
      h⁻¹ := rfl
  have ho : orderOf (h' * s * h'⁻¹) = 3 := by
    have := (MulAut.conj h' : ↥co2P ≃* ↥co2P).orderOf_eq s
    simpa [MulAut.conj_apply, hs] using this
  exact (gLAPPrimeCoreOf_centralizer_conj h' s).1
    (gLAPPrimeCoreOf_eq_bot_of_mem_Dg ho (hval ▸ hD))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.Co2Cert

theorem sporadicOPrimeHolds_Co2_three :
    SporadicOPrimeHolds .Co2 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Co2 := e
  exact OPrimeCoreTrivialAt.of_mulEquiv (e0.trans co2PermEquiv) Co2T.oPrimeCoreTrivialAt_co2P

theorem sporadicOnePairHolds_Co2_three :
    SporadicOnePairHolds .Co2 3 :=
  ⟨sporadicOPrimeHolds_Co2_three, sporadicOuterHolds_Co2 3⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
