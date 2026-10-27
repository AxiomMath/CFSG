module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3Three
public import CFSG.RankThree.Native.Co3FiveCentralizers
public import Certificates.Certificate36903
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Co3.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump

section Fuse


private theorem fuseCheck_eq : fuseCheck () = true := Certificates.certificate36903.1

private theorem fuse_parts :
    (∀ i < 2, validA 276 (fuseGens ())[i]! = true ∧ inP (levels ()) (fuseGens ())[i]! = true) ∧
    (∀ k < 243, k = 0 ∨ (tPar[k]! = k ∧ (k = kA ∨ k = kB)) ∨
      (tPar[k]! < 243 ∧ tPar[k]! ≠ 0 ∧ tGen[k]! < 2 ∧ tDep[tPar[k]!]! < tDep[k]! ∧
        eqA 276 (dElts ())[k]! (conjA 276 (fuseGens ())[tGen[k]!]! (dElts ())[tPar[k]!]!) =
          true)) := by
  have h := fuseCheck_eq
  simp only [fuseCheck, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · have := allLt_spec h1 hi
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allLt_spec h2 hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with (h0 | h1) | ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨a, b, c, d, e⟩)

private noncomputable def xA : Equiv.Perm (Fin 276) := φ (Multiplicative.ofAdd (vec kA))

private noncomputable def xB : Equiv.Perm (Fin 276) := φ (Multiplicative.ofAdd (vec kB))

private theorem rep_xA : Rep 276 (dElts ())[kA]! xA := rep_dElts (by decide)

private theorem rep_xB : Rep 276 (dElts ())[kB]! xB := rep_dElts (by decide)

private theorem fuse_sound : ∀ k < 243, k ≠ 0 → ∃ h ∈ co3P,
    h * xA * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) ∨
      h * xB * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) := by
  obtain ⟨hgens, hforest⟩ := fuse_parts
  suffices H : ∀ d, ∀ k < 243, tDep[k]! = d → k ≠ 0 → ∃ h ∈ co3P,
      h * xA * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) ∨
        h * xB * h⁻¹ = φ (Multiplicative.ofAdd (vec k)) from
    fun k hk hk0 => H _ k hk rfl hk0
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hk hd hk0
    rcases hforest k hk with h0 | ⟨_, hkAB⟩ | ⟨hp, hp0, hg, hdep, he⟩
    · exact absurd h0 hk0
    · rcases hkAB with rfl | rfl
      · exact ⟨1, co3P.one_mem, Or.inl (by simp [xA])⟩
      · exact ⟨1, co3P.one_mem, Or.inr (by simp [xB])⟩
    · obtain ⟨h, hh, hcase⟩ := ih (tDep[tPar[k]!]!) (hd ▸ hdep) (tPar[k]!) hp rfl hp0
      obtain ⟨hv, hP⟩ := hgens (tGen[k]!) hg
      have hn : permOfArr 276 (fuseGens ())[tGen[k]!]! ∈ co3P :=
        mem_co3P_of_inP (rep_of_validA hv) hP
      have hkD := rep_dElts hk
      have hpD := rep_dElts hp
      have hconj := (eqA_iff hkD (rep_conjA hv hpD)).1 he
      refine ⟨permOfArr 276 (fuseGens ())[tGen[k]!]! * h, co3P.mul_mem hn hh, ?_⟩
      rcases hcase with hcase | hcase
      · left
        rw [hconj, ← hcase]
        group
      · right
        rw [hconj, ← hcase]
        group

end Fuse

private theorem permsA_two {n : ℕ} {gs : Array (Array ℕ)} (h : gs.size = 2) :
    permsA n gs = {permOfArr n gs[0]!, permOfArr n gs[1]!} := by
  ext x
  simp only [permsA, h, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

section Pair


private theorem pairCheck_sound {c : Array ℕ} {C : Equiv.Perm (Fin 276)} (hc : Rep 276 c C)
    {gs : Array (Array ℕ)} {fuel : ℕ} (h : pairCheck c gs fuel = true) :
    ∃ g₁ g₂ : Equiv.Perm (Fin 276), g₁ ∈ co3P ∧ g₂ ∈ co3P ∧ g₁ * C = C * g₁ ∧
      g₂ * C = C * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276)))) := by
  simp only [pairCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hsz, hall⟩, henum, hbig⟩ := h
  have hk : ∀ k, k < 2 → validA 276 gs[k]! = true ∧ inP (levels ()) gs[k]! = true ∧
      commA 276 gs[k]! c = true ∧ eqA 276 (powArr 276 gs[k]! 5) (idA 276) = true ∧
      eqA 276 gs[k]! (idA 276) = false := by
    intro k hk
    have := allLt_spec hall hk
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := this
    exact ⟨a, b, c, d, e⟩
  have hspec := enumOK_spec keys_lt henum
  have hcard : Nat.card (Subgroup.closure (permsA 276 gs)) = (enumBfs 276 gs keys fuel).pts.size :=
    hspec.2.1
  have hone : ∀ k, k < 2 → orderOf (permOfArr 276 gs[k]!) = 5 ∧ permOfArr 276 gs[k]! ∈ co3P ∧
      permOfArr 276 gs[k]! * C = C * permOfArr 276 gs[k]! := by
    intro k hkk
    obtain ⟨hv, hP, hcm, hpow, hne⟩ := hk k hkk
    have hrep := rep_of_validA hv
    refine ⟨?_, mem_co3P_of_inP hrep hP, (commA_iff hrep hc).1 hcm⟩
    have h5 : permOfArr 276 gs[k]! ^ 5 = 1 := (eqA_iff (rep_powArr hrep 5) rep_idA).1 hpow
    have h1 : permOfArr 276 gs[k]! ≠ 1 := fun h1 => by
      rw [(eqA_iff hrep rep_idA).2 h1] at hne
      exact absurd hne (by decide)
    exact orderOf_eq_prime h5 h1
  obtain ⟨o0, m0, c0⟩ := hone 0 (by norm_num)
  obtain ⟨o1, m1, c1⟩ := hone 1 (by norm_num)
  refine ⟨_, _, m0, m1, c0, c1, o0, o1, ?_⟩
  have hs : Subgroup.closure (permsA 276 gs) = Subgroup.closure ({permOfArr 276 gs[0]!,
      permOfArr 276 gs[1]!} : Set (Equiv.Perm (Fin 276))) := by rw [permsA_two hsz]
  rw [← hs, hcard]
  exact hbig

private theorem pair_xA :
    ∃ g₁ g₂ : Equiv.Perm (Fin 276), g₁ ∈ co3P ∧ g₂ ∈ co3P ∧ g₁ * xA = xA * g₁ ∧
      g₂ * xA = xA * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276)))) :=
  pairCheck_sound rep_xA Certificates.certificate36903.2.1

private theorem pair_xB :
    ∃ g₁ g₂ : Equiv.Perm (Fin 276), g₁ ∈ co3P ∧ g₂ ∈ co3P ∧ g₁ * xB = xB * g₁ ∧
      g₂ * xB = xB * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276)))) :=
  pairCheck_sound rep_xB Certificates.certificate36903.2.2.1

end Pair

section Five

open scoped Pointwise


private theorem exists_conj_le_sylow_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P K : Subgroup G) (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hK : IsPGroup p K) : ∃ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ P := by
  obtain ⟨Q, hKQ⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard P hP)
  have hP' : (P : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    have := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
    simpa [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] using this.symm
  refine ⟨g, fun k hk => ?_⟩
  rw [hP']
  exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj g) _).2
    ⟨k, hKQ hk, by simp [MulAut.smul_def]⟩

private theorem no_order25_centralized {s : Equiv.Perm (Fin 276)} (hs : s ∈ co3P)
    (hs3 : orderOf s = 3) {E : Subgroup (Equiv.Perm (Fin 276))} (hEP : E ≤ co3P)
    (hE : Nat.card E = 25) (hcomm : ∀ e ∈ E, e * s = s * e) : False := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQcard : Nat.card (co3FiveQ.subgroupOf co3P) =
      5 ^ (Nat.card co3P).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3FiveQ_le_P).toEquiv, card_co3FiveQ,
      factorization_card_co3P_five]
    norm_num
  have hEG : IsPGroup 5 (E.subgroupOf co3P) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_le_sylow_of_card (co3FiveQ.subgroupOf co3P) (E.subgroupOf co3P)
    hQcard hEG
  set gP : Equiv.Perm (Fin 276) := (g : Equiv.Perm (Fin 276)) with hgP
  have hgmem : gP ∈ co3P := g.2
  set E' : Subgroup (Equiv.Perm (Fin 276)) := E.map (MulAut.conj gP).toMonoidHom with hE'
  have hE'Q : E' ≤ co3FiveQ := by
    rintro _ ⟨e, he, rfl⟩
    have := hg ⟨e, hEP he⟩ (Subgroup.mem_subgroupOf.2 he)
    exact Subgroup.mem_subgroupOf.1 this
  have hE'card : Nat.card E' = 25 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj gP).injective, hE]
  set s' : Equiv.Perm (Fin 276) := gP * s * gP⁻¹ with hs'
  have hs'P : s' ∈ co3P := co3P.mul_mem (co3P.mul_mem hgmem hs) (co3P.inv_mem hgmem)
  have hs'3 : orderOf s' = 3 := by
    have := (MulAut.conj gP : Equiv.Perm (Fin 276) ≃* Equiv.Perm (Fin 276)).orderOf_eq s
    simpa [MulAut.conj_apply, hs3] using this
  have hcomm' : ∀ e ∈ E', e * s' = s' * e := by
    rintro _ ⟨e, he, rfl⟩
    have := hcomm e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs']
    calc gP * e * gP⁻¹ * (gP * s * gP⁻¹) = gP * (e * s) * gP⁻¹ := by group
      _ = gP * (s * e) * gP⁻¹ := by rw [this]
      _ = gP * s * gP⁻¹ * (gP * e * gP⁻¹) := by group
  have hx25 : co3FiveLine 25 ∈ E' := by
    have hAcard : Nat.card co3FiveQ = 125 := card_co3FiveQ
    have hApg : IsPGroup 5 co3FiveQ := IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)
    haveI : Group.IsNilpotent co3FiveQ := hApg.isNilpotent
    set B : Subgroup co3FiveQ := E'.subgroupOf co3FiveQ with hB
    have hBcard : Nat.card B = 25 := by
      rw [hB, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'Q).toEquiv, hE'card]
    have hBindex : B.index = 5 := by
      have := B.card_mul_index
      rw [hBcard, hAcard] at this
      omega
    have hBnormal : B.Normal := by
      apply Subgroup.normal_of_index_eq_minFac_card
      rw [hBindex, hAcard]
      norm_num
    have hBne : B ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hBcard
      omega
    obtain ⟨⟨z, hzmem⟩, hz1⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one).1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hBne)
    obtain ⟨hzB, hzc⟩ := Subgroup.mem_inf.1 hzmem
    have hzE : (z : Equiv.Perm (Fin 276)) ∈ E' := Subgroup.mem_subgroupOf.1 hzB
    have hz1' : (z : Equiv.Perm (Fin 276)) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    have hzx : (z : Equiv.Perm (Fin 276)) ∈ Subgroup.zpowers (co3FiveLine 25) := by
      rw [← co3FiveCentA_eq]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun a ha => ?_, ?_⟩
      · have ha' : a ∈ co3FiveQ := co3FiveA_eq_Q ▸ ha
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨a, ha'⟩)
      · exact co3FiveA_le_C25 (by rw [co3FiveA_eq_Q]; exact z.2)
    have hcx : Nat.card (Subgroup.zpowers (co3FiveLine 25)) = 5 := by
      rw [Nat.card_zpowers, orderOf_co3FiveLine]
    have hz5 : orderOf (z : Equiv.Perm (Fin 276)) = 5 := by
      have hd : orderOf (z : Equiv.Perm (Fin 276)) ∣ 5 := by
        have := Subgroup.orderOf_dvd_natCard _ hzx
        rwa [hcx] at this
      rcases (Nat.dvd_prime (by norm_num)).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hz1'
      · exact h
    have heq : Subgroup.zpowers (z : Equiv.Perm (Fin 276)) =
        Subgroup.zpowers (co3FiveLine 25) :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzx) (by
        rw [hcx, Nat.card_zpowers, hz5])
    have hx25z : co3FiveLine 25 ∈ Subgroup.zpowers (z : Equiv.Perm (Fin 276)) := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le).2 hzE hx25z
  have hs'C : s' ∈ co3FiveC25 := by
    rw [co3FiveC25_eq]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hs'P⟩
    exact (hcomm' _ hx25).symm
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep co3FiveKeyPts_lt co3Five_C25_facts.enum hs'C
  set t : Array ℕ := co3FiveC25Cert.pts[i]! with ht
  have hs'3' : s' ^ 3 = 1 := hs'3 ▸ pow_orderOf_eq_one s'
  have hs'1 : s' ≠ 1 := fun h => by rw [h, orderOf_one] at hs'3; omega
  have hcount : ((List.range co3FiveQCert.pts.size).filter
      fun j => commA 276 co3FiveQCert.pts[j]! t).length < 25 := by
    have hfive : fiveCheck () = true := Certificates.certificate36903.2.2.2
    simp only [fiveCheck] at hfive
    have := allLt_spec hfive hi
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    rcases this with (h1 | h2) | h3
    · rw [(eqA_iff (rep_powArr hrep 3) rep_idA).2 hs'3'] at h1
      exact absurd h1 (by decide)
    · exact absurd ((eqA_iff hrep rep_idA).1 h2) hs'1
    · exact h3
  let J : Finset ℕ := ((List.range co3FiveQCert.pts.size).filter
    fun j => commA 276 co3FiveQCert.pts[j]! t).toFinset
  have hJ : J.card < 25 := lt_of_le_of_lt (List.toFinset_card_le _) hcount
  have hmem : ∀ e ∈ E', ∃ j, j ∈ J ∧ Rep 276 co3FiveQCert.pts[j]! e := by
    intro e he
    obtain ⟨j, hj, hjrep⟩ := enumOK_exists_rep co3FiveKeyPts_lt co3Five_Q_facts.enum (hE'Q he)
    refine ⟨j, ?_, hjrep⟩
    simp only [J, List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨hj, (commA_iff hjrep hrep).2 (hcomm' e he)⟩
  choose! f hfJ hfrep using hmem
  let F : E' → J := fun e => ⟨f e, hfJ e e.2⟩
  have hF : Function.Injective F := by
    intro e₁ e₂ h
    have h' : f e₁ = f e₂ := congrArg Subtype.val h
    exact Subtype.ext ((hfrep e₁ e₁.2).unique (h' ▸ hfrep e₂ e₂.2))
  have hle := Nat.card_le_card_of_injective F hF
  rw [hE'card, Nat.card_eq_fintype_card, Fintype.card_coe] at hle
  omega

end Five

section Classes


private theorem exists_conj_xA_xB_y {s : Equiv.Perm (Fin 276)} (hs : s ∈ co3P)
    (hs3 : orderOf s = 3) :
    ∃ k ∈ co3P, ∃ c : Equiv.Perm (Fin 276), (c = xA ∨ c = xB ∨ c = yPerm) ∧ ∃ e : ℕ,
      (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s := by
  obtain ⟨h, hh, hcase⟩ := exists_conj_D_or_y hs hs3
  have hhinv : h⁻¹ ∈ co3P := co3P.inv_mem hh
  have hback : h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s := by group
  rcases hcase with hD | hy | hy2
  · obtain ⟨a, ha⟩ := hD
    have hk : idx a.toAdd < 243 := idx_lt _
    have hvec : φ (Multiplicative.ofAdd (vec (idx a.toAdd))) = h * s * h⁻¹ := by
      rw [vec_idx]
      exact ha
    have hk0 : idx a.toAdd ≠ 0 := by
      intro h0
      have ha0 : a.toAdd = 0 := (idx_eq_zero_iff _).1 h0
      have : a = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_one]
        exact ha0
      rw [this, map_one] at ha
      have hs1 : s = 1 := by
        have : h * s * h⁻¹ = 1 := ha.symm
        simpa using this
      rw [hs1, orderOf_one] at hs3
      omega
    obtain ⟨h', hh', hfuse⟩ := fuse_sound _ hk hk0
    rw [hvec] at hfuse
    refine ⟨h⁻¹ * h', co3P.mul_mem hhinv hh', ?_⟩
    rcases hfuse with hf | hf
    · refine ⟨xA, Or.inl rfl, 1, Or.inl rfl, ?_⟩
      calc h⁻¹ * h' * xA ^ 1 * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * xA * h'⁻¹) * h⁻¹⁻¹ := by group
        _ = s := by rw [hf]; exact hback
    · refine ⟨xB, Or.inr (Or.inl rfl), 1, Or.inl rfl, ?_⟩
      calc h⁻¹ * h' * xB ^ 1 * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * xB * h'⁻¹) * h⁻¹⁻¹ := by group
        _ = s := by rw [hf]; exact hback
  · refine ⟨h⁻¹, hhinv, yPerm, Or.inr (Or.inr rfl), 1, Or.inl rfl, ?_⟩
    rw [pow_one, ← hy]
    exact hback
  · refine ⟨h⁻¹, hhinv, yPerm, Or.inr (Or.inr rfl), 2, Or.inr rfl, ?_⟩
    rw [← hy2]
    exact hback

private theorem centralizer_pow_eq_of_pow_three' {G : Type*} [Group G] {X : G} (hX : X ^ 3 = 1)
    {e : ℕ} (he : e = 1 ∨ e = 2) :
    Subgroup.centralizer ({X ^ e} : Set G) = Subgroup.centralizer ({X} : Set G) := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · apply le_antisymm
    · intro z hz
      have hz' : z * X ^ 2 = X ^ 2 * z := Subgroup.mem_centralizer_singleton_iff.1 hz
      have hy4 : X = (X ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hX, one_mul, pow_one]
      rw [Subgroup.mem_centralizer_singleton_iff, hy4]
      exact Commute.pow_right hz' 2
    · intro z hz
      have hz' : z * X = X * z := Subgroup.mem_centralizer_singleton_iff.1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.pow_right (show Commute z X from hz') 2).eq

private theorem pair_conj {c s k : Equiv.Perm (Fin 276)} (hk : k ∈ co3P) {e : ℕ}
    (hkc : k * c ^ e * k⁻¹ = s)
    (h : ∃ g₁ g₂ : Equiv.Perm (Fin 276), g₁ ∈ co3P ∧ g₂ ∈ co3P ∧ g₁ * c = c * g₁ ∧
      g₂ * c = c * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276))))) :
    ∃ g₁ g₂ : Equiv.Perm (Fin 276), g₁ ∈ co3P ∧ g₂ ∈ co3P ∧ g₁ * s = s * g₁ ∧
      g₂ * s = s * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276)))) := by
  obtain ⟨g₁, g₂, hg₁, hg₂, hc₁, hc₂, ho₁, ho₂, hbig⟩ := h
  have hkinv : k⁻¹ ∈ co3P := co3P.inv_mem hk
  have hcomm : ∀ g : Equiv.Perm (Fin 276), g * c = c * g →
      (k * g * k⁻¹) * s = s * (k * g * k⁻¹) := by
    intro g hg
    have hge : g * c ^ e = c ^ e * g := (Commute.pow_right (show Commute g c from hg) e).eq
    rw [← hkc]
    calc k * g * k⁻¹ * (k * c ^ e * k⁻¹) = k * (g * c ^ e) * k⁻¹ := by group
      _ = k * (c ^ e * g) * k⁻¹ := by rw [hge]
      _ = k * c ^ e * k⁻¹ * (k * g * k⁻¹) := by group
  have hord : ∀ g : Equiv.Perm (Fin 276), orderOf g = 5 → orderOf (k * g * k⁻¹) = 5 := by
    intro g hg
    have := (MulAut.conj k : Equiv.Perm (Fin 276) ≃* Equiv.Perm (Fin 276)).orderOf_eq g
    simpa [MulAut.conj_apply, hg] using this
  refine ⟨k * g₁ * k⁻¹, k * g₂ * k⁻¹, co3P.mul_mem (co3P.mul_mem hk hg₁) hkinv,
    co3P.mul_mem (co3P.mul_mem hk hg₂) hkinv, hcomm g₁ hc₁, hcomm g₂ hc₂, hord g₁ ho₁,
    hord g₂ ho₂, ?_⟩
  have hmap : (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276)))).map
      (MulAut.conj k).toMonoidHom = Subgroup.closure
        ({k * g₁ * k⁻¹, k * g₂ * k⁻¹} : Set (Equiv.Perm (Fin 276))) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj k).injective]
  exact hbig

private theorem good_of_order_three {s : Equiv.Perm (Fin 276)} (hs : s ∈ co3P)
    (hs3 : orderOf s = 3) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 276))) ⊓ co3P :
      Subgroup (Equiv.Perm (Fin 276))) ∨
    ∃ g₁ g₂ : Equiv.Perm (Fin 276), g₁ ∈ co3P ∧ g₂ ∈ co3P ∧ g₁ * s = s * g₁ ∧
      g₂ * s = s * g₂ ∧ orderOf g₁ = 5 ∧ orderOf g₂ = 5 ∧
      1080 < Nat.card (Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276)))) := by
  obtain ⟨k, hk, c, hc, e, he, hkc⟩ := exists_conj_xA_xB_y hs hs3
  rcases hc with rfl | rfl | rfl
  · exact Or.inr (pair_conj hk hkc pair_xA)
  · exact Or.inr (pair_conj hk hkc pair_xB)
  · left
    have h1 := card_centralizer_inf_conj co3P hk hkc
    rw [centralizer_pow_eq_of_pow_three' yPerm_pow he] at h1
    have h2 : Nat.card (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 276))) ⊓ co3P :
        Subgroup (Equiv.Perm (Fin 276))) = 4536 := by
      rw [← Cy_eq.1]
      exact Cy_eq.2
    rw [← h1, h2]
    norm_num

private theorem no_subnormal_1080 {s : Equiv.Perm (Fin 276)} (hs : s ∈ co3P) (hs3 : orderOf s = 3)
    {K : Subgroup (Equiv.Perm (Fin 276))}
    (hsub : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 276))) ⊓
      co3P)) (hcard : Nat.card K = 1080) : False := by
  have hKC : K ≤ Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 276))) ⊓ co3P :=
    le_of_isSubnormal_open hsub
  set C := Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 276))) ⊓ co3P with hC
  rcases good_of_order_three hs hs3 with h5 | ⟨g₁, g₂, hg₁, hg₂, hc₁, hc₂, ho₁, ho₂, hbig⟩
  · exact h5 ((by norm_num : 5 ∣ 1080).trans (hcard ▸ Subgroup.card_dvd_of_le hKC))
  · have h25 : ¬ 25 ∣ Nat.card C := by
      intro hd
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 (n := 2)
        (by simpa using hd)
      refine no_order25_centralized hs hs3 (E := E.map C.subtype) ?_ ?_ ?_
      · rintro _ ⟨e, -, rfl⟩
        exact (Subgroup.mem_inf.1 e.2).2
      · rw [Subgroup.card_map_of_injective C.subtype_injective, hE]
        norm_num
      · rintro _ ⟨e, -, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 e.2).1
    have hrel : ¬ 5 ∣ K.relIndex C := by
      intro hd
      apply h25
      have h := Subgroup.relIndex_mul_card K C
      rw [inf_eq_left.2 hKC, hcard] at h
      have h' : 5 * 5 ∣ Nat.card C := h ▸ Nat.mul_dvd_mul hd (by norm_num : 5 ∣ 1080)
      simpa using h'
    have hco : ∀ g ∈ C, orderOf g = 5 → g ∈ K := fun g hg ho =>
      mem_of_isSubnormal_of_coprime hsub hg (by
        rw [ho]
        exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hrel)
    have hcl : Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 276))) ≤ K := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hco _ (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hc₁, hg₁⟩) ho₁
      · exact hco _ (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hc₂, hg₂⟩) ho₂
    have := Subgroup.card_le_of_le hcl
    omega

end Classes

section Main


private theorem no_subnormal_1080_of_mulEquiv {G : Type*} [Group G] (φ : G ≃* ↥co3P) {s : G}
    (hs : orderOf s = 3) {K : Subgroup G}
    (hsub : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({s} : Set G)))
    (hcard : Nat.card K = 1080) : False := by
  let ι : G →* Equiv.Perm (Fin 276) := co3P.subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := co3P.subtype_injective.comp φ.injective
  have hmapC : (Subgroup.centralizer ({s} : Set G)).map ι =
      Subgroup.centralizer ({ι s} : Set (Equiv.Perm (Fin 276))) ⊓ co3P := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, (φ y).2⟩
      show ι y * ι s = ι s * ι y
      rw [← map_mul, ← map_mul, hy]
    · rintro ⟨hx, hxP⟩
      have hxι : ι (φ.symm ⟨x, hxP⟩) = x := by simp [ι]
      refine ⟨φ.symm ⟨x, hxP⟩, ?_, hxι⟩
      apply hι
      rw [map_mul, map_mul, hxι]
      exact hx
  have hsub' := hsub.map ι
  rw [hmapC] at hsub'
  have hts : orderOf (ι s) = 3 := by rw [orderOf_injective ι hι s]; exact hs
  exact no_subnormal_1080 (φ s).2 hts hsub' ((Subgroup.card_map_of_injective hι).trans hcard)

end Main

theorem sporNoPumpup_Co3
    (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    SporNoPumpup .Co3 := by
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Co3).Group :=
    Finite.of_equiv ↥co3P ((hbr .Co3).some.symm.trans co3PermEquiv).symm.toEquiv
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (hbr .Co3).some.toEquiv]
    show Nat.card NativeSporadic.Co3 = sporOrd .Co3
    rw [card_Co3_of_perm]
    rfl
  · exact OPrimeCoreTrivialAt.of_mulEquiv ((hbr .Co3).some.symm.trans co3PermEquiv)
      oPrimeCoreTrivialAt_co3P
  · intro s hs K hK h
    rcases h with h | ⟨hM, _⟩
    · exact no_subnormal_1080_of_mulEquiv ((hbr .Co3).some.symm.trans co3PermEquiv) hs hK.2.1
        (card_of_isHatSix h)
    · exact absurd hM (by decide)
  · intro h3
    exact absurd h3 (by decide)

end CFSG.HardMathSupport.Solomon.Coordinator
