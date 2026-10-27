module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Three
public import CFSG.RankThree.Native.Co2FiveCentralizers
public import Certificates.Certificate36904

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

namespace Co2Spor

theorem exists_conj_le_of_full {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {P Q R : Subgroup G}
    [Finite P] (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p)
    (hRP : R ≤ P) (hR : IsPGroup p ↥R) : ∃ g ∈ P, ∀ r ∈ R, g⁻¹ * r * g ∈ Q := by
  let S0 : Sylow p P := Sylow.ofCard (Q.subgroupOf P)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQ])
  have hpg : IsPGroup p ↥(R.subgroupOf P) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRP).symm
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S0 S
  refine ⟨g, g.2, fun r hr => ?_⟩
  have hmem : (⟨r, hRP hr⟩ : P) ∈ ((g • S0 : Sylow p P) : Subgroup P) := by
    rw [hg]
    exact hS (Subgroup.mem_subgroupOf.2 hr)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  have : ((g⁻¹ * ⟨r, hRP hr⟩ * g : P) : G) ∈ Q := hmem
  simpa using this

theorem mem_of_card_sq_of_central {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p ^ 3) {z : G} (hz : z ∈ Subgroup.center G)
    (hnc : ¬ ∀ a b : G, a * b = b * a) {R : Subgroup G} (hR : Nat.card R = p ^ 2) : z ∈ R := by
  by_contra hzR
  have hRc : ∀ a b : R, a * b = b * a := IsPGroup.commutative_of_card_eq_prime_sq hR
  set H : Subgroup G := Subgroup.closure ((R : Set G) ∪ {z}) with hH
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hzH : z ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have hHc : IsMulCommutative ↥H := by
    refine Subgroup.isMulCommutative_closure ?_
    intro u hu v hv _
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact congrArg Subtype.val (hRc ⟨u, hu⟩ ⟨v, hv⟩)
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Subgroup.mem_center_iff.1 hz u
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (Subgroup.mem_center_iff.1 hz v).symm
    · rw [Set.mem_singleton_iff] at hu hv
      subst hu
      subst hv
      exact absurd rfl ‹_›
  have hdvd1 : p ^ 2 ∣ Nat.card H := hR ▸ Subgroup.card_dvd_of_le hRH
  have hdvd2 : Nat.card H ∣ p ^ 3 := hG ▸ Subgroup.card_subgroup_dvd_card H
  have hne : Nat.card H ≠ p ^ 2 := by
    intro h
    have : R = H := Subgroup.eq_of_le_of_card_ge hRH (by rw [h, hR])
    exact hzR (this ▸ hzH)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd2
  have hp2 : 2 ≤ k := by
    have h1 : p ^ 2 ∣ p ^ k := hk' ▸ hdvd1
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h1
  have hk3 : k = 3 := by
    interval_cases k
    · exact absurd hk' hne
    · rfl
  have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [hk', hk3, hG])
  apply hnc
  intro a b
  have ha : a ∈ H := hHtop ▸ Subgroup.mem_top a
  have hb : b ∈ H := hHtop ▸ Subgroup.mem_top b
  exact congrArg Subtype.val (hHc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

section Certified

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T Co2Pump

theorem fuseCheck_parts (h : fuseCheck () = true) :
    (∀ i < 2, validA 2300 (fuseGens ())[i]! = true ∧
      inP (levels ()) (fuseGens ())[i]! = true) ∧
    ∀ k < 81, k = 0 ∨ (tPar[k]! = k ∧ (k = kA ∨ k = kB)) ∨
      (tPar[k]! < 81 ∧ tPar[k]! ≠ 0 ∧ tGen[k]! < 2 ∧ tDep[tPar[k]!]! < tDep[k]! ∧
        eqA 2300 (dElts ())[k]! (conjA 2300 (fuseGens ())[tGen[k]!]! (dElts ())[tPar[k]!]!) =
          true) := by
  unfold fuseCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · have := allLt_spec h1 hi
    simpa only [Bool.and_eq_true] using this
  · have := allLt_spec h2 hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with (h0 | h0) | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨h0.1.1.1.1, h0.1.1.1.2, h0.1.1.2, h0.1.2, h0.2⟩)

section CertFusion


theorem fuse_forest : ∀ m k, k < 81 → k ≠ 0 → tDep[k]! = m →
    ∃ n ∈ co2P, ∃ c, (c = kA ∨ c = kB) ∧
      n * φ (Multiplicative.ofAdd (vec k)) * n⁻¹ = φ (Multiplicative.ofAdd (vec c)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk hk0 hm
    obtain ⟨hgens, hforest⟩ := fuseCheck_parts Certificates.certificate36904.1
    rcases hforest k hk with h0 | ⟨hpar, hroot⟩ | ⟨hp81, hp0, hg2, hdep, heq⟩
    · exact absurd h0 hk0
    · exact ⟨1, co2P.one_mem, k, hroot, by simp⟩
    · obtain ⟨hNv, hNP⟩ := hgens (tGen[k]!) hg2
      have hNmem : permOfArr 2300 (fuseGens ())[tGen[k]!]! ∈ co2P :=
        mem_co2P_of_inP (rep_of_validA hNv) hNP
      have hrep := rep_conjA hNv (rep_dElts hp81)
      have hdk := (eqA_iff (rep_dElts hk) hrep).1 heq
      obtain ⟨n', hn'P, c, hc, hn'⟩ := ih _ (hm ▸ hdep) _ hp81 hp0 rfl
      refine ⟨n' * (permOfArr 2300 (fuseGens ())[tGen[k]!]!)⁻¹,
        co2P.mul_mem hn'P (co2P.inv_mem hNmem), c, hc, ?_⟩
      rw [hdk, ← hn']
      group

theorem exists_conj_xRep {s : Equiv.Perm (Fin 2300)} (hs : s ∈ co2P) (hs3 : orderOf s = 3) :
    ∃ n ∈ co2P, ∃ c, (c = kA ∨ c = kB) ∧
      n * s * n⁻¹ = φ (Multiplicative.ofAdd (vec c)) := by
  obtain ⟨h, hhP, hD⟩ := exists_conj_mem_Dg hs hs3
  have hD' : h * s * h⁻¹ ∈ (φ : Multiplicative (Fin 4 → ZMod 3) →* Equiv.Perm (Fin 2300)).range :=
    hD
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hD'
  have hk := idx_lt a.toAdd
  have hvec : vec (idx a.toAdd) = a.toAdd := vec_idx _
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one] at ha
    have : s = 1 := by
      have h1 : h * s * h⁻¹ = 1 := ha.symm
      calc s = h⁻¹ * (h * s * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hs3
    omega
  have hk0 : idx a.toAdd ≠ 0 := fun h0 => ha1 (by
    have := (idx_eq_zero_iff _).1 h0
    exact Multiplicative.toAdd.injective (by simpa using this))
  obtain ⟨n', hn'P, c, hc, hn'⟩ := fuse_forest _ _ hk hk0 rfl
  refine ⟨n' * h, co2P.mul_mem hn'P hhP, c, hc, ?_⟩
  have h1 : φ (Multiplicative.ofAdd (vec (idx a.toAdd))) = h * s * h⁻¹ := by
    rw [hvec]
    simpa using ha
  rw [← hn', h1]
  group

end CertFusion

section CertPairs

theorem treeOK_card_le {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (h : treeOK n gs ps c = true) :
    c.pts.size ≤ Nat.card ↥(Subgroup.closure (permsA n gs)) := by
  unfold treeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hgs, hpos⟩, hroot⟩, htree⟩, hkeys⟩ := h
  have hrep : ∀ i < c.pts.size, ∃ g ∈ Subgroup.closure (permsA n gs), Rep n c.pts[i]! g := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [hroot]
        exact rep_idA
      · have := allLt_spec htree hi
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
        rcases this with h0 | ⟨⟨hp, hl⟩, he⟩
        · omega
        · obtain ⟨g, hg, hrg⟩ := ih (c.par[i]!) hp (hp.trans hi)
          have hgl := rep_of_validA (allLt_spec hgs hl)
          refine ⟨permOfArr n gs[c.lab[i]!]! * g,
            Subgroup.mul_mem _ (Subgroup.subset_closure (mem_permsA hl)) hg, ?_⟩
          rw [he]
          exact rep_compA hgl hrg
  choose! f hfmem hfrep using hrep
  have hnd : (c.pts.toList.map (keyA n ps)).Nodup := by
    have hp := List.mergeSort_perm (c.pts.toList.map (keyA n ps)) (fun a b => decide (a ≤ b))
    exact hp.nodup_iff.1 (List.Pairwise.imp (fun h' => ne_of_lt h') hkeys)
  have hlen : (c.pts.toList.map (keyA n ps)).length = c.pts.size := by simp
  have hinj : Function.Injective (fun i : Fin c.pts.size => (⟨f i, hfmem i i.2⟩ :
      ↥(Subgroup.closure (permsA n gs)))) := by
    intro i j hij
    have hij' : f i = f j := congrArg Subtype.val hij
    have hkey : keyA n ps c.pts[(i : ℕ)]! = keyA n ps c.pts[(j : ℕ)]! := by
      unfold keyA
      congr 1
      apply List.map_congr_left
      intro p hp
      have hp' := hps p hp
      rw [(hfrep i i.2).apply hp', (hfrep j j.2).apply hp', hij']
    have hgi : (c.pts.toList.map (keyA n ps))[(i : ℕ)]'(by rw [hlen]; exact i.2) =
        keyA n ps c.pts[(i : ℕ)]! := by
      simp [getElem!_pos c.pts i i.2]
    have hgj : (c.pts.toList.map (keyA n ps))[(j : ℕ)]'(by rw [hlen]; exact j.2) =
        keyA n ps c.pts[(j : ℕ)]! := by
      simp [getElem!_pos c.pts j j.2]
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 (hgi.trans (hkey.trans hgj.symm)))
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem permsA_two {n : ℕ} {gs : Array (Array ℕ)} (h : gs.size = 2) :
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


theorem pair_sound {c : Array ℕ} {X : Equiv.Perm (Fin 2300)} (hc : Rep 2300 c X)
    {gs : Array (Array ℕ)} {fuel : ℕ} (h : pairCheck c gs fuel = true) :
    ∃ a b : Equiv.Perm (Fin 2300), a ∈ co2P ∧ b ∈ co2P ∧ a * X = X * a ∧ b * X = X * b ∧
      orderOf a = 5 ∧ orderOf b = 5 ∧
      1080 < Nat.card ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 2300)))) := by
  unfold pairCheck at h
  dsimp only at h
  generalize arrBfs (leftA 2300 gs) gs.size (keyA 2300 co2FiveKeyPts) (idA 2300) fuel = cert at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hsz, hall⟩, htree⟩, hbig⟩ := h
  have hone : ∀ i < 2, Rep 2300 gs[i]! (permOfArr 2300 gs[i]!) ∧ permOfArr 2300 gs[i]! ∈ co2P ∧
      permOfArr 2300 gs[i]! * X = X * permOfArr 2300 gs[i]! ∧
      orderOf (permOfArr 2300 gs[i]!) = 5 := by
    intro i hi
    have h1 := allLt_spec hall hi
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
    obtain ⟨⟨⟨⟨hv, hP⟩, hcm⟩, hpw⟩, hne⟩ := h1
    have hrep := rep_of_validA hv
    refine ⟨hrep, mem_co2P_of_inP hrep hP, ?_, ?_⟩
    · exact (CFSG.RankThree.Native.commA_iff hrep hc).1 hcm
    · have h5 : permOfArr 2300 gs[i]! ^ 5 = 1 :=
        (eqA_iff (rep_powArr hrep 5) rep_idA).1 hpw
      have h1 : permOfArr 2300 gs[i]! ≠ 1 := fun h' =>
        absurd ((eqA_iff hrep rep_idA).2 h') (by rw [hne]; exact Bool.false_ne_true)
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact orderOf_eq_prime h5 h1
  obtain ⟨-, hP0, hc0, ho0⟩ := hone 0 (by norm_num)
  obtain ⟨-, hP1, hc1, ho1⟩ := hone 1 (by norm_num)
  refine ⟨permOfArr 2300 gs[0]!, permOfArr 2300 gs[1]!, hP0, hP1, hc0, hc1, ho0, ho1, ?_⟩
  have hle := treeOK_card_le (ps := co2FiveKeyPts) (by decide) htree
  rw [permsA_two hsz] at hle
  omega

end CertPairs

section CertFive


theorem x0_mem_of_card_25 {R : Subgroup (Equiv.Perm (Fin 2300))} (hRQ : R ≤ co2FiveQ)
    (hR : Nat.card R = 25) : co2FiveLine 0 ∈ R := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcomm : ∀ g ∈ co2FiveQ, g * co2FiveLine 0 = co2FiveLine 0 * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1
      (co2FiveC0_le_centralizer (co2FiveA_le_C0 (co2FiveA_eq_Q ▸ hg)))
  have hz : (⟨co2FiveLine 0, co2FiveLine_mem_Q 0⟩ : ↥co2FiveQ) ∈ Subgroup.center ↥co2FiveQ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2)
  have hnc : ¬ ∀ a b : ↥co2FiveQ, a * b = b * a := by
    intro hall
    have hle : co2FiveA ≤ Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓
        co2FiveC0 := by
      intro g hg
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_, co2FiveA_le_C0 hg⟩
      have hh' : h ∈ co2FiveQ := co2FiveA_eq_Q ▸ hh
      have hg' : g ∈ co2FiveQ := co2FiveA_eq_Q ▸ hg
      exact congrArg Subtype.val (hall ⟨h, hh'⟩ ⟨g, hg'⟩)
    have := Subgroup.card_le_of_le hle
    rw [card_co2FiveA, card_co2FiveCentA] at this
    omega
  have hmem := mem_of_card_sq_of_central (p := 5) (G := ↥co2FiveQ)
    (by rw [card_co2FiveQ]; norm_num) hz hnc (R := R.subgroupOf co2FiveQ)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRQ).toEquiv, hR]; norm_num)
  exact Subgroup.mem_subgroupOf.1 hmem


theorem fiveCheck_parts (h : fiveCheck () = true) :
    ∀ i < co2FiveC0Cert.pts.size,
      eqA 2300 (powArr 2300 co2FiveC0Cert.pts[i]! 3) (idA 2300) = false ∨
      eqA 2300 co2FiveC0Cert.pts[i]! (idA 2300) = true ∨
      ((List.range co2FiveQCert.pts.size).filter fun j =>
        CFSG.RankThree.Native.commA 2300 co2FiveQCert.pts[j]! co2FiveC0Cert.pts[i]!).length
          < 25 := by
  intro i hi
  unfold fiveCheck at h
  dsimp only at h
  have := allLt_spec h hi
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
  rcases this with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem not_dvd_card_centralizer {s : Equiv.Perm (Fin 2300)} (hs : s ∈ co2P)
    (hs3 : orderOf s = 3) :
    ¬ 25 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) := by
  intro h25
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C := Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P with hC
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 (n := 2)
    (by simpa using h25)
  set R : Subgroup (Equiv.Perm (Fin 2300)) := K.map C.subtype with hR
  have hRcard : Nat.card R = 25 := by
    rw [hR, Subgroup.card_map_of_injective C.subtype_injective, hK]
    norm_num
  have hRC : R ≤ C := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hRP : R ≤ co2P := hRC.trans inf_le_right
  have hRp : IsPGroup 5 ↥R := IsPGroup.of_card (n := 2) (by rw [hRcard]; norm_num)
  obtain ⟨g, hgP, hg⟩ := exists_conj_le_of_full (p := 5) co2FiveQ_le_P
    (by rw [card_co2FiveQ, factorization_card_co2P_five]; norm_num) hRP hRp
  set R' : Subgroup (Equiv.Perm (Fin 2300)) := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'
  have hR'Q : R' ≤ co2FiveQ := by
    rintro _ ⟨r, hr, rfl⟩
    simpa using hg r hr
  have hR'card : Nat.card R' = 25 := by
    rw [hR', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hRcard]
  have hx0 : co2FiveLine 0 ∈ R' := x0_mem_of_card_25 hR'Q hR'card
  set t : Equiv.Perm (Fin 2300) := g⁻¹ * s * g with ht
  have htP : t ∈ co2P := co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hgP) hs) hgP
  have ht3 : orderOf t = 3 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 2300) ≃* Equiv.Perm (Fin 2300)).orderOf_eq s
    simpa [MulAut.conj_apply, ht, hs3] using this
  have hcomm : ∀ r ∈ R', r * t = t * r := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : r * s = s * r := Subgroup.mem_centralizer_singleton_iff.1 (hRC hr).1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ht]
    calc g⁻¹ * r * g * (g⁻¹ * s * g) = g⁻¹ * (r * s) * g := by group
      _ = g⁻¹ * (s * r) * g := by rw [h1]
      _ = g⁻¹ * s * g * (g⁻¹ * r * g) := by group
  have htC : t ∈ co2FiveC0 := by
    rw [co2FiveC0_eq]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm _ hx0).symm, htP⟩
  obtain ⟨i, hi, hrep⟩ := co2FiveC0_exists_rep htC
  have ht3' : t ^ 3 = 1 := ht3 ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht3; omega
  rcases fiveCheck_parts Certificates.certificate36904.2.2.2 i hi with h1 | h1 | h1
  · rw [(eqA_iff (rep_powArr hrep 3) rep_idA).2 ht3'] at h1
    exact absurd h1 (by decide)
  · exact ht1 ((eqA_iff hrep rep_idA).1 h1)
  · set F := ((List.range co2FiveQCert.pts.size).filter fun j =>
      CFSG.RankThree.Native.commA 2300 co2FiveQCert.pts[j]! co2FiveC0Cert.pts[i]!) with hF
    have hsub : (R' : Set (Equiv.Perm (Fin 2300))) ⊆
        ↑(F.toFinset.image fun j => permOfArr 2300 co2FiveQCert.pts[j]!) := by
      intro r hr
      obtain ⟨j, hj, hjr⟩ := (co2FiveQ_spec.1 r).1 (hR'Q hr)
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨j, ?_, hjr⟩
      rw [List.mem_toFinset, hF, List.mem_filter, List.mem_range]
      refine ⟨hj, ?_⟩
      have hQrep := co2FiveQ_spec.2.2 j hj
      exact (CFSG.RankThree.Native.commA_iff hQrep hrep).2 (by rw [hjr]; exact hcomm r hr)
    have h2 : (R' : Set (Equiv.Perm (Fin 2300))).ncard ≤
        (F.toFinset.image fun j => permOfArr 2300 co2FiveQCert.pts[j]!).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    have h3 := Finset.card_image_le (s := F.toFinset)
      (f := fun j => permOfArr 2300 co2FiveQCert.pts[j]!)
    have h4 := List.toFinset_card_le F
    have h5 : Nat.card R' = (R' : Set (Equiv.Perm (Fin 2300))).ncard :=
      (Nat.card_coe_set_eq _)
    omega

end CertFive

section CertMain


theorem exists_pair_xRep {c : ℕ} (hc : c = kA ∨ c = kB) :
    ∃ a b : Equiv.Perm (Fin 2300), a ∈ co2P ∧ b ∈ co2P ∧
      a * φ (Multiplicative.ofAdd (vec c)) = φ (Multiplicative.ofAdd (vec c)) * a ∧
      b * φ (Multiplicative.ofAdd (vec c)) = φ (Multiplicative.ofAdd (vec c)) * b ∧
      orderOf a = 5 ∧ orderOf b = 5 ∧
      1080 < Nat.card ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 2300)))) := by
  have hc81 : c < 81 := by
    rcases hc with rfl | rfl <;> decide
  rcases hc with rfl | rfl
  · exact pair_sound (rep_dElts hc81) Certificates.certificate36904.2.1
  · exact pair_sound (rep_dElts hc81) Certificates.certificate36904.2.2.1

theorem co2P_fiveGen {s : Equiv.Perm (Fin 2300)} (hs : s ∈ co2P)
    (hs3 : orderOf s = 3) :
    ¬ 25 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) ∧
    ∃ T : Set (Equiv.Perm (Fin 2300)), T ⊆ co2P ∧
      (∀ g ∈ T, g * s = s * g ∧ orderOf g = 5) ∧ 1080 < Nat.card ↥(Subgroup.closure T) := by
  refine ⟨not_dvd_card_centralizer hs hs3, ?_⟩
  obtain ⟨n, hnP, c, hc, hn⟩ := exists_conj_xRep hs hs3
  obtain ⟨a, b, haP, hbP, hac, hbc, ha5, hb5, hbig⟩ := exists_pair_xRep hc
  have hs' : s = n⁻¹ * φ (Multiplicative.ofAdd (vec c)) * n := by
    rw [← hn]
    group
  have hord : ∀ x : Equiv.Perm (Fin 2300), orderOf (n⁻¹ * x * n) = orderOf x := fun x => by
    have := (MulAut.conj n⁻¹ : Equiv.Perm (Fin 2300) ≃* Equiv.Perm (Fin 2300)).orderOf_eq x
    simpa [MulAut.conj_apply] using this
  have hcommute : ∀ x : Equiv.Perm (Fin 2300),
      x * φ (Multiplicative.ofAdd (vec c)) = φ (Multiplicative.ofAdd (vec c)) * x →
        n⁻¹ * x * n * s = s * (n⁻¹ * x * n) := by
    intro x hx
    calc n⁻¹ * x * n * s = n⁻¹ * (x * φ (Multiplicative.ofAdd (vec c))) * n := by
          rw [hs']; group
      _ = n⁻¹ * (φ (Multiplicative.ofAdd (vec c)) * x) * n := by rw [hx]
      _ = s * (n⁻¹ * x * n) := by rw [hs']; group
  refine ⟨{n⁻¹ * a * n, n⁻¹ * b * n}, ?_, ?_, ?_⟩
  · rintro _ (rfl | rfl)
    · exact co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hnP) haP) hnP
    · exact co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hnP) hbP) hnP
  · rintro _ (rfl | rfl)
    · exact ⟨hcommute a hac, by rw [hord, ha5]⟩
    · exact ⟨hcommute b hbc, by rw [hord, hb5]⟩
  · have hcl : Subgroup.closure ({n⁻¹ * a * n, n⁻¹ * b * n} : Set (Equiv.Perm (Fin 2300))) =
        (Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 2300)))).map
          (MulAut.conj n⁻¹).toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]
      simp [MulAut.conj_apply]
    rw [hcl, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective]
    exact hbig

end CertMain

theorem fiveGen_transport
    {S : Type*} [Group S] (ψ : S →* Equiv.Perm (Fin 2300)) (hψ : Function.Injective ψ)
    (hrange : ψ.range = co2P) (s : S) (hs3 : orderOf s = 3) :
    ¬ 25 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set S)) ∧
      ∃ T : Set S, T ⊆ ↑(Subgroup.centralizer ({s} : Set S)) ∧ (∀ g ∈ T, orderOf g = 5) ∧
        1080 < Nat.card ↥(Subgroup.closure T) := by
  have hsP : ψ s ∈ co2P := hrange ▸ MonoidHom.mem_range.2 ⟨s, rfl⟩
  have hs3' : orderOf (ψ s) = 3 := by rw [orderOf_injective ψ hψ s]; exact hs3
  obtain ⟨h25, T', hT'P, hT'c, hbig⟩ := co2P_fiveGen hsP hs3'
  have hmap : (Subgroup.centralizer ({s} : Set S)).map ψ =
      Subgroup.centralizer ({ψ s} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by rw [← map_mul, ← map_mul, hy], hrange ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩⟩
    · rintro ⟨hx, hxP⟩
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 (hrange ▸ hxP)
      exact ⟨y, hψ (by rw [map_mul, map_mul, hx]), rfl⟩
  refine ⟨?_, ψ ⁻¹' T', ?_, ?_, ?_⟩
  · rwa [← Subgroup.card_map_of_injective hψ, hmap]
  · intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.2 (hψ (by rw [map_mul, map_mul]; exact (hT'c _ hg).1))
  · intro g hg
    rw [← orderOf_injective ψ hψ g]
    exact (hT'c _ hg).2
  · have himg : ψ '' (ψ ⁻¹' T') = T' := by
      rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
      intro x hx
      exact MonoidHom.mem_range.1 (hrange ▸ hT'P hx)
    rw [← Subgroup.card_map_of_injective hψ, MonoidHom.map_closure, himg]
    exact hbig

end Certified

end Co2Spor

open Co2Spor

open CFSG.Sporadic.Co2Cert in
theorem sporNoPumpup_Co2
    (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    SporNoPumpup .Co2 := by
  have e0 : (TauCeti.CFSGIndex.sporadic .Co2).Group ≃* NativeSporadic.Co2 := (hbr .Co2).some.symm
  let φS : (TauCeti.CFSGIndex.sporadic .Co2).Group ≃* ↥co2P := e0.trans co2PermEquiv
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Co2).Group :=
    Finite.of_equiv ↥co2P φS.symm.toEquiv
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [Nat.card_congr φS.toEquiv, card_co2P]
    rfl
  · exact OPrimeCoreTrivialAt.of_mulEquiv φS Co2T.oPrimeCoreTrivialAt_co2P
  · intro s hs K hK h
    rcases h with hSix | ⟨hM, _⟩
    · let ψ : (TauCeti.CFSGIndex.sporadic .Co2).Group →* Equiv.Perm (Fin 2300) :=
        co2P.subtype.comp φS.toMonoidHom
      have hψ : Function.Injective ψ := co2P.subtype_injective.comp φS.injective
      have hrange : ψ.range = co2P := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact (φS y).2
        · intro hx
          exact ⟨φS.symm ⟨x, hx⟩, by simp [ψ]⟩
      obtain ⟨h25, T, hTC, hT5, hbig⟩ := fiveGen_transport ψ hψ hrange s hs
      exact false_of_isHatSix_of_five_gen hK hSix h25 hTC hT5 hbig
    · exact absurd hM (by decide)
  · intro h
    exact absurd h (by decide)

end CFSG.HardMathSupport.Solomon.Coordinator
