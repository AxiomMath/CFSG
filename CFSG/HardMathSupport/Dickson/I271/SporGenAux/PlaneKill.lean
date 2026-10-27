module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped commutatorElement

section Defs

@[expose] def PFixGen (p : ℕ) {S : Type*} [Group S] (E : Subgroup (MulAut S)) : Prop :=
  ∃ T : Set S, Subgroup.closure T = ⊤ ∧
    ∀ σ ∈ T, Nat.Coprime (orderOf σ) p ∧ ∃ f ∈ E, f ≠ 1 ∧ f σ = σ

@[expose] def NoSig (p : ℕ) {S : Type*} [Group S] (E : Subgroup (MulAut S)) : Prop :=
  ∀ T : Subgroup (MulAut S), Nat.Coprime p (Nat.card T) →
    E ≤ Subgroup.normalizer (T : Set (MulAut S)) → T = ⊥

@[expose] def AutRankLe2 (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ E : Subgroup (MulAut S), IsElemAbelian p E → Nat.card E ≤ p ^ 2

@[expose] def PlaneKill (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ E : Subgroup (MulAut S), IsElemAbelian p E → Nat.card E = p ^ 2 → PFixGen p E ∨ NoSig p E

end Defs

section Img

variable {X : Type} [Group X]

@[expose] noncomputable def imgB (B K : Subgroup X) :
    Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)) :=
  ((B ⊓ Subgroup.normalizer (K : Set X)).subgroupOf (Subgroup.normalizer (K : Set X))).map
    (i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)))

theorem mem_imgB {B K : Subgroup X} {e : MulAut (↥K ⧸ Subgroup.center ↥K)} :
    e ∈ imgB B K ↔ ∃ (x : X) (hx : x ∈ Subgroup.normalizer (K : Set X)), x ∈ B ∧
      i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) ⟨x, hx⟩ = e := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, n.2, (Subgroup.mem_subgroupOf.1 hn).1, rfl⟩
  · rintro ⟨x, hx, hxB, rfl⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.2 ⟨hxB, hx⟩, rfl⟩

theorem card_imgB {B K : Subgroup X} (hperf : commutator ↥K = ⊤) :
    Nat.card (imgB B K) = autOrderIn B K := by
  unfold imgB
  rw [← Subgroup.relIndex_ker, ker_i271Act hperf (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)),
    Subgroup.relIndex_subgroupOf (inf_le_right : B ⊓ Subgroup.normalizer (K : Set X) ≤
      Subgroup.normalizer (K : Set X))]
  rfl

theorem isElemAbelian_imgB [Finite X] {p : ℕ} {B K : Subgroup X} (hB : IsElemAbelian p B) :
    IsElemAbelian p (imgB B K) :=
  CFSG.SectionRank.isElemAbelian_map
    (i271_isElemAbelian_subgroupOf _ (i271_isElemAbelian_of_le hB inf_le_left)) _

end Img

theorem isStronglyBalancedIn_of_noSig {X : Type} [Group X] {p : ℕ} {B K : Subgroup X}
    (hperf : commutator ↥K = ⊤) (h : NoSig p (imgB B K)) : IsStronglyBalancedIn p B K := by
  intro S0 hS0N hcop hnorm
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hN
  set θ := i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) with hθ
  set T : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)) := (S0.subgroupOf N).map θ with hT
  have hTcop : Nat.Coprime p (Nat.card T) := by
    have hcard : Nat.card (S0.subgroupOf N) = Nat.card S0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0N).toEquiv
    refine Nat.Coprime.coprime_dvd_right ?_ (hcard ▸ hcop)
    exact Subgroup.card_map_dvd _ _
  have hAT : imgB B K ≤ Subgroup.normalizer (T : Set (MulAut (↥K ⧸ Subgroup.center ↥K))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ∈ Subgroup.normalizer ((S0.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hx' : (x : X) ∈ B ⊓ N := hx
      have := Subgroup.mem_normalizer_iff.1 (hnorm hx') (h : X)
      simpa [Subgroup.mem_subgroupOf] using this
    exact Subgroup.le_normalizer_map θ (Subgroup.mem_map_of_mem θ hxn)
  have hTbot : T = ⊥ := h T hTcop hAT
  intro s hs
  have hsN : s ∈ N := hS0N hs
  have h1 : θ ⟨s, hsN⟩ ∈ T := Subgroup.mem_map_of_mem θ ((Subgroup.mem_subgroupOf).2 hs)
  rw [hTbot, Subgroup.mem_bot] at h1
  have h2 : (⟨s, hsN⟩ : ↥N) ∈ θ.ker := h1
  rw [hθ, ker_i271Act hperf (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)),
    Subgroup.mem_subgroupOf] at h2
  exact h2


section Lift

theorem commutator_mul_central_left {G : Type*} [Group G] {c : G} (hc : c ∈ Subgroup.center G)
    (a g : G) : ⁅a * c, g⁆ = ⁅a, g⁆ := by
  have h := Subgroup.mem_center_iff.1 hc g
  simp only [commutatorElement_def]
  calc a * c * g * (a * c)⁻¹ * g⁻¹ = a * (c * g) * c⁻¹ * a⁻¹ * g⁻¹ := by group
    _ = a * (g * c) * c⁻¹ * a⁻¹ * g⁻¹ := by rw [← h]
    _ = a * g * a⁻¹ * g⁻¹ := by group

theorem commutator_mul_central_right {G : Type*} [Group G] {d : G} (hd : d ∈ Subgroup.center G)
    (a b : G) : ⁅a, b * d⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.1 hd a⁻¹
  simp only [commutatorElement_def]
  calc a * (b * d) * a⁻¹ * (b * d)⁻¹ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [← h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_top_of_perfect_of_central {K : Type*} [Group K] (hperf : commutator K = ⊤)
    {H : Subgroup K} (hdec : ∀ g : K, ∃ h ∈ H, ∃ z ∈ Subgroup.center K, g = h * z) : H = ⊤ := by
  rw [eq_top_iff, ← hperf, commutator, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨ha, hha, za, hza, rfl⟩ := hdec a
  obtain ⟨hb, hhb, zb, hzb, rfl⟩ := hdec b
  rw [commutator_mul_central_left hza, commutator_mul_central_right hzb, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hha hhb) (H.inv_mem hha)) (H.inv_mem hhb)

variable {X : Type} [Group X] [Finite X]

theorem exists_coprime_lift_centralized {p : ℕ} {K : Subgroup X} (hp : p.Prime)
    (hZ : IsPGroup p (Subgroup.center ↥K)) {x : X} (hx : x ∈ Subgroup.normalizer (K : Set X))
    {σ : ↥K ⧸ Subgroup.center ↥K}
    (hfix : i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) ⟨x, hx⟩ σ = σ)
    (hco : Nat.Coprime (orderOf σ) p) :
    ∃ k : ↥K, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = σ ∧ Nat.Coprime (orderOf k) p ∧
      x * (k : X) * x⁻¹ = (k : X) := by
  obtain ⟨k, hk, hkco⟩ := CFSG.RankThree.CentralLift.exists_coprime_lift hp
    (QuotientGroup.mk' (Subgroup.center ↥K)) (QuotientGroup.mk'_surjective _) hco
  have hk' : (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = σ := hk
  refine ⟨k, hk', hkco, ?_⟩
  set k' : ↥K := K.normalizerMonoidHom ⟨x, hx⟩ k with hk'def
  have hπ : (QuotientGroup.mk k' : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k := by
    have h1 : i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K)) ⟨x, hx⟩
        (QuotientGroup.mk k) = QuotientGroup.mk k' := rfl
    rw [← h1, hk']
    exact hfix
  have hz : k'⁻¹ * k ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hπ
  set z : ↥K := k'⁻¹ * k with hzdef
  have hkk : k = k' * z := by rw [hzdef]; group
  have hord : orderOf k' = orderOf k := MulEquiv.orderOf_eq (K.normalizerMonoidHom ⟨x, hx⟩) k
  obtain ⟨n, hn⟩ := hZ ⟨z, hz⟩
  have hzn : z ^ (p ^ n) = 1 := congrArg Subtype.val hn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hzn)
  have hcop : Nat.Coprime (orderOf k') (orderOf z) := by
    rw [hj, hord]
    exact Nat.Coprime.pow_right j hkco
  have hcomm : Commute k' z := Subgroup.mem_center_iff.1 hz k'
  have hmul := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  rw [← hkk, hord] at hmul
  have hpos : 0 < orderOf k := orderOf_pos k
  have hz1 : orderOf z = 1 := by
    have : orderOf k * orderOf z = orderOf k * 1 := by rw [mul_one]; exact hmul.symm
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hzone : z = 1 := orderOf_eq_one_iff.1 hz1
  have hkeq : k' = k := by rw [hkk, hzone, mul_one]
  have := congrArg (fun w : ↥K => (w : X)) hkeq
  simpa [hk'def] using this

theorem caseA_of_pFixGen {p : ℕ} {K B : Subgroup X} (hH : I271Hyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hc : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (K : Set X)))
    (hF : PFixGen p (imgB B K)) : I271CaseA p K B := by
  have hp := hH.prime
  have hBel : IsElemAbelian p B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hperf : commutator ↥K = ⊤ := hq.1
  have hZ : IsPGroup p (Subgroup.center ↥K) :=
    i271h_center_isPGroup hp (i271h_primeCore_eq_bot hH.core hH.comp)
  refine ⟨hH.rank_four, i271h_isInGOne_of_le hBN ?_⟩
  obtain ⟨T, hTgen, hT⟩ := hF
  set Cb : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hCb
  have hCbel : IsElemAbelian p Cb := i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨c, hcard⟩ := i271_exists_card_eq hp hCbel
  have hc2 : 2 ≤ c := by rw [← i271_pRank_eq hp hCbel hcard]; exact hc
  set H' : Subgroup ↥K := (coreIn p 3 B K).subgroupOf K with hH'
  have claim1 : ∀ σ ∈ T, ∃ k : ↥K, k ∈ H' ∧
      (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = σ := by
    intro σ hσ
    obtain ⟨hco, f, hf, hf1, hfσ⟩ := hT σ hσ
    obtain ⟨x, hx, hxB, rfl⟩ := mem_imgB.1 hf
    obtain ⟨k, hk, hkco, hkx⟩ := exists_coprime_lift_centralized hp hZ hx hfσ hco
    refine ⟨k, ?_, hk⟩
    set Q : Subgroup X := Cb ⊔ Subgroup.zpowers x with hQ
    have hQB : Q ≤ B := sup_le inf_le_left ((Subgroup.zpowers_le).2 hxB)
    have hxCb : x ∉ Cb := by
      intro hxC
      apply hf1
      have hker : (⟨x, hx⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈
          (i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K))).ker := by
        rw [ker_i271Act hperf (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K))]
        exact Subgroup.mem_subgroupOf.2 hxC.2
      exact MonoidHom.mem_ker.1 hker
    have hQel : IsElemAbelian p Q := i271_isElemAbelian_of_le hBel hQB
    obtain ⟨j, hj⟩ := i271_exists_card_eq hp hQel
    have hCQ : Cb ≤ Q := le_sup_left
    have hxQ : x ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hcj : c ≤ j := by
      have := Subgroup.card_dvd_of_le hCQ
      rw [hcard, hj] at this
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 this
    have hcj' : c ≠ j := by
      intro hcj''
      apply hxCb
      have hle : Nat.card Q ≤ Nat.card Cb := by rw [hcard, hj, hcj'']
      rw [Subgroup.eq_of_le_of_card_ge hCQ hle]
      exact hxQ
    have hj3 : 3 ≤ j := by omega
    have hQrank : 3 ≤ CFSG.Open.pRank p Q := by rw [i271_pRank_eq hp hQel hj]; exact hj3
    have hkQ : (k : X) ∈ Subgroup.centralizer (Q : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq'
      have hQle : Q ≤ Subgroup.centralizer ({(k : X)} : Set X) := by
        refine sup_le (fun q hq'' => ?_) ((Subgroup.zpowers_le).2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hq''.2 (k : X) k.2).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have : x * (k : X) = (k : X) * x := by
            calc x * (k : X) = (x * (k : X) * x⁻¹) * x := by group
              _ = (k : X) * x := by rw [hkx]
          exact this
      exact Subgroup.mem_centralizer_singleton_iff.1 (hQle hq')
    have hS : Subgroup.zpowers (k : X) ≤ K ⊓ Subgroup.centralizer (Q : Set X) := by
      rw [Subgroup.zpowers_le]
      exact ⟨k.2, hkQ⟩
    have := i271h_le_coreIn_of_le_centralizer hQB hQrank hS (Subgroup.mem_zpowers (k : X))
    exact Subgroup.mem_subgroupOf.2 this
  have hmap : H'.map (QuotientGroup.mk' (Subgroup.center ↥K)) = ⊤ := by
    rw [eq_top_iff, ← hTgen, Subgroup.closure_le]
    intro σ hσ
    obtain ⟨k, hk, hkσ⟩ := claim1 σ hσ
    exact ⟨k, hk, hkσ⟩
  have hdec : ∀ g : ↥K, ∃ h ∈ H', ∃ z ∈ Subgroup.center ↥K, g = h * z := by
    intro g
    have hg : (QuotientGroup.mk' (Subgroup.center ↥K)) g ∈
        H'.map (QuotientGroup.mk' (Subgroup.center ↥K)) := hmap ▸ Subgroup.mem_top _
    obtain ⟨h, hh, hhg⟩ := hg
    refine ⟨h, hh, h⁻¹ * g, QuotientGroup.eq.1 hhg, by group⟩
  have hH'top : H' = ⊤ := eq_top_of_perfect_of_central hperf hdec
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ H' := hH'top ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 this

end Lift

theorem conclusion_of_planeKill {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X}
    (hH : I271Hyp p K B) (hN : I271Norm p K B)
    (hR : AutRankLe2 p (↥K ⧸ Subgroup.center ↥K)) (hP : PlaneKill p (↥K ⧸ Subgroup.center ↥K)) :
    I271CaseA p K B ∨ IsStronglyBalancedIn p B K := by
  have hp := hH.prime
  have hBel : IsElemAbelian p B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hperf : commutator ↥K = ⊤ := hq.1
  have hAel : IsElemAbelian p (imgB B K) := isElemAbelian_imgB hBel
  have hAcard : Nat.card (imgB B K) = autOrderIn B K := card_imgB hperf
  have hA2 : Nat.card (imgB B K) = p ^ 2 := le_antisymm (hR _ hAel) (hAcard ▸ hN.2)
  rcases hP _ hAel hA2 with hF | hS
  · refine Or.inl (caseA_of_pFixGen hH hN.1 ?_ hF)
    have h1 := pRank_le_centralizer_add hp hBel hN.1 (r := 2) (hAcard ▸ hA2.le)
    have h2 := hH.rank_four
    omega
  · exact Or.inr (isStronglyBalancedIn_of_noSig hperf hS)

end CFSG.HardMathSupport.Dickson.I271
