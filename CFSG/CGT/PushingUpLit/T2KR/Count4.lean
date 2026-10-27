module

public import CFSG.CGT.PushingUpLit.T2KR.Count3

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_zpowers_eq (a : G) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact h a (Subgroup.mem_zpowers a)
  · intro h x hx
    obtain ⟨k, rfl⟩ := hx
    exact Commute.zpow_left (h a (Set.mem_singleton a)) k

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem card_CV_involution {b : ↥M} (hb : b * b = 1) (hχ : H.chi b ≠ 1) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({(b : G)} : Set G)) = Nat.card (Fq n) := by
  rw [← centralizer_zpowers_eq, H.card_CV (Subgroup.zpowers (b : G)) ((Subgroup.zpowers_le).2 b.2),
    ← H.card_fixed_actHom hb hχ]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  constructor
  · intro h
    exact h b (Subgroup.mem_zpowers _)
  · intro h x hx
    obtain ⟨k, rfl⟩ := hx
    have hmem : H.actHom b ∈ MulAction.stabilizer (Equiv.Perm (Fin 2 → Fq n)) w := h
    have := Subgroup.zpow_mem _ hmem k
    have e : (⟨(b : G) ^ k, M.zpow_mem b.2 k⟩ : ↥M) = b ^ k := Subtype.ext (by simp)
    rw [e, map_zpow]
    exact this

include H in
theorem commutator_inv_mem {a : G} (ha : a ∈ M) (ha2 : a * a = 1) {u : G} (hu : u ∈ QM L M) :
    ⁅u, a⁆ ∈ QM L M ∧ a * ⁅u, a⁆ = ⁅u, a⁆ * a := by
  have hQ : ∀ x ∈ QM L M, a * x * a⁻¹ ∈ QM L M := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (NatBlock.le_normalizer_centralizer H.normal ha) x).1 hx
  have hmem : ⁅u, a⁆ ∈ QM L M := by
    have e : ⁅u, a⁆ = u * (a * u⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hu (hQ _ (inv_mem hu))
  refine ⟨hmem, ?_⟩
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hsq : ⁅u, a⁆ * ⁅u, a⁆ = 1 := H.Q_sq _ hmem
  have h1 : a * ⁅u, a⁆ * a⁻¹ = ⁅u, a⁆⁻¹ := by
    have e1 : a * ⁅u, a⁆ * a⁻¹ = a * u * a * u⁻¹ * (a⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅u, a⁆⁻¹ = a * u * a⁻¹ * u⁻¹ := by simp only [commutatorElement_def]; group
    rw [e1, e2, hai, ha2, mul_one]
  have h2 : ⁅u, a⁆⁻¹ = ⁅u, a⁆ := inv_eq_of_mul_eq_one_right hsq
  rw [h2] at h1
  calc a * ⁅u, a⁆ = (a * ⁅u, a⁆ * a⁻¹) * a := by group
    _ = ⁅u, a⁆ * a := by rw [h1]

end MData

namespace PairFacts

variable {L M : Subgroup G} {n : ℕ} {H : MData G L M n} {P B D : Subgroup G}

theorem step610 (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M) :
    D.relIndex (B ⊓ (L ⊔ QM L M)) = 2 ∧ D.relIndex B = 4 ∧ n = 2 := by
  classical
  set E : Subgroup G := B ⊓ (L ⊔ QM L M) with hE
  have hEB : E ≤ B := inf_le_left
  have hQLQ : QM L M ≤ L ⊔ QM L M := le_sup_right
  have hDE : D ≤ E := le_inf hP.D_le_B (hP.D_le_Q.trans hQLQ)
  have hVQ : blockU L ≤ QM L M := H.blockU_le_QM
  have hq4 := four_le_card H
  have hBE : E.relIndex B = 2 := hP.relIndex_E hBLQ
  have h69 : D.relIndex E ≤ 2 := hP.step69 hBLQ
  have hposDE := relIndex_pos' D E
  have hDB : D.relIndex B = D.relIndex E * 2 := by
    rw [← hBE]
    exact (Subgroup.relIndex_mul_relIndex D E B hDE hEB).symm
  have hPQ := hP.step67 hBLQ
  have hDPB : D.relIndex P = D.relIndex B := by
    have h1 := relIndex_mul_card_of_le hP.D_le_P
    have h2 := relIndex_mul_card_of_le hP.D_le_B
    rw [hP.card_PB, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hDE2 : D.relIndex E = 2 := by
    by_contra hne
    have h1 : D.relIndex E = 1 := by omega
    have hED : E ≤ D := Subgroup.relIndex_eq_one.1 h1
    obtain ⟨a, haB, hax⟩ := Subgroup.relIndex_dvd_two_iff.1 (by rw [hBE] : E.relIndex B ∣ 2)
    have haE : a ∉ E := by
      intro haE
      have hBE' : B ≤ E := fun x hx => (hax x hx).elim (fun h => by
        have := E.mul_mem h (E.inv_mem haE)
        simpa using this) id
      have := Subgroup.relIndex_eq_one.2 hBE'
      omega
    have haLQ : a ∉ L ⊔ QM L M := fun h => haE ⟨haB, h⟩
    have haM : a ∈ M := hP.B_le_M haB
    have ha2 : a * a = 1 := hP.B_sq a haB
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have haχ := hP.chi_ne_one haB haLQ
    have hb2 : (⟨a, haM⟩ : ↥M) * ⟨a, haM⟩ = 1 := Subtype.ext ha2
    set Ca : Subgroup G := QM L M ⊓ Subgroup.centralizer ({a} : Set G) with hCa
    have hDCa : D ≤ Ca := fun d hd =>
      ⟨hP.D_le_Q hd, Subgroup.mem_centralizer_iff.2 fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hP.B_comm a haB d (hP.D_le_B hd)⟩
    have hcomm : ⁅QM L M, B⁆ ≤ Ca := by
      rw [Subgroup.commutator_le]
      intro u hu x hx
      obtain ⟨hua, hca⟩ := H.commutator_inv_mem haM ha2 hu
      have hCaa : ⁅u, a⁆ ∈ Ca := ⟨hua, Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hca⟩
      rcases hax x hx with h | h
      · have hd : x * a ∈ D := hED h
        obtain ⟨d, hdD, hxd⟩ : ∃ d ∈ D, x = d * a := ⟨x * a, hd, by rw [mul_assoc, ha2, mul_one]⟩
        have hdQ : d ∈ QM L M := hP.D_le_Q hdD
        have hc1 : u * d = d * u := H.Q_comm u hu d hdQ
        have hc2 : d * ⁅u, a⁆ = ⁅u, a⁆ * d := H.Q_comm d hdQ _ hua
        have e : ⁅u, x⁆ = ⁅u, a⁆ := by
          rw [hxd]
          calc ⁅u, d * a⁆ = (u * d) * (a * u⁻¹ * a⁻¹) * d⁻¹ := by
                simp only [commutatorElement_def]
                group
            _ = (d * u) * (a * u⁻¹ * a⁻¹) * d⁻¹ := by rw [hc1]
            _ = d * ⁅u, a⁆ * d⁻¹ := by
                simp only [commutatorElement_def]
                group
            _ = ⁅u, a⁆ * d * d⁻¹ := by rw [hc2]
            _ = ⁅u, a⁆ := by group
        rw [e]
        exact hCaa
      · have hxD : x ∈ D := hED h
        have : ⁅u, x⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 (H.Q_comm u hu x (hP.D_le_Q hxD))
        rw [this]
        exact Ca.one_mem
    have hPCa : P ≤ Ca := hP.P_le_comm.trans (sup_le hcomm hDCa)
    have hCV : Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({a} : Set G)) = Nat.card (Fq n) :=
      H.card_CV_involution (b := ⟨a, haM⟩) hb2 haχ
    have hCaV : Ca ⊓ blockU L = blockU L ⊓ Subgroup.centralizer ({a} : Set G) := by
      ext x
      constructor
      · rintro ⟨⟨_, hxc⟩, hxV⟩
        exact ⟨hxV, hxc⟩
      · rintro ⟨hxV, hxc⟩
        exact ⟨⟨hVQ hxV, hxc⟩, hxV⟩
    have hq0 : 0 < Nat.card (Fq n) := Nat.card_pos
    have hrelV : Ca.relIndex (blockU L) = Nat.card (Fq n) := by
      rw [← Subgroup.inf_relIndex_right Ca (blockU L), hCaV]
      have h := relIndex_mul_card_of_le
        (inf_le_left : blockU L ⊓ Subgroup.centralizer ({a} : Set G) ≤ blockU L)
      rw [hCV, H.card_V] at h
      exact Nat.eq_of_mul_eq_mul_right hq0 (h.trans (sq _))
    have hle1 : Ca.relIndex (blockU L) ≤ Ca.relIndex (QM L M) :=
      Subgroup.relIndex_le_of_le_right hVQ (relIndex_pos' Ca (QM L M)).ne'
    have hle2 : Ca.relIndex (QM L M) ∣ P.relIndex (QM L M) :=
      Subgroup.relIndex_dvd_of_le_left (QM L M) hPCa
    have hle3 : Ca.relIndex (QM L M) ≤ 2 := by
      have := Nat.le_of_dvd (by omega) hle2
      omega
    omega
  refine ⟨hDE2, by omega, ?_⟩
  have hD4 : D.relIndex B = 4 := by omega
  have hDQ : D.relIndex (QM L M) = 8 := by
    rw [← Subgroup.relIndex_mul_relIndex D P (QM L M) hP.D_le_P hP.P_le_Q, hDPB, hD4, hPQ]
  obtain ⟨b, hbB, hbn⟩ := IsConcreteLE.not_le_iff_exists.1 hBLQ
  have hbM : b ∈ M := hP.B_le_M hbB
  have hb2 : (⟨b, hbM⟩ : ↥M) * ⟨b, hbM⟩ = 1 := Subtype.ext (hP.B_sq b hbB)
  have hCV : Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({b} : Set G)) = Nat.card (Fq n) :=
    H.card_CV_involution (b := ⟨b, hbM⟩) hb2 (hP.chi_ne_one hbB hbn)
  have hDV : D ⊓ blockU L ≤ blockU L ⊓ Subgroup.centralizer ({b} : Set G) := by
    rintro d ⟨hdD, hdV⟩
    refine ⟨hdV, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hP.B_comm b hbB d (hP.D_le_B hdD)
  have hcardDV : Nat.card ↥(D ⊓ blockU L) ≤ Nat.card (Fq n) :=
    (Subgroup.card_le_of_le hDV).trans hCV.le
  have hrelDV : D.relIndex (blockU L) ≤ 8 := by
    rw [← hDQ]
    exact Subgroup.relIndex_le_of_le_right H.blockU_le_QM (relIndex_pos' D (QM L M)).ne'
  have hVcard := Subgroup.relIndex_mul_card D (blockU L)
  rw [H.card_V] at hVcard
  have hq8 : Nat.card (Fq n) ≤ 8 := by
    have h1 : Nat.card (Fq n) ^ 2 ≤ 8 * Nat.card (Fq n) := by
      calc Nat.card (Fq n) ^ 2 = D.relIndex (blockU L) * Nat.card ↥(D ⊓ blockU L) := hVcard.symm
        _ ≤ 8 * Nat.card (Fq n) := Nat.mul_le_mul hrelDV hcardDV
    nlinarith
  have hev := hP.even_n hBLQ
  have hn2 := H.nat.two_le
  rw [GaloisField.card 2 n H.n_ne_zero] at hq8
  have : n ≤ 3 := by
    by_contra h4
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, hk⟩ := hev
  omega

theorem step611 (hP : PairFacts H P B D) (hBLQ : ¬ B ≤ L ⊔ QM L M) :
    Nat.card ↥(D ⊓ blockU L) = 2 ∧ D.relIndex (blockU L) = 8 ∧
      (Nat.card D = 2 ∨ Nat.card D = 4) := by
  classical
  obtain ⟨hDE2, hD4, hn⟩ := hP.step610 hBLQ
  set E : Subgroup G := B ⊓ (L ⊔ QM L M) with hE
  have hEB : E ≤ B := inf_le_left
  have hEL : E ≤ L ⊔ QM L M := inf_le_right
  have hQLQ : QM L M ≤ L ⊔ QM L M := le_sup_right
  have hDE : D ≤ E := le_inf hP.D_le_B (hP.D_le_Q.trans hQLQ)
  have hVQ : blockU L ≤ QM L M := H.blockU_le_QM
  have hq : Nat.card (Fq n) = 4 := by
    rw [GaloisField.card 2 n H.n_ne_zero, hn]
    norm_num
  have hPQ := hP.step67 hBLQ
  have hDPB : D.relIndex P = D.relIndex B := by
    have h1 := relIndex_mul_card_of_le hP.D_le_P
    have h2 := relIndex_mul_card_of_le hP.D_le_B
    rw [hP.card_PB, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hDQ : D.relIndex (QM L M) = 8 := by
    rw [← Subgroup.relIndex_mul_relIndex D P (QM L M) hP.D_le_P hP.P_le_Q, hDPB, hD4, hPQ]
  obtain ⟨b, hbB, hbn⟩ := IsConcreteLE.not_le_iff_exists.1 hBLQ
  have hbM : b ∈ M := hP.B_le_M hbB
  have hb2 : (⟨b, hbM⟩ : ↥M) * ⟨b, hbM⟩ = 1 := Subtype.ext (hP.B_sq b hbB)
  have hbχ := hP.chi_ne_one hbB hbn
  obtain ⟨e, heE, heD⟩ : ∃ e ∈ E, e ∉ D := by
    by_contra hcon
    push Not at hcon
    have : E ≤ D := hcon
    have := Subgroup.relIndex_eq_one.2 this
    omega
  have heB : e ∈ B := hEB heE
  have heQ : e ∉ QM L M := fun h => heD (by rw [← hP.B_inf_Q]; exact ⟨heB, h⟩)
  have hbe : b * e = e * b := hP.B_comm b hbB e heB
  have hD2 : ∀ d ∈ D, d ∈ QM L M ∧ (b * d = d * b) ∧ (e * d = d * e) := fun d hd =>
    ⟨hP.D_le_Q hd, hP.B_comm b hbB d (hP.D_le_B hd), hP.B_comm e heB d (hP.D_le_B hd)⟩
  have hDC : D ≤ QM L M ⊓ Subgroup.centralizer ({b, e} : Set G) := fun d hd =>
    ⟨(hD2 d hd).1, Subgroup.mem_centralizer_iff.2 fun x hx => by
      rcases hx with rfl | hx
      · exact (hD2 d hd).2.1
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (hD2 d hd).2.2⟩
  have hQcard := H.card_centralizer_QM_pair_le hb2 hbχ (hEL heE) (hP.B_sq e heB) heQ hbe
  have hDle : Nat.card D ≤ 4 := (Subgroup.card_le_of_le hDC).trans (hq ▸ hQcard)
  have hVC := H.card_CV_pair_le hb2 hbχ (hEL heE) (hP.B_sq e heB) heQ hbe
  have hDV : D ⊓ blockU L ≤ blockU L ⊓ Subgroup.centralizer ({b, e} : Set G) := fun d hd =>
    ⟨hd.2, (hDC hd.1).2⟩
  have hDVle : Nat.card ↥(D ⊓ blockU L) ≤ 2 := by
    have := (Subgroup.card_le_of_le hDV)
    rw [hq] at hVC
    nlinarith
  have hVcard := Subgroup.relIndex_mul_card D (blockU L)
  rw [H.card_V, hq] at hVcard
  have hrelDV : D.relIndex (blockU L) ≤ 8 := by
    rw [← hDQ]
    exact Subgroup.relIndex_le_of_le_right hVQ (relIndex_pos' D (QM L M)).ne'
  have hDVpos : 0 < Nat.card ↥(D ⊓ blockU L) := Nat.card_pos
  have hrelpos := relIndex_pos' D (blockU L)
  have hDV2 : Nat.card ↥(D ⊓ blockU L) = 2 := by nlinarith
  have hrel8 : D.relIndex (blockU L) = 8 := by nlinarith
  refine ⟨hDV2, hrel8, ?_⟩
  have hDp : IsPGroup 2 D := fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hP.B_sq x (hP.D_le_B x.2)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hDp
  have hQcard : Nat.card (QM L M) = 8 * Nat.card D := by
    have := relIndex_mul_card_of_le hP.D_le_Q
    rw [hDQ] at this
    exact this.symm
  have hVQcard : Nat.card ↥(blockU L) ≤ Nat.card (QM L M) := Subgroup.card_le_of_le hVQ
  rw [H.card_V, hq, hQcard] at hVQcard
  have hk2 : 2 ≤ 2 ^ k := hk ▸ (by omega : 2 ≤ Nat.card D)
  have hk4 : 2 ^ k ≤ 4 := hk ▸ hDle
  have : k ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · omega
  · left; omega
  · right; omega

end PairFacts

end CFSG.CGT.PushingUpLit.T2KR
