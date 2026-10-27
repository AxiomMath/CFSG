module

public import CFSG.CGT.PushingUpLit.T2K.FiveB

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_odd_of_isPGroup {K : Subgroup G} (hodd : Odd (Nat.card ↥K)) (hp : IsPGroup 2 ↥K) :
    K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hp
  have ha0 : a = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (by rw [ha]; exact Nat.even_pow.2 ⟨even_two, hne⟩)
  exact Subgroup.eq_bot_of_card_eq _ (by simpa [ha0] using ha)

omit [Finite G] in
theorem assembly_pCoreOf_eq_oTwoIn (M : Subgroup G) : CFSG.Assembly.pCoreOf 2 M = oTwoIn M := by
  unfold CFSG.Assembly.pCoreOf
  rfl

@[expose] def QOf (L M : Subgroup G) : Subgroup G := M ⊓ Subgroup.centralizer (blockU L : Set G)

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}

theorem centralizer_eq_bot (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hC : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := Subgroup.centralizer (L : Set G) with hX
  have hXM : X ≤ M := h.centralizer_le hE1
  have hXn : M ≤ Subgroup.normalizer (X : Set G) := h.le_normalizer_centralizer hE1
  have hodd : Odd (Nat.card ↥X) := by
    by_contra hnot
    have hev := Nat.not_odd_iff_even.1 hnot
    obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
    have hord : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
    have hu1 : (u : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      omega
    have hZ2 : IsPGroup 2 (Subgroup.zpowers (u : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
    obtain ⟨k, hk, hkB⟩ := exists_conj_le_of_isPGroup hT hZ2
      ((Subgroup.zpowers_le).2 (hXM u.2))
    have h1 : k * (u : G) * k⁻¹ ∈ T := hkB ⟨u, Subgroup.mem_zpowers _, by simp [MulAut.conj_apply]⟩
    have h2 : k * (u : G) * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hXn hk) u).1 u.2
    have h3 : k * (u : G) * k⁻¹ ∈ T ⊓ X := ⟨h1, h2⟩
    rw [hC, Subgroup.mem_bot] at h3
    apply hu1
    have e : (u : G) = k⁻¹ * (k * (u : G) * k⁻¹) * k := by group
    rw [e, h3]
    group
  have hcomm : ∀ x ∈ X, ∀ c ∈ oTwoIn M, x * c = c * x := by
    intro x hx c hc
    have hcM : c ∈ M := oTwoIn_le M hc
    have hxM : x ∈ M := hXM hx
    have h1 : x * c * x⁻¹ * c⁻¹ ∈ X ⊓ oTwoIn M := by
      refine ⟨?_, ?_⟩
      · have hcx : c * x⁻¹ * c⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hXn hcM) x⁻¹).1
          (X.inv_mem hx)
        have := X.mul_mem hx hcx
        simpa [mul_assoc] using this
      · have hxc : x * c * x⁻¹ ∈ oTwoIn M := conj_mem_oTwoIn (Subgroup.le_normalizer hxM) hc
        exact (oTwoIn M).mul_mem hxc ((oTwoIn M).inv_mem hc)
    have hbot : X ⊓ oTwoIn M = ⊥ := by
      refine eq_bot_of_odd_of_isPGroup ?_ ((isPGroup_oTwoIn M).to_le inf_le_right)
      exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : x * c * x⁻¹ = c := mul_inv_eq_one.1 h1
    calc x * c = (x * c * x⁻¹) * x := by group
      _ = c * x := by rw [h2]
  have hct := h.charTwo M (by
    obtain ⟨P, hP, hP2, hMP⟩ := h.maxLocal.1
    exact ⟨P, hP, hP2, hMP⟩)
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hxO : x ∈ oTwoIn M := by
    rw [← assembly_pCoreOf_eq_oTwoIn] at hcomm ⊢
    exact hct ⟨hXM hx, Subgroup.mem_centralizer_iff.2 fun c hc => (hcomm x hx c hc).symm⟩
  have hbot : X ⊓ oTwoIn M = ⊥ := by
    refine eq_bot_of_odd_of_isPGroup ?_ ((isPGroup_oTwoIn M).to_le inf_le_right)
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have : x ∈ X ⊓ oTwoIn M := ⟨hx, hxO⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

theorem isElemAbelian_Q (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) : IsElemAbelian 2 (QOf L M) := by
  have hMN := h.normal hE1
  refine isElemAbelian_of_forall' (fun x hx y hy => ?_) (fun x hx => ?_)
  · have := h.natBlock.comm_mem_centralizer hMN hx hy
    rw [hC, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · have := h.natBlock.sq_mem_centralizer hMN hx
    rw [hC, Subgroup.mem_bot] at this
    exact this

theorem le_normalizer_Q (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple) :
    M ≤ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
  intro m hm
  have hV : m ∈ Subgroup.normalizer (blockU L : Set G) :=
    NatBlock.le_normalizer_blockU_of_le (h.normal hE1) hm
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hm,
    mem_normalizer_centralizer hV⟩

theorem Q_le_T (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hC : Subgroup.centralizer (L : Set G) = ⊥) :
    QOf L M ≤ T := by
  have hQ := h.isElemAbelian_Q hE1 hC
  exact le_of_isPGroup_normal hT inf_le_left (h.le_normalizer_Q hE1)
    (fun g => ⟨1, Subtype.ext (by simpa using hQ.2 g g.2)⟩)

theorem inf_centralizer_blockU_eq_Q (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hC : Subgroup.centralizer (L : Set G) = ⊥) :
    T ⊓ Subgroup.centralizer (blockU L : Set G) = QOf L M :=
  le_antisymm (fun _ hx => ⟨hT.le hx.1, hx.2⟩) (le_inf (h.Q_le_T hE1 hT hC) inf_le_right)

theorem blockU_le_Q (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : blockU L ≤ QOf L M :=
  le_inf (NatBlock.blockU_le_sylow h.le (h.normal hE1) hT |>.trans hT.le) fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun w hw => h.natBlock.blockU_comm w hw v hv

theorem normalizer_Q_eq (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hC : Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) = M := by
  by_contra hne
  have hQne : QOf L M ≠ ⊥ := fun h0 =>
    h.blockU_ne_bot (le_bot_iff.1 (h0 ▸ h.blockU_le_Q hE1 hT))
  exact h.maxLocal.2 _ (lt_of_le_of_ne (h.le_normalizer_Q hE1) (Ne.symm hne))
    ⟨QOf L M, hQne, fun g => ⟨1, Subtype.ext (by
      simpa using (h.isElemAbelian_Q hE1 hC).2 g g.2)⟩, rfl⟩

theorem isMaxElemAbelian_Q (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hC : Subgroup.centralizer (L : Set G) = ⊥) :
    IsMaxElemAbelian T (QOf L M) := by
  obtain ⟨A, hA, hAP⟩ := h.exists_max_le_P hE1 hT
  have hAQ : A ≤ QOf L M := fun a ha => ⟨hT.le (hAP ha).1, (hAP ha).2⟩
  have heq : A = QOf L M :=
    Subgroup.eq_of_le_of_card_ge hAQ (hA.2.2 _ (h.Q_le_T hE1 hT hC) (h.isElemAbelian_Q hE1 hC))
  exact heq ▸ hA

omit [Finite G] in
theorem mem_normalizer_conj_iff {Q : Subgroup G} {g t : G} :
    g⁻¹ * t * g ∈ Subgroup.normalizer (Q : Set G) ↔
      t ∈ Subgroup.normalizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hq x
    have h1 := hq (g⁻¹ * x * g)
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have e : g⁻¹ * x * g = g⁻¹ * x * g := rfl
    have e2 : g⁻¹ * (t * x * t⁻¹) * g = (g⁻¹ * t * g) * (g⁻¹ * x * g) * (g⁻¹ * t * g)⁻¹ := by
      group
    rw [e2]
    exact h1
  · intro hq x
    have h1 := hq (g * x * g⁻¹)
    rw [mem_map_conj_iff, mem_map_conj_iff] at h1
    have e1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    have e2 : g⁻¹ * (t * (g * x * g⁻¹) * t⁻¹) * g = (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1

theorem Q_weakly_closed (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hC : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {g : G}
    (hg : (QOf L M).map (MulAut.conj g).toMonoidHom ≤ T) :
    (QOf L M).map (MulAut.conj g).toMonoidHom = QOf L M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hs.hyp
  have hT := hs.sylow
  have hCG := h.centralizer_eq_bot hE1 hT hC
  by_contra hne
  have hQ : IsElemAbelian 2 (QOf L M) := h.isElemAbelian_Q hE1 hCG
  have hQmax := h.isMaxElemAbelian_Q hE1 hT hCG
  have hPQ := h.inf_centralizer_blockU_eq_Q hE1 hT hCG
  have hQT := h.Q_le_T hE1 hT hCG
  have hMQ := h.normalizer_Q_eq hE1 hT hCG
  set A : Subgroup G := (QOf L M).map (MulAut.conj g).toMonoidHom with hAdef
  have hAmax : IsMaxElemAbelian T A :=
    ⟨hg, isElemAbelian_map_conj hQ g, fun B hBT hBe => by
      rw [hAdef, card_map_conj]
      exact hQmax.2.2 B hBT hBe⟩
  have hnot : ¬ A ≤ Subgroup.centralizer (blockU L : Set G) := by
    intro hle
    apply hne
    have hle' : A ≤ QOf L M := hPQ ▸ le_inf hg hle
    exact Subgroup.eq_of_le_of_card_ge hle' (by rw [hAdef, card_map_conj])
  have H : Hyp45 L M T A n := ⟨h.natBlock, h.le, h.normal hE1, hT, hAmax, hnot⟩
  have hZ : blockZ L = ⊥ :=
    eq_bot_iff.2 ((inf_le_right : blockZ L ≤ Subgroup.centralizer (L : Set G)).trans hCG.le)
  have hBle : Hyp45.bGrp L A ≤ QOf L M := hPQ ▸ H.B_le_P
  have hBeq : Hyp45.bGrp L A = QOf L M :=
    Subgroup.eq_of_le_of_card_ge hBle (H.isMaxElemAbelian_B.2.2 _ hQT hQ)
  have hBV : Hyp45.bGrp L A = blockU L := by rw [H.bGrp_eq_sup_S hs.S_elem, hC, bot_sup_eq]
  have hQV : QOf L M = blockU L := hBeq.symm.trans hBV
  have hOV : oTwoIn L = blockU L := by
    have hle : oTwoIn L ≤ QOf L M := by
      intro x hx
      have hxL : x ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := by
        rw [h.natBlock.inf_centralizer_blockU]
        exact hx
      exact ⟨h.le hxL.1, hxL.2⟩
    exact le_antisymm (hQV ▸ hle) (blockU_le_oTwoIn L)
  rcases H.four_five_six hZ hs.S_elem with ⟨-, -, hA'⟩ | ⟨hO', -, -⟩
  swap
  · exact hO' hOV
  have hTA : T ≤ Subgroup.normalizer (A : Set G) := by
    intro t ht
    have hmax' := isMaxElemAbelian_map_conj hAmax (Subgroup.le_normalizer ht)
    have hnot' : ¬ A.map (MulAut.conj t).toMonoidHom ≤ Subgroup.centralizer (blockU L : Set G) := by
      intro hle
      apply hnot
      intro x hx
      have hV : t ∈ Subgroup.normalizer (blockU L : Set G) :=
        NatBlock.le_normalizer_blockU_of_le (h.normal hE1) (hT.le ht)
      have hC' : t⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer (blockU L : Set G) : Set G) :=
        mem_normalizer_centralizer ((Subgroup.normalizer (blockU L : Set G)).inv_mem hV)
      have hx' : t * x * t⁻¹ ∈ Subgroup.centralizer (blockU L : Set G) :=
        hle ⟨x, hx, by simp [MulAut.conj_apply]⟩
      have := (Subgroup.mem_normalizer_iff.1 hC' (t * x * t⁻¹)).1 hx'
      simpa [mul_assoc] using this
    exact mem_normalizer_of_map_conj_eq (hA' _ hmax' hnot')
  have hTg : ∀ t ∈ T, g⁻¹ * t * g ∈ M := by
    intro t ht
    rw [← hMQ]
    exact mem_normalizer_conj_iff.2 (hTA ht)
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (T.map (MulAut.conj g⁻¹).toMonoidHom) M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      have := hTg t ht
      simpa [MulAut.conj_apply, mul_assoc] using this
    · rw [card_map_conj, hT.card_eq]
  obtain ⟨k, hk, hconj⟩ := hT.exists_mem_conj hT'
  have hgk : (g * k)⁻¹ ∈ Subgroup.normalizer (T : Set G) := by
    apply mem_normalizer_of_map_conj_eq
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_map_conj])
    rintro _ ⟨t, ht, rfl⟩
    have h1 : g⁻¹ * t * g ∈ T.map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨t, ht, by simp⟩
    have h2 := (hconj (g⁻¹ * t * g)).1 h1
    simpa [MulAut.conj_apply, mul_assoc] using h2
  have hgkN : g * k ∈ Subgroup.normalizer (T : Set G) := by
    simpa using (Subgroup.normalizer (T : Set G)).inv_mem hgk
  have hgM : g ∈ M := by
    have := M.mul_mem (hs.N_T hgkN) (M.inv_mem hk)
    simpa using this
  exact hne (map_conj_eq_of_mem_normalizer (h.le_normalizer_Q hE1 hgM))

theorem Q_eq_oTwoIn (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple)
    (hC : Subgroup.centralizer (L : Set G) = ⊥) : QOf L M = oTwoIn M := by
  apply le_antisymm
  · exact SixThree.le_oTwoIn_of_isPGroup inf_le_left
      (fun g => ⟨1, Subtype.ext (by simpa using (h.isElemAbelian_Q hE1 hC).2 g g.2)⟩)
      (h.le_normalizer_Q hE1)
  · refine le_inf (oTwoIn_le M) ?_
    refine h.natBlock.le_centralizer_of_two_quot h.le (h.normal hE1) (oTwoIn_le M)
      (SixThree.le_normalizer_oTwoIn M) fun x hx => ?_
    obtain ⟨k, hk⟩ := isPGroup_oTwoIn M ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [this]
    exact Subgroup.one_mem _

end T2Hyp

structure Sec6 (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) : Prop where
  sec4 : Sec4 G L M T n
  C_T : T ⊓ Subgroup.centralizer (L : Set G) = ⊥
  C_G : Subgroup.centralizer (L : Set G) = ⊥
  Q_abelian : IsElemAbelian 2 (QOf L M)
  Q_eq_oTwo : QOf L M = oTwoIn M
  Q_le_T : QOf L M ≤ T
  P_eq_Q : T ⊓ Subgroup.centralizer (blockU L : Set G) = QOf L M
  N_Q : Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) = M
  Q_max : IsMaxElemAbelian T (QOf L M)
  Q_wc : ∀ g : G, (QOf L M).map (MulAut.conj g).toMonoidHom ≤ T →
    (QOf L M).map (MulAut.conj g).toMonoidHom = QOf L M

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}

theorem sec6 (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hC : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Sec6 G L M T n := by
  have h := hs.hyp
  have hT := hs.sylow
  have hCG := h.centralizer_eq_bot hE1 hT hC
  exact ⟨hs, hC, hCG, h.isElemAbelian_Q hE1 hCG, h.Q_eq_oTwoIn hE1 hCG, h.Q_le_T hE1 hT hCG,
    h.inf_centralizer_blockU_eq_Q hE1 hT hCG, h.normalizer_Q_eq hE1 hT hCG,
    h.isMaxElemAbelian_Q hE1 hT hCG, fun _ hg => Q_weakly_closed hs hE1 hC hg⟩

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
