module

public import CFSG.GH74.GLS.C3.Layer1.BkIvk73G
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Apply
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Q

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

section Final

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

theorem ivk_7_3_A57_core_of_hord
    {G : Type} [Group G] [Finite G] (h73 : IVK.IVK_7_3_g4)
    (hks : IsKProperSimple G) (hgen : Gen4 G) (hgh : KGH G)
    {n : ℕ} (hn : n = 5 ∨ n = 7) {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) (haN : a ∈ NW x)
    (hW : pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥)
    (hord : n = 5 → ∀ R : Subgroup (NWbar x), IsPGroup 2 ↥R → Nat.card ↥R ≤ 2 ^ 6)
    (hns5 : n = 5 → ¬ CFSG.IsComponent (toNWbar x K)) :
    ∃ e0 : NWbar x ≃* alternatingGroup (Fin (n + 4)),
      (toNWbar x K).map e0.toMonoidHom = stdAlt n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNtop : NW x ≠ ⊤ := NW_ne_top hks h hW
  have hKN : K ≤ NW x := h.K_le_C.trans (centralizer_le_NW x)
  have hQN : Q ≤ NW x := (h.Q_le_T.trans h.T_le_C).trans (centralizer_le_NW x)
  have hxN : x ∈ NW x := centralizer_le_NW x (mem_centralizer_singleton_iff.2 rfl)
  have hQS : IsSylowOf 2 Q (centralizer (K : Set G)) := isSylowOf_Q_centralizer hn h
  have hKq : IsQuasisimple ↥K := isQuasisimple_of_isCompIn' h.terminal.2.1
  have hQ2 : IsPGroup 2 ↥Q := h.sylowQ.isPGroup
  have hKqn : IsQuasisimple ↥(K.subgroupOf (NW x)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKN).symm hKq
  have hOK := mem_pPrimeCore_of_le hKN (pPrimeCoreOf_le_NW h)
  obtain ⟨eb0⟩ := equiv_map_piO hOK
  obtain ⟨ekbar⟩ := h.kbar
  let ψ : ↥(K.subgroupOf (NW x)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKN
  let e2 : (↥(K.subgroupOf (NW x)) ⧸ pPrimeCore 2 ↥(K.subgroupOf (NW x))) ≃*
      (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)
  let eKhat : ↥(toNWbar x K) ≃* alternatingGroup (Fin n) := (eb0.trans e2).trans ekbar
  have hKnc := exists_noncomm_map_of_equiv hn eKhat
  have hQab : ∀ q ∈ Q.subgroupOf (NW x), ∀ q' ∈ Q.subgroupOf (NW x), q * q' = q' * q := by
    intro q hq q' hq'
    have := h.elemQ
    exact Subtype.ext (congrArg (fun z : ↥Q => (z : G))
      ((IsMulCommutative.is_comm (M := ↥Q)).comm ⟨(q : G), hq⟩ ⟨(q' : G), hq'⟩))
  have hQne : Q.subgroupOf (NW x) ≠ ⊥ := by
    intro h0
    have h1 : (⟨x, hxN⟩ : ↥(NW x)) ∈ Q.subgroupOf (NW x) := h.x_mem_Q
    rw [h0, Subgroup.mem_bot] at h1
    have h2 : x = 1 := congrArg Subtype.val h1
    have h3 := h.x_order
    rw [h2, orderOf_one] at h3
    omega
  have hQle : Q ≤ centralizer (K : Set G) ⊓ NW x := le_inf hQS.le hQN
  have hQSn : IsSylowOf 2 (Q.subgroupOf (NW x)) (centralizer ((K.subgroupOf (NW x) : Subgroup ↥(NW x)) :
      Set ↥(NW x))) := by
    rw [centralizer_subgroupOf_eq hKN]
    exact isSylowOf_subgroupOf_of_le hQle inf_le_right (hQS.of_le hQle inf_le_left)
  have htermn : ∀ u ∈ Q.subgroupOf (NW x), orderOf u = 2 →
      IsPCompIn 2 (centralizer ({u} : Set ↥(NW x))) (K.subgroupOf (NW x)) := by
    intro u hu hu2
    have huG : (u : G) ∈ Q := hu
    have hu2G : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
    have hcomp := h.terminal.2.2.2 (u : G) hu2G (hQS.le huG)
    exact isPCompIn_subgroupOf_centralizer u.2 hKN
      (isPCompIn_two_of_isCompIn_of_even hcomp h.terminal.2.2.1)
  have hSylY := isSylowOf_centralizer_map hKqn hKnc hQab hQne hQSn htermn
  have hQ2n : IsPGroup 2 ↥(Q.subgroupOf (NW x)) := hQ2.comap_subtype
  have hQel_hat : IsElementaryAbelian 2 ↥((Q.subgroupOf (NW x)).map (piO ↥(NW x))) := by
    have := h.elemQ
    have : IsElementaryAbelian 2 ↥(Q.subgroupOf (NW x)) := IsElementaryAbelian.subgroupOf hQN
    exact IsElementaryAbelian.map (piO ↥(NW x))
  have hQcard_hat : Nat.card ↥((Q.subgroupOf (NW x)).map (piO ↥(NW x))) = 4 := by
    rw [CFSG.ComponentClassification.GSThmB.OddQuot.card_map_of_isPGroup hQ2n,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]
    exact h.card_Q
  have hKhat_q : IsQuasisimple ↥(toNWbar x K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eKhat.symm (isQuasisimple_alt hn)
  have htermY : ∀ û ∈ (Q.subgroupOf (NW x)).map (piO ↥(NW x)), orderOf û = 2 →
      IsCompIn (centralizer ({û} : Set (NWbar x))) (toNWbar x K) := by
    rintro _ ⟨u, hu, rfl⟩ hû2
    have hu2 : orderOf u = 2 := by
      have hsq : (piO ↥(NW x) u) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (piO ↥(NW x) u)
        rwa [hû2] at this
      have h1 : u ^ 2 = 1 := by
        have h2 : piO ↥(NW x) (u ^ 2) = piO ↥(NW x) 1 := by rw [map_pow, hsq, map_one]
        exact CFSG.ComponentClassification.GSThmB.OddQuot.injOn_of_isPGroup hQ2n
          (Subgroup.pow_mem _ hu 2) (Subgroup.one_mem _) h2
      refine orderOf_eq_prime h1 ?_
      intro hu1
      rw [hu1, map_one, orderOf_one] at hû2
      omega
    have hK2n := htermn u hu hu2
    have hmap := CFSG.ComponentClassification.UGSChain.map_twoComponent_centralizer_quotient hu2
      hK2n.1 hK2n.2
    exact isCompIn_of_isPCompIn_of_quasisimple ⟨hmap.1, hmap.2⟩ hKhat_q
  have hNK : IsKGroupNative ↥(NW x) := hks.isKGroupNative_of_ne_top hNtop
  have hY : IsKGroupNative (NWbar x) :=
    isKGroupNative_of_surjective hNK ⊤
      ((QuotientGroup.mk' (pPrimeCore 2 ↥(NW x))).comp (⊤ : Subgroup ↥(NW x)).subtype)
      ((QuotientGroup.mk'_surjective _).comp fun m => ⟨⟨m, trivial⟩, rfl⟩)
  have hO : pPrimeCore 2 (NWbar x) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥(NW x)) 2
  have hns : ¬ CFSG.IsComponent (toNWbar x K) := by
    obtain h5 | h7 := id hn
    · exact hns5 h5
    · subst h7
      intro hcomp
      have hsA : IsSimpleGroup (alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hncA : ∃ a b : ↥(alternatingGroup (Fin 7)), a * b ≠ b * a := by
        by_contra hc
        push Not at hc
        exact alt_not_isSolvable 7 hn
          ((IsSimpleGroup.comm_iff_isSolvable (G := ↥(alternatingGroup (Fin 7)))).1 hc)
      have hcenA : center (alternatingGroup (Fin 7)) = ⊥ :=
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncA).2
      have hZ : ∀ y ∈ toNWbar x K, (∀ k ∈ toNWbar x K, k * y = y * k) → y = 1 := by
        intro y hy hyc
        have hmem : eKhat ⟨y, hy⟩ ∈ center (alternatingGroup (Fin 7)) := by
          rw [Subgroup.mem_center_iff]
          intro b
          obtain ⟨k, rfl⟩ := eKhat.surjective b
          rw [← map_mul, ← map_mul]
          exact congrArg eKhat (Subtype.ext (hyc k.1 k.2))
        rw [hcenA, Subgroup.mem_bot] at hmem
        have h1 : (⟨y, hy⟩ : ↥(toNWbar x K)) = 1 := eKhat.injective (by rw [hmem, map_one])
        exact congrArg Subtype.val h1
      have h8 : 2 ^ 3 ∣ Nat.card ↥(toNWbar x K) := by
        rw [Nat.card_congr eKhat.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        norm_num [Nat.factorial]
      have hxC : piO ↥(NW x) ⟨x, hxN⟩ ∈ centralizer ((toNWbar x K : Subgroup (NWbar x)) : Set (NWbar x)) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨k, hk, rfl⟩
        have h1 : (k : G) * x = x * (k : G) :=
          Subgroup.mem_centralizer_iff.1 (hQS.le h.x_mem_Q) (k : G) hk
        show piO ↥(NW x) k * piO ↥(NW x) ⟨x, hxN⟩ = piO ↥(NW x) ⟨x, hxN⟩ * piO ↥(NW x) k
        rw [← map_mul, ← map_mul]
        exact congrArg (piO ↥(NW x)) (Subtype.ext h1)
      have hx1 : piO ↥(NW x) ⟨x, hxN⟩ ≠ 1 := by
        have hx2 : orderOf (⟨x, hxN⟩ : ↥(NW x)) = 2 := by
          rw [Subgroup.orderOf_mk]; exact h.x_order
        intro h1
        have := orderOf_piO_of_orderOf_two hx2
        rw [h1, orderOf_one] at this
        omega
      have hzN : a * x * a⁻¹ ∈ NW x := NW x |>.mul_mem (NW x |>.mul_mem haN hxN) ((NW x).inv_mem haN)
      have hgx : piO ↥(NW x) ⟨a, haN⟩ * piO ↥(NW x) ⟨x, hxN⟩ * (piO ↥(NW x) ⟨a, haN⟩)⁻¹ ∈
          toNWbar x K := by
        have h1 : piO ↥(NW x) (⟨a, haN⟩ * ⟨x, hxN⟩ * ⟨a, haN⟩⁻¹) =
            piO ↥(NW x) ⟨a, haN⟩ * piO ↥(NW x) ⟨x, hxN⟩ * (piO ↥(NW x) ⟨a, haN⟩)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        rw [← h1]
        refine ⟨⟨a * x * a⁻¹, hzN⟩, hz.2, ?_⟩
        rfl
      exact false_of_isComponent_of_card_two_part hcomp hZ h8 hSylY hQcard_hat.le hxC hx1 hgx
  have hgenY : Gen4 (NWbar x) := Gen4.quotient _ (Gen4.subgroup (NW x) hgen)
  have hGHY : ∀ L : Subgroup (NWbar x), IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) →
      GHList ↥L :=
    fun L hs hn => IVK.ghList_of_subgroup_of_quotient hgh hNtop (piO ↥(NW x))
      (QuotientGroup.mk'_surjective _) L hs hn
  exact ivk73_apply_g4 h73 hY hgenY hGHY hO hn hord eKhat hQel_hat hQcard_hat hSylY htermY hns

theorem ivk_7_3_A57_core
    {G : Type} [Group G] [Finite G] (h73 : IVK.IVK_7_3_g4)
    (hks : IsKProperSimple G) (hgen : Gen4 G) (hgh : KGH G)
    {n : ℕ} (hn : n = 5 ∨ n = 7) {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) (haN : a ∈ NW x)
    (hW : pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥)
    (hns5 : n = 5 → ¬ CFSG.IsComponent (toNWbar x K)) :
    ∃ e0 : NWbar x ≃* alternatingGroup (Fin (n + 4)),
      (toNWbar x K).map e0.toMonoidHom = stdAlt n := by
  have hord : n = 5 → ∀ R : Subgroup (NWbar x), IsPGroup 2 ↥R → Nat.card ↥R ≤ 2 ^ 6 := by
    intro h5 R hR
    have h1 := card_le_card_S_of_isPGroup h hR
    have h2 := card_S_le hn h hS
    subst h5
    rw [alt_two_part_five] at h2
    exact h1.trans h2
  exact ivk_7_3_A57_core_of_hord h73 hks hgen hgh hn h hz haN hW hord hns5

theorem b_ivk_7_3_A57_of_g4
    (h73 : IVK.IVK_7_3_g4) (hstd : B_ivk_7_3_A57_std) :
    B_ivk_7_3_A57 := by
  intro G _ _ hG n hn x K T Q S a h hS hz haN hW
  have hn' : n = 5 ∨ n = 7 := by simpa using hn
  obtain ⟨e0, he0⟩ := ivk_7_3_A57_core h73 hG.kproper hG.gen4 hG.kgh hn' h hS hz haN hW
    (fun h5 => by
      subst h5
      exact hstd G hG x K T Q S a h hS hz haN hW)
  refine ⟨⊤, Subgroup.topEquiv.trans e0, Subgroup.IsSubnormal.top, le_top, ?_⟩
  rw [← he0]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(w : NWbar x), hw, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, trivial⟩, hy, rfl⟩

end Final

end CFSG.GH74.GLS.C3.Layer1.Bk
