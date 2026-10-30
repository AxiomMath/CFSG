module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private def dsa6a : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
private def dsa6b : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

private theorem dsa6_norm_dec : ∀ g : Equiv.Perm (Fin 5), Equiv.Perm.sign g = 1 →
    ((∀ v : Equiv.Perm (Fin 5), ((v = 1 ∨ v = dsa6a ∨ v = dsa6b ∨ v = dsa6a * dsa6b) ↔
        (g * v * g⁻¹ = 1 ∨ g * v * g⁻¹ = dsa6a ∨ g * v * g⁻¹ = dsa6b ∨ g * v * g⁻¹ = dsa6a * dsa6b)))
      ↔ g 4 = 4) := by
  decide +kernel

private theorem dsa6_card_fix4 :
    Nat.card {g : alternatingGroup (Fin 5) // (g : Equiv.Perm (Fin 5)) 4 = 4} = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def dsa6VA : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {g | (g : Equiv.Perm (Fin 5)) = 1 ∨ (g : Equiv.Perm (Fin 5)) = dsa6a ∨
    (g : Equiv.Perm (Fin 5)) = dsa6b ∨ (g : Equiv.Perm (Fin 5)) = dsa6a * dsa6b}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
      rw [hx, hy] <;> decide +kernel
  one_mem' := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_one, true_or]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at hx ⊢
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;> decide +kernel

private theorem dsa6_disj_sign : ∀ w : Equiv.Perm (Fin 5),
    (w = 1 ∨ w = dsa6a ∨ w = dsa6b ∨ w = dsa6a * dsa6b) → Equiv.Perm.sign w = 1 := by
  decide +kernel

private theorem dsa6_memVA (h : alternatingGroup (Fin 5)) : h ∈ dsa6VA ↔
    ((h : Equiv.Perm (Fin 5)) = 1 ∨ (h : Equiv.Perm (Fin 5)) = dsa6a ∨
      (h : Equiv.Perm (Fin 5)) = dsa6b ∨ (h : Equiv.Perm (Fin 5)) = dsa6a * dsa6b) := Iff.rfl

private theorem dsa6_normalizer_VA (g : alternatingGroup (Fin 5)) :
    g ∈ Subgroup.normalizer (dsa6VA : Set (alternatingGroup (Fin 5))) ↔
      (g : Equiv.Perm (Fin 5)) 4 = 4 := by
  have key := dsa6_norm_dec (g : Equiv.Perm (Fin 5)) (Equiv.Perm.mem_alternatingGroup.mp g.2)
  rw [Subgroup.mem_normalizer_iff, ← key]
  constructor
  · intro hN v
    by_cases hv : Equiv.Perm.sign v = 1
    · have h1 := hN ⟨v, Equiv.Perm.mem_alternatingGroup.mpr hv⟩
      rw [dsa6_memVA, dsa6_memVA] at h1
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h1
    · constructor
      · intro hv1
        exact absurd (dsa6_disj_sign v hv1) hv
      · intro hv2
        have hs : Equiv.Perm.sign ((g : Equiv.Perm (Fin 5)) * v * (g : Equiv.Perm (Fin 5))⁻¹) ≠ 1 := by
          rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.mem_alternatingGroup.mp g.2]
          simpa using hv
        exact absurd (dsa6_disj_sign _ hv2) hs
  · intro hv h
    have h1 := hv h.1
    rw [dsa6_memVA, dsa6_memVA]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h1

private theorem dsa6_card_normalizer_VA :
    Nat.card (Subgroup.normalizer (dsa6VA : Set (alternatingGroup (Fin 5)))) = 12 := by
  rw [← dsa6_card_fix4]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => dsa6_normalizer_VA g))

private theorem dsa6_card_VA : Nat.card dsa6VA = 4 := by
  have e : Nat.card dsa6VA = Nat.card {g : alternatingGroup (Fin 5) //
      ((g : Equiv.Perm (Fin 5)) = 1 ∨ (g : Equiv.Perm (Fin 5)) = dsa6a ∨
        (g : Equiv.Perm (Fin 5)) = dsa6b ∨ (g : Equiv.Perm (Fin 5)) = dsa6a * dsa6b)} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun g => dsa6_memVA g))
  rw [e, Nat.card_eq_fintype_card]
  decide +kernel

private theorem dsa6_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem dsa6_card_sylow_of_card60 {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (hT : IsSylowTwoOf T ⊤) (hX : Nat.card X = 60) : Nat.card T = 4 := by
  obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
  have hm := T.card_mul_index
  have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
  have hodd : ¬ 2 ∣ T.index := by rw [← e]; exact hT.2.2
  rw [hX, hk] at hm
  have hdvd : 2 ^ k ∣ 60 := ⟨T.index, hm.symm⟩
  have hle : 2 ^ k ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hk6 : k < 6 := by
    by_contra h
    push Not at h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  rw [hk]
  interval_cases k <;> omega

private theorem dsa6_card_conjSub {X : Type} [Group X] (g : X) (H : Subgroup X) :
    Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem dsa6_card_normalizer_sylow {X : Type} [Group X] [Finite X]
    (ψ : X ≃* alternatingGroup (Fin 5)) (T : Subgroup X) (hT : IsSylowTwoOf T ⊤) :
    Nat.card (Subgroup.normalizer (T : Set X)) = 12 := by
  set V0X : Subgroup X := dsa6VA.comap ψ.toMonoidHom with hV0X
  have hcardX : Nat.card X = 60 := by
    rw [Nat.card_congr ψ.toEquiv, dsa6_card_alt5]
  have hV0card : Nat.card V0X = 4 := by
    have := Subgroup.card_map_of_injective (f := ψ.toMonoidHom) (K := V0X) ψ.injective
    rw [hV0X, Subgroup.map_comap_eq_self_of_surjective ψ.surjective] at this
    rw [← this, dsa6_card_VA]
  have hV0p : IsPGroup 2 V0X := IsPGroup.of_card (show Nat.card V0X = 2 ^ 2 by rw [hV0card]; norm_num)
  have hTcard : Nat.card T = 4 := dsa6_card_sylow_of_card60 T hT hcardX
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hT le_top hV0p
  have heq : V0X = conjSub x T :=
    Subgroup.eq_of_le_of_card_ge hx (by rw [dsa6_card_conjSub, hTcard, hV0card])
  have hN : Nat.card (Subgroup.normalizer (V0X : Set X)) = Nat.card (Subgroup.normalizer (T : Set X)) := by
    rw [heq, ← dsa6_card_conjSub x (Subgroup.normalizer (T : Set X)), ← conjSub_normalizer]
  rw [← hN]
  have hmap : (Subgroup.normalizer (V0X : Set X)).map ψ.toMonoidHom =
      Subgroup.normalizer (dsa6VA : Set (alternatingGroup (Fin 5))) := by
    rw [Subgroup.map_normalizer_eq_of_bijective V0X (f := ψ.toMonoidHom) ψ.bijective]
    rw [hV0X, Subgroup.map_comap_eq_self_of_surjective ψ.surjective]
  have hc := Subgroup.card_map_of_injective (f := ψ.toMonoidHom) (K := Subgroup.normalizer (V0X : Set X))
    ψ.injective
  rw [hmap, dsa6_card_normalizer_VA] at hc
  exact hc.symm

theorem dsa6_frattini_eq_bot {G : Type} [Group G] {P L Q : Subgroup G}
    (h : A5Chief P L Q (dsFrattini Q)) (hQ : Nat.card Q = 16) : dsFrattini Q = ⊥ := by
  have hle : dsFrattini Q ≤ Q := Subgroup.map_subtype_le _
  have hm := Subgroup.relIndex_mul_card (H := dsFrattini Q) (K := Q)
  rw [inf_eq_left.mpr hle, h.card, hQ] at hm
  have h1 : Nat.card (dsFrattini Q) = 1 := by omega
  exact (Subgroup.eq_bot_iff_card _).mpr h1

theorem dsa6_comm_mem {G : Type} [Group G] {P L Q : Subgroup G}
    (h : A5Chief P L Q ⊥) {l e : G} (hl : l ∈ L) (he : e ∈ Q) : ⁅l, e⁆ ∈ Q ⊓ L := by
  have hQP : Q ≤ P := h.E_le
  have hlP : l ∈ P := h.le hl
  have hC : ⁅l, e⁆ = (l * e * l⁻¹) * e⁻¹ := by
    rw [commutatorElement_def]
  constructor
  · have hA : l * e * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (h.norm_E hlP) e).mp he
    rw [hC]
    exact Q.mul_mem hA (Q.inv_mem he)
  · have hB : e * l⁻¹ * e⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (h.norm_L (hQP he)) l⁻¹).mp (L.inv_mem hl)
    have hC' : ⁅l, e⁆ = l * (e * l⁻¹ * e⁻¹) := by
      rw [commutatorElement_def]; simp only [mul_assoc]
    rw [hC']
    exact L.mul_mem hl hB

theorem dsa6_le_of_chief {G : Type} [Group G] {P L Q : Subgroup G}
    (h : A5Chief P L Q ⊥) : Q ≤ L := by
  have hN : P ≤ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) := by
    intro p hp
    have hQ := Subgroup.mem_normalizer_iff.mp (h.norm_E hp)
    have hL := Subgroup.mem_normalizer_iff.mp (h.norm_L hp)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [hQ x, hL x]
  obtain ⟨l, hl, e, he, hne⟩ := h.nontriv
  have hmem := dsa6_comm_mem h hl he
  have hX : Q ⊓ L = Q := by
    rcases h.irred (Q ⊓ L) bot_le inf_le_left hN with h' | h'
    · exfalso
      rw [h'] at hmem
      exact hne hmem
    · exact h'
  exact inf_eq_left.mp hX

theorem dsa6_A5Par {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) :
    A5Par L1 (L1 ⊔ bigB L1 L2 S) :=
  A5Par.of_hyp111R (Finite4.gen4 (G := G)) h.hyp h.ns1

theorem dsa6_Q_le [DSLeaf LeafFrattiniChief] {G : Type} [Group G] [Finite4 G]
    {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (hQ : Nat.card (dsQ L1 L2 S) = 16) :
    dsQ L1 L2 S ≤ L1 := by
  have hA := frattini_chief (dsa6_A5Par h)
  have hΦ := dsa6_frattini_eq_bot hA hQ
  rw [hΦ] at hA
  exact dsa6_le_of_chief hA

theorem dsa6_S_le [DSLeaf LeafFrattiniChief] [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIStep4]
    {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S)
    (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) (c2 : ⁅dsZi L2 S, L2⁆ ≠ ⊥) : S ≤ L1 ⊓ L2 := by
  have hs := dsa_case_i_step4 h c1 c2
  have hQ1 := dsa6_Q_le h hs.2.2.1.2
  have hQ2 := dsa6_Q_le h.symm hs.2.2.2.2
  have e1 := (dsa_no_field h).1
  have e2 := (dsa_no_field h).2.1
  exact le_inf (e1.le.trans (sup_le inf_le_right hQ1)) (e2.le.trans (sup_le inf_le_right hQ2))

theorem dsa6_card_quot {X : Type} [Group X] (hq : IsL2Quot 2 X) : Nat.card X = 60 := by
  rw [IsL2Quot.card (by norm_num) hq]
  norm_num

theorem dsa6_card_L {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hQ : Nat.card (pCoreOf 2 L) = 16) :
    Nat.card L = 960 := by
  have h1 : Nat.card (pCore 2 ↥L) = 16 := by
    rw [← hQ]
    exact (Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective).symm
  have h2 : (pCore 2 ↥L).index = 60 := by
    rw [← dsa6_card_quot hq]
    rfl
  have h3 := (pCore 2 ↥L).card_mul_index
  rw [h1, h2] at h3
  simpa using h3.symm

theorem dsa6_index_borel {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    ((borelOf L S).subgroupOf L).index = 5 := by
  obtain ⟨hT2, hTodd, hNorm⟩ := F1.map_borelOf_eq_normalizer hsyl
  obtain ⟨ψ⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  set T' : Subgroup ↥L := (S ⊓ L).subgroupOf L with hT'
  set Tb : Subgroup (oTwoQuot ↥L) := T'.map π with hTb
  have hTsyl : IsSylowTwoOf Tb ⊤ := by
    refine ⟨le_top, hT2, ?_⟩
    have e : (Tb.subgroupOf ⊤).index = Tb.index := Subgroup.relIndex_top_right _
    rw [e]
    exact hTodd
  have hcardN : Nat.card (Subgroup.normalizer (Tb : Set (oTwoQuot ↥L))) = 12 :=
    dsa6_card_normalizer_sylow ψ Tb hTsyl
  have hidxN : (Subgroup.normalizer (Tb : Set (oTwoQuot ↥L))).index = 5 := by
    have h := (Subgroup.normalizer (Tb : Set (oTwoQuot ↥L))).card_mul_index
    rw [hcardN, dsa6_card_quot hq] at h
    omega
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ (borelOf L S).subgroupOf L := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have h1 : (x : G) ∈ pCoreOf 2 L := (F1.mem_pCore_iff_coe x).mp hx
    exact F1.sylow_le_borelOf L S (F7.isSylowTwoOf_pCoreOf_le hsyl h1)
  have himg : ((borelOf L S).subgroupOf L).map π = Subgroup.normalizer (Tb : Set (oTwoQuot ↥L)) :=
    hNorm
  have hi := Subgroup.index_map_eq (f := π) (H := (borelOf L S).subgroupOf L) hsurj hker
  rw [himg] at hi
  rw [← hi]
  exact hidxN

theorem dsa6_card_borel {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hQ : Nat.card (pCoreOf 2 L) = 16) : Nat.card (borelOf L S) = 192 := by
  have hle : borelOf L S ≤ L := F1.borelOf_le L S
  have h := ((borelOf L S).subgroupOf L).card_mul_index
  rw [dsa6_index_borel hq hsyl, dsa6_card_L L hq hQ] at h
  have hc : Nat.card ((borelOf L S).subgroupOf L) = Nat.card (borelOf L S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  omega

theorem dsa6_mem_K {G : Type} [Group G] {P L Q : Subgroup G} {p : G} :
    p ∈ dsCentMod P L Q ↔ p ∈ P ∧ p ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ l ∈ L, ⁅p, l⁆ ∈ Q :=
  Iff.rfl

theorem dsa6_K_conj {G : Type} [Group G] {P L Q : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    {p k : G} (hp : p ∈ P) (hk : k ∈ dsCentMod P L Q) : p * k * p⁻¹ ∈ dsCentMod P L Q := by
  rw [dsa6_mem_K] at hk ⊢
  obtain ⟨hkP, hkN, hkc⟩ := hk
  refine ⟨P.mul_mem (P.mul_mem hp hkP) (P.inv_mem hp), ?_, ?_⟩
  · exact (Subgroup.normalizer (Q : Set G)).mul_mem
      ((Subgroup.normalizer (Q : Set G)).mul_mem (hPQ hp) hkN)
      ((Subgroup.normalizer (Q : Set G)).inv_mem (hPQ hp))
  · intro l hl
    have h1 := Subgroup.mem_normalizer_iff.mp (hPL (P.inv_mem hp)) l
    rw [inv_inv] at h1
    have hl' : p⁻¹ * l * p ∈ L := h1.mp hl
    have key : ⁅p * k * p⁻¹, l⁆ = p * ⁅k, p⁻¹ * l * p⁆ * p⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact (Subgroup.mem_normalizer_iff.mp (hPQ hp) _).mp (hkc _ hl')

theorem dsa6_K_le_normalizer {G : Type} [Group G] {P L Q S : Subgroup G}
    (hSL : S ≤ L) (hQS : Q ≤ S) {k : G} (hk : k ∈ dsCentMod P L Q) :
    k ∈ Subgroup.normalizer (S : Set G) := by
  have fwd : ∀ x ∈ dsCentMod P L Q, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro x hx s hs
    rw [dsa6_mem_K] at hx
    have hc := hx.2.2 s (hSL hs)
    have e : x * s * x⁻¹ = ⁅x, s⁆ * s := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact S.mul_mem (hQS hc) hs
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact fwd k hk s
  · intro hs
    have h := fwd k⁻¹ ((dsCentMod P L Q).inv_mem hk) _ hs
    have e2 : k⁻¹ * (k * s * k⁻¹) * k⁻¹⁻¹ = s := by group
    rwa [e2] at h

theorem dsa6_le_K {G : Type} [Group G] {P L Q : Subgroup G} (hLP : L ≤ P) (hQP : Q ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ dsCentMod P L Q := by
  intro q hq
  rw [dsa6_mem_K]
  refine ⟨hQP hq, hPQ (hQP hq), fun l hl => ?_⟩
  have hA : l * q⁻¹ * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hPQ (hLP hl)) q⁻¹).mp (Q.inv_mem hq)
  have e : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by
    rw [commutatorElement_def]
    simp only [mul_assoc]
  rw [e]
  exact Q.mul_mem hq hA

private theorem dsa6_central_perm : ∀ g : Equiv.Perm (Fin 5), Equiv.Perm.sign g = 1 →
    (∀ h : Equiv.Perm (Fin 5), Equiv.Perm.sign h = 1 → g * h = h * g) → g = 1 := by
  decide +kernel

theorem dsa6_central_quot {X : Type} [Group X] (hq : IsL2Quot 2 X) (x : X)
    (hx : ∀ y : X, x * y = y * x) : x = 1 := by
  obtain ⟨ψ⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  have hcomm : ∀ h : alternatingGroup (Fin 5), ψ x * h = h * ψ x := by
    intro h
    have := congrArg ψ (hx (ψ.symm h))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hψ : ψ x = 1 := by
    apply Subtype.ext
    show ((ψ x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1
    apply dsa6_central_perm ((ψ x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
      (Equiv.Perm.mem_alternatingGroup.mp (ψ x).2)
    intro h hh
    have := congrArg Subtype.val (hcomm ⟨h, Equiv.Perm.mem_alternatingGroup.mpr hh⟩)
    simpa using this
  have : x = ψ.symm (ψ x) := (ψ.symm_apply_apply x).symm
  rw [this, hψ, map_one]

theorem dsa6_K_inf {G : Type} [Group G] {L Q : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L))
    (hQL : Q ⊓ L ≤ pCoreOf 2 L) {k : G} (hkL : k ∈ L) (hk : ∀ l ∈ L, ⁅k, l⁆ ∈ Q) :
    k ∈ pCoreOf 2 L := by
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcen : ∀ y : oTwoQuot ↥L, π ⟨k, hkL⟩ * y = y * π ⟨k, hkL⟩ := by
    intro y
    obtain ⟨l, rfl⟩ := hsurj y
    have hcomm_mem : ⁅(⟨k, hkL⟩ : ↥L), l⁆ ∈ pCore 2 ↥L := by
      rw [F1.mem_pCore_iff_coe]
      have h1 : ((⁅(⟨k, hkL⟩ : ↥L), l⁆ : ↥L) : G) = ⁅k, (l : G)⁆ := by
        simp [commutatorElement_def]
      rw [h1]
      exact hQL ⟨hk _ l.2, L.mul_mem (L.mul_mem (L.mul_mem hkL l.2) (L.inv_mem hkL))
        (L.inv_mem l.2)⟩
    have h1 : π ⁅(⟨k, hkL⟩ : ↥L), l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm_mem
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π ⟨k, hkL⟩ * π l = (π ⟨k, hkL⟩ * π l * (π ⟨k, hkL⟩)⁻¹ * (π l)⁻¹) * (π l * π ⟨k, hkL⟩) := by
          group
      _ = π l * π ⟨k, hkL⟩ := by rw [h1, one_mul]
  have hx1 : π ⟨k, hkL⟩ = 1 := dsa6_central_quot hq _ hcen
  have hmem : (⟨k, hkL⟩ : ↥L) ∈ pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hx1
  exact (F1.mem_pCore_iff_coe _).mp hmem

theorem dsa6_KZ {G : Type} [Group G] {P L1 Q S : Subgroup G}
    (hLP : L1 ≤ P) (hPL : P ≤ Subgroup.normalizer (L1 : Set G))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hQdef : pCoreOf 2 P = Q) (hCT : CharTwo P)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hZi : dsZi L1 S = Q)
    {c : G} (hc : c ∈ dsCentMod P L1 Q) (hcZ : ∀ z ∈ dsZ S, c * z = z * c) : c ∈ Q := by
  have hcP : c ∈ P := ((dsa6_mem_K).mp hc).1
  have hcc := ((dsa6_mem_K).mp hc).2.2
  let C : Subgroup G := Subgroup.centralizer ({c} : Set G) ⊓ Q
  have hmemC : ∀ q, q ∈ C ↔ c * q = q * c ∧ q ∈ Q := by
    intro q
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1 c (Set.mem_singleton c), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact h1, h2⟩
  have hinv : ∀ l ∈ L1, ∀ q ∈ C, l⁻¹ * q * l ∈ C := by
    intro l hl q hq
    obtain ⟨hcq, hqQ⟩ := (hmemC q).mp hq
    have hcomQ : ⁅c, l⁆ ∈ Q := hcc l hl
    have hcl : c * l * c⁻¹ = ⁅c, l⁆ * l := by
      simp only [commutatorElement_def]
      group
    have hcomm_eq : ⁅c, l⁆ * q = q * ⁅c, l⁆ := hab _ hcomQ _ hqQ
    have e2 : c * q * c⁻¹ = q := by rw [hcq]; group
    have hxconj : c * (l⁻¹ * q * l) * c⁻¹ = l⁻¹ * q * l := by
      have e1 : c * (l⁻¹ * q * l) * c⁻¹ = (c * l * c⁻¹)⁻¹ * (c * q * c⁻¹) * (c * l * c⁻¹) := by
        group
      rw [e1, hcl, e2]
      have e3 : ⁅c, l⁆⁻¹ * q * ⁅c, l⁆ = q := by
        rw [mul_assoc, ← hcomm_eq, ← mul_assoc, inv_mul_cancel, one_mul]
      calc (⁅c, l⁆ * l)⁻¹ * q * (⁅c, l⁆ * l) = l⁻¹ * (⁅c, l⁆⁻¹ * q * ⁅c, l⁆) * l := by group
        _ = l⁻¹ * q * l := by rw [e3]
    have hxQ : l⁻¹ * q * l ∈ Q := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hPQ (P.inv_mem (hLP hl))) q).mp hqQ
      rw [inv_inv] at h1
      exact h1
    rw [hmemC]
    refine ⟨?_, hxQ⟩
    calc c * (l⁻¹ * q * l) = (c * (l⁻¹ * q * l) * c⁻¹) * c := by group
      _ = (l⁻¹ * q * l) * c := by rw [hxconj]
  have hQC : Q ≤ C := by
    rw [← hZi]
    unfold dsZi dsConjClosure
    refine iSup₂_le fun y hy => ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro z hz
    have hzQ : z ∈ Q := by
      rw [← hZi]
      exact dsZ_le_dsZi L1 S hz
    have hzC : z ∈ C := (hmemC z).mpr ⟨hcZ z hz, hzQ⟩
    have h1 := hinv y⁻¹ (L1.inv_mem hy) z hzC
    rw [inv_inv] at h1
    rw [Subgroup.mem_comap]
    exact h1
  have hcent : c ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) := by
    rw [hQdef, Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((hmemC h).mp (hQC hh)).1.symm
  have hfin := hCT (Subgroup.mem_inf.mpr ⟨hcP, hcent⟩)
  rw [hQdef] at hfin
  exact hfin

theorem dsa6_fixpt {G : Type} [Group G] {R Z : Subgroup G} {y : G}
    (hR : ∀ x ∈ R, ∀ x' ∈ R, x * x' = x' * x) (hR2 : ∀ x ∈ R, x ^ 2 = 1)
    (hy3 : y * y * y = 1)
    (hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R) (hZR : Z ≤ R) (hZy : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z)
    (hZv : ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ Z) {v : G} (hv : v ∈ R) (hvZ : v ∉ Z) :
    ∃ w ∈ R, w ≠ 1 ∧ y * w = w * y := by
  set σ : G → G := fun x => y * x * y⁻¹ with hσ
  have hσmul : ∀ x x', σ (x * x') = σ x * σ x' := by
    intro x x'
    simp only [hσ]
    group
  have hσ3 : ∀ x, σ (σ (σ x)) = x := by
    intro x
    simp only [hσ]
    have e : y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * x * (y * y * y)⁻¹ := by group
    rw [e, hy3]
    group
  set w := v * σ v * σ (σ v) with hw
  have hσv : σ v ∈ R := hyR v hv
  have hσσv : σ (σ v) ∈ R := hyR _ hσv
  have hwR : w ∈ R := R.mul_mem (R.mul_mem hv hσv) hσσv
  have hfix : σ w = w := by
    rw [hw, hσmul, hσmul, hσ3]
    have c1 := hR _ hσv _ hσσv
    have c2 := hR _ hv _ hσσv
    have c3 := hR _ hv _ hσv
    calc σ v * σ (σ v) * v = σ v * (σ (σ v) * v) := by rw [mul_assoc]
      _ = σ v * (v * σ (σ v)) := by rw [c2]
      _ = (σ v * v) * σ (σ v) := by rw [← mul_assoc]
      _ = (v * σ v) * σ (σ v) := by rw [c3]
      _ = v * σ v * σ (σ v) := rfl
  refine ⟨w, hwR, ?_, ?_⟩
  · intro hw1
    have ha : σ v * v⁻¹ ∈ Z := by
      have := hZv v hv
      simpa only [hσ, mul_assoc] using this
    set a := σ v * v⁻¹ with ha_def
    have haR : a ∈ R := hZR ha
    set s := σ a with hs_def
    have hsZ : s ∈ Z := hZy a ha
    have hsR : s ∈ R := hZR hsZ
    have hsv : σ v = a * v := by
      rw [ha_def]
      group
    have hsσ : σ (σ v) = s * (a * v) := by
      rw [hsv, hσmul, hsv]
    have hv2 : v * v = 1 := by rw [← pow_two]; exact hR2 v hv
    have ha2 : a * a = 1 := by rw [← pow_two]; exact hR2 a haR
    have hs2 : s * s = 1 := by rw [← pow_two]; exact hR2 s hsR
    have hva : v * a = a * v := hR v hv a haR
    have hsa : s * a = a * s := hR s hsR a haR
    have e1 : v * a * v = a := by
      rw [hva, mul_assoc, hv2, mul_one]
    have e2 : s * a * v = a * (s * v) := by rw [hsa, mul_assoc]
    have hwvs : w = v * s := by
      rw [hw, hsσ, hsv]
      calc v * (a * v) * (s * (a * v)) = (v * a * v) * (s * a * v) := by simp only [mul_assoc]
        _ = a * (a * (s * v)) := by rw [e1, e2]
        _ = (a * a) * (s * v) := by simp only [mul_assoc]
        _ = s * v := by rw [ha2, one_mul]
        _ = v * s := hR s hsR v hv
    have hvs : v * s = 1 := by rw [← hwvs]; exact hw1
    have hvs' : v = s⁻¹ := eq_inv_of_mul_eq_one_left hvs
    have hss' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    exact hvZ (by rw [hvs', hss']; exact hsZ)
  · calc y * w = (y * w * y⁻¹) * y := by group
      _ = w * y := by rw [show y * w * y⁻¹ = σ w from rfl, hfix]

theorem dsa6_comm_mod {G : Type} [Group G] {Q1 Q2 S : Subgroup G}
    (hdec : ∀ x ∈ S, ∃ a ∈ Q1, ∃ b ∈ Q2, x = a * b) (hQ2S : Q2 ≤ S)
    (hN1 : S ≤ Subgroup.normalizer (Q1 : Set G)) (hab2 : ∀ x ∈ Q2, ∀ y ∈ Q2, x * y = y * x)
    {x y : G} (hx : x ∈ S) (hy : y ∈ S) : ⁅x, y⁆ ∈ Q1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hdec y hy
  have hbS : b ∈ S := hQ2S hb
  have hdS : d ∈ S := hQ2S hd
  have hbd : b * d = d * b := hab2 b hb d hd
  have hdb' : d * b⁻¹ = b⁻¹ * d := by
    rw [show d * b⁻¹ = b⁻¹ * (b * d) * b⁻¹ by group, hbd]
    group
  have hbc : b * c * b⁻¹ ∈ Q1 := (Subgroup.mem_normalizer_iff.mp (hN1 hbS) c).mp hc
  have hda : d * a⁻¹ * d⁻¹ ∈ Q1 :=
    (Subgroup.mem_normalizer_iff.mp (hN1 hdS) a⁻¹).mp (Q1.inv_mem ha)
  have key : ⁅a * b, c * d⁆ = a * ((b * c * b⁻¹) * d) * a⁻¹ * d⁻¹ * c⁻¹ := by
    calc ⁅a * b, c * d⁆ = a * (b * c * (d * b⁻¹)) * a⁻¹ * d⁻¹ * c⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = a * (b * c * (b⁻¹ * d)) * a⁻¹ * d⁻¹ * c⁻¹ := by rw [hdb']
      _ = a * ((b * c * b⁻¹) * d) * a⁻¹ * d⁻¹ * c⁻¹ := by group
  rw [key]
  have e : a * ((b * c * b⁻¹) * d) * a⁻¹ * d⁻¹ * c⁻¹ = a * (b * c * b⁻¹) * (d * a⁻¹ * d⁻¹) * c⁻¹ := by
    group
  rw [e]
  exact Q1.mul_mem (Q1.mul_mem (Q1.mul_mem ha hbc) hda) (Q1.inv_mem hc)

theorem dsa6_centS_Z {G : Type} [Group G] {Q1 Q2 S : Subgroup G}
    (hdec : ∀ x ∈ S, ∃ a ∈ Q1, ∃ b ∈ Q2, x = a * b)
    (hab1 : ∀ x ∈ Q1, ∀ y ∈ Q1, x * y = y * x) (hab2 : ∀ x ∈ Q2, ∀ y ∈ Q2, x * y = y * x)
    {s z : G} (hs : s ∈ S) (hz1 : z ∈ Q1) (hz2 : z ∈ Q2) : s * z = z * s := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec s hs
  calc a * b * z = a * (b * z) := by rw [mul_assoc]
    _ = a * (z * b) := by rw [hab2 b hb z hz2]
    _ = (a * z) * b := by rw [mul_assoc]
    _ = (z * a) * b := by rw [hab1 a ha z hz1]
    _ = z * (a * b) := by rw [mul_assoc]

theorem dsa6_normal_inf_subgroupOf {G : Type} [Group G] {A H : Subgroup G}
    (hA : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) : ((A ⊓ H).subgroupOf H).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnA, hnH⟩ := Subgroup.mem_inf.mp hn
  refine Subgroup.mem_inf.mpr ⟨hA _ g.2 _ hnA, H.mul_mem (H.mul_mem g.2 hnH) (H.inv_mem g.2)⟩

theorem dsa6_perm {G : Type} [Group G] [Finite G] {P L Q B : Subgroup G} (k : ℕ)
    (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hBP : B ≤ P) (hLnB : ¬ L ≤ B)
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hpc : pCoreOf 2 L = Q) (hQB : Q ≤ B)
    (hKB : ∀ x ∈ dsCentMod P L Q, x ∈ B) (hPk : Nat.card P = 960 * k) (hBk : Nat.card B = 192 * k)
    (hLcard : Nat.card L = 960) (hQcard : Nat.card Q = 16) (hk : 0 < k) (hkodd : Odd k) :
    Nat.card (dsCentMod P L Q) = 16 * k := by
  classical
  set KG := dsCentMod P L Q with hKG
  have hQP : Q ≤ P := hQB.trans hBP
  have hQKG : Q ≤ KG := dsa6_le_K hLP hQP hPQ
  have hKGP : KG ≤ P := fun x hx => ((dsa6_mem_K).mp hx).1
  have hKGconj : ∀ p ∈ P, ∀ x ∈ KG, p * x * p⁻¹ ∈ KG := fun p hp x hx => dsa6_K_conj hPL hPQ hp hx
  set H : Subgroup ↥P := B.subgroupOf P with hH
  set Ω := ↥P ⧸ H with hΩ
  have hΩcard : Nat.card Ω = 5 := by
    have h1 := H.card_mul_index
    have hH' : Nat.card H = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
    have h2 : H.index = Nat.card Ω := rfl
    rw [hH', hBk, hPk] at h1
    have h3 : H.index = 5 := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 192 * k by omega)
      rw [h1]
      ring
    rw [← h2]
    exact h3
  set ρ : ↥P →* Equiv.Perm Ω := MulAction.toPermHom ↥P Ω with hρ
  set K' : Subgroup ↥P := ρ.ker with hK'
  have hmemK' : ∀ n : ↥P, n ∈ K' ↔ ∀ y : Ω, ρ n y = y := by
    intro n
    rw [hK', MonoidHom.mem_ker]
    constructor
    · intro h y
      rw [h]
      rfl
    · intro h
      ext y
      rw [h y]
      rfl
  have hK'B : ∀ n ∈ K', (n : G) ∈ B := by
    intro n hn
    have h1 := (hmemK' n).mp hn (QuotientGroup.mk 1)
    have h2 : (QuotientGroup.mk (n * 1) : Ω) = QuotientGroup.mk 1 := h1
    have h3 := QuotientGroup.eq.mp h2
    rw [Subgroup.mem_subgroupOf] at h3
    have h4 : ((n * 1)⁻¹ * 1 : ↥P) = n⁻¹ := by group
    rw [h4] at h3
    simpa using B.inv_mem h3
  have hKGK' : ∀ x : ↥P, (x : G) ∈ KG → x ∈ K' := by
    intro x hx
    rw [hmemK']
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hc : (z : G)⁻¹ * (x : G)⁻¹ * (z : G) ∈ KG := by
      have := hKGconj (z : G)⁻¹ (P.inv_mem z.2) ((x : G)⁻¹) (KG.inv_mem hx)
      simpa [mul_assoc] using this
    have hcB := hKB _ hc
    show (QuotientGroup.mk (x * z) : Ω) = QuotientGroup.mk z
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf]
    have e : (((x * z)⁻¹ * z : ↥P) : G) = (z : G)⁻¹ * (x : G)⁻¹ * (z : G) := by
      simp [mul_assoc]
    rw [e]
    exact hcB
  have hK'norm : ∀ g : ↥P, ∀ n ∈ K', g * n * g⁻¹ ∈ K' := fun g n hn =>
    (MonoidHom.normal_ker ρ).conj_mem n hn g
  set KK : Subgroup G := K'.map P.subtype with hKK
  have hKKmem : ∀ n ∈ K', (n : G) ∈ KK := fun n hn => Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  have hKKB : ∀ x ∈ KK, x ∈ B := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    exact hK'B n hn
  have hKKP : ∀ g ∈ P, ∀ x ∈ KK, g * x * g⁻¹ ∈ KK := by
    intro g hg x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    have := hK'norm ⟨g, hg⟩ n hn
    exact Subgroup.mem_map.mpr ⟨_, this, rfl⟩
  have hQL : Q ≤ L := by rw [← hpc]; exact FaithfulA5.pCoreOf_le_self 2 L
  haveI : IsSimpleGroup (oTwoQuot ↥L) := (FaithfulA5.isSimpleGroup_and_card_of_isL2Quot hq).1
  set M' : Subgroup ↥L := (KK ⊓ L).subgroupOf L with hM'
  haveI hM'norm : M'.Normal :=
    dsa6_normal_inf_subgroupOf (A := KK) (H := L) (fun h hh a ha => hKKP h (hLP hh) a ha)
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  set N'' : Subgroup (oTwoQuot ↥L) := M'.map π with hN''
  haveI hNn : N''.Normal := Subgroup.Normal.map hM'norm π (QuotientGroup.mk'_surjective _)
  have hMQ : ∀ x ∈ KK ⊓ L, x ∈ Q := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N'' with hbot | htop
    · intro x hx
      have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).2
      have hxM : (⟨x, hxL⟩ : ↥L) ∈ M' := Subgroup.mem_subgroupOf.mpr hx
      have hmem : π ⟨x, hxL⟩ ∈ N'' := Subgroup.mem_map.mpr ⟨_, hxM, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have hpc' : (⟨x, hxL⟩ : ↥L) ∈ pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hmem
      have h2 := (F1.mem_pCore_iff_coe _).mp hpc'
      rw [hpc] at h2
      exact h2
    · exfalso
      apply hLnB
      intro y hy
      have hyPmem : π ⟨y, hy⟩ ∈ N'' := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hyPmem
      have hmG : (m : G) ∈ KK ⊓ L := Subgroup.mem_subgroupOf.mp hm
      have hmeq' : (m : ↥L ⧸ pCore 2 ↥L) = ((⟨y, hy⟩ : ↥L) : ↥L ⧸ pCore 2 ↥L) := hmeq
      have hq1 := (QuotientGroup.eq.mp hmeq')
      have hq2 := (F1.mem_pCore_iff_coe _).mp hq1
      have hyeq : y = (m : G) * ((m : G)⁻¹ * y) := by group
      have hq3 : (m : G)⁻¹ * y ∈ Q := by
        have h5 : ((m⁻¹ * ⟨y, hy⟩ : ↥L) : G) = (m : G)⁻¹ * y := by simp
        rw [h5, ← hpc] at *
        exact hq2
      rw [hyeq]
      exact B.mul_mem (hKKB _ hmG.1) (hQB hq3)
  have hKGKK : KK = KG := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
      have hnP : (n : G) ∈ P := n.2
      refine (dsa6_mem_K).mpr ⟨hnP, hPQ hnP, fun l hl => ?_⟩
      apply hMQ
      have hnK := hKKmem n hn
      have hlP : l ∈ P := hLP hl
      have hnl : ⁅(n : G), l⁆ = (n : G) * (l * (n : G)⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hinvK : l * (n : G)⁻¹ * l⁻¹ ∈ KK := by
        have := hKKP l hlP ((n : G)⁻¹) (KK.inv_mem hnK)
        exact this
      have hcomK : ⁅(n : G), l⁆ ∈ KK := by
        rw [hnl]
        exact KK.mul_mem hnK hinvK
      have hcomL : ⁅(n : G), l⁆ ∈ L := by
        have hconj : (n : G) * l * (n : G)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hPL hnP) l).mp hl
        have e : ⁅(n : G), l⁆ = ((n : G) * l * (n : G)⁻¹) * l⁻¹ := by
          rw [commutatorElement_def]
        rw [e]
        exact L.mul_mem hconj (L.inv_mem hl)
      exact Subgroup.mem_inf.mpr ⟨hcomK, hcomL⟩
    · intro x hx
      have hxP : x ∈ P := (dsa6_mem_K.mp hx).1
      exact Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, hKGK' ⟨x, hxP⟩ hx, rfl⟩
  set L' : Subgroup ↥P := L.subgroupOf P with hL'
  set ψ : ↥L' →* Equiv.Perm Ω := ρ.comp L'.subtype with hψ
  have hf : Function.Injective (P.subtype.comp L'.subtype : ↥L' →* G) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hmapQ : ψ.ker.map (P.subtype.comp L'.subtype : ↥L' →* G) = Q := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyK : (y : ↥P) ∈ K' := MonoidHom.mem_ker.mp hy
      have hyKK : ((y : ↥P) : G) ∈ KK := hKKmem _ hyK
      have hyL : ((y : ↥P) : G) ∈ L := (Subgroup.mem_subgroupOf.mp y.2)
      exact hMQ _ (Subgroup.mem_inf.mpr ⟨hyKK, hyL⟩)
    · intro hq
      have hqP : q ∈ P := hQP hq
      have hqL : q ∈ L := hQL hq
      have hqK : (⟨q, hqP⟩ : ↥P) ∈ K' := hKGK' ⟨q, hqP⟩ (hQKG hq)
      refine ⟨⟨⟨q, hqP⟩, Subgroup.mem_subgroupOf.mpr hqL⟩, MonoidHom.mem_ker.mpr hqK, rfl⟩
  have hker_card : Nat.card ψ.ker = 16 := by
    rw [← hQcard, ← hmapQ, Subgroup.card_map_of_injective hf]
  have hL'card : Nat.card ↥L' = 960 := by
    rw [hL', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLP).toEquiv, hLcard]
  have hidx : ψ.ker.index = 60 := by
    have h1 := ψ.ker.card_mul_index
    rw [hker_card, hL'card] at h1
    omega
  have hψrange : Nat.card ψ.range = 60 := by
    rw [← Subgroup.index_ker ψ]
    exact hidx
  have hψle : ψ.range ≤ ρ.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  have hcardPerm : Nat.card (Equiv.Perm Ω) = 120 := by
    rw [Nat.card_perm, hΩcard]
    rfl
  have hdvd60 : 60 ∣ Nat.card ρ.range := by
    rw [← hψrange]
    exact Subgroup.card_dvd_of_le hψle
  have hdvd120 : Nat.card ρ.range ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card ρ.range
    rwa [hcardPerm] at this
  obtain ⟨j, hj⟩ := hdvd60
  have hj2 : j ≤ 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd120
    omega
  have hR : Nat.card ρ.range = 60 ∨ Nat.card ρ.range = 120 := by
    interval_cases j
    · rw [hj] at hdvd120
      norm_num at hdvd120
    · left
      rw [hj]
    · right
      rw [hj]
  have hK'idx : K'.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have h1 := K'.card_mul_index
  rw [hK'idx, hPk] at h1
  have hKKcard : Nat.card KK = Nat.card K' :=
    Subgroup.card_map_of_injective (f := P.subtype) P.subtype_injective
  have hKGcard : Nat.card KG = Nat.card K' := by
    rw [← hKGKK, hKKcard]
  have hfin : Nat.card KG * Nat.card ρ.range = 960 * k := by
    rw [hKGcard, ← h1]
  have hQKGdvd : Nat.card Q ∣ Nat.card KG := Subgroup.card_dvd_of_le hQKG
  rw [hQcard] at hQKGdvd
  rcases hR with hR | hR
  · rw [hR] at hfin
    omega
  · exfalso
    rw [hR] at hfin
    obtain ⟨m, hm⟩ := hkodd
    have h8 : Nat.card KG = 8 * k := by omega
    rw [h8] at hQKGdvd
    omega

def dsa6_MA {G : Type} [Group G] (B Z : Subgroup G) (hZ : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) :
    MulAction ↥B ↥Z where
  smul b z := ⟨(b : G) * z * (b : G)⁻¹, hZ b b.2 z z.2⟩
  one_smul z := by
    apply Subtype.ext
    show ((1 : ↥B) : G) * (z : G) * ((1 : ↥B) : G)⁻¹ = (z : G)
    simp
  mul_smul b c z := by
    apply Subtype.ext
    show ((b * c : ↥B) : G) * (z : G) * ((b * c : ↥B) : G)⁻¹ =
      ((b : G) * ((c : G) * (z : G) * (c : G)⁻¹) * (b : G)⁻¹)
    simp [mul_assoc]

theorem dsa6_KZ_card {G : Type} [Group G] [Finite G] (B Z : Subgroup G)
    (hZ : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) (hZ4 : Nat.card Z = 4) :
    Nat.card (Subgroup.map B.subtype (MonoidHom.ker (@MulAction.toPermHom ↥B ↥Z _ (dsa6_MA B Z hZ)))) *
      Nat.card (@MulAction.toPermHom ↥B ↥Z _ (dsa6_MA B Z hZ)).range = Nat.card B ∧
    Nat.card (@MulAction.toPermHom ↥B ↥Z _ (dsa6_MA B Z hZ)).range ∣ 24 := by
  letI := dsa6_MA B Z hZ
  set φ := MulAction.toPermHom ↥B ↥Z with hφ
  constructor
  · rw [Subgroup.card_map_of_injective B.subtype_injective]
    have h := φ.ker.card_mul_index
    rw [Subgroup.index_ker] at h
    exact h
  · have h : Nat.card (Equiv.Perm ↥Z) = 24 := by
      rw [Nat.card_perm, hZ4]
      rfl
    rw [← h]
    exact Subgroup.card_subgroup_dvd_card _

theorem dsa6_side {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) (hq : IsL2Quot 2 (oTwoQuot ↥L1)) (hS1 : S ≤ L1)
    (hQ1L : dsQ L1 L2 S ≤ L1) (hsum : dsQ L1 L2 S ⊔ dsQ L2 L1 S = S)
    (hcQ : Nat.card (dsQ L1 L2 S) = 16)
    (hNS : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hSylB : IsSylowTwoOf S (bigB L1 L2 S)) :
    ∃ k : ℕ, Odd k ∧ Nat.card (bigB L1 L2 S) = 192 * k ∧
      (L1.subgroupOf (bigB L1 L2 S)).index = k ∧
      Nat.card (dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S)) = 16 * k ∧
      dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S) ≤ bigB L1 L2 S ∧
      Nat.card ↥(L1 ⊓ bigB L1 L2 S) = 192 ∧ pCoreOf 2 L1 = dsQ L1 L2 S ∧ Nat.card L1 = 960 := by
  have hQS : dsQ L1 L2 S ≤ S := le_sup_left.trans hsum.le
  have hBS : S ≤ bigB L1 L2 S := hSylB.1
  have hP1N : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := F1.parabolic_le_normalizer h
  have hPQ : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer ((dsQ L1 L2 S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S)
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hLP : L1 ≤ L1 ⊔ bigB L1 L2 S := le_sup_left
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := hBP.trans hP1N
  have hpc : pCoreOf 2 L1 = dsQ L1 L2 S := by
    apply le_antisymm
    · exact F1.pCoreOf_le_pCoreOf_parabolic h
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ1L
        (hLP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hmaxS : (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) = bigB L1 L2 S := by
    rcases F1.bigB_maximal_in_parabolic h ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G))
      (le_inf hBP hNS) inf_le_left with h' | h'
    · exact h'
    · exfalso
      have hPS : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := inf_eq_left.mp h'
      apply h.r1.borel_ne
      rw [inf_eq_left.mpr hS1]
      exact inf_eq_left.mpr (hLP.trans hPS)
  have hLnB : ¬ L1 ≤ bigB L1 L2 S := by
    intro hLB
    apply h.r1.borel_ne
    rw [inf_eq_left.mpr hS1]
    exact inf_eq_left.mpr (hLB.trans hNS)
  have hKB : ∀ x ∈ dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S), x ∈ bigB L1 L2 S := by
    intro x hx
    rw [← hmaxS]
    exact ⟨((dsa6_mem_K).mp hx).1, dsa6_K_le_normalizer hS1 hQS hx⟩
  have hpcQ : Nat.card (pCoreOf 2 L1) = 16 := by rw [hpc, hcQ]
  have hcL1 : Nat.card L1 = 960 := dsa6_card_L L1 hq hpcQ
  have hcBL1 : Nat.card (borelOf L1 S) = 192 := dsa6_card_borel hq h.hyp.h1.sylow hpcQ
  have hBL1 : Nat.card (L1.subgroupOf (bigB L1 L2 S)) = 192 := by
    have h1 : Nat.card ((L1.subgroupOf (bigB L1 L2 S)).map (bigB L1 L2 S).subtype) =
        Nat.card (L1.subgroupOf (bigB L1 L2 S)) :=
      Subgroup.card_map_of_injective (bigB L1 L2 S).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at h1
    rw [← h1, F1.inf_bigB_eq_borelOf h]
    exact hcBL1
  set k := (L1.subgroupOf (bigB L1 L2 S)).index with hk
  have hBk : Nat.card (bigB L1 L2 S) = 192 * k := by
    have h1 := (L1.subgroupOf (bigB L1 L2 S)).card_mul_index
    rw [hBL1] at h1
    exact h1.symm
  have hidxP : (L1.subgroupOf (L1 ⊔ bigB L1 L2 S)).index = k := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer hBN
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBN
    have e1 := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient
      (bigB L1 L2 S) L1 hBN).toEquiv
    have e2 : bigB L1 L2 S ⊔ L1 = L1 ⊔ bigB L1 L2 S := sup_comm _ _
    rw [e2] at e1
    have c1 : Nat.card (↥(bigB L1 L2 S) ⧸ L1.subgroupOf (bigB L1 L2 S)) = k := rfl
    have c2 : Nat.card (↥(L1 ⊔ bigB L1 L2 S) ⧸ L1.subgroupOf (L1 ⊔ bigB L1 L2 S)) =
        (L1.subgroupOf (L1 ⊔ bigB L1 L2 S)).index := rfl
    rw [c1, c2] at e1
    exact e1.symm
  have hPk : Nat.card ↥(L1 ⊔ bigB L1 L2 S) = 960 * k := by
    have h1 := (L1.subgroupOf (L1 ⊔ bigB L1 L2 S)).card_mul_index
    have h2 : Nat.card (L1.subgroupOf (L1 ⊔ bigB L1 L2 S)) = 960 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLP).toEquiv, hcL1]
    rw [h2, hidxP] at h1
    exact h1.symm
  have hsubS : S.subgroupOf (bigB L1 L2 S) ≤ L1.subgroupOf (bigB L1 L2 S) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hS1 hx
  have hk_odd : Odd k := by
    have hd := Subgroup.index_dvd_of_le hsubS
    have hodd : ¬ 2 ∣ (S.subgroupOf (bigB L1 L2 S)).index := hSylB.2.2
    rw [Nat.odd_iff]
    by_contra hc
    have h2 : 2 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
    exact hodd (h2.trans hd)
  have hk0 : 0 < k := hk_odd.pos
  have hQB : dsQ L1 L2 S ≤ bigB L1 L2 S := hQS.trans hBS
  have hQcard : Nat.card (dsQ L1 L2 S) = 16 := hcQ
  refine ⟨k, hk_odd, hBk, rfl, ?_, ?_, ?_, hpc, hcL1⟩
  · exact dsa6_perm k hLP hP1N hPQ hBP hLnB hq hpc hQB hKB hPk hBk hcL1 hQcard hk0 hk_odd
  · intro x hx
    exact hKB x hx
  · rw [F1.inf_bigB_eq_borelOf h]
    exact hcBL1

def dsa6_KZG {G : Type} [Group G] (B Z : Subgroup G) (hZ : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) :
    Subgroup G :=
  (MonoidHom.ker (@MulAction.toPermHom ↥B ↥Z _ (dsa6_MA B Z hZ))).map B.subtype

theorem mem_dsa6_KZG {G : Type} [Group G] {B Z : Subgroup G}
    (hZ : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) {x : G} :
    x ∈ dsa6_KZG B Z hZ ↔ x ∈ B ∧ ∀ z ∈ Z, x * z = z * x := by
  letI := dsa6_MA B Z hZ
  constructor
  · intro hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨b.2, fun z hz => ?_⟩
    have h1 := MonoidHom.mem_ker.mp hb
    have h2 : ∀ w : ↥Z, ((b : G) * (w : G) * (b : G)⁻¹) = w := by
      intro w
      have h3 : (MulAction.toPermHom ↥B ↥Z) b w = w := by
        rw [h1]
        rfl
      have h4 : (b • w : ↥Z) = w := h3
      exact congrArg Subtype.val h4
    have h4 : (b : G) * z * (b : G)⁻¹ = z := h2 ⟨z, hz⟩
    calc (b : G) * z = ((b : G) * z * (b : G)⁻¹) * (b : G) := by group
      _ = z * (b : G) := by rw [h4]
  · rintro ⟨hxB, hc⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxB⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    apply Equiv.ext
    intro w
    apply Subtype.ext
    simp only [MulAction.toPermHom_apply, Equiv.Perm.one_apply]
    change (x : G) * (w : G) * (x : G)⁻¹ = (w : G)
    rw [hc w w.2]
    group

theorem dsa6_orbit {G : Type} [Group G] [Finite G] {Z : Subgroup G} (hZ4 : Nat.card Z = 4) {y : G}
    (hy3 : y * y * y = 1) (hyZ : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z) {c : G} (hc : c ∈ Z) (hc1 : c ≠ 1)
    (hcy : y * c = c * y) {z : G} (hz : z ∈ Z) : y * z = z * y := by
  by_contra hzy
  set σ : G → G := fun x => y * x * y⁻¹ with hσ
  have hσinj : ∀ a b : G, σ a = σ b → a = b := by
    intro a b h
    simp only [hσ] at h
    have h' := congrArg (fun x => y⁻¹ * x * y) h
    simpa [mul_assoc] using h'
  have hσ3 : ∀ x, σ (σ (σ x)) = x := by
    intro x
    simp only [hσ]
    have e : y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * x * (y * y * y)⁻¹ := by group
    rw [e, hy3]
    group
  have hσc : σ c = c := by
    simp only [hσ]
    rw [hcy]
    group
  have hσ1 : σ 1 = 1 := by
    simp only [hσ]
    group
  have hσz : σ z ≠ z := by
    intro h
    apply hzy
    simp only [hσ] at h
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [h]
  have hwZ : σ z ∈ Z := hyZ z hz
  have hw2Z : σ (σ z) ∈ Z := hyZ _ hwZ
  have a2 : z ≠ 1 := by
    intro h
    apply hσz
    rw [h, hσ1]
  have a3 : σ z ≠ 1 := by
    intro h
    apply a2
    apply hσinj
    rw [h, hσ1]
  have a4 : σ (σ z) ≠ 1 := by
    intro h
    apply a3
    apply hσinj
    rw [h, hσ1]
  have a5 : z ≠ c := by
    intro h
    apply hσz
    rw [h]
    exact hσc
  have a6 : σ z ≠ c := by
    intro h
    have h2 : σ (σ z) = σ z := by rw [h, hσc]
    apply hσz
    apply hσinj
    rw [h2]
  have a7 : σ (σ z) ≠ c := by
    intro h
    apply a5
    have h3 : σ (σ (σ z)) = σ c := by rw [h]
    rw [hσ3 z, hσc] at h3
    exact h3
  have a8 : σ (σ z) ≠ z := by
    intro h
    apply hσz
    have h3 : σ (σ (σ z)) = σ z := by rw [h]
    rw [hσ3 z] at h3
    exact h3.symm
  have a9 : σ z ≠ σ (σ z) := by
    intro h
    apply hσz
    apply hσinj
    exact h.symm
  have hset : ({1, c, z, σ z, σ (σ z)} : Set G).ncard = 5 := by
    have n1 : (1 : G) ∉ ({c, z, σ z, σ (σ z)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hc1 h.symm, fun h => a2 h.symm, fun h => a3 h.symm, fun h => a4 h.symm⟩
    have n2 : c ∉ ({z, σ z, σ (σ z)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => a5 h.symm, fun h => a6 h.symm, fun h => a7 h.symm⟩
    have n3 : z ∉ ({σ z, σ (σ z)} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hσz.symm, fun h => a8 h.symm⟩
    have n4 : σ z ∉ ({σ (σ z)} : Set G) := by
      simp only [Set.mem_singleton_iff]
      exact a9
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n4, Set.ncard_singleton]
  have hsub : ({1, c, z, σ z, σ (σ z)} : Set G) ⊆ (Z : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact hc
    · exact hz
    · exact hwZ
    · exact hw2Z
  have hZc : (Z : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hZ4
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hset, hZc] at this
  omega

theorem dsa6_inter {G : Type} [Group G] [Finite G] {S M M' : Subgroup G}
    (hS : Nat.card S = 64) (hSM : S ≤ M) (hSM' : S ≤ M') (hc : Nat.card M = 192)
    (hc' : Nat.card M' = 192) (hne : M ≠ M') : M ⊓ M' = S := by
  have h1 : Nat.card ↥(M ⊓ M') ∣ 192 := by
    rw [← hc]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card S ∣ Nat.card ↥(M ⊓ M') := Subgroup.card_dvd_of_le (le_inf hSM hSM')
  rw [hS] at h2
  obtain ⟨m, hm⟩ := h2
  rw [hm] at h1
  have hmle : m ≤ 3 := by
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  interval_cases m
  · norm_num at h1
  · exact (Subgroup.eq_of_le_of_card_ge (le_inf hSM hSM') (by rw [hm, hS])).symm
  · norm_num at h1
  · exfalso
    have hIM : M ⊓ M' = M := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hm])
    have hMM' : M ≤ M' := hIM ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hMM' (by rw [hc', hc]))

theorem dsa6_count {G : Type} [Group G] [Finite G] {B S : Subgroup G} {M1 M2 M3 M4 M5 : Subgroup G}
    (hB : Nat.card B = 576) (hS : Nat.card S = 64) (hSB : S ≤ B)
    (hS1 : S ≤ M1) (hS2 : S ≤ M2) (hS3 : S ≤ M3) (hS4 : S ≤ M4) (hS5 : S ≤ M5)
    (hB1 : M1 ≤ B) (hB2 : M2 ≤ B) (hB3 : M3 ≤ B) (hB4 : M4 ≤ B) (hB5 : M5 ≤ B)
    (c1 : Nat.card M1 = 192) (c2 : Nat.card M2 = 192) (c3 : Nat.card M3 = 192)
    (c4 : Nat.card M4 = 192) (c5 : Nat.card M5 = 192)
    (n12 : M1 ≠ M2) (n13 : M1 ≠ M3) (n14 : M1 ≠ M4) (n15 : M1 ≠ M5) (n23 : M2 ≠ M3)
    (n24 : M2 ≠ M4) (n25 : M2 ≠ M5) (n34 : M3 ≠ M4) (n35 : M3 ≠ M5) (n45 : M4 ≠ M5) :
    False := by
  have hdis : ∀ M M' : Subgroup G, M ⊓ M' = S → Disjoint ((M : Set G) \ (S : Set G))
      ((M' : Set G) \ (S : Set G)) := by
    intro M M' h
    rw [Set.disjoint_left]
    intro x hx hx'
    have hxS : x ∈ M ⊓ M' := ⟨hx.1, hx'.1⟩
    rw [h] at hxS
    exact hx.2 hxS
  have hsd : ∀ M : Subgroup G, S ≤ M → Nat.card M = 192 →
      ((M : Set G) \ (S : Set G)).ncard = 128 := by
    intro M hSM hMc
    have hdisj : Disjoint ((M : Set G) \ (S : Set G)) (S : Set G) := Set.disjoint_sdiff_left
    have hunion : ((M : Set G) \ (S : Set G)) ∪ (S : Set G) = (M : Set G) :=
      Set.diff_union_of_subset hSM
    have h1 := Set.ncard_union_eq hdisj
    rw [hunion] at h1
    have hMn : (M : Set G).ncard = 192 := by
      rw [← Nat.card_coe_set_eq]
      exact hMc
    have hSn : (S : Set G).ncard = 64 := by
      rw [← Nat.card_coe_set_eq]
      exact hS
    omega
  have e1 := dsa6_inter hS hS1 hS2 c1 c2 n12
  have e2 := dsa6_inter hS hS1 hS3 c1 c3 n13
  have e3 := dsa6_inter hS hS1 hS4 c1 c4 n14
  have e4 := dsa6_inter hS hS1 hS5 c1 c5 n15
  have e5 := dsa6_inter hS hS2 hS3 c2 c3 n23
  have e6 := dsa6_inter hS hS2 hS4 c2 c4 n24
  have e7 := dsa6_inter hS hS2 hS5 c2 c5 n25
  have e8 := dsa6_inter hS hS3 hS4 c3 c4 n34
  have e9 := dsa6_inter hS hS3 hS5 c3 c5 n35
  have e10 := dsa6_inter hS hS4 hS5 c4 c5 n45
  have d12 := hdis M1 M2 e1
  have d13 := hdis M1 M3 e2
  have d14 := hdis M1 M4 e3
  have d15 := hdis M1 M5 e4
  have d23 := hdis M2 M3 e5
  have d24 := hdis M2 M4 e6
  have d25 := hdis M2 M5 e7
  have d34 := hdis M3 M4 e8
  have d35 := hdis M3 M5 e9
  have d45 := hdis M4 M5 e10
  have hU1 : (((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)).ncard = 256 := by
    rw [Set.ncard_union_eq d12, hsd M1 hS1 c1, hsd M2 hS2 c2]
  have hd3 : Disjoint (((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)) ((M3 : Set G) \ S) :=
    Set.disjoint_union_left.mpr ⟨d13, d23⟩
  have hU2 : ((((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)) ∪ ((M3 : Set G) \ S)).ncard = 384 := by
    rw [Set.ncard_union_eq hd3, hU1, hsd M3 hS3 c3]
  have hd4 : Disjoint ((((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)) ∪ ((M3 : Set G) \ S))
      ((M4 : Set G) \ S) :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨d14, d24⟩, d34⟩
  have hU3 : (((((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)) ∪ ((M3 : Set G) \ S)) ∪
      ((M4 : Set G) \ S)).ncard = 512 := by
    rw [Set.ncard_union_eq hd4, hU2, hsd M4 hS4 c4]
  have hd5 : Disjoint (((((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)) ∪ ((M3 : Set G) \ S)) ∪
      ((M4 : Set G) \ S)) ((M5 : Set G) \ S) :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨d15, d25⟩, d35⟩, d45⟩
  have hU5 : (((((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)) ∪ ((M3 : Set G) \ S)) ∪
      ((M4 : Set G) \ S) ∪ ((M5 : Set G) \ S)).ncard = 640 := by
    rw [Set.ncard_union_eq hd5, hU3, hsd M5 hS5 c5]
  have hsub : (((((M1 : Set G) \ S) ∪ ((M2 : Set G) \ S)) ∪ ((M3 : Set G) \ S)) ∪
      ((M4 : Set G) \ S) ∪ ((M5 : Set G) \ S)) ⊆ (B : Set G) \ (S : Set G) := by
    intro x hx
    rcases hx with (((hx | hx) | hx) | hx) | hx
    · exact ⟨hB1 hx.1, hx.2⟩
    · exact ⟨hB2 hx.1, hx.2⟩
    · exact ⟨hB3 hx.1, hx.2⟩
    · exact ⟨hB4 hx.1, hx.2⟩
    · exact ⟨hB5 hx.1, hx.2⟩
  have hBS : ((B : Set G) \ (S : Set G)).ncard = 512 := by
    have hdisj : Disjoint ((B : Set G) \ (S : Set G)) (S : Set G) := Set.disjoint_sdiff_left
    have hunion : ((B : Set G) \ (S : Set G)) ∪ (S : Set G) = (B : Set G) :=
      Set.diff_union_of_subset hSB
    have h1 := Set.ncard_union_eq hdisj
    rw [hunion] at h1
    have hBn : (B : Set G).ncard = 576 := by
      rw [← Nat.card_coe_set_eq]
      exact hB
    have hSn : (S : Set G).ncard = 64 := by
      rw [← Nat.card_coe_set_eq]
      exact hS
    omega
  have hle := Set.ncard_le_ncard hsub
  rw [hU5, hBS] at hle
  omega

theorem dsa6_k_dvd {G : Type} [Group G] [Finite G] {B K Q Z : Subgroup G} (k : ℕ)
    (hZB : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) (hZ4 : Nat.card Z = 4)
    (hKB : K ≤ B) (hK : Nat.card K = 16 * k) (hQK : Q ≤ K) (hQB : Q ≤ B)
    (hQcard : Nat.card Q = 16) (hQZ : ∀ q ∈ Q, ∀ z ∈ Z, q * z = z * q)
    (hKZ : ∀ c ∈ K, (∀ z ∈ Z, c * z = z * c) → c ∈ Q) : k ∣ 24 := by
  letI := dsa6_MA B Z hZB
  set ψ : ↥(K.subgroupOf B) →* Equiv.Perm ↥Z :=
    (MulAction.toPermHom ↥B ↥Z).comp (K.subgroupOf B).subtype with hψ
  have hf : Function.Injective (B.subtype.comp (K.subgroupOf B).subtype : ↥(K.subgroupOf B) →* G) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hmapQ : ψ.ker.map (B.subtype.comp (K.subgroupOf B).subtype : ↥(K.subgroupOf B) →* G) = Q := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : (MulAction.toPermHom ↥B ↥Z) (x.1) = 1 := MonoidHom.mem_ker.mp hx
      have hcen : ∀ z ∈ Z, ((x : G) * z = z * (x : G)) := by
        intro z hz
        have h2 : ∀ w : ↥Z, ((x : G) * (w : G) * (x : G)⁻¹) = w := by
          intro w
          have h3 : (MulAction.toPermHom ↥B ↥Z) x.1 w = w := by
            rw [hx1]
            rfl
          have h4 : (x.1 • w : ↥Z) = w := h3
          exact congrArg Subtype.val h4
        have h4 : (x : G) * z * (x : G)⁻¹ = z := h2 ⟨z, hz⟩
        calc (x : G) * z = ((x : G) * z * (x : G)⁻¹) * (x : G) := by group
          _ = z * (x : G) := by rw [h4]
      have hxK : ((x : ↥B) : G) ∈ K := Subgroup.mem_subgroupOf.mp x.2
      exact hKZ _ hxK hcen
    · intro hq
      refine ⟨⟨⟨q, hQB hq⟩, Subgroup.mem_subgroupOf.mpr (hQK hq)⟩, ?_, rfl⟩
      refine MonoidHom.mem_ker.mpr ?_
      apply Equiv.ext
      intro w
      apply Subtype.ext
      simp only [MulAction.toPermHom_apply, Equiv.Perm.one_apply]
      change (q : G) * (w : G) * (q : G)⁻¹ = (w : G)
      rw [hQZ q hq w w.2]
      group
  have hker_card : Nat.card ψ.ker = 16 := by
    rw [← hQcard, ← hmapQ, Subgroup.card_map_of_injective hf]
  have hKBcard : Nat.card ↥(K.subgroupOf B) = 16 * k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKB).toEquiv, hK]
  have h1 := ψ.ker.card_mul_index
  rw [hker_card, hKBcard] at h1
  have hidx : ψ.ker.index = k := by omega
  have hrange : Nat.card ψ.range = k := (Subgroup.index_ker ψ).symm.trans hidx
  have h24 : Nat.card (Equiv.Perm ↥Z) = 24 := by
    rw [Nat.card_perm, hZ4]
    rfl
  have hdvd := Subgroup.card_subgroup_dvd_card ψ.range
  rw [hrange, h24] at hdvd
  exact hdvd

theorem dsa6_D1 {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hcB : Nat.card (bigB L1 L2 S) = 576) (hcB1 : Nat.card ↥(L1 ⊓ bigB L1 L2 S) = 192)
    (hS1 : S ≤ L1) (hSB : S ≤ bigB L1 L2 S)
    (hB1eq : L1 ⊓ bigB L1 L2 S = borelOf L1 S) (hB2eq : L2 ⊓ bigB L1 L2 S = borelOf L2 S) :
    L1 ⊓ bigB L1 L2 S ≠ L2 ⊓ bigB L1 L2 S := by
  intro heq
  have hsub : bigB L1 L2 S ≤ L1 ⊓ bigB L1 L2 S := by
    show borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ L1 ⊓ bigB L1 L2 S
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_inf (F1.borelOf_le L1 S) (le_sup_left.trans le_sup_left)
    · rw [← hB2eq, heq]
    · exact le_inf hS1 hSB
  have heqB : bigB L1 L2 S = L1 ⊓ bigB L1 L2 S := le_antisymm hsub inf_le_right
  rw [heqB] at hcB
  omega

theorem dsa6_D2 {G : Type} [Group G] [Finite G] {L B Q Z : Subgroup G}
    (hZB : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) (hNat : NatSec L ⊥ Q) (hZQ : Z ≤ Q)
    (hZ4 : Nat.card Z = 4) (hc : Nat.card ↥(L ⊓ B) = 192) :
    L ⊓ B ≠ dsa6_KZG B Z hZB := by
  intro heq
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥(L ⊓ B)) (by rw [hc]; norm_num)
  have hdL : ((x : ↥(L ⊓ B)) : G) ∈ L := (Subgroup.mem_inf.mp x.2).1
  have hdB : ((x : ↥(L ⊓ B)) : G) ∈ B := (Subgroup.mem_inf.mp x.2).2
  have hord : orderOf ((x : ↥(L ⊓ B)) : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hK : ((x : ↥(L ⊓ B)) : G) ∈ dsa6_KZG B Z hZB := by
    rw [← heq]
    exact x.2
  have hcen := ((mem_dsa6_KZG hZB).mp hK).2
  have hZne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ4
    norm_num at hZ4
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hzZ : (z : G) ∈ Z := z.2
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
  have hfix := hNat _ hdL hord (z : G) (hZQ hzZ)
  have hzd : (z : G) * ((x : ↥(L ⊓ B)) : G) = ((x : ↥(L ⊓ B)) : G) * (z : G) :=
    (hcen (z : G) hzZ).symm
  have hcomm : ⁅(z : G), ((x : ↥(L ⊓ B)) : G)⁆ ∈ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot, commutatorElement_def]
    rw [hzd]
    group
  exact hz1 (Subgroup.mem_bot.mp (hfix hcomm))

theorem dsa6_D3 {G : Type} [Group G] [Finite G] {L B K Q S : Subgroup G}
    (hKL : K ⊓ L ≤ Q) (hQ : Nat.card Q = 16) (hK : Nat.card K = 48) :
    L ⊓ B ≠ K ⊔ S := by
  intro heq
  have h1 : K ≤ L ⊓ B := by
    rw [heq]
    exact le_sup_left
  have hKL' : K ≤ L := h1.trans inf_le_left
  have hle : K ≤ Q := fun x hx => hKL ⟨hx, hKL' hx⟩
  have := Subgroup.card_le_of_le hle
  omega

theorem dsa6_D6 {G : Type} [Group G] [Finite G] {B K Q S Z : Subgroup G}
    (hZB : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z)
    (hKZ : ∀ c ∈ K, (∀ z ∈ Z, c * z = z * c) → c ∈ Q) (hQ : Nat.card Q = 16)
    (hK : Nat.card K = 48) : K ⊔ S ≠ dsa6_KZG B Z hZB := by
  intro heq
  have h1 : K ≤ dsa6_KZG B Z hZB := by
    rw [← heq]
    exact le_sup_left
  have hle : K ≤ Q := fun c hc =>
    hKZ c hc (fun z hz => ((mem_dsa6_KZG hZB).mp (h1 hc)).2 z hz)
  have := Subgroup.card_le_of_le hle
  omega

theorem dsa6_D4 {G : Type} [Group G] [Finite G] {L1 L2 B Q1 Q2 K2 S : Subgroup G}
    (hNat1 : NatSec L1 ⊥ Q1) (hab1 : ∀ x ∈ Q1, ∀ y ∈ Q1, x * y = y * x)
    (hsq1 : ∀ x ∈ Q1, x ^ 2 = 1) (hcQ1 : Nat.card Q1 = 16) (hZ4 : Nat.card ↥(Q1 ⊓ Q2) = 4)
    (hL1N : L1 ≤ Subgroup.normalizer (Q1 : Set G))
    (hK2N : ∀ y ∈ K2, y ∈ Subgroup.normalizer (Q2 : Set G))
    (hK2c : ∀ y ∈ K2, ∀ l ∈ L2, ⁅y, l⁆ ∈ Q2) (hK2card : Nat.card K2 = 48)
    (hQ1L2 : Q1 ≤ L2) (heq : L1 ⊓ B = K2 ⊔ S) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hK2L1 : K2 ≤ L1 := by
    have h1 : K2 ≤ L1 ⊓ B := by
      rw [heq]
      exact le_sup_left
    exact h1.trans inf_le_left
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥K2) (by rw [hK2card]; norm_num)
  set y : G := (x : G) with hy
  have hyK2 : y ∈ K2 := x.2
  have hyL1 : y ∈ L1 := hK2L1 hyK2
  have hord : orderOf y = 3 := by
    rw [hy, Subgroup.orderOf_coe]
    exact hx
  have hy3 : y * y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hord] at h
    simpa [pow_succ, mul_assoc] using h
  have hyR : ∀ r ∈ Q1, y * r * y⁻¹ ∈ Q1 := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hL1N hyL1) r).mp hr
  have hyQ2 : ∀ r ∈ Q2, y * r * y⁻¹ ∈ Q2 := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hK2N y hyK2) r).mp hr
  have hZy : ∀ z ∈ Q1 ⊓ Q2, y * z * y⁻¹ ∈ Q1 ⊓ Q2 := fun z hz =>
    Subgroup.mem_inf.mpr ⟨hyR z hz.1, hyQ2 z hz.2⟩
  have hZv : ∀ r ∈ Q1, y * r * y⁻¹ * r⁻¹ ∈ Q1 ⊓ Q2 := by
    intro r hr
    refine Subgroup.mem_inf.mpr ⟨Q1.mul_mem (hyR r hr) (Q1.inv_mem hr), ?_⟩
    have e : y * r * y⁻¹ * r⁻¹ = ⁅y, r⁆ := by rw [commutatorElement_def]
    rw [e]
    exact hK2c y hyK2 r (hQ1L2 hr)
  have hvex : ∃ v ∈ Q1, v ∉ Q1 ⊓ Q2 := by
    by_contra hcon
    push Not at hcon
    have hle : Q1 ≤ Q1 ⊓ Q2 := fun v hv => hcon v hv
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨v, hvQ1, hvZ⟩ := hvex
  obtain ⟨w, hwQ1, hw1, hwy⟩ := dsa6_fixpt hab1 hsq1 hy3 hyR inf_le_left hZy hZv hvQ1 hvZ
  have hcomm : ⁅w, y⁆ ∈ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc w * y * w⁻¹ * y⁻¹ = (w * y) * w⁻¹ * y⁻¹ := rfl
      _ = (y * w) * w⁻¹ * y⁻¹ := by rw [hwy]
      _ = 1 := by group
  exact hw1 (Subgroup.mem_bot.mp (hNat1 y hyL1 hord w hwQ1 hcomm))

theorem dsa6_inv' {G : Type} [Group G] {Q : Subgroup G} {c : G}
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {L : Subgroup G} (hcQ : ∀ l ∈ L, ⁅c, l⁆ ∈ Q)
    {q : G} (hqC : c * q = q * c) (hqQ : q ∈ Q) {l : G} (hl : l ∈ L) :
    c * (l⁻¹ * q * l) = (l⁻¹ * q * l) * c := by
  have hcomQ : ⁅c, l⁆ ∈ Q := hcQ l hl
  have hcl : c * l * c⁻¹ = ⁅c, l⁆ * l := by
    simp only [commutatorElement_def]
    group
  have hcomm_eq : ⁅c, l⁆ * q = q * ⁅c, l⁆ := hab _ hcomQ _ hqQ
  have e2 : c * q * c⁻¹ = q := by rw [hqC]; group
  have hxconj : c * (l⁻¹ * q * l) * c⁻¹ = l⁻¹ * q * l := by
    have e1 : c * (l⁻¹ * q * l) * c⁻¹ = (c * l * c⁻¹)⁻¹ * (c * q * c⁻¹) * (c * l * c⁻¹) := by
      group
    rw [e1, hcl, e2]
    have e3 : ⁅c, l⁆⁻¹ * q * ⁅c, l⁆ = q := by
      rw [mul_assoc, ← hcomm_eq, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (⁅c, l⁆ * l)⁻¹ * q * (⁅c, l⁆ * l) = l⁻¹ * (⁅c, l⁆⁻¹ * q * ⁅c, l⁆) * l := by group
      _ = l⁻¹ * q * l := by rw [e3]
  calc c * (l⁻¹ * q * l) = (c * (l⁻¹ * q * l) * c⁻¹) * c := by group
    _ = (l⁻¹ * q * l) * c := by rw [hxconj]

theorem dsa6_card_le_four {G : Type} [Group G] [Finite G] {Q W Z : Subgroup G}
    (hWQ : W ≤ Q) (hZQ : Z ≤ Q) (hWZ : ∀ c ∈ W, c ∈ Z → c = 1)
    (hZ : Nat.card Z = 4) (hQ : Nat.card Q = 16) : Nat.card W ≤ 4 := by
  let f : ↥W × ↥Z → ↥Q := fun p => ⟨(p.1 : G) * (p.2 : G), Q.mul_mem (hWQ p.1.2) (hZQ p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨w, z⟩ ⟨w', z'⟩ h
    have h' : (w : G) * (z : G) = (w' : G) * (z' : G) := congrArg Subtype.val h
    have h1 : (w' : G)⁻¹ * (w : G) = 1 := by
      apply hWZ _ (W.mul_mem (W.inv_mem w'.2) w.2)
      have hc : (w' : G)⁻¹ * (w : G) = (z' : G) * (z : G)⁻¹ := by
        calc (w' : G)⁻¹ * (w : G) = (w' : G)⁻¹ * ((w : G) * (z : G)) * (z : G)⁻¹ := by group
          _ = (w' : G)⁻¹ * ((w' : G) * (z' : G)) * (z : G)⁻¹ := by rw [h']
          _ = (z' : G) * (z : G)⁻¹ := by group
      rw [hc]
      exact Z.mul_mem z'.2 (Z.inv_mem z.2)
    have hww : (w : G) = (w' : G) := (inv_mul_eq_one.mp h1).symm
    have hzz : (z : G) = (z' : G) := by
      apply mul_left_cancel (a := (w : G))
      rw [h', hww]
    exact Prod.ext (Subtype.ext hww) (Subtype.ext hzz)
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, hZ, hQ] at hcard
  omega

theorem dsa6_A5_fixed {G : Type} [Group G] [Finite G] {L W : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hL : Nat.card L = 960)
    (hW : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) (hWc : Nat.card W ≤ 4) :
    ∃ x ∈ L, orderOf x = 3 ∧ ∀ w ∈ W, x * w * x⁻¹ = w := by
  classical
  letI := dsa6_MA L W hW
  set φ : ↥L →* Equiv.Perm ↥W := MulAction.toPermHom ↥L ↥W with hφ
  set K : Subgroup ↥L := φ.ker with hK
  set O : Subgroup ↥L := pCore 2 ↥L with hO
  have hKidx : K.index ∣ 24 := by
    rw [hK, Subgroup.index_ker]
    have h4 : Nat.factorial 4 = 24 := rfl
    have h1 : Nat.card (Equiv.Perm ↥W) ∣ 24 := by
      rw [Nat.card_perm, ← h4]
      exact Nat.factorial_dvd_factorial hWc
    exact (Subgroup.card_subgroup_dvd_card _).trans h1
  obtain ⟨ψ⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  have hsimp : IsSimpleGroup (oTwoQuot ↥L) := ψ.isSimpleGroup
  set π : ↥L →* (↥L ⧸ O) := QuotientGroup.mk' O with hπ
  haveI hKn : K.Normal := MonoidHom.normal_ker φ
  haveI hN : (K.map π).Normal := Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective O)
  have htop : K.map π = ⊤ := by
    rcases hsimp.eq_bot_or_eq_top_of_normal (K.map π) with hbot | htop
    · exfalso
      have hKO : K ≤ O := by
        intro k hk
        have hmem : π k ∈ K.map π := Subgroup.mem_map_of_mem π hk
        rw [hbot, Subgroup.mem_bot] at hmem
        exact (QuotientGroup.eq_one_iff k).mp hmem
      have h60 : O.index = 60 := dsa6_card_quot hq
      have hdvd : O.index ∣ K.index := Subgroup.index_dvd_of_le hKO
      have h24 := hdvd.trans hKidx
      rw [h60] at h24
      have := Nat.le_of_dvd (by norm_num) h24
      omega
    · exact htop
  have hdec : ∀ l : ↥L, ∃ k ∈ K, ∃ o ∈ O, l = k * o := by
    intro l
    have hl : π l ∈ K.map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp hl
    refine ⟨k, hk, k⁻¹ * l, ?_, by group⟩
    have h1 : π (k⁻¹ * l) = 1 := by rw [map_mul, map_inv, hkl, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨x3, hx3⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥L) (by rw [hL]; norm_num)
  obtain ⟨k, hk, o, ho, hxo⟩ := hdec x3
  have hP : IsPGroup 2 ↥O := CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hP ⟨o, ho⟩
  have hn1 : o ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hkφ : φ k = 1 := (MonoidHom.mem_ker).mp hk
  have hx1 : φ x3 = φ o := by
    rw [hxo, map_mul, hkφ, one_mul]
  have hx3p : x3 ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x3
  have h3 : (φ x3) ^ 3 = 1 := by rw [← map_pow, hx3p, map_one]
  have hn' : (φ x3) ^ (2 ^ n) = 1 := by rw [hx1, ← map_pow, hn1, map_one]
  have hd1 := orderOf_dvd_of_pow_eq_one h3
  have hd2 := orderOf_dvd_of_pow_eq_one hn'
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hg : orderOf (φ x3) ∣ 1 := by
    have := Nat.dvd_gcd hd1 hd2
    rwa [Nat.Coprime.gcd_eq_one hcop] at this
  have h1 : φ x3 = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  refine ⟨(x3 : G), x3.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hx3
  · intro w hw
    have h2 := DFunLike.congr_fun h1 (⟨w, hw⟩ : ↥W)
    have h3' : (x3 • (⟨w, hw⟩ : ↥W) : ↥W) = ⟨w, hw⟩ := h2
    exact congrArg Subtype.val h3'

theorem dsa6_noCent {G : Type} [Group G] [Finite G] {L B Q Z : Subgroup G}
    (hNat : NatSec L ⊥ Q) (hZQ : Z ≤ Q) (hZ4 : Nat.card Z = 4) (hc : Nat.card ↥(L ⊓ B) = 192)
    (hcent : ∀ x ∈ L ⊓ B, ∀ z ∈ Z, x * z = z * x) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥(L ⊓ B)) (by rw [hc]; norm_num)
  have hxL : ((x : ↥(L ⊓ B)) : G) ∈ L := (Subgroup.mem_inf.mp x.2).1
  have hxord : orderOf ((x : ↥(L ⊓ B)) : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hZbot : Z ≤ ⊥ := by
    intro z hz
    apply hNat _ hxL hxord z (hZQ hz)
    have e := hcent _ x.2 z hz
    rw [commutatorElement_def]
    calc z * (x : G) * z⁻¹ * (x : G)⁻¹ = (z * (x : G)) * z⁻¹ * (x : G)⁻¹ := rfl
      _ = ((x : G) * z) * z⁻¹ * (x : G)⁻¹ := by rw [← e]
      _ = 1 := by group
  have h1 := Subgroup.card_le_of_le hZbot
  rw [Subgroup.card_bot, hZ4] at h1
  omega

theorem dsa6_KS_card192 {G : Type} [Group G] [Finite G] {K S Q : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (K : Set G)) (hcS : Nat.card S = 64) (hK : Nat.card K = 48)
    (hKS : K ⊓ S = Q) (hQ : Nat.card Q = 16) : Nat.card ↥(K ⊔ S) = 192 := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hSN
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hSN
  have hc1 : Nat.card (K.subgroupOf S) = 16 := by
    have h1 : Nat.card ((K.subgroupOf S).map S.subtype) = Nat.card (K.subgroupOf S) :=
      Subgroup.card_map_of_injective S.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, hKS, hQ] at h1
    omega
  have hidxS : (K.subgroupOf S).index = 4 := by
    have h := (K.subgroupOf S).card_mul_index
    rw [hc1] at h
    have h' : Nat.card ↥S = 64 := hcS
    omega
  have e1 := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient S K hSN).toEquiv
  have e2 : S ⊔ K = K ⊔ S := sup_comm _ _
  rw [e2] at e1
  have c1 : Nat.card (↥S ⧸ K.subgroupOf S) = (K.subgroupOf S).index := rfl
  have c2 : Nat.card (↥(K ⊔ S) ⧸ K.subgroupOf (K ⊔ S)) = (K.subgroupOf (K ⊔ S)).index := rfl
  rw [c1, c2] at e1
  have hidxK : (K.subgroupOf (K ⊔ S)).index = 4 := by rw [← e1, hidxS]
  have hKK : Nat.card (K.subgroupOf (K ⊔ S)) = 48 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ S)).toEquiv, hK]
  have h := (K.subgroupOf (K ⊔ S)).card_mul_index
  rw [hKK, hidxK] at h
  omega

theorem dsa6_arith (n r : ℕ) (hr : r ∣ 24) (hnr : n * r = 576) (hn : 64 ∣ n) :
    n = 192 ∨ n = 576 := by
  obtain ⟨m, rfl⟩ := hn
  have hmr' : 64 * (m * r) = 64 * 9 := by
    have : 64 * m * r = 576 := hnr
    rw [show 64 * (m * r) = 64 * m * r by ring, this]
  have hmr : m * r = 9 := by omega
  have hr9 : r ∣ 9 := Dvd.intro_left m hmr
  have hr3 : r ∣ 3 := by
    have := Nat.dvd_gcd hr hr9
    norm_num at this
    exact this
  have hr_le : r ≤ 3 := Nat.le_of_dvd (by norm_num) hr3
  interval_cases r
  · simp at hnr
  · right
    omega
  · norm_num at hr3
  · left
    omega

theorem dsa6_KZG_card192 {G : Type} [Group G] [Finite G] {B S Q1 Q2 L : Subgroup G}
    (hZB : ∀ b ∈ B, ∀ z ∈ Q1 ⊓ Q2, b * z * b⁻¹ ∈ Q1 ⊓ Q2) (hZ4 : Nat.card ↥(Q1 ⊓ Q2) = 4)
    (hcB : Nat.card B = 576) (hcS : Nat.card S = 64) (hSB : S ≤ B)
    (hScent : ∀ s ∈ S, ∀ z ∈ Q1 ⊓ Q2, s * z = z * s)
    (hNat : NatSec L ⊥ Q1) (hLB : Nat.card ↥(L ⊓ B) = 192) :
    Nat.card (dsa6_KZG B (Q1 ⊓ Q2) hZB) = 192 := by
  obtain ⟨hdiv, hr⟩ := dsa6_KZ_card B (Q1 ⊓ Q2) hZB hZ4
  have hKZG : Nat.card (dsa6_KZG B (Q1 ⊓ Q2) hZB) *
      Nat.card (@MulAction.toPermHom ↥B ↥(Q1 ⊓ Q2) _ (dsa6_MA B (Q1 ⊓ Q2) hZB)).range = 576 := by
    rw [← hcB]
    exact hdiv
  have hSK : S ≤ dsa6_KZG B (Q1 ⊓ Q2) hZB := by
    intro s hs
    rw [mem_dsa6_KZG]
    exact ⟨hSB hs, fun z hz => hScent s hs z hz⟩
  have hdvdS : 64 ∣ Nat.card (dsa6_KZG B (Q1 ⊓ Q2) hZB) := by
    have h := Subgroup.card_dvd_of_le hSK
    rwa [hcS] at h
  rcases dsa6_arith _ _ hr hKZG hdvdS with h192 | h576
  · exact h192
  · exfalso
    have hle : dsa6_KZG B (Q1 ⊓ Q2) hZB ≤ B := fun x hx => ((mem_dsa6_KZG hZB).mp hx).1
    have hcard : Nat.card ↥B ≤ Nat.card ↥(dsa6_KZG B (Q1 ⊓ Q2) hZB) := by
      rw [hcB, h576]
    have hKB : dsa6_KZG B (Q1 ⊓ Q2) hZB = B := Subgroup.eq_of_le_of_card_ge hle hcard
    apply dsa6_noCent hNat inf_le_left hZ4 hLB
    intro x hx z hz
    have hxB : x ∈ dsa6_KZG B (Q1 ⊓ Q2) hZB := by
      rw [hKB]
      exact (Subgroup.mem_inf.mp hx).2
    exact ((mem_dsa6_KZG hZB).mp hxB).2 z hz

theorem dsa6_D8 {G : Type} [Group G] [Finite G] {L1 L2 S Q1 Q2 K1 K2 : Subgroup G}
    (hab2 : ∀ x ∈ Q2, ∀ y ∈ Q2, x * y = y * x) (hsq2 : ∀ x ∈ Q2, x ^ 2 = 1)
    (hcQ2 : Nat.card Q2 = 16) (hZ4 : Nat.card ↥(Q1 ⊓ Q2) = 4)
    (hdec : ∀ x ∈ S, ∃ a ∈ Q1, ∃ b ∈ Q2, x = a * b)
    (hQ2S : Q2 ≤ S) (hS1 : S ≤ L1) (hQ2L2 : Q2 ≤ L2)
    (hL2N : L2 ≤ Subgroup.normalizer (Q2 : Set G))
    (hN1 : S ≤ Subgroup.normalizer (Q1 : Set G))
    (hSK1 : S ≤ Subgroup.normalizer (K1 : Set G))
    (hK1N : ∀ a ∈ K1, a ∈ Subgroup.normalizer (Q1 : Set G))
    (hK1c : ∀ a ∈ K1, ∀ l ∈ L1, ⁅a, l⁆ ∈ Q1)
    (hK2N : ∀ y ∈ K2, y ∈ Subgroup.normalizer (Q2 : Set G))
    (hK2c : ∀ y ∈ K2, ∀ l ∈ L2, ⁅y, l⁆ ∈ Q2)
    (hK2B : ∀ y ∈ K2, y ∈ Subgroup.normalizer (Q1 : Set G))
    (hK2card : Nat.card K2 = 48)
    (hKZ2 : ∀ c ∈ K2, (∀ z ∈ Q1 ⊓ Q2, c * z = z * c) → c ∈ Q2)
    (hq2 : IsL2Quot 2 (oTwoQuot ↥L2)) (hcardL2 : Nat.card L2 = 960)
    (hnat2 : NatSec L2 ⊥ Q2)
    (heq : K1 ⊔ S = K2 ⊔ S) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x3, hx3⟩ := exists_prime_orderOf_dvd_card' 3 (G := ↥K2) (by rw [hK2card]; norm_num)
  set y : G := (x3 : G) with hy
  have hyK2 : y ∈ K2 := x3.2
  have hord : orderOf y = 3 := by
    rw [hy, Subgroup.orderOf_coe]
    exact hx3
  have hy3 : y * y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hord] at h
    simpa [pow_succ, mul_assoc] using h
  have hyK1S : y ∈ K1 ⊔ S := by
    rw [heq]
    exact Subgroup.mem_sup_left hyK2
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K1 S hSK1
  have hmem : y ∈ (↑(K1 ⊔ S) : Set G) := hyK1S
  rw [hmul] at hmem
  obtain ⟨a, ha, s, hs, hys⟩ := Set.mem_mul.mp hmem
  have hcomQ1 : ∀ r ∈ Q2, ⁅y, r⁆ ∈ Q1 := by
    intro r hr
    have hrS : r ∈ S := hQ2S hr
    have hc : ⁅s, r⁆ ∈ Q1 := dsa6_comm_mod hdec hQ2S hN1 hab2 hs hrS
    have hd : ⁅a, r⁆ ∈ Q1 := hK1c a ha r (hS1 hrS)
    have key : ⁅y, r⁆ = (a * ⁅s, r⁆ * a⁻¹) * ⁅a, r⁆ := by
      rw [← hys]
      simp only [commutatorElement_def]
      group
    rw [key]
    exact Q1.mul_mem ((Subgroup.mem_normalizer_iff.mp (hK1N a ha) _).mp hc) hd
  have hyQ2 : ∀ r ∈ Q2, y * r * y⁻¹ ∈ Q2 := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hK2N y hyK2) r).mp hr
  have hyQ1 : ∀ r ∈ Q1, y * r * y⁻¹ ∈ Q1 := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hK2B y hyK2) r).mp hr
  have hZv : ∀ r ∈ Q2, y * r * y⁻¹ * r⁻¹ ∈ Q1 ⊓ Q2 := by
    intro r hr
    have e : y * r * y⁻¹ * r⁻¹ = ⁅y, r⁆ := by rw [commutatorElement_def]
    rw [e]
    exact Subgroup.mem_inf.mpr ⟨hcomQ1 r hr, hK2c y hyK2 r (hQ2L2 hr)⟩
  have hZy : ∀ z ∈ Q1 ⊓ Q2, y * z * y⁻¹ ∈ Q1 ⊓ Q2 := fun z hz =>
    Subgroup.mem_inf.mpr ⟨hyQ1 z hz.1, hyQ2 z hz.2⟩
  have hZnc : ∃ z0 ∈ Q1 ⊓ Q2, y * z0 ≠ z0 * y := by
    by_contra hcon
    push Not at hcon
    have hyQ2' : y ∈ Q2 := hKZ2 y hyK2 (fun z hz => hcon z hz)
    have h2 : y * y = 1 := by rw [← pow_two]; exact hsq2 y hyQ2'
    have h1 : y = 1 := by
      have h := hy3
      rw [h2, one_mul] at h
      exact h
    rw [h1, orderOf_one] at hord
    norm_num at hord
  obtain ⟨z0, hz0, hz0ne⟩ := hZnc
  have hfreeC : ∀ c ∈ Q1 ⊓ Q2, y * c = c * y → c = 1 := by
    intro c hc hcy
    by_contra hc1
    exact hz0ne (dsa6_orbit hZ4 hy3 hZy hc hc1 hcy hz0)
  have hvex : ∃ v ∈ Q2, v ∉ Q1 ⊓ Q2 := by
    by_contra hcon
    push Not at hcon
    have hle : Q2 ≤ Q1 ⊓ Q2 := fun v hv => hcon v hv
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨v, hvQ2, hvZ⟩ := hvex
  obtain ⟨w, hwQ2, hw1, hwy⟩ :=
    dsa6_fixpt hab2 hsq2 hy3 hyQ2 inf_le_right hZy hZv hvQ2 hvZ
  set W : Subgroup G := Subgroup.centralizer ({y} : Set G) ⊓ Q2 with hW
  have hmemW : ∀ q, q ∈ W ↔ y * q = q * y ∧ q ∈ Q2 := by
    intro q
    rw [hW, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1 y (Set.mem_singleton y), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact h1, h2⟩
  have hWQ : W ≤ Q2 := inf_le_right
  have hWne : ∃ w0 ∈ W, w0 ≠ 1 := ⟨w, (hmemW w).mpr ⟨hwy, hwQ2⟩, hw1⟩
  have hWZ : ∀ c ∈ W, c ∈ Q1 ⊓ Q2 → c = 1 := by
    intro c hc hcZ
    exact hfreeC c hcZ ((hmemW c).mp hc).1
  have hWc : Nat.card W ≤ 4 := dsa6_card_le_four hWQ inf_le_right hWZ hZ4 hcQ2
  have hWL : ∀ l ∈ L2, ∀ w0 ∈ W, l * w0 * l⁻¹ ∈ W := by
    intro l hl w0 hw0
    have hw0' := (hmemW w0).mp hw0
    have hQ : l * w0 * l⁻¹ ∈ Q2 := (Subgroup.mem_normalizer_iff.mp (hL2N hl) w0).mp hw0'.2
    have hcomm := dsa6_inv' hab2 (c := y) (fun l' hl' => hK2c y hyK2 l' hl') hw0'.1 hw0'.2
      (L2.inv_mem hl)
    rw [inv_inv] at hcomm
    exact (hmemW _).mpr ⟨hcomm, hQ⟩
  obtain ⟨x, hxL2, hxord, hxfix⟩ := dsa6_A5_fixed hq2 hcardL2 hWL hWc
  obtain ⟨w0, hw0, hw01⟩ := hWne
  have hxw := hxfix w0 hw0
  have hc' : x * w0 = w0 * x := by
    calc x * w0 = (x * w0 * x⁻¹) * x := by group
      _ = w0 * x := by rw [hxw]
  have hcomm : ⁅w0, x⁆ = 1 := by
    rw [commutatorElement_def]
    calc w0 * x * w0⁻¹ * x⁻¹ = (x * w0) * w0⁻¹ * x⁻¹ := by rw [← hc']
      _ = 1 := by group
  have hw0Q : w0 ∈ Q2 := ((hmemW w0).mp hw0).2
  have hbot : w0 ∈ (⊥ : Subgroup G) := hnat2 x hxL2 hxord w0 hw0Q (by rw [hcomm]; exact Subgroup.one_mem _)
  exact hw01 (Subgroup.mem_bot.mp hbot)

theorem dsa6_dec {G : Type} [Group G] {Q1 Q2 S : Subgroup G} (hsum : Q1 ⊔ Q2 = S)
    (hN : Q2 ≤ Subgroup.normalizer (Q1 : Set G)) :
    ∀ x ∈ S, ∃ a ∈ Q1, ∃ b ∈ Q2, x = a * b := by
  intro x hx
  rw [← hsum] at hx
  have hmem : x ∈ (↑(Q1 ⊔ Q2) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q1 Q2 hN] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem dsa6_S_le_KZG {G : Type} [Group G] {B S Z : Subgroup G}
    (hZB : ∀ b ∈ B, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) (hSB : S ≤ B)
    (hScent : ∀ s ∈ S, ∀ z ∈ Z, s * z = z * s) : S ≤ dsa6_KZG B Z hZB := by
  intro s hs
  rw [mem_dsa6_KZG]
  exact ⟨hSB hs, fun z hz => hScent s hs z hz⟩

theorem dsa6_k3 {G : Type} [Group G] [Finite G] {L1 L2 S Q1 Q2 K1 K2 : Subgroup G}
    (hS1 : S ≤ L1) (hS2 : S ≤ L2) (hSB : S ≤ bigB L1 L2 S)
    (hcB : Nat.card (bigB L1 L2 S) = 576) (hcS : Nat.card S = 64)
    (hsum : Q1 ⊔ Q2 = S) (hQ1S : Q1 ≤ S) (hQ2S : Q2 ≤ S)
    (hcQ1 : Nat.card Q1 = 16) (hcQ2 : Nat.card Q2 = 16) (hZ4 : Nat.card ↥(Q1 ⊓ Q2) = 4)
    (hab1 : ∀ x ∈ Q1, ∀ y ∈ Q1, x * y = y * x) (hab2 : ∀ x ∈ Q2, ∀ y ∈ Q2, x * y = y * x)
    (hsq1 : ∀ x ∈ Q1, x ^ 2 = 1) (hsq2 : ∀ x ∈ Q2, x ^ 2 = 1)
    (hNat1 : NatSec L1 ⊥ Q1) (hNat2 : NatSec L2 ⊥ Q2)
    (hBQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 : Set G))
    (hBQ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 : Set G))
    (hL1N : L1 ≤ Subgroup.normalizer (Q1 : Set G)) (hL2N : L2 ≤ Subgroup.normalizer (Q2 : Set G))
    (hQ2L1 : Q2 ≤ L1) (hQ1L2 : Q1 ≤ L2)
    (hq2 : IsL2Quot 2 (oTwoQuot ↥L2)) (hcardL2 : Nat.card L2 = 960)
    (hB1eq : L1 ⊓ bigB L1 L2 S = borelOf L1 S) (hB2eq : L2 ⊓ bigB L1 L2 S = borelOf L2 S)
    (hcL1B : Nat.card ↥(L1 ⊓ bigB L1 L2 S) = 192) (hcL2B : Nat.card ↥(L2 ⊓ bigB L1 L2 S) = 192)
    (hK1card : Nat.card K1 = 48) (hK2card : Nat.card K2 = 48)
    (hK1B : K1 ≤ bigB L1 L2 S) (hK2B : K2 ≤ bigB L1 L2 S)
    (hK1Q : Q1 ≤ K1) (hK2Q : Q2 ≤ K2)
    (hK1N : ∀ a ∈ K1, a ∈ Subgroup.normalizer (Q1 : Set G))
    (hK1c : ∀ a ∈ K1, ∀ l ∈ L1, ⁅a, l⁆ ∈ Q1) (hK1L : K1 ⊓ L1 ≤ Q1)
    (hK2N : ∀ y ∈ K2, y ∈ Subgroup.normalizer (Q2 : Set G))
    (hK2c : ∀ y ∈ K2, ∀ l ∈ L2, ⁅y, l⁆ ∈ Q2) (hK2L : K2 ⊓ L2 ≤ Q2)
    (hKZ1 : ∀ c ∈ K1, (∀ z ∈ Q1 ⊓ Q2, c * z = z * c) → c ∈ Q1)
    (hKZ2 : ∀ c ∈ K2, (∀ z ∈ Q1 ⊓ Q2, c * z = z * c) → c ∈ Q2)
    (hSK1 : S ≤ Subgroup.normalizer (K1 : Set G)) (hSK2 : S ≤ Subgroup.normalizer (K2 : Set G)) :
    False := by
  have hZB : ∀ b ∈ bigB L1 L2 S, ∀ z ∈ Q1 ⊓ Q2, b * z * b⁻¹ ∈ Q1 ⊓ Q2 := fun b hb z hz =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBQ1 hb) z).mp hz.1,
      (Subgroup.mem_normalizer_iff.mp (hBQ2 hb) z).mp hz.2⟩
  have hSN1 : S ≤ Subgroup.normalizer (Q1 : Set G) := fun s hs => hBQ1 (hSB hs)
  have hdec : ∀ x ∈ S, ∃ a ∈ Q1, ∃ b ∈ Q2, x = a * b :=
    dsa6_dec hsum (by intro q hq; exact hBQ1 (hSB (hQ2S hq)))
  have hScent : ∀ s ∈ S, ∀ z ∈ Q1 ⊓ Q2, s * z = z * s := fun s hs z hz =>
    dsa6_centS_Z hdec hab1 hab2 hs hz.1 hz.2
  have hKS1 : K1 ⊓ S = Q1 :=
    le_antisymm (fun x hx => hK1L (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
      hS1 (Subgroup.mem_inf.mp hx).2⟩)) (le_inf hK1Q hQ1S)
  have hKS2 : K2 ⊓ S = Q2 :=
    le_antisymm (fun x hx => hK2L (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
      hS2 (Subgroup.mem_inf.mp hx).2⟩)) (le_inf hK2Q hQ2S)
  have c3 : Nat.card (dsa6_KZG (bigB L1 L2 S) (Q1 ⊓ Q2) hZB) = 192 :=
    dsa6_KZG_card192 hZB hZ4 hcB hcS hSB hScent hNat1 hcL1B
  have c4 : Nat.card ↥(K1 ⊔ S) = 192 := dsa6_KS_card192 hSK1 hcS hK1card hKS1 hcQ1
  have c5 : Nat.card ↥(K2 ⊔ S) = 192 := dsa6_KS_card192 hSK2 hcS hK2card hKS2 hcQ2
  have hSM1 : S ≤ L1 ⊓ bigB L1 L2 S := le_inf hS1 hSB
  have hSM2 : S ≤ L2 ⊓ bigB L1 L2 S := le_inf hS2 hSB
  have hSM3 : S ≤ dsa6_KZG (bigB L1 L2 S) (Q1 ⊓ Q2) hZB := dsa6_S_le_KZG hZB hSB hScent
  have hBM3 : dsa6_KZG (bigB L1 L2 S) (Q1 ⊓ Q2) hZB ≤ bigB L1 L2 S :=
    fun x hx => ((mem_dsa6_KZG hZB).mp hx).1
  have n12 : L1 ⊓ bigB L1 L2 S ≠ L2 ⊓ bigB L1 L2 S :=
    dsa6_D1 hcB hcL1B hS1 hSB hB1eq hB2eq
  have n13 : L1 ⊓ bigB L1 L2 S ≠ dsa6_KZG (bigB L1 L2 S) (Q1 ⊓ Q2) hZB :=
    dsa6_D2 hZB hNat1 inf_le_left hZ4 hcL1B
  have n14 : L1 ⊓ bigB L1 L2 S ≠ K1 ⊔ S := dsa6_D3 hK1L hcQ1 hK1card
  have n15 : L1 ⊓ bigB L1 L2 S ≠ K2 ⊔ S := fun heq =>
    dsa6_D4 hNat1 hab1 hsq1 hcQ1 hZ4 hL1N hK2N hK2c hK2card hQ1L2 heq
  have n23 : L2 ⊓ bigB L1 L2 S ≠ dsa6_KZG (bigB L1 L2 S) (Q1 ⊓ Q2) hZB :=
    dsa6_D2 hZB hNat2 inf_le_right hZ4 hcL2B
  have n24 : L2 ⊓ bigB L1 L2 S ≠ K1 ⊔ S := fun heq =>
    dsa6_D4 hNat2 hab2 hsq2 hcQ2 (by rw [inf_comm]; exact hZ4) hL2N hK1N hK1c hK1card hQ2L1 heq
  have n25 : L2 ⊓ bigB L1 L2 S ≠ K2 ⊔ S := dsa6_D3 hK2L hcQ2 hK2card
  have n34 : dsa6_KZG (bigB L1 L2 S) (Q1 ⊓ Q2) hZB ≠ K1 ⊔ S :=
    Ne.symm (dsa6_D6 (S := S) hZB hKZ1 hcQ1 hK1card)
  have n35 : dsa6_KZG (bigB L1 L2 S) (Q1 ⊓ Q2) hZB ≠ K2 ⊔ S :=
    Ne.symm (dsa6_D6 (S := S) hZB hKZ2 hcQ2 hK2card)
  have n45 : K1 ⊔ S ≠ K2 ⊔ S := fun heq =>
    dsa6_D8 hab2 hsq2 hcQ2 hZ4 hdec hQ2S hS1 (hQ2S.trans hS2) hL2N
      hSN1 hSK1 hK1N hK1c hK2N hK2c (fun y hy => hBQ1 (hK2B hy)) hK2card hKZ2 hq2 hcardL2
      hNat2 heq
  exact dsa6_count hcB hcS hSB hSM1 hSM2 hSM3 (le_sup_right) (le_sup_right)
    inf_le_right inf_le_right hBM3 (sup_le hK1B hSB) (sup_le hK2B hSB)
    hcL1B hcL2B c3 c4 c5 n12 n13 n14 n15 n23 n24 n25 n34 n35 n45

theorem dsa6_comm_of_elem {G : Type} [Group G] {E : Subgroup G} (h : IsElemAbelian 2 E) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  intro x hx y hy
  have := h.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem dsa6_sq_of_elem {G : Type} [Group G] {E : Subgroup G} (h : IsElemAbelian 2 E) :
    ∀ x ∈ E, x ^ 2 = 1 := fun x hx => h.2 x hx

theorem dsa6_odd_dvd24 {k : ℕ} (hk : k ∣ 24) (ho : Odd k) : k = 1 ∨ k = 3 := by
  have hle : k ≤ 24 := Nat.le_of_dvd (by norm_num) hk
  interval_cases k
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso; revert hk ho; decide)

theorem dsa6_normalizes_K {G : Type} [Group G] {P L Q S : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hSP : S ≤ P) : S ≤ Subgroup.normalizer ((dsCentMod P L Q : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact dsa6_K_conj hPL hPQ (hSP hs) hk
  · intro hk
    have h := dsa6_K_conj hPL hPQ (P.inv_mem (hSP hs)) hk
    have e : s⁻¹ * (s * k * s⁻¹) * s⁻¹⁻¹ = k := by group
    rw [e] at h
    exact h

theorem dsa6_core [DSLeaf LeafFrattiniChief] [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIStep4]
    [DSLeaf LeafDSACaseIOffender] [DSLeaf LeafDSACaseIFrattini] [DSLeaf LeafSylowS]
    {G : Type} [Group G] [Finite4 G]
    {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S) (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥)
    (c2 : ⁅dsZi L2 S, L2⁆ ≠ ⊥) : bigB L1 L2 S ≤ L1 ⊓ L2 := by
  have hFr := dsa_case_i_frattini h c1 c2
  have hst := dsa_case_i_step4 h c1 c2
  have hoff := dsa_case_i_offender h c1 c2
  have hnf := dsa_no_field h
  have hnf' := dsa_no_field h.symm
  have hSL := dsa6_S_le h c1 c2
  have hS1 : S ≤ L1 := hSL.trans inf_le_left
  have hS2 : S ≤ L2 := hSL.trans inf_le_right
  have hsum : dsQ L1 L2 S ⊔ dsQ L2 L1 S = S := hst.1
  have hsum' : dsQ L2 L1 S ⊔ dsQ L1 L2 S = S := by rw [sup_comm]; exact hst.1
  have hcS : Nat.card S = 64 := by rw [hst.2.1]; norm_num
  have hQ1c : Nat.card (dsQ L1 L2 S) = 16 := hst.2.2.1.2
  have hQ2c : Nat.card (dsQ L2 L1 S) = 16 := hst.2.2.2.2
  have hab1 : ∀ x ∈ dsQ L1 L2 S, ∀ y ∈ dsQ L1 L2 S, x * y = y * x :=
    dsa6_comm_of_elem hst.2.2.1.1
  have hab2 : ∀ x ∈ dsQ L2 L1 S, ∀ y ∈ dsQ L2 L1 S, x * y = y * x :=
    dsa6_comm_of_elem hst.2.2.2.1
  have hsq1 : ∀ x ∈ dsQ L1 L2 S, x ^ 2 = 1 := dsa6_sq_of_elem hst.2.2.1.1
  have hsq2 : ∀ x ∈ dsQ L2 L1 S, x ^ 2 = 1 := dsa6_sq_of_elem hst.2.2.2.1
  have hZ1 : dsZi L1 S = dsQ L1 L2 S := hFr.1.symm
  have hZ2 : dsZi L2 S = dsQ L2 L1 S := hFr.2.symm
  have hNat1 : NatSec L1 ⊥ (dsQ L1 L2 S) := by rw [← hZ1]; exact hoff.2.2.1
  have hNat2 : NatSec L2 ⊥ (dsQ L2 L1 S) := by rw [← hZ2]; exact hoff.2.2.2.1
  have hZ4 : Nat.card ↥(dsQ L1 L2 S ⊓ dsQ L2 L1 S) = 4 := by
    have h4 := hoff.2.2.2.2.2.2
    rw [hZ1, hZ2] at h4
    exact h4
  have hQ1L1 : dsQ L1 L2 S ≤ L1 := dsa6_Q_le h hQ1c
  have hQ2L2 : dsQ L2 L1 S ≤ L2 := dsa6_Q_le h.symm hQ2c
  have hSylB : IsSylowTwoOf S (bigB L1 L2 S) := (sylow_s h.hyp).1
  have hSB : S ≤ bigB L1 L2 S := hSylB.1
  have hSylB' : IsSylowTwoOf S (bigB L2 L1 S) := (sylow_s h.symm.hyp).1
  have hBc : bigB L2 L1 S = bigB L1 L2 S := bigB_comm L1 L2 S
  have hQ1S : dsQ L1 L2 S ≤ S := le_sup_left.trans hsum.le
  have hQ2S : dsQ L2 L1 S ≤ S := le_sup_right.trans hsum.le
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) := (dsa6_A5Par h).quot
  have hq2 : IsL2Quot 2 (oTwoQuot ↥L2) := (dsa6_A5Par h.symm).quot
  obtain ⟨k, hko, hBk, hidx, hK1card, hK1B, hL1B, hpc1, hcL1⟩ :=
    dsa6_side h.hyp hq1 hS1 hQ1L1 hsum hQ1c (dsa_no_field h).2.2 hSylB
  obtain ⟨k2, hko2, hB2k, hidx2, hK2card, hK2B, hL2B, hpc2, hcL2⟩ :=
    dsa6_side h.symm.hyp hq2 hS2 hQ2L2 hsum' hQ2c hnf'.2.2 hSylB'
  rw [hBc] at hB2k hidx2 hK2card hK2B hL2B
  have hkk : k2 = k := by omega
  rw [hkk] at hidx2 hK2card
  have hP1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S)
  have hQ2P : dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
    unfold dsQ
    rw [hBc]
  have hP2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := by
    rw [hQ2P]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L2 ⊔ bigB L1 L2 S)
  have hBQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) := le_sup_right.trans hP1
  have hBQ2 : bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := le_sup_right.trans hP2
  have hL1N : L1 ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) := le_sup_left.trans hP1
  have hL2N : L2 ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := le_sup_left.trans hP2
  have hZQ1 : dsZ S ≤ dsQ L1 L2 S := by
    rw [← hZ1]
    exact dsZ_le_dsZi L1 S
  have hZQ2 : dsZ S ≤ dsQ L2 L1 S := by
    rw [← hZ2]
    exact dsZ_le_dsZi L2 S
  have hZQ : dsZ S ≤ dsQ L1 L2 S ⊓ dsQ L2 L1 S := le_inf hZQ1 hZQ2
  have hP1L : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    F1.parabolic_le_normalizer h.hyp
  have hP2L : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have := F1.parabolic_le_normalizer h.symm.hyp
    rw [hBc] at this
    exact this
  have hCT1 : CharTwo (L1 ⊔ bigB L1 L2 S) := F1.parabolic_charTwo h.hyp
  have hCT2 : CharTwo (L2 ⊔ bigB L1 L2 S) := by
    have := F1.parabolic_charTwo h.symm.hyp
    rw [hBc] at this
    exact this
  have hKZ1 : ∀ c ∈ dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S),
      (∀ z ∈ dsQ L1 L2 S ⊓ dsQ L2 L1 S, c * z = z * c) → c ∈ dsQ L1 L2 S := fun c hc hcZ =>
    dsa6_KZ le_sup_left hP1L hP1 rfl hCT1 hab1 hZ1 hc (fun z hz => hcZ z (hZQ hz))
  have hKZ2 : ∀ c ∈ dsCentMod (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S),
      (∀ z ∈ dsQ L1 L2 S ⊓ dsQ L2 L1 S, c * z = z * c) → c ∈ dsQ L2 L1 S := fun c hc hcZ =>
    dsa6_KZ le_sup_left hP2L hP2 hQ2P.symm hCT2 hab2 hZ2 hc (fun z hz => hcZ z (hZQ hz))
  have hK1N : ∀ a ∈ dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S),
      a ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) := fun a ha => (dsa6_mem_K.mp ha).2.1
  have hK1c : ∀ a ∈ dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S), ∀ l ∈ L1,
      ⁅a, l⁆ ∈ dsQ L1 L2 S := fun a ha l hl => (dsa6_mem_K.mp ha).2.2 l hl
  have hK2N : ∀ y ∈ dsCentMod (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S),
      y ∈ Subgroup.normalizer (dsQ L2 L1 S : Set G) := fun y hy => (dsa6_mem_K.mp hy).2.1
  have hK2c : ∀ y ∈ dsCentMod (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S), ∀ l ∈ L2,
      ⁅y, l⁆ ∈ dsQ L2 L1 S := fun y hy l hl => (dsa6_mem_K.mp hy).2.2 l hl
  have hK1L : dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S) ⊓ L1 ≤ dsQ L1 L2 S := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hQL : dsQ L1 L2 S ⊓ L1 ≤ pCoreOf 2 L1 := by
      rw [hpc1]
      exact inf_le_left
    have := dsa6_K_inf hq1 hQL hx2 (fun l hl => (dsa6_mem_K.mp hx1).2.2 l hl)
    rw [hpc1] at this
    exact this
  have hK2L : dsCentMod (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) ⊓ L2 ≤ dsQ L2 L1 S := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hQL : dsQ L2 L1 S ⊓ L2 ≤ pCoreOf 2 L2 := by
      rw [hpc2]
      exact inf_le_left
    have := dsa6_K_inf hq2 hQL hx2 (fun l hl => (dsa6_mem_K.mp hx1).2.2 l hl)
    rw [hpc2] at this
    exact this
  have hQK1 : dsQ L1 L2 S ≤ dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S) :=
    dsa6_le_K le_sup_left (FaithfulA5.pCoreOf_le_self 2 (L1 ⊔ bigB L1 L2 S)) hP1
  have hQK2 : dsQ L2 L1 S ≤ dsCentMod (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) :=
    dsa6_le_K le_sup_left (by rw [hQ2P]; exact FaithfulA5.pCoreOf_le_self 2 _) hP2
  have hSK1 : S ≤ Subgroup.normalizer ((dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S) :
      Subgroup G) : Set G) :=
    dsa6_normalizes_K hP1L hP1 (hSB.trans le_sup_right)
  have hSK2 : S ≤ Subgroup.normalizer ((dsCentMod (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) :
      Subgroup G) : Set G) :=
    dsa6_normalizes_K hP2L hP2 (hSB.trans le_sup_right)
  have hZB : ∀ b ∈ bigB L1 L2 S, ∀ z ∈ dsQ L1 L2 S ⊓ dsQ L2 L1 S,
      b * z * b⁻¹ ∈ dsQ L1 L2 S ⊓ dsQ L2 L1 S := fun b hb z hz =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBQ1 hb) z).mp hz.1,
      (Subgroup.mem_normalizer_iff.mp (hBQ2 hb) z).mp hz.2⟩
  have hk24 : k ∣ 24 :=
    dsa6_k_dvd k hZB hZ4 hK1B hK1card (hQK1) (hQ1S.trans hSB) hQ1c
      (fun q hq z hz => hab1 q hq z hz.1) hKZ1
  rcases dsa6_odd_dvd24 hk24 hko with rfl | rfl
  ·
    have hB1 : bigB L1 L2 S ≤ L1 := Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hidx)
    have hB2 : bigB L1 L2 S ≤ L2 :=
      Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp hidx2)
    exact le_inf hB1 hB2
  ·
    exfalso
    have hB576 : Nat.card (bigB L1 L2 S) = 576 := by omega
    have hB2eq : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
      have := F1.inf_bigB_eq_borelOf h.symm.hyp
      rw [hBc] at this
      exact this
    have hK2Q : dsQ L2 L1 S ≤ dsCentMod (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) := hQK2
    exact dsa6_k3 hS1 hS2 hSB hB576 hcS hsum hQ1S hQ2S hQ1c hQ2c hZ4 hab1 hab2 hsq1 hsq2
      hNat1 hNat2 hBQ1 hBQ2 hL1N hL2N (hQ2S.trans hS1) (hQ1S.trans hS2) hq2 hcL2
      (F1.inf_bigB_eq_borelOf h.hyp) hB2eq hL1B hL2B
      (by omega) (by omega) hK1B hK2B hQK1 hK2Q hK1N hK1c hK1L hK2N hK2c hK2L hKZ1 hKZ2 hSK1 hSK2

theorem leafDSAA6 [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIOffender] [DSLeaf LeafDSACaseIFrattini] [DSLeaf LeafDSACaseIStep4] [DSLeaf LeafM2] [DSLeaf LeafM3] [DSLeaf LeafSylowS] [DSLeaf LeafFrattiniChief] : LeafDSAA6 := by
  intro G _ _ L1 L2 S h c1 c2
  exact dsa6_core h c1 c2

end CFSG.GH74.QTGen4.DSGen4
