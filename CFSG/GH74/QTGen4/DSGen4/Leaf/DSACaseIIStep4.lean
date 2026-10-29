module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.G2A5Iso

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement


private def dss24a5A : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def dss24a5B : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private def dss24a5V0 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | x = 1 ∨ x = dss24a5A ∨ x = dss24a5B ∨ x = dss24a5A * dss24a5B}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      decide +kernel
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem dss24a5V0_mem (x : alternatingGroup (Fin 5)) :
    x ∈ dss24a5V0 ↔ (x = 1 ∨ x = dss24a5A ∨ x = dss24a5B ∨ x = dss24a5A * dss24a5B) :=
  Iff.rfl

private theorem dss24a5V0_card : Nat.card dss24a5V0 = 4 := by
  have hset : (dss24a5V0 : Set (alternatingGroup (Fin 5))) =
      ↑({1, dss24a5A, dss24a5B, dss24a5A * dss24a5B} : Finset (alternatingGroup (Fin 5))) := by
    ext x
    simp [dss24a5V0_mem]
  have h4 : ({1, dss24a5A, dss24a5B, dss24a5A * dss24a5B} :
      Finset (alternatingGroup (Fin 5))).card = 4 := by
    decide +kernel
  show Nat.card (dss24a5V0 : Set (alternatingGroup (Fin 5))) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, h4]

private theorem dss24a5_mem_normalizer_V0 (σ : alternatingGroup (Fin 5)) :
    σ ∈ Subgroup.normalizer (dss24a5V0 : Set (alternatingGroup (Fin 5))) ↔
      (σ : Equiv.Perm (Fin 5)) 4 = 4 := by
  rw [Subgroup.mem_normalizer_iff]
  simp only [dss24a5V0_mem]
  revert σ
  decide +kernel

private theorem dss24a5_card_normalizer_V0 :
    Nat.card (Subgroup.normalizer (dss24a5V0 : Set (alternatingGroup (Fin 5)))) = 12 := by
  have e : Nat.card (Subgroup.normalizer (dss24a5V0 : Set (alternatingGroup (Fin 5)))) =
      Nat.card {σ : alternatingGroup (Fin 5) // (σ : Equiv.Perm (Fin 5)) 4 = 4} :=
    Nat.card_congr (Equiv.subtypeEquivRight dss24a5_mem_normalizer_V0)
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem dss24a5_card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem dss24a5_index_odd (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 4) : ¬ 2 ∣ W.index := by
  have h := Subgroup.card_mul_index W
  rw [hW, dss24a5_card] at h
  omega

private def dss24a5_sylow (W : Subgroup (alternatingGroup (Fin 5))) (hW : Nat.card W = 4) :
    Sylow 2 (alternatingGroup (Fin 5)) :=
  (IsPGroup.of_card (n := 2) (by rw [hW]; norm_num)).toSylow (dss24a5_index_odd W hW)

private theorem dss24a5_sylow_coe (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 4) :
    (dss24a5_sylow W hW : Subgroup (alternatingGroup (Fin 5))) = W :=
  IsPGroup.toSylow_coe _ _

theorem dss24_a5_normalizer_card (K : Subgroup (alternatingGroup (Fin 5)))
    (hK : Nat.card K = 4) :
    Nat.card (Subgroup.normalizer (K : Set (alternatingGroup (Fin 5)))) = 12 := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5))
    (dss24a5_sylow dss24a5V0 dss24a5V0_card) (dss24a5_sylow K hK)
  have hcoe : dss24a5V0.map (MulAut.conj c).toMonoidHom = K := by
    have h := congrArg
      (fun P : Sylow 2 (alternatingGroup (Fin 5)) => (P : Subgroup (alternatingGroup (Fin 5)))) hc
    simp only [Sylow.coe_subgroup_smul, dss24a5_sylow_coe dss24a5V0 dss24a5V0_card,
      dss24a5_sylow_coe K hK] at h
    rw [← h]
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, MulAut.conj_symm_apply]
  rw [← hcoe, ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact dss24a5_card_normalizer_V0


theorem dss24_sylow_inf_normal {G : Type} [Group G] [Finite G] {S L P : Subgroup G}
    (hS : IsSylowTwoOf S P) (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    IsSylowTwoOf (S ⊓ L) L := by
  exact CFSG.Quasithin.F7.isSylowTwoOf_inf_normal hS hLP (hS.1.trans hPL)

theorem dss24_pCore_relIndex_four {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    (pCoreOf 2 L).relIndex T = 4 := by
  have hQT : pCoreOf 2 L ≤ T := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT
  have h60 : (pCoreOf 2 L).relIndex L = 60 := by
    have hc : Nat.card (oTwoQuot ↥L) = 60 := by
      rw [CFSG.Quasithin.IsL2Quot.card (by norm_num) hq]; norm_num
    have hsub : (pCoreOf 2 L).subgroupOf L = pCore 2 ↥L := by
      unfold pCoreOf
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [Subgroup.relIndex, hsub, Subgroup.index]
    exact hc
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hQT hT.1
  rw [h60] at hmul
  have hodd : ¬ 2 ∣ T.relIndex L := hT.2.2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT.2.1
  have hd : (pCoreOf 2 L).relIndex T ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rw [hm] at hmul ⊢
  have hm6 : m < 6 := by
    by_contra hcon
    have h64 : 2 ^ 6 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < T.relIndex L := Nat.pos_of_ne_zero (fun h => hodd (h ▸ dvd_zero 2))
    have : 2 ^ m ≤ 60 := by
      rw [← hmul]
      exact Nat.le_mul_of_pos_right _ hpos
    omega
  interval_cases m <;> omega

theorem dss24_relIndex_normalizer_sylow_five {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    (hA : ∀ K : Subgroup (alternatingGroup (Fin 5)), Nat.card K = 4 →
      Nat.card (Subgroup.normalizer (K : Set (alternatingGroup (Fin 5)))) = 12)
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) :
    (L ⊓ Subgroup.normalizer (T : Set G)).relIndex L = 5 := by
  have hTL : T ⊓ L = T := inf_eq_left.mpr hT.1
  have hsyl : IsSylowTwoOf (T ⊓ L) L := by rw [hTL]; exact hT
  obtain ⟨-, -, hB⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  have hborel : CFSG.Quasithin.borelOf L T = L ⊓ Subgroup.normalizer (T : Set G) := by
    unfold CFSG.Quasithin.borelOf
    rw [hTL]
  rw [hborel, hTL] at hB
  have hcardQ : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [CFSG.Quasithin.IsL2Quot.card (by norm_num) hq]; norm_num
  have hsurj : Function.Surjective (QuotientGroup.mk' (pCore 2 ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hkerT : (QuotientGroup.mk' (pCore 2 ↥L)).ker ≤ T.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := (CFSG.Quasithin.F1.mem_pCore_iff_coe x).mp hx
    rw [Subgroup.mem_subgroupOf]
    exact CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT h1
  have hker : (QuotientGroup.mk' (pCore 2 ↥L)).ker ≤
      (L ⊓ Subgroup.normalizer (T : Set G)).subgroupOf L := by
    intro x hx
    have h2 : (x : G) ∈ T := by
      have := hkerT hx
      rwa [Subgroup.mem_subgroupOf] at this
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, Subgroup.le_normalizer h2⟩
  have hidx : (L ⊓ Subgroup.normalizer (T : Set G)).relIndex L =
      (Subgroup.normalizer (((T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) :
        Subgroup (oTwoQuot ↥L)) : Set (oTwoQuot ↥L))).index := by
    rw [Subgroup.relIndex, ← hB, Subgroup.index_map_eq _ hsurj hker]
  rw [hidx]
  set Tb : Subgroup (oTwoQuot ↥L) := (T.subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))
    with hTb
  have hTbidx : Tb.index = T.relIndex L := Subgroup.index_map_eq _ hsurj hkerT
  have h4 := dss24_pCore_relIndex_four hq hT
  have h60 : (pCoreOf 2 L).relIndex L = 60 := by
    have hsub : (pCoreOf 2 L).subgroupOf L = pCore 2 ↥L := by
      unfold pCoreOf
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [Subgroup.relIndex, hsub, Subgroup.index]
    exact hcardQ
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _
    (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hT) hT.1
  rw [h4, h60] at hmul
  have h15 : T.relIndex L = 15 := by omega
  have hTbcard : Nat.card Tb = 4 := by
    have := Tb.card_mul_index
    rw [hTbidx, h15, hcardQ] at this
    omega
  obtain ⟨e⟩ := hq
  obtain ⟨e₀⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 (GaloisField 2 2)
    CFSG.Quasithin.A5Model.card_gf4 CFSG.Quasithin.A5Model.card_sl2_gf4
  let ψ : oTwoQuot ↥L ≃* alternatingGroup (Fin 5) :=
    e.trans ((CFSG.Quasithin.pslTwoGf2EquivSl 2).trans e₀)
  have hK : Nat.card (Tb.map ψ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hTbcard
  have hN := hA _ hK
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective ψ.injective] at hN
  have := (Subgroup.normalizer (Tb : Set (oTwoQuot ↥L))).card_mul_index
  rw [hN, hcardQ] at this
  omega


theorem dss24_commutator_commutator_eq_bot {G : Type} [Group G] {E Q X : Subgroup G}
    (hE : IsElemAbelian 2 E) (hEX : X ≤ Subgroup.normalizer (E : Set G))
    (hQE : ∀ e ∈ E, ∀ q ∈ Q, ⁅e, q⁆ = 1) (hQX : Q ≤ X)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hidx : Q.relIndex X = 2) :
    ⁅⁅E, X⁆, X⁆ = ⊥ := by
  obtain ⟨hcomm, hsq⟩ := hE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEinv : ∀ a ∈ E, a⁻¹ = a := by
    intro a ha
    have h2 := hsq a ha
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_right h2
  have hconj' : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    exact (Subgroup.mem_normalizer_iff.mp (hEX hx) e).mp he
  have hQc : ∀ e ∈ E, ∀ q ∈ Q, e * q = q * e := by
    intro e he q hq
    exact commutatorElement_eq_one_iff_mul_comm.mp (hQE e he q hq)
  have hidx' : (Q.subgroupOf X).index = 2 := hidx
  have h2 : ∀ x ∈ X, ∀ y ∈ X, x ∉ Q → y ∉ Q → x * y ∈ Q := by
    intro x hx y hy hxQ hyQ
    have hx' : (⟨x, hx⟩ : X) ∉ Q.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]; exact hxQ
    have hy' : (⟨y, hy⟩ : X) ∉ Q.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]; exact hyQ
    have := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
      (iff_of_false hx' hy')
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have key : ∀ e ∈ E, ∀ x ∈ X, ∀ y ∈ X, ⁅e, x⁆ * y = y * ⁅e, x⁆ := by
    intro e he x hx y hy
    have hc : ⁅e, x⁆ ∈ E := by
      have : ⁅e, x⁆ = e * (x * e⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact E.mul_mem he (hconj' x hx e⁻¹ (E.inv_mem he))
    by_cases hxQ : x ∈ Q
    · rw [hQE e he x hxQ, one_mul, mul_one]
    by_cases hyQ : y ∈ Q
    · exact hQc _ hc y hyQ
    have hxinvQ : x⁻¹ ∉ Q := fun h => hxQ (by simpa using Q.inv_mem h)
    have hq : x⁻¹ * y ∈ Q := h2 x⁻¹ (X.inv_mem hx) y hy hxinvQ hyQ
    have hxx : x * x ∈ Q := h2 x hx x hx hxQ hxQ
    have hcx : ⁅e, x⁆ * x = x * ⁅e, x⁆ := by
      have hfE : x * e * x⁻¹ ∈ E := hconj' x hx e he
      have hxxe : e * (x * x) = (x * x) * e := hQc e he (x * x) hxx
      have hf : x⁻¹ * e * x = x * e * x⁻¹ := by
        calc x⁻¹ * e * x = x⁻¹ * (e * (x * x)) * x⁻¹ := by group
          _ = x⁻¹ * ((x * x) * e) * x⁻¹ := by rw [hxxe]
          _ = x * e * x⁻¹ := by group
      have h1 : ⁅e, x⁆ = e * (x * e * x⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      have h3 : x⁻¹ * ⁅e, x⁆ * x = (x * e * x⁻¹) * e⁻¹ := by
        rw [commutatorElement_def, ← hf]; group
      have h4 : (x * e * x⁻¹) * e⁻¹ = e * (x * e * x⁻¹)⁻¹ := by
        rw [hEinv _ hfE, hEinv e he, hEc _ hfE e he]
      calc ⁅e, x⁆ * x = x * (x⁻¹ * ⁅e, x⁆ * x) := by group
        _ = x * ⁅e, x⁆ := by rw [h3, h4, ← h1]
    have hqc : ⁅e, x⁆ * (x⁻¹ * y) = (x⁻¹ * y) * ⁅e, x⁆ := hQc _ hc _ hq
    calc ⁅e, x⁆ * y = (⁅e, x⁆ * x) * (x⁻¹ * y) := by group
      _ = x * (⁅e, x⁆ * (x⁻¹ * y)) := by rw [hcx]; group
      _ = x * ((x⁻¹ * y) * ⁅e, x⁆) := by rw [hqc]
      _ = y * ⁅e, x⁆ := by group
  have hle : ⁅E, X⁆ ≤ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.commutator_le]
    intro e he x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (key e he x hx y hy).symm
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro d hd y hy
  have := Subgroup.mem_centralizer_iff.mp (hle hd) y hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact this.symm


theorem dss24_card_le_of_comm_sq {G : Type} [Group G] [Finite G]
    (hR : ∀ R : Subgroup G, IsPGroup 2 R → (dsFrattini R).relIndex R ≤ 16)
    (V Z : Subgroup G) (hV : IsPGroup 2 V) (hZV : Z ≤ V)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Z) (hsq : ∀ a ∈ V, a ^ 2 ∈ Z) :
    Nat.card V ≤ 16 * Nat.card Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN : (Z.subgroupOf V).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : ((g * n * g⁻¹ : V) : G) = ⁅(g : G), (n : G)⁆ * (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
    rw [h1]
    exact Z.mul_mem (hcomm _ g.2 _ n.2) hn
  have hfr : frattini ↥V ≤ Z.subgroupOf V :=
    CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := 2) (Z.subgroupOf V)
      (fun a b => by
        rw [Subgroup.mem_subgroupOf]
        exact hcomm _ a.2 _ b.2)
      (fun a => by
        rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow]
        exact hsq _ a.2)
  have hle : dsFrattini V ≤ Z := by
    unfold dsFrattini
    rw [Subgroup.map_le_iff_le_comap]
    exact hfr
  have h1 := Subgroup.relIndex_mul_card (dsFrattini V) V
  have h2 : Nat.card ↥(dsFrattini V ⊓ V) ≤ Nat.card Z :=
    Subgroup.card_le_of_le (inf_le_left.trans hle)
  have h3 := hR V hV
  calc Nat.card V = (dsFrattini V).relIndex V * Nat.card ↥(dsFrattini V ⊓ V) := h1.symm
    _ ≤ 16 * Nat.card Z := Nat.mul_le_mul h3 h2


theorem dss24_comm_sq_of_generated {G : Type} [Group G] (V Z : Subgroup G)
    (𝒳 : Set (Subgroup G)) (hV : V = ⨆ X ∈ 𝒳, X)
    (hab : ∀ X ∈ 𝒳, ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ = 1) (hsq : ∀ X ∈ 𝒳, ∀ x ∈ X, x ^ 2 = 1)
    (hZX : ∀ X ∈ 𝒳, Z ≤ X) (hcomm : ∀ X ∈ 𝒳, ∀ Y ∈ 𝒳, ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ Z) :
    (∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Z) ∧ (∀ a ∈ V, a ^ 2 ∈ Z) := by
  have hind : ∀ (C : G → Prop), (∀ X ∈ 𝒳, ∀ x ∈ X, C x) → C 1 →
      (∀ x y, C x → C y → C (x * y)) → ∀ v ∈ V, C v := by
    intro C hmem h1 hmul v hv
    rw [hV, iSup_subtype'] at hv
    exact Subgroup.iSup_induction (C := C) _ hv (fun i x hx => hmem i.1 i.2 x hx) h1 hmul
  have hXV : ∀ X ∈ 𝒳, X ≤ V := by
    intro X hX
    rw [hV]
    exact le_iSup₂ (f := fun X (_ : X ∈ 𝒳) => X) X hX
  have hcent : ∀ v ∈ V, ∀ z ∈ Z, v * z = z * v := by
    refine hind (fun v => ∀ z ∈ Z, v * z = z * v) ?_ ?_ ?_
    · intro X hX x hx z hz
      exact commutatorElement_eq_one_iff_mul_comm.mp (hab X hX x hx z (hZX X hX hz))
    · intro z _
      rw [one_mul, mul_one]
    · intro x y hx hy z hz
      rw [mul_assoc, hy z hz, ← mul_assoc, hx z hz, mul_assoc]
  have hc1 : ∀ Y ∈ 𝒳, ∀ a ∈ Y, ∀ b ∈ V, ⁅a, b⁆ ∈ Z := by
    intro Y hY a ha b hb
    refine (hind (fun b => b ∈ V ∧ ⁅a, b⁆ ∈ Z) ?_ ?_ ?_ b hb).2
    · intro X hX x hx
      exact ⟨hXV X hX hx, hcomm Y hY X hX a ha x hx⟩
    · exact ⟨V.one_mem, by rw [commutatorElement_one_right]; exact Z.one_mem⟩
    · rintro x y ⟨hxV, hxZ⟩ ⟨hyV, hyZ⟩
      refine ⟨V.mul_mem hxV hyV, ?_⟩
      have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅a, y⁆ * x⁻¹ = ⁅a, y⁆ := by
        rw [hcent x hxV _ hyZ, mul_inv_cancel_right]
      rw [e, e2]
      exact Z.mul_mem hxZ hyZ
  have hc2 : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    refine (hind (fun a => a ∈ V ∧ ⁅a, b⁆ ∈ Z) ?_ ?_ ?_ a ha).2
    · intro X hX x hx
      exact ⟨hXV X hX hx, hc1 X hX x hx b hb⟩
    · exact ⟨V.one_mem, by rw [commutatorElement_one_left]; exact Z.one_mem⟩
    · rintro x y ⟨hxV, hxZ⟩ ⟨hyV, hyZ⟩
      refine ⟨V.mul_mem hxV hyV, ?_⟩
      have e : ⁅x * y, b⁆ = (x * ⁅y, b⁆ * x⁻¹) * ⁅x, b⁆ := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅y, b⁆ * x⁻¹ = ⁅y, b⁆ := by
        rw [hcent x hxV _ hyZ, mul_inv_cancel_right]
      rw [e, e2]
      exact Z.mul_mem hyZ hxZ
  refine ⟨hc2, ?_⟩
  intro a ha
  refine (hind (fun a => a ∈ V ∧ a ^ 2 ∈ Z) ?_ ?_ ?_ a ha).2
  · intro X hX x hx
    exact ⟨hXV X hX hx, by rw [hsq X hX x hx]; exact Z.one_mem⟩
  · exact ⟨V.one_mem, by rw [one_pow]; exact Z.one_mem⟩
  · rintro x y ⟨hxV, hxZ⟩ ⟨hyV, hyZ⟩
    refine ⟨V.mul_mem hxV hyV, ?_⟩
    have hyx : ⁅y, x⁆ ∈ Z := hc2 y hyV x hxV
    have e : (x * y) ^ 2 = (x * ⁅y, x⁆ * x⁻¹) * x ^ 2 * y ^ 2 := by
      simp only [commutatorElement_def, pow_two]; group
    have e2 : x * ⁅y, x⁆ * x⁻¹ = ⁅y, x⁆ := by
      rw [hcent x hxV _ hyx, mul_inv_cancel_right]
    rw [e, e2]
    exact Z.mul_mem (Z.mul_mem hyx hxZ) hyZ


theorem dss24_cover_of_five {G : Type} [Group G] [Finite G] {V Z : Subgroup G}
    (𝒳 : Finset (Subgroup G)) (hcard : 𝒳.card = 5) (hZ : Nat.card Z = 4)
    (hX : ∀ X ∈ 𝒳, X ≤ V ∧ Z ≤ X ∧ Nat.card X = 16)
    (hint : ∀ X ∈ 𝒳, ∀ Y ∈ 𝒳, X ≠ Y → X ⊓ Y = Z) (hV : Nat.card V ≤ 64) :
    ∀ v ∈ V, ∃ X ∈ 𝒳, v ∈ X := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  intro v hv
  let S : Subgroup G → Finset G := fun H => Finset.univ.filter (fun g => g ∈ H)
  have hmemS : ∀ H : Subgroup G, ∀ g, g ∈ S H ↔ g ∈ H := fun H g => by simp [S]
  have hS : ∀ H : Subgroup G, Nat.card H = (S H).card := fun H =>
    Nat.subtype_card (S H) (fun x => hmemS H x)
  have hne : 𝒳.Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  let F : Subgroup G → Finset G := fun X => S X \ S Z
  have hmemF : ∀ X : Subgroup G, ∀ g, g ∈ F X ↔ g ∈ X ∧ g ∉ Z := fun X g => by
    simp only [F, Finset.mem_sdiff, hmemS]
  have hFcard : ∀ X ∈ 𝒳, (F X).card = 12 := by
    intro X hX'
    obtain ⟨_, hZX, hXc⟩ := hX X hX'
    have hsub : S Z ⊆ S X := by
      intro g hg
      rw [hmemS] at hg ⊢
      exact hZX hg
    rw [Finset.card_sdiff_of_subset hsub, ← hS, ← hS, hXc, hZ]
  have hdisj : (𝒳 : Set (Subgroup G)).PairwiseDisjoint F := by
    intro X hX' Y hY' hXY
    change Disjoint (F X) (F Y)
    rw [Finset.disjoint_left]
    intro g hgX hgY
    rw [hmemF] at hgX hgY
    have hXY' : g ∈ X ⊓ Y := ⟨hgX.1, hgY.1⟩
    rw [hint X hX' Y hY' hXY] at hXY'
    exact hgX.2 hXY'
  have hBcard : (𝒳.biUnion F).card = 60 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hFcard]
    simp [hcard]
  have hdisj2 : Disjoint (S Z) (𝒳.biUnion F) := by
    rw [Finset.disjoint_left]
    intro g hgZ hgB
    rw [Finset.mem_biUnion] at hgB
    obtain ⟨X, _, hgX⟩ := hgB
    rw [hmemF] at hgX
    rw [hmemS] at hgZ
    exact hgX.2 hgZ
  have hTcard : (S Z ∪ 𝒳.biUnion F).card = 64 := by
    rw [Finset.card_union_of_disjoint hdisj2, hBcard, ← hS, hZ]
  have hTsub : S Z ∪ 𝒳.biUnion F ⊆ S V := by
    intro g hg
    rw [Finset.mem_union, Finset.mem_biUnion] at hg
    rw [hmemS]
    rcases hg with hg | ⟨X, hX', hgX⟩
    · rw [hmemS] at hg
      obtain ⟨X, hX'⟩ := hne
      exact (hX X hX').1 ((hX X hX').2.1 hg)
    · rw [hmemF] at hgX
      exact (hX X hX').1 hgX.1
  have heq : S Z ∪ 𝒳.biUnion F = S V := by
    apply Finset.eq_of_subset_of_card_le hTsub
    rw [hTcard, ← hS]
    exact hV
  have hvT : v ∈ S Z ∪ 𝒳.biUnion F := by
    rw [heq, hmemS]
    exact hv
  rw [Finset.mem_union, Finset.mem_biUnion] at hvT
  rcases hvT with hvZ | ⟨X, hX', hvX⟩
  · rw [hmemS] at hvZ
    obtain ⟨X, hX'⟩ := hne
    exact ⟨X, hX', (hX X hX').2.1 hvZ⟩
  · rw [hmemF] at hvX
    exact ⟨X, hX', hvX.1⟩


theorem dss24_ncard_conj_orbit {G : Type} [Group G] [Finite G] (K Y : Subgroup G) :
    Set.ncard {X : Subgroup G | ∃ g ∈ K, X = Y.map (MulAut.conj g).toMonoidHom} =
      (K ⊓ Subgroup.normalizer (Y : Set G)).relIndex K := by
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  have hsmul : ∀ (f : MulAut G) (X : Subgroup G), f • X = X.map f.toMonoidHom :=
    fun _ _ => rfl
  have hstab : (MulAction.stabilizer (MulAut G) Y).comap MulAut.conj =
      Subgroup.normalizer (Y : Set G) := by
    ext g
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq, MulEquiv.toMonoidHom_eq_coe]
  have horb : {X : Subgroup G | ∃ g ∈ K, X = Y.map (MulAut.conj g).toMonoidHom} =
      MulAction.orbit (K.map MulAut.conj) Y := by
    ext X
    simp only [Set.mem_setOf_eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨MulAut.conj g, Subgroup.mem_map_of_mem _ hg⟩, rfl⟩
    · rintro ⟨⟨f, hf⟩, rfl⟩
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hf
      exact ⟨g, hg, rfl⟩
  rw [horb, ← MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf,
    ← Subgroup.relIndex, ← Subgroup.relIndex_comap, hstab, inf_comm,
    Subgroup.inf_relIndex_right]

private abbrev cj {G : Type} [Group G] (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

private theorem mem_cj {G : Type} [Group G] {g : G} {H : Subgroup G} {y : G} :
    y ∈ cj g H ↔ g⁻¹ * y * g ∈ H := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e : g⁻¹ * (MulAut.conj g).toMonoidHom z * g = z := by
      simp only [MulAut.conj_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom]
      group
    rw [e]
    exact hz
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by
      simp only [MulAut.conj_apply, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom]
      group⟩

private theorem cj_mul {G : Type} [Group G] (g h : G) (H : Subgroup G) :
    cj (g * h) H = cj g (cj h H) := by
  ext y
  rw [mem_cj, mem_cj, mem_cj]
  have e : (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
  rw [e]

private theorem cj_one {G : Type} [Group G] (H : Subgroup G) : cj 1 H = H := by
  ext y
  rw [mem_cj, inv_one, one_mul, mul_one]

private theorem cj_cj_inv {G : Type} [Group G] (g : G) (H : Subgroup G) :
    cj g⁻¹ (cj g H) = H := by
  ext y
  rw [mem_cj, mem_cj, inv_inv]
  have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rw [e]

private theorem cj_cj_inv' {G : Type} [Group G] (g : G) (H : Subgroup G) :
    cj g (cj g⁻¹ H) = H := by
  rw [← cj_mul, mul_inv_cancel, cj_one]

private theorem cj_inf {G : Type} [Group G] (g : G) (A B : Subgroup G) :
    cj g (A ⊓ B) = cj g A ⊓ cj g B := by
  ext y
  simp only [Subgroup.mem_inf, mem_cj]

private theorem cj_mono {G : Type} [Group G] (g : G) {A B : Subgroup G} (h : A ≤ B) :
    cj g A ≤ cj g B :=
  Subgroup.map_mono h

private theorem cj_bot {G : Type} [Group G] (g : G) : cj g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

private theorem cj_card {G : Type} [Group G] (g : G) (H : Subgroup G) :
    Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem cj_eq_of_mem_normalizer {G : Type} [Group G] {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : cj g H = H := by
  ext y
  rw [mem_cj]
  have hn := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [e] at hn
  exact hn

private theorem mem_normalizer_of_cj {G : Type} [Group G] {g : G} {H : Subgroup G}
    (h : cj g H = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hm : g * y * g⁻¹ ∈ cj g H ↔ g⁻¹ * (g * y * g⁻¹) * g ∈ H := mem_cj
  rw [h] at hm
  have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rw [e] at hm
  exact hm.symm

private theorem cj_comm {G : Type} [Group G] {g : G} {A : Subgroup G}
    (hA : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e) : ∀ x ∈ cj g A, ∀ y ∈ cj g A, x * y = y * x := by
  intro x hx y hy
  rw [mem_cj] at hx hy
  have h1 := hA _ hx _ hy
  calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = y * x := by group

private theorem cj_sq {G : Type} [Group G] {g : G} {A : Subgroup G}
    (hA : ∀ a ∈ A, a ^ 2 = 1) : ∀ x ∈ cj g A, x ^ 2 = 1 := by
  intro x hx
  rw [mem_cj] at hx
  have ex : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [ex, conj_pow, hA _ hx, mul_one, mul_inv_cancel]

private theorem dss24_isElemAbelian_of_comm {G : Type} [Group G] (V : Subgroup G)
    (hc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hs : ∀ a ∈ V, a ^ 2 = 1) : IsElemAbelian 2 V :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hs x hx⟩

private theorem dss24_comm_of_elemAbelian {G : Type} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem dss24_isPGroup_of_sq {G : Type} [Group G] (V : Subgroup G)
    (hs : ∀ a ∈ V, a ^ 2 = 1) : IsPGroup 2 V := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using hs g.1 g.2)⟩

private theorem dss24_comm_of_sq {G : Type} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) : a * b = b * a := by
  have ha2 : a * a = 1 := by rw [← sq]; exact ha
  have hb2 : b * b = 1 := by rw [← sq]; exact hb
  have hab2 : (a * b) * (a * b) = 1 := by rw [← sq]; exact hab
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab2
  rw [mul_inv_rev, ha', hb'] at hab'
  exact hab'.symm

private theorem dss24_transport {G : Type} [Group G] {g g' : G} {H K Z : Subgroup G}
    (h : ∀ e ∈ H, ∀ f ∈ cj (g⁻¹ * g') K, ⁅e, f⁆ ∈ Z) :
    ∀ x ∈ cj g H, ∀ y ∈ cj g' K, ⁅x, y⁆ ∈ cj g Z := by
  intro x hx y hy
  rw [mem_cj] at hx hy
  rw [mem_cj]
  have hf : g⁻¹ * y * g ∈ cj (g⁻¹ * g') K := by
    rw [mem_cj]
    have e : (g⁻¹ * g')⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * g') = g'⁻¹ * y * g' := by group
    rw [e]
    exact hy
  have he := h _ hx _ hf
  have e2 : g⁻¹ * ⁅x, y⁆ * g = ⁅g⁻¹ * x * g, g⁻¹ * y * g⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e2]
  exact he

private theorem dss24_comm_sup {G : Type} [Group G] (y : G) (A B : Subgroup G)
    (hA : ∀ a ∈ A, y * a = a * y) (hB : ∀ b ∈ B, y * b = b * y) :
    ∀ x ∈ A ⊔ B, y * x = x * y := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      (fun b hb => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
    · rw [Set.mem_singleton_iff.mp hh]
      exact hA a ha
    · rw [Set.mem_singleton_iff.mp hh]
      exact hB b hb
  intro x hx
  exact Subgroup.mem_centralizer_iff.mp (hle hx) y (Set.mem_singleton y)

private theorem dss24_relIndex_sup {G : Type} [Group G] [Finite G] {L B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (L : Set G)) :
    B.relIndex (L ⊔ B) = (L ⊓ B).relIndex L := by
  have h1 : L.relIndex (B ⊔ L) = L.relIndex B :=
    CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hB
  rw [sup_comm] at h1
  have hm1 := Subgroup.relIndex_mul_relIndex (L ⊓ B) L (L ⊔ B) inf_le_left le_sup_left
  have hm2 := Subgroup.relIndex_mul_relIndex (L ⊓ B) B (L ⊔ B) inf_le_right le_sup_right
  rw [Subgroup.inf_relIndex_right] at hm2
  have hpos : 0 < L.relIndex B := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h1] at hm1
  have key : L.relIndex B * B.relIndex (L ⊔ B) = L.relIndex B * (L ⊓ B).relIndex L := by
    rw [hm2, ← hm1]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos key

private theorem dss24_eq_of_commute {G : Type} [Group G] [Finite G]
    (hR : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 16) {E W : Subgroup G}
    (hE : IsElemAbelian 2 E) (hW : IsElemAbelian 2 W) (hEc : Nat.card E = 16)
    (hWc : Nat.card W = 16) (hcomm : ∀ e ∈ E, ∀ w ∈ W, e * w = w * e) : W = E := by
  have hEV : E ≤ ⨆ X ∈ ({E, W} : Set (Subgroup G)), X :=
    le_iSup₂ (f := fun X (_ : X ∈ ({E, W} : Set (Subgroup G))) => X) E (by simp)
  have hWV : W ≤ ⨆ X ∈ ({E, W} : Set (Subgroup G)), X :=
    le_iSup₂ (f := fun X (_ : X ∈ ({E, W} : Set (Subgroup G))) => X) W (by simp)
  have hmemEW : ∀ X ∈ ({E, W} : Set (Subgroup G)), X = E ∨ X = W := by
    intro X hX
    rcases hX with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨hVc, hVs⟩ := dss24_comm_sq_of_generated (⨆ X ∈ ({E, W} : Set (Subgroup G)), X) ⊥
    ({E, W} : Set (Subgroup G)) rfl
    (fun X hX x hx y hy => by
      rcases hmemEW X hX with rfl | rfl
      · exact commutatorElement_eq_one_iff_mul_comm.mpr (dss24_comm_of_elemAbelian hE hx hy)
      · exact commutatorElement_eq_one_iff_mul_comm.mpr (dss24_comm_of_elemAbelian hW hx hy))
    (fun X hX x hx => by
      rcases hmemEW X hX with rfl | rfl
      · exact hE.2 x hx
      · exact hW.2 x hx)
    (fun X _ => bot_le)
    (fun X hX Y hY x hx y hy => by
      rcases hmemEW X hX with rfl | rfl <;> rcases hmemEW Y hY with rfl | rfl
      · exact Subgroup.mem_bot.mpr
          (commutatorElement_eq_one_iff_mul_comm.mpr (dss24_comm_of_elemAbelian hE hx hy))
      · exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hcomm x hx y hy))
      · exact Subgroup.mem_bot.mpr
          (commutatorElement_eq_one_iff_mul_comm.mpr (hcomm y hy x hx).symm)
      · exact Subgroup.mem_bot.mpr
          (commutatorElement_eq_one_iff_mul_comm.mpr (dss24_comm_of_elemAbelian hW hx hy)))
  have hVel : IsElemAbelian 2 (⨆ X ∈ ({E, W} : Set (Subgroup G)), X) :=
    dss24_isElemAbelian_of_comm _
      (fun a ha b hb => commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hVc a ha b hb)))
      (fun a ha => Subgroup.mem_bot.mp (hVs a ha))
  have hVle := hR _ hVel
  have hEV' : E = ⨆ X ∈ ({E, W} : Set (Subgroup G)), X :=
    Subgroup.eq_of_le_of_card_ge hEV (by omega)
  have hWE : W ≤ E := hEV' ▸ hWV
  exact Subgroup.eq_of_le_of_card_ge hWE (by omega)

private theorem dss24_cj_centralizer {G : Type} [Group G] {S : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (S : Set G)) :
    cj b (Subgroup.centralizer (S : Set G)) = Subgroup.centralizer (S : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ z ∈ Subgroup.centralizer (S : Set G),
      g * z * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg z hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := Subgroup.mem_normalizer_iff.mp (inv_mem hg) s
      rw [inv_inv] at this
      exact this.mp hs
    have hc := hz _ hs'
    calc s * (g * z * g⁻¹) = g * ((g⁻¹ * s * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * s * g)) * g⁻¹ := by rw [hc]
      _ = (g * z * g⁻¹) * s := by group
  apply le_antisymm
  · intro y hy
    rw [mem_cj] at hy
    have := key b hb _ hy
    rwa [show b * (b⁻¹ * y * b) * b⁻¹ = y by group] at this
  · intro y hy
    rw [mem_cj]
    have := key b⁻¹ (inv_mem hb) y hy
    rwa [inv_inv] at this

private theorem cj_elemAbelian {G : Type} [Group G] (g : G) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) : IsElemAbelian 2 (cj g A) :=
  dss24_isElemAbelian_of_comm _
    (fun a ha b hb => cj_comm (fun e he f hf => dss24_comm_of_elemAbelian hA he hf) a ha b hb)
    (fun a ha => cj_sq (fun e he => hA.2 e he) a ha)

private theorem dss24_endgame {G : Type} [Group G] [Finite G]
    {P2 B Z1 Z Q2 : Subgroup G} {x : G}
    (hR : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 16)
    (hRF : ∀ R : Subgroup G, IsPGroup 2 R → (dsFrattini R).relIndex R ≤ 16)
    (hBN : P2 ⊓ Subgroup.normalizer (Z1 : Set G) = B) (hBP : B ≤ P2)
    (hBr : ∀ s ∈ P2, s ∉ B → ∀ g ∈ P2, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * s * b₂)
    (hxP : x ∈ P2) (hxB : x ∉ B)
    (hZ1el : IsElemAbelian 2 Z1) (hZ1c : Nat.card Z1 = 16)
    (hZc : Nat.card Z = 4) (hZZ1 : Z ≤ Z1) (hZP2 : P2 ≤ Subgroup.normalizer (Z : Set G))
    (hZ1Q2 : Z1 ≤ Q2) (hQ2 : ∀ g ∈ P2, cj g Q2 = Q2) (hQ2p : IsPGroup 2 Q2)
    (hZW : Z1 ⊓ cj x Z1 = Z) (hWc : ∀ e ∈ Z1, ∀ f ∈ cj x Z1, ⁅e, f⁆ ∈ Z)
    (hWnc : ∃ e ∈ Z1, ∃ f ∈ cj x Z1, e * f ≠ f * e)
    (hcount : Set.ncard {X : Subgroup G | ∃ g ∈ P2, X = cj g Z1} = 5) : False := by
  have hZ1ab : ∀ e ∈ Z1, ∀ f ∈ Z1, e * f = f * e :=
    fun e he f hf => dss24_comm_of_elemAbelian hZ1el he hf
  have hBZ1 : ∀ b ∈ B, cj b Z1 = Z1 := by
    intro b hb
    have hb' : b ∈ P2 ⊓ Subgroup.normalizer (Z1 : Set G) := by
      rw [hBN]
      exact hb
    exact cj_eq_of_mem_normalizer (Subgroup.mem_inf.mp hb').2
  have hBZ : ∀ b ∈ B, cj b Z = Z := fun b hb => cj_eq_of_mem_normalizer (hZP2 (hBP hb))
  have E1 : ∀ h ∈ P2, h ∉ B → Z1 ⊓ cj h Z1 = Z ∧ ∀ e ∈ Z1, ∀ f ∈ cj h Z1, ⁅e, f⁆ ∈ Z := by
    intro h hh hhB
    rcases hBr x hxP hxB h hh with hB' | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    · exact absurd hB' hhB
    · have hcj : cj (b₁ * x * b₂) Z1 = cj b₁ (cj x Z1) := by
        rw [cj_mul, cj_mul, hBZ1 b₂ hb₂]
      rw [hcj]
      refine ⟨?_, ?_⟩
      · calc Z1 ⊓ cj b₁ (cj x Z1) = cj b₁ Z1 ⊓ cj b₁ (cj x Z1) := by rw [hBZ1 b₁ hb₁]
          _ = cj b₁ (Z1 ⊓ cj x Z1) := (cj_inf b₁ _ _).symm
          _ = cj b₁ Z := by rw [hZW]
          _ = Z := hBZ b₁ hb₁
      · intro e he f hf
        have hh : ∀ e ∈ Z1, ∀ f ∈ cj (b₁⁻¹ * b₁) (cj x Z1), ⁅e, f⁆ ∈ Z := by
          rw [inv_mul_cancel, cj_one]
          exact hWc
        have key := dss24_transport hh e (by rw [hBZ1 b₁ hb₁]; exact he) f hf
        rwa [hBZ b₁ hb₁] at key
  obtain ⟨𝒳, h𝒳⟩ : ∃ 𝒳 : Set (Subgroup G), 𝒳 = {X | ∃ g ∈ P2, X = cj g Z1} := ⟨_, rfl⟩
  have hmem : ∀ X, X ∈ 𝒳 ↔ ∃ g ∈ P2, X = cj g Z1 := fun X => by rw [h𝒳]; rfl
  rw [← h𝒳] at hcount
  have hfin : 𝒳.Finite := Set.finite_of_ncard_ne_zero (by rw [hcount]; norm_num)
  have hcard5 : hfin.toFinset.card = 5 := by
    rw [← Set.ncard_eq_toFinset_card 𝒳 hfin, hcount]
  have hmemf : ∀ X, X ∈ hfin.toFinset ↔ X ∈ 𝒳 := fun X => Set.Finite.mem_toFinset hfin
  have hX_Q2 : ∀ X ∈ 𝒳, X ≤ Q2 := by
    intro X hX
    obtain ⟨g, hg, rfl⟩ := (hmem X).mp hX
    exact (cj_mono g hZ1Q2).trans (hQ2 g hg).le
  have hX_Z : ∀ X ∈ 𝒳, Z ≤ X := by
    intro X hX
    obtain ⟨g, hg, rfl⟩ := (hmem X).mp hX
    exact (cj_eq_of_mem_normalizer (hZP2 hg)).symm.le.trans (cj_mono g hZZ1)
  have hX_card : ∀ X ∈ 𝒳, Nat.card X = 16 := by
    intro X hX
    obtain ⟨g, hg, rfl⟩ := (hmem X).mp hX
    rw [cj_card, hZ1c]
  have hX_ab : ∀ X ∈ 𝒳, ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ = 1 := by
    intro X hX a ha b hb
    obtain ⟨g, hg, rfl⟩ := (hmem X).mp hX
    exact commutatorElement_eq_one_iff_mul_comm.mpr (cj_comm hZ1ab a ha b hb)
  have hX_sq : ∀ X ∈ 𝒳, ∀ x ∈ X, x ^ 2 = 1 := by
    intro X hX a ha
    obtain ⟨g, hg, rfl⟩ := (hmem X).mp hX
    exact cj_sq (fun e he => hZ1el.2 e he) a ha
  have hX_inter : ∀ X ∈ 𝒳, ∀ Y ∈ 𝒳, X ≠ Y → X ⊓ Y = Z := by
    intro X hX Y hY hne
    obtain ⟨g, hg, rfl⟩ := (hmem X).mp hX
    obtain ⟨g', hg', rfl⟩ := (hmem Y).mp hY
    have hh : g⁻¹ * g' ∈ P2 := P2.mul_mem (P2.inv_mem hg) hg'
    have hY' : cj g' Z1 = cj g (cj (g⁻¹ * g') Z1) := by
      rw [← cj_mul, mul_inv_cancel_left]
    have hhB : g⁻¹ * g' ∉ B := by
      intro hhB
      apply hne
      rw [hY', hBZ1 _ hhB]
    rw [hY', ← cj_inf, (E1 _ hh hhB).1, cj_eq_of_mem_normalizer (hZP2 hg)]
  have hcomm_fam : ∀ X ∈ 𝒳, ∀ Y ∈ 𝒳, ∀ a ∈ X, ∀ b ∈ Y, ⁅a, b⁆ ∈ Z := by
    intro X hX Y hY a ha b hb
    obtain ⟨g, hg, rfl⟩ := (hmem X).mp hX
    obtain ⟨g', hg', rfl⟩ := (hmem Y).mp hY
    have hh : ∀ e ∈ Z1, ∀ f ∈ cj (g⁻¹ * g') Z1, ⁅e, f⁆ ∈ Z := by
      intro e he f hf
      by_cases hhB : g⁻¹ * g' ∈ B
      · rw [hBZ1 _ hhB] at hf
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZ1ab e he f hf)]
        exact Z.one_mem
      · exact (E1 _ (P2.mul_mem (P2.inv_mem hg) hg') hhB).2 e he f hf
    have key := dss24_transport hh a ha b hb
    rwa [cj_eq_of_mem_normalizer (hZP2 hg)] at key
  obtain ⟨V, hVdef⟩ : ∃ V : Subgroup G, V = ⨆ X ∈ 𝒳, X := ⟨_, rfl⟩
  have hXV : ∀ X ∈ 𝒳, X ≤ V := fun X hX => by
    rw [hVdef]
    exact le_iSup₂ (f := fun X (_ : X ∈ 𝒳) => X) X hX
  have hVle : V ≤ Q2 := by
    rw [hVdef]
    exact iSup₂_le fun X hX => hX_Q2 X hX
  have hVp : IsPGroup 2 V := IsPGroup.to_le hQ2p hVle
  obtain ⟨hVc, hVs⟩ := dss24_comm_sq_of_generated V Z 𝒳 hVdef hX_ab
    (fun X hX a ha => hX_sq X hX a ha) hX_Z hcomm_fam
  have hZ1mem : Z1 ∈ 𝒳 := (hmem Z1).mpr ⟨1, P2.one_mem, (cj_one Z1).symm⟩
  have hZ1V : Z1 ≤ V := fun z hz => hXV Z1 hZ1mem hz
  have hZV : Z ≤ V := hZZ1.trans hZ1V
  have hcardV := dss24_card_le_of_comm_sq hRF V Z hVp hZV hVc hVs
  rw [hZc] at hcardV
  have hcover := dss24_cover_of_five hfin.toFinset hcard5 hZc
    (fun X hX => ⟨hXV X ((hmemf X).mp hX), hX_Z X ((hmemf X).mp hX),
      hX_card X ((hmemf X).mp hX)⟩)
    (fun X hX Y hY hne => hX_inter X ((hmemf X).mp hX) Y ((hmemf Y).mp hY) hne)
    (by omega)
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨X, hX, hvX⟩ := hcover v hv
    exact hX_sq X ((hmemf X).mp hX) v hvX
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a :=
    fun a ha b hb => dss24_comm_of_sq (hVsq a ha) (hVsq b hb) (hVsq _ (V.mul_mem ha hb))
  obtain ⟨e, he, f, hf, hne⟩ := hWnc
  have hWV : cj x Z1 ≤ V := hXV _ ((hmem _).mpr ⟨x, hxP, rfl⟩)
  exact hne (hVcomm e (hZ1V he) f (hWV hf))


theorem leafDSACaseIIStep4 [DSLeaf LeafDSANoField] [DSLeaf LeafDSACaseIIOmega] [DSLeaf LeafDSACaseIIQQ] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafM3] [DSLeaf LeafM4] [DSLeaf LeafBruhat] [DSLeaf LeafRankBounds] [DSLeaf LeafSylowS] : LeafDSACaseIIStep4 := by
  intro G _ _ L1 L2 S h c2 c1
  intro hZle
  have hG := (Finite4.gen4 (G := G))
  have hqL1 : IsL2Quot 2 (oTwoQuot ↥L1) :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 hG h.hyp.hyp.h1 h.ns1
  have hqL2 : IsL2Quot 2 (oTwoQuot ↥L2) :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 hG h.hyp.hyp.h2 h.ns2
  obtain ⟨hS1eq, -, hBS⟩ := dsa_no_field h
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, hBS⟩
  obtain ⟨-, hZZ1, hZ1Om, hZ1Oel, -, hP1Z1, -⟩ := zi_structure hZS
  obtain ⟨hA5, hZ1eq, hZeq, hfaithZ⟩ := zi_chief hZS hqL1 c1
  obtain ⟨hSylB, hSylP1, hQ1S⟩ := sylow_s h.hyp
  obtain ⟨hRF, hR⟩ := rank_bounds (G := G)
  have hBN2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (F1.bigB_le_normalizer_left h.hyp).2
  have hP1N1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    F1.parabolic_le_normalizer h.hyp
  have hZ2 : dsZi L2 S = dsZ S := dsZi_eq_dsZ_of_commutator_eq_bot c2
  have hBr2 : ∀ s ∈ L2 ⊔ bigB L1 L2 S, s ∉ bigB L1 L2 S → ∀ g ∈ L2 ⊔ bigB L1 L2 S,
      g ∈ bigB L1 L2 S ∨ ∃ b₁ ∈ bigB L1 L2 S, ∃ b₂ ∈ bigB L1 L2 S, g = b₁ * s * b₂ := by
    have hb := bruhat h.hyp.symm (Or.inl hqL2)
    rw [bigB_comm] at hb
    exact hb
  have hSylP2 : IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) := by
    have := (sylow_s h.hyp.symm).2.1
    rw [bigB_comm] at this
    exact this
  have hQ2S : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ S := by
    have := (sylow_s h.hyp.symm).2.2
    rw [bigB_comm] at this
    exact this
  have hQ2eq : dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
    unfold dsQ
    rw [bigB_comm]
  have hinfB2 : L2 ⊓ bigB L1 L2 S = L2 ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
    have := CFSG.Quasithin.F1.inf_bigB_eq_borelOf h.hyp.symm
    rw [bigB_comm] at this
    exact this
  set Z1 := dsZi L1 S with hZ1d
  set Z := dsZ S with hZd
  set Q1 := dsQ L1 L2 S with hQ1d
  set B := bigB L1 L2 S with hBd
  set P1 := L1 ⊔ B with hP1d
  set P2 := L2 ⊔ B with hP2d
  set S1 := S ⊓ L1 with hS1d
  have hBP1 : B ≤ P1 := le_sup_right
  have hL1P1 : L1 ≤ P1 := le_sup_left
  have hL2P2 : L2 ≤ P2 := le_sup_left
  have hBP2 : B ≤ P2 := le_sup_right
  have hS1P1 : S ≤ P1 := hSylP1.1
  have hS2pg : IsPGroup 2 S := hSylP1.2.1
  have hQ1S' : Q1 ≤ S := hQ1S
  have hQ1p : IsPGroup 2 Q1 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P1
  have hP1N : P1 ≤ Subgroup.normalizer (Q1 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1
  have hP2N2 : P2 ≤ Subgroup.normalizer (L2 : Set G) := sup_le Subgroup.le_normalizer hBN2
  have hP2N : P2 ≤ Subgroup.normalizer (pCoreOf 2 P2 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P2
  have hQ2cj : ∀ g ∈ P2, cj g (pCoreOf 2 P2) = pCoreOf 2 P2 :=
    fun g hg => cj_eq_of_mem_normalizer (hP2N hg)
  have hQ2p : IsPGroup 2 (pCoreOf 2 P2) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P2
  have hZ1Q2 : Z1 ≤ pCoreOf 2 P2 := by
    rw [← hQ2eq]
    exact hZle
  have hOmC : dsOmega1 (centerOf Q1) ≤ centerOf Q1 := (Subgroup.closure_le _).2 fun x hx => hx.1
  have hZ1Q1 : Z1 ≤ Q1 := by
    rw [hZ1eq]
    exact hOmC.trans inf_le_left
  have hZ1el : IsElemAbelian 2 Z1 := by
    rw [hZ1eq]
    exact hZ1Oel
  have hZ1cen : ∀ e ∈ Z1, ∀ q ∈ Q1, ⁅e, q⁆ = 1 := by
    intro e he q hq
    rw [hZ1eq] at he
    have hc : q * e = e * q := Subgroup.mem_centralizer_iff.mp (hOmC he).2 q hq
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc.symm
  have hZ1c : Nat.card Z1 = 16 := by
    have := hA5.card
    rwa [Subgroup.relIndex_bot_left] at this
  have hZ1ne : Z1 ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hZ1c
    norm_num at hZ1c
  have hZ1ab : ∀ e ∈ Z1, ∀ f ∈ Z1, e * f = f * e :=
    fun e he f hf => dss24_comm_of_elemAbelian hZ1el he hf
  have hZ1pg : IsPGroup 2 Z1 := dss24_isPGroup_of_sq Z1 (fun a ha => hZ1el.2 a ha)
  have hBZ1 : ∀ b ∈ B, cj b Z1 = Z1 := fun b hb => cj_eq_of_mem_normalizer (hP1Z1 (hBP1 hb))
  have hZ1le : Z1 ≤ L1 ⊔ L2 ⊔ S := hZ1Q1.trans (hQ1S'.trans le_sup_right)
  have hBZ : ∀ b ∈ B, cj b Z = Z := by
    intro b hb
    rw [hZeq, cj_inf, hBZ1 b hb, dss24_cj_centralizer (hBS hb)]
  have hL2Z : ∀ l ∈ L2, cj l Z ≤ Z := by
    intro l hl
    have hcl : cj l Z ≤ dsZi L2 S :=
      le_iSup₂ (f := fun y (_ : y ∈ L2) => Z.map (MulAut.conj y).toMonoidHom) l hl
    rw [hZ2] at hcl
    exact hcl
  have hL2N : ∀ l ∈ L2, cj l Z = Z := by
    intro l hl
    apply le_antisymm (hL2Z l hl)
    have h1 := cj_mono l (hL2Z l⁻¹ (inv_mem hl))
    rwa [cj_cj_inv'] at h1
  have hP2Z : P2 ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le (fun l hl => mem_normalizer_of_cj (hL2N l hl)) (fun b hb => mem_normalizer_of_cj (hBZ b hb))
  have hPB : P2 ⊓ Subgroup.normalizer (Z1 : Set G) = B :=
    normalizer_inf_eq_bigB h.hyp hZ1pg hZ1le hZ1ne hP1Z1
  have hS1Syl : IsSylowTwoOf S1 L1 := dss24_sylow_inf_normal hSylP1 hL1P1 hP1N1
  have hS2Syl : IsSylowTwoOf (S ⊓ L2) L2 := dss24_sylow_inf_normal hSylP2 hL2P2 hP2N2
  have hcount : Set.ncard {X : Subgroup G | ∃ g ∈ P2, X = cj g Z1} = 5 := by
    have h1 : Set.ncard {X : Subgroup G | ∃ g ∈ P2, X = cj g Z1} = B.relIndex P2 := by
      have := dss24_ncard_conj_orbit P2 Z1
      rw [hPB] at this
      exact this
    have h2 : B.relIndex P2 = (L2 ⊓ B).relIndex L2 := dss24_relIndex_sup hBN2
    have h5 : (L2 ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G)).relIndex L2 = 5 :=
      dss24_relIndex_normalizer_sylow_five dss24_a5_normalizer_card hqL2 hS2Syl
    rw [h1, h2, hinfB2, h5]
  have step1 : ∃ x ∈ P2, ¬ cj x Z1 ≤ Q1 := by
    by_contra hcon
    push Not at hcon
    have hcomm1 : ∀ g ∈ P2, ∀ g' ∈ P2, ∀ a ∈ cj g Z1, ∀ b ∈ cj g' Z1, ⁅a, b⁆ = 1 := by
      intro g hg g' hg' a ha b hb
      have hh : ∀ e ∈ Z1, ∀ f ∈ cj (g⁻¹ * g') Z1, ⁅e, f⁆ ∈ (⊥ : Subgroup G) := by
        intro e he f hf
        exact Subgroup.mem_bot.mpr (hZ1cen e he f (hcon _ (P2.mul_mem (P2.inv_mem hg) hg') hf))
      have key := dss24_transport hh a ha b hb
      rw [cj_bot] at key
      exact Subgroup.mem_bot.mp key
    obtain ⟨𝒳0, h𝒳0⟩ : ∃ 𝒳0 : Set (Subgroup G), 𝒳0 = {X | ∃ g ∈ P2, X = cj g Z1} := ⟨_, rfl⟩
    have hmem0 : ∀ X, X ∈ 𝒳0 ↔ ∃ g ∈ P2, X = cj g Z1 := fun X => by rw [h𝒳0]; rfl
    obtain ⟨V0, hV0def⟩ : ∃ V0 : Subgroup G, V0 = ⨆ X ∈ 𝒳0, X := ⟨_, rfl⟩
    obtain ⟨hV0c, hV0s⟩ := dss24_comm_sq_of_generated V0 ⊥ 𝒳0 hV0def
      (fun X hX a ha b hb => by
        obtain ⟨g, hg, rfl⟩ := (hmem0 X).mp hX
        exact hcomm1 g hg g hg a ha b hb)
      (fun X hX a ha => by
        obtain ⟨g, hg, rfl⟩ := (hmem0 X).mp hX
        exact cj_sq (fun e he => hZ1el.2 e he) a ha)
      (fun X _ => bot_le)
      (fun X hX Y hY a ha b hb => by
        obtain ⟨g, hg, rfl⟩ := (hmem0 X).mp hX
        obtain ⟨g', hg', rfl⟩ := (hmem0 Y).mp hY
        rw [hcomm1 g hg g' hg' a ha b hb]
        exact Subgroup.one_mem _)
    have hV0el : IsElemAbelian 2 V0 :=
      dss24_isElemAbelian_of_comm V0
        (fun a ha b hb => commutatorElement_eq_one_iff_mul_comm.mp
          (Subgroup.mem_bot.mp (hV0c a ha b hb)))
        (fun a ha => Subgroup.mem_bot.mp (hV0s a ha))
    have hZ1V0 : Z1 ≤ V0 := by
      rw [hV0def]
      exact le_iSup₂ (f := fun X (_ : X ∈ 𝒳0) => X) Z1
        ((hmem0 Z1).mpr ⟨1, P2.one_mem, (cj_one Z1).symm⟩)
    have hV0eq : Z1 = V0 :=
      Subgroup.eq_of_le_of_card_ge hZ1V0 (by rw [hZ1c]; exact hR _ hV0el)
    have hsub : ∀ g ∈ P2, cj g Z1 ≤ Z1 := by
      intro g hg
      calc cj g Z1 ≤ V0 := by
            rw [hV0def]
            exact le_iSup₂ (f := fun X (_ : X ∈ 𝒳0) => X) (cj g Z1) ((hmem0 _).mpr ⟨g, hg, rfl⟩)
        _ = Z1 := hV0eq.symm
    have hN : P2 ≤ Subgroup.normalizer (Z1 : Set G) := by
      intro g hg
      apply mem_normalizer_of_cj
      apply le_antisymm (hsub g hg)
      calc Z1 = cj g (cj g⁻¹ Z1) := (cj_cj_inv' g Z1).symm
        _ ≤ cj g Z1 := cj_mono g (hsub g⁻¹ (P2.inv_mem hg))
    have hcf : Z1 = ⊥ :=
      coreFree h.hyp.hyp hZ1pg hZ1le (le_sup_left.trans hP1Z1) (hL2P2.trans hN) (hS1P1.trans hP1Z1)
    exact hZ1ne hcf
  have hA1 : ∀ y ∈ P2, ¬ cj y Z1 ≤ Q1 → ¬ Z1 ≤ cj y Q1 := by
    intro y hy hyQ hle
    have hcomm : ∀ e ∈ Z1, ∀ f ∈ cj y Z1, e * f = f * e := by
      intro e he f hf
      have he' : e ∈ cj y Q1 := hle he
      rw [mem_cj] at he' hf
      have h1 : ⁅y⁻¹ * f * y, y⁻¹ * e * y⁆ = 1 := hZ1cen _ hf _ he'
      have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
      calc e * f = y * ((y⁻¹ * e * y) * (y⁻¹ * f * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * f * y) * (y⁻¹ * e * y)) * y⁻¹ := by rw [← h2]
        _ = f * e := by group
    have hEq : cj y Z1 = Z1 :=
      dss24_eq_of_commute hR hZ1el (cj_elemAbelian y hZ1el) hZ1c
        (by rw [cj_card, hZ1c]) hcomm
    exact hyQ (hEq.le.trans hZ1Q1)
  have hWne : ∀ y ∈ P2, ¬ cj y Z1 ≤ Q1 → ∃ e ∈ Z1, ∃ f ∈ cj y Z1, e * f ≠ f * e := by
    intro y hy hyQ
    by_contra hno
    push Not at hno
    have hEq : cj y Z1 = Z1 :=
      dss24_eq_of_commute hR hZ1el (cj_elemAbelian y hZ1el) hZ1c
        (by rw [cj_card, hZ1c]) hno
    exact hyQ (hEq.le.trans hZ1Q1)
  obtain ⟨x, hxP, hxQ, hAx⟩ : ∃ x ∈ P2, ¬ cj x Z1 ≤ Q1 ∧
      Q1.relIndex (cj x⁻¹ Z1 ⊔ Q1) ≤ Q1.relIndex (cj x Z1 ⊔ Q1) := by
    obtain ⟨x₀, hx₀P, hx₀⟩ := step1
    by_cases hc : Q1.relIndex (cj x₀⁻¹ Z1 ⊔ Q1) ≤ Q1.relIndex (cj x₀ Z1 ⊔ Q1)
    · exact ⟨x₀, hx₀P, hx₀, hc⟩
    · refine ⟨x₀⁻¹, P2.inv_mem hx₀P, ?_, ?_⟩
      · intro hle
        apply hA1 x₀ hx₀P hx₀
        calc Z1 = cj x₀ (cj x₀⁻¹ Z1) := (cj_cj_inv' x₀ Z1).symm
          _ ≤ cj x₀ Q1 := cj_mono x₀ hle
      · rw [inv_inv]
        omega
  set W := cj x Z1 with hWdef
  set X := W ⊔ Q1 with hXdef
  have hxB' : x ∉ B := fun hxB => hxQ (by rw [hWdef, hBZ1 x hxB]; exact hZ1Q1)
  have hWel : IsElemAbelian 2 W := cj_elemAbelian x hZ1el
  have hWc : Nat.card W = 16 := by rw [hWdef, cj_card, hZ1c]
  have hWQ2 : W ≤ pCoreOf 2 P2 := (cj_mono x hZ1Q2).trans (hQ2cj x hxP).le
  have hWS : W ≤ S := hWQ2.trans hQ2S
  have hXS : X ≤ S := sup_le hWS hQ1S'
  have hXP1 : X ≤ P1 := hXS.trans hS1P1
  have hQ1X : Q1 ≤ X := le_sup_right
  have hWX : W ≤ X := le_sup_left
  have hXN1 : X ≤ Subgroup.normalizer (Z1 : Set G) := hXP1.trans hP1Z1
  have hXNQ : X ≤ Subgroup.normalizer (Q1 : Set G) := hXP1.trans hP1N
  have hN_inf : L1 ≤ Subgroup.normalizer ((Q1 ⊓ L1 : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hQn := Subgroup.mem_normalizer_iff.mp (hP1N (hL1P1 hl)) y
    have hLn := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := L1) hl) y
    exact Subgroup.mem_inf.trans ((and_congr hQn hLn).trans Subgroup.mem_inf.symm)
  have hQL1 : Q1 ⊓ L1 = pCoreOf 2 L1 := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer inf_le_right hN_inf
        (IsPGroup.to_le hQ1p inf_le_left)
    · exact le_inf (F1.pCoreOf_le_pCoreOf_parabolic h.hyp) (CFSG.LieType.BorelTits.pCoreOf_le 2 L1)
  have hQ1S4 : Q1.relIndex S = 4 := by
    have hT := dss24_pCore_relIndex_four hqL1 hS1Syl
    have hTN : S1 ≤ Subgroup.normalizer (Q1 : Set G) := inf_le_left.trans (hS1P1.trans hP1N)
    have hQT : Q1 ⊓ S1 = pCoreOf 2 L1 := by
      rw [hS1d, ← inf_assoc, inf_eq_left.mpr hQ1S', hQL1]
    calc Q1.relIndex S = Q1.relIndex (S1 ⊔ Q1) := congrArg (fun T => Q1.relIndex T) hS1eq
      _ = Q1.relIndex S1 := F1.relIndex_sup_eq_of_le_normalizer hTN
      _ = (Q1 ⊓ S1).relIndex S1 := (Subgroup.inf_relIndex_right Q1 S1).symm
      _ = (pCoreOf 2 L1).relIndex S1 := by rw [hQT]
      _ = 4 := hT
  have hAof_ge : 2 ≤ Q1.relIndex X := by
    have h1 : Q1.relIndex X ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      exact hxQ (hWX.trans hle)
    have h0 : Q1.relIndex X ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hAof_dvd : Q1.relIndex X ∣ 4 := by
    have h1 := Subgroup.relIndex_mul_relIndex Q1 X S hQ1X hXS
    rw [hQ1S4] at h1
    exact ⟨_, h1.symm⟩
  have hAof_cases : Q1.relIndex X = 2 ∨ Q1.relIndex X = 4 := by
    have hle4 : Q1.relIndex X ≤ 4 := Nat.le_of_dvd (by norm_num) hAof_dvd
    have hne3 : Q1.relIndex X ≠ 3 := by
      intro h3
      rw [h3] at hAof_dvd
      norm_num at hAof_dvd
    omega
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G, Y = Z1 ⊓ Subgroup.centralizer (W : Set G) := ⟨_, rfl⟩
  have hT0Y : Z1 ⊓ cj x Q1 ≤ Y := by
    intro z hz
    obtain ⟨hz1, hzQ⟩ := Subgroup.mem_inf.mp hz
    rw [hYdef]
    refine Subgroup.mem_inf.mpr ⟨hz1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ cj x Z1 := hw
    rw [mem_cj] at hw' hzQ
    have h1 : ⁅x⁻¹ * w * x, x⁻¹ * z * x⁆ = 1 := hZ1cen _ hw' _ hzQ
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    calc w * z = x * ((x⁻¹ * w * x) * (x⁻¹ * z * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * z * x) * (x⁻¹ * w * x)) * x⁻¹ := by rw [h2]
      _ = z * w := by group
  have hTZ1 : (Z1 ⊓ cj x Q1).relIndex Z1 = Q1.relIndex (cj x⁻¹ Z1 ⊔ Q1) := by
    have htr := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (Z1 ⊓ cj x Q1) Z1 (MulAut.conj x⁻¹).injective
    have e1 : cj x⁻¹ (Z1 ⊓ cj x Q1) = cj x⁻¹ Z1 ⊓ Q1 := by
      rw [cj_inf, cj_cj_inv]
    have hZ1'N : cj x⁻¹ Z1 ≤ Subgroup.normalizer (Q1 : Set G) := by
      have : cj x⁻¹ Z1 ≤ S := (cj_mono x⁻¹ hZ1Q2).trans ((hQ2cj x⁻¹ (P2.inv_mem hxP)).le.trans hQ2S)
      exact this.trans (hS1P1.trans hP1N)
    rw [← htr]
    change (cj x⁻¹ (Z1 ⊓ cj x Q1)).relIndex (cj x⁻¹ Z1) = _
    rw [e1, inf_comm (cj x⁻¹ Z1) Q1, Subgroup.inf_relIndex_right,
      F1.relIndex_sup_eq_of_le_normalizer hZ1'N]
  have hOff : Y.relIndex Z1 ≤ Q1.relIndex (cj x⁻¹ Z1 ⊔ Q1) := by
    rw [← hTZ1]
    have hYZ1 : Y ≤ Z1 := by
      rw [hYdef]
      exact inf_le_left
    exact Subgroup.relIndex_le_of_le_left hT0Y (Subgroup.index_ne_zero_of_finite)
  have hYZ1' : Y ≤ Z1 := by
    rw [hYdef]
    exact inf_le_left
  have hYZ1 : Y ≤ Z1 := hYZ1'
  have hYc : ∀ y ∈ Y, ∀ x' ∈ X, ⁅y, x'⁆ ∈ (⊥ : Subgroup G) := by
    intro y hy x' hx'
    rw [hYdef] at hy
    obtain ⟨hyZ1, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyW : ∀ w ∈ W, y * w = w * y := fun w hw =>
      (Subgroup.mem_centralizer_iff.mp hyC w hw).symm
    have hyQ : ∀ q ∈ Q1, y * q = q * y := fun q hq =>
      commutatorElement_eq_one_iff_mul_comm.mp (hZ1cen y hyZ1 q hq)
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
      (dss24_comm_sup y W Q1 hyW hyQ x' hx'))
  have hXS1 : X ≤ S1 ⊔ Q1 := hXS.trans hS1eq.le
  have hs1S : ∀ t ∈ S1, t ∈ S := fun t ht => (inf_le_left : S1 ≤ S) ht
  have hCZ1 : ⁅Z1, S1⁆ ≤ Z1 := by
    rw [Subgroup.commutator_le]
    intro g1 hg1 g2 hg2
    have hg2N : g2 ∈ Subgroup.normalizer (Z1 : Set G) := hP1Z1 (hS1P1 (hs1S g2 hg2))
    have hc : g2 * g1⁻¹ * g2⁻¹ ∈ Z1 :=
      (Subgroup.mem_normalizer_iff.mp hg2N g1⁻¹).mp (Z1.inv_mem hg1)
    have e : ⁅g1, g2⁆ = g1 * (g2 * g1⁻¹ * g2⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z1.mul_mem hg1 hc
  rcases hAof_cases with hA2 | hA4
  ·
    exfalso
    have hcomm_ne : ⁅Z1, W⁆ ≠ ⊥ := by
      intro hbot
      obtain ⟨e, he, f, hf, hne⟩ := hWne x hxP hxQ
      apply hne
      have hmem : ⁅e, f⁆ ∈ ⁅Z1, W⁆ := Subgroup.commutator_mem_commutator he hf
      rw [hbot, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    have hq : ⁅⁅Z1, X⁆, X⁆ ≤ (⊥ : Subgroup G) :=
      (dss24_commutator_commutator_eq_bot hZ1el hXN1 hZ1cen hQ1X hXNQ hA2).le
    have hnt : ¬ ⁅Z1, X⁆ ≤ (⊥ : Subgroup G) := by
      intro hle
      apply hcomm_ne
      exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hWX).trans hle)
    have hfaith : ∀ x' ∈ X, (∀ e ∈ Z1, ⁅x', e⁆ ∈ (⊥ : Subgroup G)) → x' ∈ Q1 := by
      intro x' hx' hc
      exact hfaithZ x' (hXP1 hx') (IsPGroup.to_le hS2pg (Subgroup.zpowers_le.mpr (hXS hx')))
        (fun e he => Subgroup.mem_bot.mp (hc e he))
    have hcardY : Y.relIndex Z1 ≤ (X ⊓ Q1).relIndex X := by
      rw [inf_eq_right.mpr hQ1X]
      exact hOff.trans hAx
    obtain ⟨-, -, hY4⟩ := m4 hA5 hS1Syl hXS1 hq hnt hfaith bot_le hYZ1 hYc hcardY
    omega
  ·
    have hXeq : X = S := by
      have h1 := Subgroup.relIndex_mul_relIndex Q1 X S hQ1X hXS
      rw [hA4, hQ1S4] at h1
      have h2 : X.relIndex S = 1 := by omega
      exact le_antisymm hXS (Subgroup.relIndex_eq_one.mp h2)
    have hYS : ∀ y ∈ Y, y ∈ Z1 ∧ ∀ s ∈ S, y * s = s * y := by
      intro y hy
      refine ⟨hYZ1 hy, fun s hs => ?_⟩
      have hsX : s ∈ X := by
        rw [hXeq]
        exact hs
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hYc y hy s hsX))
    have hYZ : Y = Z := by
      rw [hZeq]
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hzS⟩ := hYS z hz
        exact Subgroup.mem_inf.mpr ⟨hz1,
          Subgroup.mem_centralizer_iff.mpr (fun s hs => (hzS s hs).symm)⟩
      · intro hz
        obtain ⟨hz1, hzC⟩ := Subgroup.mem_inf.mp hz
        rw [hYdef]
        exact Subgroup.mem_inf.mpr ⟨hz1,
          Subgroup.mem_centralizer_iff.mpr (fun w hw => Subgroup.mem_centralizer_iff.mp hzC w (hWS hw))⟩
    have hcY : 4 ≤ Nat.card Y := by
      have hm := Subgroup.relIndex_mul_card (H := Y) (K := Z1)
      rw [inf_eq_left.mpr hYZ1, hZ1c] at hm
      have hrel : Y.relIndex Z1 ≤ 4 := (hOff.trans hAx).trans hA4.le
      by_contra hlt
      push Not at hlt
      have := Nat.mul_le_mul hrel (show Nat.card Y ≤ 3 by omega)
      omega
    obtain ⟨hM3N, hM3nN⟩ := m3 hA5 hS1Syl
    by_cases hNat : NatSec L1 ⊥ Z1
    · obtain ⟨-, hrel4, hcomm1, hfix1, -⟩ := hM3N hNat
      rw [sup_bot_eq, Subgroup.relIndex_bot_left] at hrel4
      rw [sup_bot_eq] at hfix1
      have hcomm1' : ∀ t ∈ S1, ∀ f ∈ ⁅Z1, S1⁆, ⁅f, t⁆ ∈ (⊥ : Subgroup G) := by
        intro t ht f hf
        have := hcomm1 t ht f (by rw [sup_bot_eq]; exact hf)
        exact this
      have hC_eq : ⁅Z1, S1⁆ = Y := by
        apply le_antisymm
        · intro c hc
          rw [hYdef]
          refine Subgroup.mem_inf.mpr ⟨hCZ1 hc, Subgroup.mem_centralizer_iff.mpr (fun w hw => ?_)⟩
          have hA' : ∀ a ∈ S1, c * a = a * c := fun a ha =>
            commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hcomm1' a ha c hc))
          have hB' : ∀ q ∈ Q1, c * q = q * c := fun q hq =>
            commutatorElement_eq_one_iff_mul_comm.mp (hZ1cen c (hCZ1 hc) q hq)
          have hwS : w ∈ S := hWS hw
          have hs' : w ∈ S1 ⊔ Q1 := by
            rw [← hS1eq]
            exact hwS
          exact (dss24_comm_sup c S1 Q1 hA' hB' w hs').symm
        · intro y hy
          exact hfix1 y (hYZ1 hy) (fun t ht => Subgroup.mem_bot.mpr
            (commutatorElement_eq_one_iff_mul_comm.mpr ((hYS y hy).2 t (hs1S t ht))))
      have hZc : Nat.card Z = 4 := by
        have hZY : Z = ⁅Z1, S1⁆ := by rw [← hYZ, hC_eq]
        rw [hZY]
        exact hrel4
      have hZW : Z1 ⊓ W = Z := by
        apply le_antisymm
        · intro z hz
          obtain ⟨hz1, hzW⟩ := Subgroup.mem_inf.mp hz
          have hzY : z ∈ Y := by
            rw [hYdef]
            exact Subgroup.mem_inf.mpr ⟨hz1, Subgroup.mem_centralizer_iff.mpr
              (fun h hh => dss24_comm_of_elemAbelian hWel hh hzW)⟩
          rw [← hYZ]
          exact hzY
        · intro z hz
          have hzZ1 : z ∈ Z1 := hZZ1 hz
          have h' := Subgroup.mem_normalizer_iff.mp (hP2Z (P2.inv_mem hxP)) z
          rw [inv_inv] at h'
          have hxz : x⁻¹ * z * x ∈ Z1 := hZZ1 (h'.mp hz)
          exact Subgroup.mem_inf.mpr ⟨hzZ1, mem_cj.mpr hxz⟩
      have hWc' : ∀ e ∈ Z1, ∀ f ∈ W, ⁅e, f⁆ ∈ Z := by
        intro e he f hf
        have hfS : f ∈ Q1 ⊔ S1 := by
          rw [sup_comm, ← hS1eq]
          exact hWS hf
        have hS1N : S1 ≤ Subgroup.normalizer (Q1 : Set G) := inf_le_left.trans (hS1P1.trans hP1N)
        obtain ⟨q, hq, s, hs, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hS1N).mp hfS
        have hqe : e * q = q * e := commutatorElement_eq_one_iff_mul_comm.mp (hZ1cen e he q hq)
        have hmem : ⁅e, s⁆ ∈ ⁅Z1, S1⁆ := Subgroup.commutator_mem_commutator he hs
        have hcq : ⁅e, s⁆ * q = q * ⁅e, s⁆ :=
          commutatorElement_eq_one_iff_mul_comm.mp (hZ1cen _ (hCZ1 hmem) q hq)
        have e2 : ⁅e, q * s⁆ = ⁅e, s⁆ := by
          have e3 : ⁅e, q * s⁆ = q * ⁅e, s⁆ * q⁻¹ := by
            simp only [commutatorElement_def]
            calc e * (q * s) * e⁻¹ * (q * s)⁻¹ = (e * q) * s * e⁻¹ * s⁻¹ * q⁻¹ := by group
              _ = (q * e) * s * e⁻¹ * s⁻¹ * q⁻¹ := by rw [hqe]
              _ = q * (e * s * e⁻¹ * s⁻¹) * q⁻¹ := by group
          rw [e3, ← hcq]
          group
        rw [e2, ← hYZ, ← hC_eq]
        exact hmem
      exact dss24_endgame hR hRF hPB hBP2 hBr2 hxP hxB' hZ1el hZ1c hZc hZZ1 hP2Z hZ1Q2 hQ2cj
        hQ2p hZW hWc' (hWne x hxP hxQ) hcount
    · exfalso
      obtain ⟨-, hrel2, -, -, hfix2, -⟩ := hM3nN hNat
      rw [Subgroup.relIndex_bot_left] at hrel2
      have hYF : Y ≤ ⁅⁅Z1, S1⁆, S1⁆ ⊔ ⊥ := by
        intro y hy
        obtain ⟨hyZ1, hyS⟩ := hYS y hy
        exact hfix2 y hyZ1 (fun t ht => Subgroup.mem_bot.mpr
          (commutatorElement_eq_one_iff_mul_comm.mpr (hyS t (hs1S t ht))))
      have := Subgroup.card_le_of_le hYF
      omega

end CFSG.GH74.QTGen4.DSGen4
