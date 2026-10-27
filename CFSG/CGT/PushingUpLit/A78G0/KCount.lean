module

public import CFSG.CGT.PushingUpLit.A78G0.KData
import CFSG.CGT.PushingUpLit.A78G0.Fibers
public import CFSG.CGT.PushingUpLit.A78G0.Cliques

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78S4

section SL2

variable {e : ℕ}

theorem sup_eq_top_of_card_SL2 (he : 2 ≤ e) {A B : Subgroup (Matrix.SpecialLinearGroup (Fin 2)
    (GaloisField 2 e))} (hA : Nat.card A = 2 ^ e) (hB : Nat.card B = 2 ^ e) (hAB : A ≠ B) :
    A ⊔ B = ⊤ := by
  have h := CFSG.CGT.PushingUpLit.A78.isElemAbRankOne_upper_lower (GaloisField 2 e)
  have hU := CFSG.CGT.PushingUpLit.A78.card_upperUnipotent_gf (e := e) (by omega)
  obtain ⟨x, hx⟩ := CFSG.Timmesfeld.ARS.ElemAbRankOne.exists_eq_map_conj h
    (IsPGroup.of_card hA) (hA.trans hU.symm)
  obtain ⟨y, hy⟩ := CFSG.Timmesfeld.ARS.ElemAbRankOne.exists_eq_map_conj h
    (IsPGroup.of_card hB) (hB.trans hU.symm)
  rw [hx, hy]
  exact CFSG.Timmesfeld.ARS.ElemAbRankOne.sup_map_conj_eq_top h
    (fun heq => hAB (by rw [hx, hy]; exact heq))

end SL2

section Transport

variable {G : Type} [Group G] {S : Type} [Group S] {K' : Subgroup G} (φ : ↥K' ≃* S)

noncomputable def toS (C : Subgroup G) : Subgroup S := (C.subgroupOf K').map φ.toMonoidHom

theorem toS_card {C : Subgroup G} (hC : C ≤ K') : Nat.card (toS φ C) = Nat.card C := by
  unfold toS
  rw [Subgroup.card_map_of_injective φ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv

theorem toS_inj {C D : Subgroup G} (hC : C ≤ K') (hD : D ≤ K') : toS φ C = toS φ D ↔ C = D := by
  unfold toS
  rw [(Subgroup.map_injective φ.injective).eq_iff]
  exact subgroupOf_inj_of_le hC hD

theorem toS_sup {C D : Subgroup G} (hC : C ≤ K') (hD : D ≤ K') :
    toS φ (C ⊔ D) = toS φ C ⊔ toS φ D := by
  unfold toS
  rw [Subgroup.subgroupOf_sup hC hD, Subgroup.map_sup]

theorem toS_top : toS φ K' = ⊤ := by
  unfold toS
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ φ.surjective]

theorem toS_cs (C : Subgroup G) (k : ↥K') : toS φ (cs C k) = cs (toS φ C) (φ k) := by
  unfold toS
  rw [← map_conj_subgroupOf_mk (H := C) (L := K') k.2]
  exact CFSG.Timmesfeld.RankOne.map_map_conj φ.toMonoidHom (C.subgroupOf K') k

noncomputable def csIso (K : Subgroup G) (l : G) : ↥K ≃* ↥(cs K l) :=
  Subgroup.equivMapOfInjective K (MulAut.conj l).toMonoidHom (MulAut.conj l).injective

end Transport

section Sylow

variable {G : Type} [Group G] {K' : Subgroup G} {e : ℕ}
  (φ : ↥K' ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))

include φ

theorem sylow_sup_eq (he : 2 ≤ e) {P Q : Subgroup G} (hP : P ≤ K') (hQ : Q ≤ K')
    (hPc : Nat.card P = 2 ^ e) (hQc : Nat.card Q = 2 ^ e) (hPQ : P ≠ Q) : P ⊔ Q = K' := by
  have h1 : toS φ P ⊔ toS φ Q = ⊤ :=
    sup_eq_top_of_card_SL2 he (by rw [toS_card φ hP, hPc]) (by rw [toS_card φ hQ, hQc])
      (fun h => hPQ ((toS_inj φ hP hQ).1 h))
  rw [← toS_sup φ hP hQ, ← toS_top φ] at h1
  exact (toS_inj φ (sup_le hP hQ) le_rfl).1 h1

theorem sylow_conj (he : 2 ≤ e) {P Q : Subgroup G} (hP : P ≤ K') (hQ : Q ≤ K')
    (hPc : Nat.card P = 2 ^ e) (hQc : Nat.card Q = 2 ^ e) : ∃ k ∈ K', Q = cs P k := by
  obtain ⟨s, hs⟩ := exists_cs_eq_of_card_SL2 he (A := toS φ P) (B := toS φ Q)
    (by rw [toS_card φ hP, hPc]) (by rw [toS_card φ hQ, hQc])
  obtain ⟨k, rfl⟩ := φ.surjective s
  refine ⟨k, k.2, ?_⟩
  have h1 : toS φ Q = toS φ (cs P k) := by rw [hs, toS_cs]
  exact (toS_inj φ hQ (cs_le_L hP k.2)).1 h1

theorem sylow_not_commuting (he : 2 ≤ e) {P Q : Subgroup G} (hP : P ≤ K') (hQ : Q ≤ K')
    (hPc : Nat.card P = 2 ^ e) (hQc : Nat.card Q = 2 ^ e) (hPQ : P ≠ Q) : ¬ Commuting P Q := by
  have hopp := opposite_of_sylow_sl2 he φ hP hQ hPc hQc hPQ
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hPc
    have : 2 ^ 0 < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  exact hopp.not_commuting hPbot

end Sylow

section Complement

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  {h : G0Core G L₁ L₂ V W Z Z₂ e} {K A : Subgroup G}

theorem KData.exists_mul (hK : KData h K A) {l : G} (hl : l ∈ L₁) :
    ∃ v ∈ V, ∃ k ∈ K, l = v * k :=
  (mem_sup_iff_of_normalizes (K := V) (H := K)
    (fun _ hk _ hv => conj_mem_of_mem_normalizer' (h.L_le_M (hK.le_L hk)) hv)).1
    (hK.sup_V ▸ hl)

theorem kData_iso (hK : KData h K A) :
    Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) := by
  obtain ⟨D⟩ := h.pair.side₁.nat
  let f : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
    MonoidHom.mk' (fun k : ↥K => D.ρ k)
      (fun a b => D.ρ_mul a (hK.le_L a.2) b (hK.le_L b.2))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : G) ∈ V := (D.ρ_eq_one a (hK.le_L a.2)).1 ha
    have h2 : (a : G) ∈ K ⊓ V := ⟨a.2, h1⟩
    rw [hK.inf_V, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨l, hl, hlg⟩ := D.ρ_surj g
    obtain ⟨v, hv, k, hk, rfl⟩ := hK.exists_mul hl
    refine ⟨⟨k, hk⟩, ?_⟩
    show D.ρ k = g
    rw [← hlg, D.ρ_mul v (h.V_le_L hv) k (hK.le_L hk), (D.ρ_eq_one v (h.V_le_L hv)).2 hv, one_mul]
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem kData_sylow_mem (hK : KData h K A) {l : G} (hl : l ∈ L₁) {P : Subgroup G}
    (hP : P ≤ cs K l) (hc : Nat.card P = 2 ^ e) : P ∈ sigmaSet (zClass Z) Z := by
  obtain ⟨φ₀⟩ := kData_iso hK
  have hA' : cs A l ≤ cs K l := cs_mono hK.A_le l
  have hAc : Nat.card (cs A l) = 2 ^ e := by rw [card_cs, hK.A_card]
  obtain ⟨k, -, hPk⟩ := sylow_conj ((csIso K l).symm.trans φ₀) h.two_le hA' hP hAc hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hPk, ← cs_mul]
    exact cs_mem_zClass hK.A_mem _
  · intro hPZ
    have hZP : Z ≤ cs K l := hPZ ▸ hP
    apply h.hZ
    refine (Subgroup.eq_bot_iff_forall Z).2 fun z hz => ?_
    have hz2 : l⁻¹ * z * l ∈ K := mem_cs.1 (hZP hz)
    have hz3 : l⁻¹ * z * l ∈ V := by
      have := conj_mem_of_mem_normalizer' (h.L_le_M (L₁.inv_mem hl)) (h.Z_le_V hz)
      simpa using this
    have h4 : l⁻¹ * z * l ∈ K ⊓ V := ⟨hz2, hz3⟩
    rw [hK.inf_V, Subgroup.mem_bot] at h4
    calc z = l * (l⁻¹ * z * l) * l⁻¹ := by group
      _ = 1 := by rw [h4]; group
  · intro z hz p hp
    have hpL : p ∈ L₁ := cs_le_L hK.le_L hl (hP hp)
    exact (Subgroup.mem_centralizer_iff.1 (h.pair.side₁.Z_cent hz) p hpL).symm

@[expose] def conjK (L₁ K : Subgroup G) : Set (Subgroup G) := {C | ∃ x ∈ L₁, C = cs K x}

theorem ncard_conjK (hK : KData h K A) : (conjK L₁ K).ncard = 2 ^ (2 * e) := by
  have h1 : conjK L₁ K = {C | ∃ x ∈ V, C = cs K x} := by
    ext C
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, hv, k, hk, rfl⟩ := hK.exists_mul hx
      refine ⟨v, hv, ?_⟩
      rw [cs_mul, cs_of_mem_normalizer (Subgroup.le_normalizer hk)]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, h.V_le_L hx, rfl⟩
  have h2 : (Subgroup.normalizer (K : Set G)).subgroupOf V = Z.subgroupOf V := by
    ext ⟨v, hv⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show v ∈ Subgroup.normalizer (K : Set G) ↔ v ∈ Z
    constructor
    · intro hn
      refine h.pair.side₁.mem_Z_of_cent hv (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
      obtain ⟨v', hv', k, hk, rfl⟩ := hK.exists_mul hl
      have hkL : k ∈ L₁ := hK.le_L hk
      have hc : v * k * v⁻¹ * k⁻¹ ∈ K ⊓ V := by
        refine ⟨K.mul_mem ((Subgroup.mem_normalizer_iff.1 hn k).1 hk) (K.inv_mem hk), ?_⟩
        have : v * k * v⁻¹ * k⁻¹ = v * (k * v⁻¹ * k⁻¹) := by group
        rw [this]
        exact V.mul_mem hv (conj_mem_of_mem_normalizer' (h.L_le_M hkL) (V.inv_mem hv))
      rw [hK.inf_V, Subgroup.mem_bot] at hc
      have hvk : v * k = k * v := by
        calc v * k = (v * k * v⁻¹ * k⁻¹) * (k * v) := by group
          _ = k * v := by rw [hc, one_mul]
      calc v' * k * v = v' * (k * v) := by group
        _ = v' * (v * k) := by rw [hvk]
        _ = (v' * v) * k := by group
        _ = (v * v') * k := by rw [(h.jst.abelian_V v' hv' v hv).eq]
        _ = v * (v' * k) := by group
    · intro hz
      refine le_normalizer_of_conj' (A := Z) (B := K) (fun z hz k hk => ?_) hz
      have hcomm := Subgroup.mem_centralizer_iff.1 (h.pair.side₁.Z_cent hz) k (hK.le_L hk)
      have : z * k * z⁻¹ = k := by rw [← hcomm]; group
      rw [this]
      exact hk
  rw [h1, ncard_conj_class, h2]
  have h3 := Subgroup.card_mul_index (Z.subgroupOf V)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le_V).toEquiv,
    h.pair.side₁.card_V] at h3
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hZpos (by rw [h3, Nat.mul_comm])

@[expose] def sylSet (e : ℕ) (K' : Subgroup G) : Set (Subgroup G) :=
  {P | P ≤ K' ∧ Nat.card P = 2 ^ e}

theorem ncard_sylSet_cs (hK : KData h K A) (x : G) : (sylSet e (cs K x)).ncard = 2 ^ e + 1 := by
  obtain ⟨φ₀⟩ := kData_iso hK
  exact ncard_sylow_sl2 h.two_le ((csIso K x).symm.trans φ₀)

def pairsT (L₁ K : Subgroup G) (e : ℕ) : Set (Subgroup G × (Subgroup G × Subgroup G)) :=
  {p | p.1 ∈ conjK L₁ K ∧ p.2 ∈ (sylSet e p.1).offDiag}

theorem ncard_pairsT (hK : KData h K A) :
    (pairsT L₁ K e).ncard = 2 ^ (2 * e) * ((2 ^ e + 1) * 2 ^ e) := by
  have hF : ∀ K' ∈ conjK L₁ K, ((sylSet e K').offDiag).ncard = (2 ^ e + 1) * 2 ^ e := by
    rintro K' ⟨x, hx, rfl⟩
    rw [ncard_offDiag_eq _ (Set.toFinite _), ncard_sylSet_cs hK x, Nat.add_sub_cancel]
  exact (ncard_pairs _ _ _ hF).trans (by rw [ncard_conjK hK])

def nonCommPairs (Z : Subgroup G) : Set (Subgroup G × Subgroup G) :=
  {p | p.1 ∈ sigmaSet (zClass Z) Z ∧ p.2 ∈ {C | C ∈ sigmaSet (zClass Z) Z ∧ ¬ Commuting p.1 C}}

theorem ncard_nonCommPairs (hG : G0Core G L₁ L₂ V W Z Z₂ e) :
    (nonCommPairs Z).ncard = 2 ^ e * (2 ^ e + 1) * 2 ^ (2 * e) := by
  have hS : (sigmaSet (zClass Z) Z).ncard = 2 ^ e * (2 ^ e + 1) :=
    (Nat.card_coe_set_eq _).symm.trans hG.sigma_card
  have hF : ∀ B ∈ sigmaSet (zClass Z) Z,
      {C | C ∈ sigmaSet (zClass Z) Z ∧ ¬ Commuting B C}.ncard = 2 ^ (2 * e) := by
    intro B hB
    have h1 : {C | C ∈ sigmaSet (zClass Z) Z ∧ Commuting B C}.ncard = 2 ^ e :=
      (Nat.card_coe_set_eq _).symm.trans (hG.sigma_clique B hB)
    have h2 : {C | C ∈ sigmaSet (zClass Z) Z ∧ ¬ Commuting B C} =
        sigmaSet (zClass Z) Z \ {C | C ∈ sigmaSet (zClass Z) Z ∧ Commuting B C} := by
      ext C
      constructor
      · rintro ⟨hC, hn⟩
        exact ⟨hC, fun h' => hn h'.2⟩
      · rintro ⟨hC, hn⟩
        exact ⟨hC, fun h' => hn ⟨hC, h'⟩⟩
    have hsub : {C | C ∈ sigmaSet (zClass Z) Z ∧ Commuting B C} ⊆ sigmaSet (zClass Z) Z :=
      fun C hC => hC.1
    have h3 := Set.ncard_sdiff_add_ncard_of_subset hsub
    rw [← h2, h1, hS] at h3
    have h4 : 2 ^ e * (2 ^ e + 1) = 2 ^ (2 * e) + 2 ^ e := by
      rw [two_mul, pow_add]
      ring
    exact Nat.add_right_cancel (h3.trans h4)
  exact (ncard_pairs _ _ _ hF).trans (by rw [hS])

theorem kcount (hK : KData h K A) {B C : Subgroup G} (hB : B ∈ sigmaSet (zClass Z) Z)
    (hC : C ∈ sigmaSet (zClass Z) Z) (hBC : ¬ Commuting B C) : ∃ l ∈ L₁, B ⊔ C = cs K l := by
  obtain ⟨φ₀⟩ := kData_iso hK
  have he := h.two_le
  have hsub : Prod.snd '' pairsT L₁ K e ⊆ nonCommPairs Z := by
    rintro _ ⟨⟨K', P, Q⟩, ⟨⟨x, hx, rfl⟩, ⟨hP, hPc⟩, ⟨hQ, hQc⟩, hPQ⟩, rfl⟩
    exact ⟨kData_sylow_mem hK hx hP hPc, kData_sylow_mem hK hx hQ hQc,
      sylow_not_commuting ((csIso K x).symm.trans φ₀) he hP hQ hPc hQc hPQ⟩
  have hinj : Set.InjOn Prod.snd (pairsT L₁ K e) := by
    rintro ⟨K₁, P₁, Q₁⟩ ⟨⟨x₁, hx₁, rfl⟩, ⟨hP₁, hP₁c⟩, ⟨hQ₁, hQ₁c⟩, hPQ₁⟩
      ⟨K₂, P₂, Q₂⟩ ⟨⟨x₂, hx₂, rfl⟩, ⟨hP₂, hP₂c⟩, ⟨hQ₂, hQ₂c⟩, hPQ₂⟩ heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have e1 := sylow_sup_eq ((csIso K x₁).symm.trans φ₀) he hP₁ hQ₁ hP₁c hQ₁c hPQ₁
    have e2 := sylow_sup_eq ((csIso K x₂).symm.trans φ₀) he hP₂ hQ₂ hP₂c hQ₂c hPQ₂
    exact Prod.ext (e1.symm.trans e2) rfl
  have hcard : (nonCommPairs Z).ncard ≤ (Prod.snd '' pairsT L₁ K e).ncard := by
    rw [hinj.ncard_image, ncard_pairsT hK, ncard_nonCommPairs h]
    exact le_of_eq (by ring)
  have hsurj := Set.eq_of_subset_of_ncard_le hsub hcard
  have hBCN : (B, C) ∈ nonCommPairs Z := ⟨hB, hC, hBC⟩
  rw [← hsurj] at hBCN
  obtain ⟨⟨K', P, Q⟩, ⟨⟨x, hx, rfl⟩, ⟨hP, hPc⟩, ⟨hQ, hQc⟩, hPQ⟩, hpq⟩ := hBCN
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpq
  exact ⟨x, hx, sylow_sup_eq ((csIso K x).symm.trans φ₀) he hP hQ hPc hQc hPQ⟩

end Complement

end CFSG.CGT.PushingUpLit.A78G0
