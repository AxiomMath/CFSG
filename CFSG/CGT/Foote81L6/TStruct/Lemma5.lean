module

public import CFSG.CGT.Foote81L6.TStruct.DihProd
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.CGT.Foote81L6.TStruct.Classes

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct DihedralGroup

theorem IsE64.map_conj_of_le {G : Type*} [Group G] {T E : Subgroup G} (hE : IsE64 T E) {g : G}
    (hg : E.map (MulAut.conj g).toMonoidHom ≤ T) : IsE64 T (E.map (MulAut.conj g).toMonoidHom) :=
  ⟨hg, isElemAbelian_two_iff.2 (mul_self_map_conj hE.mul_self g), by rw [card_map_conj, hE.2.2]⟩

theorem TStruct.exists_sylow_subgroupOf_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (T : Sylow p G) {E : Subgroup G} (hET : E ≤ T)
    (hfus : ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ (T : Subgroup G), E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom) :
    ∃ Q : Sylow p ↥(normalizer (E : Set G)),
      (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (E : Set G)) := by
  set NE := normalizer (E : Set G) with hNE
  have hS : IsPGroup p ↥((T : Subgroup G).subgroupOf NE) := T.isPGroup'.comap_subtype
  obtain ⟨P, hP⟩ := hS.exists_le_sylow
  have hP' : IsPGroup p ↥((P : Subgroup NE).map NE.subtype) := P.isPGroup'.map NE.subtype
  obtain ⟨T', hT'⟩ := hP'.exists_le_sylow
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq G T T'
  have hmemT : ∀ z, z ∈ ((x • T : Sylow p G) : Subgroup G) → x⁻¹ * z * x ∈ T := by
    intro z hz
    rwa [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hz
  have hEP : E ≤ (P : Subgroup NE).map NE.subtype := fun z hz =>
    ⟨⟨z, le_normalizer hz⟩, hP (mem_subgroupOf.2 (hET hz)), rfl⟩
  have hEx : E.map (MulAut.conj x⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨z, hz, rfl⟩
    show x⁻¹ * z * x⁻¹⁻¹ ∈ T
    rw [inv_inv]
    exact hmemT z (hT' (hEP hz))
  obtain ⟨h, hh, e⟩ := hfus x⁻¹ hEx
  have hw : x * h ∈ NE := by
    apply mem_normalizer_of_map_conj_eq
    rw [← map_conj_map_conj, ← e, map_conj_map_conj, mul_inv_cancel, map_conj_one]
  have hle : ((P : Subgroup NE).map NE.subtype).map (MulAut.conj (x * h)⁻¹).toMonoidHom ≤
      (T : Subgroup G) ⊓ NE := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨?_, ?_⟩
    · have h1 := hmemT z (hT' ⟨z, hz, rfl⟩)
      show (x * h)⁻¹ * (z : G) * (x * h)⁻¹⁻¹ ∈ T
      have e' : (x * h)⁻¹ * (z : G) * (x * h)⁻¹⁻¹ = h⁻¹ * (x⁻¹ * z * x) * h := by group
      rw [e']
      exact mul_mem (mul_mem (inv_mem hh) h1) hh
    · exact mul_mem (mul_mem (inv_mem hw) z.2) (inv_mem (inv_mem hw))
  have hcard : Nat.card (P : Subgroup NE) ≤ Nat.card ((T : Subgroup G).subgroupOf NE) := by
    calc Nat.card (P : Subgroup NE) = Nat.card ((P : Subgroup NE).map NE.subtype) :=
          (card_map_of_injective NE.subtype_injective).symm
      _ = Nat.card (((P : Subgroup NE).map NE.subtype).map
            (MulAut.conj (x * h)⁻¹).toMonoidHom) := (card_map_conj _ _).symm
      _ ≤ Nat.card ↥((T : Subgroup G) ⊓ NE) := card_le_of_le hle
      _ = Nat.card ((T : Subgroup G).subgroupOf NE) := by
          rw [← subgroupOf_map_subtype, card_map_of_injective NE.subtype_injective]
  exact ⟨P, (eq_of_le_of_card_ge hP hcard).symm⟩

namespace FooteCore

section Local

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem a_ne_b₀ : D.a ≠ D.b₀ := fun h =>
  D.a_ne_one (mem_bot.1 (D.A_inf_B ▸ mem_inf.2 ⟨D.a_mem, by rw [h]; exact D.b₀_mem_B⟩))

theorem not_isConj_a_b₀ (hL3 : ∀ y ∈ D.Zab, IsConj D.a y → y = D.a) : ¬ IsConj D.a D.b₀ :=
  fun h => D.a_ne_b₀
    (hL3 _ (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) h).symm

theorem mem_normalizer_E64_of_odd (hab : ¬ IsConj D.a D.b₀) {Q : Subgroup G} (hQT : Q ≤ T)
    {y : G} (hyQ : y ∈ normalizer (Q : Set G)) {N : ℕ} (hN : Odd N) (hyN : y ^ N = 1)
    {F : Subgroup G} (hF : IsE64 T F) (hFQ : F ≤ Q) : y ∈ normalizer (F : Set G) := by
  haveI := D.finite_T
  obtain ⟨Fk, hFk⟩ : ∃ Fk : ℕ → Subgroup G, ∀ k, Fk k = F.map (MulAut.conj (y ^ k)).toMonoidHom :=
    ⟨_, fun _ => rfl⟩
  have hFkQ : ∀ k, Fk k ≤ Q := fun k => by
    rw [hFk]
    exact map_conj_le hFQ fun q hq => (mem_normalizer_iff.1 (pow_mem hyQ k) q).1 hq
  have hFkE : ∀ k, IsE64 T (Fk k) := fun k => by
    have h := hFkQ k
    rw [hFk] at h ⊢
    exact hF.map_conj_of_le (h.trans hQT)
  have hF0 : Fk 0 = F := by rw [hFk, pow_zero, map_conj_one]
  obtain ⟨XA, hXA⟩ : ∃ X : Subgroup G, X = ⨆ k, Fk k ⊓ D.A := ⟨_, rfl⟩
  obtain ⟨X0, hX0⟩ : ∃ X : Subgroup G, X = ⨆ k, Fk k ⊓ D.B₀ := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X : Subgroup G, X = ⨆ k, Fk k ⊓ D.B₁ := ⟨_, rfl⟩
  have hXA_le : XA ≤ D.A := hXA ▸ iSup_le fun k => inf_le_right
  have hX0_le : X0 ≤ D.B₀ := hX0 ▸ iSup_le fun k => inf_le_right
  have hX1_le : X1 ≤ D.B₁ := hX1 ▸ iSup_le fun k => inf_le_right
  have hFA : F ⊓ D.A ≤ XA := by
    rw [hXA, ← hF0]
    exact le_iSup (fun k => Fk k ⊓ D.A) 0
  have hF0' : F ⊓ D.B₀ ≤ X0 := by
    rw [hX0, ← hF0]
    exact le_iSup (fun k => Fk k ⊓ D.B₀) 0
  have hF1' : F ⊓ D.B₁ ≤ X1 := by
    rw [hX1, ← hF0]
    exact le_iSup (fun k => Fk k ⊓ D.B₁) 0
  have hXX : XA ⊔ (X0 ⊔ X1) = ⨆ k, Fk k := by
    apply le_antisymm
    · rw [hXA, hX0, hX1]
      exact sup_le (iSup_mono fun k => inf_le_left)
        (sup_le (iSup_mono fun k => inf_le_left) (iSup_mono fun k => inf_le_left))
    · refine iSup_le fun k => (D.E64_decomp (hFkE k)).1.le.trans ?_
      rw [hXA, hX0, hX1]
      exact sup_le_sup (le_iSup (fun k => Fk k ⊓ D.A) k)
        (sup_le_sup (le_iSup (fun k => Fk k ⊓ D.B₀) k) (le_iSup (fun k => Fk k ⊓ D.B₁) k))
  have hXT : (⨆ k, Fk k) ≤ T := iSup_le fun k => (hFkE k).1
  haveI : Finite ↥(⨆ k, Fk k) := Finite.of_injective _ (inclusion_injective hXT)
  have hmap : (XA ⊔ (X0 ⊔ X1)).map (MulAut.conj y).toMonoidHom = XA ⊔ (X0 ⊔ X1) := by
    rw [hXX]
    have hle : (⨆ k, Fk k).map (MulAut.conj y).toMonoidHom ≤ ⨆ k, Fk k := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      have e : (Fk k).map (MulAut.conj y).toMonoidHom = Fk (k + 1) := by
        rw [hFk, hFk, map_conj_map_conj, pow_succ']
      rw [e]
      exact le_iSup Fk (k + 1)
    exact eq_of_le_of_card_ge hle (by rw [card_map_conj])
  obtain ⟨hdec, hFA4, hF04, hF14⟩ := D.E64_decomp hF
  obtain ⟨k₀, -, ⟨φ₀⟩⟩ := exists_dihedral_of_four D.A_iso.some hXA_le hFA4 hFA
  obtain ⟨k₁, -, ⟨φ₁⟩⟩ := exists_dihedral_of_four D.B₀_iso.some hX0_le hF04 hF0'
  obtain ⟨k₂, -, ⟨φ₂⟩⟩ := exists_dihedral_of_four D.B₁_iso.some hX1_le hF14 hF1'
  have h01 : ∀ x ∈ XA, ∀ z ∈ X0, x * z = z * x := fun x hx z hz =>
    D.A_comm_B₀B₁ x (hXA_le hx) z (mem_sup_left (hX0_le hz))
  have h02 : ∀ x ∈ XA, ∀ z ∈ X1, x * z = z * x := fun x hx z hz =>
    D.A_comm_B₀B₁ x (hXA_le hx) z (mem_sup_right (hX1_le hz))
  have h12 : ∀ x ∈ X0, ∀ z ∈ X1, x * z = z * x := fun x hx z hz =>
    D.B₀_comm_B₁ x (hX0_le hx) z (hX1_le hz)
  have hi0 : XA ⊓ (X0 ⊔ X1) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hXA_le (sup_le_sup hX0_le hX1_le)).trans D.A_inf_B₀B₁.le)
  have hi1 : X0 ⊓ X1 = ⊥ := eq_bot_iff.2 ((inf_le_inf hX0_le hX1_le).trans D.B₀_inf_B₁.le)
  rcases comm_central_or_conj_zc (a := ![k₀, k₁, k₂]) φ₀ φ₁ φ₂ h01 h02 h12 hi0 hi1 hmap hN hyN
    with h | ⟨hall, j, hj⟩
  ·
    have hFX : F ≤ XA ⊔ (X0 ⊔ X1) := hdec.le.trans (sup_le_sup hFA (sup_le_sup hF0' hF1'))
    haveI := hF.finite
    refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
    have hyv : y * v * y⁻¹ ∈ T := hQT ((mem_normalizer_iff.1 hyQ v).1 (hFQ hv))
    have hc : v⁻¹ * (y * v * y⁻¹) ∈ T ⊓ centralizer (F : Set G) :=
      mem_inf.2 ⟨mul_mem (inv_mem (hF.1 hv)) hyv,
        mem_centralizer_iff.2 fun w hw => h v (hFX hv) w (hFX hw)⟩
    rw [D.centralizer_E64 hF] at hc
    have e : y * v * y⁻¹ = v * (v⁻¹ * (y * v * y⁻¹)) := by group
    rw [e]
    exact mul_mem hv hc
  ·
    exfalso
    have hza : ((φ₀.symm (zc k₀) : XA) : G) = D.a :=
      symm_zc_eq φ₀ (hall 0) (hFA (mem_inf.2 ⟨D.a_mem_E64 hF, D.a_mem⟩)) D.a_ne_one
        fun x hx => D.a_comm_A (hXA_le hx)
    have hzb : ((φ₁.symm (zc k₁) : X0) : G) = D.b₀ :=
      symm_zc_eq φ₁ (hall 1) (hF0' (mem_inf.2 ⟨D.b₀_mem_E64 hF, D.b₀_mem⟩)) D.b₀_ne_one
        fun x hx => D.b₀_comm x (hX0_le hx)
    exact hab (isConj_iff.2 ⟨y ^ j,
      (congrArg (fun t => y ^ j * t * (y ^ j)⁻¹) hza).symm.trans (hj.trans hzb)⟩)

theorem exists_conj_eq_of_coprime_index [Finite G] (hab : ¬ IsConj D.a D.b₀) {Q : Subgroup G}
    (hQT : Q ≤ T)
    (hidx : Nat.Coprime 2 ((T ⊓ normalizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))).index)
    {F : Subgroup G} (hF : IsE64 T F) (hFQ : F ≤ Q) {g : G} (hg : g ∈ normalizer (Q : Set G)) :
    ∃ s ∈ T, F.map (MulAut.conj g).toMonoidHom = F.map (MulAut.conj s).toMonoidHom := by
  set NQ := normalizer (Q : Set G) with hNQ
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G,
      K = NQ ⊓ ⨅ (F' : Subgroup G) (_ : IsE64 T F' ∧ F' ≤ Q), normalizer (F' : Set G) :=
    ⟨_, rfl⟩
  have hmemK : ∀ x, x ∈ K ↔ x ∈ NQ ∧
      ∀ F' : Subgroup G, IsE64 T F' → F' ≤ Q → x ∈ normalizer (F' : Set G) := by
    intro x
    simp only [hK, mem_inf, mem_iInf, and_imp]
  have hKle : K ≤ NQ := fun x hx => ((hmemK x).1 hx).1
  have hKn : ∀ s ∈ NQ, ∀ x ∈ K, s * x * s⁻¹ ∈ K := by
    intro s hs x hx
    obtain ⟨hxN, hxF⟩ := (hmemK x).1 hx
    refine (hmemK _).2 ⟨mul_mem (mul_mem hs hxN) (inv_mem hs), fun F' hF' hF'Q => ?_⟩
    have hle : F'.map (MulAut.conj s⁻¹).toMonoidHom ≤ Q :=
      map_conj_le hF'Q fun q hq => (mem_normalizer_iff.1 (inv_mem hs) q).1 hq
    have hx' := hxF _ (hF'.map_conj_of_le (hle.trans hQT)) hle
    exact conj_mem_normalizer_of_map_conj_eq
      (by rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]) hx'
  have hodd : ∀ x ∈ NQ, ∀ {M : ℕ}, Odd M → x ^ M = 1 → x ∈ K := fun x hx M hM hxM =>
    (hmemK x).2 ⟨hx, fun F' hF' hF'Q => D.mem_normalizer_E64_of_odd hab hQT hx hM hxM hF' hF'Q⟩
  haveI : (K.subgroupOf NQ).Normal :=
    (normal_subgroupOf_iff hKle).2 fun x s hx hs => hKn s hs x hx
  have hp : IsPGroup 2 (↥NQ ⧸ K.subgroupOf NQ) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, M, hM, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have h1 : (x ^ 2 ^ e) ^ M = 1 := by rw [← pow_mul, ← he, pow_orderOf_eq_one]
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact hodd _ (x ^ 2 ^ e).2 hM h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hKidx : (K.subgroupOf NQ).index = 2 ^ k := by rw [index_eq_card, hk]
  set S := T ⊓ NQ with hS
  have hSK : S ≤ normalizer (K : Set G) := fun s hs => mem_normalizer_iff.2 fun x =>
    ⟨fun hx => hKn s (mem_inf.1 hs).2 x hx, fun hx => by
      have := hKn s⁻¹ (inv_mem (mem_inf.1 hs).2) _ hx
      rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this⟩
  have h1 : ((K ⊔ S).subgroupOf NQ).index ∣ (S.subgroupOf NQ).index :=
    index_dvd_of_le fun x hx => mem_subgroupOf.2 (mem_sup_right (mem_subgroupOf.1 hx))
  have h2 : ((K ⊔ S).subgroupOf NQ).index ∣ 2 ^ k := by
    rw [← hKidx]
    exact index_dvd_of_le fun x hx => mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hx))
  have hidx1 : ((K ⊔ S).subgroupOf NQ).index = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_right h1 hidx).symm)
      h2
  have hgL : g ∈ K ⊔ S := subgroupOf_eq_top.1 (index_eq_one.1 hidx1) hg
  obtain ⟨k', hk', s, hs, rfl⟩ := (mem_sup_iff_of_le_normalizer hSK).1 hgL
  refine ⟨s, (mem_inf.1 hs).1, ?_⟩
  have hFs : IsE64 T (F.map (MulAut.conj s).toMonoidHom) := hF.map_conj (mem_inf.1 hs).1
  have hFsQ : F.map (MulAut.conj s).toMonoidHom ≤ Q :=
    map_conj_le hFQ fun q hq => (mem_normalizer_iff.1 (mem_inf.1 hs).2 q).1 hq
  rw [← map_conj_map_conj]
  exact map_conj_eq_self_of_mem_normalizer (((hmemK k').1 hk').2 _ hFs hFsQ)

end Local

section Sylow

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {m n : ℕ}
  (D : FooteCore G (T : Subgroup G) m n)

theorem lemma5_of_not_isConj (hab : ¬ IsConj D.a D.b₀) :
    ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ (T : Subgroup G),
        E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom := by
  intro E hE g hg
  have hg' : E.map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ T := by rwa [inv_inv]
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion T hE.1 hg'
  have heq : E.map (MulAut.conj c⁻¹).toMonoidHom = E.map (MulAut.conj g).toMonoidHom :=
    map_conj_eq_of_agree fun v hv => by rw [inv_inv, hcg v hv, inv_inv]
  have key : ∀ c : G, CFSG.RankTwoShapes.AlperinDecomposition 2 (T : Subgroup G) E c →
      ∃ h ∈ (T : Subgroup G),
        E.map (MulAut.conj c⁻¹).toMonoidHom = E.map (MulAut.conj h).toMonoidHom := by
    intro c hc
    induction hc with
    | one => exact ⟨1, one_mem _, by rw [inv_one]⟩
    | @step c' n' Q _ hQ hEQ hn ih =>
      obtain ⟨h, hh, e⟩ := ih
      have hF : IsE64 (T : Subgroup G) (E.map (MulAut.conj h).toMonoidHom) := hE.map_conj hh
      have hFQ : E.map (MulAut.conj h).toMonoidHom ≤ Q := by rw [← e]; exact hEQ
      obtain ⟨s, hs, es⟩ :=
        D.exists_conj_eq_of_coprime_index hab hQ.1 hQ.2.1 hF hFQ (inv_mem hn)
      refine ⟨s * h, mul_mem hs hh, ?_⟩
      rw [mul_inv_rev, ← map_conj_map_conj, e, es, map_conj_map_conj]
  obtain ⟨h, hh, e⟩ := key c hc
  exact ⟨h, hh, heq.symm.trans e⟩

theorem lemma5 (hL3 : ∀ y ∈ D.Zab, IsConj D.a y → y = D.a) :
    ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ (T : Subgroup G),
        E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom :=
  D.lemma5_of_not_isConj (D.not_isConj_a_b₀ hL3)

theorem sylow_normalizer_E64 (hL3 : ∀ y ∈ D.Zab, IsConj D.a y → y = D.a) :
    ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∃ Q : Sylow 2 ↥(normalizer (E : Set G)),
      (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (E : Set G)) := fun E hE =>
  exists_sylow_subgroupOf_normalizer T hE.1 (D.lemma5 hL3 E hE)

end Sylow

end FooteCore

end CFSG.CGT.Foote81L6
