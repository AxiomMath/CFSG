module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
public import CFSG.Foundations.MaxCardThompson
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

@[expose] def omegaCenter (X : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ X ∧ (∀ x ∈ X, g * x = x * g) ∧ g ^ 2 = 1}
  mul_mem' := by
    rintro a b ⟨haX, haC, ha2⟩ ⟨hbX, hbC, hb2⟩
    refine ⟨X.mul_mem haX hbX, fun x hx => ?_, ?_⟩
    · rw [mul_assoc, hbC x hx, ← mul_assoc, haC x hx, mul_assoc]
    · rw [(show Commute a b from haC b hbX).mul_pow, ha2, hb2, mul_one]
  one_mem' := ⟨X.one_mem, fun x _ => by rw [one_mul, mul_one], one_pow 2⟩
  inv_mem' := by
    rintro a ⟨haX, haC, ha2⟩
    refine ⟨X.inv_mem haX, fun x hx => ?_, by rw [inv_pow, ha2, inv_one]⟩
    calc a⁻¹ * x = a⁻¹ * (x * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * x) * a⁻¹ := by rw [haC x hx]
      _ = x * a⁻¹ := by group

theorem mem_omegaCenter {X : Subgroup G} {g : G} :
    g ∈ omegaCenter X ↔ g ∈ X ∧ (∀ x ∈ X, g * x = x * g) ∧ g ^ 2 = 1 :=
  Iff.rfl

theorem omegaCenter_le (X : Subgroup G) : omegaCenter X ≤ X := fun _ hg =>
  (mem_omegaCenter.1 hg).1

theorem isElemAbelian_omegaCenter (X : Subgroup G) : IsElemAbelian 2 (omegaCenter X) :=
  ⟨IsMulCommutative.of_setLike_mul_comm fun _ ha _ hb =>
    (mem_omegaCenter.1 ha).2.1 _ (mem_omegaCenter.1 hb).1,
    fun _ hx => (mem_omegaCenter.1 hx).2.2⟩

theorem omegaCenter_le_centralizer (X : Subgroup G) :
    omegaCenter X ≤ centralizer (X : Set G) := fun _ hg =>
  Subgroup.mem_centralizer_iff.2 fun h hh => ((mem_omegaCenter.1 hg).2.1 h hh).symm

private theorem conj_mem_omegaCenter {X : Subgroup G} {n : G} (hn : n ∈ normalizer (X : Set G))
    {g : G} (hg : g ∈ omegaCenter X) : n * g * n⁻¹ ∈ omegaCenter X := by
  obtain ⟨hgX, hgC, hg2⟩ := mem_omegaCenter.1 hg
  refine mem_omegaCenter.2 ⟨(Subgroup.mem_normalizer_iff.1 hn g).1 hgX, fun x hx => ?_, ?_⟩
  · have hy : n⁻¹ * x * n ∈ X := (Subgroup.mem_normalizer_iff''.1 hn x).1 hx
    calc n * g * n⁻¹ * x = n * (g * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * x * n) * g) * n⁻¹ := by rw [hgC _ hy]
      _ = x * (n * g * n⁻¹) := by group
  · rw [conj_pow, hg2, mul_one, mul_inv_cancel]

theorem normalizer_le_normalizer_omegaCenter (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (omegaCenter X : Set G) := by
  intro n hn
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => conj_mem_omegaCenter hn hg, fun h => ?_⟩
  have := conj_mem_omegaCenter ((normalizer (X : Set G)).inv_mem hn) h
  simpa [mul_assoc] using this

theorem omegaCenter_characteristic (S : Subgroup G) :
    ((omegaCenter S).subgroupOf S).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_le]
  intro φ y hy
  obtain ⟨-, hC, h2⟩ := mem_omegaCenter.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hy))
  refine Subgroup.mem_subgroupOf.2 (mem_omegaCenter.2 ⟨y.2, fun x hx => ?_, ?_⟩)
  · have key : y * ⟨x, hx⟩ = ⟨x, hx⟩ * y := by
      apply φ.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (hC _ (φ ⟨x, hx⟩).2)
    exact congrArg Subtype.val key
  · have key : y ^ 2 = 1 := by
      apply φ.injective
      rw [map_pow, map_one]
      exact Subtype.ext h2
    exact congrArg Subtype.val key

theorem omegaCenter_ne_bot [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    omegaCenter S ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
  have := hS.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center S)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hS (c : S)
  have hc1 : (c : S) ≠ 1 := fun h => hc (Subtype.ext h)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hc1 (orderOf_eq_one_iff.1 (by simpa using hk))
  have h2 : 2 ∣ orderOf (c : S) := by rw [hk]; exact dvd_pow_self 2 hk0
  have hdord : orderOf ((c : S) ^ (orderOf (c : S) / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos (c : S)).ne' h2
  have hd1 : (c : S) ^ (orderOf (c : S) / 2) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdord
    omega
  have hd2 : ((c : S) ^ (orderOf (c : S) / 2)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one ((c : S) ^ (orderOf (c : S) / 2))
    rwa [hdord] at this
  have hdc : (c : S) ^ (orderOf (c : S) / 2) ∈ Subgroup.center S := Subgroup.pow_mem _ c.2 _
  intro hbot
  have hmem : (((c : S) ^ (orderOf (c : S) / 2) : S) : G) ∈ omegaCenter S :=
    mem_omegaCenter.2 ⟨(((c : S) ^ (orderOf (c : S) / 2) : S)).2, fun x hx =>
      (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hdc ⟨x, hx⟩).symm)),
      congrArg Subtype.val hd2⟩
  rw [hbot] at hmem
  exact hd1 (Subtype.ext (Subgroup.mem_bot.1 hmem))

theorem omegaCenter_le_omegaCenter {S O : Subgroup G} (hOS : O ≤ S)
    (hC : S ⊓ centralizer (O : Set G) ≤ O) : omegaCenter S ≤ omegaCenter O := by
  intro g hg
  obtain ⟨hgS, hgC, hg2⟩ := mem_omegaCenter.1 hg
  have hgO : g ∈ O := hC (Subgroup.mem_inf.2 ⟨hgS,
    Subgroup.mem_centralizer_iff.2 fun h hh => (hgC h (hOS hh)).symm⟩)
  exact mem_omegaCenter.2 ⟨hgO, fun x hx => hgC x (hOS hx), hg2⟩

theorem thompsonSubgroup_le' (S : Subgroup G) : CFSG.thompsonSubgroup S ≤ S :=
  CFSG.ambientMaxCardThompson_le S

private theorem map_mem_thompsonAbelianSubgroups_aux {H : Type*} [Group H] (e : G ≃* H)
    {P A : Subgroup G} (hA : A ∈ CFSG.thompsonAbelianSubgroups P) :
    A.map e.toMonoidHom ∈ CFSG.thompsonAbelianSubgroups (P.map e.toMonoidHom) := by
  obtain ⟨hAP, hAc, hAm⟩ := hA
  refine ⟨Subgroup.map_mono hAP, inferInstance, ?_⟩
  intro B hB hBc
  have hBP : B.map e.symm.toMonoidHom ≤ P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hB hy
    simpa using hz
  calc
    Nat.card B = Nat.card (B.map e.symm.toMonoidHom) :=
      (Subgroup.card_map_of_injective (K := B) e.symm.injective).symm
    _ ≤ Nat.card A := hAm _ hBP inferInstance
    _ = Nat.card (A.map e.toMonoidHom) :=
      (Subgroup.card_map_of_injective (K := A) e.injective).symm

private theorem map_thompsonSubgroup_le_aux {H : Type*} [Group H] (e : G ≃* H) (P : Subgroup G) :
    (CFSG.thompsonSubgroup P).map e.toMonoidHom ≤
      CFSG.thompsonSubgroup (P.map e.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun A hA => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (map_mem_thompsonAbelianSubgroups_aux e hA)

private theorem thompsonSubgroup_top_map_subtype_aux (S : Subgroup G) :
    (CFSG.thompsonSubgroup (⊤ : Subgroup S)).map S.subtype = CFSG.thompsonSubgroup S := by
  classical
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro A hA
    exact (Subgroup.map_le_iff_le_comap).mp <| le_sSup <| by
      refine ⟨?_, ?_, ?_⟩
      · simpa using (Subgroup.map_subtype_le (H := S) (K := A))
      · let : IsMulCommutative A := hA.2.1
        exact Subgroup.map_isMulCommutative (H := A) S.subtype
      · intro B hB hBcomm
        let B' : Subgroup S := B.subgroupOf S
        have hAmax := hA.2.2 B' (by simp) (by
          let : IsMulCommutative B := hBcomm
          infer_instance)
        calc
          Nat.card B = Nat.card B' := by
            simpa [B', Subgroup.map_subgroupOf_eq_of_le hB] using
              (Subgroup.card_subtype S B')
          _ ≤ Nat.card A := hAmax
          _ = Nat.card (A.map S.subtype) := by
            symm
            exact Subgroup.card_map_of_injective (K := A) S.subtype_injective
  · refine sSup_le ?_
    intro A hA
    have hAin :
        A.subgroupOf S ∈ CFSG.thompsonAbelianSubgroups (⊤ : Subgroup S) := by
      refine ⟨by simp, ?_, ?_⟩
      · let : IsMulCommutative A := hA.2.1
        infer_instance
      · intro B hB hBcomm
        have hAmax := hA.2.2 (B.map S.subtype) (by
          simpa using (Subgroup.map_subtype_le (H := S) (K := B))) (by
            exact Subgroup.map_isMulCommutative (H := B) S.subtype)
        calc
          Nat.card B = Nat.card (B.map S.subtype) := by
            symm
            exact Subgroup.card_subtype S B
          _ ≤ Nat.card A := hAmax
          _ = Nat.card (A.subgroupOf S) := by
            simpa [Subgroup.map_subgroupOf_eq_of_le hA.1] using
              (Subgroup.card_subtype S (A.subgroupOf S))
    calc
      A = (A.subgroupOf S).map S.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA.1]
      _ ≤ (CFSG.thompsonSubgroup (⊤ : Subgroup S)).map S.subtype := by
        exact Subgroup.map_mono (le_sSup hAin)

private theorem thompsonSubgroup_subgroupOf_eq_aux (S : Subgroup G) :
    (CFSG.thompsonSubgroup S).subgroupOf S = CFSG.thompsonSubgroup (⊤ : Subgroup S) := by
  apply Subgroup.map_injective S.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (thompsonSubgroup_le' S),
    thompsonSubgroup_top_map_subtype_aux]

theorem thompsonSubgroup_characteristic [Finite G] (S : Subgroup G) :
    ((CFSG.thompsonSubgroup S).subgroupOf S).Characteristic := by
  rw [thompsonSubgroup_subgroupOf_eq_aux, Subgroup.characteristic_iff_map_le]
  intro φ
  have h := map_thompsonSubgroup_le_aux φ (⊤ : Subgroup S)
  rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h

theorem thompsonSubgroup_ne_bot [Finite G] {S : Subgroup G} (hne : S ≠ ⊥) :
    CFSG.thompsonSubgroup S ≠ ⊥ :=
  CFSG.thompsonSubgroup_ne_bot_of_finite hne

private theorem normalizer_le_normalizer_thompsonSubgroup_aux (O : Subgroup G) :
    normalizer (O : Set G) ≤ normalizer (CFSG.thompsonSubgroup O : Set G) :=
  Adapters.leanEval_thompsonSubgroup_eq O ▸ CFSG.Open.normalizer_le_normalizer_thompsonSubgroup O

theorem normalizer_le_normalizer_thompsonSubgroup [Finite G] {S O : Subgroup G} (hOS : O ≤ S)
    (h : ∀ A ∈ CFSG.thompsonAbelianSubgroups S, A ≤ O) :
    normalizer (O : Set G) ≤ normalizer (CFSG.thompsonSubgroup S : Set G) := by
  have hJ : CFSG.thompsonSubgroup S = CFSG.thompsonSubgroup O := by
    apply le_antisymm
    · exact sSup_le fun A hA =>
        le_sSup (CFSG.thompsonAbelianSubgroups_mem_of_le hOS hA (h A hA))
    · obtain ⟨A, hA⟩ := CFSG.thompsonAbelianSubgroups_nonempty (G := G) S
      exact CFSG.thompsonSubgroup_le_of_mem_thompsonAbelianSubgroups hOS hA (h A hA)
  rw [hJ]
  exact normalizer_le_normalizer_thompsonSubgroup_aux O

private theorem index_le_two_aux {K : Type*} [Group K] (D : Subgroup K)
    (h : ∀ b b' : K, b ∉ D → b' ∉ D → b⁻¹ * b' ∈ D) : D.index ≤ 2 := by
  by_cases hD : D = ⊤
  · rw [hD, Subgroup.index_top]
    omega
  · obtain ⟨b₀, hb₀⟩ : ∃ b₀, b₀ ∉ D := by
      by_contra hcon
      push Not at hcon
      exact hD (eq_top_iff.2 fun x _ => hcon x)
    refine (Subgroup.index_eq_two_iff.2 ⟨b₀, fun b => ?_⟩).le
    by_cases hb : b ∈ D
    · exact Or.inr ⟨hb, fun hbb => hb₀ (by simpa using D.mul_mem (D.inv_mem hb) hbb)⟩
    · refine Or.inl ⟨?_, hb⟩
      have := h b⁻¹ b₀ (by simpa using hb) hb₀
      simpa using this

private theorem exists_of_index_le_two_aux {K : Type*} [Group K] [Finite K] (D : Subgroup K)
    (h : D.index ≤ 2) : D = ⊤ ∨ ∃ b₀ : K, ∀ b : K, b ∈ D ∨ b * b₀ ∈ D := by
  have h0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge D.index 2 with h1 | h2
  · exact Or.inl (Subgroup.index_eq_one.1 (by omega))
  · obtain ⟨b₀, hb₀⟩ := Subgroup.index_eq_two_iff.1 (by omega : D.index = 2)
    refine Or.inr ⟨b₀, fun b => ?_⟩
    rcases hb₀ b with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inr h1
    · exact Or.inl h1

private theorem card_le_two_mul_card_inf_aux [Finite G] {A O : Subgroup G}
    (hAO : ∀ a ∈ A, ∀ a' ∈ A, a ∉ O → a' ∉ O → a⁻¹ * a' ∈ O) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ O) := by
  have hidx : O.relIndex A ≤ 2 :=
    index_le_two_aux (O.subgroupOf A) fun b b' hb hb' => hAO _ b.2 _ b'.2 hb hb'
  have h := Subgroup.relIndex_mul_card (H := O) (K := A)
  rw [inf_comm] at h
  calc Nat.card A = O.relIndex A * Nat.card ↥(A ⊓ O) := h.symm
    _ ≤ 2 * Nat.card ↥(A ⊓ O) := Nat.mul_le_mul_right _ hidx

private theorem card_mul_card_le_aux [Finite G] {S A V : Subgroup G}
    (hA : A ∈ CFSG.thompsonAbelianSubgroups S) (hVS : V ≤ S) (hVc : IsMulCommutative V) {a : G}
    (ha : a ∈ A) :
    Nat.card ↥(A ⊓ centralizer (V : Set G)) * Nat.card V ≤
      Nat.card A * Nat.card ↥(centralizer ({a} : Set G) ⊓ V) := by
  obtain ⟨hAS, hAc, hAmax⟩ := hA
  set C : Subgroup G := A ⊓ centralizer (V : Set G)
  have hCA : C ≤ A := inf_le_left
  have hCVc : C ≤ centralizer (V : Set G) := inf_le_right
  have hVC : V ≤ centralizer (C : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun c hc => (Subgroup.mem_centralizer_iff.1 (hCVc hc) v hv).symm
  have hXc : IsMulCommutative ↥(C ⊔ V) := by
    have hCC : C ≤ centralizer (C : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.2 (isMulCommutative_anti hCA)
    have hVV : V ≤ centralizer (V : Set G) := Subgroup.le_centralizer_iff_isMulCommutative.2 hVc
    refine Subgroup.le_centralizer_iff_isMulCommutative.1 (sup_le ?_ ?_)
    · exact Subgroup.le_centralizer_iff.2 (sup_le hCC hVC)
    · exact Subgroup.le_centralizer_iff.2 (sup_le hCVc hVV)
  have hXA : Nat.card ↥(C ⊔ V) ≤ Nat.card ↥A := hAmax _ (sup_le (hCA.trans hAS) hVS) hXc
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := C) (B := V) (hVC.trans (Subgroup.centralizer_le_normalizer _))
  have hCVle : C ⊓ V ≤ centralizer ({a} : Set G) ⊓ V := fun g hg =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      (setLike_mul_comm (hCA (Subgroup.mem_inf.1 hg).1) ha), (Subgroup.mem_inf.1 hg).2⟩
  calc Nat.card ↥C * Nat.card ↥V = Nat.card ↥(C ⊔ V) * Nat.card ↥(C ⊓ V) := hprod.symm
    _ ≤ Nat.card ↥A * Nat.card ↥(centralizer ({a} : Set G) ⊓ V) :=
      Nat.mul_le_mul hXA (Subgroup.card_le_of_le hCVle)

private theorem exists_of_relIndex_centralizer_le_two_aux [Finite G] {V : Subgroup G}
    (hVc : IsMulCommutative V) {a : G} (haN : a ∈ normalizer (V : Set G))
    (hidx : (centralizer ({a} : Set G)).relIndex V ≤ 2) :
    ∃ w ∈ V, ∀ v ∈ V, a * v * a⁻¹ = v ∨ a * v * a⁻¹ = w * v := by
  rcases exists_of_index_le_two_aux ((centralizer ({a} : Set G)).subgroupOf V) hidx with
    hD | ⟨b₀, hb₀⟩
  · refine ⟨1, V.one_mem, fun v hv => Or.inl ?_⟩
    have hva : (⟨v, hv⟩ : V) ∈ (centralizer ({a} : Set G)).subgroupOf V :=
      hD ▸ Subgroup.mem_top _
    have hcomm : a * v = v * a :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hva)).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · have hbV : a * (b₀ : G)⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 haN _).1 (V.inv_mem b₀.2)
    refine ⟨(b₀ : G) * (a * (b₀ : G)⁻¹ * a⁻¹), V.mul_mem b₀.2 hbV, fun v hv => ?_⟩
    rcases hb₀ ⟨v, hv⟩ with hvD | hvD
    · left
      have hcomm : a * v = v * a :=
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hvD)).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    · right
      have hcomm : a * (v * (b₀ : G)) = v * (b₀ : G) * a :=
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hvD)).symm
      have hw : v * ((b₀ : G) * (a * (b₀ : G)⁻¹ * a⁻¹)) =
          (b₀ : G) * (a * (b₀ : G)⁻¹ * a⁻¹) * v :=
        setLike_mul_comm hv (V.mul_mem b₀.2 hbV)
      calc a * v * a⁻¹ = (a * (v * (b₀ : G))) * (b₀ : G)⁻¹ * a⁻¹ := by group
        _ = (v * (b₀ : G) * a) * (b₀ : G)⁻¹ * a⁻¹ := by rw [hcomm]
        _ = v * ((b₀ : G) * (a * (b₀ : G)⁻¹ * a⁻¹)) := by group
        _ = (b₀ : G) * (a * (b₀ : G)⁻¹ * a⁻¹) * v := hw

theorem exists_small_of_mem_thompsonAbelianSubgroups [Finite G] {S A V O : Subgroup G}
    (hA : A ∈ CFSG.thompsonAbelianSubgroups S) (hVS : V ≤ S) (hV : IsElemAbelian 2 V)
    (hOV : V ≤ centralizer (O : Set G))
    (hAO : ∀ a ∈ A, ∀ a' ∈ A, a ∉ O → a' ∉ O → a⁻¹ * a' ∈ O) {a : G} (ha : a ∈ A)
    (haN : a ∈ normalizer (V : Set G)) :
    ∃ w ∈ V, ∀ v ∈ V, a * v * a⁻¹ = v ∨ a * v * a⁻¹ = w * v := by
  refine exists_of_relIndex_centralizer_le_two_aux hV.1 haN ?_
  have hOC : O ≤ centralizer (V : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun h hh => (Subgroup.mem_centralizer_iff.1 (hOV hh) g hg).symm
  have hAC : Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ centralizer (V : Set G)) :=
    (card_le_two_mul_card_inf_aux hAO).trans
      (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (inf_le_inf_left A hOC)))
  have hCpos : 0 < Nat.card ↥(A ⊓ centralizer (V : Set G)) := Nat.card_pos
  have hV2 : Nat.card ↥V ≤ 2 * Nat.card ↥(centralizer ({a} : Set G) ⊓ V) := by
    have hle : Nat.card ↥(A ⊓ centralizer (V : Set G)) * Nat.card ↥V ≤
        Nat.card ↥(A ⊓ centralizer (V : Set G)) *
          (2 * Nat.card ↥(centralizer ({a} : Set G) ⊓ V)) :=
      calc _ ≤ Nat.card ↥A * Nat.card ↥(centralizer ({a} : Set G) ⊓ V) :=
            card_mul_card_le_aux hA hVS hV.1 ha
        _ ≤ (2 * Nat.card ↥(A ⊓ centralizer (V : Set G))) *
              Nat.card ↥(centralizer ({a} : Set G) ⊓ V) := Nat.mul_le_mul_right _ hAC
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hle hCpos
  have h := Subgroup.relIndex_mul_card (H := centralizer ({a} : Set G)) (K := V)
  have hpos : 0 < Nat.card ↥(centralizer ({a} : Set G) ⊓ V) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [h]
  exact hV2

end CFSG.LocalAnalysis.RankThreeTheoremC
