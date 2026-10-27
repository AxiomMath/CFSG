module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

public section

namespace CFSG.ABGTheoremB.RelativeZJ

open CFSG
open scoped Pointwise commutatorElement

section

variable {G : Type*} [Group G]

theorem rzj_eq_one_of_mem_pGroup_sq_eq_one
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (H : Subgroup G) (hHp : IsPGroup p ↥H) {d : G} (hd : d ∈ H) (hdsq : d ^ 2 = 1) :
    d = 1 := by
  have hpow : orderOf (⟨d, hd⟩ : H) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hdsq)
  rcases (IsPGroup.iff_orderOf (p := p) (G := H)).1 hHp (⟨d, hd⟩ : H) with ⟨k, hk⟩
  have hk_dvd : p ^ k ∣ 2 := by simpa [hk] using hpow
  have hk_zero : k = 0 := by
    cases k with
    | zero =>
        rfl
    | succ k =>
        exfalso
        have hpdvd : p ∣ 2 := by
          exact dvd_trans (dvd_pow_self p (Nat.succ_ne_zero _)) hk_dvd
        have hp_eq_two : p = 2 := by
          exact (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hpdvd
        exact hpodd hp_eq_two
  have hord : orderOf (⟨d, hd⟩ : H) = 1 := by
    simpa [hk_zero] using hk
  have htriv : (⟨d, hd⟩ : H) = 1 := orderOf_eq_one_iff.mp hord
  exact congrArg Subtype.val htriv

@[expose] def rzj_replacementCommChain (B A : Subgroup G) : ℕ → Subgroup G
  | 0 => B
  | n + 1 => ⁅rzj_replacementCommChain B A n, A⁆

@[simp] theorem rzj_replacementCommChain_zero (B A : Subgroup G) :
    rzj_replacementCommChain B A 0 = B := rfl

@[simp] theorem rzj_replacementCommChain_succ (B A : Subgroup G) (n : ℕ) :
    rzj_replacementCommChain B A (n + 1) = ⁅rzj_replacementCommChain B A n, A⁆ := rfl

theorem rzj_replacementCommChain_le_normalizer
    (B A : Subgroup G) [B.Normal] :
    ∀ n, A ≤ Subgroup.normalizer (rzj_replacementCommChain B A n : Set G)
  | 0 => by
      rw [rzj_replacementCommChain_zero, Subgroup.normalizer_eq_top (H := B)]
      exact le_top
  | n + 1 => by
      let D : Subgroup G := rzj_replacementCommChain B A n
      let : ((⁅D, A⁆).subgroupOf (D ⊔ A)).Normal := commutator_normal_in_sup D A
      have hsup_norm : D ⊔ A ≤ Subgroup.normalizer (((⁅D, A⁆ : Subgroup G) : Set G)) := by
        exact
          Subgroup.le_normalizer_of_normal_subgroupOf
            (H := ⁅D, A⁆) (K := D ⊔ A) (commutator_le_sup D A)
      rw [rzj_replacementCommChain_succ]
      exact le_sup_right.trans hsup_norm

theorem rzj_replacementCommChain_descends
    (B A : Subgroup G) [B.Normal] (n : ℕ) :
    rzj_replacementCommChain B A (n + 1) ≤ rzj_replacementCommChain B A n := by
  rw [rzj_replacementCommChain_succ]
  refine (Subgroup.commutator_le).2 ?_
  intro x hx a ha
  have ha_norm : a ∈ Subgroup.normalizer (rzj_replacementCommChain B A n : Set G) :=
    rzj_replacementCommChain_le_normalizer B A n ha
  have hconj : a * x⁻¹ * a⁻¹ ∈ rzj_replacementCommChain B A n :=
    (Subgroup.mem_normalizer_iff.mp ha_norm x⁻¹).1
      ((rzj_replacementCommChain B A n).inv_mem hx)
  rw [commutatorElement_def]
  simpa [mul_assoc] using (rzj_replacementCommChain B A n).mul_mem hx hconj

theorem rzj_replacementCommChain_le_left
    (B A : Subgroup G) [B.Normal] :
    ∀ n, rzj_replacementCommChain B A n ≤ B
  | 0 => le_rfl
  | n + 1 =>
      (rzj_replacementCommChain_descends B A n).trans (rzj_replacementCommChain_le_left B A n)

theorem rzj_replacementCommChain_antitone
    (B A : Subgroup G) [B.Normal] {i j : ℕ}
    (hij : i ≤ j) :
    rzj_replacementCommChain B A j ≤ rzj_replacementCommChain B A i := by
  induction hij with
  | refl =>
      exact le_rfl
  | @step j hij ih =>
      exact (rzj_replacementCommChain_descends B A j).trans ih

theorem rzj_replacementCommChain_eq_bot_of_eq_bot_of_le
    (B A : Subgroup G) [B.Normal] {i j : ℕ}
    (hij : i ≤ j) (hi : rzj_replacementCommChain B A i = ⊥) :
    rzj_replacementCommChain B A j = ⊥ := by
  apply le_antisymm
  · exact (rzj_replacementCommChain_antitone B A hij).trans_eq hi
  · exact bot_le

theorem rzj_replacementCommChain_le_sup
    (B A : Subgroup G) :
    ∀ n, rzj_replacementCommChain B A n ≤ B ⊔ A
  | 0 => le_sup_left
  | n + 1 =>
      calc
        rzj_replacementCommChain B A (n + 1) = ⁅rzj_replacementCommChain B A n, A⁆ := by
          rw [rzj_replacementCommChain_succ]
        _ ≤ rzj_replacementCommChain B A n ⊔ A := commutator_le_sup _ _
        _ ≤ B ⊔ A := sup_le (rzj_replacementCommChain_le_sup B A n) le_sup_right

@[expose] def rzj_replacementCommChainSub (B A : Subgroup G) : ℕ → Subgroup ↥(B ⊔ A)
  | 0 => B.subgroupOf (B ⊔ A)
  | n + 1 => ⁅rzj_replacementCommChainSub B A n, A.subgroupOf (B ⊔ A)⁆

@[simp] theorem rzj_replacementCommChainSub_zero (B A : Subgroup G) :
    rzj_replacementCommChainSub B A 0 = B.subgroupOf (B ⊔ A) := rfl

@[simp] theorem rzj_replacementCommChainSub_succ (B A : Subgroup G) (n : ℕ) :
    rzj_replacementCommChainSub B A (n + 1) =
      ⁅rzj_replacementCommChainSub B A n, A.subgroupOf (B ⊔ A)⁆ := rfl

theorem rzj_replacementCommChainSub_eq_subgroupOf
    (B A : Subgroup G) :
    ∀ n,
      rzj_replacementCommChainSub B A n =
        (rzj_replacementCommChain B A n).subgroupOf (B ⊔ A)
  | 0 => by
      ext x
      simp [rzj_replacementCommChainSub, rzj_replacementCommChain]
  | n + 1 => by
      let S : Subgroup G := B ⊔ A
      apply (Subgroup.map_subtype_inj (H := S)).mp
      calc
        (rzj_replacementCommChainSub B A (n + 1)).map S.subtype =
            ⁅(rzj_replacementCommChainSub B A n).map S.subtype,
              (A.subgroupOf S).map S.subtype⁆ := by
              rw [rzj_replacementCommChainSub_succ, Subgroup.map_commutator]
        _ = ⁅rzj_replacementCommChain B A n, A⁆ := by
              rw [rzj_replacementCommChainSub_eq_subgroupOf B A n,
                Subgroup.map_subgroupOf_eq_of_le
                  (rzj_replacementCommChain_le_sup B A n),
                Subgroup.map_subgroupOf_eq_of_le le_sup_right]
        _ = ((rzj_replacementCommChain B A (n + 1)).subgroupOf S).map S.subtype := by
              simpa [rzj_replacementCommChain_succ] using
                (Subgroup.map_subgroupOf_eq_of_le
                  (rzj_replacementCommChain_le_sup B A (n + 1)))

theorem rzj_replacementCommChainSub_le_lowerCentralSeries
    (B A : Subgroup G) :
    ∀ n,
      rzj_replacementCommChainSub B A n ≤
        (⊤ : Subgroup ↥(B ⊔ A)).lowerCentralSeries n
  | 0 => by
      simp [Subgroup.lowerCentralSeries_zero]
  | n + 1 => by
      rw [rzj_replacementCommChainSub_succ, Subgroup.lowerCentralSeries_succ]
      exact
        (Subgroup.commutator_mono
          (rzj_replacementCommChainSub_le_lowerCentralSeries B A n) le_top)

theorem rzj_replacementCommChain_eventually_bot_of_isNilpotent
    (B A : Subgroup G)
    (hnil : Group.IsNilpotent ↥(B ⊔ A)) :
    ∃ n, rzj_replacementCommChain B A n = ⊥ := by
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↥(B ⊔ A))).1 hnil
  refine ⟨n, ?_⟩
  calc
    rzj_replacementCommChain B A n =
        ((rzj_replacementCommChain B A n).subgroupOf (B ⊔ A)).map (B ⊔ A).subtype := by
          symm
          exact Subgroup.map_subgroupOf_eq_of_le (rzj_replacementCommChain_le_sup B A n)
    _ = (rzj_replacementCommChainSub B A n).map (B ⊔ A).subtype := by
          rw [rzj_replacementCommChainSub_eq_subgroupOf]
    _ = ⊥ := by
          apply le_antisymm
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hybot : y ∈ (⊥ : Subgroup ↥(B ⊔ A)) := by
              exact (rzj_replacementCommChainSub_le_lowerCentralSeries B A n).trans_eq hn hy
            simpa using hybot
          · exact bot_le

theorem rzj_replacementCommChain_eventually_bot
    {p : ℕ} [Fact (Nat.Prime p)] [Finite G]
    (B A : Subgroup G)
    (hBAp : IsPGroup p ↥(B ⊔ A)) :
    ∃ n, rzj_replacementCommChain B A n = ⊥ := by
  exact
    rzj_replacementCommChain_eventually_bot_of_isNilpotent B A
      (IsPGroup.isNilpotent (p := p) hBAp)

theorem rzj_replacementCommChain_exists_positive_abelian
    {p : ℕ} [Fact (Nat.Prime p)] [Finite G]
    (B A : Subgroup G) (hBne : B ≠ ⊥)
    (hBAp : IsPGroup p ↥(B ⊔ A)) :
    ∃ n, 0 < n ∧ IsMulCommutative (rzj_replacementCommChain B A n) := by
  obtain ⟨n, hn⟩ := rzj_replacementCommChain_eventually_bot (p := p) B A hBAp
  have hnpos : 0 < n := by
    cases n with
    | zero =>
        exfalso
        exact hBne (by simpa [rzj_replacementCommChain_zero] using hn)
    | succ n =>
        simp
  refine ⟨n, hnpos, ?_⟩
  rw [hn]
  infer_instance

@[expose] def rzj_subgroupCentralizerIn' (U H : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (H : Set G) ⊓ U

theorem rzj_thompsonSubgroup_le (P : Subgroup G) :
    thompsonSubgroup (G := G) P ≤ P := by
  refine sSup_le ?_
  intro A hA
  exact hA.1

theorem rzj_thompsonCenter_le (P : Subgroup G) :
    thompsonCenter (G := G) P ≤ P := by
  calc
    thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
      exact inf_le_left
    _ ≤ P := rzj_thompsonSubgroup_le (G := G) P

theorem rzj_thompsonCenter_isMulCommutative (P : Subgroup G) :
    IsMulCommutative (thompsonCenter (G := G) P) := by
  refine (Subgroup.le_centralizer_iff_isMulCommutative (K := thompsonCenter (G := G) P)).1 ?_
  have hle_left : thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
    exact inf_le_left
  have hle_right :
      thompsonCenter (G := G) P ≤
        Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  exact hle_right.trans <|
    Subgroup.centralizer_le
      (show (thompsonCenter (G := G) P : Set G) ⊆ (thompsonSubgroup (G := G) P : Set G) from
        hle_left)

section ConstraintAndStability

variable (p : ℕ) [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem rzj_pCore_map_le_pCore_of_surjective {H : Type*} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (pCore p G).map f ≤ pCore p H := by
  exact le_sSup <|
    And.intro
      (Subgroup.Normal.map (H := pCore p G) inferInstance f hf)
      (IsPGroup.map (p := p) (H := pCore p G) (pCore_isPGroup (G := G) (p := p)) f)

variable [Finite G]

omit [Finite G] in
theorem rzj_normalizer_le_normalizer_thompsonCenter (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (thompsonCenter (G := G) S : Set G) := by
  classical
  let J : Subgroup G := thompsonSubgroup (G := G) S
  have hJ_map_eq :
      ∀ g ∈ Subgroup.normalizer (S : Set G), J.map (MulAut.conj g).toMonoidHom = J := by
    intro g hg
    let e : G ≃* G := MulAut.conj g
    have himage :
        (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S =
          thompsonAbelianSubgroups (G := G) S := by
      ext A
      constructor
      · rintro ⟨B, hB, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp hg _).1 (hB.1 hy)
        · let : IsMulCommutative B := hB.2.1
          exact Subgroup.map_isMulCommutative (H := B) e.toMonoidHom
        · intro C hC hCcomm
          have hCpre_le : C.map e.symm.toMonoidHom ≤ S := by
            intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
              (Subgroup.normalizer (S : Set G)).inv_mem hg
            simpa [e] using (Subgroup.mem_normalizer_iff.mp hginv _).1 (hC hy)
          have hCpre_comm : IsMulCommutative (C.map e.symm.toMonoidHom) := by
            let : IsMulCommutative C := hCcomm
            exact Subgroup.map_isMulCommutative (H := C) e.symm.toMonoidHom
          have hBmax := hB.2.2 (C.map e.symm.toMonoidHom) hCpre_le hCpre_comm
          calc
            Nat.card C = Nat.card (C.map e.symm.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.symm.injective
            _ ≤ Nat.card B := hBmax
            _ = Nat.card (B.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := B) e.injective
      · intro hA
        refine ⟨A.map e.symm.toMonoidHom, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
              (Subgroup.normalizer (S : Set G)).inv_mem hg
            simpa [e] using (Subgroup.mem_normalizer_iff.mp hginv _).1 (hA.1 hy)
          · let : IsMulCommutative A := hA.2.1
            exact Subgroup.map_isMulCommutative (H := A) e.symm.toMonoidHom
          · intro C hC hCcomm
            have hCpre_le : C.map e.toMonoidHom ≤ S := by
              intro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
              exact (Subgroup.mem_normalizer_iff.mp hg _).1 (hC hy)
            have hCpre_comm : IsMulCommutative (C.map e.toMonoidHom) := by
              let : IsMulCommutative C := hCcomm
              exact Subgroup.map_isMulCommutative (H := C) e.toMonoidHom
            have hAmax := hA.2.2 (C.map e.toMonoidHom) hCpre_le hCpre_comm
            calc
              Nat.card C = Nat.card (C.map e.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := C) e.injective
              _ ≤ Nat.card A := hAmax
              _ = Nat.card (A.map e.symm.toMonoidHom) := by
                symm
                exact Subgroup.card_map_of_injective (K := A) e.symm.injective
        · ext x
          simp
    calc
      J.map (MulAut.conj g).toMonoidHom
          = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) S)) := rfl
      _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) S) := by
        simp
      _ = J := by
        simpa [J, thompsonSubgroup] using congrArg sSup himage
  have hconj_mem :
      ∀ g ∈ Subgroup.normalizer (S : Set G),
        ∀ z ∈ thompsonCenter (G := G) S,
          g * z * g⁻¹ ∈ thompsonCenter (G := G) S := by
    intro g hg z hz
    refine ⟨?_, ?_⟩
    · have hzJ : z ∈ J := by
        simpa [thompsonCenter, centerIn, J] using hz.1
      have hzmap : g * z * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzJ
      rwa [hJ_map_eq g hg] at hzmap
    · exact Subgroup.mem_centralizer_iff.mpr <| by
        intro y hy
        have hy' : g⁻¹ * y * g ∈ J := by
          have hymap :
              g⁻¹ * y * g ∈ J.map (MulAut.conj g⁻¹).toMonoidHom := by
            simpa [J] using
              (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hy)
          rwa [hJ_map_eq g⁻¹ ((Subgroup.normalizer (S : Set G)).inv_mem hg)] at hymap
        have hzcent :
            z ∈ Subgroup.centralizer (J : Set G) := by
          simpa [thompsonCenter, centerIn, J] using hz.2
        have hcomm := (Subgroup.mem_centralizer_iff.mp hzcent _ hy')
        have hcomm' := congrArg (fun x : G => g * x * g⁻¹) hcomm
        simpa [mul_assoc] using hcomm'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact hconj_mem g hg z hz
  · intro hz
    have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normalizer (S : Set G)).inv_mem hg
    have hz' := hconj_mem g⁻¹ hginv (g * z * g⁻¹) hz
    simpa [mul_assoc] using hz'

omit [Finite G] in
theorem rzj_thompsonAbelianSubgroups_subset_of_contains_mem
    {P R : Subgroup G} (hR_le_P : R ≤ P) {A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hA_le_R : A ≤ R) :
    ∀ {B : Subgroup G},
      B ∈ thompsonAbelianSubgroups (G := G) R →
        B ∈ thompsonAbelianSubgroups (G := G) P := by
  intro B hB
  refine ⟨hB.1.trans hR_le_P, hB.2.1, ?_⟩
  intro C hC hCcomm
  have hBmax := hB.2.2 A hA_le_R hA.2.1
  have hAmax := hA.2.2 C hC hCcomm
  exact hAmax.trans hBmax


omit [Finite G] in
theorem rzj_thompsonCenter_le_of_mem_thompsonAbelianSubgroups
    {P R : Subgroup G} (hR_le_P : R ≤ P) {A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hZ_le_A : thompsonCenter (G := G) P ≤ A)
    (hA_le_R : A ≤ R) :
    thompsonCenter (G := G) P ≤ thompsonCenter (G := G) R :=
  CFSG.thompsonCenter_le_of_mem_thompsonAbelianSubgroups hR_le_P hA hZ_le_A hA_le_R


theorem rzj_thompsonSubgroup_eq_of_le
    {P R : Subgroup G} (hR_le_P : R ≤ P)
    (hJP_le_R : thompsonSubgroup (G := G) P ≤ R) :
    thompsonSubgroup (G := G) R = thompsonSubgroup (G := G) P :=
  CFSG.thompsonSubgroup_eq_of_le hR_le_P hJP_le_R

theorem rzj_thompsonCenter_eq_of_le
    {P R : Subgroup G} (hR_le_P : R ≤ P)
    (hJP_le_R : thompsonSubgroup (G := G) P ≤ R) :
    thompsonCenter (G := G) R = thompsonCenter (G := G) P := by
  change centerIn (thompsonSubgroup R) = centerIn (thompsonSubgroup P)
  rw [rzj_thompsonSubgroup_eq_of_le (G := G) hR_le_P hJP_le_R]

theorem rzj_thompsonAbelianSubgroups_centralizer_eq
    {P A : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P) :
    rzj_subgroupCentralizerIn' P A = A := by
  apply le_antisymm
  · intro x hx
    let B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {x})
    have hB_le_P : B ≤ P := by
      refine (Subgroup.closure_le (K := P)).2 ?_
      intro y hy
      rcases hy with hyA | rfl
      · exact hA.1 hyA
      · exact hx.2
    have hB_comm : IsMulCommutative B := by
      change IsMulCommutative (Subgroup.closure ((A : Set G) ∪ {x}))
      let : IsMulCommutative A := hA.2.1
      exact Subgroup.isMulCommutative_closure (k := ((A : Set G) ∪ {x})) <| by
        intro y hy z hz _
        rcases hy with hyA | rfl
        · rcases hz with hzA | rfl
          · exact setLike_mul_comm (s := A) hyA hzA
          · exact Subgroup.mem_centralizer_iff.mp hx.1 _ hyA
        · rcases hz with hzA | rfl
          · exact (Subgroup.mem_centralizer_iff.mp hx.1 _ hzA).symm
          · simp
    have hB_card_le : Nat.card B ≤ Nat.card A := hA.2.2 B hB_le_P hB_comm
    have hA_le_B : A ≤ B := by
      intro y hy
      exact Subgroup.subset_closure (Or.inl hy)
    have hB_eq_A : A = B := Subgroup.eq_of_le_of_card_ge hA_le_B hB_card_le
    have hxB : x ∈ B := Subgroup.subset_closure (Or.inr (by simp))
    rw [← hB_eq_A] at hxB
    exact hxB
  · intro x hx
    refine ⟨?_, hA.1 hx⟩
    exact ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1) hx

theorem rzj_replacementCommChain_le_of_succ_eq_bot
    {P B A : Subgroup G} [B.Normal]
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hB_le_P : B ≤ P) {n : ℕ}
    (hsucc : rzj_replacementCommChain B A (n + 1) = ⊥) :
    rzj_replacementCommChain B A n ≤ A := by
  have hcent : rzj_replacementCommChain B A n ≤ Subgroup.centralizer (A : Set G) := by
    exact
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 <| by
        simpa [rzj_replacementCommChain_succ] using hsucc
  have hleP : rzj_replacementCommChain B A n ≤ P := by
    exact (rzj_replacementCommChain_le_left B A n).trans hB_le_P
  intro x hx
  have hx' : x ∈ rzj_subgroupCentralizerIn' P A := ⟨hcent hx, hleP hx⟩
  rwa [rzj_thompsonAbelianSubgroups_centralizer_eq (G := G) hA] at hx'

omit [Finite G] in
theorem rzj_inf_le_centralizer_commutator_of_commutator_le
    {P B A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P)
    (hBB_le_A : ⁅B, B⁆ ≤ A) :
    A ⊓ B ≤ Subgroup.centralizer (((⁅B, A⁆ : Subgroup G) : Set G)) :=
  CFSG.inf_le_centralizer_commutator_of_commutator_le hA hBB_le_A

theorem rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
    {P A B : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hB_le_P : B ≤ P) :
    B ≤ Subgroup.normalizer (A : Set G) ↔ ⁅⁅B, A⁆, A⁆ = ⊥ := by
  constructor
  · intro hB_norm
    have hBA_le_A : ⁅B, A⁆ ≤ A := by
      refine (Subgroup.commutator_le).2 ?_
      intro b hb a ha
      have hb_norm : b ∈ Subgroup.normalizer (A : Set G) := hB_norm hb
      have hba : b * a * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hb_norm a).1 ha
      rw [commutatorElement_def]
      simpa [mul_assoc] using A.mul_mem hba (A.inv_mem ha)
    have hA_le_centralizer_A :
        A ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2
      (hBA_le_A.trans hA_le_centralizer_A)
  · intro hcomm2
    have hBA_le_centralizer_A : ⁅B, A⁆ ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm2
    have hBA_le_P : ⁅B, A⁆ ≤ P := by
      exact (Subgroup.commutator_mono hB_le_P hA.1).trans (Subgroup.commutator_le_self P)
    have hBA_le_A : ⁅B, A⁆ ≤ A := by
      intro x hx
      have hx' : x ∈ rzj_subgroupCentralizerIn' P A := ⟨hBA_le_centralizer_A hx, hBA_le_P hx⟩
      rwa [rzj_thompsonAbelianSubgroups_centralizer_eq (G := G) hA] at hx'
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hcomm : ⁅b, a⁆ ∈ A := hBA_le_A (Subgroup.commutator_mem_commutator hb ha)
      rw [show b * a * b⁻¹ = ⁅b, a⁆ * a by simp [commutatorElement_def, mul_assoc]]
      exact A.mul_mem hcomm ha
    · intro hba
      have hbinv : b⁻¹ ∈ B := B.inv_mem hb
      have hcomm : ⁅b⁻¹, b * a * b⁻¹⁆ ∈ A :=
        hBA_le_A (Subgroup.commutator_mem_commutator hbinv hba)
      have : b⁻¹ * (b * a * b⁻¹) * b ∈ A := by
        rw [show b⁻¹ * (b * a * b⁻¹) * b = ⁅b⁻¹, b * a * b⁻¹⁆ * (b * a * b⁻¹) by
          simp [commutatorElement_def, mul_assoc]]
        exact A.mul_mem hcomm hba
      simpa [mul_assoc] using this

theorem rzj_replacementCommChain_two_ne_bot_of_not_normalizer
    {P B A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) (hB_le_P : B ≤ P)
    (hB_not_norm : ¬ B ≤ Subgroup.normalizer (A : Set G)) :
    rzj_replacementCommChain B A 2 ≠ ⊥ := by
  intro htwo_bot
  apply hB_not_norm
  exact
    (rzj_thompsonAbelianSubgroups_normalizer_iff_commutator_eq_bot
      (G := G) (P := P) (A := A) (B := B) hA hB_le_P).2 <| by
        simpa [rzj_replacementCommChain_succ, rzj_replacementCommChain_zero] using htwo_bot

theorem rzj_thompsonReplacement_base
    {P A : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups (G := G) P)
    {x : G} (hxP : x ∈ P)
    (hM_comm :
      IsMulCommutative
        ((Subgroup.closure {g : G | ∃ u ∈ A, ⁅x, u⁆ = g} : Subgroup G))) :
    let M : Subgroup G := Subgroup.closure {g : G | ∃ u ∈ A, ⁅x, u⁆ = g}
    let C : Subgroup G := rzj_subgroupCentralizerIn' A M
    M ⊔ C ∈ thompsonAbelianSubgroups (G := G) P := by
  classical
  let M : Subgroup G := Subgroup.closure {g : G | ∃ u ∈ A, ⁅x, u⁆ = g}
  let C : Subgroup G := rzj_subgroupCentralizerIn' A M
  refine ⟨?_, ?_, ?_⟩
  · have hM_le_P : M ≤ P := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      exact
        (Subgroup.commutator_le_self P)
          (Subgroup.commutator_mem_commutator hxP (hA.1 hu))
    exact sup_le hM_le_P (fun y hy => hA.1 hy.2)
  · rw [Subgroup.sup_eq_closure]
    let : IsMulCommutative A := hA.2.1
    exact Subgroup.isMulCommutative_closure
      (k := (((M : Subgroup G) : Set G) ∪ ((C : Subgroup G) : Set G))) <| by
        intro y hy z hz _
        rcases hy with hyM | hyC
        · rcases hz with hzM | hzC
          · exact
              setLike_mul_comm
                (s := M) hyM hzM
          · exact Subgroup.mem_centralizer_iff.mp hzC.1 _ hyM
        · rcases hz with hzM | hzC
          · exact (Subgroup.mem_centralizer_iff.mp hyC.1 _ hzM).symm
          · exact
              setLike_mul_comm
                (s := A) hyC.2 hzC.2
  · intro B hB_le_P hB_comm
    have hB_card_le_A : Nat.card B ≤ Nat.card A := hA.2.2 B hB_le_P hB_comm
    have hA_card_le :
        Nat.card A ≤
          Nat.card ↥(M ⊔ C) := by
      let M0 : Subgroup G := M
      let C0 : Subgroup G := rzj_subgroupCentralizerIn' A M0
      have hM0_comm : IsMulCommutative ↥M0 := by
        simpa [M0] using hM_comm
      change Nat.card A ≤ Nat.card ↥(M0 ⊔ C0)
      have hC0_le_A : C0 ≤ A := by
        intro y hy
        exact hy.2
      let D0 : Subgroup G := rzj_subgroupCentralizerIn' M0 A
      have hM0_le_P : M0 ≤ P := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with ⟨u, hu, rfl⟩
        exact
          (Subgroup.commutator_le_self P)
            (Subgroup.commutator_mem_commutator hxP (hA.1 hu))
      have hD0_le_M0 : D0 ≤ M0 := by
        intro y hy
        exact hy.2
      have hcentP_eq_A : rzj_subgroupCentralizerIn' P A = A :=
        rzj_thompsonAbelianSubgroups_centralizer_eq (G := G) hA
      have hA_le_centA : A ≤ Subgroup.centralizer (A : Set G) :=
        (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1
      have hD0_le_A : D0 ≤ A := by
        intro y hy
        have hyPA : y ∈ rzj_subgroupCentralizerIn' P A := by
          exact ⟨hy.1, hM0_le_P hy.2⟩
        simpa [hcentP_eq_A] using hyPA
      have hD0_eq_inf : D0 = M0 ⊓ C0 := by
        ext y
        constructor
        · intro hy
          refine ⟨hy.2, ⟨?_, hD0_le_A hy⟩⟩
          exact ((Subgroup.le_centralizer_iff_isMulCommutative (K := M0)).2 hM0_comm) hy.2
        · rintro ⟨hyM, hyC0⟩
          exact ⟨hA_le_centA hyC0.2, hyM⟩
      have hquot_le :
          Nat.card (A ⧸ C0.subgroupOf A) ≤ Nat.card (M0 ⧸ D0.subgroupOf M0) := by
        classical
        let : IsMulCommutative A := hA.2.1
        have hcomm_swap {a c : G} (ha : a ∈ A) (hc : c ∈ A)
            (haxc : ⁅⁅x, a⁆, c⁆ = 1) :
            ⁅⁅x, c⁆, a⁆ = 1 := by
          have hxaM0 : ⁅x, a⁆ ∈ M0 := by
            exact Subgroup.subset_closure ⟨a, ha, rfl⟩
          have hxcM0 : ⁅x, c⁆ ∈ M0 := by
            exact Subgroup.subset_closure ⟨c, hc, rfl⟩
          have hac : Commute a c := by
            exact setLike_mul_comm (s := A) ha hc
          let s : G := x * a * x⁻¹
          let t : G := x * c * x⁻¹
          let β : G := ⁅x, a⁆
          let δ : G := ⁅x, c⁆
          have hs_eq : s = β * a := by
            dsimp [s, β]
            simp [commutatorElement_def, mul_assoc]
          have hβ_eq : β = s * a⁻¹ := by
            dsimp [s, β]
            simp [commutatorElement_def, mul_assoc]
          have hδ_eq : δ = t * c⁻¹ := by
            dsimp [t, δ]
            simp [commutatorElement_def, mul_assoc]
          have hβc : Commute β c := commutatorElement_eq_one_iff_commute.mp haxc
          have hs_c : Commute s c := by
            change s * c = c * s
            calc
              s * c = (β * a) * c := by rw [hs_eq]
              _ = β * (a * c) := by simp [mul_assoc]
              _ = β * (c * a) := by rw [hac.eq]
              _ = (β * c) * a := by simp [mul_assoc]
              _ = (c * β) * a := by rw [hβc.eq]
              _ = c * (β * a) := by simp [mul_assoc]
              _ = c * s := by rw [hs_eq]
          have hst : Commute s t := by
            change s * t = t * s
            calc
              s * t = (x * a * x⁻¹) * (x * c * x⁻¹) := by rfl
              _ = x * a * c * x⁻¹ := by simp [mul_assoc]
              _ = x * (a * c) * x⁻¹ := by simp [mul_assoc]
              _ = x * (c * a) * x⁻¹ := by rw [hac.eq]
              _ = x * c * a * x⁻¹ := by simp [mul_assoc]
              _ = (x * c * x⁻¹) * (x * a * x⁻¹) := by simp [mul_assoc]
              _ = t * s := by rfl
          have hβδ : Commute β δ := by
            dsimp [β, δ]
            exact setLike_mul_comm (s := M0) hxaM0 hxcM0
          have hAinvCinv : Commute a⁻¹ c⁻¹ := (hac.inv_left).inv_right
          have hAinv_t_cinv : a⁻¹ * t * c⁻¹ = t * a⁻¹ * c⁻¹ := by
            have hs_eq' :
                s * (a⁻¹ * t * c⁻¹) = s * (t * a⁻¹ * c⁻¹) := by
              calc
                s * (a⁻¹ * t * c⁻¹) = (s * a⁻¹) * (t * c⁻¹) := by simp [mul_assoc]
                _ = β * δ := by rw [hβ_eq, hδ_eq]
                _ = δ * β := by rw [hβδ.eq]
                _ = (t * c⁻¹) * (s * a⁻¹) := by rw [hδ_eq, hβ_eq]
                _ = t * (c⁻¹ * s) * a⁻¹ := by simp [mul_assoc]
                _ = t * (s * c⁻¹) * a⁻¹ := by rw [(hs_c.inv_right).eq]
                _ = (t * s) * c⁻¹ * a⁻¹ := by simp [mul_assoc]
                _ = (s * t) * c⁻¹ * a⁻¹ := by rw [hst.eq]
                _ = s * (t * c⁻¹ * a⁻¹) := by simp [mul_assoc]
                _ = s * (t * (c⁻¹ * a⁻¹)) := by simp [mul_assoc]
                _ = s * (t * (a⁻¹ * c⁻¹)) := by rw [← hAinvCinv.eq]
                _ = s * (t * a⁻¹ * c⁻¹) := by simp [mul_assoc]
            exact mul_left_cancel hs_eq'
          have hAinv_t : a⁻¹ * t = t * a⁻¹ := by
            have hmul := congrArg (fun z => z * c) hAinv_t_cinv
            simpa [mul_assoc] using hmul
          have ht_a : Commute t a := by
            have htaInv : Commute a⁻¹ t := by
              change a⁻¹ * t = t * a⁻¹
              rw [hAinv_t]
            simpa using htaInv.inv_left.symm
          have hcInv_a : c⁻¹ * a = a * c⁻¹ := by
            simpa using (hac.inv_right.symm.eq)
          have hδa : Commute δ a := by
            change δ * a = a * δ
            calc
              δ * a = (t * c⁻¹) * a := by rw [hδ_eq]
              _ = t * (c⁻¹ * a) := by simp [mul_assoc]
              _ = t * (a * c⁻¹) := by rw [hcInv_a]
              _ = (t * a) * c⁻¹ := by simp [mul_assoc]
              _ = (a * t) * c⁻¹ := by rw [ht_a.eq]
              _ = a * (t * c⁻¹) := by simp [mul_assoc]
              _ = a * δ := by rw [hδ_eq]
          exact commutatorElement_eq_one_iff_commute.mpr hδa
        have hcommImage_mem (a : A) : ⁅x, (a : G)⁆ ∈ M0 := by
          exact Subgroup.subset_closure ⟨(a : G), a.2, rfl⟩
        let commImage : A → M0 := fun a => ⟨⁅x, (a : G)⁆, hcommImage_mem a⟩
        have hcommImage_calc {u v : A} :
            (((commImage u : M0)⁻¹ * commImage v : M0) : G) =
              (u : G) * ⁅x, ((u : G)⁻¹ * (v : G))⁆ * (u : G)⁻¹ := by
          simp [commImage, commutatorElement_def, mul_assoc]
        have hxc_centA_of_mem {c : G} (hcC0 : c ∈ C0) :
            ⁅x, c⁆ ∈ Subgroup.centralizer (A : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have hcA : c ∈ A := hC0_le_A hcC0
          have hxaM0 : ⁅x, a⁆ ∈ M0 := by
            exact Subgroup.subset_closure ⟨a, ha, rfl⟩
          have haxc : ⁅⁅x, a⁆, c⁆ = 1 := by
            exact
              commutatorElement_eq_one_iff_commute.mpr
                (Subgroup.mem_centralizer_iff.mp hcC0.1 _ hxaM0)
          have hxca : ⁅⁅x, c⁆, a⁆ = 1 := hcomm_swap ha hcA haxc
          exact (commutatorElement_eq_one_iff_commute.mp hxca).symm.eq
        have hc_cent_M0_of_mem {c : G} (hcA : c ∈ A)
            (hxc_centA : ⁅x, c⁆ ∈ Subgroup.centralizer (A : Set G)) :
            c ∈ Subgroup.centralizer (M0 : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hyc : Commute y c := by
            refine
              Subgroup.closure_induction
                (p := fun z _ => Commute z c) ?_ ?_ ?_ ?_ hy
            · intro g hg
              rcases hg with ⟨a, ha, rfl⟩
              have hxca : ⁅⁅x, c⁆, a⁆ = 1 := by
                have hcomm : Commute ⁅x, c⁆ a := by
                  show ⁅x, c⁆ * a = a * ⁅x, c⁆
                  exact ((Subgroup.mem_centralizer_iff.mp hxc_centA) _ ha).symm
                exact commutatorElement_eq_one_iff_commute.mpr hcomm
              have haxc : ⁅⁅x, a⁆, c⁆ = 1 := by
                exact hcomm_swap hcA ha hxca
              exact commutatorElement_eq_one_iff_commute.mp haxc
            · exact Commute.one_left c
            · intro g₁ g₂ _ _ h₁ h₂
              show Commute (g₁ * g₂) c
              calc
                (g₁ * g₂) * c = g₁ * (g₂ * c) := by simp [mul_assoc]
                _ = g₁ * (c * g₂) := by rw [h₂.eq]
                _ = (g₁ * c) * g₂ := by simp [mul_assoc]
                _ = (c * g₁) * g₂ := by rw [h₁.eq]
                _ = c * (g₁ * g₂) := by simp [mul_assoc]
            · intro g _ h
              exact h.inv_left
          exact hyc.eq
        let f : A ⧸ C0.subgroupOf A → M0 ⧸ D0.subgroupOf M0 :=
          Quotient.map'
            commImage
            (by
              intro u v huv
              apply QuotientGroup.leftRel_apply.mpr
              change
                (((commImage u : M0)⁻¹ * commImage v : M0) ∈
                  D0.subgroupOf M0)
              have huv' : ((u : G)⁻¹ * (v : G)) ∈ C0 := by
                simpa [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] using huv
              have hxc_centA : ⁅x, ((u : G)⁻¹ * (v : G))⁆ ∈ Subgroup.centralizer (A : Set G) := by
                exact hxc_centA_of_mem huv'
              have hmemD0 :
                  (((commImage u : M0)⁻¹ * commImage v : M0) : G) ∈ D0 := by
                refine ⟨?_, ?_⟩
                · let c : G := (u : G)⁻¹ * (v : G)
                  have hcalc :
                      (((commImage u : M0)⁻¹ * commImage v : M0) : G) =
                        (u : G) * ⁅x, c⁆ * (u : G)⁻¹ := by
                    simpa [commImage, c] using (hcommImage_calc (u := u) (v := v))
                  have hu_centA : (u : G) ∈ Subgroup.centralizer (A : Set G) := hA_le_centA u.2
                  have hconj_cent :
                      (u : G) * ⁅x, c⁆ * (u : G)⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
                    exact (Subgroup.centralizer (A : Set G)).mul_mem
                      ((Subgroup.centralizer (A : Set G)).mul_mem hu_centA hxc_centA)
                      ((Subgroup.centralizer (A : Set G)).inv_mem hu_centA)
                  exact hcalc ▸ hconj_cent
                · simpa using (((commImage u : M0)⁻¹ * commImage v : M0).2)
              simpa [Subgroup.mem_subgroupOf] using hmemD0)
        have hf_inj : Function.Injective f := by
          intro q1 q2 hq
          refine Quotient.inductionOn₂' q1 q2 ?_ hq
          intro u v huv
          apply Quotient.sound
          apply QuotientGroup.leftRel_apply.mpr
          change (u⁻¹ * v : A) ∈ C0.subgroupOf A
          have huv' :
              ((commImage u : M0)⁻¹ * commImage v : M0) ∈
                D0.subgroupOf M0 := by
            simpa [QuotientGroup.leftRel_apply] using (Quotient.exact' huv)
          let c : G := (u : G)⁻¹ * (v : G)
          have hcA : c ∈ A := A.mul_mem (A.inv_mem u.2) v.2
          have hmemD0 :
              ((((commImage u : M0)⁻¹ * commImage v : M0) : M0) : G) ∈ D0 := by
            simpa [Subgroup.mem_subgroupOf] using huv'
          have hd_centA :
              ((((commImage u : M0)⁻¹ * commImage v : M0) : M0) : G) ∈
                Subgroup.centralizer (A : Set G) := hmemD0.1
          have hcalc :
              (((commImage u : M0)⁻¹ * commImage v : M0) : G) =
                (u : G) * ⁅x, c⁆ * (u : G)⁻¹ := by
            simpa [commImage, c] using (hcommImage_calc (u := u) (v := v))
          have hu_centA : (u : G) ∈ Subgroup.centralizer (A : Set G) := hA_le_centA u.2
          have hxc_cent : ⁅x, c⁆ ∈ Subgroup.centralizer (A : Set G) := by
            have : (u : G)⁻¹ *
                ((((commImage u : M0)⁻¹ * commImage v : M0) : M0) : G) *
                (u : G) ∈ Subgroup.centralizer (A : Set G) := by
              exact (Subgroup.centralizer (A : Set G)).mul_mem
                ((Subgroup.centralizer (A : Set G)).mul_mem
                  ((Subgroup.centralizer (A : Set G)).inv_mem hu_centA) hd_centA)
                hu_centA
            simpa [hcalc, mul_assoc] using this
          have hc_cent_M0 : c ∈ Subgroup.centralizer (M0 : Set G) := by
            exact hc_cent_M0_of_mem hcA hxc_cent
          exact ⟨hc_cent_M0, hcA⟩
        exact Nat.card_le_card_of_injective f hf_inj
      have hcardA :
          Nat.card A = Nat.card (A ⧸ C0.subgroupOf A) * Nat.card C0 := by
        have hcardA' :
            Nat.card A = Nat.card (A ⧸ C0.subgroupOf A) * Nat.card (C0.subgroupOf A) := by
          simpa using
            (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := C0.subgroupOf A))
        have hcardC0 : Nat.card (C0.subgroupOf A) = Nat.card C0 := by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := C0) (K := A) hC0_le_A).toEquiv
        rw [hcardA', hcardC0]
      have hcardMC :
          Nat.card ↥(M0 ⊔ C0) =
            Nat.card (M0 ⧸ D0.subgroupOf M0) * Nat.card C0 := by
        let H : Subgroup G := M0 ⊔ C0
        let K : Subgroup H := C0.subgroupOf H
        have hC0_le_centM0 : C0 ≤ Subgroup.centralizer (M0 : Set G) := by
          intro y hy
          exact hy.1
        have hM0_le_normC0 : M0 ≤ Subgroup.normalizer (C0 : Set G) := by
          intro y hy
          rw [Subgroup.mem_normalizer_iff]
          intro z
          constructor
          · intro hz
            have hyz : z * y = y * z :=
              (Subgroup.le_centralizer_iff).1 hC0_le_centM0 hy z hz
            have hconj : y * z * y⁻¹ = z := by
              calc
                y * z * y⁻¹ = z * y * y⁻¹ := by rw [hyz, mul_assoc]
                _ = z := by simp
            simpa [hconj] using hz
          · intro hz
            have hyz : (y * z * y⁻¹) * y = y * (y * z * y⁻¹) :=
              (Subgroup.le_centralizer_iff).1 hC0_le_centM0 hy (y * z * y⁻¹) hz
            have hz_eq : z = y * z * y⁻¹ := by
              simpa [mul_assoc] using congrArg (fun t => y⁻¹ * t) hyz
            rw [hz_eq]
            exact hz
        have hK_normal : K.Normal := by
          change (C0.subgroupOf (M0 ⊔ C0)).Normal
          exact
            (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := M0) (N := C0) hM0_le_normC0)
        let : K.Normal := hK_normal
        have hcardH :
            Nat.card H = Nat.card (H ⧸ K) * Nat.card K := by
          simpa [H, K] using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := K))
        have hcardK : Nat.card K = Nat.card C0 := by
          exact Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := C0) (K := H) le_sup_right).toEquiv
        have hD0_eq_subgroupOf : D0.subgroupOf M0 = C0.subgroupOf M0 := by
          ext y
          simp [D0, hD0_eq_inf, Subgroup.mem_subgroupOf]
        let e : M0 ⧸ D0.subgroupOf M0 ↪ H ⧸ K :=
          (Subgroup.quotientEquivOfEq hD0_eq_subgroupOf).toEmbedding.trans
            (Subgroup.quotientSubgroupOfEmbeddingOfLE (H := C0) (s := M0) (t := H) le_sup_left)
        have he_surj : Function.Surjective e := by
          intro q
          refine Quotient.inductionOn' q ?_
          intro h
          have hh_sup : h ∈ (M0.subgroupOf H) ⊔ K := by
            have hsup_top : (M0.subgroupOf H) ⊔ K = ⊤ := by
              change (M0.subgroupOf (M0 ⊔ C0)) ⊔ C0.subgroupOf (M0 ⊔ C0) = ⊤
              rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
              simp
            rw [hsup_top]
            simp
          rcases (Subgroup.mem_sup_of_normal_right (s := M0.subgroupOf H) (t := K) (x := h)).1
              hh_sup with
            ⟨m, hmM, c, hcK, hmc⟩
          have hmM0 : (m : G) ∈ M0 := by
            simpa [Subgroup.mem_subgroupOf] using hmM
          refine ⟨QuotientGroup.mk (⟨(m : G), hmM0⟩ : M0), ?_⟩
          change
            ((Subgroup.quotientSubgroupOfEmbeddingOfLE (H := C0) (s := M0) (t := H) le_sup_left)
              ((Subgroup.quotientEquivOfEq hD0_eq_subgroupOf)
                (QuotientGroup.mk (⟨(m : G), hmM0⟩ : M0))) = QuotientGroup.mk h)
          rw [Subgroup.quotientEquivOfEq_mk,
            Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk (H := C0) (h := le_sup_left)
            (g := (⟨(m : G), hmM0⟩ : M0))]
          apply Quotient.sound
          apply (QuotientGroup.leftRel_apply).mpr
          have hm_eq : (Subgroup.inclusion le_sup_left (⟨(m : G), hmM0⟩ : M0) : H) = m := by
            ext
            rfl
          rw [hm_eq, ← hmc]
          simpa [K, Subgroup.mem_subgroupOf]
        have hcardQ : Nat.card (H ⧸ K) = Nat.card (M0 ⧸ D0.subgroupOf M0) := by
          exact Nat.card_congr
            (Equiv.ofBijective e.toFun
              (show Function.Bijective e.toFun from ⟨e.injective, he_surj⟩)).symm
        calc
          Nat.card ↥(M0 ⊔ C0) = Nat.card (H ⧸ K) * Nat.card K := hcardH
          _ = Nat.card (M0 ⧸ D0.subgroupOf M0) * Nat.card C0 := by
            rw [hcardQ, hcardK]
      calc
        Nat.card A = Nat.card (A ⧸ C0.subgroupOf A) * Nat.card C0 := hcardA
        _ ≤ Nat.card (M0 ⧸ D0.subgroupOf M0) * Nat.card C0 := by
          exact Nat.mul_le_mul_right _ hquot_le
        _ = Nat.card ↥(M0 ⊔ C0) := hcardMC.symm
    exact hB_card_le_A.trans hA_card_le

theorem rzj_theorem_8_2_9
    (P B : Subgroup G)
    (hrepl :
      ∀ {A : Subgroup G},
        A ∈ thompsonAbelianSubgroups (G := G) P →
        ¬ B ≤ Subgroup.normalizer (A : Set G) →
        ∃ A' : Subgroup G,
          A' ∈ thompsonAbelianSubgroups (G := G) P ∧
          A ⊓ B < A' ⊓ B ∧
          A' ≤ Subgroup.normalizer (A : Set G)) :
    ∃ A : Subgroup G,
      A ∈ thompsonAbelianSubgroups (G := G) P ∧
      B ≤ Subgroup.normalizer (A : Set G) := by
  classical
  obtain ⟨A0, hA0⟩ := thompsonAbelianSubgroups_nonempty (G := G) P
  let S : Set (Subgroup G) := thompsonAbelianSubgroups (G := G) P
  have hS_nonempty : S.Nonempty := ⟨A0, hA0⟩
  have hS_finite : S.Finite := Set.toFinite S
  obtain ⟨A, hAmax⟩ :=
    hS_finite.exists_maximalFor (f := fun R : Subgroup G => Nat.card ↥(R ⊓ B)) S hS_nonempty
  have hA : A ∈ S := hAmax.prop
  by_cases hBA : B ≤ Subgroup.normalizer (A : Set G)
  · exact ⟨A, hA, hBA⟩
  · rcases hrepl hA hBA with ⟨A', hA', hlt, _⟩
    have hcard_le : Nat.card ↥(A ⊓ B) ≤ Nat.card ↥(A' ⊓ B) := Subgroup.card_le_of_le hlt.le
    have hcard_ne : Nat.card ↥(A ⊓ B) ≠ Nat.card ↥(A' ⊓ B) := by
      intro hEq
      apply hlt.ne
      exact Subgroup.eq_of_le_of_card_ge hlt.le (le_of_eq hEq.symm)
    have hcard_lt : Nat.card ↥(A ⊓ B) < Nat.card ↥(A' ⊓ B) := lt_of_le_of_ne hcard_le hcard_ne
    exact False.elim <| (not_lt_of_ge (hAmax.le hA')) hcard_lt

theorem rzj_thompsonCenter_le_of_mem {U A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) U) : thompsonCenter (G := G) U ≤ A := by
  have hAJ : A ≤ thompsonSubgroup (G := G) U := le_sSup hA
  have hZU : thompsonCenter (G := G) U ≤ U := rzj_thompsonCenter_le U
  have hcomm : IsMulCommutative (A ⊔ thompsonCenter (G := G) U : Subgroup G) := by
    rw [Subgroup.sup_eq_closure]
    let : IsMulCommutative A := hA.2.1
    let : IsMulCommutative (thompsonCenter (G := G) U) := rzj_thompsonCenter_isMulCommutative U
    exact Subgroup.isMulCommutative_closure
      (k := ((A : Set G) ∪ (thompsonCenter (G := G) U : Set G))) <| by
        intro y hy z hz _
        rcases hy with hyA | hyZ
        · rcases hz with hzA | hzZ
          · exact setLike_mul_comm (s := A) hyA hzA
          · exact Subgroup.mem_centralizer_iff.mp hzZ.2 y (hAJ hyA)
        · rcases hz with hzA | hzZ
          · exact (Subgroup.mem_centralizer_iff.mp hyZ.2 z (hAJ hzA)).symm
          · exact setLike_mul_comm (s := thompsonCenter (G := G) U) hyZ hzZ
  have hle : A ⊔ thompsonCenter (G := G) U ≤ U := sup_le hA.1 hZU
  have hcard := hA.2.2 _ hle hcomm
  have heq : A = A ⊔ thompsonCenter (G := G) U := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  intro z hz
  rw [heq]
  exact Subgroup.mem_sup_right hz

end ConstraintAndStability

end

end CFSG.ABGTheoremB.RelativeZJ
