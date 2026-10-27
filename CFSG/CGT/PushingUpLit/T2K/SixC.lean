module

public import CFSG.CGT.PushingUpLit.T2K.SixB
public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 normal_of_goldschmidt_of_no_layer)

theorem isCharacteristicP_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) {p : ℕ}
    (h : IsCharacteristicP p A) : IsCharacteristicP p B := by
  unfold IsCharacteristicP at h ⊢
  intro b hb
  rw [← pCore_map_iso p e] at hb ⊢
  refine ⟨e.symm b, h ?_, by simp⟩
  rw [Subgroup.mem_centralizer_iff] at hb ⊢
  intro a ha
  have h1 := hb (e a) ⟨a, ha, rfl⟩
  apply e.injective
  simpa using h1

theorem isCharacteristicP_of_normal' {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (N : Subgroup K) [N.Normal] (hK : IsCharacteristicP p K) : IsCharacteristicP p ↥N := by
  have hKF := (isCharacteristicP_iff_generalizedFitting_eq_pCore K p).mp hK
  have hmono := CFSG.ComponentClassification.GeneralizedFitting.normal_monotone N
  rw [← generalizedFitting_eq_componentClassification,
    ← generalizedFitting_eq_componentClassification, hKF] at hmono
  have hFp : IsPGroup p ↥(generalizedFitting ↥N) := by
    have h := (CFSG.pCore_isPGroup (p := p) (G := K)).to_le hmono
    exact h.of_injective ((generalizedFitting ↥N).equivMapOfInjective N.subtype
      N.subtype_injective).toMonoidHom (MulEquiv.injective _)
  have hFn : (generalizedFitting ↥N).Normal := by
    rw [generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal _
  have hFO : generalizedFitting ↥N ≤ CFSG.pCore p ↥N := le_sSup ⟨hFn, hFp⟩
  change Subgroup.centralizer (CFSG.pCore p ↥N : Set ↥N) ≤ CFSG.pCore p ↥N
  exact (Subgroup.centralizer_le hFO).trans
    ((centralizer_generalizedFitting_le ↥N).trans hFO)

variable {G : Type} [Group G] [Finite G]

theorem isCharacteristicP_centralizer (hchar : CFSG.Assembly.IsCharTwoType G) {D : Subgroup G}
    (hD : IsPGroup 2 ↥D) (hD1 : D ≠ ⊥) :
    IsCharacteristicP 2 ↥(Subgroup.centralizer (D : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : IsPLocal 2 (Subgroup.normalizer (D : Set G)) := ⟨D, hD1, hD, rfl⟩
  have hNc : IsCharacteristicP 2 ↥(Subgroup.normalizer (D : Set G)) :=
    CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar hN
  have hle : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.centralizer_le_normalizer (D : Set G)
  have hnorm : ((Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 fun n hn => mem_normalizer_centralizer hn
  have := hnorm
  have h1 := isCharacteristicP_of_normal'
    ((Subgroup.centralizer (D : Set G)).subgroupOf (Subgroup.normalizer (D : Set G))) hNc
  exact isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hle) h1

namespace T2Hyp

variable {L M T D : Subgroup G} {n : ℕ}

theorem mem_of_map_conj_le_M (hs : Sec6 G L M T n) {g : G}
    (hg : (QOf L M).map (MulAut.conj g).toMonoidHom ≤ M) : g ∈ M := by
  have hQp : IsPGroup 2 ↥(QOf L M) :=
    fun x => ⟨1, Subtype.ext (by simpa using hs.Q_abelian.2 x x.2)⟩
  have hQgp : IsPGroup 2 ↥((QOf L M).map (MulAut.conj g).toMonoidHom) :=
    hQp.map (MulAut.conj g).toMonoidHom
  obtain ⟨k, hk, hkT⟩ := exists_conj_le_of_isPGroup hs.sec4.sylow hQgp hg
  have hmap : (QOf L M).map (MulAut.conj (k * g)).toMonoidHom ≤ T := by
    have e : ((QOf L M).map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom =
        (QOf L M).map (MulAut.conj (k * g)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [← e]
    exact hkT
  have hkg : k * g ∈ M := by
    rw [← hs.N_Q]
    exact mem_normalizer_of_map_conj_eq (hs.Q_wc (k * g) hmap)
  have := M.mul_mem (M.inv_mem hk) hkg
  simpa using this

theorem exists_g_of_ne_bot (hGold : Goldschmidt1974) (hs : Sec6 G L M T n) (hD : IsD L M D)
    (hD1 : D ≠ ⊥) :
    ∃ g : G, g ∈ Subgroup.centralizer (D : Set G) ∧ g ∉ M ∧
      D < (QOf L M).map (MulAut.conj g).toMonoidHom ⊓ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hcon' : ∀ g : G, g ∈ Subgroup.centralizer (D : Set G) → g ∉ M →
      ¬ D < (QOf L M).map (MulAut.conj g).toMonoidHom ⊓ M :=
    fun g hg hgM hlt => hcon ⟨g, hg, hgM, hlt⟩
  have hQ : IsElemAbelian 2 (QOf L M) := hs.Q_abelian
  have hQp : IsPGroup 2 ↥(QOf L M) := fun x => ⟨1, Subtype.ext (by simpa using hQ.2 x x.2)⟩
  have hDQ : D ≤ QOf L M := hD.le_Q
  have hQM : QOf L M ≤ M := inf_le_left
  have hDp : IsPGroup 2 ↥D := hQp.to_le hDQ
  have hQH : QOf L M ≤ Subgroup.centralizer (D : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_comm' hQ (hDQ hd) hq
  have hchK := isCharacteristicP_centralizer hs.sec4.hyp.charTwo hDp hD1
  set H : Subgroup G := Subgroup.centralizer (D : Set G) with hH
  set A : Subgroup ↥H := (QOf L M).subgroupOf H with hAdef
  have hAp : IsPGroup 2 ↥A := hQp.comap_subtype
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  have hAab : IsMulCommutative ↥A :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (isElemAbelian_comm' hQ
      (show ((a : ↥H) : G) ∈ QOf L M from a.2) (show ((b : ↥H) : G) ∈ QOf L M from b.2)))⟩⟩
  have hS' : IsPGroup 2 ↥((S : Subgroup ↥H).map H.subtype) := S.isPGroup'.map H.subtype
  have hQS' : QOf L M ≤ (S : Subgroup ↥H).map H.subtype := fun q hq =>
    ⟨⟨q, hQH hq⟩, hAS (show (⟨q, hQH hq⟩ : ↥H) ∈ A from hq), rfl⟩
  have hSM : (S : Subgroup ↥H).map H.subtype ≤ M := two_le_M hs hS' hQS'
  have hcl : ∀ a ∈ A, ∀ k : ↥H, k⁻¹ * a * k ∈ (S : Subgroup ↥H) → k⁻¹ * a * k ∈ A := by
    intro a ha k hk
    have haQ : ((a : ↥H) : G) ∈ QOf L M := ha
    have hyM : (k : G)⁻¹ * ((a : ↥H) : G) * (k : G) ∈ M :=
      hSM ⟨k⁻¹ * a * k, hk, by simp⟩
    show (k : G)⁻¹ * ((a : ↥H) : G) * (k : G) ∈ QOf L M
    by_cases hkM : (k : G) ∈ M
    · have hkn : (k : G)⁻¹ ∈ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
        rw [hs.N_Q]
        exact M.inv_mem hkM
      have := (Subgroup.mem_normalizer_iff.1 hkn ((a : ↥H) : G)).1 haQ
      simpa [mul_assoc] using this
    · have hg'H : (k : G)⁻¹ ∈ H := H.inv_mem k.2
      have hg'M : (k : G)⁻¹ ∉ M := fun hmem => hkM (by simpa using M.inv_mem hmem)
      have hnlt := hcon' _ hg'H hg'M
      have hDle : D ≤ (QOf L M).map (MulAut.conj ((k : G)⁻¹)).toMonoidHom ⊓ M := by
        intro d hd
        refine ⟨(mem_map_conj_iff _ _ _).2 ?_, hQM (hDQ hd)⟩
        have hc : d * (k : G) = (k : G) * d := Subgroup.mem_centralizer_iff.1 k.2 d hd
        have e : ((k : G)⁻¹)⁻¹ * d * (k : G)⁻¹ = d := by
          calc ((k : G)⁻¹)⁻¹ * d * (k : G)⁻¹ = (k : G) * d * (k : G)⁻¹ := by rw [inv_inv]
            _ = d := by rw [← hc]; group
        rw [e]
        exact hDQ hd
      have heq := (eq_of_le_of_not_lt hDle hnlt).symm
      have hyD : (k : G)⁻¹ * ((a : ↥H) : G) * (k : G) ∈ D := by
        rw [← heq]
        refine ⟨(mem_map_conj_iff _ _ _).2 ?_, hyM⟩
        have e : ((k : G)⁻¹)⁻¹ * ((k : G)⁻¹ * ((a : ↥H) : G) * (k : G)) * (k : G)⁻¹ =
            ((a : ↥H) : G) := by group
        rw [e]
        exact haQ
      exact hDQ hyD
  set M₀ : Subgroup ↥H := Subgroup.normalClosure (A : Set ↥H) with hM₀
  have hM₀n : M₀.Normal := Subgroup.normalClosure_normal
  have hchM₀ : IsCharacteristicP 2 ↥M₀ := isCharacteristicP_of_normal' M₀ hchK
  have hodd : CFSG.Open.goldschmidtOddCore ↥M₀ = ⊥ := by
    rw [CFSG.Goldschmidt.goldschmidtOddCore_eq_pPrimeCore]
    exact pPrimeCore_eq_bot_of_isCharacteristicP ↥M₀ 2 hchM₀
  have hlayer : goldschmidtLayer (↥M₀ ⧸ goldschmidtOddCore ↥M₀) = ⊥ := by
    have e : (↥M₀ ⧸ goldschmidtOddCore ↥M₀) ≃* ↥M₀ :=
      (QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot
    have hX : IsCharacteristicP 2 (↥M₀ ⧸ goldschmidtOddCore ↥M₀) :=
      isCharacteristicP_of_mulEquiv' e.symm hchM₀
    have h1 := layer_eq_bot_of_isCharacteristicP (↥M₀ ⧸ goldschmidtOddCore ↥M₀) 2 hX
    exact (layer_eq_componentClassification _).symm.trans h1
  have hcent : ∀ x ∈ CFSG.Goldschmidt.oddCoreOf M₀, ∀ m ∈ M₀, m * x = x * m := by
    intro x hx m hm
    unfold CFSG.Goldschmidt.oddCoreOf at hx
    rw [hodd, Subgroup.map_bot, Subgroup.mem_bot] at hx
    rw [hx]
    simp
  have hnormal : A.Normal := normal_of_goldschmidt_of_no_layer hGold S A hAS hAab hcl hlayer hcent
  have key : ∀ (h : G), h ∈ H → ∀ x : G, x ∈ QOf L M → h * x * h⁻¹ ∈ QOf L M := by
    intro h hh x hx
    have hx' : (⟨x, hQH hx⟩ : ↥H) ∈ A := hx
    exact hnormal.conj_mem _ hx' ⟨h, hh⟩
  have hHn : H ≤ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key h hh x, fun hx => ?_⟩
    have := key h⁻¹ (H.inv_mem hh) _ hx
    simpa [mul_assoc] using this
  have hHM : H ≤ M := by
    rw [← hs.N_Q]
    exact hHn
  obtain ⟨g₀, hg₀M, hDg₀⟩ := hD.exists_g
  have hQg₀ : IsElemAbelian 2 ((QOf L M).map (MulAut.conj g₀).toMonoidHom) :=
    isElemAbelian_map_conj hQ g₀
  have hQg₀H : (QOf L M).map (MulAut.conj g₀).toMonoidHom ≤ H := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_comm' hQg₀ (hDg₀ hd) hy
  exact hg₀M (mem_of_map_conj_le_M hs (hQg₀H.trans hHM))

end T2Hyp

@[expose] def Print64D1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G),
    Sec6 G L M T n → IsD L M D → D = ⊥ →
    ∃ g : G, g ∈ Subgroup.centralizer (D : Set G) ∧ g ∉ M ∧
      D < (QOf L M).map (MulAut.conj g).toMonoidHom ⊓ M

theorem print64_of (hGold : Goldschmidt1974) (h1 : Print64D1) : Print64 := by
  intro G _ _ L M T n D hs hD
  by_cases hD1 : D = ⊥
  · exact h1 G L M T n D hs hD hD1
  · exact T2Hyp.exists_g_of_ne_bot hGold hs hD hD1

end CFSG.CGT.PushingUpLit.T2K
