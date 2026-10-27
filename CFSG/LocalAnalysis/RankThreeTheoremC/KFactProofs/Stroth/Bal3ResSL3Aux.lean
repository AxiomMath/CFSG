module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResPhiN
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Elem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open Subgroup

section Helpers

variable {X : Type*} [Group X] [Finite X]

theorem card_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {S H R : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S H) (hRH : R ≤ H) (hR : IsPGroup p R) :
    Nat.card R ≤ Nat.card S := by
  rw [hS.card_eq]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
  have hdvd : p ^ k ∣ Nat.card H := hk ▸ Subgroup.card_dvd_of_le hRH
  have hle : k ≤ (Nat.card H).factorization p :=
    ((Fact.out : p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hle

theorem three_le_pRank_of_le {K E : Subgroup X} (hEK : E ≤ K) (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hE' : IsElemAbelian 3 (E.subgroupOf K) := IsElemAbelian.comap hE K.subtype_injective
  have hc' : Nat.card (E.subgroupOf K) = 3 ^ 3 := by
    rw [← hc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE' hc'

end Helpers

section LemmaE

variable {G : Type*} [Group G] [Finite G]

theorem pow_three_eq_normMap {B : Subgroup G} (hBe : IsElemAbelian 3 B) {x b : G}
    (hx3 : x ^ 3 = 1) (hb : b ∈ B) (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) :
    (x * b) ^ 3 = normMap x b := by
  have hb1 : x * b * x⁻¹ ∈ B := hxB b hb
  have hb2 : x * (x * b * x⁻¹) * x⁻¹ ∈ B := hxB _ hb1
  have h1 : b * (x * b * x⁻¹) = (x * b * x⁻¹) * b := hBe.comm hb hb1
  have h2 : b * (x * (x * b * x⁻¹) * x⁻¹) = (x * (x * b * x⁻¹) * x⁻¹) * b := hBe.comm hb hb2
  have hxx : x⁻¹ * x⁻¹ = x := by
    have h3 : x * x * x = 1 := by
      rw [pow_succ, pow_succ, pow_one] at hx3
      exact hx3
    calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * (x * x * x) := by rw [h3, mul_one]
      _ = x := by group
  have key : (x * b) ^ 3 = (x * b * x⁻¹) * (x * (x * b * x⁻¹) * x⁻¹) * b := by
    calc (x * b) ^ 3 = x * b * x * b * x * b := by
          rw [pow_succ, pow_succ, pow_one]; simp only [mul_assoc]
      _ = x * b * x * b * (x⁻¹ * x⁻¹) * b := by rw [hxx]
      _ = _ := by group
  rw [key]
  unfold normMap
  generalize x * b * x⁻¹ = b₁ at h1 h2 ⊢
  generalize x * b₁ * x⁻¹ = b₂ at h2 ⊢
  calc b₁ * b₂ * b = b₁ * (b₂ * b) := mul_assoc _ _ _
    _ = b₁ * (b * b₂) := by rw [h2]
    _ = (b₁ * b) * b₂ := (mul_assoc _ _ _).symm
    _ = (b * b₁) * b₂ := by rw [h1]

theorem exists_pow_three_ne_one_grp {B T : Subgroup G} {z x : G}
    (hGc : Nat.card G = 81) (hBe : IsElemAbelian 3 B) (hBc : Nat.card B = 27)
    (hTn : T.Normal) (hTc : Nat.card T = 27) (hTB : Nat.card (T ⊓ B : Subgroup G) = 9)
    (hxT : x ∉ T) (hx3 : x ^ 3 = 1)
    (hzB : z ∈ B) (hzo : orderOf z = 3) (hzx : x * z = z * x)
    (hCB : ∀ b ∈ B, x * b = b * x → b ∈ zpowers z) :
    ∃ t ∈ T, t ^ 3 ≠ 1 ∧ t ^ 3 ∈ zpowers z := by
  classical
  by_contra hcon
  push Not at hcon
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (3 : ℕ).Prime := ⟨hp3⟩
  have hBind : B.index = 3 := by
    have h1 := Subgroup.card_mul_index B
    rw [hBc, hGc] at h1
    omega
  have hBn : B.Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hBind, hGc]
    norm_num
  have hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun b hb => hBn.conj_mem b hb x
  have hxnB : x ∉ B := by
    intro hxB'
    have hle : B ≤ zpowers z := fun b hb => hCB b hb (hBe.comm hxB' hb)
    have := Subgroup.card_le_of_le hle
    rw [hBc, Nat.card_zpowers, hzo] at this
    omega
  have hx1 : x ≠ 1 := fun h => hxnB (h ▸ B.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxx : x⁻¹ * x⁻¹ = x := by
    have h3 : x * x * x = 1 := by
      rw [pow_succ, pow_succ, pow_one] at hx3
      exact hx3
    calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * (x * x * x) := by rw [h3, mul_one]
      _ = x := by group
  obtain ⟨KN, hKNB, hKNc, hKN, hKNz⟩ :=
    exists_subgroup_ker_normMap hBe hBc hx3 hxB hzB hzo hzx hCB
  have hcube : ∀ b ∈ B, x * b ∈ T → (x * b) ^ 3 = 1 := by
    intro b hb hxb
    by_contra h1
    exact hcon _ hxb h1 (by rw [pow_three_eq_normMap hBe hx3 hb hxB]; exact hKNz b hb)
  obtain ⟨t₁, ht₁T, ht₁B⟩ : ∃ t₁ ∈ T, t₁ ∉ B := by
    by_contra h
    push Not at h
    have hle : T ≤ B := h
    have h2 : T ⊓ B = T := inf_eq_left.2 hle
    rw [h2, hTc] at hTB
    omega
  have hsup : B ⊔ zpowers x = ⊤ := by
    have hlt : 27 < Nat.card (B ⊔ zpowers x : Subgroup G) := by
      by_contra hle
      push Not at hle
      have heq : B ⊔ zpowers x = B :=
        (Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ zpowers x) (by rw [hBc]; exact hle)).symm
      exact hxnB (heq ▸ (le_sup_right : zpowers x ≤ B ⊔ zpowers x) (mem_zpowers x))
    have hd1 : Nat.card B ∣ Nat.card (B ⊔ zpowers x : Subgroup G) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card (B ⊔ zpowers x : Subgroup G) ∣ 81 := hGc ▸ Subgroup.card_subgroup_dvd_card _
    rw [hBc] at hd1
    obtain ⟨c, hc⟩ := hd1
    have hc3 : c ∣ 3 := by
      rw [hc] at hd2
      have : 27 * c ∣ 27 * 3 := by simpa using hd2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hcle : c ≤ 3 := Nat.le_of_dvd (by norm_num) hc3
    have hc1 : c ≠ 1 := by rintro rfl; omega
    have hc0 : c ≠ 0 := by rintro rfl; omega
    have hc2 : c ≠ 2 := by rintro rfl; omega
    have hc3' : c = 3 := by omega
    exact Subgroup.eq_top_of_card_eq _ (by rw [hc, hc3', hGc])
  obtain ⟨t₂, ht₂T, b₂, hb₂B, ht₂⟩ : ∃ t₂ ∈ T, ∃ b₂ ∈ B, t₂ = x * b₂ := by
    have ht₁sup : t₁ ∈ B ⊔ zpowers x := by rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨b, hb, k, hk, hbk⟩ := Subgroup.mem_sup_of_normal_left.1 ht₁sup
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hj : x ^ j = x ^ (j % 3) := by
      have := zpow_mod_orderOf x j
      rw [hxo] at this
      simpa using this.symm
    have hjr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rw [hj] at hbk
    rcases hjr with h0 | h1 | h2
    · rw [h0, zpow_zero, mul_one] at hbk
      exact absurd (hbk ▸ hb) ht₁B
    · rw [h1, zpow_one] at hbk
      refine ⟨t₁, ht₁T, x⁻¹ * b * x, ?_, ?_⟩
      · have := hBn.conj_mem b hb x⁻¹
        simpa using this
      · rw [← hbk]; group
    · rw [h2] at hbk
      refine ⟨t₁⁻¹, T.inv_mem ht₁T, b⁻¹, B.inv_mem hb, ?_⟩
      rw [← hbk]
      have e : (b * x ^ (2 : ℤ))⁻¹ = x⁻¹ * x⁻¹ * b⁻¹ := by group
      rw [e, hxx]
  have hb₂KN : b₂ ∈ KN := by
    rw [← hKN b₂ hb₂B, ← pow_three_eq_normMap hBe hx3 hb₂B hxB]
    exact hcube b₂ hb₂B (by rw [← ht₂]; exact ht₂T)
  have hTBle : T ⊓ B ≤ KN := by
    intro a ha
    have hab : b₂ * a ∈ B := B.mul_mem hb₂B ha.2
    have hTm : x * (b₂ * a) ∈ T := by
      have : t₂ * a ∈ T := T.mul_mem ht₂T ha.1
      rw [ht₂, mul_assoc] at this
      exact this
    have h1 : normMap x (b₂ * a) = 1 := by
      rw [← pow_three_eq_normMap hBe hx3 hab hxB]
      exact hcube _ hab hTm
    have h2 : b₂ * a ∈ KN := (hKN _ hab).1 h1
    have := KN.mul_mem (KN.inv_mem hb₂KN) h2
    simpa using this
  have hTBeq : T ⊓ B = KN :=
    Subgroup.eq_of_le_of_card_ge hTBle (by rw [hKNc, hTB])
  have hb₂T : b₂ ∈ T := by
    have : b₂ ∈ T ⊓ B := hTBeq ▸ hb₂KN
    exact this.1
  apply hxT
  have : t₂ * b₂⁻¹ ∈ T := T.mul_mem ht₂T (T.inv_mem hb₂T)
  rw [ht₂] at this
  simpa using this

end LemmaE

section Ambient

variable {X : Type*} [Group X] [Finite X]

theorem card_sup_mul_card_inf_of_commute' (L R : Subgroup X)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup X) * Nat.card (L ⊓ R : Subgroup X) = Nat.card L * Nat.card R := by
  let μ : L × R →* X := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : X) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup X) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : X), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : X)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

theorem mem_elem_of_pRank {P E : Subgroup X} {z : X} (hEP : E ≤ P) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hrk : CFSG.Open.pRank 3 P = 3) (hzP : z ∈ P)
    (hzo : orderOf z = 3) (hzc : ∀ y ∈ E, y * z = z * y) : z ∈ E := by
  by_contra hzE
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hzp : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
  have hZe : IsElemAbelian 3 (zpowers z) := CFSG.AGLEmbedding.isElemAbelian_zpowers hzp
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((show Commute a z from hzc a ha).zpow_right k).eq
  have hsup := IsElemAbelian.sup_of_commute hE hZe hcomm
  have hinf : E ⊓ zpowers z = ⊥ := by
    rw [inf_comm]
    exact zpowers_inf_eq_bot_of_notMem hp3 hzo hzE
  have hcard := card_sup_mul_card_inf_of_commute' E (zpowers z) hcomm
  rw [hinf, Subgroup.card_bot, hEc, Nat.card_zpowers, hzo] at hcard
  have hc4 : Nat.card (E ⊔ zpowers z : Subgroup X) = 3 ^ 4 := by
    norm_num at hcard ⊢
    omega
  have hle : E ⊔ zpowers z ≤ P := sup_le hEP (Subgroup.zpowers_le.2 hzP)
  have h4 : 4 ≤ CFSG.Open.pRank 3 P := CFSG.SectionRank.le_pRank hp3.one_lt hle hsup hc4
  omega

theorem nine_le_card_inf {P T B : Subgroup X} (hPc : Nat.card P = 81) (hTP : T ≤ P)
    (hBP : B ≤ P) (hTc : Nat.card T = 27) (hBc : Nat.card B = 27) :
    9 ≤ Nat.card (T ⊓ B : Subgroup X) := by
  have h1 := Subgroup.relIndex_mul_card T P
  rw [inf_eq_left.2 hTP, hTc, hPc] at h1
  have hr : T.relIndex P = 3 := by omega
  have h2 := Subgroup.relIndex_mul_card T B
  rw [hBc] at h2
  have hle : T.relIndex B ≤ T.relIndex P :=
    Subgroup.relIndex_le_of_le_right hBP (by rw [hr]; norm_num)
  by_contra hlt
  push Not at hlt
  have : T.relIndex B * Nat.card (T ⊓ B : Subgroup X) ≤ 3 * 8 :=
    Nat.mul_le_mul (hle.trans hr.le) (by omega)
  omega

theorem false_of_conj_plane {D B : Subgroup X} {g : X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 D (centralizer (D : Set X))) (hDc : Nat.card D = 9)
    (hBe : IsElemAbelian 3 B) (hBc : Nat.card B = 27) (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ B) :
    False := by
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  set S : Subgroup X := B.map (MulAut.conj g⁻¹).toMonoidHom with hSdef
  have hScard : Nat.card S = 27 := by
    rw [hSdef, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hBc]
  have hSp : IsPGroup 3 S := IsPGroup.of_card (n := 3) (by rw [hScard]; norm_num)
  have hSC : S ≤ centralizer (D : Set X) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have h1 : (MulAut.conj g⁻¹).toMonoidHom b = g⁻¹ * b * g := by simp [MulAut.conj_apply]
    rw [h1]
    have hcomm : b * (g * d * g⁻¹) = (g * d * g⁻¹) * b := hBe.comm hb (hgD d hd)
    calc d * (g⁻¹ * b * g) = g⁻¹ * ((g * d * g⁻¹) * b) * g := by group
      _ = g⁻¹ * (b * (g * d * g⁻¹)) * g := by rw [hcomm]
      _ = g⁻¹ * b * g * d := by group
  have := card_le_of_isSylowOf hS hSC hSp
  rw [hScard, hDc] at this
  omega

theorem exists_pow_three_ne_one {P B T : Subgroup X} {z x : X}
    (hPc : Nat.card P = 81) (hBP : B ≤ P) (hBe : IsElemAbelian 3 B) (hBc : Nat.card B = 27)
    (hTP : T ≤ P) (hTn : P ≤ normalizer (T : Set X)) (hTc : Nat.card T = 27)
    (hTB : Nat.card (T ⊓ B : Subgroup X) = 9)
    (hxP : x ∈ P) (hxT : x ∉ T) (hx3 : x ^ 3 = 1)
    (hzB : z ∈ B) (hzo : orderOf z = 3) (hzx : x * z = z * x)
    (hCB : ∀ b ∈ B, x * b = b * x → b ∈ zpowers z) :
    ∃ t ∈ T, t ^ 3 ≠ 1 ∧ t ^ 3 ∈ zpowers z := by
  have hzP : z ∈ P := hBP hzB
  have hTn' : (T.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTP).2 hTn
  have hBc' : Nat.card (B.subgroupOf P) = 27 := by
    rw [← hBc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  have hTc' : Nat.card (T.subgroupOf P) = 27 := by
    rw [← hTc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv
  have hTB' : Nat.card (T.subgroupOf P ⊓ B.subgroupOf P : Subgroup P) = 9 := by
    rw [← hTB]
    have : T.subgroupOf P ⊓ B.subgroupOf P = (T ⊓ B).subgroupOf P := by
      ext y; simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hTP)).toEquiv
  have hzo' : orderOf (⟨z, hzP⟩ : P) = 3 := by rw [Subgroup.orderOf_mk]; exact hzo
  obtain ⟨t', ht'T, ht', ht'z⟩ := exists_pow_three_ne_one_grp (G := P) (B := B.subgroupOf P)
    (T := T.subgroupOf P) (z := ⟨z, hzP⟩) (x := ⟨x, hxP⟩) hPc
    (IsElemAbelian.comap hBe P.subtype_injective) hBc' hTn' hTc' hTB'
    (fun h => hxT h) (Subtype.ext (by simpa using hx3)) hzB hzo'
    (Subtype.ext (by simpa using hzx))
    (by
      intro b hb hxb
      have hb' : (b : X) ∈ B := hb
      have h1 : x * (b : X) = (b : X) * x := congrArg Subtype.val hxb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hCB _ hb' h1)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩)
  refine ⟨(t' : X), ht'T, fun h => ht' (Subtype.ext (by simpa using h)), ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ht'z
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

end Ambient


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
