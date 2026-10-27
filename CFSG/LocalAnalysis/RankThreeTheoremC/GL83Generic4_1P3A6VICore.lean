module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec11.Wreath
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VILines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VIOrder3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VITools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VIWreath
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartTwo.Sec11 (W33)
open CFSG.RankThree.PartTwo.KFacts (WreathData eConj eBase eConj_zero eConj_mem_eBase)

variable {G : Type} [Group G] [Finite G]

theorem a6vi_core {P : Sylow 3 G} {x : G} {T : Subgroup G} {n n' : G}
    (hxP : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hQsyl : IsSylowOf 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)))
    (hQab : IsMulCommutative ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G))
    (hTel : IsElemAbelian 3 T) (hTc : Nat.card T = 3 ^ 2)
    (hTQ : T ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G)) (hxT : x ∉ T)
    (hQeq : (P : Subgroup G) ⊓ centralizer ({x} : Set G) = T ⊔ zpowers x)
    (hconjT : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤
        (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom ≤ T)
    (hL33 : ∀ g₁ g₂ g₃ : G, g₁ * x * g₁⁻¹ ∈ T → g₂ * x * g₂⁻¹ ∈ T → g₃ * x * g₃⁻¹ ∈ T →
      zpowers (g₁ * x * g₁⁻¹) ≠ zpowers (g₂ * x * g₂⁻¹) →
      zpowers (g₁ * x * g₁⁻¹) ≠ zpowers (g₃ * x * g₃⁻¹) →
      zpowers (g₂ * x * g₂⁻¹) ≠ zpowers (g₃ * x * g₃⁻¹) → False)
    (hn : n ∈ normalizer (((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G))
    (hnT : n * x * n⁻¹ ∈ T) (hn'x : n' ∈ centralizer ({x} : Set G))
    (hn'T : n' ∈ normalizer (T : Set G))
    (hn'y : n' * (n * x * n⁻¹) * n'⁻¹ ∉ zpowers (n * x * n⁻¹)) :
    Nonempty ((P : Subgroup G) ≃* W33) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hQ
  have hxQ : x ∈ Q := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcx : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  have hTx : ∀ t ∈ T, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc =>
    hQcomm t (hTQ ht) c (zpowers_le.mpr hxQ hc)
  have hQ3 : ∀ q ∈ Q, q ^ 3 = 1 := by
    intro q hq
    rw [hQeq] at hq
    obtain ⟨t₀, ht₀, c₀, hc₀, rfl⟩ := u3l42_decomp hTx hq
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc₀
    rw [(Commute.mul_pow (hTx t₀ ht₀ _ hc₀) 3), hTel.2 t₀ ht₀, one_mul, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hQ27 : Nat.card Q = 27 := by
    rw [hQeq, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three T hx3 hxT
      (fun a ha => hTx a ha x (mem_zpowers x)), hTc]
    norm_num
  set y := n * x * n⁻¹ with hy
  set y₂ := n' * y * n'⁻¹ with hy₂
  have hy₂T : y₂ ∈ T := (mem_normalizer_iff.mp hn'T y).mp hnT
  have hL01 : zpowers x ≠ zpowers y := fun h => hxT (zpowers_le.mpr hnT (h ▸ mem_zpowers x))
  have hL02 : zpowers x ≠ zpowers y₂ := fun h => hxT (zpowers_le.mpr hy₂T (h ▸ mem_zpowers x))
  have hL12 : zpowers y ≠ zpowers y₂ := fun h => hn'y (h ▸ mem_zpowers y₂)
  have hn'xx : n' * x * n'⁻¹ = x := by
    rw [mem_centralizer_singleton_iff.mp hn'x]; group
  have hy₂' : (n' * n) * x * (n' * n)⁻¹ = y₂ := by rw [hy₂, hy]; group
  have hn'Q : n' ∈ normalizer (Q : Set G) := by
    rw [hQeq]
    exact a6vi_mem_normalizer_sup hn'T (sr628_centralizer_le_normalizer_zpowers x hn'x)
  have hD : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q →
      zpowers (g * x * g⁻¹) = zpowers x ∨ zpowers (g * x * g⁻¹) = zpowers y ∨
        zpowers (g * x * g⁻¹) = zpowers y₂ := by
    intro g hg
    rcases hconjT g hg with h0 | hT'
    · exact Or.inl (by rw [← a6vi_map_conj_zpowers]; exact h0)
    · have hwT : g * x * g⁻¹ ∈ T := hT' (by rw [a6vi_map_conj_zpowers]; exact mem_zpowers _)
      by_contra hne
      push Not at hne
      obtain ⟨-, hne1, hne2⟩ := hne
      exact hL33 n (n' * n) g hnT (by rw [hy₂']; exact hy₂T) hwT (by rw [hy₂']; exact hL12)
        (fun h => hne1 h.symm) (by rw [hy₂']; exact fun h => hne2 h.symm)
  have hmapQ : ∀ g : G, g * x * g⁻¹ ∈ Q → (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q :=
    fun g hg => by rw [a6vi_map_conj_zpowers]; exact zpowers_le.mpr hg
  have hlineQ : ∀ w : G, (w = x ∨ w = y ∨ w = y₂) →
      ∃ g : G, w = g * x * g⁻¹ ∧ (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q := by
    intro w hw
    rcases hw with h | h | h
    · exact ⟨1, by rw [h]; group, hmapQ 1 (by simpa using hxQ)⟩
    · exact ⟨n, h, hmapQ n (hTQ hnT)⟩
    · exact ⟨n' * n, by rw [h, hy₂'], hmapQ _ (by rw [hy₂']; exact hTQ hy₂T)⟩
  have hperm : ∀ h ∈ normalizer (Q : Set G), ∀ w : G, (w = x ∨ w = y ∨ w = y₂) →
      (zpowers (h * w * h⁻¹) = zpowers x ∨ zpowers (h * w * h⁻¹) = zpowers y ∨
        zpowers (h * w * h⁻¹) = zpowers y₂) := by
    intro h hh w hw
    obtain ⟨g, rfl, hg⟩ := hlineQ w hw
    have e : h * (g * x * g⁻¹) * h⁻¹ = (h * g) * x * (h * g)⁻¹ := by group
    rw [e]
    refine hD (h * g) ?_
    rw [← a6vi_map_conj_mul]
    exact a6vi_map_conj_le hh hg
  obtain ⟨r, hrN, -, hr3Q, hrx, hry, hry₂⟩ :=
    a6vi_exists_three_cycle hQsyl hx1 hx3 hL01 hL02 hL12 hperm hn rfl hn'Q hn'xx rfl
  have hr3C : r ^ 3 ∈ centralizer ({x} : Set G) := hQsyl.le hr3Q
  have hre₂ : r * (r * (r * x * r⁻¹) * r⁻¹) * r⁻¹ = x := by
    have e3 : r * (r * (r * x * r⁻¹) * r⁻¹) * r⁻¹ = r ^ 3 * x * (r ^ 3)⁻¹ := by
      rw [pow_three]; group
    rw [e3, mem_centralizer_singleton_iff.mp hr3C]; group
  have hconjQ : ∀ w ∈ Q, r * w * r⁻¹ ∈ Q := fun w hw => (mem_normalizer_iff.mp hrN w).mp hw
  have he₁Q : r * x * r⁻¹ ∈ Q := hconjQ x hxQ
  have he₂Q : r * (r * x * r⁻¹) * r⁻¹ ∈ Q := hconjQ _ he₁Q
  have hry' : zpowers (r * (r * x * r⁻¹) * r⁻¹) = zpowers y₂ := by
    rw [a6vi_zpowers_conj_congr hrx r]; exact hry
  set e₁ := r * x * r⁻¹ with he₁
  set e₂ := r * e₁ * r⁻¹ with he₂
  have hne1 : ∀ g : G, g * x * g⁻¹ ≠ 1 := fun g h => hx1 (by
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, h]; group)
  have hc3 : ∀ g : G, Nat.card (zpowers (g * x * g⁻¹)) = 3 := fun g => by
    rw [Nat.card_zpowers,
      orderOf_eq_prime (by rw [conj_pow, hx3, mul_one, mul_inv_cancel]) (hne1 g)]
  have hcy : Nat.card (zpowers y) = 3 := hc3 n
  have hcy₂ : Nat.card (zpowers y₂) = 3 := by rw [← hy₂']; exact hc3 _
  have hc₁ : Nat.card (zpowers e₁) = 3 := by rw [hrx]; exact hcy
  have hc₂ : Nat.card (zpowers e₂) = 3 := by rw [hry']; exact hcy₂
  have hTx0 : T ⊓ zpowers x = ⊥ := by
    have hdvd : Nat.card (T ⊓ zpowers x : Subgroup G) ∣ 3 := by
      rw [← hcx]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have h := Subgroup.eq_of_le_of_card_ge (inf_le_right : T ⊓ zpowers x ≤ zpowers x)
        (by rw [hcx, h3])
      exact hxT ((h.symm.le.trans inf_le_left) (mem_zpowers x))
  have hT12le : zpowers e₂ ⊔ zpowers e₁ ≤ T :=
    sup_le (by rw [hry']; exact zpowers_le.mpr hy₂T) (by rw [hrx]; exact zpowers_le.mpr hnT)
  have hT : (zpowers e₂ ⊔ zpowers e₁) ⊓ zpowers x = ⊥ :=
    eq_bot_iff.mpr (le_trans (inf_le_inf_right _ hT12le) hTx0.le)
  have h12 : zpowers e₂ ⊓ zpowers e₁ = ⊥ :=
    a6vi_inf_eq_bot_of_ne hc₂ hc₁ (by rw [hry', hrx]; exact fun h => hL12 h.symm)
  have he₁3 : e₁ ^ 3 = 1 := hQ3 _ he₁Q
  have he₁n : e₁ ∉ zpowers e₂ := by
    intro h
    apply hL12
    have hle : zpowers e₁ ≤ zpowers e₂ := zpowers_le.mpr h
    have := Subgroup.eq_of_le_of_card_ge hle (by rw [hc₁, hc₂])
    rw [← hrx, ← hry', this]
  have hTeq : zpowers e₂ ⊔ zpowers e₁ = T := by
    refine Subgroup.eq_of_le_of_card_ge hT12le ?_
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three _ he₁3 he₁n
      (fun a ha => hQcomm a (zpowers_le.mpr he₂Q ha) e₁ he₁Q), hc₂, hTc]
    norm_num
  have hQeq' : Q = zpowers x ⊔ (zpowers e₂ ⊔ zpowers e₁) := by
    rw [hTeq]; exact hQeq.trans (sup_comm _ _)
  have hr3 : r ^ 3 ∈ zpowers x ⊔ (zpowers e₂ ⊔ zpowers e₁) := by rw [← hQeq']; exact hr3Q
  have hxe₁ : Commute x e₁ := hQcomm x hxQ e₁ he₁Q
  have hxe₂ : Commute x e₂ := hQcomm x hxQ e₂ he₂Q
  have he₁₂ : Commute e₁ e₂ := hQcomm e₁ he₁Q e₂ he₂Q
  obtain ⟨k, hk⟩ := a6vi_exists_order_three hx3 hx1 hxe₁ hxe₂ he₁₂ hT h12 hre₂ hr3
  set t := r * x ^ (-k) with ht
  have hxk : ∀ w : G, Commute x w → x ^ (-k) * w * x ^ k = w := fun w hw => by
    rw [(hw.zpow_left (-k)).eq, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hC1' : t * x * t⁻¹ = e₁ := by rw [ht, he₁]; group
  have hC2' : t ^ 2 * x * (t ^ 2)⁻¹ = e₂ := by
    have h1 : t ^ 2 * x * (t ^ 2)⁻¹ = r * (x ^ (-k) * e₁ * x ^ k) * r⁻¹ := by
      rw [ht, he₁, pow_two]; group
    rw [h1, hxk e₁ hxe₁, he₂]
  have hC1 : eConj x t 1 = e₁ := by
    show t ^ 1 * x * (t ^ 1)⁻¹ = e₁
    rw [pow_one]; exact hC1'
  have hC2 : eConj x t 2 = e₂ := hC2'
  have hBase : eBase x t = Q := by
    apply le_antisymm
    · rw [eBase, closure_le]
      rintro _ (rfl | rfl | rfl)
      · rw [eConj_zero]; exact hxQ
      · rw [hC1]; exact he₁Q
      · rw [hC2]; exact he₂Q
    · rw [hQeq']
      refine sup_le ?_ (sup_le ?_ ?_)
      · have h0 := eConj_mem_eBase (e := x) (t := t) (i := 0) (Or.inl rfl)
        rw [eConj_zero] at h0
        exact zpowers_le.mpr h0
      · rw [zpowers_le, ← hC2]; exact eConj_mem_eBase (Or.inr (Or.inr rfl))
      · rw [zpowers_le, ← hC1]; exact eConj_mem_eBase (Or.inr (Or.inl rfl))
  have hW : WreathData x t :=
    { pow_e := hx3
      pow_t := hk
      comm := by rw [hC1]; exact hxe₁
      card_eBase := by rw [hBase]; exact hQ27
      not_mem := by
        rw [hBase]
        intro htQ
        apply hL01
        have hrQ : r ∈ Q := by
          have e : r = t * x ^ k := by rw [ht]; group
          rw [e]; exact Q.mul_mem htQ (Q.zpow_mem hxQ k)
        have he : e₁ = x := by rw [he₁, hQcomm r hrQ x hxQ]; group
        rw [← hrx, he] }
  set R : Subgroup G := closure ({x, t} : Set G) with hR
  have hQR : Q ≤ R := by rw [← hBase]; exact hW.eBase_le
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 4) (by rw [hW.card_closure]; norm_num)
  have hzQ : eConj x t 0 * eConj x t 1 * eConj x t 2 ∈ Q := by
    rw [← hBase]
    exact mul_mem (mul_mem (eConj_mem_eBase (Or.inl rfl)) (eConj_mem_eBase (Or.inr (Or.inl rfl))))
      (eConj_mem_eBase (Or.inr (Or.inr rfl)))
  have hU : ∀ A : Subgroup G, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A = 27 →
      A = Q := fun A hAR hAc hA =>
    (a6vi_eq_eBase_of_abelian hW (hQ3 _ hzQ) hAR hAc hA).trans hBase
  have hxN : ∀ j : ℤ, x ^ j ∈ normalizer (Q : Set G) := fun j =>
    Subgroup.le_normalizer (Q.zpow_mem hxQ j)
  have htN : t ∈ normalizer (Q : Set G) := by rw [ht]; exact mul_mem hrN (hxN (-k))
  have htR : t ∈ R := subset_closure (by simp)
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  have hSR : (S : Subgroup G) = R := by
    by_contra hne
    have hlt : R < S := lt_of_le_of_ne hRS (Ne.symm hne)
    obtain ⟨s, hsS, hsN, hsR⟩ := sr628_exists_mem_normalizer_not_mem S.isPGroup' hlt
    have hsQ : s ∈ normalizer (Q : Set G) := by
      apply a6vi_mem_normalizer_of_map_eq
      refine hU _ (a6vi_map_conj_le hsN hQR) ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc s * a * s⁻¹ * (s * b * s⁻¹) = s * (a * b) * s⁻¹ := by group
          _ = s * (b * a) * s⁻¹ := by rw [hQcomm a ha b hb]
          _ = s * b * s⁻¹ * (s * a * s⁻¹) := by group
      · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]; exact hQ27
    obtain ⟨v, hvR, hvN, hv⟩ : ∃ v ∈ R, v ∈ normalizer (Q : Set G) ∧
        zpowers (s * x * s⁻¹) = zpowers (v * x * v⁻¹) := by
      rcases hperm s hsQ x (Or.inl rfl) with h | h | h
      · exact ⟨1, one_mem _, one_mem _, by rw [h, one_mul, inv_one, mul_one]⟩
      · exact ⟨t, htR, htN, by rw [h, ← hrx, hC1']⟩
      · exact ⟨t ^ 2, pow_mem htR 2, pow_mem htN 2, by rw [h, ← hry', hC2']⟩
    set u := v⁻¹ * s with hu
    have huS : u ∈ (S : Subgroup G) := mul_mem (inv_mem (hRS hvR)) hsS
    obtain ⟨e, he⟩ := S.isPGroup' ⟨u, huS⟩
    have hue : u ^ (3 ^ e) = 1 := by
      have := congrArg Subtype.val he
      simpa using this
    have hux : u * x * u⁻¹ ∈ zpowers x := by
      have h1 := a6vi_zpowers_conj_congr hv v⁻¹
      have e1 : v⁻¹ * (s * x * s⁻¹) * v⁻¹⁻¹ = u * x * u⁻¹ := by rw [hu]; group
      have e2 : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
      rw [e1, e2] at h1
      rw [← h1]; exact mem_zpowers _
    have huC : u ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h := p34_conj_eq_of_pow hx1 hx3 hue hux
      calc u * x = u * x * u⁻¹ * u := by group
        _ = x * u := by rw [h]
    have huQ : u ∈ Q := a6vi_mem_of_mem_normalizer hQsyl hue (mul_mem (inv_mem hvN) hsQ) huC
    apply hsR
    have e : s = v * u := by rw [hu]; group
    rw [e]
    exact mul_mem hvR (hQR huQ)
  exact ⟨(Sylow.equiv P S).trans ((MulEquiv.subgroupCongr hSR).trans hW.mulEquiv.symm)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
