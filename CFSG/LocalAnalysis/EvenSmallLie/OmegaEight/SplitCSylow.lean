module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCDefs
public import CFSG.Monster.B.Recog.GenericTransferExtremal
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Setup

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem mem_of_index_eq_two_of_simple [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (x : G) :
    ∀ K : Subgroup G, K.index = 2 → x ∈ K := by
  intro K hK
  have hN := Subgroup.normal_of_index_eq_two hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exfalso
    rw [h, Subgroup.index_bot] at hK
    obtain ⟨b, c, hbc⟩ := hnab
    have hcyc : IsCyclic G := isCyclic_of_prime_card (p := 2) hK
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg c)
    exact hbc ((Commute.refl g).zpow_zpow i j).eq
  · rw [h]; exact mem_top x

namespace Setting

variable {ε : Eps} {t : G} {L H₀ U Q P S₀ : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setting ε t L H₀ U Q P S₀ a ψ p)
include hS

theorem Q_le_H₀ : Q ≤ H₀ := hS.rad.Q_le_L.trans hS.shape.L_le

theorem Q_le_S₀ : Q ≤ S₀ := hS.rad.Q_le_U.trans hS.data.U_le

theorem a_mem_H₀ : a ∈ H₀ := hS.Q_le_H₀ hS.rad.a_mem_Q

theorem TH_le_centralizer : S₀ ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
  sup_le (hS.data.S₀_le.trans hS.shape.le_centralizer)
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))

theorem isPGroup_TH : IsPGroup 2 (S₀ ⊔ zpowers t : Subgroup G) :=
  hS.shape.isPGroup_sup hS.data.S₀_le hS.data.pgroup

theorem commute_ψ (v : V6) : ψ v * t = t * ψ v :=
  hS.shape.commute_of_mem (hS.Q_le_H₀ (hS.rad.ψ_mem v))

theorem mem_E_iff {x : G} : x ∈ Q ⊔ zpowers t ↔ ∃ v, x = ψ v ∨ x = t * ψ v := by
  rw [hS.shape.mem_sup_iff hS.Q_le_H₀]
  constructor
  · rintro ⟨q, hq, h | h⟩ <;> obtain ⟨v, rfl⟩ := hS.rad.mem_ψ q hq
    · exact ⟨v, Or.inl h⟩
    · exact ⟨v, Or.inr (h.trans (hS.commute_ψ v))⟩
  · rintro ⟨v, h | h⟩
    · exact ⟨ψ v, hS.rad.ψ_mem v, Or.inl h⟩
    · exact ⟨ψ v, hS.rad.ψ_mem v, Or.inr (h.trans (hS.commute_ψ v).symm)⟩

theorem E_comm {x y : G} (hx : x ∈ Q ⊔ zpowers t) (hy : y ∈ Q ⊔ zpowers t) : x * y = y * x :=
  sup_comm_of (fun x hx y hy => hS.rad.Q_comm hx hy) (fun x hx y hy => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]) (hS.shape.commute_sup hS.Q_le_H₀) hx hy

theorem E_mul_self {x : G} (hx : x ∈ Q ⊔ zpowers t) : x * x = 1 := by
  obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hx
  · exact hS.rad.ψ_mul_self v
  · calc t * ψ v * (t * ψ v) = t * (ψ v * t) * ψ v := by group
      _ = t * (t * ψ v) * ψ v := by rw [hS.commute_ψ v]
      _ = (t * t) * (ψ v * ψ v) := by group
      _ = 1 := by rw [hS.shape.mul_self, hS.rad.ψ_mul_self, one_mul]

theorem card_E : Nat.card (Q ⊔ zpowers t : Subgroup G) = 128 := by
  rw [hS.shape.card_sup hS.Q_le_H₀, hS.rad.card_Q]

theorem centralizer_E :
    centralizer ((Q ⊔ zpowers t : Subgroup G) : Set G) = Q ⊔ zpowers t := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_centralizer_iff.2 fun y hy =>
    hS.E_comm hy hx)
  exact hS.data.centralizer_Q
    ⟨centralizer_le (Set.singleton_subset_iff.2 (mem_sup_right (mem_zpowers t))) hx,
      centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx⟩

theorem E_le_TH : (Q ⊔ zpowers t : Subgroup G) ≤ S₀ ⊔ zpowers t :=
  sup_le_sup_right hS.Q_le_S₀ _

theorem TH_le_normalizer_E :
    (S₀ ⊔ zpowers t : Subgroup G) ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
  refine sup_le (fun x hx => mem_normalizer_sup (hS.data.le_normalizer hx)
    (mem_normalizer_zpowers (hS.shape.commute_of_mem (hS.data.S₀_le hx))))
    (zpowers_le.2 (le_normalizer (mem_sup_right (mem_zpowers t))))

theorem center_TH {z : G} (hz : z ∈ S₀ ⊔ zpowers t)
    (hc : ∀ x ∈ S₀ ⊔ zpowers t, z * x = x * z) : z = 1 ∨ z = a ∨ z = t ∨ z = t * a := by
  have hzQ : z ∈ Q ⊔ zpowers t := by
    refine hS.data.centralizer_Q ⟨mem_centralizer_singleton_iff.2
      (hc t (mem_sup_right (mem_zpowers t))),
      mem_centralizer_iff.2 fun q hq => (hc q (hS.E_le_TH (mem_sup_left hq))).symm⟩
  obtain ⟨q, hq, hzq⟩ := (hS.shape.mem_sup_iff hS.Q_le_H₀).1 hzQ
  have hqU : ∀ x ∈ U, q * x = x * q := by
    intro x hx
    have hxT : x ∈ S₀ ⊔ zpowers t := mem_sup_left (hS.data.U_le hx)
    have hxt : x * t = t * x := hS.shape.commute_of_mem (hS.data.S₀_le (hS.data.U_le hx))
    rcases hzq with rfl | rfl
    · exact hc x hxT
    · have h := hc x hxT
      have : q * x * t = x * q * t := by
        calc q * x * t = q * (x * t) := by group
          _ = q * (t * x) := by rw [hxt]
          _ = q * t * x := by group
          _ = x * (q * t) := h
          _ = x * q * t := by group
      exact mul_right_cancel this
  have hqt : q * t = t * q := hS.shape.commute_of_mem (hS.Q_le_H₀ hq)
  rcases hS.rad.center_U q (hS.rad.Q_le_U hq) hqU with rfl | rfl <;> rcases hzq with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl (one_mul t)))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr hqt))

theorem not_isSylow [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (T : Sylow 2 G) : (T : Subgroup G) ≠ S₀ ⊔ zpowers t := by
  intro hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : S₀.relIndex (T : Subgroup G) = 2 := hT ▸ hS.shape.relIndex_sup hS.data.S₀_le
  have ht2 : t ^ 2 = 1 := by rw [pow_two, hS.shape.mul_self]
  obtain ⟨g, hgS, hodd⟩ := CFSG.Monster.B.Recog.exists_conj_mem_odd_relIndex_of_transfer T hidx ht2
    (mem_of_index_eq_two_of_simple hG hnab t)
  set u := g * t * g⁻¹ with hu
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  have hTC : (T : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hT] at hx
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hS.TH_le_centralizer hx)
    rw [hC, mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  have hdvd : Nat.card T ∣ Nat.card C := by
    have h1 := card_dvd_of_le hTC
    rwa [card_map_of_injective (MulAut.conj g).injective] at h1
  have hmul := relIndex_mul_card (H := (T : Subgroup G)) (K := C)
  obtain ⟨k, hk⟩ := (T.isPGroup').exists_card_eq
  have hcop : Nat.Coprime (2 ^ k) ((T : Subgroup G).relIndex C) :=
    Nat.Coprime.pow_left k (Odd.coprime_two_left hodd)
  have hdvd' : Nat.card T ∣ Nat.card ((T : Subgroup G) ⊓ C : Subgroup G) := by
    rw [← hmul, mul_comm] at hdvd
    rw [hk] at hdvd ⊢
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hTle : (T : Subgroup G) ≤ C := by
    have h1 : (T : Subgroup G) ⊓ C = T :=
      eq_of_le_of_card_ge inf_le_left (Nat.le_of_dvd Nat.card_pos hdvd')
    rw [← h1]
    exact inf_le_right
  have hucent : ∀ x ∈ S₀ ⊔ zpowers t, u * x = x * u := fun x hx =>
    (mem_centralizer_singleton_iff.1 (hTle (hT ▸ hx))).symm
  have huH : u ∈ H₀ := hS.data.S₀_le hgS
  rcases hS.center_TH (mem_sup_left hgS) hucent with h | h | h | h
  · apply hS.shape.ne_one
    have h' : g * t * g⁻¹ = 1 := h
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  · exact hS.shape.conj_not_mem hS.rad.odd g (by
      rw [show g * t * g⁻¹ = a from h]; exact hS.rad.Q_le_L hS.rad.a_mem_Q)
  · exact hS.shape.not_mem (h ▸ huH)
  · apply hS.shape.not_mem
    have h2 : t = u * a⁻¹ := by rw [h]; group
    rw [h2]
    exact H₀.mul_mem huH (H₀.inv_mem hS.a_mem_H₀)

theorem exists_conj_eq_mul [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∃ n ∈ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * a := by
  set TH : Subgroup G := S₀ ⊔ zpowers t with hTHdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS'⟩ := hS.isPGroup_TH.exists_le_sylow
  have hlt : TH < S := lt_of_le_of_ne hS' (fun h => hS.not_isSylow hG hnab S h.symm)
  obtain ⟨n, hnS, hnN, hnTH⟩ := exists_mem_normalizer_not_mem S.isPGroup' hlt
  have hnt : n * t ≠ t * n := by
    intro hnt
    set V : Subgroup G := TH ⊔ zpowers n
    have hVS : V ≤ S := sup_le hS' (zpowers_le.2 hnS)
    have hV : V = TH := hS.data.sylow V (sup_le hS.TH_le_centralizer (zpowers_le.2
      (mem_centralizer_singleton_iff.2 hnt))) (S.isPGroup'.to_le hVS) le_sup_left
    exact hnTH (hV ▸ mem_sup_right (mem_zpowers n))
  have hmem : n * t * n⁻¹ ∈ TH := (mem_normalizer_iff.1 hnN t).1 (mem_sup_right (mem_zpowers t))
  have hcent : ∀ x ∈ TH, n * t * n⁻¹ * x = x * (n * t * n⁻¹) := by
    intro x hx
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ TH := (mem_normalizer_iff.1 (inv_mem hnN) x).1 hx
    rw [inv_inv] at hx'
    have hc : n⁻¹ * x * n * t = t * (n⁻¹ * x * n) :=
      mem_centralizer_singleton_iff.1 (hS.TH_le_centralizer hx')
    calc n * t * n⁻¹ * x = n * (t * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * (n⁻¹ * x * n * t) * n⁻¹ := by rw [← hc]
      _ = x * (n * t * n⁻¹) := by group
  rcases hS.center_TH hmem hcent with h | h | h | h
  · exfalso
    apply hS.shape.ne_one
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · exact absurd (h ▸ hS.rad.Q_le_L hS.rad.a_mem_Q) (hS.shape.conj_not_mem hS.rad.odd n)
  · exact absurd (by
      calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [h]) hnt
  · exact ⟨n, hnN, h⟩

end Setting

end CFSG.EvenSmallLie.OmegaEight.SplitC
