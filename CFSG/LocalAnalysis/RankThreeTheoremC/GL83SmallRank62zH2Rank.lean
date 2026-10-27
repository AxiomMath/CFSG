module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxGroup
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.SectionRank Subgroup

variable {G : Type} [Group G]

theorem k631b_isElemAbelian_zpowers {f : ℕ} {x : G} (hx : x ^ f = 1) :
    IsElemAbelian f (zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

private theorem k631b_noncomm_aux {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n => h m m.2 n n.2

theorem k631b_mem_sup {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {z : G}
    (hz : z ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = z := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (k631b_noncomm_aux h)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hz
  obtain ⟨⟨a, b⟩, rfl⟩ := hz
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem k631b_join_elem {f : ℕ} {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) (hA : IsElemAbelian f A) (hB : IsElemAbelian f B) :
    IsElemAbelian f (A ⊔ B) ∧ Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype (k631b_noncomm_aux h) with hφ
  have hrange : φ.range = A ⊔ B := by
    have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (k631b_noncomm_aux h)
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hinf
  obtain ⟨hAc, hAe⟩ := hA
  obtain ⟨hBc, hBe⟩ := hB
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · intro x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    rw [← hrange] at hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    apply Subtype.ext
    show φ u * φ v = φ v * φ u
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (congrArg Subtype.val (hAc.is_comm.comm u.1 v.1))
    · exact Subtype.ext (congrArg Subtype.val (hBc.is_comm.comm u.2 v.2))
  · intro x hx
    rw [← hrange] at hx
    obtain ⟨u, rfl⟩ := hx
    rw [← map_pow]
    have : u ^ f = 1 := Prod.ext (Subtype.ext (hAe _ u.1.2 |> fun h' => by simpa using h'))
      (Subtype.ext (hBe _ u.2.2 |> fun h' => by simpa using h'))
    rw [this, map_one]
  · have e : (A × B) ≃ (A ⊔ B : Subgroup G) :=
      (MonoidHom.ofInjective hinj).toEquiv.trans (MulEquiv.subgroupCongr hrange).toEquiv
    rw [← Nat.card_prod, Nat.card_congr e]

theorem k631b_sup_zpowers {f : ℕ} (hf : f.Prime) {B : Subgroup G} {x : G} {k : ℕ}
    (hB : IsElemAbelian f B) (hBk : Nat.card B = f ^ k) (hx : x ^ f = 1) (hxB : x ∉ B)
    (hc : ∀ b ∈ B, b * x = x * b) :
    IsElemAbelian f (B ⊔ zpowers x) ∧ Nat.card (B ⊔ zpowers x : Subgroup G) = f ^ (k + 1) := by
  have : Fact f.Prime := ⟨hf⟩
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ B.one_mem)
  have hcard : Nat.card (zpowers x) = f := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx hx1]
  have hZ : IsElemAbelian f (zpowers x) := k631b_isElemAbelian_zpowers hx
  have hinf : B ⊓ zpowers x = ⊥ := by
    have hdvd : Nat.card (B ⊓ zpowers x : Subgroup G) ∣ f := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hf).mp hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hfin : Finite (zpowers x) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; exact hf.ne_zero)
      have heq : B ⊓ zpowers x = zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard, h1])
      have hxI : x ∈ B ⊓ zpowers x := by
        rw [heq]
        exact mem_zpowers x
      exact hxB hxI.1
  have hcomm : ∀ b ∈ B, ∀ z ∈ zpowers x, b * z = z * b := by
    intro b hb z hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute b x from hc b hb) n).eq
  obtain ⟨hJe, hJc⟩ := k631b_join_elem hcomm hinf hB hZ
  refine ⟨hJe, ?_⟩
  rw [hJc, hBk, hcard, pow_succ]

theorem k631b_exists_order_f {f : ℕ} (hf : f.Prime) {E : Subgroup G} (hE : IsPGroup f E) {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) : ∃ x ∈ zpowers e, x ^ f = 1 ∧ x ≠ 1 := by
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hE ⟨e, he⟩
  rw [Subgroup.orderOf_mk] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact he1 (orderOf_eq_one_iff.mp (by simpa using hm))
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨e ^ (f ^ m'), npow_mem_zpowers e _, ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, ← hm]
    exact pow_orderOf_eq_one e
  · refine pow_ne_one_of_lt_orderOf (pow_ne_zero m' hf.ne_zero) ?_
    rw [hm]
    exact Nat.pow_lt_pow_right hf.one_lt (Nat.lt_succ_self m')

variable [Finite G]

theorem k631b_succ_rank {f : ℕ} (hf : f.Prime) {B H : Subgroup G} {x : G} {k : ℕ}
    (hB : IsElemAbelian f B) (hBk : Nat.card B = f ^ k) (hBH : B ≤ H) (hxH : x ∈ H)
    (hx : x ^ f = 1) (hxB : x ∉ B) (hc : ∀ b ∈ B, b * x = x * b) :
    k + 1 ≤ CFSG.Open.pRank f H := by
  obtain ⟨hJe, hJc⟩ := k631b_sup_zpowers hf hB hBk hx hxB hc
  exact le_pRank hf.one_lt (sup_le hBH (zpowers_le.mpr hxH)) hJe hJc

theorem k631b_pRank_le_of_sylow {f : ℕ} (hf : f.Prime) {J S : Subgroup G} (hSJ : S ≤ J)
    (hS : IsPGroup f S) (hSi : ¬ f ∣ (S.subgroupOf J).index) :
    CFSG.Open.pRank f J ≤ CFSG.Open.pRank f S := by
  have : Fact f.Prime := ⟨hf⟩
  refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.pRank_le_of_sylow hSJ hS ?_
  intro n hn
  have h1 : Nat.card (S.subgroupOf J) * (S.subgroupOf J).index = Nat.card J :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (S.subgroupOf J) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSJ).toEquiv
  rw [← h1, h2] at hn
  have hcop : Nat.Coprime (f ^ n) (S.subgroupOf J).index :=
    ((Nat.Prime.coprime_iff_not_dvd hf).2 hSi).pow_left n
  exact hcop.dvd_of_dvd_mul_right hn

structure k631b_Ctx (f : ℕ) (E F : Subgroup G) : Prop where
  prime : f.Prime
  ne_two : f ≠ 2
  pgroup : IsPGroup f E
  sylow : ¬ f ∣ E.index
  comm : IsMulCommutative E
  rank : CFSG.Open.pRank f E = 4
  le : F ≤ E
  elem : IsElemAbelian f F
  card : Nat.card F = f ^ 4

theorem k631b_Ctx.mul_comm {f : ℕ} {E F : Subgroup G} (h : k631b_Ctx f E F) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have := h.comm
  exact setLike_mul_comm (s := E) ha hb

theorem k631b_Ctx.mem_of_pow {f : ℕ} {E F : Subgroup G} (h : k631b_Ctx f E F) {x : G}
    (hxE : x ∈ E) (hxf : x ^ f = 1) : x ∈ F := by
  by_contra hxF
  have h5 := k631b_succ_rank h.prime h.elem h.card h.le hxE hxf hxF
    (fun b hb => h.mul_comm (h.le hb) hxE)
  rw [h.rank] at h5
  omega

theorem k631b_Ctx.card_inf {f : ℕ} {E F : Subgroup G} (h : k631b_Ctx f E F) {D : Subgroup G}
    (hD : D ≤ E) : Nat.card (F ⊓ D : Subgroup G) = f ^ CFSG.Open.pRank f D := by
  have hFD : IsElemAbelian f (F ⊓ D) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le h.elem inf_le_left
  have hFp : IsPGroup f F := IsPGroup.of_card h.card
  have hp : IsPGroup f ↥(F ⊓ D) := hFp.to_le inf_le_left
  have : Fact f.Prime := ⟨h.prime⟩
  obtain ⟨j, hj⟩ := hp.exists_card_eq
  have h1 : j ≤ CFSG.Open.pRank f D := le_pRank h.prime.one_lt inf_le_right hFD hj
  have h2 : CFSG.Open.pRank f D ≤ j := by
    refine pRank_le h.prime.one_lt fun B hBD hB => ?_
    have hBF : B ≤ F := fun x hx => h.mem_of_pow (hD (hBD hx)) (hB.2 x hx)
    rw [← hj]
    exact Subgroup.card_le_of_le (le_inf hBF hBD)
  rw [hj]
  congr 1
  omega

theorem k631b_Ctx.pRank_inf {f : ℕ} {E F : Subgroup G} (h : k631b_Ctx f E F) {D : Subgroup G}
    (hD : D ≤ E) : CFSG.Open.pRank f (F ⊓ D) = CFSG.Open.pRank f D := by
  refine le_antisymm (pRank_mono h.prime.one_lt inf_le_right) ?_
  exact le_pRank h.prime.one_lt le_rfl
    (CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le h.elem inf_le_left)
    (h.card_inf hD)

theorem k631b_Ctx.rank_split {f : ℕ} {E F : Subgroup G} (h : k631b_Ctx f E F)
    {D₁ D₂ : Subgroup G} (h1 : D₁ ≤ E) (h2 : D₂ ≤ E) (hinf : D₁ ⊓ D₂ = ⊥)
    (hsup : E ≤ D₁ ⊔ D₂) : CFSG.Open.pRank f D₁ + CFSG.Open.pRank f D₂ = 4 := by
  have hcomm : ∀ a ∈ F ⊓ D₁, ∀ b ∈ F ⊓ D₂, a * b = b * a :=
    fun a ha b hb => h.mul_comm (h.le ha.1) (h.le hb.1)
  have hinf' : (F ⊓ D₁) ⊓ (F ⊓ D₂) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ D₁ ⊓ D₂ := ⟨hx.1.2, hx.2.2⟩
    rwa [hinf] at this
  obtain ⟨-, hc⟩ := k631b_join_elem hcomm hinf'
    (CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le h.elem inf_le_left)
    (CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le h.elem inf_le_left)
  have hF : F ≤ (F ⊓ D₁) ⊔ (F ⊓ D₂) := by
    intro z hz
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
      k631b_mem_sup (fun a ha b hb => h.mul_comm (h1 ha) (h2 hb)) (hsup (h.le hz))
    have hz' : (x₁ * x₂) ^ f = 1 := h.elem.2 _ hz
    rw [(Commute.mul_pow (show Commute x₁ x₂ from h.mul_comm (h1 hx₁) (h2 hx₂)))] at hz'
    have h12 : x₁ ^ f = (x₂ ^ f)⁻¹ := eq_inv_of_mul_eq_one_left hz'
    have hmem : x₁ ^ f ∈ D₁ ⊓ D₂ := by
      refine ⟨D₁.pow_mem hx₁ f, ?_⟩
      rw [h12]
      exact D₂.inv_mem (D₂.pow_mem hx₂ f)
    rw [hinf, Subgroup.mem_bot] at hmem
    have hx2f : x₂ ^ f = 1 := by
      rw [hmem] at h12
      simpa using h12.symm
    exact mul_mem_sup ⟨h.mem_of_pow (h1 hx₁) hmem, hx₁⟩ ⟨h.mem_of_pow (h2 hx₂) hx2f, hx₂⟩
  have hFeq : (F ⊓ D₁) ⊔ (F ⊓ D₂) = F := le_antisymm (sup_le inf_le_left inf_le_left) hF
  rw [hFeq, h.card, h.card_inf h1, h.card_inf h2, ← pow_add] at hc
  exact (Nat.pow_right_injective h.prime.two_le hc).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
