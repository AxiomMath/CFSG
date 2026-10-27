module

public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Open

variable {G : Type*} [Group G] {p : ℕ} {E F : Subgroup G}

theorem IsElemAbelian.comm (h : IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  have := h.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)

theorem IsElemAbelian.comap {H : Type*} [Group H] {E : Subgroup H} (h : IsElemAbelian p E)
    {f : G →* H} (hf : Function.Injective f) : IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h.comm a.2 b.2
  · rw [map_pow, h.2 _ hx, map_one]

theorem IsElemAbelian.closure_of_commute {s : Set G} (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hp : ∀ a ∈ s, a ^ p = 1) : IsElemAbelian p (Subgroup.closure s) := by
  have hcomm : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s : Set G) := by
    rw [Subgroup.centralizer_closure]
    refine (Subgroup.closure_le _).2 fun a ha => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun b hb => hc b hb a ha
  have hall : ∀ g ∈ Subgroup.closure s, g ^ p = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha => exact hp a ha
    | one => simp
    | mul a b ha hb iha ihb =>
        have hab : a * b = b * a := Subgroup.mem_centralizer_iff.1 (hcomm hb) a ha
        rw [Commute.mul_pow hab, iha, ihb, one_mul]
    | inv a ha iha => simp [inv_pow, iha]
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hall x hx⟩
  exact Subgroup.mem_centralizer_iff.1 (hcomm b.2) a a.2

theorem IsElemAbelian.sup_of_commute (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hc : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a) : IsElemAbelian p (E ⊔ F) := by
  have hEF : E ⊔ F = Subgroup.closure ((E : Set G) ∪ F) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hEF]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a (ha | ha) b (hb | hb)
    · exact hE.comm ha hb
    · exact hc a ha b hb
    · exact (hc b hb a ha).symm
    · exact hF.comm ha hb
  · rintro a (ha | ha)
    · exact hE.2 a ha
    · exact hF.2 a ha

theorem IsElemAbelian.mul_self_eq_one (h : IsElemAbelian 2 E) {a : G} (ha : a ∈ E) : a * a = 1 := by
  rw [← pow_two]
  exact h.2 a ha

end CFSG.Open

namespace CFSG

theorem IsElementaryAbelian.of_forall {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ a ∈ E, a ^ p = 1) :
    IsElementaryAbelian p E :=
  Open.isElemAbelian_iff_isElementaryAbelian.mp
    ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem IsElementaryAbelian.two_of_forall_mul_self {G : Type*} [Group G] {E : Subgroup G}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) :
    IsElementaryAbelian 2 E :=
  IsElementaryAbelian.of_forall hc fun a ha => by rw [pow_two]; exact hsq a ha

end CFSG
