module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

namespace Lemma124

@[expose] def Prop117cStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {K : Subgroup G} (hK : GLAPComponent p (Cg a) K) (ht : Type117c p A K),
    K ≤ M ∨ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_le {p : ℕ} {H K : Subgroup G} (hHK : H ≤ K) (hK : IsElemAbelian p K) :
    IsElemAbelian p H := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hK.2 x (hHK hx)⟩
  have h2 := congrArg Subtype.val (hK.1.is_comm.comm (⟨a.1, hHK a.2⟩ : K) ⟨b.1, hHK b.2⟩)
  exact Subtype.ext h2

theorem barX_mono_aux (p : ℕ) {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T :=
  Subgroup.map_mono fun _ hx => (Subgroup.mem_subgroupOf).2 (h ((Subgroup.mem_subgroupOf).1 hx))

theorem comp_le_aux {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) : L ≤ X := h.1

theorem pRank_eq_two_of_card_nine {H : Subgroup G} (hH : IsElemAbelian 3 H) (h9 : Nat.card H = 9) :
    CFSG.Open.pRank 3 H = 2 := by
  have hgreat : IsGreatest
      {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} 2 := by
    refine ⟨⟨H, le_rfl, hH, by rw [h9]; norm_num⟩, ?_⟩
    rintro k ⟨E, hEH, -, hEk⟩
    have hle : Nat.card E ≤ Nat.card H := Subgroup.card_le_of_le hEH
    rw [hEk, h9] at hle
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 3)).1 (by simpa using hle)
  unfold CFSG.Open.pRank
  exact hgreat.csSup_eq

theorem exists_isSylowIn_above_aux {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup 3 ↥P) :
    ∃ Q : Subgroup G, IsSylowIn 3 X Q ∧ P ≤ Q := by
  obtain ⟨Q, hPQ, hQmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ X ∧ IsPGroup 3 ↥R}).exists_le_maximal ⟨hPX, hP⟩
  exact ⟨Q, ⟨hQmax.1.1, hQmax.1.2, fun R' hR'X hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'X, hR'p⟩ hQR') hQR'⟩, hPQ⟩

theorem isPGroup_three_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 3 A) : IsPGroup 3 ↥A :=
  fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA.2 x.1 x.2)⟩

theorem card_eq_pow_pRank {A : Subgroup G} (hA : IsElemAbelian 3 A) :
    Nat.card A = 3 ^ CFSG.Open.pRank 3 A := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (isPGroup_three_of_isElemAbelian hA)
  have hsupEq : CFSG.Open.pRank 3 A = sSup
      {k : ℕ | ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := rfl
  have hbdd : BddAbove
      {k : ℕ | ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, -, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  have hnS : n ∈ {k : ℕ | ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} :=
    ⟨A, le_rfl, hA, hn⟩
  have hsup := Nat.sSup_mem ⟨n, hnS⟩ hbdd
  rw [← hsupEq] at hsup
  obtain ⟨E, hEA, -, hE⟩ := hsup
  have hnle : n ≤ CFSG.Open.pRank 3 A := by
    rw [hsupEq]
    exact le_csSup hbdd hnS
  have hdvd : Nat.card E ∣ Nat.card A := Subgroup.card_dvd_of_le hEA
  rw [hE, hn] at hdvd
  have hle : CFSG.Open.pRank 3 A ≤ n :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 hdvd
  rw [hn]
  congr 1
  omega

theorem card_eq_of_pRank_four {A : Subgroup G} (hA : IsElemAbelian 3 A)
    (hA4 : CFSG.Open.pRank 3 A = 4) : Nat.card A = 3 ^ 4 := by
  rw [card_eq_pow_pRank hA, hA4]

theorem exists_mul_of_mem_sup {H F : Subgroup G} (hcomm : ∀ h ∈ H, ∀ f ∈ F, h * f = f * h) {x : G}
    (hx : x ∈ H ⊔ F) : ∃ h ∈ H, ∃ f ∈ F, h * f = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, F.one_mem, mul_one x⟩
    · exact ⟨1, H.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, H.one_mem, 1, F.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨h1, hh1, f1, hf1, rfl⟩ := ihx
    obtain ⟨h2, hh2, f2, hf2, rfl⟩ := ihy
    refine ⟨h1 * h2, H.mul_mem hh1 hh2, f1 * f2, F.mul_mem hf1 hf2, ?_⟩
    calc h1 * h2 * (f1 * f2) = h1 * (h2 * f1) * f2 := by simp only [mul_assoc]
      _ = h1 * (f1 * h2) * f2 := by rw [hcomm h2 hh2 f1 hf1]
      _ = h1 * f1 * (h2 * f2) := by simp only [mul_assoc]
  | inv x _ ihx =>
    obtain ⟨h1, hh1, f1, hf1, rfl⟩ := ihx
    have hc : h1 * f1 = f1 * h1 := hcomm h1 hh1 f1 hf1
    refine ⟨h1⁻¹, H.inv_mem hh1, f1⁻¹, F.inv_mem hf1, ?_⟩
    calc h1⁻¹ * f1⁻¹ = (f1 * h1)⁻¹ := (mul_inv_rev f1 h1).symm
      _ = (h1 * f1)⁻¹ := by rw [hc]

theorem card_eq_mul_of_sup_eq {A H F : Subgroup G} (hcomm : ∀ h ∈ H, ∀ f ∈ F, h * f = f * h)
    (hdec : A = H ⊔ F) (hdisj : H ⊓ F = ⊥) : Nat.card A = Nat.card H * Nat.card F := by
  have hHA : ∀ h ∈ H, h ∈ A := fun h hh => by rw [hdec]; exact Subgroup.mem_sup_left hh
  have hFA : ∀ f ∈ F, f ∈ A := fun f hf => by rw [hdec]; exact Subgroup.mem_sup_right hf
  let φ : ↥H × ↥F → ↥A := fun q => ⟨q.1.1 * q.2.1, A.mul_mem (hHA _ q.1.2) (hFA _ q.2.2)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨h1, hh1⟩, ⟨f1, hf1⟩⟩ ⟨⟨h2, hh2⟩, ⟨f2, hf2⟩⟩ heq
      have hv : h1 * f1 = h2 * f2 := congrArg Subtype.val heq
      have e : h2⁻¹ * h1 = f2 * f1⁻¹ := by
        calc h2⁻¹ * h1 = h2⁻¹ * (h1 * f1) * f1⁻¹ := by group
          _ = h2⁻¹ * (h2 * f2) * f1⁻¹ := by rw [hv]
          _ = f2 * f1⁻¹ := by group
      have hmem : h2⁻¹ * h1 ∈ H ⊓ F := by
        refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem hh2) hh1, ?_⟩
        rw [e]
        exact F.mul_mem hf2 (F.inv_mem hf1)
      rw [hdisj, Subgroup.mem_bot] at hmem
      have h12 : h1 = h2 := (inv_mul_eq_one.1 hmem).symm
      have hf12 : f1 = f2 := by
        have h1' : f2 * f1⁻¹ = 1 := by rw [← e]; exact hmem
        exact (mul_inv_eq_one.1 h1').symm
      subst h12
      subst hf12
      rfl
    · intro x
      obtain ⟨h, hh, f, hf, hx⟩ := exists_mul_of_mem_sup hcomm (show (x : G) ∈ H ⊔ F by
        rw [← hdec]; exact x.2)
      exact ⟨(⟨h, hh⟩, ⟨f, hf⟩), Subtype.ext hx⟩
  have hc := Nat.card_congr (Equiv.ofBijective φ hφ)
  rw [Nat.card_prod] at hc
  exact hc.symm

end Helpers

section Pieces

variable {G : Type} [Group G] [Finite G]

theorem four_le_pRank_of_inputs (h123 : Lemma123Statement) (h122 : Lemma122_i_iiStatement)
    (h117c : Prop117cStatement) {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a)
    {K : Subgroup G} (hK : GLAPComponent 3 (Cg a) K)
    (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K) :
    4 ≤ CFSG.Open.pRank 3 A := by
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  have h3 : 3 ≤ CFSG.Open.pRank 3 A := h.pair.1.2.1.1.2
  by_contra hlt
  have hA3 : CFSG.Open.pRank 3 A = 3 := by omega
  have ht : Type117c 3 A K := ⟨rfl, hA3, hK3⟩
  rcases h117c h.toSec11 h.ha.1 h.ha.2 hK ht with hKM' | ⟨A1, hA1, haA1⟩
  · apply hKM
    have hKC : K ≤ M ⊓ Cg a := le_inf hKM' (comp_le_aux hK)
    exact barX_mono_aux 3 hKC
  · exact (h122 h).2 ⟨A1, hA1, haA1⟩

theorem pRank_inter_eq_two_of_inputs (h123 : Lemma123Statement) {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) : CFSG.Open.pRank 3 (E ⊓ A) = 2 := by
  obtain ⟨hp3, -, -, -, -, ⟨hcard, -⟩, -⟩ := h123 h
  subst hp3
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  exact pRank_eq_two_of_card_nine (isElemAbelian_of_le inf_le_right hAel) hcard

theorem inter_disjoint_centBar_of_faithful {E A K : Subgroup G}
    (hfaith : InducesFaithfulInner 3 (E ⊓ A) K) : (E ⊓ A) ⊓ centBar 3 A K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxA₀, hxF⟩ := Subgroup.mem_inf.1 hx
  have hxC : x ∈ centBar 3 ⊤ K := by
    unfold centBar at hxF ⊢
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxF).1, Subgroup.mem_top x⟩
  exact hfaith.2.1 x hxA₀ hxC

end Pieces

end Lemma124

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
