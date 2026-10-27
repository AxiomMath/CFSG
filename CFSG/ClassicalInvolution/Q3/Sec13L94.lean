module

public import CFSG.ClassicalInvolution.Q3.TL3T21
import CFSG.ClassicalInvolution.Q3.TL3T22
import CFSG.ClassicalInvolution.Q3.Sec13StarCount
import CFSG.ClassicalInvolution.Asc77.AscCX5
import CFSG.ClassicalInvolution.Asc77.AscC25W1
import CFSG.ClassicalInvolution.Asc77.AscE187B2a
import CFSG.ClassicalInvolution.Q3.Q3T7C231Clique
import CFSG.ClassicalInvolution.Q3.Q3T7P24A00
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace L94

section Q8

variable {L : Subgroup G} {s : G}

private theorem comm_of_mem (hs : IsUniqueInvolution L s) {x : G} (hx : x ∈ L) : x * s = s * x :=
  mul_inv_eq_iff_eq_mul.1 (hs.conj_eq (conjSub_eq_self_of_mem hx))

private theorem orderOf_eq_four_of_sq (h8 : Nat.card L = 8) (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x)
    {w : G} (hw : w ∈ L) (hw2 : w * w ≠ 1) : orderOf w = 4 := by
  have hdvd : orderOf w ∣ 8 := h8 ▸ L.orderOf_dvd_natCard hw
  have h1 : orderOf w ≠ 1 := fun h => hw2 (by rw [orderOf_eq_one_iff.1 h, mul_one])
  have h2 : orderOf w ≠ 2 := fun h => hw2 (by rw [← sq, ← h, pow_orderOf_eq_one])
  have h8' : orderOf w ≠ 8 := by
    intro h
    have heq : Subgroup.zpowers w = L :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw) (by rw [h8, Nat.card_zpowers, h])
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    rw [← heq, Subgroup.mem_zpowers_iff] at hx hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact hxy (Commute.zpow_zpow_self w m n).eq
  obtain ⟨k, hk⟩ : ∃ k, orderOf w = k := ⟨_, rfl⟩
  rw [hk] at hdvd h1 h2 h8' ⊢
  have hpos : 0 < k := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : k ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases k <;> omega

private theorem mul_self_eq (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {w : G} (hw : w ∈ L) (hw1 : w ≠ 1) (hws : w ≠ s) :
    w * w = s := by
  have hw2 : w * w ≠ 1 := fun h => (hs.unique w hw h).elim hw1 hws
  have h4 : w ^ 4 = 1 := by
    rw [← orderOf_eq_four_of_sq h8 hnab hw hw2]
    exact pow_orderOf_eq_one w
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq] at h4
  exact (hs.unique _ (L.mul_mem hw hw) h4).resolve_left hw2

private theorem orderOf_eq_four (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {w : G} (hw : w ∈ L) (hw1 : w ≠ 1) (hws : w ≠ s) :
    orderOf w = 4 :=
  orderOf_eq_four_of_sq h8 hnab hw fun h => (hs.unique w hw h).elim hw1 hws

private theorem commutator_eq (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {x y : G} (hx : x ∈ L) (hy : y ∈ L) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = s := by
  have key : ∀ a ∈ L, a = 1 ∨ a = s → ∀ b ∈ L, a * b = b * a := by
    rintro a - (rfl | rfl) b hb
    · rw [one_mul, mul_one]
    · exact (comm_of_mem hs hb).symm
  by_cases hx1 : x = 1 ∨ x = s
  · left
    rw [key x hx hx1 y hy, mul_inv_cancel_right, mul_inv_cancel]
  by_cases hy1 : y = 1 ∨ y = s
  · left
    rw [← key y hy hy1 x hx, mul_inv_cancel_right, mul_inv_cancel]
  push Not at hx1 hy1
  have hxs := mul_self_eq hs h8 hnab hx hx1.1 hx1.2
  have hys := mul_self_eq hs h8 hnab hy hy1.1 hy1.2
  have hxi : x⁻¹ = x * s := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hxs, hs.sq]
  have hyi : y⁻¹ = y * s := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hys, hs.sq]
  have hxy : x * y * x⁻¹ * y⁻¹ = x * y * (x * y) := by
    rw [hxi, hyi]
    calc x * y * (x * s) * (y * s) = x * y * x * (s * y) * s := by group
      _ = x * y * x * (y * s) * s := by rw [comm_of_mem hs hy]
      _ = x * y * (x * y) * (s * s) := by group
      _ = x * y * (x * y) := by rw [hs.sq, mul_one]
  rw [hxy]
  by_cases h : x * y = 1 ∨ x * y = s
  · left
    rcases h with h | h <;> rw [h]
    · rw [mul_one]
    · exact hs.sq
  · push Not at h
    exact Or.inr (mul_self_eq hs h8 hnab (L.mul_mem hx hy) h.1 h.2)

private theorem exists_fixed (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {y : G} (hyL : ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hy2 : y * y = 1) :
    ∃ x ∈ L, orderOf x = 4 ∧ (y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x * s) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := ⟨a, ha, b, hb, hab⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact hab (by rw [one_mul, mul_one])
  have has : a ≠ s := by rintro rfl; exact hab (comm_of_mem hs hb).symm
  have ha4 := orderOf_eq_four hs h8 hnab ha ha1 has
  have hasq := mul_self_eq hs h8 hnab ha ha1 has
  have hai : a⁻¹ = a * s := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hasq, hs.sq]
  set a' := y * a * y⁻¹ with ha'
  have ha'L : a' ∈ L := hyL a ha
  by_cases hfix : a' = a ∨ a' = a * s
  · exact ⟨a, ha, ha4, hfix⟩
  push Not at hfix
  have hx1 : a * a' ≠ 1 := by
    intro h
    apply hfix.2
    rw [← hai]
    exact eq_inv_of_mul_eq_one_right h
  have hxs : a * a' ≠ s := by
    intro h
    apply hfix.1
    have : a' = a⁻¹ * s := by rw [← h, inv_mul_cancel_left]
    rw [this, hai, mul_assoc, hs.sq, mul_one]
  refine ⟨a * a', L.mul_mem ha ha'L, orderOf_eq_four hs h8 hnab (L.mul_mem ha ha'L) hx1 hxs, ?_⟩
  have hconj : y * (a * a') * y⁻¹ = a' * a := by
    calc y * (a * a') * y⁻¹ = a' * ((y * y) * a * (y * y)⁻¹) := by rw [ha']; group
      _ = a' * a := by rw [hy2, one_mul, inv_one, mul_one]
  rw [hconj]
  have hc : a' * a = (a' * a * a'⁻¹ * a⁻¹) * (a * a') := by group
  rcases commutator_eq hs h8 hnab ha'L ha with h | h
  · left
    rw [hc, h, one_mul]
  · right
    rw [hc, h, ← comm_of_mem hs (L.mul_mem ha ha'L)]

end Q8

private theorem exists_noncomm (hΩ : HypOmegaGen Ω) {L : Subgroup G} (hL : L ∈ Ω)
    (h2 : IsPGroup 2 L) : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  obtain ⟨-, P, hP, hPnab⟩ := hΩ.omega1 L hL
  have hPL : L = P := hP.2.2 L le_rfl h2 hP.1
  subst hPL
  by_contra h
  push Not at h
  exact hPnab (IsMulCommutative.of_comm fun a b => Subtype.ext (h a a.2 b b.2))

private theorem eq_one_or_eq_of_mem_zpowers {s w : G} (hs : s * s = 1)
    (hw : w ∈ Subgroup.zpowers s) : w = 1 ∨ w = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hs2 : s ^ (2 : ℤ) = 1 := by rw [zpow_two, hs]
  rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hs2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · exact Or.inl (zpow_zero s)
  · exact Or.inr (zpow_one s)

private theorem comm_of_conj_eq {x y : G} (h : y * x * y⁻¹ = x) : x * y = y * x := by
  calc x * y = y * x * y⁻¹ * y := by rw [h]
    _ = y * x := by group

private theorem conj_eq_of_comm {x y : G} (h : x * y = y * x) : y * x * y⁻¹ = x := by
  rw [← h, mul_inv_cancel_right]

private theorem isPGroup_zpowers_of_mul_self {x : G} (hx : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hx])
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

private theorem orderOf_inv_conj (y x : G) : orderOf (y⁻¹ * x * y) = orderOf x := by
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj y⁻¹) x

private theorem mem_dSet_of_orderOf_four (hΩ : HypOmegaGen Ω) (h2 : ∀ L ∈ Ω, IsPGroup 2 L)
    (h8 : ∀ L ∈ Ω, Nat.card L = 8) {W : Subgroup G} (hW : W ∈ WSet Ω) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hWP : W ≤ P) {M : Subgroup G} (hM : M ∈ Ω) {x : G} (hxM : x ∈ M)
    (hxP : x ∈ P) (hx4 : orderOf x = 4) : M ∈ DSet Ω W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hMM : IsSylow2In M M := ⟨le_rfl, h2 M hM, fun V hVM _ hMV => le_antisymm hVM hMV⟩
  have hU : Subgroup.zpowers x ∈ USet Ω :=
    mem_USet_of_natCard hM hMM (Subgroup.zpowers_le.mpr hxM) inferInstance
      (by rw [Nat.card_zpowers, hx4, h8 M hM])
  obtain ⟨T, hTD, hTM⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW (hWP.trans hPQ) hM hU
    (Subgroup.zpowers_le.mpr hxM) (Subgroup.zpowers_le.mpr (hPQ hxP))
  rw [hTM.2.2 M le_rfl (h2 M hM) hTM.1]
  exact hTD

private theorem false_of_forall_conj_ne (hΩ : HypOmegaGen Ω) (h2 : ∀ L ∈ Ω, IsPGroup 2 L)
    (h8 : ∀ L ∈ Ω, Nat.card L = 8) {W S : Subgroup G} (hW : W ∈ WSet Ω)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {z e : G} (hzW : z ∈ W) (heW : e ∈ W)
    (he2 : e * e = 1) (hz2 : z * z = 1)
    (hS : IsSylow2In S (Subgroup.centralizer ({z} : Set G))) (hWS : W ≤ S)
    (hSe : S ≤ Subgroup.centralizer ({e} : Set G))
    (hT : ∀ R ∈ Ω, R ∈ DSet Ω W → ∀ r : G, IsUniqueInvolution R r →
      ∃ n ∈ Subgroup.centralizer ({e} : Set G), n * z * n⁻¹ = r)
    (hZ : z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G)))
    {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hLL' : L ≠ L') {s : G}
    (hs : IsUniqueInvolution L s) (hs' : IsUniqueInvolution L' s)
    (hpair : ∀ M ∈ Ω, IsUniqueInvolution M s → M = L ∨ M = L')
    (hsz : s * z = z * s) (hV : (L ⊔ L') ⊓ Subgroup.centralizer ({z} : Set G) ≤ S)
    (hbad : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ y ∈ Subgroup.centralizer ({e} : Set G),
      c * s * c⁻¹ ≠ y * z * y⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hze : z * e = e * z := hWab z hzW e heW
  have hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x :=
    PhilipHall.Frame.twin_commute hΩ hL hL' hLL' hs hs' (h2 L hL)
  have hinf : ∀ w ∈ L, w ∈ L' → w = 1 ∨ w = s := by
    intro w hw hw'
    have hmem : w ∈ L ⊓ L' := ⟨hw, hw'⟩
    rw [PhilipHall.Frame.twin_inf_eq hΩ hL hL' hLL' hs hs' (h2 L hL)] at hmem
    exact eq_one_or_eq_of_mem_zpowers hs.sq hmem
  have hdec : ∀ a ∈ L, ∀ a' ∈ L, ∀ b ∈ L', ∀ b' ∈ L', a * b = a' * b' →
      a' = a ∨ a' = a * s := by
    intro a ha a' ha' b hb b' hb' h
    have h1 : a⁻¹ * a' = b * b'⁻¹ := by
      calc a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
        _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [h]
        _ = b * b'⁻¹ := by group
    have hL1 : a⁻¹ * a' ∈ L := L.mul_mem (L.inv_mem ha) ha'
    have hL2 : a⁻¹ * a' ∈ L' := h1 ▸ L'.mul_mem hb (L'.inv_mem hb')
    rcases hinf _ hL1 hL2 with h3 | h3
    · left
      calc a' = a * (a⁻¹ * a') := by group
        _ = a := by rw [h3, mul_one]
    · right
      calc a' = a * (a⁻¹ * a') := by group
        _ = a * s := by rw [h3]
  have hnab := exists_noncomm hΩ hL (h2 L hL)
  have hnab' := exists_noncomm hΩ hL' (h2 L' hL')
  have hzC : s ∈ (L ⊔ L') ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨Subgroup.mem_sup_left hs.mem, Subgroup.mem_centralizer_singleton_iff.mpr hsz⟩
  have hse : s * e = e * s := Subgroup.mem_centralizer_singleton_iff.mp (hSe (hV hzC))
  have hperm : ∀ y : G, y * s * y⁻¹ = s → ∀ M ∈ Ω, IsUniqueInvolution M s →
      conjSub y M = L ∨ conjSub y M = L' := fun y hy M hM hsM =>
    hpair _ (hΩ.conjInvariant y M hM) (by simpa [hy] using hsM.conj y)
  have hzs : z * s * z⁻¹ = s := by rw [← hsz, mul_inv_cancel_right]
  have hes : e * s * e⁻¹ = s := by rw [← hse, mul_inv_cancel_right]
  have hW2 : IsPGroup 2 W := hS.2.1.to_le hWS
  have F1 : ∀ M ∈ Ω, IsUniqueInvolution M s → ∀ x ∈ M, orderOf x = 4 → x * e ≠ e * x := by
    intro M hM hsM x hxM hx4 hxe
    have hWe : W ≤ Subgroup.centralizer ({e} : Set G) := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw e heW)
    obtain ⟨P, hP, hWP⟩ := IsSylow2In.exists_ge hW2 hWe
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
    obtain ⟨y, hy, hxy⟩ := exists_conj_of_isSylow2In hP hx2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxe))
    have hx' : y⁻¹ * x * y ∈ P := mem_conjSub_iff.mp (hxy (Subgroup.mem_zpowers x))
    have hM' : conjSub y⁻¹ M ∈ Ω := hΩ.conjInvariant y⁻¹ M hM
    have hxM' : y⁻¹ * x * y ∈ conjSub y⁻¹ M := by
      simpa using conj_mem_conjSub (n := y⁻¹) hxM
    have hD := mem_dSet_of_orderOf_four hΩ h2 h8 hW hP.2.1 hWP hM' hxM' hx'
      (by rw [orderOf_inv_conj]; exact hx4)
    obtain ⟨n, hn, hnz⟩ := hT _ hM' hD _ (hsM.conj y⁻¹)
    refine hbad 1 (Subgroup.one_mem _) (y * n) (Subgroup.mul_mem _ hy hn) ?_
    calc 1 * s * 1⁻¹ = y * (y⁻¹ * s * y⁻¹⁻¹) * y⁻¹ := by group
      _ = y * n * z * (y * n)⁻¹ := by rw [← hnz]; group
  have F2 : ∀ M ∈ Ω, IsUniqueInvolution M s → ∀ x ∈ M, orderOf x = 4 → x * z ≠ z * x := by
    intro M hM hsM x hxM hx4 hxz
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
    obtain ⟨y, hy, hxy⟩ := exists_conj_of_isSylow2In hS hx2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxz))
    have hx' : y⁻¹ * x * y ∈ S := mem_conjSub_iff.mp (hxy (Subgroup.mem_zpowers x))
    have hM' : conjSub y⁻¹ M ∈ Ω := hΩ.conjInvariant y⁻¹ M hM
    have hxM' : y⁻¹ * x * y ∈ conjSub y⁻¹ M := by
      simpa using conj_mem_conjSub (n := y⁻¹) hxM
    have hD := mem_dSet_of_orderOf_four hΩ h2 h8 hW hS.2.1 hWS hM' hxM' hx'
      (by rw [orderOf_inv_conj]; exact hx4)
    obtain ⟨n, hn, hnz⟩ := hT _ hM' hD _ (hsM.conj y⁻¹)
    exact hbad y⁻¹ (Subgroup.inv_mem _ hy) n hn hnz.symm
  have hcz : ∀ y : G, ∀ M N : Subgroup G, conjSub y M = N → ∀ m ∈ M, y * m * y⁻¹ ∈ N :=
    fun y M N h m hm => h ▸ conj_mem_conjSub hm
  have hother : ∀ y : G, y * s * y⁻¹ = s →
      (conjSub y L = L → conjSub y L' = L') ∧ (conjSub y L = L' → conjSub y L' = L) := by
    intro y hy
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hperm y hy L' hL' hs' with h' | h'
      · exact absurd (conjSub_injective y (h.trans h'.symm)) hLL'
      · exact h'
    · rcases hperm y hy L' hL' hs' with h' | h'
      · exact h'
      · exact absurd (conjSub_injective y (h.trans h'.symm)) hLL'
  have hX2 : IsPGroup 2 (L ⊔ L' : Subgroup G) := IsPGroup.to_sup_of_normal_right' (h2 L hL)
    (h2 L' hL') (Sec6Gen.le_normalizer_of_twin hΩ hL hL' hLL' hs hs')
  have hzX : conjSub z (L ⊔ L') = L ⊔ L' := by
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub]
    rcases hperm z hzs L hL hs with h | h
    · rw [h, (hother z hzs).1 h]
    · rw [h, (hother z hzs).2 h, sup_comm]
  have hV2 : IsPGroup 2 ((L ⊔ L') ⊔ Subgroup.zpowers z : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hX2 (isPGroup_zpowers_of_mul_self hz2)
      (Subgroup.zpowers_le.mpr ((mem_normalizer_iff_conjSub_eq).mpr hzX))
  have F3 : ∀ d ∈ L ⊔ L', d * (e * z) = (e * z) * d → d * z = z * d := fun d hd hde =>
    CX.comm_of_mem_zStarOf hV2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
      (Subgroup.mem_sup_left hd) hZ (by rw [← mul_assoc, hze, mul_assoc]) hde
  have hw2 : e * z * (e * z) = 1 := by
    calc e * z * (e * z) = e * (z * e) * z := by group
      _ = e * e * (z * z) := by rw [hze]; group
      _ = 1 := by rw [he2, hz2, mul_one]
  rcases hperm z hzs L hL hs with hzL | hzL
  ·
    have hzL' := (hother z hzs).1 hzL
    rcases hperm e hes L hL hs with heL | heL
    ·
      have heL' := (hother e hes).1 heL
      obtain ⟨x₁, hx₁, hx₁4, hzx₁⟩ := exists_fixed hs (h8 L hL) hnab (hcz z L L hzL) hz2
      have hzx₁' : z * x₁ * z⁻¹ = x₁ * s :=
        hzx₁.resolve_left fun h => F2 L hL hs x₁ hx₁ hx₁4 (comm_of_conj_eq h)
      obtain ⟨x₂, hx₂, hx₂4, hzx₂⟩ := exists_fixed hs' (h8 L' hL') hnab' (hcz z L' L' hzL') hz2
      have hzx₂' : z * x₂ * z⁻¹ = x₂ * s :=
        hzx₂.resolve_left fun h => F2 L' hL' hs' x₂ hx₂ hx₂4 (comm_of_conj_eq h)
      have hdz : x₁ * x₂ * z = z * (x₁ * x₂) := by
        apply comm_of_conj_eq
        calc z * (x₁ * x₂) * z⁻¹ = (z * x₁ * z⁻¹) * (z * x₂ * z⁻¹) := by group
          _ = x₁ * (s * x₂) * s := by rw [hzx₁', hzx₂']; group
          _ = x₁ * (x₂ * s) * s := by rw [comm_of_mem hs' hx₂]
          _ = x₁ * x₂ * (s * s) := by group
          _ = x₁ * x₂ := by rw [hs.sq, mul_one]
      have hdS : x₁ * x₂ ∈ S := hV ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left hx₁)
        (Subgroup.mem_sup_right hx₂), Subgroup.mem_centralizer_singleton_iff.mpr hdz⟩
      have hde : x₁ * x₂ * e = e * (x₁ * x₂) := Subgroup.mem_centralizer_singleton_iff.mp (hSe hdS)
      have hex : e * x₁ * e⁻¹ = x₁ ∨ e * x₁ * e⁻¹ = x₁ * s := by
        refine hdec x₁ hx₁ _ (hcz e L L heL x₁ hx₁) x₂ hx₂ _ (hcz e L' L' heL' x₂ hx₂) ?_
        calc x₁ * x₂ = e * (x₁ * x₂) * e⁻¹ := (conj_eq_of_comm hde).symm
          _ = e * x₁ * e⁻¹ * (e * x₂ * e⁻¹) := by group
      rcases hex with h | h
      · exact F1 L hL hs x₁ hx₁ hx₁4 (comm_of_conj_eq h)
      · refine F2 L hL hs x₁ hx₁ hx₁4 (F3 x₁ (Subgroup.mem_sup_left hx₁) (comm_of_conj_eq ?_))
        calc e * z * x₁ * (e * z)⁻¹ = e * (z * x₁ * z⁻¹) * e⁻¹ := by group
          _ = e * x₁ * e⁻¹ * (e * s * e⁻¹) := by rw [hzx₁']; group
          _ = x₁ := by rw [h, hes, mul_assoc, hs.sq, mul_one]
    ·
      have heL' := (hother e hes).2 heL
      have hwL : conjSub (e * z) L = L' := by rw [conjSub_mul, hzL, heL]
      have key : ∀ l ∈ L, z * l * z⁻¹ = l ∨ z * l * z⁻¹ = l * s := by
        intro l hl
        have hl' : e * z * l * (e * z)⁻¹ ∈ L' := hcz (e * z) L L' hwL l hl
        have hd : l * (e * z * l * (e * z)⁻¹) * (e * z) =
            (e * z) * (l * (e * z * l * (e * z)⁻¹)) := by
          apply comm_of_conj_eq
          calc e * z * (l * (e * z * l * (e * z)⁻¹)) * (e * z)⁻¹ =
              (e * z * l * (e * z)⁻¹) * ((e * z * (e * z)) * l * (e * z * (e * z))⁻¹) := by
                group
            _ = e * z * l * (e * z)⁻¹ * l := by rw [hw2, one_mul, inv_one, mul_one]
            _ = l * (e * z * l * (e * z)⁻¹) := (hcomm l hl _ hl').symm
        have hdz := F3 _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
          (Subgroup.mem_sup_right hl')) hd
        refine hdec l hl _ (hcz z L L hzL l hl) _ hl' _ (hcz z L' L' hzL' _ hl') ?_
        calc l * (e * z * l * (e * z)⁻¹) = z * (l * (e * z * l * (e * z)⁻¹)) * z⁻¹ :=
              (conj_eq_of_comm hdz).symm
          _ = z * l * z⁻¹ * (z * (e * z * l * (e * z)⁻¹) * z⁻¹) := by group
      obtain ⟨x, hx, hx4, hxz⟩ := Sec13.exists_comm_orderOf_four hs (h8 L hL) hnab key
      exact F2 L hL hs x hx hx4 hxz.symm
  ·
    have hzL' := (hother z hzs).2 hzL
    have hdle : ∀ l ∈ L, l * (z * l * z⁻¹) * e = e * (l * (z * l * z⁻¹)) := by
      intro l hl
      have hl' : z * l * z⁻¹ ∈ L' := hcz z L L' hzL l hl
      have hdz : l * (z * l * z⁻¹) * z = z * (l * (z * l * z⁻¹)) := by
        apply comm_of_conj_eq
        calc z * (l * (z * l * z⁻¹)) * z⁻¹ = (z * l * z⁻¹) * ((z * z) * l * (z * z)⁻¹) := by
              group
          _ = z * l * z⁻¹ * l := by rw [hz2, one_mul, inv_one, mul_one]
          _ = l * (z * l * z⁻¹) := (hcomm l hl _ hl').symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hSe (hV ⟨Subgroup.mul_mem _
        (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hl'),
        Subgroup.mem_centralizer_singleton_iff.mpr hdz⟩))
    rcases hperm e hes L hL hs with heL | heL
    ·
      have heL' := (hother e hes).1 heL
      have key : ∀ l ∈ L, e * l * e⁻¹ = l ∨ e * l * e⁻¹ = l * s := by
        intro l hl
        have hl' : z * l * z⁻¹ ∈ L' := hcz z L L' hzL l hl
        refine hdec l hl _ (hcz e L L heL l hl) _ hl' _ (hcz e L' L' heL' _ hl') ?_
        calc l * (z * l * z⁻¹) = e * (l * (z * l * z⁻¹)) * e⁻¹ := (conj_eq_of_comm (hdle l hl)).symm
          _ = e * l * e⁻¹ * (e * (z * l * z⁻¹) * e⁻¹) := by group
      obtain ⟨x, hx, hx4, hxe⟩ := Sec13.exists_comm_orderOf_four hs (h8 L hL) hnab key
      exact F1 L hL hs x hx hx4 hxe.symm
    ·
      have heL' := (hother e hes).2 heL
      have hwL : conjSub (e * z) L = L := by rw [conjSub_mul, hzL, heL']
      have key : ∀ l ∈ L, e * z * l * (e * z)⁻¹ = l ∨ e * z * l * (e * z)⁻¹ = l * s := by
        intro l hl
        have hl' : z * l * z⁻¹ ∈ L' := hcz z L L' hzL l hl
        have hel : e * l * e⁻¹ ∈ L' := hcz e L L' heL l hl
        have hwl : e * z * l * (e * z)⁻¹ ∈ L := hcz (e * z) L L hwL l hl
        refine hdec l hl _ hwl _ hl' _ hel ?_
        calc l * (z * l * z⁻¹) = e * (l * (z * l * z⁻¹)) * e⁻¹ := (conj_eq_of_comm (hdle l hl)).symm
          _ = e * l * e⁻¹ * (e * z * l * (e * z)⁻¹) := by group
          _ = e * z * l * (e * z)⁻¹ * (e * l * e⁻¹) := (hcomm _ hwl _ hel).symm
      obtain ⟨x, hx, hx4, hxw⟩ := Sec13.exists_comm_orderOf_four hs (h8 L hL) hnab key
      exact F2 L hL hs x hx hx4 (F3 x (Subgroup.mem_sup_left hx) hxw.symm)

theorem exists_conj_fusion (hΩ : HypOmegaGen Ω) (h2 : ∀ L ∈ Ω, IsPGroup 2 L)
    (h8 : ∀ L ∈ Ω, Nat.card L = 8) {W S : Subgroup G} (hW : W ∈ WSet Ω)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {z e : G} (hzW : z ∈ W) (heW : e ∈ W)
    (he2 : e * e = 1) (hS : IsSylow2In S (Subgroup.centralizer ({z} : Set G))) (hWS : W ≤ S)
    (hSe : S ≤ Subgroup.centralizer ({e} : Set G))
    (hT : ∀ R ∈ Ω, R ∈ DSet Ω W → ∀ r : G, IsUniqueInvolution R r →
      ∃ n ∈ Subgroup.centralizer ({e} : Set G), n * z * n⁻¹ = r)
    (hZ : z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G)))
    (htw : ∀ L ∈ Ω, ∀ s : G, IsUniqueInvolution L s → ∃ L' ∈ Ω, L ≠ L' ∧
      IsUniqueInvolution L' s ∧ ∀ M ∈ Ω, IsUniqueInvolution M s → M = L ∨ M = L')
    {K : Subgroup G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) {x : G}
    (hxG : ∃ g : G, x = g * z * g⁻¹) (hxz : x * z = z * x) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), ∃ y ∈ Subgroup.centralizer ({e} : Set G),
      c * x * c⁻¹ = y * z * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hbad
  push Not at hbad
  obtain ⟨g, rfl⟩ := hxG
  have hL : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  obtain ⟨L', hL', hne, hx', hpair⟩ := htw _ hL _ (hz.conj g)
  set L := conjSub g K with hLdef
  set x := g * z * g⁻¹ with hxdef
  have hx : IsUniqueInvolution L x := hz.conj g
  have hX2 : IsPGroup 2 (L ⊔ L' : Subgroup G) := IsPGroup.to_sup_of_normal_right' (h2 L hL)
    (h2 L' hL') (Sec6Gen.le_normalizer_of_twin hΩ hL hL' hne hx hx')
  obtain ⟨c, hc, hcV⟩ := exists_conj_of_isSylow2In hS
    (hX2.to_le (inf_le_left : (L ⊔ L') ⊓ Subgroup.centralizer ({z} : Set G) ≤ L ⊔ L'))
    inf_le_right
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine false_of_forall_conj_ne hΩ h2 h8 hW hWab hzW heW he2 hz.sq hS hWS hSe hT hZ
    (hΩ.conjInvariant c⁻¹ L hL) (hΩ.conjInvariant c⁻¹ L' hL')
    (fun h => hne (conjSub_injective c⁻¹ h)) (s := c⁻¹ * x * c)
    (by simpa using hx.conj c⁻¹) (by simpa using hx'.conj c⁻¹) ?_ ?_ ?_ ?_
  · intro M hM hsM
    have h1 : IsUniqueInvolution (conjSub c M) x := by simpa [mul_assoc] using hsM.conj c
    rcases hpair _ (hΩ.conjInvariant c M hM) h1 with h | h
    · left; rw [← h, conjSub_inv_conjSub]
    · right; rw [← h, conjSub_inv_conjSub]
  · have hczi : c⁻¹ * z = z * c⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcz, mul_inv_cancel_right]
    calc c⁻¹ * x * c * z = c⁻¹ * x * (c * z) := by group
      _ = c⁻¹ * (x * z) * c := by rw [hcz]; group
      _ = c⁻¹ * z * x * c := by rw [hxz]; group
      _ = z * (c⁻¹ * x * c) := by rw [hczi]; group
  · rintro w ⟨hw, hwz⟩
    have hw' : c * w * c⁻¹ ∈ L ⊔ L' := by
      have h1 : w ∈ conjSub c⁻¹ (L ⊔ L') := by
        rw [conjSub, Subgroup.map_sup]
        exact hw
      simpa using mem_conjSub_iff.mp h1
    have hwz' : c * w * c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hwz) (Subgroup.inv_mem _ hc)
    have h2' := mem_conjSub_iff.mp (hcV ⟨hw', hwz'⟩)
    simpa [mul_assoc] using h2'
  · intro c' hc' y hy h
    refine hbad (c' * c⁻¹) (Subgroup.mul_mem _ hc' (Subgroup.inv_mem _ hc)) y hy ?_
    rw [← h]
    group

theorem exists_swap_equiv (hP : Q3CL.PartIHypG Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {K K' : Subgroup G} {z : G} (hK : K ∈ Ω) (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K = {K, K'}) (hS4 : MuIsoS4 Ω W) :
    ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4),
      ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap := by
  obtain ⟨⟨d₀, hd₀⟩, hcl⟩ := Q3T7.c231_clique hP hK htrans hz hK' hne hperp hW
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) := Q3T6.Mu.isTT_muDelta hP hW
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Q3T6.Mu.isStar_muDelta (Q3CL.T8.ctxOf hP hW)
  by_cases hconn : ∀ d ∈ Thompson.muDelta Ω W, ∀ a ∈ Thompson.muDelta Ω W,
      Star3T.Conn (Thompson.muDelta Ω W) d a
  · exfalso
    set Δ := Thompson.muDelta Ω W with hΔ
    obtain ⟨d', hne, hcent⟩ : ∃ d', d₀ ≠ d' ∧ Star3T.cent Δ d₀ = {d₀, d'} := by
      obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp (hcl d₀ hd₀)
      have hdx : d₀ ∈ ({x, y} : Set _) := hxy' ▸ Star3T.self_mem_cent hd₀
      rcases hdx with rfl | hdy
      · exact ⟨y, hxy, hxy'⟩
      · rw [Set.mem_singleton_iff] at hdy
        subst hdy
        exact ⟨x, fun e => hxy e.symm, by rw [hxy', Set.pair_comm]⟩
    have hd'c : d' ∈ Star3T.cent Δ d₀ := by rw [hcent]; exact Or.inr rfl
    have hd'Δ : d' ∈ Δ := hd'c.1
    have hcomm : d₀ * d' = d' * d₀ := hd'c.2.symm
    have hcent' : Star3T.cent Δ d' = {d₀, d'} := by
      have hsub : ({d₀, d'} : Set _) ⊆ Star3T.cent Δ d' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨hd₀, hcomm⟩
        · exact Star3T.self_mem_cent hd'Δ
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [hcl d' hd'Δ, Set.ncard_pair hne]) (Set.toFinite _)).symm
    have hall : ∀ a, Relation.ReflTransGen (Star3T.Adj Δ) d₀ a → a = d₀ ∨ a = d' := by
      intro a hb
      induction hb with
      | refl => exact Or.inl rfl
      | @tail b c _ hbc ih =>
        obtain ⟨-, hc, hbc⟩ := hbc
        rcases ih with rfl | rfl
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent] at this
          exact this
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent'] at this
          exact this
    have hΔeq : Δ = {d₀, d'} := by
      ext a
      constructor
      · exact fun ha => hall a (hconn d₀ hd₀ a ha)
      · rintro (rfl | rfl)
        · exact hd₀
        · exact hd'Δ
    have hgen : Subgroup.closure ({d₀, d'} : Set ↥(muGroup Ω W)) = ⊤ := by
      rw [← hΔeq]
      exact hTT.closure_eq_top
    obtain ⟨e₁⟩ := T7B.nonempty_mulEquiv_klein (hTT.mul_self d₀ hd₀) (hTT.mul_self d' hd'Δ)
      (hTT.ne_one d₀ hd₀) (hTT.ne_one d' hd'Δ) hne hcomm hgen
    obtain ⟨e₂⟩ := hS4
    have h1 := Nat.card_congr e₁.toEquiv
    have h2 := Nat.card_congr e₂.toEquiv
    rw [h2] at h1
    have h3 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      rfl
    have h4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega
  · push Not at hconn
    obtain ⟨d, hd, a, ha, hnc⟩ := hconn
    exact Star3T.exists_mulEquiv_perm_four hTT hS hd ha hnc (hcl d hd)

private def conjRep (hΩ : HypOmegaGen Ω) {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) (ρ : Thompson.Rep Ω W) : Thompson.Rep Ω W where
  K := conjSub n ρ.K
  R := conjSub n ρ.R
  r := n * ρ.r * n⁻¹
  hK := hΩ.conjInvariant n ρ.K ρ.hK
  hR := Q3CL.Thompson.conjSub_mem_D hΩ ρ.hR hn
  hRK := ρ.hRK.conj n
  hr := conj_mem_conjSub ρ.hr
  hrW := fun h => ρ.hrW ((Thompson.mem_normalizer_iff_of_mem hn _).mp h)

private theorem conjRep_img (hΩ : HypOmegaGen Ω) {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) (ρ : Thompson.Rep Ω W) :
    (conjRep hΩ hn ρ).img = Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ := by
  show Thompson.piG W (n * ρ.r * n⁻¹) = Thompson.piG W n * Thompson.piG W ρ.r *
    (Thompson.piG W n)⁻¹
  rw [Thompson.piG_mul (Subgroup.mul_mem _ hn ρ.r_mem_normalizer) (Subgroup.inv_mem _ hn),
    Thompson.piG_mul hn ρ.r_mem_normalizer, Thompson.piG_inv hn]

private theorem exists_rep (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ Ω) (h2 : IsPGroup 2 R) (hRD : R ∈ DSet Ω W) :
    ∃ ρ : Thompson.Rep Ω W, ρ.K = R := by
  have hRR : IsSylow2In R R := ⟨le_rfl, h2, fun V hVR _ hRV => le_antisymm hVR hRV⟩
  obtain ⟨-, -, -, -, hcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hRD hR hRR
  have hnle : ¬ R ≤ W := by
    intro hle
    rw [inf_eq_left.mpr hle] at hcard
    have : 0 < Nat.card ↥R := Nat.card_pos
    omega
  obtain ⟨r, hr, hrW⟩ := Set.not_subset.mp hnle
  exact ⟨⟨R, R, r, hR, hRD, hRR, hr, hrW⟩, rfl⟩

theorem exists_mGrp_conj (hP : Q3CL.PartIHypG Ω) (h2 : ∀ L ∈ Ω, IsPGroup 2 L) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hperp : KPerp Ω K = {K, K'}) (hS4 : MuIsoS4 Ω W)
    (hKD : K ∈ DSet Ω W) {R : Subgroup G} (hR : R ∈ Ω) (hRD : R ∈ DSet Ω W) {r : G}
    (hr : IsUniqueInvolution R r) : ∃ n ∈ MGrp Ω W, n * z * n⁻¹ = r := by
  obtain ⟨φ, hφ⟩ := exists_swap_equiv hP hW hK htrans hz hK' hne hperp hS4
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨ρ, hρK⟩ := exists_rep hP.hyp hW hK (h2 K hK) hKD
  obtain ⟨σ, hσR⟩ := exists_rep hP.hyp hW hR (h2 R hR) hRD
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem hφ (T7D.imgQ_mem ρ) (T7D.imgQ_mem σ)
  obtain ⟨n, hn, hyn⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
  have hnN : n ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hn
  have himg : Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ = σ.img := by
    rw [← hyn]
    exact congrArg Subtype.val hy
  have hKn : conjSub n K = R := by
    have := c.K_eq_of_img_eq (conjRep hP.hyp hnN ρ) σ (by rw [conjRep_img, himg])
    rw [← hρK, ← hσR]
    exact this
  refine ⟨n, hn, ?_⟩
  have h1 := hz.conj n
  rw [hKn] at h1
  exact (hr.eq h1).symm

private theorem not_mGrp_le_of_muIsoS4 {W : Subgroup G} (hS4 : MuIsoS4 Ω W) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hMP : MGrp Ω W ≤ P) : False := by
  obtain ⟨φ⟩ := hS4
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 with hσ
  have hσ3 : orderOf σ = 3 := orderOf_eq_prime (by rw [hσ]; decide) (by rw [hσ]; decide)
  obtain ⟨m, hm, hmy⟩ := T7E.exists_mem_MGrp_of_mem_muGroup (φ.symm σ)
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hm
  have h1 : orderOf (φ.symm σ) = 3 := by rw [MulEquiv.orderOf_eq, hσ3]
  have h2 : orderOf ((φ.symm σ : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) = 3 := by
    rw [Subgroup.orderOf_coe, h1]
  have h3 : Thompson.piG W m = Thompson.piN W ⟨m, hmN⟩ := by
    simp only [Thompson.piG, dif_pos hmN]
  rw [hmy, h3] at h2
  have h4 : orderOf (Thompson.piN W ⟨m, hmN⟩) ∣ orderOf (⟨m, hmN⟩ : ↥(Subgroup.normalizer
      (W : Set G))) := orderOf_map_dvd _ _
  rw [h2, Subgroup.orderOf_mk] at h4
  obtain ⟨k, hk⟩ := (hP ⟨m, hMP hm⟩)
  have h5 : orderOf m ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk (H := P) m (hMP hm)]
    exact orderOf_dvd_of_pow_eq_one hk
  have h6 : 3 ∣ 2 ^ k := h4.trans h5
  exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
    (Nat.Prime.dvd_of_dvd_pow (by norm_num) h6)) (by norm_num)

theorem exists_isSylow2In_le_normalizer (hP : Q3CL.PartIHypG Ω)
    (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (h2 : ∀ L ∈ Ω, IsPGroup 2 L)
    (h8 : ∀ L ∈ Ω, Nat.card L = 8) {W : Subgroup G} (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W)
    {H : Subgroup G} (hWH : W ≤ H) :
    ∃ S : Subgroup G, IsSylow2In S H ∧ W ≤ S ∧ S ≤ Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' := hW
  obtain ⟨η, ⟨S₀, hη, hinv⟩, hWη⟩ := hW
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup G) := fun U hU => (hη.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup G) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have h612 := Q3.Q3T8.Disconnected.AschTight.Sec7.l6_12_mod G Ω hP htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | halt
  swap
  ·
    exfalso
    refine not_mGrp_le_of_muIsoS4 hS4 S₀.isPGroup' (iSup₂_le fun R hR => ?_)
    obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR.1
    have hRJeq : J = R := hRJ.2.2 J le_rfl (h2 J hJ) hRJ.1
    subst hRJeq
    obtain ⟨-, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hP.hyp hW' hR hJ hRJ
    have hle : J ⊓ W ≤ J ⊓ (S₀ : Subgroup G) := inf_le_inf_left J hWS₀
    have h2' : 2 < Nat.card ↥(J ⊓ (S₀ : Subgroup G)) :=
      lt_of_lt_of_le (by omega) (Subgroup.card_le_of_le hle)
    obtain ⟨J', hJ', hJS⟩ := exists_isSylow2In_of_mem_RSet (halt J hJ h2')
    have hJ'eq : J' = J ⊓ (S₀ : Subgroup G) := hJS.2.2 J' le_rfl (h2 J' hJ') hJS.1
    have hcard : Nat.card ↥(J ⊓ (S₀ : Subgroup G)) = Nat.card ↥J := by
      rw [← hJ'eq, h8 J' hJ', h8 J hJ]
    have heq : J ⊓ (S₀ : Subgroup G) = J :=
      Subgroup.eq_of_le_of_card_ge inf_le_left hcard.ge
    exact heq ▸ inf_le_right
  · have hMS₀ : (⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup G)}, U) ≤
        (S₀ : Subgroup G) := iSup₂_le fun U hU => hU.2
    have hηeq : η = η₀ := huniq η ⟨S₀, hη, hinv⟩ fun m hm U hU => hinv m (hMS₀ hm) U hU
    subst hηeq
    obtain ⟨S, hS, hWS⟩ := IsSylow2In.exists_ge (S₀.isPGroup'.to_le hWS₀) hWH
    obtain ⟨S₁, hSS₁⟩ := hS.2.1.exists_le_sylow
    refine ⟨S, hS, hWS, fun s hs => ?_⟩
    obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₀ S₁
    have hUW : ∀ U ∈ η, U ≤ W := fun U hU => hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V)
      U hU le_rfl
    have hx1 : ∀ U ∈ η, conjSub x⁻¹ U ∈ η := by
      refine hwc x⁻¹ fun U hU => ?_
      rw [conjSub_le_iff, inv_inv, hx]
      exact (hUW U hU).trans (hWS.trans hSS₁)
    have e2 : conjSub x⁻¹ W = W := hWη ▸ Sec7.conjSub_iSup_eq_of_forall_mem hx1
    have e3 : conjSub x W = W := by
      conv_lhs => rw [← e2]
      exact conjSub_conjSub_inv x W
    have hs₀ : x⁻¹ * s * x ∈ (S₀ : Subgroup G) := by
      have := hSS₁ hs
      rw [← hx] at this
      exact mem_conjSub_iff.mp this
    have e4 : conjSub (x⁻¹ * s * x) W = W := hWη ▸ Sec7.conjSub_iSup_eq_of_forall_mem (hinv _ hs₀)
    have e5 : conjSub s W = W := by
      have : s = x * (x⁻¹ * s * x) * x⁻¹ := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, conjSub_mul, e2, e4, e3]
    exact mem_normalizer_iff_conjSub_eq.mpr e5

end L94

theorem l9_4_fusion (hD : ThmDHyp 3 Ω) {K K' W : Subgroup G} {z u e g : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K = {K, K'}) (hd : Hyp23bData Ω K K' W z u e g)
    (hZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set G))) {x : G}
    (hxG : ∃ y : G, x = y * z * y⁻¹) (hxz : x ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), ∃ y ∈ Subgroup.centralizer ({e} : Set G),
      c * x * c⁻¹ = y * z * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ : HypOmegaGen Ω := hD.hyp
  have h2 : ∀ L ∈ Ω, IsPGroup 2 L := hD.two
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hD.card L hL]; norm_num
  have hP : Q3CL.PartIHypG Ω := ⟨hΩ, classicalClause_of_two hΩ h2, hD.aEmpty⟩
  have htrK : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := fun J hJ => hD.trans K hK J hJ
  have heE : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← hd.he]
    exact Subgroup.mem_closure_singleton_self e
  have heW : e ∈ W := heE.1
  have hec : ∀ n ∈ Subgroup.normalizer (W : Set G), n * e = e * n := by
    intro n hn
    obtain ⟨y, hy, hye⟩ := heE.2
    have := Subgroup.mem_center_iff.mp hy ⟨n, hn⟩
    rw [← hye]
    exact congrArg Subtype.val this
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := (Q3CL.T8.ctxOf hP hd.hW).comm_W
  obtain ⟨hK'Ω, z', hz₁, hz'⟩ := id hK'
  have hzK' : IsUniqueInvolution K' z := by rw [hz.eq hz₁]; exact hz'
  have htwK : ∀ M ∈ Ω, IsUniqueInvolution M z → M = K ∨ M = K' := by
    intro M hM hzM
    by_cases hMK : M = K
    · exact Or.inl hMK
    have hMp : M ∈ KPerp Ω K :=
      Set.mem_insert_of_mem K (Q3CL.T3.twin_mem_omegaNbr hΩ hK hM hMK hz hzM)
    rw [hperp] at hMp
    simpa [hMK] using hMp
  have htw : ∀ L ∈ Ω, ∀ s : G, IsUniqueInvolution L s → ∃ L' ∈ Ω, L ≠ L' ∧
      IsUniqueInvolution L' s ∧ ∀ M ∈ Ω, IsUniqueInvolution M s → M = L ∨ M = L' := by
    intro L hL s hs
    obtain ⟨g₁, rfl⟩ := htrK L hL
    obtain rfl : s = g₁ * z * g₁⁻¹ := hs.eq (hz.conj g₁)
    refine ⟨conjSub g₁ K', hΩ.conjInvariant g₁ K' hK'Ω,
      fun h => hne (conjSub_injective g₁ h).symm, hzK'.conj g₁, fun M hM hsM => ?_⟩
    have h1 : IsUniqueInvolution (conjSub g₁⁻¹ M) z := by
      have := hsM.conj g₁⁻¹
      rwa [show g₁⁻¹ * (g₁ * z * g₁⁻¹) * g₁⁻¹⁻¹ = z by group] at this
    rcases htwK _ (hΩ.conjInvariant g₁⁻¹ M hM) h1 with h | h
    · left; rw [← h, conjSub_conjSub_inv]
    · right; rw [← h, conjSub_conjSub_inv]
  have hWz : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hd.hzW)
  obtain ⟨S, hS, hWS, hSN⟩ := L94.exists_isSylow2In_le_normalizer hP
    (fun K₁ hK₁ J hJ => hD.trans K₁ hK₁ J hJ) h2 h8 hd.hW hd.hS4 hWz
  have hSe : S ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hec x (hSN hx))
  have hKD : K ∈ DSet Ω W := by
    obtain ⟨S', R, R', hWS', hRK, -, hRS', -⟩ :=
      Q3T7.c231_sylow_frame hP hK hK'Ω hz hzK' hd.hW hd.hzW
    have hRD : R ∈ DSet Ω W :=
      Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hd.hW hWS' (mem_RSet_of_isSylow2In hK hRK) hRS'
    rwa [← hRK.2.2 K le_rfl (h2 K hK) hRK.1] at hRD
  have hT : ∀ R ∈ Ω, R ∈ DSet Ω W → ∀ r : G, IsUniqueInvolution R r →
      ∃ n ∈ Subgroup.centralizer ({e} : Set G), n * z * n⁻¹ = r := by
    intro R hR hRD r hr
    obtain ⟨n, hn, hnz⟩ :=
      L94.exists_mGrp_conj hP h2 hd.hW hK htrK hz hK' hne hperp hd.hS4 hKD hR hRD hr
    exact ⟨n, Subgroup.mem_centralizer_singleton_iff.mpr
      (hec n (Thompson.MGrp_le_normalizer Ω W hn)), hnz⟩
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hd.hg
  have hge : g⁻¹ * e * g = e := by rw [mul_assoc, ← hec g hgN, inv_mul_cancel_left]
  have hgz : g⁻¹ * (u * e) * g = z := by rw [← hd.hgt]; group
  have hgu : g⁻¹ * u * g = e * z := by
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hd.he2
    calc g⁻¹ * u * g = g⁻¹ * (u * e) * g * (g⁻¹ * e⁻¹ * g) := by group
      _ = z * e := by rw [hgz, hei, hge]
      _ = e * z := hWab z hd.hzW e heW
  have hZ' : z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G)) := by
    have hZ1 := C25W.conj_mem_zStarOf_conjSub _ g⁻¹ hZ
    rw [← C25W.centralizer_conj, inv_inv, hgz, hgu] at hZ1
    exact hZ1
  exact L94.exists_conj_fusion hΩ h2 h8 hd.hW hWab hd.hzW heW hd.he2 hS hWS hSe hT hZ' htw hK hz
    hxG (Subgroup.mem_centralizer_singleton_iff.mp hxz)

theorem l9_4 (hD : ThmDHyp 3 Ω) {K K' W : Subgroup G} {z u e g : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K = {K, K'}) (hd : Hyp23bData Ω K K' W z u e g)
    (hZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set G))) :
    (∀ x : G, (∃ y : G, x = y * z * y⁻¹) → x ∈ Subgroup.centralizer ({z} : Set G) →
        x = z ∨ ∃ c ∈ Subgroup.centralizer ({z} : Set G), x = c * (u * e) * c⁻¹) ∨
      ∃ y ∈ Subgroup.centralizer ({e} : Set G),
        y * z * y⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧ y * z * y⁻¹ ≠ z ∧
          ∀ c ∈ Subgroup.centralizer ({z} : Set G), y * z * y⁻¹ ≠ c * (u * e) * c⁻¹ := by
  by_cases h2' : ∃ y ∈ Subgroup.centralizer ({e} : Set G),
      y * z * y⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧ y * z * y⁻¹ ≠ z ∧
        ∀ c ∈ Subgroup.centralizer ({z} : Set G), y * z * y⁻¹ ≠ c * (u * e) * c⁻¹
  · exact Or.inr h2'
  left
  intro x hxG hxz
  by_contra hx
  push Not at hx
  obtain ⟨c, hc, y, hy, hcy⟩ := l9_4_fusion hD hK hz hK' hne hperp hd hZ hxG hxz
  apply h2'
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine ⟨y, hy, ?_, fun h => hx.1 ?_, fun c' hc' h => hx.2 (c⁻¹ * c')
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc') ?_⟩
  · rw [← hcy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hxz) (Subgroup.inv_mem _ hc)
  · calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = c⁻¹ * (z * c) := by rw [hcy, h, mul_assoc]
      _ = z := by rw [← hcz, inv_mul_cancel_left]
  · calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = c⁻¹ * (c' * (u * e) * c'⁻¹) * c := by rw [hcy, h]
      _ = c⁻¹ * c' * (u * e) * (c⁻¹ * c')⁻¹ := by group

end CFSG.ClassicalInvolution.Q3.Sec13
