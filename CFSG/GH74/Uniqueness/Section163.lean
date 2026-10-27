module

public import CFSG.GH74.Uniqueness.Section163Gen
public import CFSG.GH74.Uniqueness.Section163Rank
public import CFSG.GH74.Uniqueness.Section123

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Conf16

variable (c : Conf16 Z M)

theorem u_mem_M : c.u ∈ M := (mem_inf.mp c.hu).1

theorem u_mul_self : c.u * c.u = 1 := by rw [← sq, ← c.hu2, pow_orderOf_eq_one]

theorem u_ne_one : c.u ≠ 1 := fun h => by
  have := c.hu2
  rw [h, orderOf_one] at this
  omega

theorem z_mem_BM : c.z ∈ c.B ⊓ M := c.hT1.le c.hz_T1.1

theorem not_B_le : ¬ c.B ≤ M := fun h => c.htM (h c.ht_B)

theorem nonempty_BM : (Z ∩ ((c.B ⊓ M : Subgroup X) : Set X)).Nonempty := ⟨c.z, c.hz, c.z_mem_BM⟩

theorem isSylowOf_T1 (S : ZDSetup X Z M) : ABGLocalTools.IsSylowOf 2 c.T1 c.B :=
  S.prodDisc.isSylowOf_of_mem c.hT1 c.hz c.hz_T1.1

end Conf16

theorem ZDSetup.inter_eq_singleton_of_solvable
    (S : ZDSetup X Z M) (c : Conf16 Z M)
    (hsol : Group.IsSolvable ↥(cenHull Z c.u)) :
    Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) = {c.z} := by
  have hBtop : c.B ≠ ⊤ := A2.centralizer_ne_top S c.u_ne_one
  obtain ⟨-, h | h⟩ := S.corollary713 c.B hBtop c.not_B_le c.nonempty_BM
  · obtain ⟨-, u₀, -, hu₀, -⟩ := h
    have hz : c.z ∈ Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) := ⟨c.hz, c.z_mem_BM⟩
    rw [hu₀] at hz ⊢
    rw [Set.mem_singleton_iff.mp hz]
  · exfalso
    obtain ⟨-, hB, -, -⟩ := h
    have hsolv : Group.IsSolvable (↥(cenHull Z c.u) ⧸ center ↥(cenHull Z c.u)) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (center ↥(cenHull Z c.u)))
    have hsimple := isSimpleGroup_of_isBenderGroup hB
    obtain ⟨x, y, hxy⟩ := exists_not_commute_of_isBenderGroup hB
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) x y)

theorem ZDSetup.false_of_four_le_D (S : ZDSetup X Z M) (c : Conf16 Z M)
    (hZu : Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) = {c.z}) {W : Subgroup X} (hWD : W ≤ c.D)
    (hW4 : Nat.card W = 4) (hW2 : ∀ w ∈ W, w * w = 1) (huW : c.u ∈ W) : False := by
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => by
    have e1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hW2 _ (W.mul_mem ha hb))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hW2 b hb),
      inv_eq_of_mul_eq_one_right (hW2 a ha)] at e1
    exact e1.symm
  have hWz : ∀ w ∈ W, w * c.z * w⁻¹ = c.z := by
    intro w hw
    have hwM : w ∈ M := (mem_inf.mp (hWD hw)).1
    have hwu : w * c.u = c.u * w := hcomm w hw c.u huW
    have hzu : c.z * c.u = c.u * c.z := mem_centralizer_singleton_iff.mp (mem_inf.mp c.z_mem_BM).1
    have hmem : w * c.z * w⁻¹ ∈ Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) := by
      refine ⟨by simpa using S.invariant.2 c.z c.hz w⁻¹, mem_inf.mpr ⟨?_, ?_⟩⟩
      · rw [mem_centralizer_singleton_iff]
        have hwinv : w⁻¹ * c.u = c.u * w⁻¹ := by
          calc w⁻¹ * c.u = w⁻¹ * (c.u * w) * w⁻¹ := by group
            _ = w⁻¹ * (w * c.u) * w⁻¹ := by rw [hwu]
            _ = c.u * w⁻¹ := by group
        symm
        calc c.u * (w * c.z * w⁻¹) = (c.u * w) * c.z * w⁻¹ := by group
          _ = w * (c.u * c.z) * w⁻¹ := by rw [← hwu]; group
          _ = w * (c.z * c.u) * w⁻¹ := by rw [← hzu]
          _ = w * c.z * (c.u * w⁻¹) := by group
          _ = w * c.z * (w⁻¹ * c.u) := by rw [hwinv]
          _ = (w * c.z * w⁻¹) * c.u := by group
      · exact M.mul_mem (M.mul_mem hwM c.hzM) (M.inv_mem hwM)
    rw [hZu] at hmem
    exact hmem
  have hCz : ∀ w ∈ W, w ≠ 1 → centralizer ({w} : Set X) ⊓ pPrimeCoreIn c.D ≤
      centralizer ({c.z} : Set X) := by
    intro w hw hw1 y hy
    obtain ⟨hyw, hyN⟩ := mem_inf.mp hy
    have hyM : y ∈ M := (mem_inf.mp (pPrimeCoreIn_le _ hyN)).1
    have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 w hw) hw1
    have hle := c.hmax w (hWD hw) hw2
    rw [hZu, Set.ncard_singleton] at hle
    have hzw : c.z * w = w * c.z := by
      have h1 := hWz w hw
      calc c.z * w = (w * c.z * w⁻¹) * w := by rw [h1]
        _ = w * c.z := by group
    have hzmem : c.z ∈ Z ∩ ((centralizer ({w} : Set X) ⊓ M : Subgroup X) : Set X) :=
      ⟨c.hz, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hzw, c.hzM⟩⟩
    have hyw' : y * w = w * y := mem_centralizer_singleton_iff.mp hyw
    have hymem : y * c.z * y⁻¹ ∈ Z ∩ ((centralizer ({w} : Set X) ⊓ M : Subgroup X) : Set X) := by
      refine ⟨by simpa using S.invariant.2 c.z c.hz y⁻¹, mem_inf.mpr ⟨?_, ?_⟩⟩
      · rw [mem_centralizer_singleton_iff]
        have hyw'' : y⁻¹ * w = w * y⁻¹ := by
          calc y⁻¹ * w = y⁻¹ * (w * y) * y⁻¹ := by group
            _ = y⁻¹ * (y * w) * y⁻¹ := by rw [hyw']
            _ = w * y⁻¹ := by group
        calc y * c.z * y⁻¹ * w = y * c.z * (y⁻¹ * w) := by group
          _ = y * (c.z * w) * y⁻¹ := by rw [hyw'']; group
          _ = y * w * c.z * y⁻¹ := by rw [hzw]; group
          _ = w * (y * c.z * y⁻¹) := by rw [hyw']; group
      · exact M.mul_mem (M.mul_mem hyM c.hzM) (M.inv_mem hyM)
    have heq : y * c.z * y⁻¹ = c.z := (Set.ncard_le_one (Set.toFinite _)).mp hle _ hymem _ hzmem
    rw [mem_centralizer_singleton_iff]
    calc y * c.z = (y * c.z * y⁻¹) * y := by group
      _ = c.z * y := by rw [heq]
  have hND : pPrimeCoreIn c.D ≤ centralizer ({c.z} : Set X) :=
    le_of_inf_centralizer_le_of_four (odd_card_pPrimeCoreIn _) hW4 hW2
      (hWD.trans (pPrimeCoreIn_normalizes _)) hCz
  obtain ⟨hbij, -⟩ := S.prodDisc.prop36c S.invariant c.ht c.htM
  obtain ⟨y, hy, hyz, hyzc⟩ := S.exists_commuting_ne c.hz
  have hyM : y ∈ M := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
    (mem_centralizer_singleton_iff.mpr hyzc)
  obtain ⟨x, hx, hxy⟩ := (hbij c.z ⟨c.hz, c.hzM⟩).surjOn ⟨hy, hyM⟩
  have hxz : x * c.z = c.z * x := mem_centralizer_singleton_iff.mp (hND hx.1)
  apply hyz
  rw [← hxy]
  change x⁻¹ * c.z * x = c.z
  rw [mul_assoc, ← hxz]
  group

theorem ZDSetup.false_of_not_four_le_D
    (S : ZDSetup X Z M) (c : Conf16 Z M)
    (hZu : Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) = {c.z})
    (hno : ¬ ∃ V : Subgroup X, V ≤ c.D ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hno2 : ∀ γ ∈ omega M, γ ≠ M → ∀ V : Subgroup X, V ≤ M ⊓ γ → Nat.card V = 4 →
      (∀ v ∈ V, v * v = 1) → False := by
    intro γ hγ hγM V hV hV4 hV2
    have hβ : conjugate M c.t ∈ omega M := conjugate_mem_omega (self_mem_omega M) c.t
    have hβM : conjugate M c.t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
    obtain ⟨g, hg1, hg2⟩ := S.theorem4.1 M (self_mem_omega M) γ hγ (Ne.symm hγM) M
      (self_mem_omega M) (conjugate M c.t) hβ (Ne.symm hβM)
    apply hno
    refine ⟨conjugate V g, fun x hx => ?_, by rw [card_conjugate]; exact hV4, fun v hv => ?_⟩
    · rw [mem_conjugate_iff] at hx
      obtain ⟨hx1, hx2⟩ := mem_inf.mp (hV hx)
      have h1 : x ∈ conjugate M g := mem_conjugate_iff.mpr hx1
      have h2 : x ∈ conjugate γ g := mem_conjugate_iff.mpr hx2
      rw [hg1] at h1
      rw [hg2] at h2
      exact mem_inf.mpr ⟨h1, h2⟩
    · rw [mem_conjugate_iff] at hv
      have h := hV2 _ hv
      calc v * v = g⁻¹ * ((g * v * g⁻¹) * (g * v * g⁻¹)) * g := by group
        _ = 1 := by rw [h]; group
  have hiso : ∀ y ∈ Z, y ∈ c.B → y * c.z = c.z * y → y = c.z := by
    intro y hy hyB hyz
    have hyM : y ∈ M := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
      (mem_centralizer_singleton_iff.mpr hyz)
    have hmem : y ∈ Z ∩ ((c.B ⊓ M : Subgroup X) : Set X) := ⟨hy, mem_inf.mpr ⟨hyB, hyM⟩⟩
    rw [hZu] at hmem
    exact hmem
  obtain ⟨N, hNB, hBN, hNodd, hfac⟩ :=
    (isZStarIn_of_isolated S.invariant c.hz (mem_inf.mp c.z_mem_BM).1 hiso).exists_mul_centralizer
      (S.invariant.mul_self_eq_one c.hz)
  have huZ : c.u ∉ Z := by
    intro huZ
    have hut := (mem_inf.mp c.hu).2
    rw [mem_conjugate_iff] at hut
    have htinv : c.t⁻¹ ∈ M := S.prodDisc.mem_of_conj_mem huZ c.u_mem_M (by simpa using hut)
    exact c.htM (by simpa using M.inv_mem htinv)
  obtain ⟨E, hEB, hE8, hE2⟩ := S.exists_elemAbelian_eight_le_centralizer c.hu2 huZ
  have hEp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa [sq] using hE2 g g.2)⟩
  obtain ⟨b, -, hEb⟩ := exists_conjugate_le_of_isSylowOf (c.isSylowOf_T1 S) hEB hEp
  set E' := conjugate E b with hE'
  have hE'8 : Nat.card E' = 8 := by rw [hE', card_conjugate]; exact hE8
  have hE'2 : ∀ e ∈ E', e * e = 1 := by
    intro e he
    rw [hE', mem_conjugate_iff] at he
    have h := hE2 _ he
    calc e * e = b⁻¹ * ((b * e * b⁻¹) * (b * e * b⁻¹)) * b := by group
      _ = 1 := by rw [h]; group
  have hcard : ∀ s : Set X, s.ncard < 8 → ∃ e ∈ E', e ∉ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hle := Set.ncard_le_ncard (show (E' : Set X) ⊆ s from hcon) (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, show Nat.card (E' : Set X) = Nat.card E' from rfl, hE'8] at hle
    omega
  obtain ⟨a, haE, haS⟩ := hcard {1, c.u} (by
    have := Set.ncard_insert_le (1 : X) ({c.u} : Set X)
    rw [Set.ncard_singleton] at this
    omega)
  obtain ⟨b', hbE, hbS⟩ := hcard {1, c.u, a, a * c.u} (by
    have h1 := Set.ncard_insert_le (1 : X) ({c.u, a, a * c.u} : Set X)
    have h2 := Set.ncard_insert_le c.u ({a, a * c.u} : Set X)
    have h3 := Set.ncard_insert_le a ({a * c.u} : Set X)
    rw [Set.ncard_singleton] at h3
    omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at haS hbS
  obtain ⟨ha1, hau⟩ := haS
  obtain ⟨hb1, hbu, hba, hbau⟩ := hbS
  have hab : a * b' = b' * a := by
    have e1 : (a * b')⁻¹ = a * b' := inv_eq_of_mul_eq_one_right (hE'2 _ (E'.mul_mem haE hbE))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hE'2 b' hbE),
      inv_eq_of_mul_eq_one_right (hE'2 a haE)] at e1
    exact e1.symm
  set W' := fourSub a b' (hE'2 a haE) (hE'2 b' hbE) hab with hW'
  have hW'4 : Nat.card W' = 4 := card_fourSub ha1 hb1 (Ne.symm hba)
  have huW' : c.u ∉ W' := by
    rintro (h | h | h | h)
    · exact c.u_ne_one h
    · exact hau h.symm
    · exact hbu h.symm
    · apply hbau
      calc b' = a * (a * b') := by rw [← mul_assoc, hE'2 a haE, one_mul]
        _ = a * c.u := by rw [h]
  have hW'T1 : W' ≤ c.T1 := fourSub_le (hEb haE) (hEb hbE)
  have hK : ∀ w ∈ W', w ≠ 1 → centralizer ({w} : Set X) ⊓ N ≤ M := by
    intro w hw hw1 k hk
    obtain ⟨hkw, hkN⟩ := mem_inf.mp hk
    by_contra hkM
    have hγ : conjugate M k ∈ omega M := conjugate_mem_omega (self_mem_omega M) k
    have hγM : conjugate M k ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr hkM
    have hwBM := c.hT1.le (hW'T1 hw)
    have hwM : w ∈ M := (mem_inf.mp hwBM).2
    have hww : w * w = 1 := mul_self_of_mem_fourSub w hw
    have huw : c.u * w = w * c.u := (mem_centralizer_singleton_iff.mp (mem_inf.mp hwBM).1).symm
    have huw_ne : c.u ≠ w := fun h => huW' (h ▸ hw)
    have hku : k * c.u = c.u * k := mem_centralizer_singleton_iff.mp (hNB hkN)
    have hkw' : k * w = w * k := mem_centralizer_singleton_iff.mp hkw
    refine hno2 (conjugate M k) hγ hγM (fourSub c.u w c.u_mul_self hww huw) (fourSub_le ?_ ?_)
      (card_fourSub c.u_ne_one hw1 huw_ne) mul_self_of_mem_fourSub
    · refine mem_inf.mpr ⟨c.u_mem_M, mem_conjugate_iff.mpr ?_⟩
      rw [hku, mul_inv_cancel_right]
      exact c.u_mem_M
    · refine mem_inf.mpr ⟨hwM, mem_conjugate_iff.mpr ?_⟩
      rw [hkw', mul_inv_cancel_right]
      exact hwM
  have hNM : N ≤ M := le_of_inf_centralizer_le_of_four hNodd hW'4 mul_self_of_mem_fourSub
    ((hW'T1.trans (c.hT1.le.trans inf_le_left)).trans hBN) hK
  obtain ⟨k, hkN, d, hd, htkd⟩ := hfac c.t c.ht_B
  apply c.htM
  rw [htkd]
  exact M.mul_mem (hNM hkN) (S.prodDisc.centralizer_le_of_mem c.hz c.hzM (mem_inf.mp hd).2)

theorem ZDSetup.not_solvable_cenHull
    (S : ZDSetup X Z M) (c : Conf16 Z M) :
    ¬ Group.IsSolvable ↥(cenHull Z c.u) := by
  intro hsol
  have hZu := S.inter_eq_singleton_of_solvable c hsol
  by_cases h4 : ∃ V : Subgroup X, V ≤ c.D ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1
  · obtain ⟨V, hVD, hV4, hV2⟩ := h4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hu2grp : IsPGroup 2 (zpowers c.u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.hu2, pow_one])
    obtain ⟨P, hP, huP⟩ := exists_isSylowOf_ge_of_le (zpowers_le.mpr c.hu) hu2grp
    have hVp : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by simpa [sq] using hV2 g g.2)⟩
    obtain ⟨d, -, hVd⟩ := exists_conjugate_le_of_isSylowOf hP hVD hVp
    have hVd4 : Nat.card (conjugate V d) = 4 := by rw [card_conjugate]; exact hV4
    have hVd2 : ∀ v ∈ conjugate V d, v * v = 1 := by
      intro v hv
      rw [mem_conjugate_iff] at hv
      have h := hV2 _ hv
      calc v * v = d⁻¹ * ((d * v * d⁻¹) * (d * v * d⁻¹)) * d := by group
        _ = 1 := by rw [h]; group
    obtain ⟨v, hvP, hvv, hv1, hvu, huv⟩ :=
      exists_commute_ne_of_four hP.isPGroup (huP (mem_zpowers _)) c.hu2 hVd hVd4 hVd2
    exact S.false_of_four_le_D c hZu (W := fourSub c.u v c.u_mul_self hvv huv)
      (fourSub_le c.hu (hP.le hvP)) (card_fourSub c.u_ne_one hv1 (Ne.symm hvu))
      mul_self_of_mem_fourSub (Or.inr (Or.inl rfl))
  · exact S.false_of_not_four_le_D c hZu h4

theorem ZDSetup.lemma163
    (S : ZDSetup X Z M) : Lemma163Stmt Z M := by
  intro c
  have hBtop : c.B ≠ ⊤ := A2.centralizer_ne_top S c.u_ne_one
  have hns := S.not_solvable_cenHull c
  refine ⟨S.benderSub_exists hBtop c.not_B_le c.nonempty_BM hns, ?_, c.isSylowOf_T1 S, ?_⟩
  ·
    obtain ⟨-, h | h⟩ := S.corollary713 c.B hBtop c.not_B_le c.nonempty_BM
    · exact absurd h.1 hns
    · obtain ⟨-, -, -, hfac⟩ := h
      have hβ : conjugate M c.t ∈ alphaOrbit M c.B := ⟨c.t, c.ht_B, rfl⟩
      have hβM : conjugate M c.t ≠ M :=
        (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
      have := hfac _ hβ hβM
      rwa [inf_assoc] at this
  ·
    intro u' hu'M hu'2 hsol'
    by_contra hC
    have hCu : ¬ c.B ≤ M := c.not_B_le
    have h714 := S.corollary714 c.hu2 hu'2 c.u_mem_M hu'M hCu hC
    exact hns (h714.2.mpr hsol')

end CFSG.GH74.Uniqueness
